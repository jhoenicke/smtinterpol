package de.uni_freiburg.informatik.ultimate.smtinterpol.itt;

/**
 * This class represents a function type, i.e., the set/class of functions
 * from a domain to a range.  The domain and range must be sets or classes,
 * i.e., their type must be U.  The range can depend on the
 * parameter of the function.  This is achieved using de Bruijn indexed
 * variables.  The range can contain a de Bruijn variable bound by this
 * PiTerm whose type is the domain.
 * 
 * @author hoenicke
 */
public class PiTerm extends Term {
	Term mDomain;
	Term mRange;
	/**
	 * If this is non-zero it gives the position of the next argument
	 * in mRange that contains this and all the following
	 * arguments in its type in a way that it can easily be recovered.
	 */
	int mMaybeHidden;
	
	public PiTerm(Term domain, Term range) {
		this(domain, range, typecheck(domain, range));
	}
	public PiTerm(Term domain, Term range, Term type) {
		super(type);
		assert typecheck(domain, range).equals(type);
		this.mDomain = domain;
		this.mRange = range;
		this.mMaybeHidden = checkHidden(range);
		this.mNumFreeVariables = Math.max(mDomain.numFreeVariables(), 
										  mRange.numFreeVariables() - 1);
	}
	
	/**
	 * Compute the type of a pi term with the given arguments.
	 * The type is always U.  We also check that the domain and range
	 * have type U.
	 * @param domain the domain type, its type must be U.
	 * @param range the range type, its type must be U.
	 * @return the type of the pi term.
	 */
	public static Term typecheck(Term domain, Term range) {
		Term domType = domain.getType().evaluateHead();
		Term rngType = range.getType().evaluateHead();
		if (domType instanceof UniverseTerm
			&& rngType instanceof UniverseTerm) {
			int domLevel = ((UniverseTerm) domType).getLevel();
			int rngLevel = ((UniverseTerm) rngType).getLevel();
			return Term.universe(Math.max(domLevel, rngLevel));
		}
		throw new IllegalArgumentException("Typecheck: PI "+domType+" and "+rngType);
	}

	/**
	 * Checks if the variable may be hidden and how many type arguments
	 * must be at least skipped.  We compute {@see mMaybeHidden}.
	 */
	private static int checkHidden(Term range) {
		int varNumber = 0;
		range = range.evaluateHead();
		while (range instanceof PiTerm) {
			PiTerm pi = (PiTerm) range;
			if (checkVariableUnifiable(pi.mDomain, varNumber)) {
				return varNumber + 1;
			}
			if (pi.mMaybeHidden == 0) {
				return 0;
			}
			for (int i = 0; i < pi.mMaybeHidden; i++) {
				range = ((PiTerm) range).mRange.evaluateHead();
				varNumber++;
			}
		}
		return 0;
	}

	/**
	 * Checks if the head symbol is a constructor or a type
	 * constructor.  Other heads are not allowed for unification.
	 */
	private static boolean checkHead(Term term) {
		term = term.evaluateHead();
		while (term instanceof AppTerm) {
			term = ((AppTerm) term).mFunc;
		}
		return (term instanceof Constructor)
			|| (term instanceof InductiveType);
	}
	
	private static boolean checkVariableUnifiable(Term term, int varNumber) {
		term = term.evaluateHead();

		if ((term instanceof SubstTerm)
			&& ((SubstTerm) term).mSubstitution.mShiftOffset == varNumber)
			return true;
		if (term instanceof PiTerm) {
			PiTerm pi = (PiTerm) term;
			return checkVariableUnifiable(pi.mDomain, varNumber)
				|| checkVariableUnifiable(pi.mRange, varNumber+1);
		}
		/* first check that term is an application of constructor 
		 * or type constructor */
		if (!checkHead(term))
			return false;

		/* Check if variable occurs in argument in good position. */
		while (term instanceof AppTerm) {
			AppTerm app = (AppTerm) term;
			if (checkVariableUnifiable(app.mArg, varNumber))
				return true;
			term = app.mFunc;
		}
		
		/* Variable couldn't be unified */
		return false;
	}

	private PiTerm skipHidden(int hidden) {
		PiTerm t = this;
		while (hidden-- > 0) {
			t = (PiTerm) t.mRange.evaluateHead();
		}
		return t;
	}

	/**
	 * Substitute the hidden arguments and write them to the Term array.
	 * We assume, we already checked that the domType is suitable for 
	 * unification.
	 * @param argType the type of the argument supplied to the
	 *   function that skips hidden arguments, or a subtype on recursive 
	 *   calls.  This is unified with domType.
	 * @param domType The type of the parameter where the argument should be
	 *   applied or a subtype of this at recursive calls.  
	 * @param hiddenArgs an array where the found hidden arguments are written
	 *   to.
	 * @param numHidden the number of hidden arguments.  This is the number of
	 *   parameters skipped until the domType parameter.
	 * @param offset the number of variables in domType that are bound by
	 *   the parameter type (for recursive calls).
	 */
	private boolean substituteHidden(Term argType, Term domType,
									 Term[] hiddenArgs, int numHidden,
									 int offset) {
		argType = argType.evaluateHead();
		domType = domType.evaluateHead();

		if (domType instanceof SubstTerm) {
			/* found a possible substitution */
			int index = offset + numHidden - 1 -
				((SubstTerm) domType).mSubstitution.mShiftOffset;
			if (index >= 0 && index < numHidden) {
				if (offset > 0) {
					/* The original domType and argType are of the form
					 * x: Type -> ... x_(index+offset) ...
					 * x: Type -> ... argType ...
					 * If x occurs in argType, we will get a type error
					 * later.  We don't check for it now. Instead we replace
					 * all x by U.
					 */
					Term[] skipped = new Term[offset];
					for (int i = 0; i < offset; i++) {
						skipped[i] = Term.universe(0);
					}
					argType = Term.substitute
						(argType, new Substitution(skipped, 0), null);
				}
				if (hiddenArgs[index] == null) {
					hiddenArgs[index] = argType;
					/* Substitute recursively. argType becomes the new
					 * argType for index
					 */
					substituteHidden(argType.getType(),
									 skipHidden(index).mDomain,
									 hiddenArgs, index, 0);
				} else if (!hiddenArgs[index].equals(argType)) {
					return false;
				}
				return true;
			} else {
				if (!(argType instanceof SubstTerm))
					return false;
				int argIndex = offset + numHidden - 1 -
					((SubstTerm) argType).mSubstitution.mShiftOffset;
				if (index < 0)
					argIndex -= numHidden;
				return argIndex == index;
			}
		}

		if (domType instanceof PiTerm) {
			if (!(argType instanceof PiTerm))
				return false;
			PiTerm piDom = (PiTerm) domType;
			PiTerm piArg = (PiTerm) argType;
			return substituteHidden(piArg.mDomain, piDom.mDomain,
									hiddenArgs, numHidden, offset)
				&& substituteHidden(piArg.mRange, piDom.mRange,
									hiddenArgs, numHidden, offset + 1);
		}

		/* skip things that can't be unified correctly for now. */
		if (!checkHead(domType))
			return true;

		while (domType instanceof AppTerm) {
			if (!(argType instanceof AppTerm))
				return false;
			AppTerm appDom = (AppTerm) domType;
			AppTerm appArg = (AppTerm) argType;
			if (!substituteHidden(appArg.mArg, appDom.mArg,
								  hiddenArgs, numHidden, offset))
				return false;
			domType = appDom.mFunc;
			argType = appArg.mFunc;
		}
		/* now domType is a constructor, check that it is the right one */
		return argType.equals(domType);
	}

	private Term checkHiddenArguments(Term func, Term arg, int hidden) {
		PiTerm next = skipHidden(hidden);
		/* First, check if we get a match on the sub level */
		if (next.mMaybeHidden > 0) {
			Term result = checkHiddenArguments(func, arg,
											   hidden + mMaybeHidden);
			if (result != null)
				return result;
		}
		
		/* Check if we get a match on this level */
		Term[] hiddenArgs = new Term[hidden];
		if (!substituteHidden(arg.getType(), next.mDomain,
							  hiddenArgs, hidden, 0))
			return null;
		
		for (int i = 0; i < hidden; i++) {
			Term dom = ((PiTerm)func.getType().evaluateHead()).mDomain;
			if (hiddenArgs[i] == null
				|| !hiddenArgs[i].getType().isSubType(dom)) {
				return null;
			}
			func = new AppTerm(func, hiddenArgs[i]);
		}
		return func;
	}

	public Term instantiateHiddenArguments(Term func, Term arg) {
		Term result = checkHiddenArguments(func, arg, 0);
		return result == null ? func : result;
	}
	
	@Override
	public Term evaluateHead() {
		return this;
	}

	public String toString(int offset, int prec) {
		if (mName != null)
			return mName.toString(offset, prec);
		StringBuilder sb = new StringBuilder();
		if (prec >= 1)
			sb.append('(');
		if (mMaybeHidden > 0)
			sb.append('{');
		sb.append('@').append(offset).append(" : ");
		sb.append(mDomain.toString(offset, 2));
		if (mMaybeHidden > 0)
			sb.append('}');
		sb.append(" -> ").append(mRange.toString(offset + 1, 0));
		if (prec >= 1)
			sb.append(')');
		return sb.toString();
	}

	public boolean equalsHead(Term o) {
		if (!(o instanceof PiTerm))
			return false;
		PiTerm other = (PiTerm) o;
		return mDomain.equals(other.mDomain) && mRange.equals(other.mRange);
	}

	public boolean isSubTypeHead(Term o) {
		if (!(o instanceof PiTerm))
			return false;
		PiTerm other = (PiTerm) o;
		return other.mDomain.isSubType(mDomain)
				&& mRange.isSubType(other.mRange);
	}
}
