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
	int mNumFreeVariables;
	boolean mIsHidden;
	
	public PiTerm(LocalInfo info, Term range) {
		this(info.mTerm, range, info.mIsHidden);
		assert !info.mIsLet;
	}
	public PiTerm(Term domain, Term range, boolean isHidden) {
		this(domain, range, typecheck(domain, range), isHidden);
	}
	public PiTerm(Term domain, Term range, Term type, boolean isHidden) {
		super(type);
		assert typecheck(domain, range).isSubType(type);
		this.mDomain = domain;
		this.mRange = range;
		if (isHidden) {
			checkHidden(range);
			this.mIsHidden = true;
		}
		mNumFreeVariables = Math.max(mDomain.numFreeVariables(), 
				mRange.numFreeVariables() - 1);
	}
	
	@Override
	public int numFreeVariables() {
		return mNumFreeVariables;
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
	 * Checks that range is a PiTerm and that the variable 0 occurs in
	 * the first non-hidden PiTerm at a unifiable location.
	 */
	private static void checkHidden(Term range) {
		int varNumber = 0;
		range = range.evaluateHead();
		while (range instanceof PiTerm) {
			PiTerm pi = (PiTerm) range;
			if (pi.mIsHidden) {
				varNumber++;
				range = pi.mRange.evaluateHead();
				continue;
			}
			if (checkVariableUnifiable(pi.mDomain, varNumber))
				return;
			throw new IllegalArgumentException
				("Hidden Variables must occur in type of next non-hidden variables @-1:(" + pi.mRange.evaluate() + ") -> " + pi.mDomain.evaluate());
		}
		throw new IllegalArgumentException
			("Hidden Variables must be followed by non-hidden variables: " + range.evaluate());
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
		Term t = term;
		while (t instanceof AppTerm) {
			t = ((AppTerm) t).mFunc;
		}
		if (!(t instanceof Constructor)
			&& !(t instanceof InductiveType))
			return false;
		
		/* Check if variable occurs in argument in good position. */
		t = term;
		while (t instanceof AppTerm) {
			AppTerm app = (AppTerm) t;
			if (checkVariableUnifiable(app.mArg, varNumber))
				return true;
			t = app.mFunc;
		}
		
		/* Variable couldn't be unified */
		return false;
	}

	/**
	 * Checks that range is a PiTerm and that the variable 0 occurs in
	 * the first non-hidden PiTerm at a unifiable location.
	 */
	public static void substituteHidden(Term argType, Term domType,
										Term[] hiddenArgs, int offset) {
		argType = argType.evaluateHead();
		domType = domType.evaluateHead();

		if (domType instanceof SubstTerm) {
			/* found a substitution */
			int index = ((SubstTerm) domType).mSubstitution.mShiftOffset - offset;
			assert index < hiddenArgs.length
				&& hiddenArgs[hiddenArgs.length - 1 - index] == null;
			if (offset > 0) {
				Term[] skipped = new Term[offset];
				for (int i = 0; i < offset; i++) {
					skipped[i] = Term.universe(0);
				}
				argType = Term.substitute
					(argType, new Substitution(skipped, 0), null);
			}
			hiddenArgs[hiddenArgs.length - 1 - index] = argType;
		}

		if (domType instanceof PiTerm) {
			if (!(argType instanceof PiTerm))
				throw new IllegalArgumentException("Can't unify " + argType +
												   " and " + domType);
			PiTerm pi = (PiTerm) domType;
			for (int var = 0; var < hiddenArgs.length; var++) {
				if (hiddenArgs[var] == null
					&& checkVariableUnifiable(pi.mDomain, hiddenArgs.length-1-var + offset))
					substituteHidden(((PiTerm) argType).mDomain, pi.mDomain,
									 hiddenArgs, offset);
				if (hiddenArgs[var] == null
					&& checkVariableUnifiable(pi.mRange, hiddenArgs.length-1-var + offset + 1))
					substituteHidden(((PiTerm) argType).mRange, pi.mRange,
									 hiddenArgs, offset + 1);
			}
			return;
		}

		Term t = domType;
		Term a = argType;
		while (t instanceof AppTerm) {
			if (!(a instanceof AppTerm))
				throw new IllegalArgumentException("Can't unify " + a.evaluate() +
												   " and " + t.evaluate());
			Term arg = ((AppTerm) t).mArg;
			for (int var = 0; var < hiddenArgs.length; var++) {
				if (hiddenArgs[var] == null
					&& checkVariableUnifiable(arg, hiddenArgs.length-1
											  - var + offset)) {
					substituteHidden(((AppTerm) a).mArg, arg,
									 hiddenArgs, offset);
					break;
				}
			}
			a = ((AppTerm) a).mFunc;
			t = ((AppTerm) t).mFunc;
		}
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
		if (mIsHidden)
			sb.append('{');
		sb.append('@').append(offset).append(" : ");
		sb.append(mDomain.toString(offset, 2));
		if (mIsHidden)
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
