package de.uni_freiburg.informatik.ultimate.smtinterpol.itt;

import java.util.ArrayDeque;

public class Constructor extends Term {
	InductiveType mInductiveType;
	String mName;
	int    mIndex;
	
	public Constructor(String name, int index, 
			InductiveType type, Term declType) {
		super(computeType(type, declType));
		mInductiveType = type;
		mName = name;
		mIndex = index;
	}
	
	private static Term computeType(InductiveType indType, Term declType) {
		if (indType.mNumShared == -1) {
			indType.mNumShared = indType.mParams.length
				- countPrivateVars(declType);
		}
		/* Check the parameter types */
		Term type = declType;
		int offset = 0;
		while (type instanceof PiTerm) {
			PiTerm pi = (PiTerm) type;
			if (!checkClean(indType, pi.mDomain, offset, true))
				throw new IllegalArgumentException("Constructor malformed");
			type = pi.mRange;
			offset++;
		}
		/* Check the return type */
		if (!checkTCApplication(indType, type, offset))
			throw new IllegalArgumentException("Constructor malformed");
		/* Substitute private parameters with U, we already checked
		 * they are not present in the type.
		 */
		Term[] dummy = new Term[indType.mParams.length - indType.mNumShared];
		for (int i = 0; i < dummy.length; i++)
			dummy[i] = Term.U;
		Substitution backShift = new Substitution(dummy, 0);
		declType = Term.substitute(declType, backShift, null);
		/* Now add the shared parameters in front of the type */
		for (int i = indType.mNumShared - 1; i >= 0; i--) {
			declType = new PiTerm(indType.mParams[i], declType);
		}
		return declType.evaluate();
	}

	private static int countPrivateVars(Term type) {
		/* compute the number of shared arguments by looking at return type */
		// get return type and update offset to expected inherited parameter
		int offset = 0;
		while (type instanceof PiTerm) {
			type = ((PiTerm) type).mRange;
			offset++;
		}
		// count private arguments
		int numPrivs = 0;
		while (type instanceof AppTerm) {
			AppTerm app = (AppTerm) type;
			Term arg = app.mArg;
			if (arg instanceof SubstTerm) {
				SubstTerm subst = (SubstTerm) arg;
				if (subst.mSubTerm instanceof Variable
					&& subst.mSubstitution.mSubstTerms.length == 0
					&& subst.mSubstitution.mShiftOffset == offset)
					break;
			}
			offset++;
			numPrivs++;
			type = app.mFunc;
		}
		return numPrivs;
	}

	private static boolean checkTCApplication(InductiveType indType, Term paramType, int offset) {
		int numPriv = indType.mParams.length - indType.mNumShared;
		Term type = paramType;
		int argNum = 0;
		while (type instanceof AppTerm) {
			AppTerm app = (AppTerm) type;
			if (argNum < numPriv) {
				/* just check that private parameters are okay */
				if (!checkClean(indType, app.mArg, offset, false))
					return false;
			} else {
				/* check that shared arg is correctly referenced */
				if (! (app.mArg instanceof SubstTerm))
					return false;
				SubstTerm subst = (SubstTerm) app.mArg;
				if (! (subst.mSubTerm instanceof Variable)
					|| subst.mSubstitution.mSubstTerms.length != 0)
					return false;
				int index = subst.mSubstitution.mShiftOffset;
				if (index != offset + argNum)
					return false;
			}
			type = app.mFunc;
			argNum++;
		}
		return type == indType && argNum == indType.mParams.length;
	}

	private static boolean checkClean(InductiveType indType, Term type, 
			int offset, boolean allowTC) {
		if (allowTC && checkTCApplication(indType, type, offset))
			return true;
		type = type.evaluateHead();
		if (type == indType)
			return false;
		if (type instanceof AppTerm) {
			AppTerm app = (AppTerm) type;
			return checkClean(indType, app.mFunc, offset, false)
				&& checkClean(indType, app.mArg, offset + 1, false);
		}
		if (type instanceof SubstTerm) {
			SubstTerm subst = (SubstTerm) type;
			assert (subst.mSubTerm instanceof Variable);
			assert (subst.mSubstitution.mSubstTerms.length == 0);
			int index = subst.mSubstitution.mShiftOffset;
			assert index < offset + indType.mParams.length;
			return index < offset
				|| index >= offset + indType.mParams.length - indType.mNumShared;
		}
		if (type instanceof PiTerm) {
			PiTerm pi = (PiTerm) type;
			return checkClean(indType, pi.mDomain, offset, false)
				&& checkClean(indType, pi.mRange, offset + 1, allowTC);
		}
		if (type instanceof LambdaTerm) {
			LambdaTerm lam = (LambdaTerm) type;
			return checkClean(indType, lam.mType, offset, false)
				&& checkClean(indType, lam.mSubTerm, offset + 1, false);
		}
		return true;
	}

	protected String toString(int offset, int prec) {
		return mInductiveType.mName + "." + mName;
	}

	public Term computeRecType(Term cType) {
		ArrayDeque<Term> constrParams = new ArrayDeque<Term>();
		Term t = getType().evaluateHead();
		Substitution shiftOne = Substitution.shift(1);
		Term me = this;
		for (int j = 0; j < mInductiveType.mNumShared; j++) {
			Term param = ((PiTerm) t).mDomain;
			me = Term.application(Term.substitute(me, shiftOne, null), 
					Term.variable(1 + mIndex, param), null);
			t = ((PiTerm) t).mRange;
		}
		int offset = 0;
		Substitution reorderVars = Substitution.shift(1 + mIndex);
		while (t instanceof PiTerm) {
			PiTerm pi = (PiTerm) t;
			Term param = Term.substitute(pi.mDomain, reorderVars, null);
			constrParams.add(param);
			t = pi.mRange.evaluateHead();
			me = Term.application(Term.substitute(me, shiftOne, null), 
					Term.variable(0, param), null);
			reorderVars = Substitution.consShifted(Term.variable(0, param),
					reorderVars, Integer.MAX_VALUE);
			offset++;
			if (isTC(param)) {
				// adapt term to cope for the extra param before the recursive param.
				Term q = Term.substitute(param, shiftOne, null);
				q = q.evaluateHead();
				ArrayDeque<Term> funcArgs = new ArrayDeque<Term>();
				while (q instanceof PiTerm) {
					PiTerm pi2 = (PiTerm) q;
					funcArgs.addLast(pi2.mDomain);
					q = pi2.mRange.evaluateHead();
				}
				Term c = buildCTerm(q, offset + funcArgs.size(), cType);
				// The parameter for which this is the recursive copy.
				int paramNr = funcArgs.size();
				Term termParam = Term.variable(paramNr, param);
				for (Term arg : funcArgs) {
					termParam = Term.application(termParam, Term.variable(--paramNr, arg), null);
				}
				c = Term.application(c, termParam, null);
				while (!funcArgs.isEmpty()) {
					c = new PiTerm(funcArgs.removeLast(), c);
				}
				constrParams.add(c);
				offset++;
				me = Term.substitute(me, shiftOne, null);
				reorderVars = Substitution.compose(reorderVars, shiftOne, Integer.MAX_VALUE);
			}
		}
		t = Term.substitute(t, reorderVars, null);
		Term result = buildCTerm(t, offset, cType);
		result = Term.application(result, me, null);
		while (!constrParams.isEmpty()) {
			result = new PiTerm(constrParams.removeLast(), result);
		}
		return result;
	}

	private Term buildCTerm(Term param, int offset, Term cType) {
		Term[] localArgs = new Term[mInductiveType.mParams.length 
		                            - mInductiveType.mNumShared];
		for (int i = localArgs.length-1; i >= 0; i--) {
			AppTerm app = (AppTerm) param.evaluateHead();
			localArgs[i] = app.mArg;
			param = app.mFunc;
		}
		Term c = Term.variable(offset + mIndex, cType);
		for (int i = 0; i < localArgs.length; i++) {
			c = Term.application(c, localArgs[i], null);
		}
		return c;
	}

	private boolean isTC(Term param) {
		param = param.evaluateHead();
		while (param instanceof PiTerm) {
			PiTerm pi = (PiTerm) param;
			param = pi.mRange.evaluateHead();
		}
		for (int i = 0; i < mInductiveType.mParams.length; i++) {
			if (!(param instanceof AppTerm))
				return false;
			param = ((AppTerm) param).mFunc.evaluateHead();
		}
		return param == mInductiveType;
	}

	public Term applyRec(Term constrCase, Term partialRecTerm,
			ArrayDeque<Term> constrArgs) {
		// remove shared arguments (which reappear in constrArgs but are
		// not used)
		for (int i = 0; i < mInductiveType.mNumShared; i++) {
			constrArgs.removeFirst();
		}
		// for each remaining argument add it to constrCase
		while (!constrArgs.isEmpty()) {
			Term arg = constrArgs.removeFirst();
			constrCase = Term.application(constrCase, arg, null);
			Term argType = arg.getType();
			// if it is a recursive argument also add the recursive application
			if (isTC(argType)) {
				// partialRecTerm contains everything except the priv arguments
				// and arg.
				Term rec = partialRecTerm;
				argType = argType.evaluateHead();
				Term[] params = null;
				if (argType instanceof PiTerm) {
					ArrayDeque<Term> funcParams = new ArrayDeque<Term>();
					while (argType instanceof PiTerm) {
						PiTerm pi = (PiTerm) argType;
						funcParams.addLast(pi.mDomain);
						argType = pi.mRange.evaluateHead();
					}
					params = funcParams.toArray(new Term[funcParams.size()]);
					arg = Term.substitute(arg, Substitution.shift(params.length), null);
					for (int i = 0; i < params.length; i++) {
						Term param = Term.variable(params.length - i - 1, params[i]);
						arg = Term.application(arg, param, null);
					}
					rec = Term.substitute(rec, 
							Substitution.shift(params.length), null);
				}

				// Extract local parameters from arg type.
				int numLocals = mInductiveType.mParams.length
							- mInductiveType.mNumShared;
				if (numLocals > 0) {
					ArrayDeque<Term> localTerms = new ArrayDeque<Term>();
					for (int i = 0; i < numLocals; i++) {
						AppTerm app = (AppTerm) argType.evaluateHead();
						localTerms.addFirst(app.mArg);
						argType = app.mFunc;
					}
					for (Term local: localTerms) {
						rec = Term.application(rec, local, null);
					}
				}
				rec = Term.application(rec, arg, null);
				if (params != null) {
					for (int i = params.length - 1; i >= 0; i--) {
						rec = Term.lambda(params[i], rec, null);
					}
				}
				constrCase = Term.application(constrCase, rec, null);
			}
		}
		return constrCase;
	}
}
