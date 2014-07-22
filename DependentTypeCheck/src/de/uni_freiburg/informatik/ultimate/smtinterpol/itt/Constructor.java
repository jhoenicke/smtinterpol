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
			/* compute the number of shared arguments by looking at return type */
			Term type = declType;
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
						&& subst.mSubstitution instanceof Substitution.Shift
						&& ((Substitution.Shift) 
								subst.mSubstitution).mOffset == offset)
						break;
				}
				offset++;
				numPrivs++;
			}
			indType.mNumShared = indType.mParams.length - numPrivs;
		}
		Term type = declType;
		int offset = 0;
		while (type instanceof PiTerm) {
			PiTerm pi = (PiTerm) type;
			if (!checkTCApplication(indType, pi.mDomain, offset)
				&& !checkClean(indType, pi.mDomain, offset))
				throw new IllegalArgumentException("Constructor malformed");
			type = pi.mRange;
			offset++;
		}
		if (!checkTCApplication(indType, type, offset))
			throw new IllegalArgumentException("Constructor malformed");
		Substitution backShift = Substitution.shift(0);
		for (int i = 0; i < indType.mParams.length - indType.mNumShared; i++)
			backShift = Substitution.cons(Term.variable(0, Term.U), backShift);
		declType = Term.substitute(declType, backShift, null);
		for (int i = indType.mNumShared - 1; i >= 0; i--) {
			declType = new PiTerm(indType.mParams[i], declType);
		}
		return declType.evaluate();
	}

	private static boolean checkTCApplication(InductiveType indType, Term paramType, int offset) {
		int numPriv = indType.mParams.length - indType.mNumShared;
		Term type = paramType;
		int argNum = 0;
		while (type instanceof AppTerm) {
			AppTerm app = (AppTerm) type;
			if (argNum < numPriv) {
				/* just check that private parameters are okay */
				if (!checkClean(indType, app.mArg, offset))
					return false;
			} else {
				/* check that shared arg is correctly referenced */
				if (! (app.mArg instanceof SubstTerm))
					return false;
				SubstTerm subst = (SubstTerm) app.mArg;
				if (! (subst.mSubTerm instanceof Variable)
					|| !(subst.mSubstitution instanceof Substitution.Shift))
					return false;
				int index = ((Substitution.Shift) subst.mSubstitution).mOffset;
				if (index != offset + argNum)
					return false;
			}
			type = app.mFunc;
			argNum++;
		}
		return type == indType && argNum == indType.mParams.length;
	}

	private static boolean checkClean(InductiveType indType, Term type, int offset) {
		if (type == indType)
			return false;
		if (type instanceof AppTerm) {
			AppTerm app = (AppTerm) type;
			return checkClean(indType, app.mFunc, offset)
				&& checkClean(indType, app.mArg, offset + 1);
		}
		if (type instanceof SubstTerm) {
			SubstTerm subst = (SubstTerm) type;
			if (!(subst.mSubTerm instanceof Variable))
				return false;
			if (!(subst.mSubstitution instanceof Substitution.Shift))
				return false;
			int index = ((Substitution.Shift) subst.mSubstitution).mOffset;
			assert index < offset + indType.mParams.length;
			return index < offset
				|| index >= offset + indType.mParams.length - indType.mNumShared;
		}
		if (type instanceof PiTerm) {
			PiTerm pi = (PiTerm) type;
			return checkClean(indType, pi.mDomain, offset)
				&& checkClean(indType, pi.mRange, offset + 1);
		}
		if (type instanceof LambdaTerm) {
			LambdaTerm lam = (LambdaTerm) type;
			return checkClean(indType, lam.mType, offset)
				&& checkClean(indType, lam.mSubTerm, offset + 1);
		}
		return true;
	}

	protected String toString(int offset, int prec) {
		return mInductiveType.mName + "." + mName;
	}

	public Term computeJType(Term cType) {
		ArrayDeque<Term> constrParams = new ArrayDeque<Term>();
		Term t = getType().evaluateHead();
		Substitution shiftOne = Substitution.shift(1);
		Term me = this;
		for (int j = 0; j < mInductiveType.mNumShared; j++) {
			Term param = ((PiTerm) t).mDomain;
			me = new AppTerm(Term.substitute(me, shiftOne, null), 
					Term.variable(1 + mIndex, param));
			t = ((PiTerm) t).mRange;
		}
		int offset = 0;
		Substitution reorderVars = Substitution.shift(1 + mIndex);
		while (t instanceof PiTerm) {
			PiTerm pi = (PiTerm) t;
			Term param = Term.substitute(pi.mDomain, reorderVars, null);
			constrParams.add(param);
			t = pi.mRange.evaluateHead();
			me = new AppTerm(Term.substitute(me, shiftOne, null), 
					Term.variable(0, param));
			reorderVars = Substitution.cons(Term.variable(0, param),
					Substitution.compose(reorderVars, shiftOne));
			offset++;
			if (isTC(param)) {
				Term c = buildCTerm(Term.substitute(param, shiftOne, null), 
						offset, cType);
				c = new AppTerm(c, Term.variable(0, param));
				constrParams.add(c);
				offset++;
				me = Term.substitute(me, shiftOne, null);
				reorderVars = Substitution.compose(reorderVars, shiftOne);
			}
		}
		t = Term.substitute(t, reorderVars, null);
		Term result = buildCTerm(t, offset, cType);
		result = new AppTerm(result, me);
		while (!constrParams.isEmpty()) {
			result = new PiTerm(constrParams.removeLast(), result);
		}
		return result;
	}

	private Term buildCTerm(Term q, int offset, Term cType) {
		Term[] localArgs = new Term[mInductiveType.mParams.length 
		                            - mInductiveType.mNumShared];
		for (int i = localArgs.length-1; i >= 0; i--) {
			AppTerm app = (AppTerm) q.evaluateHead();
			localArgs[i] = app.mArg;
			q = app.mFunc;
		}
		Term c = Term.variable(offset + mIndex, cType);
		for (int i = 0; i < localArgs.length; i++) {
			c = new AppTerm(c, localArgs[i]);
		}
		return c;
	}

	private boolean isTC(Term param) {
		param = param.evaluateHead();
		for (int i = 0; i < mInductiveType.mParams.length; i++) {
			if (!(param instanceof AppTerm))
				return false;
			param = ((AppTerm) param).mFunc.evaluateHead();
		}
		return param.equals(mInductiveType);
	}

	public Term applyJ(Term constrCase, Term partialJTerm,
			ArrayDeque<Term> constrArgs) {
		// remove shared arguments (which reappear in constrArgs but are
		// not used)
		for (int i = 0; i < mInductiveType.mNumShared; i++) {
			constrArgs.removeFirst();
		}
		// for each remaining argument add it to constrCase
		while (!constrArgs.isEmpty()) {
			Term arg = constrArgs.removeFirst();
			constrCase = new AppTerm(constrCase, arg);
			Term argType = arg.getType();
			// if it is a recursive argument also add the recursive application
			if (isTC(argType)) {
				// partialJTerm contains everything except the priv arguments
				// and arg.
				Term rec = partialJTerm;

				// Extract local parameters from arg type.
				int numLocals = mInductiveType.mParams.length
							- mInductiveType.mNumShared;
				if (numLocals > 0) {
					ArrayDeque<Term> localTerms = new ArrayDeque<Term>();
					for (int i = 0; i < numLocals; i++) {
						localTerms.addFirst(((AppTerm)argType).mArg);
						argType = ((AppTerm) argType).mFunc;
					}
					for (Term local: localTerms) {
						rec = new AppTerm(rec, local);
					}
				}
				rec = new AppTerm(rec, arg);
				constrCase = new AppTerm(constrCase, rec);
			}
		}
		return constrCase;
	}
}
