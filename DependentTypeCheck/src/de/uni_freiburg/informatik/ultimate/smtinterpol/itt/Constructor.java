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
		Term type = declType;
		ArrayDeque<Term> params = new ArrayDeque<Term>();
		while (type instanceof PiTerm) {
			PiTerm pi = (PiTerm) type;
			params.addLast(pi.mDomain);
			type = pi.mRange;
		}

		ArrayDeque<Term> args = new ArrayDeque<Term>();
		while (type instanceof AppTerm) {
			AppTerm app = (AppTerm) type;
			args.addFirst(app.mArg);
			type = app.mFunc;
		}
		if (type != indType)
			throw new IllegalArgumentException("Typecheck: Constructor must return Inductive Type");
		if (indType.mNumShared == -1) {
			indType.mNumShared = 0;
			for (Term arg : args) {
				if (!(arg instanceof DeBruijnVariable))
					break;
				int index = ((DeBruijnVariable) arg).mIndex;
				if (index != params.size() + indType.mParams.length - 1
						- indType.mNumShared)
					break;
				indType.mNumShared++;
			}
		}
		int numPrivate = indType.mParams.length - indType.mNumShared;
		// TODO check that indType only occurs where it may occur, with correct
		// shared params as args and that no private params occurs.
		declType = declType.shiftBruijn(0, -numPrivate);
		for (int i = indType.mNumShared - 1; i >= 0; i--) {
			declType = new PiTerm(indType.mParams[i], declType);
		}
		return declType;
	}

	protected String toString(int offset, int prec) {
		return mInductiveType.mName + "." + mName;
	}

	public boolean equals(Object o) {
		return (this == o);
	}

	public Term computeJType(Term cType) {
		ArrayDeque<Term> constrParams = new ArrayDeque<Term>();
		Term t = getType();
		Term me = this;
		for (int j = 0; j < mInductiveType.mNumShared; j++) {
			Term param = ((PiTerm) t).mDomain;
			me = new AppTerm(me.shiftBruijn(0, 1), 
					new DeBruijnVariable(1 + mIndex, param));
			t = ((PiTerm) t).mRange;
		}
		int offset = 0;
		int numArg = 0;
		while (t instanceof PiTerm) {
			PiTerm pi = (PiTerm) t;
			Term param = pi.mDomain.shiftBruijn(numArg, 1 + mIndex);
			constrParams.add(param);
			t = pi.mRange;
			me = new AppTerm(me.shiftBruijn(0, 1), new DeBruijnVariable(0, param));
			numArg++;
			offset++;
			if (isTC(param)) {
				Term c = buildCTerm(param.shiftBruijn(0, 1), offset, cType);
				c = new AppTerm(c, new DeBruijnVariable(0, param));
				constrParams.add(c);
				offset++;
				me = me.shiftBruijn(0, 1);
				t = t.shiftBruijn(0, 1);
			}
		}
		t = t.shiftBruijn(constrParams.size(), 1 + mIndex);
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
			localArgs[i] = ((AppTerm) q).mArg;
			q = ((AppTerm) q).mFunc;
		}
		Term c = new DeBruijnVariable(offset + mIndex, cType);
		for (int i = 0; i < localArgs.length; i++) {
			c = new AppTerm(c, localArgs[i]);
		}
		return c;
	}

	private boolean isTC(Term param) {
		for (int i = 0; i < mInductiveType.mParams.length; i++) {
			if (!(param instanceof AppTerm))
				return false;
			param = ((AppTerm) param).mFunc;
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
