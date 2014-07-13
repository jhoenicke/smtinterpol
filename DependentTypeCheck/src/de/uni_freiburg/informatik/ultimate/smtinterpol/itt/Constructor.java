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

		System.err.println("New Constructor "+this+" : "+getType());
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
		declType = declType.shiftBruijn(params.size(), -numPrivate);
		for (int i = indType.mNumShared - 1; i >= 0; i--) {
			declType = new PiTerm(indType.mParams[i], declType);
		}
		return declType;
	}

	public Term internalEval() {
		return this;
	}

	protected String toString(int offset, int prec) {
		return mInductiveType.mName + "." + mName;
	}

	public boolean equals(Object o) {
		return (this == o);
	}
}
