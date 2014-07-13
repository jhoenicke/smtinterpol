package de.uni_freiburg.informatik.ultimate.smtinterpol.itt;

public class LambdaTerm extends Term {
	Term mArgType;
	Term mSubTerm;

	public LambdaTerm(Term argType, Term subTerm) {
		super(computeType(argType, subTerm));
		mArgType = argType;
		mSubTerm = subTerm;
	}

	public LambdaTerm(Term argType, Term subTerm, Term type) {
		super(type);
		mArgType = argType;
		mSubTerm = subTerm;
	}
	
	private static Term computeType(Term argType, Term subTerm) {
		return new PiTerm(argType, subTerm.getType());
	}

	@Override
	protected Term internalEval() {
		return new LambdaTerm(mArgType, mSubTerm.evaluate(), getType());
	}

	@Override
	public Term substituteAndEval(Term t, int offset) {
		return new LambdaTerm(mArgType.substituteAndEval(t, offset),
					mSubTerm.substituteAndEval(t, offset + 1));
	}

	/**
	 * Shift de Bruijn indices >= start by offset.
	 * @param start  The first index to modify.
	 * @param offset The offset added to the index.
	 * @return the substituted term.
	 */
	@Override
	public Term shiftBruijn(int start, int offset) {
		return new LambdaTerm(mArgType.shiftBruijn(start, offset),
				mSubTerm.shiftBruijn(start + 1, offset),
				getType().shiftBruijn(start, offset));
	}

	public String toString(int offset, int prec) {
		String str = "\\@" + offset + " : " + mArgType.toString(offset, 2)
						+ " " + mSubTerm.toString(offset + 1, 0);
		return prec >= 1 ? "(" + str + ")" : str;
	}

	public boolean equals(Object o) {
		if (this == o)
			return true;
		if (!(o instanceof LambdaTerm))
			return false;
		LambdaTerm other = (LambdaTerm) o;
		return mArgType.equals(other.mArgType) && mSubTerm.equals(other.mSubTerm);
	}
}
