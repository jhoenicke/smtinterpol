package de.uni_freiburg.informatik.ultimate.smtinterpol.itt;

public class DeBruijnVariable extends Term {
	int mIndex;
	
	public DeBruijnVariable(int index, Term type) {
		super(type.shiftBruijn(0, index + 1));
		mIndex = index;
	}
	
	@Override
	protected Term internalEval() {
		return this;
	}

	public Term substituteAndEval(Term t, int offset) {
		if (mIndex < offset)
			return this;
		if (mIndex > offset)
			return shiftBruijn(offset, -1);
		t = t.shiftBruijn(0, offset);
		assert getType().equals(t.getType());
		return t;
	}

	/**
	 * Shift de Bruijn indices >= start by offset.
	 * @param start  The first index to modify.
	 * @param offset The offset added to the index.
	 * @return the substituted term.
	 */
	@Override
	public Term shiftBruijn(int start, int offset) {
		if (mIndex < start)
			return this;
		return new DeBruijnVariable(mIndex + offset, 
				getType().shiftBruijn(mIndex, -mIndex-1));
	}

	public String toString(int offset, int prec) {
		return "@" + (offset - mIndex - 1);
	}

	public boolean equals(Object o) {
		if (this == o)
			return true;
		if (!(o instanceof DeBruijnVariable))
			return false;
		DeBruijnVariable other = (DeBruijnVariable) o;
		return mIndex == other.mIndex;
	}
}
