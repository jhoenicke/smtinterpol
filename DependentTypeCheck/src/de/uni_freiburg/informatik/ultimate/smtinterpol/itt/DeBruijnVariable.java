package de.uni_freiburg.informatik.ultimate.smtinterpol.itt;

public class DeBruijnVariable extends Term {
	int mIndex;
	
	public DeBruijnVariable(int index, Term type) {
		super(type.shiftBruijn(0, index + 1));
		mIndex = index;
	}
	
	public Term substitute(Term[] t, int offset) {
		if (mIndex < offset) {
			Term type = getType().substitute(t, offset);
			if (type == getType())
				return this;
			return new DeBruijnVariable(mIndex, type.shiftBruijn(mIndex, - mIndex-1));
		}
		if (mIndex - offset >= t.length) {
			return shiftBruijn(offset, -t.length);
		}
		assert (mIndex - offset < t.length);
		Term result = t[mIndex - offset].shiftBruijn(0, offset);
		assert getType().substitute(t, offset).equals(result.getType());
		return result;
	}

	/**
	 * Shift de Bruijn indices >= start by offset.
	 * @param start  The first index to modify.
	 * @param offset The offset added to the index.
	 * @return the substituted term.
	 */
	@Override
	public Term shiftBruijn(int start, int offset) {
		if (mIndex < start) {
			Term type = getType().shiftBruijn(start, offset);
			if (type == getType())
				return this;
			return new DeBruijnVariable(mIndex, type.shiftBruijn(mIndex, - mIndex-1));
		}
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
