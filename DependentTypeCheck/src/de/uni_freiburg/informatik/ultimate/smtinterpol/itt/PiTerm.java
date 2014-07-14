package de.uni_freiburg.informatik.ultimate.smtinterpol.itt;

public class PiTerm extends Term {
	Term mDomain;
	Term mRange;
	
	public PiTerm(Term domain, Term range) {
		this(domain, range, typecheck(domain, range));
	}
	public PiTerm(Term domain, Term range, Term type) {
		super(type);
		this.mDomain = domain;
		this.mRange = range;
	}
	
	private static Term typecheck(Term domain, Term range) {
		if (domain.getType() == Term.U
			&& range.getType() == Term.U)
			return Term.U;
		if (domain.getType() != Term.U && domain.getType() != null)
			throw new IllegalArgumentException("Typecheck: PI");
		if (range.getType() != Term.U && range.getType() != null)
			throw new IllegalArgumentException("Typecheck: PI");
		return null;
	}

	@Override
	protected Term internalEval() {
		return new PiTerm(mDomain.evaluate(), mRange.evaluate(), getType());
	}

	@Override
	public Term substituteAndEval(Term t, int offset) {
		return new PiTerm(mDomain.substituteAndEval(t, offset),
					mRange.substituteAndEval(t, offset + 1));
	}

	/**
	 * Shift de Bruijn indices >= start by offset.
	 * @param start  The first index to modify.
	 * @param offset The offset added to the index.
	 * @return the substituted term.
	 */
	@Override
	public Term shiftBruijn(int start, int offset) {
		return new PiTerm(mDomain.shiftBruijn(start, offset),
				mRange.shiftBruijn(start + 1, offset));
	}
	
	public String toString(int offset, int prec) {
		String str = "@" + offset + " : " + mDomain.toString(offset,1)
				+ " -> " + mRange.toString(offset + 1, 0);
		return prec >= 1 ? "(" + str + ")" : str;
	}

	public boolean equals(Object o) {
		if (this == o)
			return true;
		if (!(o instanceof PiTerm))
			return false;
		PiTerm other = (PiTerm) o;
		return mDomain.equals(other.mDomain) && mRange.equals(other.mRange);
	}
}
