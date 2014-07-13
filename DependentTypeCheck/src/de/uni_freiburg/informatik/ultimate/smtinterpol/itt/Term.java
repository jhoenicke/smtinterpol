package de.uni_freiburg.informatik.ultimate.smtinterpol.itt;

public abstract class Term {
	Term mEvaluated;
	Term mType;
	
	public final static Term U = new Term(null) {
		protected Term internalEval() { return this; }
		public String toString(int offset, int prec) { return "U"; }
		public boolean equals(Object o) {
			return (this == o);
		}
	};

	public Term(Term type) {
		mType = type;
	}
	
	@SuppressWarnings("unused")
	private Term() {}
	
	public Term getType() {
		return mType;
	}
	public Term evaluate() {
		if (mEvaluated == null)
			mEvaluated = internalEval();
		return mEvaluated;
	}
	
	protected abstract Term internalEval();
	
	/**
	 * Substitute in the current term the deBruin-Variable with index offset
	 * with t, decrease all later deBruijn indices by one and evaluate the 
	 * resulting term.
	 * @param t The term to substitute.
	 * @param offset the deBruijn index that should be substituted
	 * @return the substituted and evaluated term.
	 */
	public Term substituteAndEval(Term t, int offset) {
		return this;
	}
	
	/**
	 * Shift de Bruijn indices >= start by offset.
	 * @param start  The first index to modify.
	 * @param offset The offset added to the index.
	 * @return the substituted term.
	 */
	public Term shiftBruijn(int start, int offset) {
		return this;
	}
	
	public String toString() {
		return toString(0, 0);
	}
	
	protected abstract String toString(int offset, int prec);
	public abstract boolean equals(Object t);
}
