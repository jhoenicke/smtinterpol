package de.uni_freiburg.informatik.ultimate.smtinterpol.itt;

public class LocalInfo {
	public final String mName;
	public final Term mTerm;
	public final boolean mIsLet;
	/**
	 * The index of the last local variable with the same name.
	 * This is -1 if no previous local variable exists.
	 */
	public int mLastIndex;

	public LocalInfo(String name, Term term) {
		this.mName = name;
		this.mTerm = term;
		this.mIsLet = false;
	}

	public LocalInfo(String name, Term term, boolean isLet) {
		this.mName = name;
		this.mTerm = term;
		this.mIsLet = isLet;
	}
	
	public String toString() {
		return mName;
	}
}
