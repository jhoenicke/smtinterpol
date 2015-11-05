package de.uni_freiburg.informatik.ultimate.smtinterpol.itt;

import java.util.ArrayDeque;
import java.util.ArrayList;

public class InductiveType extends Term {
	String mName;
	int    mNumShared;
	Constructor[] mConstrs;
	RecOperator mRecOperator;
	Term[] mParams;
	boolean[] mHidden;
	
	public InductiveType(String name, Term type) {
		super(type);
		mName = name;
		mParams = splitParams(type);
		mHidden = new boolean[mParams.length];
		Term t = type;
		for (int i = 0; i < mHidden.length; i++) {
			PiTerm pi = (PiTerm) t.evaluateHead();
			mHidden[i] = pi.mIsHidden;
			t = pi.mRange;
		}
		mNumShared = -1;
		mConstrs = null;
	}
	
	public void setConstructors(ArrayList<Constructor> constrs) {
		if (constrs == null) {
			mConstrs = new Constructor[0];
			mNumShared = mParams.length;
		} else {
			assert mNumShared >= 0 && mNumShared <= mParams.length;
			mConstrs = constrs.toArray(new Constructor[constrs.size()]);
		}
		mRecOperator = new RecOperator(this);
	}

	private static Term[] splitParams(Term type) {
		ArrayDeque<Term> params = new ArrayDeque<Term>();
		type = type.evaluateHead();
		while (type instanceof PiTerm) {
			PiTerm pi = (PiTerm) type;
			params.addLast(pi.mDomain.evaluate());
			type = pi.mRange.evaluateHead();
		}
		if (type != Term.universe(0))
			throw new IllegalArgumentException("Typecheck: Illegal Inductive Type");
		return params.toArray(new Term[params.size()]);
	}

	protected String toString(int offset, int prec) {
		return mName;
	}
}