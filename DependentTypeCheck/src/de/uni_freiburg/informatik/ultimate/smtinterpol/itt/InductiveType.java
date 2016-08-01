package de.uni_freiburg.informatik.ultimate.smtinterpol.itt;

import java.util.ArrayDeque;
import java.util.ArrayList;

public class InductiveType extends Term {
	String mName;
	int    mNumShared;
	Constructor[] mConstrs;
	RecOperator mRecOperator;
	Term[] mParams;
	UniverseTerm mUniv;
	
	public InductiveType(String name, Term type) {
		super(type);
		mName = name;
		splitParams(type);
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

	private void splitParams(Term type) {
		ArrayDeque<Term> params = new ArrayDeque<Term>();
		type = type.evaluateHead();
		while (type instanceof PiTerm) {
			PiTerm pi = (PiTerm) type;
			params.addLast(pi.mDomain.evaluate());
			type = pi.mRange.evaluateHead();
		}
		if (!(type instanceof UniverseTerm))
			throw new IllegalArgumentException("Typecheck: Illegal Inductive Type");
		mParams = params.toArray(new Term[params.size()]);
		mUniv = (UniverseTerm) type;
	}

	protected String toString(int offset, int prec, boolean raw) {
		return mName;
	}
}
