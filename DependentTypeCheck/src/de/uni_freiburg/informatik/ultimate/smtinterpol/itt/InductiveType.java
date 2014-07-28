package de.uni_freiburg.informatik.ultimate.smtinterpol.itt;

import java.util.ArrayDeque;
import java.util.ArrayList;

public class InductiveType extends Term {
	String mName;
	int    mNumShared;
	Constructor[] mConstrs;
	RecOperator mRecOperator;
	Term[] mParams;
	
	public InductiveType(String name, Term type) {
		super(type);
		mName = name;
		mParams = splitParams(type);
		mNumShared = -1;
		mConstrs = null;
	}
	
	public void setConstructors(ArrayList<Constructor> constrs) {
		if (constrs == null) {
			mConstrs = new Constructor[0];
			mNumShared = 0;
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
		if (type != Term.U)
			throw new IllegalArgumentException("Typecheck: Illegal Inductive Type");
		return params.toArray(new Term[params.size()]);
	}

	protected String toString(int offset, int prec) {
		return mName;
	}
}
