package de.uni_freiburg.informatik.ultimate.smtinterpol.itt;

import java.util.ArrayDeque;
import java.util.ArrayList;

public class InductiveType extends Term {
	String mName;
	int    mNumShared;
	Constructor[] mConstrs;
	Term[] mParams;
	
	public InductiveType(String name, Term type) {
		super(type);
		mName = name;
		mParams = splitParams(type);
		mNumShared = -1;
		mConstrs = null;
		
		System.err.println("New Type "+name+" : "+getType());
	}
	
	public void setConstructors(ArrayList<Constructor> constrs) {
		if (constrs == null) {
			mConstrs = new Constructor[0];
			mNumShared = 0;
		} else {
			assert mNumShared >= 0 && mNumShared <= mParams.length;
			mConstrs = constrs.toArray(new Constructor[constrs.size()]);
		}
	}
	
	private static Term[] splitParams(Term type) {
		ArrayDeque<Term> params = new ArrayDeque<Term>();
		while (type instanceof PiTerm) {
			PiTerm pi = (PiTerm) type;
			params.addLast(pi.mDomain);
			type = pi.mRange;
		}
		if (type != Term.U)
			throw new IllegalArgumentException("Typecheck: Illegal Inductive Type");
		return params.toArray(new Term[params.size()]);
	}
	
	protected Term internalEval() {
		return this;
	}
	
	protected String toString(int offset, int prec) {
		return mName;
	}

	public boolean equals(Object o) {
		return (this == o);
	}
}
