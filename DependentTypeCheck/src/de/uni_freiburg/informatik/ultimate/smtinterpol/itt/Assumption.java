package de.uni_freiburg.informatik.ultimate.smtinterpol.itt;

public class Assumption extends Term {
	public Assumption(String name, Term type) {
		super(type);
		setName(name);
		mNumFreeVariables = type.numFreeVariables();
	}

	@Override
	protected String toString(int offset, int prec, boolean raw) {
		return mName.toString(offset, prec, raw);
	}
}
