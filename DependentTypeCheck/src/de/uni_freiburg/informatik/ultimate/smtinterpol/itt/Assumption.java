package de.uni_freiburg.informatik.ultimate.smtinterpol.itt;

public class Assumption extends Term {
	public Assumption(String name, Term type) {
		super(type);
		setName(name);
	}

	@Override
	protected String toString(int offset, int prec) {
		return mName;
	}
}
