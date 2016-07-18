package de.uni_freiburg.informatik.ultimate.smtinterpol.itt;

public class Variable extends Term {
	public Variable(Term type) {
		super(type);
		mNumFreeVariables = Math.max(1, getType().numFreeVariables());
	}
	
	public String toString(int offset, int prec, boolean raw) {
		return "@";
	}

	public Term evaluateHead() {
		throw new AssertionError("Evaluating Variable???");
	}
}
