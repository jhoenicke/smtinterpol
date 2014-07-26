package de.uni_freiburg.informatik.ultimate.smtinterpol.itt;

public class Variable extends Term {
	public Variable(Term type) {
		super(type);
	}
	
	public String toString(int offset, int prec) {
		return "@";
	}

	@Override
	public int numFreeVariables() {
		return Math.max(1, getType().numFreeVariables());
	}
	
	public Term evaluateHead() {
		System.err.println("Evaluating Variable???");
		return Term.substitute(this, Substitution.shift(0), null);
	}
}
