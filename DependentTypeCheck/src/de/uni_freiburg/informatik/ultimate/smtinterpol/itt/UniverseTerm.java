package de.uni_freiburg.informatik.ultimate.smtinterpol.itt;

public class UniverseTerm extends Term {
	final int level;
	
	public UniverseTerm(int level) {
		super(null);
		this.level = level;
	}

	public Term getType() {
		return Term.universe(level + 1);
	}

	@Override
	protected String toString(int offset, int prec) {
		return level == 0 ? "U" : "U"+level;
	}

	public int getLevel() {
		return level;
	}

	public boolean isSubTypeHead(Term t) {
		return (t instanceof UniverseTerm)
				&& level <= ((UniverseTerm) t).getLevel();
	}
}
