package de.uni_freiburg.informatik.ultimate.smtinterpol.itt;

public class UniverseTerm extends Term {
	final boolean isProp;
	final int level;
	
	public UniverseTerm(boolean prop) {
		super(null);
		this.isProp = true;
		this.level = 0;
	}

	public UniverseTerm(int level) {
		super(null);
		this.isProp = false;
		this.level = level;
	}

	public boolean isProp() {
		return isProp;
	}

	public Term getType() {
		return isProp ? Term.universe(0) : Term.universe(level + 1);
	}

	@Override
	protected String toString(int offset, int prec, boolean raw) {
		return isProp ? "Prop" : level == 0 ? "U" : "U"+level;
	}

	public int getLevel() {
		return level;
	}

	public boolean isSubTypeHead(Term t) {
		return (t instanceof UniverseTerm
				&& level <= ((UniverseTerm) t).getLevel()
				&& (isProp || !((UniverseTerm) t).isProp()));
	}
}
