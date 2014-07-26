package de.uni_freiburg.informatik.ultimate.smtinterpol.itt;

/**
 * This class represents a function type, i.e., the set/class of functions
 * from a domain to a range.  The domain and range must be sets or classes,
 * i.e., their type must be U.  The range can depend on the
 * parameter of the function.  This is achieved using de Bruijn indexed
 * variables.  The range can contain a de Bruijn variable bound by this
 * PiTerm whose type is the domain.
 * 
 * @author hoenicke
 */
public class PiTerm extends Term {
	Term mDomain;
	Term mRange;
	int mNumFreeVariables;
	
	public PiTerm(Term domain, Term range) {
		this(domain, range, typecheck(domain, range));
	}
	public PiTerm(Term domain, Term range, Term type) {
		super(type);
		assert type.equals(typecheck(domain, range));
		this.mDomain = domain;
		this.mRange = range;
		mNumFreeVariables = Math.max(mDomain.numFreeVariables(), 
				mRange.numFreeVariables() - 1);
	}
	
	@Override
	public int numFreeVariables() {
		return mNumFreeVariables;
	}
	
	/**
	 * Compute the type of a pi term with the given arguments.
	 * The type is always U.  We also check that the domain and range
	 * have type U.
	 * @param domain the domain type, its type must be U.
	 * @param range the range type, its type must be U.
	 * @return the type of the pi term.
	 */
	public static Term typecheck(Term domain, Term range) {
		Term domType = domain.getType();
		Term rngType = range.getType();
		if (domType.equals(Term.U) && rngType.equals(Term.U))
			return Term.U;
		throw new IllegalArgumentException("Typecheck: PI");
	}

	@Override
	public Term evaluateHead() {
		return this;
	}

	public String toString(int offset, int prec) {
		String str = "@" + offset + " : " + mDomain.toString(offset,1)
				+ " -> " + mRange.toString(offset + 1, 0);
		return prec >= 1 ? "(" + str + ")" : str;
	}

	public boolean equalsHead(Term o) {
		if (!(o instanceof PiTerm))
			return false;
		PiTerm other = (PiTerm) o;
		return mDomain.equals(other.mDomain) && mRange.equals(other.mRange);
	}
}
