package de.uni_freiburg.informatik.ultimate.smtinterpol.itt;

/**
 * This class represents a function type, i.e., the set/class of functions
 * from a domain to a range.  The domain and range must be sets or classes,
 * i.e., their type must be U or null.  The range can depend on the
 * parameter of the function.  This is achieved using de Bruijn indexed
 * variables.  The range can contain a de Bruijn variable bound by this
 * PiTerm whose type is the domain.
 * 
 * @author hoenicke
 */
public class PiTerm extends Term {
	Term mDomain;
	Term mRange;
	
	public PiTerm(Term domain, Term range) {
		this(domain, range, typecheck(domain, range));
	}
	public PiTerm(Term domain, Term range, Term type) {
		super(type);
		assert type == null ? typecheck(domain,range) == null
				: type.equals(typecheck(domain, range));
		this.mDomain = domain;
		this.mRange = range;
	}
	
	/**
	 * Compute the type of a pi term with the given arguments.
	 * The type is either U or null.  It is null if the 
	 * <em>type of</em> one of its arguments is null.  The arguments
	 * are never null.
	 * @param domain the domain type, its type must be U or null.
	 * @param range the range type, its type must be U or null.
	 * @return the type of the pi term.
	 */
	public static Term typecheck(Term domain, Term range) {
		Term domType = domain.getType();
		Term rngType = range.getType();
		if (domType != null)
			domType = domType.evaluateHead();
		if (rngType != null)
			rngType = rngType.evaluateHead();
		if (domType == Term.U && rngType == Term.U)
			return Term.U;
		if ((domType != Term.U && domType != null)
				|| (rngType != Term.U && rngType != null))
			throw new IllegalArgumentException("Typecheck: PI");
		return null;
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
