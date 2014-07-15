package de.uni_freiburg.informatik.ultimate.smtinterpol.itt;

/**
 * Everything is a term.  Every term has a type, which is again a term, or it
 * is null for classes (to avoid an infinite type hierarchy).
 * 
 * There are functions an function types, the latter is always represented by
 * a PiTerm.  We distinguish the following terms by their type:
 * 
 * <ul><li>
 * A <em>class</em> is a term with type null.  A class is either a PiTerm 
 * (a function type) where domain or range is a class, or it is the special
 * class U, which represents the class of all sets.
 * </li>
 * 
 * <li>A <em>set</em> is a term with type U.  Function types are also sets
 * if they are not classes.</li>
 * 
 * <li>A <em>function</em> is a term with a function type, i.e., a type that 
 * is a PiTerm.  The function type is either a set or a class.  A function
 * term can also contain classes like U as argument type in a lambda term. 
 * This can be used to represent polymorphic functions.</li>
 * 
 * <li>Every other term is called an <em>element</em>. Its type is always a 
 * set, i.e., the type of its type is U.</li> 
 * </ul>
 * 
 * A function type, i.e. a PiTerm, is always a set or a class.
 * We also distinguish terms by the Java class hierarchy, i.e.,
 * {@link PiTerm}, {@link LambdaTerm}, {@link AppTerm}, 
 * {@link DeBruijnVariable},
 * {@link JOperator}, {@link Constructor}, {@link InductiveType}.
 * However we sometimes rewrite terms to a normal form, which may change the
 * Java class used to represent the term.
 * 
 * A term is evaluated to a normal form by applying beta-reduction and
 * recursion (see {@link JOperator}).  We always evaluate the type of a term, 
 * i.e., the type is always in normal form.  We only allow to build terms that
 * are well-typed and compute the type of each term (in normal form) before
 * building a term.  This ensures that a term is always a "real" object (at
 * least if it is not a class or a polymorphic function).
 * 
 * @author Jochen Hoenicke
 */
public abstract class Term {
	/**
	 * The type of the term.  This is always in normal form.  It is null
	 * for classes.
	 */
	Term mType;
	
	public final static Term U = new Term(null) {
		public String toString(int offset, int prec) { return "U"; }
		public boolean equals(Object o) {
			return (this == o);
		}
	};

	public Term(Term type) {
		mType = type;
	}
	
	@SuppressWarnings("unused")
	private Term() {}
	
	public Term getType() {
		return mType;
	}
	
	/**
	 * Returns the normal form of the term.  This applies beta rewriting
	 * and recursion.  This must be overridden by all terms that are not
	 * necessarily in normal form.
	 */
	public Term evaluate() {
		return this;
	}
	
	/**
	 * Substitute in the current term the de Bruijn parameters with index 
	 * offset and above with the terms from the array t.  The variable with
	 * larger de Bruijn indices are decremented accordingly.
	 * Also the types are substituted accordingly.
	 * @param t The terms to substitute.  Note that t[0] corresponds to
	 *   de Bruijn index 0, therefore it is the right most parameter.
	 * @param offset the de Bruijn index that should be substituted
	 * @return the substituted and evaluated term.
	 */
	public Term substitute(Term[] t, int offset) {
		return this;
	}
	
	/**
	 * Shift de Bruijn indices >= start by offset.
	 * @param start  The first index to modify.
	 * @param offset The offset added to the index.
	 * @return the substituted term.
	 */
	public Term shiftBruijn(int start, int offset) {
		return this;
	}
	
	public String toString() {
		return toString(0, 0);
	}
	
	protected abstract String toString(int offset, int prec);
	public abstract boolean equals(Object t);
}
