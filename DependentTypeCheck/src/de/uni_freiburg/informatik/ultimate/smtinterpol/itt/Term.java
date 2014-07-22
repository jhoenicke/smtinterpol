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
 * {@link Variable},
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
	};

	public Term(Term type) {
		mType = type;
	}
	
	@SuppressWarnings("unused")
	private Term() {}
	
	public Term getType() {
		return mType == null ? null : mType;
	}
	
	/**
	 * Converts the outer-most symbols of the term to normal form.  We stop
	 * when the head is a PiTerm, a LambdaTerm, or an AppTerm where no further
	 * beta-reduction or J-reduction can be performed.
	 */
	public Term evaluateHead() {
		return this;
	}

	public String toString() {
		return toString(1, 0);
	}

	public int numVariable() {
		return 0;
	}

	protected abstract String toString(int offset, int prec);
	
	public boolean equalsHead(Term t) {
		return this == t;
	}
	
	public final boolean equals(Object o) {
		if (this == o)
			return true;
		if (!(o instanceof Term))
			return false;
		Term me = evaluateHead();
		if (me == o)
			return true;
		Term other = ((Term) o).evaluateHead();
		if (me == other)
			return true;
		boolean result = me.equalsHead(other);
		if (!result) {
			System.err.println("Unequal: " + this + " != " + o);
			System.err.println("evaled head: " + me + " != " + other);
		}
		return result;
	}
	
	public static Term application(Term func, Term arg, Term type) {
		assert type == null || type.equals(AppTerm.typecheck(func, arg));
		if (type == null)
			type = AppTerm.typecheck(func, arg);
		return new AppTerm(func, arg, type);
	}

	public static Term lambda(Term domain, Term value, Term type) {
		assert type == null || type.equals(LambdaTerm.typecheck(domain, value));
		if (type == null)
			type = LambdaTerm.typecheck(domain, value);
		return new LambdaTerm(domain, value, type);
	}

	public static Term pi(Term domain, Term range, Term type) {
		assert type == null || type.equals(PiTerm.typecheck(domain, range));
		if (type == null)
			type = PiTerm.typecheck(domain, range);
		return new PiTerm(domain, range, type);
	}

	public static Term substitute(Term term, Substitution subst, Term type) {
		assert type == null || type.equals(SubstTerm.typecheck(term, subst));
		if (type == null)
			type = SubstTerm.typecheck(term, subst);
		return new SubstTerm(term, subst, type);
	}

	public static Term variable(int offset, Term type) {
		return substitute(new Variable(substitute(type, Substitution.shift(1), null)), Substitution.shift(offset), null);
	}

	public Term evaluate() {
		Term t = evaluateHead();
		if (t instanceof AppTerm) {
			AppTerm app = (AppTerm) t;
			return Term.application(
					app.mFunc.evaluate(),
					app.mArg.evaluate(), t.getType());
		} else if (t instanceof PiTerm) {
			PiTerm pi = (PiTerm) t;
			return Term.pi(
					pi.mDomain.evaluate(),
					pi.mRange.evaluate(), t.getType());
		} else if (t instanceof LambdaTerm) {
			LambdaTerm lam = (LambdaTerm) t;
			return Term.lambda(
					lam.mArgType.evaluate(),
					lam.mSubTerm.evaluate(), t.getType());
		} else {
			return t;
		}
	}
}
