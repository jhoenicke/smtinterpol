package de.uni_freiburg.informatik.ultimate.smtinterpol.itt;

import java.util.Arrays;

/**
 * Everything is a term.  Every term has a type, which is again a term.  By
 * abuse of notation the term U representing the universe also has type U.
 * Strictly speaking U_0 should have type U_1 and so on, but we never need
 * the index, so we drop it in our representation.  Note that due to our
 * restricted way of building terms this cannot lead to a contradiction.
 * 
 * There are functions an function types, the latter is always represented by
 * a PiTerm.  We distinguish the following terms by their type:
 * 
 * <ul>
 * <li>A <em>type</em> is a term with type U.  Function types are also 
 * types.</li>
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
 * {@link RecOperator}, {@link Constructor}, {@link InductiveType}.
 * However we sometimes rewrite terms to a normal form, which may change the
 * Java class used to represent the term.
 * 
 * A term is evaluated to a normal form by applying beta-reduction and
 * recursion (see {@link RecOperator}).  We always evaluate the type of a term, 
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
	/**
	 * The free variable with the maximal index plus one.
	 */
	int mNumFreeVariables;
	/**
	 * The name of the term.  This is set for defined terms.
	 */
	PrettyTerm mName;
	
	private static Term[] universes = new Term[2];

	public Term(Term type) {
		mType = type;
	}
	
	@SuppressWarnings("unused")
	private Term() {}
	
	public Term getType() {
		return mType;
	}
	
	/**
	 * Converts the outer-most symbols of the term to normal form.  We stop
	 * when the head is a PiTerm, a LambdaTerm, or an AppTerm where no further
	 * beta-reduction or recursion-reduction can be performed.
	 */
	public Term evaluateHead() {
		return this;
	}

	public String toString() {
		return toString(0, 0);
	}

	public final int numFreeVariables() {
		return mNumFreeVariables;
	}

	protected abstract String toString(int offset, int prec);
	
	public boolean equalsHead(Term t) {
		return this == t;
	}
	
	public boolean isSubTypeHead(Term t) {
		return this.equalsHead(t);
	}
	
	public boolean isSubType(Term t) {
		if (this == t)
			return true;
		Term me = evaluateHead();
		if (me == t)
			return true;
		Term other = t.evaluateHead();
		if (me == other)
			return true;
		boolean result = me.isSubTypeHead(other);
		if (!result) {
			System.err.println("Not Subtype: " + me.evaluate());
			System.err.println(" is !=       " + other.evaluate());
		}
		return result;
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
			System.err.println("Unequal: " + me.evaluate());
			System.err.println(" is !=   " + other.evaluate());
		}
		return result;
	}
	
	public static Term universe(int level) {
		if (level >= universes.length) {
			universes = Arrays.copyOf(universes, level + 1);
		}
		if (universes[level] == null) {
			universes[level] = new UniverseTerm(level);
		}
		return universes[level];
	}

	/**
	 * Create an application term.
	 * @param func the function.
	 * @param arg  the argument.
	 * @param type the type of the appliation term.  This is 
	 *   computed if it is null.
	 * @return the application term
	 */
	public static Term application(Term func, Term arg, Term type) {
		if (type == null) {
			type = ((PiTerm) func.getType().evaluateHead()).mRange;
			if (type.numFreeVariables() > 0) {
				Substitution subst = new Substitution(new Term[] { arg }, 0);
				type = Term.substitute(type, subst, null);
			}
		}
		assert AppTerm.typecheck(func, arg).equals(type);
		return new AppTerm(func, arg, type);
	}

	/**
	 * Create an application term introducing possibly hidden arguments.
	 * @param func the function.
	 * @param arg  the argument.
	 * @return the application term
	 */
	public static Term buildApplication(Term func, Term arg) {
		Term funcType = func.getType().evaluateHead();
		Term argType = arg.getType().evaluateHead();
		if (!(funcType instanceof PiTerm))
			throw new IllegalArgumentException("Applying to a non-function");
		PiTerm pi = (PiTerm) funcType;
		func = pi.instantiateHiddenArguments(func, arg);
		pi = (PiTerm) func.getType().evaluateHead();
		if (!argType.isSubType(pi.mDomain))
			throw new IllegalArgumentException(
					"Argument has wrong type " + argType.evaluate() + 
					" expected: " + pi.mDomain.evaluate());
		return Term.application(func, arg, null);	
	}

	/**
	 * Create a lambda term.
	 * @param domain The type of the bounded variable.
	 * @param value The subexpression of the lambda term.
	 * @param type The type of the lambda expression.  If this is null
	 * it is computed and checked.
	 * @return the labmda term.
	 */
	public static Term lambda(Term domain, Term value, Term type) {
		assert type == null || LambdaTerm.typecheck(domain, value).equals(type);
		if (type == null)
			type = LambdaTerm.typecheck(domain, value);
		return new LambdaTerm(domain, value, type);
	}

	/**
	 * Create a pi term.
	 * @param domain The domain (the type of the bounded variable).
	 * @param value The range (containing the variable).
	 * @param type The type of the pi expression.  If this is null
	 * it is computed and checked.
	 * @return the labmda term.
	 */
	public static Term pi(Term domain, Term range, Term type) {
		assert type == null || PiTerm.typecheck(domain, range).equals(type);
		if (type == null)
			type = PiTerm.typecheck(domain, range);
		return new PiTerm(domain, range, type);
	}

	/**
	 * Create a substituted term.
	 * @param domain The domain (the type of the bounded variable).
	 * @param value The range (containing the variable).
	 * @param type The type of the pi expression.  If this is null
	 * it is computed and checked.
	 * @return the labmda term.
	 */
	public static Term substitute(Term term, Substitution subst, Term type) {
		if (term.numFreeVariables() == 0)
			return term;
		if (subst.mShiftOffset == 0 && subst.mSubstTerms.length == 0
				&& !(term instanceof Variable))
			return term;
		Term substterm = new SubstTerm(term, subst, type);
		if (term.mName != null)
			substterm.mName = term.mName.substitute(subst);
		assert type == null || substterm.evaluateHead().getType().equals(type);
		return substterm;
	}

	/**
	 * Create a variable.  A variable is always represented by a 
	 * substituted term where the subterm is a Variable and the 
	 * substitution is a simple shift by offset.
	 * @param offset the de-Bruijn offset of the variable.
	 * @param type the type of the variable.
	 * @return a term representing the variable.
	 */
	public static Term variable(int offset, Term type) {
		// We need to shift the type, because the deBruijn index 0 would now
		// reference the variable itself.  We only shift it by 1, the offset
		// shift is implicit in substitute.
		type = substitute(type, Substitution.shift(1), null);
		return substitute(new Variable(type), Substitution.shift(offset), null);
	}

	public Term evaluate() {
		Term t = evaluateHead();
		PrettyTerm name = t.mName;
		if (t instanceof AppTerm) {
			AppTerm app = (AppTerm) t;
			Term func = app.mFunc.evaluate();
			Term arg = app.mArg.evaluate();
			if (func != app.mFunc || arg != app.mArg) {
				t = Term.application(func, arg, t.getType());
			}
		} else if (t instanceof PiTerm) {
			PiTerm pi = (PiTerm) t;
			Term dom = pi.mDomain.evaluate();
			Term rng = pi.mRange.evaluate();
			if (dom != pi.mDomain || rng != pi.mRange) {
				t = Term.pi(dom, rng, t.getType());
			}
		} else if (t instanceof LambdaTerm) {
			LambdaTerm lam = (LambdaTerm) t;
			Term arg = lam.mArgType.evaluate();
			Term sub = lam.mSubTerm.evaluate();
			if (arg != lam.mArgType || sub != lam.mSubTerm) {
				t = Term.lambda(arg, sub, t.getType());
			}
		}
		t.mName = name;
		return t;
	}
	
	public void setName(String name) {
		mName = PrettyTerm.name(name);
	}
}
