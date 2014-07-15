package de.uni_freiburg.informatik.ultimate.smtinterpol.itt;

/**
 * This class represents a function application.  It has two sub terms
 * func and arg.  The first parameter func must be a function (i.e. its type
 * is a PiTerm).  The type of the second parameter arg must be equal to
 * the domain of the function type.  The type of the app term is now the
 * range of the function type, where the variable bound by the PiTerm is
 * replaced by arg.
 * @author hoenicke
 *
 */
public class AppTerm extends Term {
	Term mFunc, mArg;
	
	Term mEvaluated;

	public AppTerm(Term func, Term arg, Term type) {
		super(type);
		assert type.equals(typecheck(func, arg));
		mFunc = func;
		mArg = arg;
	}
	
	public AppTerm(Term func, Term arg) {
		super(typecheck(func, arg));
		mFunc = func;
		mArg = arg;
	}
	
	public static Term typecheck(Term func, Term arg) {
		Term funcType = func.getType();
		if (!(funcType instanceof PiTerm)) {
			throw new IllegalArgumentException("Typecheck: applying a non-function");
		}
		PiTerm pi = (PiTerm) funcType;
		if (!pi.mDomain.equals(arg.getType()))
			throw new IllegalArgumentException("Typecheck: function parameter has wrong type");
		// note that type != null
		return pi.mRange.substitute(new Term[] {arg}, 0).evaluate();
	}

	@Override
	public Term evaluate() {
		if (mEvaluated == null) {
			mEvaluated = myEvaluate(mFunc.evaluate(), mArg.evaluate(), getType());
		}
		return mEvaluated;
	}
	
	public Term myEvaluate(Term f, Term a, Term type) {
		if (f instanceof LambdaTerm) {
			// beta-reduction
			return ((LambdaTerm) f).mSubTerm.substitute(new Term[] { a }, 0)
					.evaluate();
		}
		/* check for J operator */
		AppTerm result = f == mFunc && a == mArg ? this 
				: new AppTerm(f, a, type);
		int numArgs = 1;
		while (f instanceof AppTerm) {
			f = ((AppTerm) f).mFunc;
			numArgs++;
		}
		if (f instanceof JOperator) {
			JOperator j = (JOperator) f;
			assert numArgs <= j.getNumArgs();
			if (numArgs == j.getNumArgs()) {
				return j.applyJ(result);
			}
		}
		/* evaluation fix point reached */
		result.mEvaluated = result;
		return result;
	}

	@Override
	public Term substitute(Term[] t, int offset) {
		Term func = mFunc.substitute(t, offset);
		Term arg  = mArg.substitute(t, offset);
		Term type = getType().substitute(t, offset);
		return new AppTerm(func, arg, type);
	}

	/**
	 * Shift de Bruijn indices >= start by offset.
	 * @param start  The first index to modify.
	 * @param offset The offset added to the index.
	 * @return the substituted term.
	 */
	@Override
	public Term shiftBruijn(int start, int offset) {
		return new AppTerm(mFunc.shiftBruijn(start, offset),
				mArg.shiftBruijn(start, offset),
				getType().shiftBruijn(start, offset));
	}
	
	public String toString(int offset, int prec) {
		String str = mFunc.toString(offset, 1) + " " 
				+ mArg.toString(offset, 2);
		return prec >= 2 ? "(" + str + ")" : str;
	}
	
	public boolean equals(Object o) {
		if (this == o)
			return true;
		if (!(o instanceof AppTerm))
			return false;
		AppTerm other = (AppTerm) o;
		return mFunc.equals(other.mFunc) && mArg.equals(other.mArg);
	}
}