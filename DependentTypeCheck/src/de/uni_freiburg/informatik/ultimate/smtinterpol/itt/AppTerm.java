package de.uni_freiburg.informatik.ultimate.smtinterpol.itt;
import java.util.ArrayDeque;

public class AppTerm extends Term {
	Term mFunc, mArg;

	public AppTerm(Term func, Term arg) {
		this(func, arg, typecheck(func, arg));
	}
	
	public AppTerm(Term func, Term arg, Term type) {
		super(type);
		mFunc = func;
		mArg = arg;
	}
	
	private static Term typecheck(Term func, Term arg) {
		Term funcType = func.getType();
		if (!(funcType instanceof PiTerm)) {
			throw new IllegalArgumentException("Typecheck: applying a non-function");
		}
		PiTerm pi = (PiTerm) funcType;
		if (!pi.mDomain.equals(arg.getType()))
			throw new IllegalArgumentException("Typecheck: function parameter has wrong type");
		return pi.mRange.substituteAndEval(arg, 0);
	}

	@Override
	public Term internalEval() {
		return myEvaluate(mFunc.evaluate(), mArg.evaluate(), getType());
	}
	
	public Term myEvaluate(Term f, Term a, Term type) {
		if (f instanceof LambdaTerm) {
			// beta-reduction
			return ((LambdaTerm) f).mSubTerm.substituteAndEval(a, 0);
		}
		Term result = f == mFunc && a == mArg ? this 
					: new AppTerm(f, a, type);

		/* check for J operator */
		ArrayDeque<Term> args = new ArrayDeque<Term>();
		args.addFirst(a);
		while (f instanceof AppTerm) {
			AppTerm app = (AppTerm) f;
			args.addFirst(app.mArg);
			f = app.mFunc;
		}
		if (f instanceof JOperator) {
			JOperator j = (JOperator) f;
			if (args.size() == j.getNumArgs()) {
				return j.applyArgs(result, args);
			}
		}
		return result;
	}

	@Override
	public Term substituteAndEval(Term t, int offset) {
		Term f = mFunc.substituteAndEval(t, offset);
		Term a = mArg.substituteAndEval(t, offset);
		return myEvaluate(f, a, getType().substituteAndEval(t, offset));
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