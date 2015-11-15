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
		//Expensive assert:
		//assert typecheck(func, arg).equals(type);
		mFunc = func;
		mArg = arg;
		mNumFreeVariables = 
				Math.max(func.numFreeVariables(), arg.numFreeVariables());
	}
	
	public AppTerm(Term func, Term arg) {
		this(func, arg, typecheck(func, arg));
	}
	
	public static Term typecheck(Term func, Term arg) {
		Term funcType = func.getType().evaluateHead();
		if (!(funcType instanceof PiTerm)) {
			throw new IllegalArgumentException("Typecheck: applying a non-function");
		}
		PiTerm pi = (PiTerm) funcType;
		if (!arg.getType().isSubType(pi.mDomain))
			throw new IllegalArgumentException("Typecheck: function parameter has wrong type");
		// note that type != null
		return Term.substitute(pi.mRange, Substitution.unit(arg), null);
	}

	@Override
	public Term evaluateHead() {
		if (mEvaluated == null) {
			mEvaluated = myEvaluate(mFunc.evaluateHead(), mArg, getType());
		}
		return mEvaluated;
	}
	
	public Term myEvaluate(Term f, Term a, Term type) {
		PrettyTerm name = null;
		if (mName != null) {
			name = mName;
		} else if (f.mName != null) {
			name = PrettyTerm.application(f.mName, a);
		}
		if (f instanceof LambdaTerm) {
			Term head = Term.substitute(((LambdaTerm) f).mSubTerm, 
					Substitution.unit(a),
					getType());
			head.mName = name;
			return head.evaluateHead();
		}
		AppTerm result = f == mFunc && a == mArg ? this 
				: new AppTerm(f, a, type);
		/* check for Rec operator */
		int numArgs = 1;
		while (f instanceof AppTerm) {
			f = ((AppTerm) f).mFunc;
			numArgs++;
		}
		if (f instanceof RecOperator) {
			RecOperator rec = (RecOperator) f;
			if (numArgs == rec.getNumArgs()) {
				return rec.applyRec(result);
			}
		}
		/* evaluation fix point reached */
		if (name != null)
			result.mName = name;
		result.mEvaluated = result;
		return result;
	}

	public String toString(int offset, int prec) {
		if (mName != null)
			return mName.toString(offset, prec);
		String str = mFunc.toString(offset, 2) + " " 
				+ mArg.toString(offset, 3);
		return prec >= 3 ? "(" + str + ")" : str;
	}
	
	public boolean equalsHead(Term o) {
		if (!(o instanceof AppTerm))
			return false;
		AppTerm other = (AppTerm) o;
		return mFunc.equals(other.mFunc) && mArg.equals(other.mArg);
	}
}
