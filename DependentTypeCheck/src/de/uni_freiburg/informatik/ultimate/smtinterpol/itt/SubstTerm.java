package de.uni_freiburg.informatik.ultimate.smtinterpol.itt;

public class SubstTerm extends Term {
	
	Term mSubTerm;
	Substitution mSubstitution;
	
	Term mEvaluated;
	
	public SubstTerm(Term term, Substitution subst, Term type) {
		super(type);
		mSubTerm = term;
		mSubstitution = subst;
	}
	
	public static Term typecheck(Term term, Substitution subst) {
		// TODO check substitution?
		Term type = term.getType();
		/* avoid deep recursions */
		if (type == Term.U || type == null)
			return type;
		return Term.substitute(type, subst, null);
	}
	
	@Override
	public Term evaluateHead() {
		if (mEvaluated != null)
			return mEvaluated;
		if (mSubTerm instanceof SubstTerm) {
			SubstTerm subsubst = (SubstTerm) mSubTerm;
			mEvaluated = Term.substitute(subsubst.mSubTerm,
					Substitution.compose(subsubst.mSubstitution, mSubstitution),
					getType()).
					evaluateHead();
		} else if (mSubTerm instanceof AppTerm) {
			AppTerm app = (AppTerm) mSubTerm;
			mEvaluated = Term.application(
					Term.substitute(app.mFunc, mSubstitution, null),
					Term.substitute(app.mArg, mSubstitution, null), 
					getType()).evaluateHead();
		} else if (mSubTerm instanceof LambdaTerm) {
			LambdaTerm lam = (LambdaTerm) mSubTerm;
			Term substArg = Term.substitute(lam.mArgType, mSubstitution, null);
			Substitution shifted = Substitution.cons(
					Term.variable(0, substArg),
					Substitution.compose(mSubstitution, Substitution.shift(1)));
			mEvaluated = new LambdaTerm(
					substArg,
					Term.substitute(lam.mSubTerm, shifted, null), 
					getType());
		} else if (mSubTerm instanceof PiTerm) {
			PiTerm pi = (PiTerm) mSubTerm;
			Term substArg = Term.substitute(pi.mDomain, mSubstitution, null);
			Substitution shifted = Substitution.cons(
					Term.variable(0, substArg),
					Substitution.compose(mSubstitution, Substitution.shift(1)));
			mEvaluated = new PiTerm(
					substArg,
					Term.substitute(pi.mRange, shifted, null), 
					getType()).evaluateHead();
		} else if (mSubTerm instanceof Variable) {
			Substitution subst = mSubstitution.evaluateHead();
			if (subst instanceof Substitution.Cons) {
				mEvaluated = ((Substitution.Cons) subst).mHead.evaluateHead();
			} else {
				assert subst instanceof Substitution.Shift;
				if (subst == mSubstitution) {
					mEvaluated = this;
				} else {
					mEvaluated = Term.substitute(mSubTerm, subst, getType());
					((SubstTerm) mEvaluated).mEvaluated = mEvaluated;
				}
			}
		} else {
			/* term is Constructor, JOp, or InductiveType */
			assert mSubTerm == Term.U || mSubTerm instanceof Constructor
					|| mSubTerm instanceof InductiveType
					|| mSubTerm instanceof JOperator;
			mEvaluated = mSubTerm;
		}
		assert !(mEvaluated instanceof SubstTerm) ||
			(((SubstTerm) mEvaluated).mSubTerm instanceof Variable);
		//System.err.println("EvaluateHead: "+this + " gives "+mEvaluated);
		return mEvaluated;
	}

	@Override
	protected String toString(int offset, int prec) {
		if (mSubTerm instanceof Variable
			&& mSubstitution instanceof Substitution.Shift) {
			int index = ((Substitution.Shift) mSubstitution).mOffset;
			return "@" + (offset - index - 1);
		}
		
		String str = mSubTerm.toString(offset, 2) + "[" 
				+ mSubstitution.toString(0) + "]";
		return prec >= 2 ? "(" + str + ")" : str;
	}

	@Override
	public boolean equalsHead(Term o) {
		assert mSubTerm instanceof Variable;
		if (!(o instanceof SubstTerm))
			return false;
		SubstTerm other = (SubstTerm) o;
		assert other.mSubTerm instanceof Variable;
		return ((Substitution.Shift) mSubstitution).mOffset
				== ((Substitution.Shift) other.mSubstitution).mOffset;
	}
}
