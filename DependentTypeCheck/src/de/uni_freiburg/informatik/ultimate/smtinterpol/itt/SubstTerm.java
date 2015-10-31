package de.uni_freiburg.informatik.ultimate.smtinterpol.itt;

/**
 * A subst term is a term on which a substitution is applied.  Instead
 * of applying the substitution eagerly, we collect all substitution and
 * only apply them lazily when descending into the term.
 * 
 * @author hoenicke
 */
public class SubstTerm extends Term {
	
	Term mSubTerm;
	Substitution mSubstitution;
	
	Term mEvaluated;
	int mNumFreeVariables;
	
	public SubstTerm(Term term, Substitution subst, Term type) {
		super(type);
		mSubTerm = term;
		mSubstitution = subst;
		mNumFreeVariables = subst.numFreeVariables(term.numFreeVariables());
	}
	
	@Override
	public int numFreeVariables() {
		return mNumFreeVariables;
	}

	/**
	 * Compute the type of a substituted term.  This is the type of 
	 * the subterm substituted with the same substitution.
	 * @param term the sub term.
	 * @param subst the substitution.
	 * @return the type of the SubstTerm.
	 */
	public static Term typecheck(Term term, Substitution subst) {
		// TODO check substitution?
		Term type = term.getType();
		/* avoid deep recursions */
		if (type.numFreeVariables() == 0)
			return type;
		return Term.substitute(type, subst, null);
	}
	
	@Override
	public Term evaluateHead() {
		if (mEvaluated != null)
			return mEvaluated;
		Term evaluated;
		if (mSubTerm instanceof SubstTerm) {
			SubstTerm subsubst = (SubstTerm) mSubTerm;
			evaluated = Term.substitute(subsubst.mSubTerm,
					Substitution.compose(subsubst.mSubstitution, mSubstitution,
							subsubst.mSubTerm.numFreeVariables()),
							getType());
		} else if (mSubTerm instanceof AppTerm) {
			AppTerm app = (AppTerm) mSubTerm;
			evaluated = Term.application(
					Term.substitute(app.mFunc, mSubstitution, null),
					Term.substitute(app.mArg, mSubstitution, null), 
					getType());
		} else if (mSubTerm instanceof LambdaTerm) {
			LambdaTerm lam = (LambdaTerm) mSubTerm;
			Term substArg = Term.substitute(lam.mArgType, mSubstitution, null);
			Substitution shifted = Substitution.consShifted(
					Term.variable(0, substArg), mSubstitution,
					lam.mSubTerm.numFreeVariables());
			evaluated = new LambdaTerm(
					substArg,
					Term.substitute(lam.mSubTerm, shifted, null), 
					getType());
		} else if (mSubTerm instanceof PiTerm) {
			PiTerm pi = (PiTerm) mSubTerm;
			Term substArg = Term.substitute(pi.mDomain, mSubstitution, null);
			Substitution shifted = Substitution.consShifted(
					Term.variable(0, substArg), mSubstitution,
					pi.mRange.numFreeVariables());
			evaluated = new PiTerm(
					substArg,
					Term.substitute(pi.mRange, shifted, null), 
					getType(), pi.mIsHidden);
		} else if (mSubTerm instanceof Variable) {
			if (mSubstitution.mSubstTerms.length == 0)
				return (mEvaluated = this);
			else
				evaluated = mSubstitution.mSubstTerms[0];
		} else {
			/* term is Universe, Constructor, RecOp, or InductiveType, 
			 * or assumption */
			assert mSubTerm instanceof UniverseTerm
					|| mSubTerm instanceof Constructor
					|| mSubTerm instanceof InductiveType
					|| mSubTerm instanceof RecOperator
					|| mSubTerm instanceof Assumption;
			evaluated = mSubTerm;
		}
		if (evaluated.mName == null && mName != null)
			evaluated.mName = mName;
		mEvaluated = evaluated.evaluateHead();
		assert !(mEvaluated instanceof SubstTerm) ||
			(((SubstTerm) mEvaluated).mSubTerm instanceof Variable);
		//System.err.println("EvaluateHead: "+this + " gives "+mEvaluated);
		return mEvaluated;
	}

	@Override
	protected String toString(int offset, int prec) {
		if (mSubTerm instanceof Variable
			&& mSubstitution.mSubstTerms.length == 0) {
			int index = mSubstitution.mShiftOffset;
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
		return mSubstitution.mShiftOffset
				== other.mSubstitution.mShiftOffset;
	}
}
