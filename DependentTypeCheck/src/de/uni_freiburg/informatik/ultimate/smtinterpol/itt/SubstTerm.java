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
	
	public SubstTerm(Term term, Substitution subst, Term type) {
		super(type);
		mSubTerm = term;
		mSubstitution = subst;
		mNumFreeVariables = subst.numFreeVariables(term.numFreeVariables());
	}
	
	public Term getType() {
		if (mType == null) {
			Term me = evaluateHead();
			if (me == this) {
				assert mSubstitution.mSubstTerms.length == 0;
 				mType = Term.substitute(mSubTerm.getType(),	
 						Substitution.shift(mSubstitution.mShiftOffset),
 						null);
			} else {
				mType = me.getType();
			}
		}
		return mType;
	}
	
	@Override
	public Term evaluateHead() {
		if (mEvaluated != null)
			return mEvaluated;
		Term evaluated;
		if (mSubTerm instanceof SubstTerm) {
			SubstTerm subsubst = (SubstTerm) mSubTerm;
			if (subsubst.mSubTerm instanceof Variable
				&& subsubst.mSubstitution.mSubstTerms.length == 0) {
				int offset = subsubst.mSubstitution.mShiftOffset;
				if (offset < mSubstitution.mSubstTerms.length)
					evaluated = mSubstitution.mSubstTerms[offset];
				else {
					offset += mSubstitution.mShiftOffset -
							mSubstitution.mSubstTerms.length;
					evaluated = Term.substitute(subsubst.mSubTerm,
							Substitution.shift(offset),
							mType);
				}
			} else {
				evaluated = Term.substitute(subsubst.mSubTerm,
						Substitution.compose(subsubst.mSubstitution, 
								mSubstitution,
								subsubst.mSubTerm.numFreeVariables()),
						mType);
			}
		} else if (mSubTerm instanceof AppTerm) {
			AppTerm app = (AppTerm) mSubTerm;
			evaluated = Term.application(
					Term.substitute(app.mFunc, mSubstitution, null),
					Term.substitute(app.mArg, mSubstitution, null), 
					mType);
		} else if (mSubTerm instanceof LambdaTerm) {
			LambdaTerm lam = (LambdaTerm) mSubTerm;
			Term substArg = Term.substitute(lam.mArgType, mSubstitution, null);
			Substitution shifted = Substitution.consShifted(
					Term.variable(0, substArg), mSubstitution,
					lam.mSubTerm.numFreeVariables());
			evaluated = Term.lambda(
					substArg,
					Term.substitute(lam.mSubTerm, shifted, null), 
					mType);
		} else if (mSubTerm instanceof PiTerm) {
			PiTerm pi = (PiTerm) mSubTerm;
			Term substArg = Term.substitute(pi.mDomain, mSubstitution, null);
			Substitution shifted = Substitution.consShifted(
					Term.variable(0, substArg), mSubstitution,
					pi.mRange.numFreeVariables());
			evaluated = Term.pi(substArg,
					Term.substitute(pi.mRange, shifted, null), 
					mType);
		} else if (mSubTerm instanceof Variable) {
			if (mSubstitution.mSubstTerms.length == 0) {
				return (mEvaluated = this);
			} else {
				assert mSubstitution.mSubstTerms[0].getType().isSubType(
						Term.substitute(mSubTerm.getType(), mSubstitution, null));
				evaluated = mSubstitution.mSubstTerms[0];
			}
		} else if (mSubTerm instanceof Assumption) {
			Assumption assump = (Assumption) mSubTerm;
			evaluated = new Assumption(assump.toString(), 
					Term.substitute(assump.getType(), mSubstitution, null));
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
		return mEvaluated;
	}

	@Override
	protected String toString(int offset, int prec) {
		if (mSubTerm instanceof Variable
			&& mSubstitution.mSubstTerms.length == 0) {
			int index = mSubstitution.mShiftOffset;
			return "@" + (offset - index - 1);
		}
		
		String str = mSubTerm.toString(offset, 3) + "[" 
				+ mSubstitution.toString(offset, 0) + "]";
		return prec >= 4 ? "(" + str + ")" : str;
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
