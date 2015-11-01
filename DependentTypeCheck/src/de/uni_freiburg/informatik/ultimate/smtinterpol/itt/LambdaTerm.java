package de.uni_freiburg.informatik.ultimate.smtinterpol.itt;

/**
 * This class represents lambda terms.  The type of a lambda term is
 * always a function type, i.e., getType() is an instance of {@link PiTerm}.
 * A lambda term has an argument type and a sub term (the parameter is
 * implemented by a de Bruijn indexed variable and has no representation).
 * The argument type must be a set or a class and is also the domain of the
 * function type.  The sub term has a new de Bruijn accessible variable
 * whose type is the argument type.  The sub term must not be a class.  Its
 * type is equal to the range type of the function and it can reference the
 * parameter (dependent type).
 * 
 * @author hoenicke
 *
 */
public class LambdaTerm extends Term {
	Term mArgType;
	Term mSubTerm;
	
	int mNumFreeVariables;

	public LambdaTerm(Term argType, Term subTerm, boolean isHidden) {
		this(argType, subTerm, typecheck(argType, subTerm, isHidden));
	}

	public LambdaTerm(Term argType, Term subTerm, Term type) {
		super(type);
		assert typecheck(argType, subTerm, ((PiTerm) type.evaluateHead()).mIsHidden).isSubType(type);
		mArgType = argType;
		mSubTerm = subTerm;
		mNumFreeVariables = Math.max(mArgType.numFreeVariables(), 
				mSubTerm.numFreeVariables() - 1);
	}
	
	@Override
	public int numFreeVariables() {
		return mNumFreeVariables;
	}
	
	public static Term typecheck(Term argType, Term subTerm, boolean isHidden) {
		return new PiTerm(argType, subTerm.getType(), isHidden);
	}

	@Override
	public Term evaluateHead() {
		return this;
	}

	public String toString(int offset, int prec) {
		if (mName != null)
			return mName.toString(offset, prec);
		StringBuilder sb = new StringBuilder();
		if (prec >= 1)
			sb.append('(');
		sb.append("\\@").append(offset).append(" : ");
		sb.append(mArgType.toString(offset, 2)).append(' ');
		if (!(mSubTerm instanceof LambdaTerm))
			sb.append("-> ");
		sb.append(mSubTerm.toString(offset + 1, 0));
		if (prec >= 1)
			sb.append(')');
		return sb.toString();
	}

	public boolean equalsHead(Term o) {
		if (!(o instanceof LambdaTerm))
			return false;
		LambdaTerm other = (LambdaTerm) o;
		return mArgType.equals(other.mArgType) && mSubTerm.equals(other.mSubTerm);
	}
}
