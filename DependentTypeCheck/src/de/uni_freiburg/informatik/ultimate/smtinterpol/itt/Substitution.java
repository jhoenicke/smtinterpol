package de.uni_freiburg.informatik.ultimate.smtinterpol.itt;

import java.util.Arrays;

public class Substitution {
	Term[] mSubstTerms;
	int mShiftOffset;
	
	public static Term[] EMPTY = new Term[0];
	public static Substitution[] sShifts = new Substitution[0];
	
	public Substitution(Term[] substterms, int offset) {
		mSubstTerms = substterms;
		mShiftOffset = offset;
	}
	
	public String toString(int offset, int prec) {
		StringBuilder sb = new StringBuilder();
		for (Term t : mSubstTerms)
			sb.append(t.toString(offset, 1)).append('.');
		sb.append('^').append(mShiftOffset);
		return sb.toString();
	}

	public String toString() {
		return toString(0, 0);
	}

	public static Substitution shift(int offset) {
		if (offset >= sShifts.length) {
			int oldlen = sShifts.length;
			sShifts = Arrays.copyOf(sShifts, 
					Math.max(offset + 1, sShifts.length * 2));
			for (int i = oldlen; i < sShifts.length; i++)
				sShifts[i] = new Substitution(EMPTY, i);
		}
		return sShifts[offset];
	}
	
	public static Substitution unit(Term first) {
		return new Substitution(new Term[] { first }, 0);
	}

	public static Substitution consShifted(Term varType, Substitution second, 
			int maxVariable) {
		Term[] terms = new Term[Math.min(maxVariable,
				second.mSubstTerms.length + 1)];
		if (terms.length == 0)
			return shift(second.mShiftOffset);
		terms[0] = Term.variable(0,  varType);
		for (int i = 1; i < terms.length; i++)
			terms[i] = Term.substitute(second.mSubstTerms[i - 1], shift(1), null);
		return new Substitution(terms, second.mShiftOffset + 1);
	}

	/**
	 * Compute the composition of two substitututions.  This is the 
	 * substitution sigma, with term[first][second] = term[sigma] for all
	 * terms.
	 * @param first the first substitution.
	 * @param second the second substitution.
	 * @param maxVariable the maximum variable number occuring in the 
	 * substituted terms.  This is used to shorten the substitution if
	 * possible.
	 * @return the composed substitution.
	 */
	public static Substitution compose(
			Substitution first, Substitution second,
			int maxVariable) {
		/* Let first = f0...f{n-1}^fs and second = s0...s{m-1}^ss, where 
		 * f0,...,f{n-1},s0,...,s{m-1} are terms and fs and ss numbers 
		 * (the shift offsets).  If fs < m, then the composed substitution 
		 * is f0[second]...f{n-1}[second].s{fs}....s{m-1}^{ss}.
		 * If fs >= m, then the composed substitution is
		 * f1[second]...fn[second]^{ss+fs-m}.
		 * We set secondLen to the number of s{i} terms added. 
		 */
		int secondLen = Math.max(0, second.mSubstTerms.length
				- first.mShiftOffset);
		Term[] terms = new Term[Math.min(first.mSubstTerms.length + secondLen,
				maxVariable)];
		if (terms.length == 0)
			return shift(first.mShiftOffset - second.mSubstTerms.length
					+ second.mShiftOffset);
		for (int i = 0; i < terms.length; i++) {
			if (i < first.mSubstTerms.length) {
				terms[i] = Term.substitute(first.mSubstTerms[i], second, null);
			} else {
				terms[i] = second.mSubstTerms[i
						- first.mSubstTerms.length + first.mShiftOffset];
			}
		}
		int offset = first.mShiftOffset <= second.mSubstTerms.length
				? second.mShiftOffset
				: second.mShiftOffset + first.mShiftOffset - second.mSubstTerms.length;
		return new Substitution(terms, offset);
	}

	public int numFreeVariables(int numFreeVariables) {
		int numFree = 0;
		for (int i = 0; i < numFreeVariables; i++) {
			if (i >= mSubstTerms.length) {
				numFree = Math.max(numFree, 
						mShiftOffset + numFreeVariables - mSubstTerms.length);
				return numFree;
			}
			numFree = Math.max(numFree, mSubstTerms[i].numFreeVariables());
		}
		return numFree;
	}
}
