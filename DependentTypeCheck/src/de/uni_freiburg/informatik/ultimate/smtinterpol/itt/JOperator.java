package de.uni_freiburg.informatik.ultimate.smtinterpol.itt;

import java.util.ArrayDeque;

public class JOperator extends Term {
	InductiveType mInductiveType;
	
	public JOperator(InductiveType type) {
		super(computeType(type));
		mInductiveType = type;
	}
	
	private static Term computeType(InductiveType type) {
		// J : publicArgs -> C -> constructors -> privateArgs -> t -> C(t)
		int numShared = type.mNumShared;
		int numPriv = type.mParams.length - numShared;
		int numConstrs = type.mConstrs.length;

		// The type "TypeCons shared priv"
		Term tcType = type;
		for (int i = 0; i < type.mParams.length; i++) {
			tcType = new AppTerm(tcType, 
					new DeBruijnVariable(type.mParams.length - i - 1, type.mParams[i]));
		}
		// The type of C: (privateArgs -> TC -> U)
		Term cType = new PiTerm(tcType, Term.U);
		for (int i = numPriv - 1; i >= 0; i--) {
			cType = new PiTerm(type.mParams[numShared + i], cType);
		}

		// Build C locals t
		Term result = new DeBruijnVariable(1 + numPriv + numConstrs, cType);
		for (int i = 0; i < numPriv; i++) {
			Term locali = new DeBruijnVariable(numPriv - i,
					type.mParams[numShared + i].shiftBruijn(i, 1 + numConstrs));
			result = new AppTerm(result, locali);
		}
		Term tType = tcType.shiftBruijn(numPriv, 1 + numConstrs);
		result = new AppTerm(result, new DeBruijnVariable(0, tType));
		// Build t -> clt
		result = new PiTerm(tType, result);
		// locals -> t -> clt
		for (int i = numPriv - 1; i >= 0; i--) {
			Term locali = type.mParams[numShared + i]
					.shiftBruijn(i, 1 + numConstrs);
			result = new PiTerm(locali, result);
		}
		
		// now come the constructors
		for (int i = numConstrs - 1; i >= 0; i--) {
			Term constrType = type.mConstrs[i].computeJType(cType);
			result = new PiTerm(constrType, result);
		}
		// now comes C
		result = new PiTerm(cType, result);
		// now come shared args
		for (int i = numShared - 1; i >= 0; i--) {
			result = new PiTerm(type.mParams[i], result);
		}
		return result;
	}
	
	public int getNumArgs() {
		return mInductiveType.mParams.length + 
				mInductiveType.mConstrs.length + 2;
	}
	
	@Override
	protected Term internalEval() {
		return this;
	}
	
	protected String toString(int offset, int prec) {
		return mInductiveType.mName + ".J";
	}

	public Term applyArgs(ArrayDeque<Term> args) {
		// TODO Auto-generated method stub
		return null;
	}

	public boolean equals(Object o) {
		return (this == o);
	}
}
