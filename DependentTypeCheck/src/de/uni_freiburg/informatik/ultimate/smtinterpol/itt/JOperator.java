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
		int numTCArgs = type.mParams.length;
		int numShared = type.mNumShared;
		int numPriv = numTCArgs - numShared;
		int numConstrs = type.mConstrs.length;

		// The type "TypeCons shared priv"
		// assumes order globals locals <- (we are here).
		Term tcType = type;
		for (int i = 0; i < numTCArgs; i++) {
			tcType = new AppTerm(tcType, 
					new DeBruijnVariable(type.mParams.length - i - 1, 
							type.mParams[i]));
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
	
	protected String toString(int offset, int prec) {
		return mInductiveType.mName + ".J";
	}

	public Term applyJ(AppTerm fullJApp) {
		AppTerm jApp = fullJApp;
		// The last parameter of J should be a constructor call.
		Term lastArg = jApp.mArg;
		jApp = (AppTerm) jApp.mFunc;
		ArrayDeque<Term> constrArgs = new ArrayDeque<Term>();
		while (lastArg instanceof AppTerm) {
			AppTerm app = (AppTerm) lastArg;
			constrArgs.addFirst(app.mArg);
			lastArg = app.mFunc;
		}
		if (!(lastArg instanceof Constructor))
			return fullJApp;
		Constructor cons = (Constructor) lastArg;
		assert cons.mInductiveType == mInductiveType;
		// Now remove the local parameters from J; we already type checked
		// that they are as expected.
		int numLocals = mInductiveType.mParams.length - 
				mInductiveType.mNumShared;
		for (int i = 0; i < numLocals; i++)
			jApp = (AppTerm) jApp.mFunc;

		// Now find the right constructor
		AppTerm t = jApp;
		int numConsToSkip = mInductiveType.mConstrs.length - cons.mIndex - 1;
		for (int i = 0; i < numConsToSkip; i++)
			t = (AppTerm) t.mFunc;
		Term constrCase = t.mArg;
		Term result = cons.applyJ(constrCase, jApp, constrArgs);
		return result.evaluate();
	}

	public boolean equals(Object o) {
		return (this == o);
	}
}
