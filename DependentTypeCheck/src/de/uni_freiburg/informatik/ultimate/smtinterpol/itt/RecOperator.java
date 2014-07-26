package de.uni_freiburg.informatik.ultimate.smtinterpol.itt;

import java.util.ArrayDeque;

public class RecOperator extends Term {
	InductiveType mInductiveType;
	
	public RecOperator(InductiveType type) {
		super(computeType(type));
		mInductiveType = type;
	}
	
	private static Term computeType(InductiveType type) {
		// rec : publicArgs -> C -> constructors -> privateArgs -> t -> C(t)
		int numTCArgs = type.mParams.length;
		int numShared = type.mNumShared;
		int numPriv = numTCArgs - numShared;
		int numConstrs = type.mConstrs.length;

		// The type "TypeCons shared priv"
		// assumes order globals locals <- (we are here).
		Term tcType = type;
		Term[] tcVars = new Term[numTCArgs];
		for (int i = 0; i < numTCArgs; i++) {
			tcVars[i] = Term.variable(numTCArgs - i - 1, type.mParams[i]);
			tcType = new AppTerm(tcType, tcVars[i]);
		}
		// The type of C: (privateArgs -> TC -> U)
		Term cType = new PiTerm(tcType, Term.U);
		for (int i = numPriv - 1; i >= 0; i--) {
			cType = new PiTerm(type.mParams[numShared + i], cType);
		}

		// Build C locals t
		Term result = Term.variable(numConstrs + numPriv + 1, cType);
		// shift the global variables over the constructor
		Term[] constrArgTypes = new Term[numPriv+1];
		Substitution constrShift = Substitution.shift(1 + numConstrs);
		for (int i = 0; i < numPriv; i++) {
			constrArgTypes[i] = Term.substitute(type.mParams[numShared + i], 
					constrShift, null);
			Term var = Term.variable(numPriv - i, constrArgTypes[i]);
			constrShift = Substitution.consShifted(Term.variable(0, constrArgTypes[i]), 
					constrShift, Integer.MAX_VALUE);
			result = new AppTerm(result, var);
		}
		constrArgTypes[numPriv] = Term.substitute(tcType, constrShift, null);
		result = new AppTerm(result, Term.variable(0, 
				constrArgTypes[numPriv]));
		// locals -> t -> clt
		for (int i = numPriv; i >= 0; i--) {
			result = new PiTerm(constrArgTypes[i], result);
		}

		// now come the constructors
		for (int i = numConstrs - 1; i >= 0; i--) {
			Term constrType = type.mConstrs[i].computeRecType(cType);
			result = new PiTerm(constrType, result);
		}
		// now comes C
		result = new PiTerm(cType, result);
		// now come shared args
		for (int i = numShared - 1; i >= 0; i--) {
			result = new PiTerm(type.mParams[i], result);
		}
		return result.evaluate();
	}
	
	public int getNumArgs() {
		return mInductiveType.mParams.length + 
				mInductiveType.mConstrs.length + 2;
	}
	
	protected String toString(int offset, int prec) {
		return mInductiveType.mName + ".rec";
	}

	public Term applyRec(AppTerm fullRecApp) {
		AppTerm recApp = fullRecApp;
		// The last parameter of rec should be a constructor call.
		Term lastArg = recApp.mArg.evaluateHead();
		recApp = (AppTerm) recApp.mFunc;
		ArrayDeque<Term> constrArgs = new ArrayDeque<Term>();
		while (lastArg instanceof AppTerm) {
			AppTerm app = (AppTerm) lastArg;
			constrArgs.addFirst(app.mArg);
			lastArg = app.mFunc.evaluateHead();
		}
		if (!(lastArg instanceof Constructor))
			return fullRecApp;
		Constructor cons = (Constructor) lastArg;
		assert cons.mInductiveType == mInductiveType;
		// Now remove the local parameters from rec; we already type checked
		// that they are as expected.
		int numLocals = mInductiveType.mParams.length - 
				mInductiveType.mNumShared;
		for (int i = 0; i < numLocals; i++)
			recApp = (AppTerm) recApp.mFunc;

		// Now find the right constructor
		AppTerm t = recApp;
		int numConsToSkip = mInductiveType.mConstrs.length - cons.mIndex - 1;
		for (int i = 0; i < numConsToSkip; i++)
			t = (AppTerm) t.mFunc;
		Term constrCase = t.mArg;
		Term result = cons.applyRec(constrCase, recApp, constrArgs);
		return result.evaluateHead();
	}
}
