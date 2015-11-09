package de.uni_freiburg.informatik.ultimate.smtinterpol.itt;

/**
 * Class that represents a pretty name for a term.  For a definition 
 * <pre>definition identifier = term</pre>
 * the pretty name of the term is set to the identifier.
 * If a named term is evaluated, the name is preserved.  If an 
 * application of a named function is evaluated, it gets a pretty name
 * corresponding to the application of the named function.
 */
public abstract class PrettyTerm {
	private static class Name extends PrettyTerm {
		String mName;

		Name(String name) {
			mName = name;
		}

		public String toString(int offset, int prec) {
			return mName;
		}
	}
	
	private static class Application extends PrettyTerm {
		PrettyTerm mFunc;
		Term mArg;

		Application(PrettyTerm func, Term arg) {
			mFunc = func;
			mArg = arg;
		}

		public String toString(int offset, int prec) {
			String str = mFunc.toString(offset, 2) + " " 
				+ mArg.evaluate().toString(offset, 3);
			return prec >= 3 ? "(" + str + ")" : str;
		}

		public PrettyTerm substitute(Substitution subst) {
			return application(mFunc, Term.substitute(mArg, subst, null));
		}
	}

	public static PrettyTerm application(PrettyTerm func, Term arg) {
		return new Application(func, arg);
	}
	public static PrettyTerm name(String name) {
		return new Name(name);
	}
	public PrettyTerm substitute(Substitution subst) {
		return this;
	}
	
	public String toString() {
		return toString(1, 0);
	}
	
	public abstract String toString(int offset, int prec);
}
