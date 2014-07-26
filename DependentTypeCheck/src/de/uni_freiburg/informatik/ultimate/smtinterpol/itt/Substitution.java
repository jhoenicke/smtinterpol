package de.uni_freiburg.informatik.ultimate.smtinterpol.itt;

public abstract class Substitution {
	public static class Shift extends Substitution {
		int mOffset;
		
		public Shift(int offset) {
			mOffset = offset;
		}

		public String toString(int prec) {
			String str = "^" + mOffset;
			return prec >= 2 ? "(" + str + ")" : str;
		}

		public Substitution evaluateHead() {
			return this;
		}
	}
	
	public static class Cons extends Substitution {
		Term mHead;
		Substitution mTail;
		
		Substitution mEvaluated;
		
		public Cons(Term head, Substitution tail) {
			mHead = head;
			mTail = tail;
		}
		
		public String toString(int prec) {
			String str = mHead.toString(1, 1) + "." 
					+ mTail.toString(1);
			return prec >= 2 ? "(" + str + ")" : str;
		}

		public Substitution evaluateHead() {
			return this;
		}
	}
	
	public static class Compose extends Substitution {
		Substitution mFirst;
		Substitution mSecond;
		
		Substitution mEvaluated;
		
		public Compose(Substitution first, Substitution second) {
			mFirst = first;
			mSecond = second;
		}
		
		public String toString(int prec) {
			String str = mFirst.toString(2) + " o " 
					+ mSecond.toString(1);
			return prec >= 1 ? "(" + str + ")" : str;
		}

		public Substitution evaluateHead() {
			if (mEvaluated == null) {
				Substitution first = mFirst.evaluateHead();
				if (first instanceof Cons) {
					Cons cons = (Cons) first;
					mEvaluated = Substitution.cons(
							Term.substitute(cons.mHead, mSecond, null),
							Substitution.compose(cons.mTail, mSecond));
				} else {
					assert first instanceof Shift;
					int offset = ((Shift) first).mOffset;
					Substitution second = mSecond.evaluateHead();
					while (offset > 0) {
						if (second instanceof Shift) {
							second = Substitution.shift(
									offset + ((Shift) second).mOffset);
							break;
						}
						second = ((Cons) second).mTail.evaluateHead();
						offset--;
					}
					mEvaluated = second;
				}
			}
			return mEvaluated;
		}
	}

	public abstract String toString(int prec);

	public abstract Substitution evaluateHead();
	
	public String toString() {
		return toString(0);
	}

	public static Substitution shift(int offset) {
		return new Shift(offset);
	}

	public static Substitution cons(Term first, Substitution second) {
		return new Cons(first, second);
	}

	public static Substitution compose(
			Substitution first, Substitution second) {
		return new Compose(first, second);
	}

	public int numFreeVariables(int numFreeVariables) {
		int numFree = 0;
		Substitution subst = this;
		while (numFreeVariables > 0) {
			subst = subst.evaluateHead();
			if (subst instanceof Shift) {
				numFree = Math.max(numFree, 
						((Shift) subst).mOffset + numFreeVariables);
				return numFree;
			} else {
				Cons cons = (Cons) subst;
				numFree = Math.max(numFree, cons.mHead.numFreeVariables());
				subst = cons.mTail;
			}
		}
		return numFree;
	}
}
