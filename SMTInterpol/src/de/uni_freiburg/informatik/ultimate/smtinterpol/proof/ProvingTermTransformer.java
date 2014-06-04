/*
 * Copyright (C) 2009-2012 University of Freiburg
 *
 * This file is part of SMTInterpol.
 *
 * SMTInterpol is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * SMTInterpol is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with SMTInterpol.  If not, see <http://www.gnu.org/licenses/>.
 */
package de.uni_freiburg.informatik.ultimate.smtinterpol.proof;

import java.util.ArrayDeque;
import java.util.HashMap;

import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.LetTerm;
import de.uni_freiburg.informatik.ultimate.logic.NonRecursive;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;

/**
 * This is the base class for transforming formulas and tracking their
 * equivalence proofs.  It does nothing by itself but you can use it to 
 * create arbitrary transformations on formulas.
 * The transform method applies the transformation in a non-recursive manner.
 *
 * Subclasses should override the function convert.  It takes as arguments
 * the term to convert and its transformation proof.  It can
 * call its super constructor on the original or a partially converted 
 * term to recurse into the arguments.  Or it can directly set a final 
 * result with <code>setResult</code>.  It can also call <code>pushTerm</code>
 * and return, which will restart the convert method (non-recursively).
 * 
 * When the transformation of the arguments is done, one of the 
 * <code>postConvert...</code> functions is called depending on the type of
 * the term.  This gets the transformed arguments, their transformation proof,
 * and the original term given to <code>super.convert()</code>.
 * 
 * @author Jochen Hoenicke
 */
public class ProvingTermTransformer extends NonRecursive {
	/**
	 * The term cache.
	 */
	private final ArrayDeque<HashMap<Term, ProofTerm>> mCache = 
		new ArrayDeque<HashMap<Term,ProofTerm>>();
	
	public static class ProofTerm {
		/**
		 * The transformed term.
		 */
		Term mTransformed;
		/**
		 * A proof for <code>(= original transformed)</code>.
		 * This is null if proof tracking is off, or if the transformed
		 * term is the same as the original.
		 */
		Term mEquivalenceProof;
		
		/**
		 * Create a proof term.
		 * @param term the transformed term.
		 * @param proof the equivalence proof.
		 */
		ProofTerm(Term term, Term proof) {
			mTransformed = term;
			mEquivalenceProof = proof;
		}
		
		public Term getTerm() {
			return mTransformed;
		}
		
		public Term getProof() {
			return mEquivalenceProof;
		}
	}
	
	/**
	 * The converted terms.  This is used for example to store the 
	 * arguments of an application term, before the application term is
	 * evaluated.
	 */
	private final ArrayDeque<ProofTerm> mConverted = new ArrayDeque<ProofTerm>();

	/**
	 * This class represents one item of work.  It consists of a term and
	 * some task that still needs to be performed on the term.
	 */
	protected static class Converter implements Walker {
		private final Term mTerm;
		private final Term mProof;
		
		public Converter(Term term, Term proof) {
			mTerm = term;
			mProof = proof;
		}
		
		public String toString() {
			return "Convert " + mTerm.toStringDirect();
		}

		@Override
		public final void walk(NonRecursive walker) {
			ProvingTermTransformer trafo = (ProvingTermTransformer) walker;
			cacheConvert(trafo);
		}
		
		private void cacheConvert(ProvingTermTransformer trafo) {
			if (mProof == null) {
				/* Do not cache partial proofs.  proof != null means that
				 * someone transformed the original term to term.  We will
				 * cache in the end that original term was transformed to
				 * the final term; the intermediate term is not cached, as
				 * its proof will still refer to the original term.
				 */
				ProofTerm newTerm = trafo.mCache.getLast().get(mTerm);
				if (newTerm != null) {
					trafo.setResult(newTerm);
					return;
				}
			}
			convert(trafo);
		}

		/**
		 * The function that does the transformation.   Override this function
		 * if you build your own term transformer.  It does not return the result
		 * but instead it puts it on the converted stack using setResult().
		 * Instead it can also enqueue some Builders that will in the end put the
		 * result on the converted stack.
		 * 
		 * You can always call super.convert() if you do not need to convert
		 * the term.  It will still convert the sub-terms. If you do not want to
		 * convert the sub terms, call setResult(term) instead.
		 */
		protected void convert(ProvingTermTransformer trafo) {
			if (mTerm instanceof ConstantTerm
				|| mTerm instanceof TermVariable) {
				// no need to cache it
				trafo.setResult(new ProofTerm(mTerm, mProof));
			} else if (mTerm instanceof ApplicationTerm) {
				trafo.enqueueWalker(new BuildApplicationTerm(this));
				trafo.pushTerms(((ApplicationTerm) mTerm).getParameters());
			} else if (mTerm instanceof LetTerm) {
				throw new AssertionError("let in prover");
			} else if (mTerm instanceof QuantifiedFormula) {
				trafo.enqueueWalker(new BuildQuantifier(this));
				trafo.pushTerm(((QuantifiedFormula) mTerm).getSubformula(), null);
				trafo.beginScope();
			} else if (mTerm instanceof AnnotatedTerm) {
				AnnotatedTerm annterm = (AnnotatedTerm) mTerm;
				trafo.enqueueWalker(new BuildAnnotation(this));
				trafo.pushTerm(annterm.getSubterm(), null);
				return;
			} else
				throw new AssertionError("Unknown Term: " + mTerm.toStringDirect());
		}

		public void postConvertApplicationTerm(ProvingTermTransformer trafo, 
				Term[] newArgs, Term[] subProofs) {
			ApplicationTerm old = (ApplicationTerm) mTerm;
			Term proof = mProof;
			Term newTerm = old;
			if (newArgs != old.getParameters()) {
				FunctionSymbol fun = old.getFunction(); 
				Theory theory = fun.getTheory();
				newTerm = theory.term(fun, newArgs);
				proof = createCongruenceProof(old, proof, subProofs);
			}
			setResult(trafo, newTerm, proof);
		}
		
		public void postConvertQuantifier(ProvingTermTransformer trafo,
				Term newBody, Term subProof) {
			QuantifiedFormula old = (QuantifiedFormula) mTerm;
			Term proof = mProof;
			Term newFormula = old;
			if (newBody != old.getSubformula()) {
				Theory theory = old.getTheory();
				TermVariable[] vars = old.getVariables();
				newFormula = old.getQuantifier() == QuantifiedFormula.EXISTS
					? theory.exists(vars, newBody) : theory.forall(vars,newBody);
				proof = createCongruenceProof(old, proof, new Term[] {subProof});
			}
			setResult(trafo, newFormula, proof);
		}

		public void postConvertAnnotation(ProvingTermTransformer trafo,
				Term newBody, Term subProof) {
			AnnotatedTerm old = (AnnotatedTerm) mTerm;
			Term proof = mProof;
			Term result = old;
			if (newBody != old.getSubterm()) {
				Annotation[] annots = old.getAnnotations();
				result = old.getTheory().annotatedTerm(annots, newBody);
				proof = createCongruenceProof(old, proof, new Term[] { subProof });
			}
			setResult(trafo, result, proof);
		}

		public Term createCongruenceProof(Term orig, Term proof, Term[] subProofs) {
			int countSubProofs = 0;
			for (Term sub : subProofs) {
				if (sub != null)
					countSubProofs++;
			}
			if (countSubProofs == 0)
				return proof;
			Term[] congArgs = new Term[1 + countSubProofs];
			int offset = 0;
			congArgs[offset++] = proof != null ? proof 
					: orig.getTheory().term("@refl", orig);
			for (Term sub : subProofs) {
				if (sub != null)
					congArgs[offset++] = sub;
			}
			assert offset == congArgs.length;
			return orig.getTheory().term("@cong", congArgs);
		}
		
		public void setResult(ProvingTermTransformer trafo, Term result, Term proof) {
			ProofTerm proofTerm = new ProofTerm(result, proof);
			if (mProof != null) {
				trafo.mCache.getLast().put(mTerm, proofTerm);
			}
			trafo.setResult(proofTerm);
		}
	}
	
	/**
	 * Push all terms in the array on the todo stack as CONVERT work item.
	 * It pushes them with an empty equivalence proof.
	 * @param terms the array of terms.
	 */
	protected final void pushTerms(Term[] terms) {
		for (int i = terms.length - 1; i >= 0; i--)
			pushTerm(terms[i], null);
	}

	/**
	 * Push all terms in the array on the todo stack as CONVERT work item.
	 * @param terms the array of terms.
	 * @param proofs the equivalence subproofs.  The array must have the
	 * same length.
	 */
	protected final void pushTerms(Term[] terms, Term[] proofs) {
		for (int i = terms.length - 1; i >= 0; i--)
			pushTerm(terms[i], proofs[i]);
	}
	
	/**
	 * Push a term on the todo stack as CONVERT work item.
	 * @param term the term to convert.
	 */
	protected final void pushTerm(Term term, Term proof) {
		enqueueWalker(new Converter(term, proof));
	}
	
	/**
	 * Set the conversion result to term.
	 * @param term the converted term.
	 */
	protected final void setResult(ProofTerm proofTerm) {
		mConverted.addLast(proofTerm);
	}
	
	protected void beginScope() {
		mCache.addLast(new HashMap<Term, ProofTerm>());
	}
	
	protected void endScope() {
		mCache.removeLast();
	}
	
	/**
	 * Transform a term.
	 * @param term the term to transform.
	 * @return the resulting transformed term.
	 */
	public final ProofTerm transform(Term term) {
		beginScope();
		run(new Converter(term, null));
		endScope();
		return mConverted.removeLast();
	}
	
	/**
	 * Get a single converted term from the converted stack.  This is the
	 * dual of pushTerm() that is called after the term were removed
	 * from the todo stack and pushed to the converted stack.  
	 * @return the new converted term.  
	 */
	protected final ProofTerm getConverted() {
		return mConverted.removeLast();
	}

	/**
	 * Get the converted terms from the converted stack.  This is the
	 * dual of pushTerm() that is called after the term were removed
	 * from the todo stack and pushed to the converted stack.  It takes
	 * the old terms as argument and checks for changes.
	 * @param oldArgs the original arguments.
	 * @return the new converted arguments.  It will return the same array
	 * oldArgs if there were no changes.
	 */
	protected final Term[] getConverted(Term[] oldArgs, Term[] proofs) {
		assert proofs.length == oldArgs.length;
		Term[] newArgs = oldArgs;
		for (int i = oldArgs.length - 1; i >= 0; i--) {
			ProofTerm newProofTerm = getConverted();
			if (newProofTerm.mTransformed != oldArgs[i]) {
				if (newArgs == oldArgs)
					newArgs = oldArgs.clone();
				proofs[i] = newProofTerm.mEquivalenceProof;
				newArgs[i] = newProofTerm.mTransformed;
			}
		}
		return newArgs;
	}

	/**
	 * Collect the arguments of an application term from the converted stack
	 * and finish the conversion of appTerm.  This is called after the arguments
	 * of appTerm have been converted.  It will put the converted term on
	 * the converted stack and store it in the cache.
	 * @param mAppTerm the application term to convert.
	 */
	protected static class BuildApplicationTerm implements Walker {
		private final Converter mConverter;
		
		public BuildApplicationTerm(Converter converter) {
			mConverter = converter;
		}
		
		public void walk(NonRecursive engine) {
			ProvingTermTransformer transformer = (ProvingTermTransformer) engine;
			/* collect args and check if they have been changed */
			Term[] oldArgs = ((ApplicationTerm) mConverter.mTerm).getParameters();
			Term[] subProofs = new Term[oldArgs.length];
			Term[] newArgs = transformer.getConverted(oldArgs, subProofs);
			mConverter.postConvertApplicationTerm(transformer,
					newArgs, subProofs);
		}

		public String toString() {
			return ((ApplicationTerm) mConverter.mTerm).getFunction().getApplicationString();
		}
	}

	/**
	 * Collect the sub term of a quantified formula and build the converted 
	 * formula.  The converted sub formula is expected to be on the
	 * converted stack. 
	 * It stores the converted quantifier on the converted stack and in the
	 * cache.
	 * @param mAnnotatedTerm the quantifier to convert.
	 */
	protected static class BuildQuantifier implements Walker {
		private final Converter mConverter;
		
		public BuildQuantifier(Converter converter) {
			mConverter = converter;
		}
		
		public void walk(NonRecursive engine) {
			ProvingTermTransformer transformer = 
					(ProvingTermTransformer) engine;
			ProofTerm sub = transformer.getConverted();
			mConverter.postConvertQuantifier(transformer, 
					sub.mTransformed, sub.mEquivalenceProof);
			transformer.endScope();
		}

		public String toString() {
			return ((QuantifiedFormula) mConverter.mTerm).getQuantifier() 
						== QuantifiedFormula.EXISTS
					? "exists" : "forall";
		}
	}

	/**
	 * Collect the sub term and annotations of an annotated formula from
	 * the converted stack.  It converts the annotation and stores the 
	 * result in the cache and on the converted stack.
	 * Note that only Annotations that are of type Term or Term[] are 
	 * converted.
	 * @param mAnnotatedTerm the annotated term.
	 */
	protected static class BuildAnnotation implements Walker {
		private final Converter mConverter;
		
		public BuildAnnotation(Converter converter) {
			mConverter = converter;
		}
		
		public void walk(NonRecursive engine) {
			ProvingTermTransformer transformer = 
					(ProvingTermTransformer) engine;
			ProofTerm sub = transformer.getConverted();
			mConverter.postConvertAnnotation(transformer,
					sub.mTransformed, sub.mEquivalenceProof);
		}
		
		public String toString() {
			return "annotate";
		}
	}
	
	public void reset() {
		super.reset();
		mConverted.clear();
		mCache.clear();
	}
}
