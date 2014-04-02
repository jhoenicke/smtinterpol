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

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Stack;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.FormulaUnLet;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.NonRecursive;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.SMTAffineTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.SMTInterpol;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.SymmetricPair;

/**
 * This proof checker checks compliance of SMTInterpol proofs with
 * its documented format. 
 * 
 * @author Pascal Raiola, Jochen Hoenicke
 */
public class ProofChecker extends NonRecursive {

	public static class ProofWalker implements Walker {
		final ApplicationTerm mTerm;
		public ProofWalker(Term term) {
			assert (term.getSort().getName().equals("@Proof"));
			mTerm = (ApplicationTerm) term;
		}
		
		public void walk(NonRecursive engine) {
			((ProofChecker) engine).walk(mTerm);
		}
	}

	public static class ResolutionWalker implements Walker {
		final ApplicationTerm mTerm;
		public ResolutionWalker(ApplicationTerm term) {
			assert term.getFunction().getName().equals("@res");
			mTerm = term;
		}
		
		public void walk(NonRecursive engine) {
			((ProofChecker) engine).walkResolution(mTerm);
		}
	}

	public static class EqualityWalker implements Walker {
		final ApplicationTerm mTerm;
		public EqualityWalker(ApplicationTerm term) {
			assert term.getFunction().getName().equals("@eq");
			mTerm = term;
		}
		
		public void walk(NonRecursive engine) {
			((ProofChecker) engine).walkEquality(mTerm);
		}
	}

	public static class ClauseWalker implements Walker {
		final ApplicationTerm mTerm;
		public ClauseWalker(ApplicationTerm term) {
			assert term.getFunction().getName().equals("@clause");
			mTerm = term;
		}
		
		public void walk(NonRecursive engine) {
			((ProofChecker) engine).walkClause(mTerm);
		}
	}

	public static class SplitWalker implements Walker {
		final ApplicationTerm mTerm;
		public SplitWalker(ApplicationTerm term) {
			assert term.getFunction().getName().equals("@split");
			mTerm = term;
		}
		
		public void walk(NonRecursive engine) {
			((ProofChecker) engine).walkSplit(mTerm);
		}
	}

	HashSet<Term> mAssertions;
	SMTInterpol mSkript;
	Logger mLogger;
	int mError;
	
	HashSet<String> mDebug = new HashSet<String>(); // Just for debugging
	
	HashMap<Term, Term> mCacheConv; //Proof Checker Cache for conversions
	
	// Declarations for the Walker
	Stack<Term> mStackResults = new Stack<Term>();
	Stack<Term> mStackResultsDebug = new Stack<Term>();
	Stack<Annotation[]> mStackAnnots = new Stack<Annotation[]>();
	
	public ProofChecker(SMTInterpol smtInterpol) {
		mSkript = smtInterpol;
		Term[] assertions = smtInterpol.getAssertions();
		FormulaUnLet unletter = new FormulaUnLet();
		mAssertions = new HashSet<Term>(assertions.length);
		for (Term ass : assertions)
			mAssertions.add(unletter.transform(ass));
		mLogger = smtInterpol.getLogger();
	}
	
	public boolean check(Term proof) {
		
		// Just for debugging
		//mDebug.add("currently");
		//mDebug.add("hardTerm");
		//mDebug.add("LemmaLAadd");
		//mDebug.add("calculateTerm");
		//mDebug.add("WalkerPath");
		//mDebug.add("WalkerPathSmall");
		//mDebug.add("LemmaCC");
		//mDebug.add("newRules");
		//mDebug.add("convertAppID");
		//mDebug.add("cacheUsed");
		//mDebug.add("cacheUsedSmall");
		//mDebug.add("allSubpaths");
		//mDebug.add("split_notOr");
		//mDebug.add("CacheRuntimeCheck");
		//mLogger.setLevel(Level.DEBUG);
	
		
		// Initializing the proof-checker-cache
		mCacheConv = new HashMap<Term, Term>();
		mError = 0;
		// Now non-recursive:
		proof = new FormulaUnLet().unlet(proof);
		run(new ProofWalker(proof));
		
		assert (mStackResults.size() == 1);
		Term resCalc = stackPopCheck(proof);
		
		if (resCalc != mSkript.term("false")) {
			reportError("The proof did not yield a contradiction but "
					+ resCalc);
		}
		
		return mError == 0;
	}
	
	private void reportError(String msg) {
		mLogger.error(msg);
		mError++;
	}

	public Term negate(Term formula) {
		if (formula instanceof ApplicationTerm) {
			ApplicationTerm appFormula = (ApplicationTerm) formula;
			
			if (appFormula.getFunction().getName() == "not") {
				return appFormula.getParameters()[0];
			}
		}
		
		//Formula is not negative
		return mSkript.term("not", formula);
	}

	/**
	 * The proof walker.  This takes a proof term and pushes the proven
	 * formula on the result stack.  It also checks the proof cache to
	 * prevent running over the same term twice.
	 * 
	 * @param proofTerm  The proof term.  Its sort must be {@literal @}Proof.
	 */
	public void walk(ApplicationTerm proofTerm) {
		/* Check the cache, if the unfolding step was already done */
		if (mCacheConv.containsKey(proofTerm)) {
			if (mDebug.contains("CacheRuntimeCheck"))
				mLogger.debug("Cache-RT: K: " + proofTerm.toString()
						+ " (known)");
			if (mDebug.contains("cacheUsed"))
				mLogger.debug("Calculation of the term " + proofTerm.toString() 
						+ " is known: " + mCacheConv.get(proofTerm).toString());
			if (mDebug.contains("cacheUsedSmall"))
				mLogger.debug("Calculation known.");
			stackPush(mCacheConv.get(proofTerm), proofTerm);
			return;
		} else
			if (mDebug.contains("CacheRuntimeCheck"))
				mLogger.debug("Cache-RT: U: " + proofTerm.toString()
						+ " (unknown)");
				
		/* Get the function and parameters */
		String rulename = proofTerm.getFunction().getName();
		Term[] params = proofTerm.getParameters();
		
		/* Just for debugging */
		if (mDebug.contains("currently"))
			mLogger.debug("Currently looking at: " + rulename
					+ " \t (function)");
		
		/* Look at the rule name and treat each different */
		switch (rulename) {
		case "@res":
			/* The resolution rule.
			 * 
			 * This function is expected to have as first argument the 
			 * main clause.  The other parameters are clauses annotated
			 * with a pivot literal, on which they are resolved.
			 */
			enqueueWalker(new ResolutionWalker(proofTerm));
			for (int i = params.length - 1; i >= 1; i--) {
				AnnotatedTerm pivotClause = (AnnotatedTerm)params[i];
				enqueueWalker(new ProofWalker(pivotClause.getSubterm()));
			}
			enqueueWalker(new ProofWalker(params[0]));
			break;
			
		case "@eq":
			enqueueWalker(new EqualityWalker(proofTerm));
			for (int i = params.length - 1; i >= 0; i--) {
				enqueueWalker(new ProofWalker(params[i]));
			}
			break;
			
		case "@lemma":
			walkLemma(proofTerm);
			break;
			
		case "@tautology":
			walkTautology(proofTerm);
			break;
		case "@asserted":
			walkAsserted(proofTerm);
			break;
			
		case "@rewrite": 
			walkRewrite(proofTerm);
			break;
			
		case "@intern":
			walkIntern(proofTerm);
			break;

		case "@split":
			enqueueWalker(new SplitWalker(proofTerm));
			enqueueWalker(new ProofWalker(
					((AnnotatedTerm) params[0]).getSubterm()));
			break;
			
		case "@clause":
			enqueueWalker(new ClauseWalker(proofTerm));
			enqueueWalker(new ProofWalker(params[0]));
			break;				
			
		default:
			throw new AssertionError("Unknown proof rule " + rulename + ".");
		}
	}
	
	public void walkLemma(ApplicationTerm lemmaApp) {
		AnnotatedTerm annTerm = (AnnotatedTerm) lemmaApp.getParameters()[0];
		String lemmaType = annTerm.getAnnotations()[0].getKey();
		Object lemmaAnnotation = annTerm.getAnnotations()[0].getValue();
		Term lemma = annTerm.getSubterm();
		
		if (mDebug.contains("currently"))
			mLogger.debug("Lemma-type: " + lemmaType);
		
		if (lemmaType == ":LA") {
			// The disjunction
			ApplicationTerm termLemmaDisj = convertApp(lemma);
			
			pm_func(termLemmaDisj,"or");
			
			int arrayLength = termLemmaDisj.getParameters().length;
			ApplicationTerm[] termMultDisj = new ApplicationTerm[arrayLength]; // multiplied [negated] disjuncts
			ApplicationTerm[] termNegDisj = new ApplicationTerm[arrayLength]; // negated disjuncts
			ApplicationTerm[] termNegDisjMayDeep = new ApplicationTerm[arrayLength]; // negated disjuncts maybe one level deeper
			ApplicationTerm[] termTurnDisj = new ApplicationTerm[arrayLength]; // disjuncts with potentially turned <=/</>=/>
			ApplicationTerm[] termNegDisjUnif = new ApplicationTerm[arrayLength];
			ApplicationTerm[] termNegDisjInv = new ApplicationTerm[arrayLength];
			
			// Now get the factors:
			Term[] numbers = (Term[]) lemmaAnnotation;
			Rational[] numbersSMT = new Rational[numbers.length];
			
			for (int i = 0; i < numbers.length; i++)
				numbersSMT[i] = calculateTerm(numbers[i]).getConstant();
			
			// New: Transform all to ... <= 0 if possible, otherwise to ... <= 0 and ... < 0 
			
			// Step 1: Uniformize the negated disjuncts and multiply with factor
			
			boolean foundLe = false; // found lower-equal (<=)
			boolean foundLt = false; // found lower-than (<)
			boolean foundEq = false; // found equality (=)
			
			for (int i = 0; i < arrayLength; i++) {
				// The convertApp_hard's are used to remove the ":quoted"-annotation
				
				// Negate them and remove the annotation
				termNegDisj[i] = convertApp_hard(negate(convertApp_hard(termLemmaDisj.getParameters()[i])));
				
				// Get rid of each negation
				String prerelation = termNegDisj[i].getFunction().getName();
				String relation;
				if (prerelation == "not") {
					// Dig one level deeper
					termNegDisjMayDeep[i] = convertApp_hard(termNegDisj[i].getParameters()[0]);
												
					prerelation = termNegDisjMayDeep[i].getFunction().getName();
					
					//Turn the relation around
					if (prerelation == "<=")
						relation = ">";
					else if (prerelation == ">=")
						relation = "<";
					else if (prerelation == "<")
						relation = ">=";
					else if (prerelation == ">")
						relation = "<=";
					else
						relation = prerelation;
				} else {
					termNegDisjMayDeep[i] = termNegDisj[i];
					relation = prerelation;
				}
				
				// If the factor is negative switch the function symbol
				if (numbersSMT[i].isNegative())
					if (relation == "<=")
						relation = ">=";
					else if (relation == ">=")
						relation = "<=";
					else if (relation == "<")
						relation = ">";
					else if (relation == ">")
						relation = "<";
				
				checkNumber(termNegDisjMayDeep[i].getParameters(),2);
				
				termTurnDisj[i] = convertApp(mSkript.term(relation, termNegDisjMayDeep[i].getParameters()));
				checkNumber(termTurnDisj[i],2);
				
				// Multiply with -1			
				Term[] paramsTemp1 = new Term[2];
				if (numbersSMT[i].isNegative()) {
					paramsTemp1[0] = calculateTerm(termTurnDisj[i].getParameters()[0]).negate();
					paramsTemp1[1] = calculateTerm(termTurnDisj[i].getParameters()[1]).negate();
					numbersSMT[i] = numbersSMT[i].negate();
				} else {
					paramsTemp1 = termTurnDisj[i].getParameters();
				}
				
				termNegDisjInv[i] = convertApp(mSkript.term(relation, paramsTemp1));
						
				//Uniformize them
				termNegDisjUnif[i] = uniformizeInEquality(termNegDisjInv[i]);
				checkNumber(termNegDisjUnif[i],2);
				
				// Multiply both sides		
				Term[] paramsTemp2 = new Term[2];
				paramsTemp2[0] = calculateTerm(termNegDisjUnif[i].getParameters()[0]).mul(numbersSMT[i]);
				paramsTemp2[1] = calculateTerm(termNegDisjUnif[i].getParameters()[1]).mul(numbersSMT[i]);
				
				termMultDisj[i] = convertApp(mSkript.term(relation, paramsTemp2));
				
				foundLe = (foundLe || pm_func_weak(termMultDisj[i], "<="));
				foundLt = (foundLt || pm_func_weak(termMultDisj[i], "<"));
				foundEq = (foundEq || pm_func_weak(termMultDisj[i], "="));
			}
			
			// Step 2: Add them up
			
			SMTAffineTerm termSum = calculateTerm(termMultDisj[0].getParameters()[0]);
			
			for (int i = 1; i < arrayLength; i++)
				termSum = termSum.add(calculateTerm(termMultDisj[i].getParameters()[0]));
			
			
			// Step 3: The contradiction
			if (!termSum.isConstant())
				throw new AssertionError("Error 2 in @lemma_:LA");
							
			Rational constant = termSum.getConstant();
			
			
			// < is strictly stronger than <= is strictly stronger than =
			if (foundLt) {
				if (constant.isNegative())
					throw new AssertionError("Error 4 in @lemma_:LA");
			} else if (foundLe) {
				if (constant.isNegative() || constant.equals(Rational.ZERO))
					throw new AssertionError("Error 3 in @lemma_:LA");
			} else if (foundEq)
				if (constant == Rational.ZERO)
					throw new AssertionError("Error 5 in @lemma_:LA");
			
		} else if (lemmaType == ":CC") {
			//Syntactical correctness
			ApplicationTerm termLemmaApp = convertApp(lemma);
			Object[] ccAnnotation = (Object[]) lemmaAnnotation;
			
			pm_func(termLemmaApp,"or");
			
			int arrayShortLength;
			
			Term termGoal;
			if (ccAnnotation[0] instanceof Term) {
				termGoal = (Term) ccAnnotation[0];
				arrayShortLength = termLemmaApp.getParameters().length - 1;
			} else {
				termGoal = mSkript.term("false");
				arrayShortLength = termLemmaApp.getParameters().length;
			}
			
			
			
			// The negated disjuncts
			ApplicationTerm[] termLemmaAppNegDisj = new ApplicationTerm[arrayShortLength]; //Negated Disjuncts WITHOUT not
			
			int j = 0;
			
			for (Term param : termLemmaApp.getParameters()) {
				ApplicationTerm paramApp = convertApp_hard(param);
				
				if (paramApp.equals(termGoal))
					continue;
				
				// Else: It must be a negation
				pm_func(paramApp,"not");
				
				if (j >= termLemmaAppNegDisj.length)
					throw new AssertionError("Error 0.5 in Lemma_:CC");
				
				termLemmaAppNegDisj[j] = convertApp_hard(paramApp.getParameters()[0]);
				j++;
			}
			
			if (j != termLemmaAppNegDisj.length)
				throw new AssertionError("Error 1 in Lemma_:CC");
			
			// Get the equalities, the annotations are ignored
			/* Old and wrong: The first equality is the goal, the others are the premises
			 * It doesn't have to be the first one.
			 */
			
			if (termGoal != mSkript.term("false"))
				pm_func(termGoal,"=");
			
			for (Term equality : termLemmaAppNegDisj)
				pm_func(equality,"=");
			
			Object[] annotValues = ccAnnotation;
			
			/* Get the subpaths. The HashMap contains pairs:
			 * - Key: Start & End of the path as Pair
			 * - Object: Path
			 */
			
			HashMap<SymmetricPair<Term>, Term[]> subpaths =
					new HashMap<SymmetricPair<Term>,Term[]>();
					
			Term termMainPathStart = null;
			Term termMainPathEnd = null;
			boolean mainPathFound = false;
			
			for (int i = 1; i < annotValues.length; i++) {
				if (annotValues[i] instanceof String)
					if (annotValues[i] == ":subpath")
						continue;
				
				if (annotValues[i] instanceof Term[]) {
					Term[] arrayTemp = (Term[]) annotValues[i];
					SymmetricPair<Term> pairTemp =
							new SymmetricPair<Term>(arrayTemp[0],arrayTemp[arrayTemp.length - 1]);
					
					if (arrayTemp.length < 2)
						System.out.println("");
					//System.out.println("Lange: " + arrayTemp.length);
					subpaths.put(pairTemp, arrayTemp);
					
					if (!mainPathFound) {
						termMainPathStart = arrayTemp[0];
						termMainPathEnd = arrayTemp[arrayTemp.length - 1];
						mainPathFound = true;
					}
				}
			}
			
			/* Get the premises. The HashMap contains pairs:
			 * - Key: Pair of the left term and the right term (which are equal by premise)
			 * - Object: Array of those terms
			 */
			HashSet<SymmetricPair<Term>> premises =
					new HashSet<SymmetricPair<Term>>();
									
			for (int i = 0; i < arrayShortLength; i++) {
				checkNumber(termLemmaAppNegDisj[i],2);							
				
				SymmetricPair<Term> pairTemp = new SymmetricPair<Term>(
						termLemmaAppNegDisj[i].getParameters()[0],
						termLemmaAppNegDisj[i].getParameters()[1]);
				premises.add(pairTemp);
			}
			
			// Real termGoal
			ApplicationTerm termGoalRealApp;
			if (termGoal.equals(mSkript.term("false"))) {
				termGoalRealApp = convertApp(mSkript.term("=", termMainPathStart, termMainPathEnd));
				SMTAffineTerm controlDiff =
						calculateTerm(termMainPathStart).add(
								calculateTerm(termMainPathEnd).negate());
				
				if (!controlDiff.isConstant() 
						|| controlDiff.getConstant().equals(Rational.ZERO))
					throw new AssertionError("Error 2 in Lemma_:CC");
			} else
				termGoalRealApp = convertApp(termGoal);
			
			
			// Now for the pathfinding
			checkNumber(termGoalRealApp,2);
			Term termStart = termGoalRealApp.getParameters()[0];
			Term termEnd = termGoalRealApp.getParameters()[1];
			
			checkEqualityPath(subpaths,premises,termStart,termEnd);
		} else if (lemmaType == ":trichotomy") {
			ApplicationTerm termDisj = convertApp(lemma);
			
			pm_func(termDisj, "or");
			
			checkNumber(termDisj,3);
			
			ApplicationTerm disjunct1App = convertApp_hard(termDisj.getParameters()[0]);
			ApplicationTerm disjunct2App = convertApp_hard(termDisj.getParameters()[1]);
			ApplicationTerm disjunct3App = convertApp_hard(termDisj.getParameters()[2]);
			
			// Find the equality
			
			ApplicationTerm equality;

			if (pm_func_weak(disjunct1App, "="))
				equality = disjunct1App;
			else if (pm_func_weak(disjunct2App, "="))
				equality = disjunct2App;
			else if (pm_func_weak(disjunct3App, "="))
				equality = disjunct3App;
			else
				throw new AssertionError("Error 1 in Lemma_trichotomy");
			
			if (!(SMTAffineTerm.create(equality.getParameters()[1]).isConstant()
					&& SMTAffineTerm.create(equality.getParameters()[1]).getConstant() == Rational.ZERO)
				&& !(SMTAffineTerm.create(equality.getParameters()[0]).isConstant()
					&& SMTAffineTerm.create(equality.getParameters()[0]).getConstant() == Rational.ZERO)) {
				throw new AssertionError("Error 2 in Lemma_trichotomy");
			}					
							
			// Uniformize the real disjuncts and the artificial should-be's and compare them
			HashSet<Term> disjunctsRealCalc = new HashSet<Term>(); //Disjuncts: real then calculated
			HashSet<Term> disjunctsArtCalc = new HashSet<Term>(); // Disjuncts: artificial then calculated
			
			disjunctsRealCalc.add(uniformizeInEquality(disjunct1App));
			disjunctsRealCalc.add(uniformizeInEquality(disjunct2App));
			disjunctsRealCalc.add(uniformizeInEquality(disjunct3App));

			disjunctsArtCalc.add(uniformizeInEquality(
					equality));
			disjunctsArtCalc.add(uniformizeInEquality(
					convertApp(mSkript.term("<", equality.getParameters()))));
			disjunctsArtCalc.add(uniformizeInEquality(
					convertApp(mSkript.term(">", equality.getParameters()))));
			
			if (!disjunctsRealCalc.equals(disjunctsArtCalc))
				throw new AssertionError("Error at the end of Lemma_trichotomy");
			
				
		} else {
			reportError("Cannot deal with lemma " + lemmaType);
		}				
		
		stackPush(lemma, lemmaApp);
	}
	
	
	public void walkTautology(ApplicationTerm tautologyApp) {
		AnnotatedTerm annTerm = (AnnotatedTerm) tautologyApp.getParameters()[0];
		String tautType = annTerm.getAnnotations()[0].getKey();
		Term tautology = annTerm.getSubterm();
		Term[] clause = termToClause(tautology);

		if (tautType == ":eq") {
			if (clause.length != 2)
				reportError("Tautology :eq must have two literals");
			
			boolean term1Negated = false;
			
			Term term1 = clause[0];
			Term term2 = clause[1];
			
			if (term1 instanceof ApplicationTerm)
				if (pm_func_weak(convertApp(term1),"not"))
					term1Negated = true;
			
			ApplicationTerm termNegApp = null; // The term t with (not t) 
			ApplicationTerm termPosApp = null; // the term without a not around
			
			if (term1Negated) {
				termNegApp = convertApp_hard(convertApp(term1).getParameters()[0]);
				termPosApp = convertApp_hard(term2);
			} else {
				pm_func(term2,"not");

				termNegApp = convertApp_hard(convertApp(term2).getParameters()[0]);
				termPosApp = convertApp_hard(term1);
			}
			
			String funcSymb = termNegApp.getFunction().getName();
			
			pm_func(termPosApp,funcSymb);
			
			ApplicationTerm termNegUnif = uniformizeInEquality(termNegApp);
			ApplicationTerm termPosUnif = uniformizeInEquality(termPosApp);
													
			if (!uniformedSame(termNegUnif,termPosUnif))
				throw new AssertionError("Error in @taut_eq");
		} else if (tautType == ":or+") {
			Term[] split = termToClause(unquote(negate(clause[0])));
			if (split.length < 2)
				reportError("Expected or-term in rule :or+ but got " + clause[0]);
			else {
				boolean problem = false;
				for (int i = 1; i < clause.length; i++) {
					if (split[i - 1] != clause[i])
						problem = true;
				}
				if (problem)
					reportError("Malformed tautology " + tautologyApp);
			}
		} else if (tautType == ":or-") {
			if (clause.length != 2 
					|| !checkOrMinus(unquote(clause[0]),clause[1]))
				reportError("Invalid application of rule :or-");
		} else if (tautType == ":termITE") {
			ApplicationTerm termOr = convertApp(tautology); // The term with or
			
			pm_func(termOr, "or");
			
			checkNumber(termOr,2);
			
			// Find the terms which may be re-ordered because of commutativity 
			
			Term termNotEq = null;
			ApplicationTerm equalityApp = null;
			ApplicationTerm equalityIteApp = null;
			Term equalityNotIte = null;
			boolean foundEq = false;
			
			if (termOr.getParameters()[0] instanceof ApplicationTerm) {
				ApplicationTerm termAppTemp = convertApp(termOr);
				if (pm_func_weak(termAppTemp,"=")
						&& pm_func_weak(termAppTemp.getParameters()[0],"ite")) {
					foundEq = true;
					equalityApp = convertApp(termOr.getParameters()[0]);
					termNotEq = termOr.getParameters()[1];
				}
			}
			
			if (!foundEq) {
				equalityApp = convertApp(termOr.getParameters()[1]);
				termNotEq = termOr.getParameters()[0];
			}
			
			if (equalityApp.getParameters()[0] instanceof ApplicationTerm) {
				ApplicationTerm termAppTemp2 = convertApp(equalityApp.getParameters()[0]);
				if (pm_func_weak(termAppTemp2, "ite")) {
					equalityIteApp = convertApp(equalityApp.getParameters()[0]);
					equalityNotIte = equalityApp.getParameters()[1];
				} else {
					equalityIteApp = convertApp(equalityApp.getParameters()[1]);
					equalityNotIte = equalityApp.getParameters()[0];
				}								
			}
			
			// Syntactical Correctness
			
			pm_func(equalityApp, "=");
			pm_func(equalityIteApp, "ite");
			
			checkNumber(equalityApp, 2);
			checkNumber(equalityIteApp, 3);
			
			// The Rule-Check
			
			if (termITEHelper_isEqual(termNotEq, equalityIteApp.getParameters()[0])) {
				if (equalityNotIte != equalityIteApp.getParameters()[2])
					throw new AssertionError("Error 1 in @taut_termITE");
			} else {
				if (equalityNotIte != equalityIteApp.getParameters()[1])
					throw new AssertionError("Error 2 in @taut_termITE");
			}
					
			
		} else {
			reportError("Unknown tautology rule " + tautType);
		}
		
		stackPush(tautology, tautologyApp);
	}

	void walkAsserted(ApplicationTerm assertedApp) {
		Term  assertedTerm = assertedApp.getParameters()[0];
		if (!mAssertions.contains(assertedTerm)) {
			reportError("Could not find asserted term " + assertedTerm);
		}
		/* Just return the part without @asserted */
		stackPush(assertedTerm, assertedApp);
	}
			
	void walkRewrite(ApplicationTerm rewriteApp) {
		/* Treatment:
		 *  - At first check if the rewrite rule was correctly executed.
		 *  - OLD: Secondly, remove the @rewrite and the annotation for later uses in the @eq-function.
		 */
		
		/* Get access to the internal terms */
		AnnotatedTerm termAppInnerAnn = convertAnn(rewriteApp.getParameters()[0]); //The annotated term inside the rewrite-term
		ApplicationTerm termEqApp = convertApp(termAppInnerAnn.getSubterm()); //The application term inside the annotated term inside the rewrite-term
		
		pm_func(termEqApp, "=");

		/* The result is simply the equality (without annotation).  
		 * Compute it first and check later.
		 */
		stackPush(termEqApp, rewriteApp);
		
		checkNumber(termEqApp,2);
		
		/* Read the rule and handle each differently */
		String rewriteRule = termAppInnerAnn.getAnnotations()[0].getKey();
		if (mDebug.contains("currently"))
			System.out.println("Rewrite-Rule: " + rewriteRule);
		if (mDebug.contains("hardTerm"))
			System.out.println("Term: " + rewriteApp.toStringDirect());
		if (rewriteRule == ":trueNotFalse") {
			if (termEqApp.getParameters()[1] != mSkript.term("false")) {
				throw new AssertionError("Error: The second argument of a rewrite of the rule " 
						+ rewriteRule + " should be true, but isn't.\n"
						+ "The term was " + termEqApp.toString());
			}
			
			ApplicationTerm termOldApp = convertApp(termEqApp.getParameters()[0]);
			pm_func(termOldApp,"=");
													
			boolean foundTrue = false;
			boolean foundFalse = false;
			
			for (Term subterm : termOldApp.getParameters()) {
				if (subterm == mSkript.term("false")) {
					foundFalse = true;
				}
				if (subterm == mSkript.term("true")) {
					foundTrue = true;
				}
				
				if (foundFalse && foundTrue) {
					return;
				}
			}
			
			throw new AssertionError("Error at the end of rule " + rewriteRule
					+ "!\n The term was " + rewriteApp.toStringDirect());
			
		} else if (rewriteRule == ":constDiff") {					
			if (termEqApp.getParameters()[1] != mSkript.term("false")) {
				throw new AssertionError("Error: The second argument of a rewrite of the rule " 
						+ rewriteRule + " should be false, but isn't.\n"
						+ "The term was " + termEqApp.toString());
			}
			
			ApplicationTerm termOldApp = convertApp(termEqApp.getParameters()[0]);
			pm_func(termOldApp,"=");
			
			HashSet<Term> constTerms = new HashSet<Term>();
			
			// Get all constant terms
			for (Term subterm : termOldApp.getParameters()) {
				if (subterm instanceof ConstantTerm) {
					constTerms.add(subterm);
				} else if (subterm instanceof ApplicationTerm) {
					// Maybe a negated constant
					ApplicationTerm subtermApp = convertApp(subterm);
					
					if (pm_func_weak(subtermApp, "-"))
						if (subtermApp.getParameters()[0] instanceof ConstantTerm)
							constTerms.add(subterm);
				}
				
			}
			
			if (mDebug.contains("newRules")) {
				System.out.println("The constant terms are:");
				for (Term termC : constTerms)
					System.out.println(termC.toStringDirect());
			}
			
			// Check if there are two different constant terms
			if (constTerms.size() <= 1)
				throw new AssertionError("Error at the end of rule " + rewriteRule
						+ "!\n The term was " + rewriteApp.toStringDirect());
			
			
		} else if (rewriteRule == ":eqTrue") {									
			ApplicationTerm termOldApp = convertApp(termEqApp.getParameters()[0]);					

			pm_func(termOldApp,"=");
			
			boolean multiconjunct = false;
			ApplicationTerm termNewApp = null; //Not nice: Initialisation as null
			if (termEqApp.getParameters()[1] instanceof ApplicationTerm)
				if (pm_func_weak(convertApp(termEqApp.getParameters()[1]), "and")) {
					termNewApp = convertApp(termEqApp.getParameters()[1]);
					multiconjunct = true;
				}					
								
			HashSet<Term> oldTerms = new HashSet<Term>();
			HashSet<Term> newTerms = new HashSet<Term>();
			
			oldTerms.addAll(Arrays.asList(termOldApp.getParameters()));
			if (multiconjunct)
				newTerms.addAll(Arrays.asList(termNewApp.getParameters()));
			else
				newTerms.add(termEqApp.getParameters()[1]);
			
			if (!oldTerms.contains(mSkript.term("true")))
				throw new AssertionError("Error 1 at " + rewriteRule + ".\n The term was " + termEqApp.toString());
			
			/* The line below is needed, to have a short equivalence check, even
			 * if more than one term is "true".
			*/
			newTerms.add(mSkript.term("true"));
			
			if (!oldTerms.equals(newTerms))
				throw new AssertionError("Error 2 at " + rewriteRule + ".\n The term was " + termEqApp.toString());
			
			// Not nice: j \notin I' isn't checked, but even if j \in I' it's still correct
			
		} else if (rewriteRule == ":eqFalse") {
			ApplicationTerm termOldApp = convertApp(termEqApp.getParameters()[0]);
			ApplicationTerm termNewApp = convertApp(termEqApp.getParameters()[1]);					

			pm_func(termOldApp, "=");
			pm_func(termNewApp, "not");
			
			boolean multidisjunct = false;
			ApplicationTerm termNewAppInnerApp = null; //Not nice: Initialisation as null
			if (termNewApp.getParameters()[0] instanceof ApplicationTerm)
				if (pm_func_weak(convertApp(termNewApp.getParameters()[0]), "or")) {
					termNewAppInnerApp = convertApp(termNewApp.getParameters()[0]);
					multidisjunct = true;
				}
			
			HashSet<Term> oldTerms = new HashSet<Term>();
			HashSet<Term> newTerms = new HashSet<Term>();
			
			oldTerms.addAll(Arrays.asList(termOldApp.getParameters()));
			if (multidisjunct)
				newTerms.addAll(Arrays.asList(termNewAppInnerApp.getParameters()));
			else
				newTerms.add(termNewApp.getParameters()[0]);
			
			if (!oldTerms.contains(mSkript.term("false")))
				throw new AssertionError("Error 1 at " + rewriteRule + ".\n The term was " + termEqApp.toString());
			
			/* The line below is needed, to have a short equivalence check, even
			 * if more than one term is "true".
			*/
			newTerms.add(mSkript.term("false"));
			
			if (!oldTerms.equals(newTerms))
				throw new AssertionError("Error 2 at " + rewriteRule + ".\n The term was " + termEqApp.toString());
			
			// Not nice: j \notin I' isn't checked, but even if j \in I' it's still correct
		
		} else if (rewriteRule == ":eqSame") {
			if (termEqApp.getParameters()[1] != mSkript.term("true")) {
				throw new AssertionError("Error: The second argument of a rewrite of the rule "
						+ rewriteRule + " should be true, but isn't.\n"
						+ "The term was " + termEqApp.toString());
			}
			
			ApplicationTerm termOldApp = convertApp(termEqApp.getParameters()[0]);
			
			pm_func(termOldApp, "=");
													
			Term termComp = termOldApp.getParameters()[0]; //compare-term
			for (Term subterm : termOldApp.getParameters())
				if (subterm != termComp)
					throw new AssertionError("Error 2 at rule " + rewriteRule + "!\n The term was " + rewriteApp.toStringDirect());
		
		} else if (rewriteRule == ":eqSimp") {
			ApplicationTerm termOldApp = convertApp(termEqApp.getParameters()[0]);
			ApplicationTerm termNewApp = convertApp(termEqApp.getParameters()[1]);
			
			pm_func(termOldApp, "=");
			pm_func(termNewApp, "=");
			
			HashSet<Term> oldTerms = new HashSet<Term>();
			HashSet<Term> newTerms = new HashSet<Term>();
			
			oldTerms.addAll(Arrays.asList(termOldApp.getParameters()));
			newTerms.addAll(Arrays.asList(termNewApp.getParameters()));
													
			if (!oldTerms.equals(newTerms))
				throw new AssertionError("Error 1 at " + rewriteRule + ".\n The term was " + termEqApp.toString());
			
			// Not nice: I' \subsetneq I isn't checked, but even if I' \supset I, it's still correct
			// Not nice: Not checked if there aren't two doubled terms in termNewApp, but even if there are, it's still correct
			
		}  else if (rewriteRule == ":eqBinary") {					
			ApplicationTerm termOldApp = convertApp(termEqApp.getParameters()[0]);
			ApplicationTerm termNewApp = convertApp(termEqApp.getParameters()[1]);
			ApplicationTerm termNewAppInnerApp = convertApp(termNewApp.getParameters()[0]);
			
			pm_func(termOldApp, "=");
			pm_func(termNewApp, "not");
			
			// Is it a binary equality?
			if (termOldApp.getParameters().length == 2) {
				pm_func(termNewAppInnerApp, "not");
				if (termOldApp != termNewAppInnerApp.getParameters()[0])
					throw new AssertionError("Error A in " + rewriteRule);
				return;
			}
			
			pm_func(termNewAppInnerApp, "or");
			
			// The array which contains the equalities
			ApplicationTerm[] arrayNewEqApp = 
					new ApplicationTerm[termNewAppInnerApp.getParameters().length];
			Term[] arrayOldTerm = termOldApp.getParameters();
			
			for (int i = 0; i < termNewAppInnerApp.getParameters().length; i++) {
				ApplicationTerm termIneqApp = convertApp(termNewAppInnerApp.getParameters()[i]);
				pm_func(termIneqApp,"not");
				
				arrayNewEqApp[i] = convertApp(termIneqApp.getParameters()[0]);
				pm_func(arrayNewEqApp[i],"=");
			}
			
			boolean[] eqFound = new boolean[arrayNewEqApp.length];
			
			for (int i = 0; i < eqFound.length; i++)
				eqFound[i] = false;
			
			// Look for each two distinct terms (j > i) if there exists a fitting equality
			for (int i = 0; i < arrayOldTerm.length; i++) {
				for (int j = i + 1; j < arrayOldTerm.length; j++) {
//							boolean found = false;
					for (int k = 0; k < arrayNewEqApp.length; k++) {
						if (!eqFound[k]) {
							checkNumber(arrayNewEqApp[k], 2);
							
							if (arrayNewEqApp[k].getParameters()[0] == arrayOldTerm[i]
									&& arrayNewEqApp[k].getParameters()[1] == arrayOldTerm[j])										
								eqFound[k] = true; // found = true;
							
							if (arrayNewEqApp[k].getParameters()[1] == arrayOldTerm[i]
									&& arrayNewEqApp[k].getParameters()[0] == arrayOldTerm[j])
								eqFound[k] = true; // found = true;
						}
					}
					
					// Wrong, because the rule allows to leave out disjuncts.
//							if (!found)
//							{
//								throw new AssertionError("Error: Couldn't find the equality that " 
//										+ "corresponds to " + arrayOldTerm[i].toStringDirect()
//										+ " and " + arrayOldTerm[j].toStringDirect() + ".\n"
//										+ "The term was " + term.toStringDirect());
//							}
				}
			}
			
			// At last check if each equality is alright
			for (int i = 0; i < eqFound.length; i++)
				if (!eqFound[i])
					throw new AssertionError("Error: Coulnd't associate the equality " 
							+ arrayNewEqApp[i] + "\n. The term was " + rewriteApp.toStringDirect());

		} else if (rewriteRule == ":distinctBool") {
			if (termEqApp.getParameters()[1] != mSkript.term("false"))
				throw new AssertionError("Error: The second argument of a rewrite of the rule "
						+ rewriteRule + " should be false, but it isn't.\n"
						+ "The term was " + termEqApp.toString());
			
			ApplicationTerm termOldApp = convertApp(termEqApp.getParameters()[0]);
			
			pm_func(termOldApp, "distinct");
			
			// Check if there are at least three parameters
			if (termOldApp.getParameters().length < 3)
				throw new AssertionError("Error 1 at " + rewriteRule);
			
			// Check if two are they are all boolean
			for (Term subterm : termOldApp.getParameters())
				if (subterm.getSort() != mSkript.sort("Bool"))
					throw new AssertionError("Error 2 at " + rewriteRule);
			
		
		} else if (rewriteRule == ":distinctSame") {					
			if (termEqApp.getParameters()[1] != mSkript.term("false")) {
				throw new AssertionError("Error: The second argument of a rewrite of the rule "
						+ rewriteRule + " should be false, but it isn't.\n"
						+ "The term was " + termEqApp.toString());
			}
			
			ApplicationTerm termOldApp = convertApp(termEqApp.getParameters()[0]);
			
			pm_func(termOldApp, "distinct");
			
			// Check if two are the same
			for (int i = 0; i < termOldApp.getParameters().length; i++)
				for (int j = i + 1; j < termOldApp.getParameters().length; j++)
					if (termOldApp.getParameters()[i] == termOldApp.getParameters()[j]) {
						return;
					}
			
			throw new AssertionError("Error at the end of rule " + rewriteRule 
					+ "!\n The term was " + rewriteApp.toStringDirect());
		
		} else if (rewriteRule == ":distinctNeg") {
			if (termEqApp.getParameters()[1] != mSkript.term("true")) {
				throw new AssertionError("Error: The second argument of a rewrite of the rule "
						+ rewriteRule + " should be true, but it isn't.\n"
						+ "The term was " + termEqApp.toString());
			}
			
			ApplicationTerm termOldApp = convertApp(termEqApp.getParameters()[0]);
			
			pm_func(termOldApp, "distinct");
			
			if (termOldApp.getParameters().length != 2)
				throw new AssertionError("Error 1 at " + rewriteRule);
			
			// Check if one is the negation of the other
			Term term1 = termOldApp.getParameters()[0];
			Term term2 = termOldApp.getParameters()[1];
			if (term1 != negate(term2))
				throw new AssertionError("Error 2 at " + rewriteRule);
		
		} else if (rewriteRule == ":distinctTrue") {
			ApplicationTerm termNewApp = convertApp(termEqApp.getParameters()[1]);
			ApplicationTerm termOldApp = convertApp(termEqApp.getParameters()[0]);
			
			pm_func(termOldApp, "distinct");
			pm_func(termNewApp,"not");
			
			if (termOldApp.getParameters().length != 2)
				throw new AssertionError("Error 2 at " + rewriteRule);
			
			// Check if one is true
			Term term1 = termOldApp.getParameters()[0];
			Term term2 = termOldApp.getParameters()[1];
			
			Term termNotTrue; // The term on the left side which is not true
			
			if (term1.equals(mSkript.term("true")))
				termNotTrue = term2;
			else if (term2.equals(mSkript.term("true")))
				termNotTrue = term1;
			else
				throw new AssertionError("Error 1 at " + rewriteRule);						
			
			if (termNewApp.getParameters()[0] != termNotTrue)
				throw new AssertionError("Error 2 at " + rewriteRule);
		
		} else if (rewriteRule == ":distinctFalse") {
			Term termNew = termEqApp.getParameters()[1];
			ApplicationTerm termOldApp = convertApp(termEqApp.getParameters()[0]);
			
			pm_func(termOldApp, "distinct");
			
			if (termOldApp.getParameters().length != 2)
				throw new AssertionError("Error 2 at " + rewriteRule);
			
			// Check if one is false
			Term term1 = termOldApp.getParameters()[0];
			Term term2 = termOldApp.getParameters()[1];
			
			Term termNotFalse; // The term on the left side which is not true
			
			if (term1.equals(mSkript.term("false")))
				termNotFalse = term2;
			else if (term2.equals(mSkript.term("false")))
				termNotFalse = term1;
			else
				throw new AssertionError("Error 1 at " + rewriteRule);						
			
			if (termNew != termNotFalse)
				throw new AssertionError("Error 2 at " + rewriteRule);
		
		} else if (rewriteRule == ":distinctBinary") {					
			ApplicationTerm termOldApp = convertApp(termEqApp.getParameters()[0]);
			ApplicationTerm termNewApp = convertApp(termEqApp.getParameters()[1]);
			ApplicationTerm termNewAppInnerApp = convertApp(termNewApp.getParameters()[0]);
			
			pm_func(termOldApp, "distinct");
			
			// Maybe it's the distinctBoolEq-rule
			if (pm_func_weak(termNewApp, "=")) {
				checkNumber(termOldApp,2);
				checkNumber(termNewApp,2);
				
				Term termP1 = termOldApp.getParameters()[0]; // The first Boolean variable
				Term termP2 = termOldApp.getParameters()[1]; // The first Boolean variable
				
				if (termP1.getSort() != mSkript.sort("Bool")
						|| termP2.getSort() != mSkript.sort("Bool"))
					throw new AssertionError("Error 1 in :distinctBinary_distinctBoolEq");
				
				boolean correctRightSide = false;
				
				// Four cases need to be checked
				if (termNewApp.getParameters()[0].equals(termP1)
						&& termNewApp.getParameters()[1].equals(negate(termP2)))
					correctRightSide = true;
				
				if (termNewApp.getParameters()[0].equals(termP2)
						&& termNewApp.getParameters()[1].equals(negate(termP1)))
					correctRightSide = true;
				
				if (termNewApp.getParameters()[1].equals(termP1)
						&& termNewApp.getParameters()[0].equals(negate(termP2)))
					correctRightSide = true;
				
				if (termNewApp.getParameters()[1].equals(termP2)
						&& termNewApp.getParameters()[0].equals(negate(termP1)))
					correctRightSide = true;
				
				if (!correctRightSide)
					throw new AssertionError("Error at the end of :distinctBinary_distinctBoolEq");
			} else {
				pm_func(termNewApp, "not");
				
				// The array which contains the equalities
				Term[] arrayNewEq = null;
				Term[] arrayOldTerm = termOldApp.getParameters(); 
				
			
				if (pm_func_weak(termNewAppInnerApp,"or")) {
					arrayNewEq = termNewAppInnerApp.getParameters(); 					 
				} else {
					arrayNewEq = termNewApp.getParameters();
				}
				
				boolean[] eqFound = new boolean[arrayNewEq.length];
				
				for (int i = 0; i < eqFound.length; i++)
					eqFound[i] = false;
				
				// Look for each two distinct terms (j > i) if there exists a fitting equality
				for (int i = 0; i < arrayOldTerm.length; i++) {
					for (int j = i + 1; j < arrayOldTerm.length; j++) {
						boolean found = false;
						for (int k = 0; k < arrayNewEq.length; k++) {
							if (!eqFound[k]) {
								ApplicationTerm termAppTemp = convertApp(arrayNewEq[k]);
								pm_func(termAppTemp, "=");
								checkNumber(termAppTemp,2);
								
								if (termAppTemp.getParameters()[0] == arrayOldTerm[i]
										&& termAppTemp.getParameters()[1] == arrayOldTerm[j]) {
									found = true;
									eqFound[k] = true;
								}
								if (termAppTemp.getParameters()[1] == arrayOldTerm[i]
										&& termAppTemp.getParameters()[0] == arrayOldTerm[j]) {
									found = true;
									eqFound[k] = true;
								}
							}
						}
						
						if (!found) {
							throw new AssertionError("Error: Couldn't find the equality that " 
									+ "corresponds to " + arrayOldTerm[i].toStringDirect()
									+ " and " + arrayOldTerm[j].toStringDirect() + ".\n"
									+ "The term was " + rewriteApp.toStringDirect());
						}
					}
				}
				
				// At last check if each equality is alright
				for (int i = 0; i < eqFound.length; i++)
					if (!eqFound[i])
						throw new AssertionError("Error: Coulnd't associate the equality " 
								+ arrayNewEq[i] + "\n. The term was " + rewriteApp.toStringDirect());
										
			}
		} else if (rewriteRule == ":notSimp") {
			/* The first argument of the rewrite has to be the 
			 * double-negated version of the second argument or
			 * "(not true)" iff the second is "false" or
			 * "(not false)" iff the second is "true".
			 */

			
			// Check syntactical correctness
			ApplicationTerm innerAppTermFirstNeg = convertApp(termEqApp.getParameters()[0]);
			pm_func(innerAppTermFirstNeg, "not");
			
			if ((innerAppTermFirstNeg.getParameters()[0] == mSkript.term("false")
					&& termEqApp.getParameters()[1] == mSkript.term("true"))
				|| (innerAppTermFirstNeg.getParameters()[0] == mSkript.term("true") 
					&& termEqApp.getParameters()[1] == mSkript.term("false"))) {
				return;
			}
			
			ApplicationTerm innerAppTermSecondNeg = convertApp(innerAppTermFirstNeg.getParameters()[0]);
			pm_func(innerAppTermSecondNeg, "not");
			
			// Check if the rule was executed correctly
			if (innerAppTermSecondNeg.getParameters()[0] != termEqApp.getParameters()[1]) {
				throw new AssertionError("Error: The rule \"notSimp\" couldn't be verified, because the following "
						+ "two terms aren't the same: " + innerAppTermSecondNeg.getParameters()[0].toString() 
						+ " and " + termEqApp.getParameters()[1].toStringDirect() + ".\n"
						+ "The original term was: " + rewriteApp.toStringDirect());
			}
			// Important: The return is done later, the following is false: 
			// return innerAppTerm.getParameters()[1];
		
		} else if (rewriteRule == ":orSimp") {
			ApplicationTerm termOldApp = convertApp(termEqApp.getParameters()[0]);
			boolean multidisjunct = true;
			Term termNew = termEqApp.getParameters()[1];
			ApplicationTerm termNewApp = null;

			pm_func(termOldApp,"or");
			
								
			HashSet<Term> oldDisjuncts = new HashSet<Term>();
			HashSet<Term> newDisjuncts = new HashSet<Term>();
			
				
			oldDisjuncts.addAll(Arrays.asList(termOldApp.getParameters()));
			
			oldDisjuncts.remove(mSkript.term("false"));
			
			if (oldDisjuncts.size() <= 1)
				multidisjunct = false;
			
			if (multidisjunct) {
				termNewApp = convertApp(termNew);
				pm_func(termNewApp,"or");
			}						
			
			if (multidisjunct)
				newDisjuncts.addAll(Arrays.asList(termNewApp.getParameters()));
			else
				newDisjuncts.add(termNew);
			
			
			/* OLD: The line below is needed, to have a short equivalence check, even
			 * if the new term still contains a disjunct false
			*/
			//newDisjuncts.add(mSkript.term("false"));
			
			if (!oldDisjuncts.equals(newDisjuncts)) {
				newDisjuncts.remove(mSkript.term("false"));
				if (!oldDisjuncts.equals(newDisjuncts))
					throw new AssertionError("Error 2 at " + rewriteRule 
							+ ".\n The term was " + termEqApp.toStringDirect());
			}
			// Not nice: I' \subsetneq I isn't checked, but even if I' \supseteq I it's still correct
			// Not nice: The work with false
			
		} else if (rewriteRule == ":orTaut") {					
			if (!(termEqApp.getParameters()[1] == mSkript.term("true"))) {
				throw new AssertionError("Error: The second argument of a rewrite of the rule "
						+ rewriteRule + " should be true, but it isn't.\n"
						+ "The term was " + termEqApp.toString());
			}
			
			ApplicationTerm termOldApp = convertApp(termEqApp.getParameters()[0]);
			pm_func(termOldApp, "or");
			
			// Case 1: One disjunct is true
			for (Term disjunct : termOldApp.getParameters())
				if (disjunct == mSkript.term("true")) {
					return;
				}
			
			// Case 2: One disjunct is the negate of another
			for (Term disjunct1 : termOldApp.getParameters())
				for (Term disjunct2 : termOldApp.getParameters())
					if (disjunct1 == negate(disjunct2)) {
						return;
					}
			
			throw new AssertionError("Error at the end of rule " + rewriteRule 
					+ "!\n The term was " + rewriteApp.toStringDirect());						
		} else if (rewriteRule == ":iteTrue") {									
			ApplicationTerm termOldApp = convertApp(termEqApp.getParameters()[0]);

			pm_func(termOldApp,"ite");
			
			checkNumber(termOldApp.getParameters(),3);
			// checkNumber(termEqApp.getParameters(),2); Is already checked	
			
			//Check syntactical correctness
			if (termOldApp.getParameters()[0] != mSkript.term("true"))
				throw new AssertionError("Error 1 at " + rewriteRule);
			
			if (termOldApp.getParameters()[1] != termEqApp.getParameters()[1])
				throw new AssertionError("Error 2 at " + rewriteRule);
		} else if (rewriteRule == ":iteFalse") {									
			ApplicationTerm termOldApp = convertApp(termEqApp.getParameters()[0]);

			pm_func(termOldApp,"ite");
			
			checkNumber(termOldApp.getParameters(),3);
			//checkNumber(termEqApp.getParameters(),2);					
			
			//Check syntactical correctness
			if (termOldApp.getParameters()[0] != mSkript.term("false"))
				throw new AssertionError("Error 1 at " + rewriteRule);
			
			if (termOldApp.getParameters()[2] != termEqApp.getParameters()[1])
				throw new AssertionError("Error 2 at " + rewriteRule);
		} else if (rewriteRule == ":iteSame") {									
			ApplicationTerm termOldApp = convertApp(termEqApp.getParameters()[0]);

			pm_func(termOldApp,"ite");
			
			checkNumber(termOldApp.getParameters(),3);
			
			//Check syntactical correctness					
			if (termOldApp.getParameters()[1] != termEqApp.getParameters()[1])
				throw new AssertionError("Error 2 at " + rewriteRule);
			
			if (termOldApp.getParameters()[2] != termEqApp.getParameters()[1])
				throw new AssertionError("Error 3 at " + rewriteRule);
		} else if (rewriteRule == ":iteBool1") {									
			ApplicationTerm termOldApp = convertApp(termEqApp.getParameters()[0]);

			pm_func(termOldApp,"ite");
			
			checkNumber(termOldApp.getParameters(),3);
			
			//Check syntactical correctness
			if (termOldApp.getParameters()[0] != termEqApp.getParameters()[1])
				throw new AssertionError("Error 1 at " + rewriteRule);
			
			if (termOldApp.getParameters()[1] != mSkript.term("true"))
				throw new AssertionError("Error 2 at " + rewriteRule);
			
			if (termOldApp.getParameters()[2] != mSkript.term("false"))
				throw new AssertionError("Error 3 at " + rewriteRule);
		} else if (rewriteRule == ":iteBool2") {								
			ApplicationTerm termOldApp = convertApp(termEqApp.getParameters()[0]);

			pm_func(termOldApp,"ite");
			
			checkNumber(termOldApp.getParameters(),3);
			
			//Check syntactical correctness
			if (mSkript.term("not",termOldApp.getParameters()[0]) 
					!= termEqApp.getParameters()[1])
				throw new AssertionError("Error 1 at " + rewriteRule);
			
			if (termOldApp.getParameters()[1] != mSkript.term("false"))
				throw new AssertionError("Error 2 at " + rewriteRule);
			
			if (termOldApp.getParameters()[2] != mSkript.term("true"))
				throw new AssertionError("Error 3 at " + rewriteRule);
		} else if (rewriteRule == ":iteBool3") {									
			ApplicationTerm termOldApp = convertApp(termEqApp.getParameters()[0]);
			ApplicationTerm termNewApp = convertApp(termEqApp.getParameters()[1]);

			pm_func(termOldApp,"ite");
			pm_func(termNewApp,"or");
			
			checkNumber(termOldApp,3);
			checkNumber(termNewApp,2);
			
			// Names as in the documentation proof.pdf
			Term t0 = termOldApp.getParameters()[0];
			Term t1 = termOldApp.getParameters()[1];
			Term t2 = termOldApp.getParameters()[2];
			
			//Check syntactical correctness					
			if (t1 != mSkript.term("true"))
				throw new AssertionError("Error 2 at " + rewriteRule);

			// or is commutative
			if (termNewApp.getParameters()[0] != t0 && termNewApp.getParameters()[1] != t0)
				throw new AssertionError("Error 4 at " + rewriteRule);
			
			if (termNewApp.getParameters()[0] != t2 && termNewApp.getParameters()[1] != t2)
				throw new AssertionError("Error 5 at " + rewriteRule);					
		} else if (rewriteRule == ":iteBool4") {									
			ApplicationTerm termOldApp = convertApp(termEqApp.getParameters()[0]);
			ApplicationTerm termNewApp = convertApp(termEqApp.getParameters()[1]);
			ApplicationTerm termNewAppInnerApp = convertApp(termNewApp.getParameters()[0]);
			
			checkNumber(termOldApp,3);
			checkNumber(termNewAppInnerApp,2);
			
			// Names as in the documentation proof.pdf
			Term t0 = termOldApp.getParameters()[0];
			Term t1 = termOldApp.getParameters()[1];
			Term t2 = termOldApp.getParameters()[2];

			pm_func(termOldApp,"ite");
			pm_func(termNewApp,"not");
			pm_func(termNewAppInnerApp,"or");
			
			//Check syntactical correctness
			if (t1 != mSkript.term("false"))
				throw new AssertionError("Error 2 at " + rewriteRule);

			// or is commutative
			if (termNewAppInnerApp.getParameters()[0] != t0 && termNewAppInnerApp.getParameters()[1] != t0)
					throw new AssertionError("Error 4 at " + rewriteRule);
				
			if (termNewAppInnerApp.getParameters()[0] != mSkript.term("not",t2)
					&& termNewAppInnerApp.getParameters()[1] != mSkript.term("not",t2))
					throw new AssertionError("Error 5 at " + rewriteRule);
							
		} else if (rewriteRule == ":iteBool5") {								
			ApplicationTerm termOldApp = convertApp(termEqApp.getParameters()[0]);
			ApplicationTerm termNewApp = convertApp(termEqApp.getParameters()[1]);

			pm_func(termOldApp,"ite");
			pm_func(termNewApp,"or");

			checkNumber(termOldApp,3);
			checkNumber(termNewApp,2);
			
			// Names as in the documentation proof.pdf
			Term t0 = termOldApp.getParameters()[0];
			Term t1 = termOldApp.getParameters()[1];
			Term t2 = termOldApp.getParameters()[2];
			
			//Check syntactical correctness
			if (t2 != mSkript.term("true"))
				throw new AssertionError("Error 3 at " + rewriteRule);

			// or is commutative
			if (termNewApp.getParameters()[0] != t1
					&& termNewApp.getParameters()[1] != t1)
					throw new AssertionError("Error 4 at " + rewriteRule);
				
			if (termNewApp.getParameters()[0] != mSkript.term("not",t0)
					&& termNewApp.getParameters()[1] != mSkript.term("not",t0))
					throw new AssertionError("Error 3 at " + rewriteRule);
			
		} else if (rewriteRule == ":iteBool6") {			
			ApplicationTerm termOldApp = convertApp(termEqApp.getParameters()[0]);
			ApplicationTerm termNewApp = convertApp(termEqApp.getParameters()[1]);
			ApplicationTerm termNewAppInnerApp = convertApp(termNewApp.getParameters()[0]);

			pm_func(termOldApp,"ite");
			pm_func(termNewApp,"not");
			pm_func(termNewAppInnerApp,"or");

			checkNumber(termOldApp,3);
			checkNumber(termNewAppInnerApp,2);
			
			// Names as in the documentation proof.pdf
			Term t0 = termOldApp.getParameters()[0];
			Term t1 = termOldApp.getParameters()[1];
			Term t2 = termOldApp.getParameters()[2];
			
			//Check syntactical correctness
			if (t2 != mSkript.term("false"))
				throw new AssertionError("Error 3 at " + rewriteRule);

			// or is commutative
			if (termNewAppInnerApp.getParameters()[0] != mSkript.term("not",t0)
					&& termNewAppInnerApp.getParameters()[1] != mSkript.term("not",t0))
				throw new AssertionError("Error 4 at " + rewriteRule);
			
			if (termNewAppInnerApp.getParameters()[0] != mSkript.term("not",t1)
					&& termNewAppInnerApp.getParameters()[1] != mSkript.term("not",t1))
				throw new AssertionError("Error 5 at " + rewriteRule);					
		} else if (rewriteRule == ":andToOr") {					
			ApplicationTerm termOldApp = convertApp(termEqApp.getParameters()[0]);
			ApplicationTerm termNewApp = convertApp(termEqApp.getParameters()[1]);
			ApplicationTerm termNewAppInnerApp = convertApp(termNewApp.getParameters()[0]);

			pm_func(termOldApp, "and");
			pm_func(termNewApp, "not");
			pm_func(termNewAppInnerApp, "or");
			
			// Check if they are the same
			// HashSets are needed to allow permutations
			
			HashSet<Term> oldTerms = new HashSet<Term>();
			HashSet<Term> newTermsInner = new HashSet<Term>();
			
			oldTerms.addAll(Arrays.asList(termOldApp.getParameters()));
			
			for (int i = 0; i < termNewAppInnerApp.getParameters().length; i++) {
				ApplicationTerm termAppTemp = convertApp(termNewAppInnerApp.getParameters()[i]);
				pm_func(termAppTemp,"not");
				newTermsInner.add(termAppTemp.getParameters()[0]);
			}
			
			if (!oldTerms.equals(newTermsInner))
				throw new AssertionError("Error at rule " + rewriteRule
						+ "!\n The term was " + rewriteApp.toStringDirect());
		} else if (rewriteRule == ":xorToDistinct") {				
			ApplicationTerm termOldApp = convertApp(termEqApp.getParameters()[0]);
			ApplicationTerm termNewApp = convertApp(termEqApp.getParameters()[1]);

			pm_func(termOldApp, "xor");
			pm_func(termNewApp, "distinct");
			
			if (termOldApp.getParameters().length != termNewApp.getParameters().length)
				throw new AssertionError("Error 1 at " + rewriteRule);
			
			for (int i = 0; i < termOldApp.getParameters().length; i++)
				if (!termOldApp.getParameters() [i].equals(
						termNewApp.getParameters()[i]))
					throw new AssertionError("Error 2 at " + rewriteRule);								
			
			// Nicer, but didn't work:
			//if (!termOldApp.getParameters().equals(termNewApp.getParameters()))						
			
		} else if (rewriteRule == ":impToOr") {			
			ApplicationTerm termOldApp = convertApp(termEqApp.getParameters()[0]);
			ApplicationTerm termNewApp = convertApp(termEqApp.getParameters()[1]);

			pm_func(termOldApp, "=>");
			pm_func(termNewApp, "or");
			
			// Check if they are the same
			// HashSets are needed to allow permutations
			
			HashSet<Term> oldTerms = new HashSet<Term>();
			HashSet<Term> newTerms = new HashSet<Term>();
			
			for (int i = 0; i < termOldApp.getParameters().length - 1; i++)
				oldTerms.add(termOldApp.getParameters()[i]);
			
			Term termImp = termOldApp.getParameters()[termOldApp.getParameters().length - 1];
				
			if (termImp != termNewApp.getParameters()[0])
				throw new AssertionError("Error 1 at " + rewriteRule);
			
			for (int i = 1; i < termNewApp.getParameters().length; i++) {
				ApplicationTerm termAppTemp = convertApp(termNewApp.getParameters()[i]);
				pm_func(termAppTemp,"not");
				newTerms.add(termAppTemp.getParameters()[0]);
			}
			
			if (!oldTerms.equals(newTerms))
				throw new AssertionError("Error at rule " + rewriteRule	+ "!\n The term was " + rewriteApp.toStringDirect());
			
			
		} else if (rewriteRule == ":strip") {
			//Term which has to be stripped, annotated term
			AnnotatedTerm stripAnnTerm = convertAnn(termEqApp.getParameters()[0]);
			if (stripAnnTerm.getSubterm() != termEqApp.getParameters()[1]) {
				throw new AssertionError("Error: Couldn't verify a strip-rewrite. Those two terms should be the same but arent"
						+ stripAnnTerm.getSubterm() + "vs. " + termEqApp.getParameters()[1] + ".");
			}
		
		} else if (rewriteRule == ":canonicalSum") {
			Term termOld = termEqApp.getParameters()[0];
			Term termNew = termEqApp.getParameters()[1];
			
			if (!calculateTerm(termOld).equals(
					calculateTerm(termNew)))
				throw new AssertionError("Error at " + rewriteRule);
		} else if (rewriteRule == ":gtToLeq0" || rewriteRule == ":geqToLeq0"
				|| rewriteRule == ":ltToLeq0" || rewriteRule == ":leqToLeq0") {
			ApplicationTerm termNewIneqApp; //the inequality of termAfterRewrite
			
			ApplicationTerm termOldApp = convertApp(termEqApp.getParameters()[0]); //termBeforeRewrite
			ApplicationTerm termNewApp = convertApp(termEqApp.getParameters()[1]);
			
			checkNumber(termOldApp,2);
			checkNumber(termNewApp,1);
			
			if (!((rewriteRule == ":gtToLeq0" && pm_func_weak(termOldApp,">"))
					|| (rewriteRule == ":geqToLeq0" && pm_func_weak(termOldApp, ">="))
					|| (rewriteRule == ":ltToLeq0" && pm_func_weak(termOldApp, "<"))
					|| (rewriteRule == ":leqToLeq0" && pm_func_weak(termOldApp, "<=")))) {
				throw new AssertionError("Expected not the function symbol "
						+ termOldApp.getFunction().getName() + " for the rule "
						+ rewriteRule + ". \n The term is: " + termEqApp.toString());
			}
			
			Term termT1 = termOldApp.getParameters()[0]; //t_1 and t_2 as in the documentation proof.pdf
			Term termT2 = termOldApp.getParameters()[1];
			
			// The second term may be a negation
			if (rewriteRule == ":ltToLeq0" || rewriteRule == ":gtToLeq0") {
				pm_func(termNewApp,"not");
				
				termNewIneqApp = convertApp(termNewApp.getParameters()[0]);
				
			} else {
				termNewIneqApp = termNewApp;
			}
			
			pm_func(termNewIneqApp, "<=");
			
			checkNumber(termNewIneqApp,2);
			
			// Warning: Code almost-duplicates (Random number: 29364)
			SMTAffineTerm termAffTemp = calculateTerm(termNewIneqApp.getParameters()[1]);
			isConstant(termAffTemp,Rational.ZERO);
			
			SMTAffineTerm leftside = calculateTerm(termNewIneqApp.getParameters()[0]);

			SMTAffineTerm termT1Aff = calculateTerm(termT1);
			SMTAffineTerm termT2Aff = calculateTerm(termT2);
			
			if (rewriteRule == ":gtToLeq0" || rewriteRule == ":leqToLeq0") {
				if (!leftside.equals(termT1Aff.add(termT2Aff.negate()))) {
					throw new AssertionError("Error: Wrong term on the left side of "
							+ "the new inequality. The term was: " + rewriteApp.toStringDirect() + "\n"
							+ "Same should be " + leftside.toStringDirect()
							+ " and " + termT1Aff.add(termT2Aff.negate()).toStringDirect() + "\n"
							+ "Random number: 02653");
				}
				// Then the rule was correctly executed
			} else {
				if (!leftside.equals(termT2Aff.add(termT1Aff.negate()))) {
					throw new AssertionError("Error: Wrong term on the left side of "
							+ "the new inequality. The term was: " + termEqApp.toStringDirect() + "\n"
							+ "Same should be " + leftside.toStringDirect()
							+ " and " + termT2Aff.add(termT1Aff.negate()).toStringDirect() + "\n"
							+ "Random number: 20472");
				}
				// Then the rule was correctly executed
			}				
		
		} else if (rewriteRule == ":leqTrue") {
			ApplicationTerm termOldApp = convertApp(termEqApp.getParameters()[0]);
			checkNumber(termOldApp,2);

			pm_func(termOldApp,"<=");
								
			SMTAffineTerm constant = calculateTerm(
					convertConst_Neg(termOldApp.getParameters()[0]));
			
			// Rule-Execution was wrong if c > 0 <=> -c < 0
			if (constant.negate().getConstant().isNegative())
				throw new AssertionError("Error 2 at " + rewriteRule);
			
			SMTAffineTerm termTemp = calculateTerm(termOldApp.getParameters()[1]);
			
			isConstant(termTemp,Rational.ZERO);
			
			if (termEqApp.getParameters()[1] != mSkript.term("true"))
				throw new AssertionError("Error 4 at " + rewriteRule);
		} else if (rewriteRule == ":leqFalse") {
			ApplicationTerm termOldApp = convertApp(termEqApp.getParameters()[0]);

			pm_func(termOldApp,"<=");
			
			checkNumber(termOldApp, 2);
								
			SMTAffineTerm constant = calculateTerm(
					convertConst_Neg(termOldApp.getParameters()[0]));
			
			// Rule-Execution was wrong if c <= 0 <=> c < 0 || c = 0
			if (constant.getConstant().isNegative()
					|| isConstant_weak(constant,Rational.ZERO))
				throw new AssertionError("Error 2 at " + rewriteRule);
			
			SMTAffineTerm termTemp = calculateTerm(termOldApp.getParameters()[1]);
			isConstant(termTemp,Rational.ZERO);
			
			if (termEqApp.getParameters()[1] != mSkript.term("false"))
				throw new AssertionError("Error 4 at " + rewriteRule);
		} else if (rewriteRule == ":desugar") {					
			/* All Int-Parameters of the outermost function
			 * are getting converted into Real-Parameters
			 */
			
			ApplicationTerm termOldApp = convertApp(termEqApp.getParameters()[0]);
			ApplicationTerm termNewApp = convertApp(termEqApp.getParameters()[1]);
			
			// Both must have the same function symbol
			pm_func(termOldApp,termNewApp.getFunction().getName());
			
			if (termOldApp.getParameters().length != termNewApp.getParameters().length)
				throw new AssertionError("Error 1 in :desugar");
			
			for (int i = 0; i < termNewApp.getParameters().length; i++) {
				Term paramIOld = termOldApp.getParameters()[i];
				Term paramINew = termNewApp.getParameters()[i];
				if (!paramIOld.equals(paramINew)) {
					if (!calculateTerm(paramIOld).isIntegral())
						throw new AssertionError("Error 2 in :desugar");
					
					// Then paramINew has to be either old.0 or (to_real old)
					// Case 1: (to_real old), Case 2: old.0
					boolean correct = false;
					
					if (paramINew instanceof ApplicationTerm) {
						// Case 1 and parts of Case 2: (Just handling of the complete Case 1)								
						ApplicationTerm paramINewApp = convertApp(paramINew);
						
						if (pm_func_weak(paramINewApp,"to_real"))								
							if (paramIOld.equals(
									paramINewApp.getParameters()[0]))
								correct = true;
							else
								throw new AssertionError("Error 4 in :desugar");
					}
					
					// Case 2 and parts of Case 1: (Just handling of the complete Case 2)
					if (calculateTerm(paramINew).getSort() == mSkript.sort("Real")) {
						// Check for equalitiy, ? and ?.0 have to be equal, therefor .equals doesn't work
						SMTAffineTerm diffZero = calculateTerm(paramINew).add(
								calculateTerm(paramIOld).negate());
						if (diffZero.isConstant()
								&& diffZero.getConstant() == Rational.ZERO)
							correct = true;
					}
					
					if (!correct)
						throw new AssertionError("Error 5 in :desugar");							
				}
			}
		} else if (rewriteRule == ":divisible") {				
			// This rule is a combination of 3-4 sub-rules
								
			// Declaration of the variables which can be declared for all sub-rules + syntactical check 
			ApplicationTerm termOldApp = convertApp(termEqApp.getParameters()[0]);					
			checkNumber(termOldApp,1);
			Term termNew = termEqApp.getParameters()[1];
			
			Term termT = termOldApp.getParameters()[0];
			BigInteger bigIN = termOldApp.getFunction().getIndices()[0]; //bigInteger N
			
			pm_func(termOldApp,"divisible");
			
			if (!termNew.equals(mSkript.term("true")) //Old: termNew instanceof ApplicationTerm
					&& !termNew.equals(mSkript.term("false"))) {
				// Sub-rule 4
				
				ApplicationTerm termNewApp = convertApp(termNew);
				pm_func(termNewApp, "=");
				
				checkNumber(termNewApp,2);
				
				// = and * are commutative
				ApplicationTerm termNewAppProd;
				if (termNewApp.getParameters()[0].equals(termT))
					termNewAppProd = convertApp(termNewApp.getParameters()[1]);
				else if (termNewApp.getParameters()[1].equals(termT))
					termNewAppProd = convertApp(termNewApp.getParameters()[0]);
				else
					throw new AssertionError("Error 1 in divisible");
				
				ApplicationTerm termNewAppDiv = null; // Not nice: Use of null
				boolean found = false;
				
				checkNumber(termNewAppProd, 2);
				
				if (termNewAppProd.getParameters()[0] instanceof ConstantTerm)
					if (convertConst(termNewAppProd.getParameters()[0]).getValue().equals(bigIN)) {
						termNewAppDiv = convertApp(termNewAppProd.getParameters()[1]);
						found = true;
					}
				if (termNewAppProd.getParameters()[1] instanceof ConstantTerm)
					if (convertConst(termNewAppProd.getParameters()[1]).getValue().equals(bigIN)) {
						termNewAppDiv = convertApp(termNewAppProd.getParameters()[0]);
						found = true;
					}
				
				checkNumber(termNewAppDiv, 2);
				
				if (!found)
					throw new AssertionError("Error 2 in divisible");
				
				pm_func(termNewAppProd, "*");
				if (!pm_func_weak(termNewAppDiv, "div")
						&& !pm_func_weak(termNewAppDiv, "/"))
					throw new AssertionError("Error 3 in divisible");
				
				if (!termNewAppDiv.getParameters()[0].equals(termT))
					throw new AssertionError("Error 4 in divisible");
				
				if (!convertConst(termNewAppDiv.getParameters()[1]).getValue().equals(bigIN))
					throw new AssertionError("Error 5 in divisible");
			} else {		
				Rational constT = calculateTerm(convertConst_Neg(termT)).getConstant();
				Rational constN = Rational.valueOf(bigIN,BigInteger.ONE);
				
				if (constT.div(constN).isIntegral())
					if (!termNew.equals(mSkript.term("true")))
						throw new AssertionError("Error 6 in divisible");

				if (!constT.div(constN).isIntegral())
					if (!termNew.equals(mSkript.term("false")))
						throw new AssertionError("Error 7 in divisible");
						
				// No special treatment of the case n = 1, but it's still correct.
			}
		} else if (rewriteRule == ":div1") {									
			ApplicationTerm termOldApp = convertApp(termEqApp.getParameters()[0]);

			pm_func(termOldApp,"div");
			
			checkNumber(termOldApp, 2);
			
			SMTAffineTerm constant = calculateTerm(
					convertConst_Neg(termOldApp.getParameters()[1]));
			
			// Rule-Execution was wrong if c != 1
			if (!constant.isConstant())
				throw new AssertionError("Error 1 at " + rewriteRule);					
			if (!(constant.getConstant().equals(Rational.ONE)))
				throw new AssertionError("Error 2 at " + rewriteRule);
			
			if (termEqApp.getParameters()[1] != termOldApp.getParameters()[0])
				throw new AssertionError("Error 3 at " + rewriteRule);
			
		} else if (rewriteRule == ":div-1") {							
			ApplicationTerm termOldApp = convertApp(termEqApp.getParameters()[0]);

			pm_func(termOldApp,"div");
			
			checkNumber(termOldApp, 2);
								
			convertConst_Neg(termOldApp.getParameters()[1]);
			
			SMTAffineTerm constant = calculateTerm(termOldApp.getParameters()[1]);
			
			// Rule-Execution was wrong if c != 1
			if (!constant.negate().isConstant())
				throw new AssertionError("Error 1 at " + rewriteRule);					
			if (!(constant.negate().getConstant().equals(Rational.ONE)))
				throw new AssertionError("Error 2 at " + rewriteRule);
			
			if (!calculateTerm(termEqApp.getParameters()[1]).negate().equals(
					calculateTerm(termOldApp.getParameters()[0])))
				throw new AssertionError("Error 3 at " + rewriteRule);
		} else if (rewriteRule == ":divConst") {									
			ApplicationTerm termOldApp = convertApp(termEqApp.getParameters()[0]);

			pm_func(termOldApp,"div");
			
			checkNumber(termOldApp, 2);
			
			convertConst_Neg(termOldApp.getParameters()[0]);
			convertConst_Neg(termOldApp.getParameters()[1]);
			
			SMTAffineTerm c1 = calculateTerm(termOldApp.getParameters()[0]);
			SMTAffineTerm c2 = calculateTerm(termOldApp.getParameters()[1]);
			
			SMTAffineTerm d = calculateTerm(termEqApp.getParameters()[1]);
			
			if (!c1.isConstant())
				throw new AssertionError("Error 1 at " + rewriteRule);
			
			if (!c2.isConstant())
				throw new AssertionError("Error 2 at " + rewriteRule);					
			
			if (c2.getConstant().equals(Rational.ZERO))
				throw new AssertionError("Error 3 at " + rewriteRule);
			
			if (!c1.isIntegral() || !c2.isIntegral() || !d.isIntegral())
				throw new AssertionError("Error 4 at " + rewriteRule);
			
			if (c2.getConstant().isNegative())
				if (!d.getConstant().equals(c1.getConstant().div(c2.getConstant()).ceil()))
					throw new AssertionError("Error 5 at " + rewriteRule);
			
			if (!c2.getConstant().isNegative())
				if (!d.getConstant().equals(c1.getConstant().div(c2.getConstant()).floor()))
					throw new AssertionError("Error 6 at " + rewriteRule);
			
		} else if (rewriteRule == ":modulo1") {									
			ApplicationTerm termOldApp = convertApp(termEqApp.getParameters()[0]);

			pm_func(termOldApp,"mod");
			
			checkNumber(termOldApp, 2);
			
			//Check syntactical correctness
			if (!(termOldApp.getParameters()[0] instanceof ConstantTerm)
					&& !checkInt_weak(termOldApp.getParameters()[0]))
				throw new AssertionError("Error 1 at " + rewriteRule);
			
			convertConst(termOldApp.getParameters()[1]);
			convertConst(termEqApp.getParameters()[1]);
			
			SMTAffineTerm constant1 = calculateTerm(termOldApp.getParameters()[1]);
			SMTAffineTerm constant0 = calculateTerm(termEqApp.getParameters()[1]);						
			
			if (!(constant1.getConstant().equals(Rational.ONE)))
				throw new AssertionError("Error 2 at " + rewriteRule);
			
			if (!(constant0.getConstant().equals(Rational.ZERO)))
				throw new AssertionError("Error 3 at " + rewriteRule);
			
		} else if (rewriteRule == ":modulo-1") {									
			ApplicationTerm termOldApp = convertApp(termEqApp.getParameters()[0]);

			pm_func(termOldApp,"mod");
			
			checkNumber(termOldApp, 2);
			
			//Check syntactical correctness
			if (!(termOldApp.getParameters()[0] instanceof ConstantTerm)
					&& !checkInt_weak(termOldApp.getParameters()[0]))
				throw new AssertionError("Error 1 at " + rewriteRule);
			
			convertConst_Neg(termOldApp.getParameters()[1]);
			convertConst(termEqApp.getParameters()[1]);
			
			SMTAffineTerm constantm1 = calculateTerm(termOldApp.getParameters()[1]);
			SMTAffineTerm constant0 = calculateTerm(termEqApp.getParameters()[1]);						
			
			if (!(constantm1.getConstant().negate().equals(Rational.ONE)))
				throw new AssertionError("Error 2 at " + rewriteRule);
			
			if (!(constant0.getConstant().equals(Rational.ZERO)))
				throw new AssertionError("Error 3 at " + rewriteRule);
			
		} else if (rewriteRule == ":moduloConst") {
			ApplicationTerm termOldApp = convertApp(termEqApp.getParameters()[0]);

			pm_func(termOldApp,"mod");
			
			checkNumber(termOldApp,2);
			
			//Check syntactical correctness
			if (!(termOldApp.getParameters()[0] instanceof ConstantTerm)
					&& !checkInt_weak(termOldApp.getParameters()[0]))
				throw new AssertionError("Error 1a at " + rewriteRule);
			if (!(termOldApp.getParameters()[1] instanceof ConstantTerm)
					&& !checkInt_weak(termOldApp.getParameters()[1]))
				throw new AssertionError("Error 1b at " + rewriteRule);
			if (!(termEqApp.getParameters()[1] instanceof ConstantTerm)
					&& !checkInt_weak(termEqApp.getParameters()[1]))
				throw new AssertionError("Error 1c at " + rewriteRule);
			
			SMTAffineTerm c1 = calculateTerm(termOldApp.getParameters()[0]);
			SMTAffineTerm c2 = calculateTerm(termOldApp.getParameters()[1]);
			
			SMTAffineTerm d = calculateTerm(termEqApp.getParameters()[1]);
			
			if (c2.getConstant().equals(Rational.ZERO))
				throw new AssertionError("Error 2 at " + rewriteRule);
			
			if (!c1.isIntegral() || !c2.isIntegral() || !d.isIntegral())
				throw new AssertionError("Error 3 at " + rewriteRule);
			
			if (c2.getConstant().isNegative()) {
				// d = c1 + c2 * ceil(c1/c2)
				if (!d.equals(c1.add(
						c2.mul(c1.div(c2.getConstant()).getConstant().ceil()).negate())))
					throw new AssertionError("Error 4 at " + rewriteRule);
			} else {
				if (!d.equals(c1.add(
						c2.mul(c1.div(c2.getConstant()).getConstant().floor()).negate())))
					throw new AssertionError("Error 5 at " + rewriteRule);
			}
		} else if (rewriteRule == ":modulo") {		
			
			ApplicationTerm termOldMod = convertApp(termEqApp.getParameters()[0]);
			ApplicationTerm termNewSum = convertApp(termEqApp.getParameters()[1]);

			checkNumber(termOldMod, 2);
			checkNumber(termNewSum, 2);
			
			Term termOldX = termOldMod.getParameters()[0];
			Term termOldY = termOldMod.getParameters()[1];
			
			ApplicationTerm termNewProd;					
			Term termNewNotProd;
			if (termNewSum.getParameters()[0] instanceof ApplicationTerm) {
				if (pm_func_weak(termNewSum.getParameters()[0],"*")) {
					termNewProd = convertApp(termNewSum.getParameters()[0]);
					termNewNotProd = termNewSum.getParameters()[1];
				} else {
					termNewProd = convertApp(termNewSum.getParameters()[1]);
					termNewNotProd = termNewSum.getParameters()[0];
				}
			} else {
				termNewProd = convertApp(termNewSum.getParameters()[1]);
				termNewNotProd = termNewSum.getParameters()[0];
			}
			
			checkNumber(termNewProd, 2);
			
			ApplicationTerm termNewDiv;
			Term termNewNotDiv;
			if (termNewProd.getParameters()[0] instanceof ApplicationTerm) {
				if (pm_func_weak(termNewProd.getParameters()[0],"/")
						|| pm_func_weak(termNewProd.getParameters()[0],"div")) {
					termNewDiv = convertApp(termNewProd.getParameters()[0]);
					termNewNotDiv = termNewProd.getParameters()[1];
				} else {
					termNewDiv = convertApp(termNewProd.getParameters()[1]);
					termNewNotDiv = termNewProd.getParameters()[0];
				}
			} else {
				termNewDiv = convertApp(termNewProd.getParameters()[1]);
				termNewNotDiv = termNewProd.getParameters()[0];
			}
			
			checkNumber(termNewDiv, 2);
			
			//ApplicationTerm termNewDiv = convertApp(termNewProd.getParameters()[1]);
			
			pm_func(termOldMod,"mod");
			pm_func(termNewSum,"+");
			pm_func(termNewProd,"*");
			if (!pm_func_weak(termNewDiv,"div")
					&& !pm_func_weak(termNewDiv,"/"))
				throw new AssertionError("Error 1 at " + rewriteRule);
			
			if (termNewNotProd != termOldX
					|| !calculateTerm(termNewNotDiv).equals(
							calculateTerm(termOldY).negate())
					|| termNewDiv.getParameters()[0] != termOldX
					|| termNewDiv.getParameters()[1] != termOldY)
				throw new AssertionError("Error 2 at " + rewriteRule);
			
		} else if (rewriteRule == ":toInt") {					
			ApplicationTerm termOldApp = convertApp(termEqApp.getParameters()[0]);
			
			pm_func(termOldApp,"to_int");
			
			// r and v as in the documentation proof.pdf
			Term termV = convertConst_Neg(termEqApp.getParameters()[1]);
			Term termR = termOldApp.getParameters()[0];
			// r can be a positive/negative fraction
			// Case A: Positive Integer, Case B: Negative Integer
			// Case C: Positive Fraction, Case D: Negative Fraction
			
			if (termR instanceof ApplicationTerm) {
				// Case B, C, D:
				ApplicationTerm termRApp = convertApp(termR);
				ApplicationTerm termRInnerApp;
				if (pm_func_weak(termRApp,"-") 
						&& termRApp.getParameters()[0] instanceof ApplicationTerm) {
					// Case D:
					termRInnerApp = convertApp(termRApp.getParameters()[0]);
					pm_func(termRInnerApp,"/");
					checkNumber(termRInnerApp,2);
					
					convertConst_Neg(termRInnerApp.getParameters()[0]); // Presumably the neg isn't needed
					convertConst_Neg(termRInnerApp.getParameters()[1]); // Presumably the neg isn't needed
				} else if (pm_func_weak(termRApp,"/")) {
					// Case C:
					pm_func(termRApp,"/");
					checkNumber(termRApp,2);
					
					convertConst_Neg(termRApp.getParameters()[0]); // Presumably the neg isn't needed
					convertConst_Neg(termRApp.getParameters()[1]); // Presumably the neg isn't needed
				} else {
					// Case B:
					pm_func(termRApp,"-");
					
					convertConst(termRApp.getParameters()[0]);
				}	
			} else {
				// Case A:
				convertConst(termR);
			}
			
			if (!calculateTerm(termR).getConstant().floor().equals(
					calculateTerm(termV).getConstant())) 	
				throw new AssertionError("Error 2 at " + rewriteRule);
			
			/* Not nice: Not checked, if v is an integer and
			 * r a real, but it is still correct.
			 */
		} else if (rewriteRule == ":toReal") {
			ApplicationTerm termOldApp = convertApp(termEqApp.getParameters()[0]);
			
			pm_func(termOldApp,"to_real");
								
			Term termOldC = convertConst_Neg(termOldApp.getParameters()[0]);
			Term termNewC = convertConst_Neg(termEqApp.getParameters()[1]);
			
			if (!calculateTerm(termOldC).getConstant().equals(
					calculateTerm(termNewC).getConstant()))						
				throw new AssertionError("Error 2 at " + rewriteRule);
			
			/* Not nice: Not checked, if cOld is an integer and
			 * cNew a real, but it is still correct.
			 */
		} else if (rewriteRule == ":storeOverStore") {
			System.out.println("\n \n \n Now finally tested: " + rewriteRule);	 //TODO					
			
			checkNumber(termEqApp.getParameters(),2);
			ApplicationTerm termOldApp = convertApp(termEqApp.getParameters()[0]);
			ApplicationTerm termNewApp = convertApp(termEqApp.getParameters()[1]);
			ApplicationTerm termOldAppInnerApp = convertApp(termOldApp.getParameters()[0]);
			
			checkNumber(termOldApp.getParameters(), 3);
			checkNumber(termOldAppInnerApp.getParameters(), 3);
			checkNumber(termNewApp.getParameters(), 3);
			
			pm_func(termOldApp,"store");
			pm_func(termOldAppInnerApp,"store");
			pm_func(termNewApp,"store");
			
			if (termOldApp.getParameters()[1] != termOldAppInnerApp.getParameters()[1]
					|| termOldApp.getParameters()[1] != termNewApp.getParameters()[1])						
				throw new AssertionError("Error 1 at " + rewriteRule);
			
			if (termOldApp.getParameters()[2]
					!= termNewApp.getParameters()[2])						
				throw new AssertionError("Error 2 at " + rewriteRule);
			
			if (termOldAppInnerApp.getParameters()[0]
					!= termNewApp.getParameters()[0])						
				throw new AssertionError("Error 3 at " + rewriteRule);
			
			/* Not nice: Not checked, if i is an integer, but
			 * it is still correct.
			 */
		} else if (rewriteRule == ":selectOverStore") {
			System.out.println("\n \n \n Now finally tested: " + rewriteRule);	 //TODO					
			
			checkNumber(termEqApp.getParameters(),2);
			ApplicationTerm termOldApp = convertApp(termEqApp.getParameters()[0]);
			Term termNew = termEqApp.getParameters()[1];
			ApplicationTerm termOldAppInnerApp = convertApp(termOldApp.getParameters()[0]);
			
			checkNumber(termOldApp,2);
			checkNumber(termOldAppInnerApp,3);
			
			pm_func(termOldApp,"select");
			pm_func(termOldAppInnerApp,"store");
			
			if (termOldApp.getParameters()[1] == termOldAppInnerApp.getParameters()[1]) {
				if (termOldAppInnerApp.getParameters()[2] != termNew)						
					throw new AssertionError("Error 2 at " + rewriteRule);						
			} else {
				ApplicationTerm termNewApp = convertApp(termNew);
				checkNumber(termNewApp.getParameters(),2);
				pm_func(termNewApp,"select");
				
				Term c1 = convertConst_Neg(termOldAppInnerApp.getParameters()[1]);
				Term c2 = convertConst_Neg(termOldApp.getParameters()[1]);
				
				if (c1 == c2)
					throw new AssertionError("Error 3 at " + rewriteRule);
				
				if (c2 != termNewApp.getParameters()[1])
					throw new AssertionError("Error 4 at " + rewriteRule);
			}
			/* Not nice: Not checked, if i is an integer, but
			 * it is still correct.
			 */
		} else if (rewriteRule == ":storeRewrite") {
			System.out.println("\n \n \n Now finally tested: " + rewriteRule);	 //TODO					
			
			// checkNumber(termEqApp.getParameters(),2); already checked
			ApplicationTerm termOldApp = convertApp(termEqApp.getParameters()[0]);
			ApplicationTerm termNewApp = convertApp(termEqApp.getParameters()[1]);
			ApplicationTerm termNewAppInnerApp = convertApp(termNewApp.getParameters()[0]);
			ApplicationTerm termOldAppInnerApp = null;

			checkNumber(termNewApp.getParameters(),2);
			checkNumber(termNewAppInnerApp.getParameters(),2);
			checkNumber(termOldApp.getParameters(), 2);
			
			Term termA = termNewAppInnerApp.getParameters()[0];
			Term termI = termNewAppInnerApp.getParameters()[1];					
			Term termV = termNewApp.getParameters()[1];
			
			if (termOldApp.getParameters()[0] == termA)
				termOldAppInnerApp = convertApp(termOldApp.getParameters()[1]);
			else if (termOldApp.getParameters()[1] == termA)
				termOldAppInnerApp = convertApp(termOldApp.getParameters()[0]);
			else
				throw new AssertionError("Error 1 in " + rewriteRule);
								
			checkNumber(termOldAppInnerApp.getParameters(),3);					
			
			pm_func(termOldApp,"=");
			pm_func(termOldAppInnerApp,"store");
			pm_func(termNewApp,"=");
			pm_func(termNewAppInnerApp,"select");
			
			
			if (termOldAppInnerApp.getParameters()[0] != termA
					|| termOldAppInnerApp.getParameters()[1] != termI
					|| termOldAppInnerApp.getParameters()[2] != termV)
				throw new AssertionError("Error 2 at " + rewriteRule);
			
			/* Not nice: Not checked, if i is an integer, but
			 * it is still correct.
			 */
		} else if (rewriteRule == ":expand") {
			Term termOld = termEqApp.getParameters()[0];
			Term termNew = termEqApp.getParameters()[1];
			
			if (!calculateTerm(termOld).equals(
					calculateTerm(termNew)))
				throw new AssertionError("Error in " + rewriteRule);
		} else if (rewriteRule == ":flatten") {
			// TODO: Testing
			/* Assumption: All nested disjunctions are put into one, i.e.
			 * no new disjunct is itself a disjunction
			 */					
			
			ApplicationTerm termOldApp = convertApp(termEqApp.getParameters()[0]);
			ApplicationTerm termNewApp = convertApp(termEqApp.getParameters()[1]);
			
			pm_func(termOldApp, "or");					
			pm_func(termNewApp, "or");
			
			HashSet<Term> oldDisjuncts = new HashSet<Term>();
			HashSet<Term> newDisjuncts = new HashSet<Term>();
			ArrayList<Term> disjuncts = new ArrayList<Term>();
			
			disjuncts.addAll(Arrays.asList(termOldApp.getParameters()));
			
			while (disjuncts.size() > 0) {
				Term currentDisjunct = disjuncts.remove(disjuncts.size() - 1);
				
				boolean currentIsDisjunction = false;
				
				if (currentDisjunct instanceof ApplicationTerm)
					currentIsDisjunction = pm_func_weak(currentDisjunct, "or");
				
				if (currentIsDisjunction) {
					ApplicationTerm currentDisjunctApp = convertApp(currentDisjunct);
					disjuncts.addAll(Arrays.asList(currentDisjunctApp.getParameters()));
				} else {
					oldDisjuncts.add(currentDisjunct);
				}								
			}		
			
			newDisjuncts.addAll(Arrays.asList(termNewApp.getParameters()));
			
			if (!oldDisjuncts.equals(newDisjuncts))
				throw new AssertionError("Error in the rule " + rewriteRule + "!\n The term was " + rewriteApp.toStringDirect());					
		
		} else {
			System.out.println("Can't handle the following rule " + termAppInnerAnn.getAnnotations()[0].getKey() + ", therefore...");
			System.out.println("...believed as alright to be rewritten: " + rewriteApp.getParameters()[0].toStringDirect() + " .");
		}				
	
		// The second part, cut the @rewrite and the annotation out, both aren't needed for the @eq-function.
		// stackPush(innerAnnTerm.getSubterm(), term);
	}
	
	public void walkIntern(ApplicationTerm internApp) {
		// Step 1: The syntactical check				
		
		ApplicationTerm termEqApp = convertApp(internApp.getParameters()[0]);
		
		/* The result is simply the first argument.  Compute it first 
		 * and check later.
		 */
		stackPush(termEqApp, internApp);
		
		
		pm_func(termEqApp,"=");
		
		// Step 1,5: Maybe the internal rewrite is just an addition of :quoted
		if (convertApp_hard(termEqApp.getParameters()[0])
				== convertApp_hard(termEqApp.getParameters()[1])) {
			return;
		}
		// Not nice: Not checked if the annotation really is quoted, but otherwise
		// it's still correct.
		
		/* Step 1,75: Maybe the first term is a negation of a Term t and 
		 * the second is the negation of (! t :quoted) 
		 */
		
		if (termEqApp.getParameters()[0] instanceof ApplicationTerm
				&& termEqApp.getParameters()[1] instanceof ApplicationTerm) {
			ApplicationTerm termLeftApp = convertApp(termEqApp.getParameters()[0]); // Term on the left side of the rewrite-"="
			ApplicationTerm termRightApp = convertApp(termEqApp.getParameters()[1]);
			
			if (pm_func_weak(termLeftApp,"not") 
					&& pm_func_weak(termRightApp,"not"))
				if (termRightApp.getParameters()[0] instanceof AnnotatedTerm) {
					AnnotatedTerm termRightAppInnerAnn = convertAnn(termRightApp.getParameters()[0]);
					if (termLeftApp.getParameters()[0].equals(
							termRightAppInnerAnn.getSubterm())) {
						return;
					}
				}
		}
		
		// Step 2: Find out if one is negated
		boolean firstNeg = false;
		boolean secondNeg = false;
		
		if (termEqApp.getParameters()[0] instanceof ApplicationTerm)
			if (pm_func_weak(termEqApp.getParameters()[0], "not"))
				firstNeg = true;
		
		if (termEqApp.getParameters()[1] instanceof ApplicationTerm)
			if (pm_func_weak(termEqApp.getParameters()[1], "not"))
				secondNeg = true;
		
		// Step 3: Get the (in)equalities, that have to be compared.
		ApplicationTerm termOldRel; // Rel stands for relation, which is used as a generic term for in-/equality
		ApplicationTerm termNewRel;
		
		// The outmost annotation is not important for the correctness-check				
		if (firstNeg)
			termOldRel = convertApp_hard(
					((ApplicationTerm) termEqApp.getParameters()[0]).getParameters()[0]);
		else
			termOldRel = convertApp_hard(termEqApp.getParameters()[0]);
		
		if (secondNeg)
			termNewRel = convertApp_hard(
					((ApplicationTerm) termEqApp.getParameters()[1]).getParameters()[0]);
		else
			termNewRel = convertApp_hard(termEqApp.getParameters()[1]);				
		
		checkNumber(termOldRel, 2);
		checkNumber(termNewRel, 2);
		
		/* Step 4: Get the terms which have to be compared
		 * For this, the (in)equality-term has to be transformed,
		 * depending on the relation-symbol
		 */
						
		if (pm_func_weak(termOldRel,"=")) {
			// Case 4.1: It's an equality
			if ((firstNeg && !secondNeg)		||		(!firstNeg && secondNeg))
				throw new AssertionError("Error 4.1.1");
			
			// term_compare = Left Side - Right Side
			SMTAffineTerm termOldCompAff =
					calculateTerm(termOldRel.getParameters()[0]).add(
							calculateTerm(termOldRel.getParameters()[1]).negate());

			SMTAffineTerm termNewCompAff =
					calculateTerm(termNewRel.getParameters()[0]).add(
							calculateTerm(termNewRel.getParameters()[1]).negate());
			
			// Precheck for better runtime - Warning: Code duplicates start here - a random number: 589354
			if (termOldCompAff.equals(termNewCompAff)) {
				return;
			}
			
			// Check for a multiplication with a rational
			Rational constOld = termOldCompAff.getConstant();
			Rational constNew = termNewCompAff.getConstant();
			
			if (constOld.equals(Rational.ZERO) && constNew.equals(Rational.ZERO)) {
				// Find the multiplication in a cofactor
				Rational oldGcd = termOldCompAff.getGcd();
				Rational newGcd = termNewCompAff.getGcd();
										
				if (termOldCompAff.mul(newGcd).equals(termNewCompAff)
						|| termOldCompAff.mul(newGcd).equals(termNewCompAff.negate())
						|| termNewCompAff.mul(oldGcd).equals(termOldCompAff)
						|| termNewCompAff.mul(oldGcd).equals(termOldCompAff.negate())) // Note: == doesn't work
				{
					return;
				}
				
				if (termOldCompAff.equals(termNewCompAff.negate()))	{
					return;
				}
				reportError("Sadly1, I couldn't find a factorial constant in the internal rewrite: "
						+ internApp.getParameters()[0].toStringDirect() + " .");
				return;
			}
								
			if (constOld.equals(Rational.ZERO) || constNew.equals(Rational.ZERO))
				throw new AssertionError("Error 4.1.2");
			
			// Calculate the factors
			Rational constGcd = constOld.gcd(constNew); // greatest common divisor
			Rational constLcm = constOld.mul(constNew).div(constGcd); // least common multiple
			Rational constOldFactor = constLcm.div(constOld);
			Rational constNewFactor = constLcm.div(constNew);
			
			termOldCompAff = termOldCompAff.mul(constOldFactor);
			termNewCompAff = termNewCompAff.mul(constNewFactor);
			
			if (termOldCompAff.equals(termNewCompAff)) {
				return;
			}
			
			System.out.println("Sadly1, I couldn't understand the internal rewrite: "
					+ internApp.getParameters()[0].toStringDirect() + " .");
			// Warning: Code duplicates end here - a random number: 589354
		} else {
			// Case 4.2: Then both have to be brought to either ... < 0 or ... <= 0
			ApplicationTerm termOldComp = uniformizeInEquality(convertApp_hard(termEqApp.getParameters()[0]));
			ApplicationTerm termNewComp = uniformizeInEquality(convertApp_hard(termEqApp.getParameters()[1]));
			
			if (termOldComp.getFunction().getName() != termNewComp.getFunction().getName())
				throw new AssertionError("Error 4.2.2");
			
			if (!pm_func_weak(termOldComp,"<=") && !pm_func_weak(termOldComp,"<"))
				throw new AssertionError("Error 4.2.3");
								
			if (!pm_func_weak(termNewComp,"<=") && !pm_func_weak(termNewComp,"<"))
				throw new AssertionError("Error 4.2.4");
			
			// Just the left side of the inequality
			SMTAffineTerm termOldCompAff = calculateTerm(termOldComp.getParameters()[0]);
			SMTAffineTerm termNewCompAff = calculateTerm(termNewComp.getParameters()[0]);
			
			// Precheck for better runtime - Warning: Code duplicates start here - a random number: 589354
			if (termOldCompAff.equals(termNewCompAff)) {
				return;
			}
			
			// Check for a multiplication with a rational
			Rational constOld = termOldCompAff.getConstant();
			Rational constNew = termNewCompAff.getConstant();
			
			if (constOld.equals(Rational.ZERO) && constNew.equals(Rational.ZERO)) {
				// Find the multiplication in a cofactor
				Rational oldGcd = termOldCompAff.getGcd();
				Rational newGcd = termNewCompAff.getGcd();
										
				if (termOldCompAff.mul(newGcd).equals(termNewCompAff)
						|| termOldCompAff.mul(newGcd).equals(termNewCompAff.negate())
						|| termNewCompAff.mul(oldGcd).equals(termOldCompAff)
						|| termNewCompAff.mul(oldGcd).equals(termOldCompAff.negate())) // Note: == doesn't work
				{
					return;
				}
				
				reportError("Sadly2, I couldn't find a factorial constant in the internal rewrite: "
						+ internApp.getParameters()[0].toStringDirect() + " .");
				return;
			}
			
			if (constOld.equals(Rational.ZERO) || constNew.equals(Rational.ZERO))
				throw new AssertionError("Error 4.2.5");
			
			// Calculate the factors
			Rational constGcd = constOld.gcd(constNew); // greatest common divisor
			Rational constLcm = constOld.mul(constNew).div(constGcd); // least common multiple
			Rational constOldFactor = constLcm.div(constOld);
			Rational constNewFactor = constLcm.div(constNew);
			
			termOldCompAff = termOldCompAff.mul(constOldFactor);
			termNewCompAff = termNewCompAff.mul(constNewFactor);
			
			if (termOldCompAff.equals(termNewCompAff)) {
				return;
			}
			
			reportError("Sadly2, I couldn't understand the internal rewrite: "
					+ internApp.getParameters()[0].toStringDirect() + " .");
		}
		
		reportError("Sadly, I had to believe the following internal rewrite: "
				+ internApp.getParameters()[0].toStringDirect() + " .");
		return;
	}	
	
	/**
	 * Convert a clause term into an Array of terms, one entry for each 
	 * disjunct.  This also handles singleton and empty clause correctly.
	 * @param clauseTerm  The term representing a clause.
	 * @return The disjuncts of the clause.
	 */
	private Term[] termToClause(Term clauseTerm) {
		assert clauseTerm != null && clauseTerm.getSort().getName() == "Bool";
		if (clauseTerm instanceof ApplicationTerm) {
			ApplicationTerm appTerm = (ApplicationTerm) clauseTerm;
			FunctionSymbol func = appTerm.getFunction();
			if (func.isIntern()) {
				if (func.getName().equals("false"))
					return new Term[0];
				if (func.getName().equals("or"))
					return appTerm.getParameters();
			}
		}
		/* in all other cases, this is a singleton clause. */
		return new Term[] { clauseTerm };
	}

	/**
	 * Convert a collection of terms into a clause term. This also handles 
	 * singleton and empty clause correctly.
	 * @param disjuncts the disjuncts of the clause.
	 * @return a term representing the clause.
	 */
	private Term clauseToTerm(Collection<Term> disjuncts) {
		if (disjuncts.size() <= 1) {
			if (disjuncts.size() == 0)
				return mSkript.term("false");
			else
				return disjuncts.iterator().next();
		} else {
			Term[] args = disjuncts.toArray(new Term[disjuncts.size()]);
			return mSkript.term("or", args);
		}
	}

	/**
	 * Handle the resolution rule.  The stack should contain the converted
	 * input clauses.
	 * @param resApp The <code>{@literal @}res</code> application from the 
	 *        original proof.
	 */
	public void walkResolution(ApplicationTerm resApp) {
		Term[] termArgs = resApp.getParameters();		

		/* Get the pivot literals (pivots[0] is always null)
		 * and retrieve the calculations for the proofs from the stack.
		 */
		Term[] pivots = new Term[termArgs.length];
		Term[] clauseTerms = new Term[termArgs.length];
		for (int i = termArgs.length - 1; i >= 1; i--) {
			AnnotatedTerm pivotPlusProof = (AnnotatedTerm) termArgs[i];
				
			/* Check if it is a pivot-annotation */
			if (pivotPlusProof.getAnnotations().length != 1
					|| pivotPlusProof.getAnnotations()[0].getKey() != ":pivot") {
				throw new IllegalArgumentException(
						"Annotation :pivot expected");
			}						
										
			/* Just take the first annotation, because 
			 * it should have exactly one - otherwise 
			 * the proof-checker throws an error 
			 */
			pivots[i] = (Term) pivotPlusProof.getAnnotations()[0].getValue();
			clauseTerms[i] = stackPopCheck(pivotPlusProof.getSubterm());
		}
		// The 0th argument is the main clause an has no pivot.
		clauseTerms[0] = stackPopCheck(termArgs[0]);
		
		/* allDisjuncts is the currently computed resolution result.
		 */
		HashSet<Term> allDisjuncts = new HashSet<Term>();

		/* Now get the disjuncts of the first argument. */
		allDisjuncts.addAll(Arrays.asList(termToClause(clauseTerms[0])));
		
		/* Resolve the other clauses */
		for (int i = 1; i < termArgs.length; i++) {
			/* Remove the negated pivot from allDisjuncts */
			if (!allDisjuncts.remove(negate(pivots[i]))) {
				reportError("Could not find negated pivot in main clause");
			}

			/* For each clause check for the pivot and add all other
			 * literals.
			 */
			Term[] clause = termToClause(clauseTerms[i]);
			boolean pivotFound = false;
			for (Term t : clause) {
				if (t == pivots[i]) {
					pivotFound = true;
				} else {
					allDisjuncts.add(t);
				}
			}
			
			if (!pivotFound) {
				reportError("Could not find pivot in secondary clause");
			}					
		}

		stackPush(clauseToTerm(allDisjuncts), resApp);
	}			
			
	public void walkEquality(ApplicationTerm eqApp) {
		Term[] eqParams = eqApp.getParameters();
		
		/* Expected: The first argument is a boolean formula each other 
		 * argument a binary equality.
		 *
		 * Each not-first argument describes a rewrite of a (sub)term of the 
		 * first term. Important is the order, e.g. the rewrite of the second 
		 * argument has to be executed before the rewrite of the third 
		 * argument! 
		 */

		/* Get the rewrite equalities from the stack. These should be
		 * proof nodes that come from an @intern or @rewrite rule.
		 */
		Term[] rewrites = new Term[eqParams.length-1];
		for (int i = eqParams.length - 1; i >= 1; i--) {
			rewrites[i - 1] = stackPopCheck(eqParams[i]);
		}
		
		/* the first argument is the term on which rewrites are applied */
		Term termEdit;
		termEdit = stackPopCheck(eqParams[0]);
		
		// Rewriting the term
		for (Term rewrite : rewrites) {
			pm_func(rewrite, "=");
			Term[] rewriteSides = ((ApplicationTerm) rewrite).getParameters();
			if (rewriteSides.length != 2)
				reportError("Rewrite equality with more than two sides?");

			termEdit = rewriteTerm(termEdit, rewriteSides[0], rewriteSides[1]);
		}
		
		stackPush(termEdit, eqApp);			
	}
	
	public void walkClause(ApplicationTerm clauseApp) {
		/* Check if the parameters of clause are two disjunctions (which they should be) */
		Term clauseTerm1 = stackPopCheck(clauseApp.getParameters()[0]);
		Term clauseTerm2 = clauseApp.getParameters()[1];
		
		// The disjuncts of each parameter
		HashSet<Term> param1Disjuncts = new HashSet<Term>(
				Arrays.asList(termToClause(clauseTerm1)));
		HashSet<Term> param2Disjuncts = new HashSet<Term>(
				Arrays.asList(termToClause(clauseTerm2)));
		
		/* Check if the clause operation was correct. Each later disjunct has to be in 
		 * the first disjunction and reverse.
		 */
		
		if (!param1Disjuncts.equals(param2Disjuncts)) {				
			reportError("The clause-operation didn't permute correctly!");
		}
										
		stackPush(clauseTerm2, clauseApp);
	}		
		
			
	public void walkSplit(ApplicationTerm splitApp) {
		// term is just the first term
		
		// The first term casted to an ApplicationTerm
		AnnotatedTerm termAppSplitInnerAnn = 
				(AnnotatedTerm) splitApp.getParameters()[0];
		ApplicationTerm termSplitReturnApp = 
				(ApplicationTerm) splitApp.getParameters()[1];
		ApplicationTerm termOldCalcApp = (ApplicationTerm) 
				stackPopCheck(termAppSplitInnerAnn.getSubterm());
		Term termSplitReturnInner = termSplitReturnApp.getParameters()[0];
								
		String splitRule = termAppSplitInnerAnn.getAnnotations()[0].getKey();
					
		if (mDebug.contains("currently"))
			System.out.println("Split-Rule: " + splitRule);
		if (mDebug.contains("hardTerm"))
			System.out.println("Term: " + splitApp.toStringDirect());
		
		if (splitRule == ":notOr") {
			if (mDebug.contains("split_notOr")) {
				System.out.println("Meldung: Wandle um (berechnet):");
				System.out.println(termOldCalcApp.toStringDirect());
				System.out.println("in");
				System.out.println(splitApp.getParameters()[1].toStringDirect());
			}
			
			pm_func(termSplitReturnApp,"not");
			if (!pm_func_weak(termOldCalcApp, "not"))
				System.out.println("Breakpoint");
			pm_func(termOldCalcApp, "not");
			ApplicationTerm termOldCalcAppInnerApp = convertApp(termOldCalcApp.getParameters()[0]);
			pm_func(termOldCalcAppInnerApp, "or");
			
			for (Term disjunct : termOldCalcAppInnerApp.getParameters()) {
				if (disjunct == termSplitReturnInner) {
					stackPush(splitApp.getParameters()[1], splitApp);
					return;
				}					
			}
			
			throw new AssertionError("Error in \"split\"");
				
		} else if (splitRule == ":=+1" || splitRule == ":=+2") {
			int rr = 2;
			if (splitRule == ":=+1")
				rr = 1;
			
			// checkNumber(termApp.getParameters(),2); already checked
			
			ApplicationTerm termOldApp = termOldCalcApp;
			ApplicationTerm termNewApp = termSplitReturnApp;
			
			checkNumber(termOldApp,2);
			checkNumber(termNewApp,2);
			
			//The term (F1 or F2) which is negated in new term
			Term termNewNeg = termOldApp.getParameters()[2 - rr];
			Term termNewPos = termOldApp.getParameters()[rr - 1];
			
			pm_func(termOldApp,"=");
			pm_func(termNewApp,"or");
			
			if (termNewApp.getParameters()[rr - 1] != mSkript.term("not",termNewNeg)
					&& termNewApp.getParameters()[2 - rr] != mSkript.term("not",termNewNeg))
				throw new AssertionError("Error 1 at " + splitRule);
			
			if (termNewApp.getParameters()[rr - 1] != termNewPos
					&& termNewApp.getParameters()[2 - rr] != termNewPos)
				throw new AssertionError("Error 2 at " + splitRule);
			
			/* Not nice: Not checked, if the F are boolean, which
			 * they should.
			 */
			
			stackPush(splitApp.getParameters()[1], splitApp);
			return;
		} else if (splitRule == ":=-1" || splitRule == ":=-2") {
			checkNumber(splitApp,2);
			
			ApplicationTerm termOldApp = termOldCalcApp;
			ApplicationTerm termNewApp = termSplitReturnApp;
			
			checkNumber(termOldApp,1);
			checkNumber(termNewApp,2);
			
			ApplicationTerm termOldAppInnerApp = convertApp(termOldApp.getParameters()[0]);
			
			checkNumber(termOldAppInnerApp,2);
			
			Term termF1 = termOldAppInnerApp.getParameters()[0];
			Term termF2 = termOldAppInnerApp.getParameters()[1];
			
			pm_func(termOldApp,"not");
			pm_func(termOldAppInnerApp,"=");
			pm_func(termNewApp,"or");
			
			if (splitRule == ":=-1") {
				// or is commutative
				if (termNewApp.getParameters()[0] != termF1
					&& termNewApp.getParameters()[1] != termF1)
					throw new AssertionError("Error 1 at " + splitRule);
			
				if (termNewApp.getParameters()[0] != termF2
					&& termNewApp.getParameters()[1] != termF2)
					throw new AssertionError("Error 2 at " + splitRule);
			} else {
				ApplicationTerm termNewAppInner1App = convertApp(termNewApp.getParameters()[0]);
				ApplicationTerm termNewAppInner2App = convertApp(termNewApp.getParameters()[1]);
			
				pm_func(termNewAppInner1App,"not");
				pm_func(termNewAppInner2App,"not");
									
				// or is commutative						
				if (termNewAppInner1App.getParameters()[0] != termF1
					&& termNewAppInner2App.getParameters()[0] != termF1)
					throw new AssertionError("Error 3 at " + splitRule);
				
				if (termNewAppInner1App.getParameters()[0] != termF2
					&& termNewAppInner2App.getParameters()[0] != termF2)
					throw new AssertionError("Error 4 at " + splitRule);
			}	
			
			/* Not nice: Not checked, if the F are boolean, which
			 * they should.
			 */
				
			stackPush(splitApp.getParameters()[1], splitApp);
			return;
		} else if (splitRule == ":ite+1" || splitRule == ":ite+2") {
			checkNumber(splitApp,2);
			
			ApplicationTerm termOldApp = termOldCalcApp;
			ApplicationTerm termNewApp = termSplitReturnApp;
			
			checkNumber(termOldApp,3);				
			checkNumber(termNewApp,2);
			
			Term termF1 = termOldApp.getParameters()[0];
			Term termF2 = termOldApp.getParameters()[1];
			Term termF3 = termOldApp.getParameters()[2];
			
			pm_func(termOldApp,"ite");
			pm_func(termNewApp,"or");
			
			if (splitRule == ":ite+2") {
				// or is commutative
				if (termNewApp.getParameters()[0] != termF1
						&& termNewApp.getParameters()[1] != termF1)
						throw new AssertionError("Error 1a at " + splitRule);
				
				if (termNewApp.getParameters()[0] != termF3
						&& termNewApp.getParameters()[1] != termF3)
						throw new AssertionError("Error 1b at " + splitRule);
			} else {					
				if (termNewApp.getParameters()[0] != termF2
					&& termNewApp.getParameters()[1] != termF2)
					throw new AssertionError("Error 2a at " + splitRule);
				
				if (termNewApp.getParameters()[0] != mSkript.term("not", termF1)
					&& termNewApp.getParameters()[1] != mSkript.term("not", termF1))
					throw new AssertionError("Error 2b at " + splitRule);
			}
					
						
			
			/* Not nice: Not checked, if the F are boolean, which
			 * they should.
			 */
			
			stackPush(splitApp.getParameters()[1], splitApp);
			return;
		
		} else if (splitRule == ":ite-1" || splitRule == ":ite-2") {
			checkNumber(splitApp,2);
			
			ApplicationTerm termOldApp = termOldCalcApp;
			ApplicationTerm termNewApp = termSplitReturnApp;
			
			checkNumber(termOldApp,1);
			checkNumber(termNewApp,2);
			
			ApplicationTerm termOldAppInnerApp = convertApp(termOldApp.getParameters()[0]);
			
			checkNumber(termOldAppInnerApp,3);								
			
			Term termF1 = termOldAppInnerApp.getParameters()[0];
			Term termF2 = termOldAppInnerApp.getParameters()[1];
			Term termF3 = termOldAppInnerApp.getParameters()[2];
			
			pm_func(termOldApp,"not");
			pm_func(termOldAppInnerApp,"ite");
			pm_func(termNewApp,"or");
			
			if (splitRule == ":ite-2") {
				// or is commutative
				if (termNewApp.getParameters()[0] != termF1
					&& termNewApp.getParameters()[1] != termF1)
					throw new AssertionError("Error 1 at " + splitRule);
			
				if (termNewApp.getParameters()[0] != mSkript.term("not", termF3)
					&& termNewApp.getParameters()[1] != mSkript.term("not", termF3))
					throw new AssertionError("Error 2 at " + splitRule);
			} else {
				ApplicationTerm termNewAppInner2App = convertApp(termNewApp.getParameters()[1]);
				ApplicationTerm termNewAppInner1App = convertApp(termNewApp.getParameters()[0]);
			
				pm_func(termNewAppInner1App,"not");
				pm_func(termNewAppInner2App,"not");
				
				checkNumber(termNewAppInner1App, 1);
				checkNumber(termNewAppInner2App, 1);
				
				// or is commutative
				if (termNewAppInner1App.getParameters()[0] != termF2
					&& termNewAppInner2App.getParameters()[0] != termF1)
					throw new AssertionError("Error 3 at " + splitRule);

				if (termNewAppInner1App.getParameters()[0] != termF1
					&& termNewAppInner2App.getParameters()[0] != termF2)
					throw new AssertionError("Error 4 at " + splitRule);
			}
			
			/* Not nice: Not checked, if the F are boolean, which
			 * they should.
			 */
				
			stackPush(splitApp.getParameters()[1], splitApp);
			return;
		} else {
			throw new AssertionError("Error: The following split-rule "
					 + "is unknown: " + splitRule);
		}
	}
			
	public void stackPush(Term pushTerm, ApplicationTerm keyTerm) {
		mCacheConv.put(keyTerm, pushTerm);
		mStackResults.push(pushTerm);
		mStackResultsDebug.push(keyTerm);
	}
	
	public Term stackPopCheck(Term expected) {
		if (mStackResults.size() !=  mStackResultsDebug.size()) {
			throw new AssertionError(
					"The debug-stack and the result-stack have different size");
		}
		Term returnTerm = mStackResults.pop();
		Term debugTerm = mStackResultsDebug.pop();

		if (mCacheConv.get(debugTerm) !=  returnTerm) {
			throw new AssertionError("The debugger couldn't associate "
					+ returnTerm.toStringDirect()
					+ " with " + debugTerm.toStringDirect());
		}
		if (expected != null && debugTerm != expected)
			throw new AssertionError("Unexpected Term on proofchecker stack.");
		
		return returnTerm;
	}
	
	public Term rewriteTerm(final Term termOrig, final Term termDelete, final Term termInsert) {
		
		return new TermTransformer() {
			
			private boolean isQuoted(Term t) {
				
				if (t instanceof AnnotatedTerm) {
					AnnotatedTerm annot = (AnnotatedTerm) t;
					for (Annotation a : annot.getAnnotations()) {
						if (a.getKey().equals(":quoted"))
							return true;
					}
				}
				return false;
			}
			
			@Override
			public void convert(Term t) {
				if (t == termDelete) {
					setResult(termInsert);
				} else if (isQuoted(t)) {
					setResult(t);
				} else {
					super.convert(t);
				}
			}
		} .transform(termOrig);
		
		
	}
		
	
	/* Convert a term to an SMTAffineTerm
	 * @param term The term to convert.
	 * @return The converted term.
	 */
	SMTAffineTerm calculateTerm(Term term) {
		if (mDebug.contains("calculateTerm"))
			System.out.println("Calculate the term: " + term.toStringDirect());
		if (term instanceof ApplicationTerm) {
			ApplicationTerm termApp = (ApplicationTerm) term;
			SMTAffineTerm resultTerm;
			if (pm_func_weak(termApp,"+")) {
				if (termApp.getParameters().length < 1)
					throw new AssertionError("Error 1 in add in calculateTerm with term " + term.toStringDirect());
				resultTerm =
						SMTAffineTerm.create(termApp.getSort().getName() == "Real"
						                        ? mSkript.decimal("0.0") 
						                        : mSkript.numeral("0"));
				for (Term summand : termApp.getParameters()) {	
					resultTerm = resultTerm.add(calculateTerm(summand));
				}					
				return resultTerm;
			} else if (pm_func_weak(termApp, "-")) {
				if (termApp.getParameters().length == 1)
					return (calculateTerm(termApp.getParameters()[0]).negate());
				
				if (termApp.getParameters().length == 2)
					return calculateTerm(termApp.getParameters()[0]).add(
							calculateTerm(termApp.getParameters()[1]).negate());
				
				throw new AssertionError("Error: The term with a \"-\" didn't have <= 2 arguments. The term was "
						+ term.toStringDirect());
			} else if (pm_func_weak(termApp, "*")) {
				if (termApp.getParameters().length != 2)
					throw new AssertionError("Error in mul in calculateTerm with term " + term.toStringDirect());
				
				SMTAffineTerm factor1 = calculateTerm(termApp.getParameters()[0]);
				SMTAffineTerm factor2 = calculateTerm(termApp.getParameters()[1]);
				if (factor1.isConstant())					
					return SMTAffineTerm.create(factor1.getConstant(), factor2);
				if (factor2.isConstant())					
					return SMTAffineTerm.create(factor2.getConstant(), factor1);
				throw new AssertionError("Error: Couldn't find the constant in the SMTAffineTerm multiplication. "
						+ "The term was " + termApp.toStringDirect());
			} else if (pm_func_weak(termApp, "/")) {
				if (termApp.getParameters().length != 2)
					throw new AssertionError("Error 1 in div in calculateTerm with term " + term.toStringDirect());
				
				SMTAffineTerm divident = calculateTerm(termApp.getParameters()[0]);
				SMTAffineTerm divisor = calculateTerm(termApp.getParameters()[1]);
				
				if (divisor.isConstant())
					return SMTAffineTerm.create(divident.getConstant().div(divisor.getConstant()), mSkript.sort("Real"));
					// Not nice: use of "Real"
				
				throw new AssertionError("Error: Couldn't find the constant in the SMTAffineTerm division. "
						+ "The term was " + termApp.toStringDirect());
			} else if (pm_func_weak(termApp, "=")
					|| pm_func_weak(termApp, "<=")
					|| pm_func_weak(termApp, "<")
					|| pm_func_weak(termApp, ">")
					|| pm_func_weak(termApp, ">=")) {
				if (termApp.getParameters().length != 2)
					throw new AssertionError("Error 1 in = in calculateTerm with term " + term.toStringDirect());
				
				SMTAffineTerm leftSide = calculateTerm(termApp.getParameters()[0]);
				SMTAffineTerm rightSide = calculateTerm(termApp.getParameters()[1]);
				
				SMTAffineTerm leftSideNew =  leftSide.add(rightSide.negate());
				SMTAffineTerm rightSideNew =  rightSide.add(rightSide.negate()); //=0
				SMTAffineTerm[]	sides = new SMTAffineTerm[2];
				if (!leftSideNew.isConstant())
					sides[0] = leftSideNew.div(leftSideNew.getGcd());
				else
					sides[0] = leftSideNew;

				if (!rightSideNew.isConstant())
					sides[1] = rightSideNew.div(rightSideNew.getGcd());
				else
					sides[1] = rightSideNew;

				return SMTAffineTerm.create(mSkript.term(termApp.getFunction().getName(), sides));
			
			} else {
				//Throwing an Error would be wrong, because of self-defined functions.
				Term[] termAppParamsCalc = new Term[termApp.getParameters().length];
				for (int i = 0; i < termApp.getParameters().length; i++)
					termAppParamsCalc[i] = calculateTerm(termApp.getParameters()[i]);
				
				return SMTAffineTerm.create(mSkript.term(termApp.getFunction().getName(),
						termAppParamsCalc));
			}
		
		
						
		} else if (term instanceof ConstantTerm) {
			return SMTAffineTerm.create(term);
		} else if (term instanceof SMTAffineTerm) {
			return (SMTAffineTerm) term;
		} else
			throw new AssertionError("Error 3 in calculateTerm with term " + term.toStringDirect());
	}
	
	ApplicationTerm convertApp(Term term, String debugString) {
		if (mDebug.contains("convertApp"))
			System.out.println("Der untere Aufruf hat die ID: " + debugString);
		
		return convertApp(term);
	}
	
	ApplicationTerm convertApp(Term term) {
		if (mDebug.contains("convertApp"))
			System.out.println("Aufruf");
		
		if (!(term instanceof ApplicationTerm)) {
			throw new AssertionError("Error: The following term should be an ApplicationTerm, "
					+ "but is of the class " + term.getClass().getSimpleName() + ".\n"
					+ "The term was: " + term.toString());
		}
		
		return (ApplicationTerm) term;
	}
	
	ApplicationTerm convertApp_hard(Term term) {
		if (term instanceof AnnotatedTerm)
			return convertApp(((AnnotatedTerm) term).getSubterm(), "annot");
		
		return convertApp(term, "hard");
	}
	
	AnnotatedTerm convertAnn(Term term) {
		if (!(term instanceof AnnotatedTerm)) {
			throw new AssertionError("Error: The following term should be an AnnotatedTerm, "
					+ "but is of the class " + term.getClass().getSimpleName() + ".\n"
					+ "The term was: " + term.toString());
		}
		
		return (AnnotatedTerm) term;
	}
	
	ConstantTerm convertConst(Term term) {
		if (!(term instanceof ConstantTerm)) {
			throw new AssertionError("Error: The following term should be a ConstantTerm, "
					+ "but is of the class " + term.getClass().getSimpleName() + ".\n"
					+ "The term was: " + term.toString());
		}
		
		return (ConstantTerm) term;
	}
	
	Term convertConst_Neg(Term term) {
		if (term instanceof ConstantTerm) {
			return (ConstantTerm) term;
		}
		
		// Then it must be a negative number
		ApplicationTerm termApp = convertApp(term);
		pm_func(termApp,"-");
		
		if (termApp.getParameters()[0] instanceof ConstantTerm)
				return termApp;
		
		throw new AssertionError("Error: The following term should be a ConstantTerm, "
				+ "but is of the class " + term.getClass().getSimpleName() + ".\n"
				+ "The term was: " + term.toString());
	}
	
	boolean checkInt_weak(Term term) {
		if (term.getSort() == mSkript.sort("Int"))
			return true;
		
		// Then it must be a negative Integer
		
		ApplicationTerm termApp = convertApp(term);
		pm_func(termApp,"-");
		
		if (termApp.getParameters()[0].getSort() == mSkript.sort("Int"))
			return true;
	
		return false;
//		throw new AssertionError("Error: The following term should be an Integer, "
//				+ "but is of the sort " + term.getSort().getName() + ".\n"
//				+ "The term was: " + term.toString());
	}
	
	// Now some pattern-match-functions.

	//Throws an error if the pattern doesn't match
	void pm_func(ApplicationTerm termApp, String pattern) {
		if (!termApp.getFunction().getName().equals(pattern))
			throw new AssertionError("Error: The pattern \"" + pattern
					+ "\" was supposed to be the function symbol of " + termApp.toStringDirect() + "\n"
					+ "Instead it was " + termApp.getFunction().getName());
	}
	
	void pm_func(Term term, String pattern) {
		pm_func(convertApp(term),pattern);
	}
	
	boolean pm_func_weak(ApplicationTerm termApp, String pattern) {
		return termApp.getFunction().getName().equals(pattern);
	}
	
	boolean pm_func_weakest(Term term, String pattern) {
		if (term instanceof ApplicationTerm)
			return pm_func_weak((ApplicationTerm) term, pattern);
		
		return false;
	}
	
	// Does this function make any sense?
	boolean pm_func_weak(Term term, String pattern) {
		if (term instanceof ApplicationTerm)
			return pm_func_weak((ApplicationTerm) term, pattern);
		
		throw new AssertionError("Expected an ApplicationTerm in func_weak!");
	}
	
	void pm_annot(AnnotatedTerm termAnn, String pattern) {
		if (termAnn.getAnnotations()[0].getKey() != pattern)
			throw new AssertionError("Error: The pattern \"" + pattern
					+ "\" was supposed to be the annotation of " + termAnn.toString() + "\n"
					+ "Instead it was " + termAnn.getAnnotations()[0].toString());
		
		if (termAnn.getAnnotations().length != 1)
			throw new AssertionError("Error: A term has " + termAnn.getAnnotations().length + " annotations,"
					+ ", but was supposed to have just one.");	
	}
	
	void checkNumber(Term[] termArray, int n) {
		if (termArray.length < n) {
			System.out.println("The array: [...");
			for (Term el: termArray)
				System.out.println(el.toStringDirect());
			System.out.println("...]");
			throw new AssertionError("Error: "
					+ "The array is to short!"
					+ "\n It should have length " + n);
		}
	}
	
	void checkNumber(ApplicationTerm termApp, int n) {
		if (termApp.getParameters().length < n)
			throw new AssertionError("Error: "
					+ "The parameter-array of " + termApp.toStringDirect() + " is to short!"
					+ "\n It should have length " + n);
	}
	
	/**
	 * Check if there is an equality path from termStart to termEnd.
	 * This reports errors using reportError.
	 * 
	 * @param subpaths the subpaths from the CC-lemma annotations.  To ensure
	 * 	termination, currently investigated subpaths are removed.
	 * @param premises the already proven equalities.  This is initialized to 
	 *  the equalities occurring in the conflict. 
	 * @param termStart one side of the equality.
	 * @param termEnd the other side of the equality.
	 */
	void checkEqualityPath(HashMap<SymmetricPair<Term>,Term[]> subpaths, 
			HashSet<SymmetricPair<Term>> premises,
			Term termStart, Term termEnd) {
		if (mDebug.contains("LemmaCC")) {
			mLogger.debug("Searching for a way from " + termStart.toStringDirect()
					+ " \n to " + termEnd.toStringDirect());
		}
		
		if (mDebug.contains("allSubpaths")) {
			mLogger.debug("All subpaths:");
			for (Term[] values : subpaths.values()) {
				StringBuilder sb = new StringBuilder();
				for (Term value : values)
					sb.append(" ~~ ").append(value.toStringDirect());
				mLogger.debug(sb.toString());
			}
		}
				
		
		// Are the terms already equal?
		if (termStart == termEnd) {
			if (mDebug.contains("LemmaCC"))
				mLogger.debug("It's equal.");
			return;
		}
		SymmetricPair<Term> searchPair = new SymmetricPair<Term>(termStart, termEnd);
		
		/* The reason for checking the premises before the subpaths is,
		 * that the subpaths may contain the same equality as the premises, which
		 * could lead to infinite loops.
		 */
		
		// Is the searched equality already a premise?
		if (premises.contains(searchPair)) {
			if (mDebug.contains("LemmaCC"))
				mLogger.debug("It's a premise or already proven");
			return;
		}
		
		// Does a path for the searched equality exist?
		if (subpaths.containsKey(searchPair)) {
			if (mDebug.contains("LemmaCC"))
				mLogger.debug("It's solvable via a subpath");
			
			Term[] path = subpaths.remove(searchPair);
			assert (path[0] == termStart && path[path.length - 1] == termEnd)
				|| (path[0] == termEnd && path[path.length - 1] == termStart);
			for (int i = 0; i < path.length - 1; i++) {
				// TODO: Make it non-recursive?
				checkEqualityPath(subpaths, premises, path[i], path[i + 1]);
			}
			/* Path is proven, add it to cache */
			premises.add(searchPair);
			return;
		}
		
		/* So the pair can't be found, then
		 * it must be a pair of two functions with the same
		 * function symbol and parameters which can be found.
		 */
		if (termStart instanceof ApplicationTerm
				&& termEnd instanceof ApplicationTerm) {
			ApplicationTerm startApp = (ApplicationTerm) termStart;
			ApplicationTerm endApp = (ApplicationTerm) termEnd;
			Term[] startParams = startApp.getParameters();
			Term[] endParams = endApp.getParameters();
		
			if (startApp.getFunction() == endApp.getFunction()
				&& startParams.length == endParams.length) {
				if (mDebug.contains("LemmaCC"))
					mLogger.debug("It's a function-equality");
				
				// check if for each parameter-pair a path can be found
				
				for (int i = 0; i < startApp.getParameters().length; i++) {
					checkEqualityPath(subpaths, premises, 
							startParams[i],	endParams[i]);
				}
				return;
			}
		}
		reportError("Cannot explain equality " + termStart + " = " + termEnd);
	}
	
	ApplicationTerm uniformizeInEquality(ApplicationTerm termApp) {
		ApplicationTerm termIneq;
		boolean negated = pm_func_weak(termApp, "not");
		
		if (!pm_func_weak(termApp, "<=")
				&& !pm_func_weak(termApp, "<")
				&& !pm_func_weak(termApp, ">=")
				&& !pm_func_weak(termApp, ">")
				&& !pm_func_weak(termApp, "=")
				&& !pm_func_weak(termApp, "not"))
			throw new AssertionError("Error 0 in uniformizeInequality");
		
		// Get the inequality
		if (negated)
			termIneq = convertApp_hard(termApp.getParameters()[0]);
		else
			termIneq = termApp;
		
		String relation = termIneq.getFunction().getName();
		checkNumber(termIneq,2);
		
		// Take everything to the left side
		
		SMTAffineTerm termLeft = calculateTerm(termIneq.getParameters()[0]);
		SMTAffineTerm termRight = calculateTerm(termIneq.getParameters()[1]);
		SMTAffineTerm termLeftNew = termLeft.add(termRight.negate());
		
		// Convert the negation into the inequality
		if (negated)
			if (relation == "<=")
				relation = ">";
			else if (relation == ">=")
				relation = "<";
			else if (relation == "<")
				relation = ">=";
			else if (relation == ">")
				relation = "<=";
			else
				throw new AssertionError("Error 1 in uniformizeInequality");
		
		// Convert: >= to <= and > to <
		if (relation == ">=") {
			termLeftNew = termLeftNew.negate();
			relation = "<=";
		} else if (relation == ">") {
			termLeftNew = termLeftNew.negate();
			relation = "<";
		}
		
		// Extra-Case for Integers
		if (onlyInts(termLeftNew) && relation == "<") {
			termLeftNew = termLeftNew.add(Rational.ONE);
			relation = "<=";
		}
		
		// Now build the to-be-returned term
		Term[] params = new Term[2];
		params[0] = termLeftNew;
		
		if (!termLeftNew.getSort().isNumericSort())
			throw new AssertionError("Error 2 in uniformizeInequality");
		
		params[1] = Rational.ZERO.toTerm(termLeftNew.getSort());		
		
		return convertApp(mSkript.term(relation, params), "unif2");
	}
	
	boolean onlyInts(Term term) {
		if (term instanceof AnnotatedTerm)
			return onlyInts(((AnnotatedTerm) term).getSubterm());
		else if (term instanceof ApplicationTerm) {
			ApplicationTerm termApp = convertApp(term);
			for (Term param : termApp.getParameters())
				if (!onlyInts(param))
					return false;
			return true;
		} else if (term instanceof SMTAffineTerm) {
			SMTAffineTerm termAff = (SMTAffineTerm) term;

			return termAff.isIntegral();
		} else {
			// So the term is constant
			
			return term.getSort().equals(mSkript.sort("Int"));			
		}			
	}
	
	void isConstant(SMTAffineTerm term, Rational constant) {
		if (!isConstant_weak(term, constant))
			throw new AssertionError("The following term should be the "
						+ "constant " + constant.toString() + " but isn't: "
						+ term.toStringDirect());
	}

	boolean isConstant_weak(SMTAffineTerm term, Rational constant) {
		if (!term.isConstant() || term.getConstant() != constant)
			return false;
		return true;
	}
	
	boolean uniformedSame(ApplicationTerm term1, ApplicationTerm term2) {
		if (term1.equals(term2))
			return true;
		
		SMTAffineTerm term1leftAff = calculateTerm(term1.getParameters()[0]);
		SMTAffineTerm term2leftAff = calculateTerm(term1.getParameters()[0]);
		
		if (term1leftAff.equals(term2leftAff))
			return true; //Should be unreachable
		
		// Maybe one side of the equation is the negation of the other
		if (term1leftAff.equals(term2leftAff.negate()))
			return true; //Should be unreachable
		
		return false;
	}
	
	boolean termITEHelper_isEqual(Term termNeg, Term termGoal) {
		if (termNeg == termGoal)
			return true;
		
		ApplicationTerm termNegApp = convertApp(termNeg);
		
		pm_func(termNegApp,"not");
		
		checkNumber(termNegApp,1);
		
		return (!termITEHelper_isEqual(termNegApp.getParameters()[0], termGoal));
	}
	
	Term splitNotOrHelper_pushNotInside(Term term) {
		if (!(term instanceof ApplicationTerm))
			return term;
		
		ApplicationTerm termApp = convertApp(term);
		
		if (!pm_func_weak(termApp,"not")) {
			Term[] paramsCalc = new Term[termApp.getParameters().length];
			
			for (int i = 0; i < termApp.getParameters().length; i++)
				paramsCalc[i] = splitNotOrHelper_pushNotInside(termApp.getParameters()[i]);				
			
			return mSkript.term(termApp.getFunction().getName(), paramsCalc);					
		}
		
		pm_func(termApp, "not"); // Should be impossible to throw an error
		
		checkNumber(termApp, 1);
		
		if (!(termApp.getParameters()[0] instanceof ApplicationTerm))
			return term;
		
		ApplicationTerm termAppInnerApp = convertApp(termApp.getParameters()[0]);
		
		if (pm_func_weak(termAppInnerApp, "not"))
			return splitNotOrHelper_pushNotInside(termAppInnerApp.getParameters()[0]);
		
		
		
		if (pm_func_weak(termAppInnerApp, "or")) {
			Term[] paramsCalc = new Term[termAppInnerApp.getParameters().length];
			
			for (int i = 0; i < paramsCalc.length; i++)
				paramsCalc[i] = splitNotOrHelper_pushNotInside(
						mSkript.term("not", termAppInnerApp.getParameters()[i]));
			
			return mSkript.term("and", paramsCalc);
		}
		
		return term;
	}
	
	ArrayList<Term> splitNotOrHelper_getConjunctsPushed(Term term) {
		/* Important:
		 * Assumes that the input-term is an
		 * output of the pushNot-helper-function
		 */
		
		ArrayList<Term> termRet = new ArrayList<Term>();
		
		if (!pm_func_weakest(term, "and")) {
			termRet.add(term);
			return termRet;
		}
		
		// So the term has the form (and ... )
		
		ApplicationTerm termApp = convertApp(term);
		for (Term param : termApp.getParameters())
			termRet.addAll(splitNotOrHelper_getConjunctsPushed(param));
		return termRet;
	}
	
	public Term unquote(Term quotedTerm) {
		if (quotedTerm instanceof AnnotatedTerm) {
			AnnotatedTerm annTerm = (AnnotatedTerm) quotedTerm;
			Annotation[] annots = annTerm.getAnnotations();
			if (annots.length == 1 && annots[0].getKey() == ":quoted") {
				Term result = annTerm.getSubterm();
				return result;
			}
		}
		reportError("Expected quoted literal, but got " + quotedTerm);
		return quotedTerm;
	}
	
	public boolean checkOrMinus(Term orTerm, Term literal) {
		if (orTerm instanceof ApplicationTerm) {
			ApplicationTerm theOrTerm = (ApplicationTerm) orTerm;
			if (theOrTerm.getFunction().getName() == "or"
					&& Arrays.asList(theOrTerm.getParameters())
						.contains(negate(literal)))
				return true;
		}
		return false;
	}
}