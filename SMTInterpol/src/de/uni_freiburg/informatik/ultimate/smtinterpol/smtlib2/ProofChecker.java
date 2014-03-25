/**
 * @author Raiola
 */

package de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2;

import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.FormulaUnLet;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm; //May not be needed
//import de.uni_freiburg.informatik.ultimate.logic.FormulaUnLet;
//import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;
//import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
//import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.SMTAffineTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.SymmetricPair;



import java.math.BigInteger;
//import java.util.ArrayList;
//import java.util.HashMap;
import java.util.*;

public class ProofChecker extends SMTInterpol {
	
	HashSet<String> debug = new HashSet<String>(); // Just for debugging
	
	HashMap<Term, Term> pcCache; //Proof Checker Cache
	
	// Declarations for the Walker
	Stack<WalkerId<Term,String>> stackWalker = new Stack<WalkerId<Term,String>>();
	Stack<Term> stackResults = new Stack<Term>();
	Stack<Term> stackResultsDebug = new Stack<Term>();
	Stack<Annotation[]> stackAnnots = new Stack<Annotation[]>();
	
	public boolean check(Term res, SMTInterpol smtInterpol) {
		
		// Just for debugging
		//debug.add("currently");
		//debug.add("passt");
		//debug.add("hardTerm");
		//debug.add("LemmaLAadd");
		//debug.add("calculateTerm");
		//debug.add("WalkerPath");
		//debug.add("LemmaCC");
		//debug.add("newRules");
		//debug.add("convertAppID");
		//debug.add("cacheUsed");
		
		// Initializing the proof-checker-cache
		pcCache = new HashMap<Term, Term>();
				
		Term resCalc;
		// Now non-recursive:
		stackWalker.push(new WalkerId<Term,String>(new FormulaUnLet().unlet(res),""));
		WalkerId<Term,String> currentWalker;
		
		
		while (!stackWalker.isEmpty())
		{
			if (debug.contains("WalkerPath"))
			{
				for (int i = 0; i < stackWalker.size(); i++)
				{
					System.out.println("Walker(" + i + "): [" + stackWalker.elementAt(i).t.toStringDirect()
							+ "," + stackWalker.elementAt(i).s + "]");
				}
				System.out.println("");
				
				for (int i = 0; i < stackResults.size(); i++)
				{
					System.out.println("Result(" + i + "): " + stackResults.elementAt(i).toStringDirect());
				}
				System.out.println("");
				
				for (int i = 0; i < stackResultsDebug.size(); i++)
				{
					System.out.println("Debug(" + i + "): " + stackResultsDebug.elementAt(i).toStringDirect());
				}
				System.out.println("");
				
				for (int i = 0; i < stackAnnots.size(); i++)
				{
					System.out.println("Annot1(" + i + "): " + stackAnnots.elementAt(i)[0].getKey()
							+ " " + stackAnnots.elementAt(i)[0].getValue());
				}
				System.out.println("");
				System.out.println("");
			}
			
			currentWalker = stackWalker.pop();
			if (currentWalker.s == "")
			{
				walk((Term) currentWalker.t, smtInterpol);
			} else
			{
				walkSpecial((Term) currentWalker.t, 
						(String) currentWalker.s, smtInterpol);
			}
		}		
		
		if (!stackResults.isEmpty())
		{
			resCalc = stackPop("end");
		} else
		{
			throw new AssertionError("Error: At the end of verifying the proof, there is no result left.");
		}
		
		if (resCalc == smtInterpol.term("false"))
		{
			return true;
		} else {
			System.out.println("The result-stack had " + (stackResults.size()  + 1) + " element(s).");
			if (stackResults.size() > 0)
			{
				System.out.println("And on top is: " + stackPop("end").toStringDirect());
			}
			return false;
		}
		
		
	}
	
	public Term negate(Term formula, SMTInterpol smtInterpol)
	{		
		if (formula instanceof ApplicationTerm)
		{
			ApplicationTerm appFormula = (ApplicationTerm) formula;
			
			if (appFormula.getFunction().getName() == "not")
			{
				return appFormula.getParameters()[0];
			}
		}
		
		//Formula is not negative
		return smtInterpol.term("not", formula);
	}
	
	public void walk(Term term, SMTInterpol smtInterpol)
	{
		/* Non-recursive */
		/* Takes proof, returns proven formula */
		
		/* Check the cache, if the unfolding step was already done */
		if (pcCache.containsKey(term))
		{
			if (pcCache.get(term) == null)
			{
				throw new AssertionError("Error: The term " + term.toString() + " was already "
						+ "calculated, but isn't in the cache.");
			}
			if (debug.contains("cacheUsed"))
				System.out.println("Calculation of the term " + term.toStringDirect() 
						+ " is known: " + pcCache.get(term).toStringDirect());
			stackPush(pcCache.get(term), term);
			return;
		}
				
		/* Declaration of variables used later */
		String functionname;
		AnnotatedTerm termAppInnerAnn;
		AnnotatedTerm annTerm;
		
		/* Look at the class of the term and treat each different */
		if (term instanceof ApplicationTerm) 
		{			
			/* It is an ApplicationTerm */
			ApplicationTerm termApp = (ApplicationTerm) term;
			
			/* Get the function and parameters */
			functionname = termApp.getFunction().getName();
			
			/* Just for debugging */
			if (debug.contains("currently"))
				System.out.println("Currently looking at: " + functionname);
			
			// A global initialization for rewrite and intern:
			ApplicationTerm termEqApp; // The ApplicationTerm with the equality
			
			/* Look at the function of the ApplicationTerm and treat each different */
			switch (functionname)
			{
			case "@res":
				/* Alright: This function is expected to have as first argument the clause which is used
				 * further, after the pivots are deleted.
				 */
				
				stackWalker.push(new WalkerId<Term,String>(termApp, "res"));
				calcParams(termApp);
				return;
				
			case "@eq":
				stackWalker.push(new WalkerId<Term,String>(termApp, "eq"));
				calcParams(termApp);
				return;
				
			case "@lemma":
				
				// If possible return the un-annotated version
				// Warning: Code duplicates (Random number: 498255)
//				if (termApp.getParameters()[0] instanceof ApplicationTerm)
//					System.out.println("");
				termAppInnerAnn = convertAnn(termApp.getParameters()[0]);
				
				if (termAppInnerAnn.getAnnotations()[0].getKey() == ":LA")
				{
					// The disjunction
					ApplicationTerm termLemmaDisj = convertApp(termAppInnerAnn.getSubterm());
					
					pm_func(termLemmaDisj,"or");
					
					int arrayLength = termLemmaDisj.getParameters().length;
					ApplicationTerm[] termMultDisj = new ApplicationTerm[arrayLength]; // multiplied [negated] disjuncts
					ApplicationTerm[] termNegDisj = new ApplicationTerm[arrayLength]; // negated disjuncts
					ApplicationTerm[] termNegDisjMayDeep = new ApplicationTerm[arrayLength]; // negated disjuncts maybe one level deeper
					ApplicationTerm[] termTurnDisj = new ApplicationTerm[arrayLength]; // disjuncts with potentially turned <=/</>=/>
					ApplicationTerm[] termNegDisjUnif = new ApplicationTerm[arrayLength];
					ApplicationTerm[] termNegDisjInv = new ApplicationTerm[arrayLength];
					
					// Now get the factors:
					Term[] numbers = (Term[]) termAppInnerAnn.getAnnotations()[0].getValue();
					Rational[] numbersSMT = new Rational[numbers.length];
					
					for (int i = 0; i < numbers.length; i++)
						numbersSMT[i] = calculateTerm(numbers[i], smtInterpol).getConstant();
					
					// New: Transform all to ... <= 0 if possible, otherwise to ... <= 0 and ... < 0 
					
					// Step 1: Uniformize the negated disjuncts and multiply with factor
					
					boolean foundLe = false; // found lower-equal (<=)
					boolean foundLt = false; // found lower-than (<)
					boolean foundEq = false; // found equality (=)
					
					for (int i = 0; i < arrayLength; i++)
					{
						// The convertApp_hard's are used to remove the ":quoted"-annotation
						
						// Negate them and remove the annotation
						termNegDisj[i] = convertApp_hard(negate(convertApp_hard(termLemmaDisj.getParameters()[i]), smtInterpol));
						
						// Get rid of each negation
						String prerelation = termNegDisj[i].getFunction().getName();
						String relation;
						if (prerelation == "not")
						{
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
						} else
						{
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
						
						termTurnDisj[i] = convertApp(smtInterpol.term(relation, termNegDisjMayDeep[i].getParameters()));
						
						
						// Multiply with -1			
						Term[] paramsTemp1 = new Term[2];
						if (numbersSMT[i].isNegative())
						{
							paramsTemp1[0] = calculateTerm(termTurnDisj[i].getParameters()[0],smtInterpol).negate();
							paramsTemp1[1] = calculateTerm(termTurnDisj[i].getParameters()[1],smtInterpol).negate();
							numbersSMT[i] = numbersSMT[i].negate();
						} else
						{
							paramsTemp1 = termTurnDisj[i].getParameters();
						}
						
						termNegDisjInv[i] = convertApp(smtInterpol.term(relation, paramsTemp1));
								
						//Uniformize them
						termNegDisjUnif[i] = uniformizeInEquality(termNegDisjInv[i], smtInterpol);
																		
						// Multiply both sides		
						Term[] paramsTemp2 = new Term[2];
						paramsTemp2[0] = calculateTerm(termNegDisjUnif[i].getParameters()[0], smtInterpol).mul(numbersSMT[i]);
						paramsTemp2[1] = calculateTerm(termNegDisjUnif[i].getParameters()[1], smtInterpol).mul(numbersSMT[i]);
						
						termMultDisj[i] = convertApp(smtInterpol.term(relation, paramsTemp2));
						
						foundLe = (foundLe || pm_func_weak(termMultDisj[i], "<="));
						foundLt = (foundLt || pm_func_weak(termMultDisj[i], "<"));
						foundEq = (foundEq || pm_func_weak(termMultDisj[i], "="));
					}
					
					// Step 2: Add them up
					
					SMTAffineTerm termSum = calculateTerm(termMultDisj[0].getParameters()[0],smtInterpol);
					
					for (int i = 1; i < arrayLength; i++)
						termSum = termSum.add(calculateTerm(termMultDisj[i].getParameters()[0],smtInterpol));
					
					
					// Step 3: The contradiction
					if (!termSum.isConstant())
						throw new AssertionError("Error 2 in @lemma_:LA");
									
					Rational constant = termSum.getConstant();
					
					
					// < is strictly stronger than <= is strictly stronger than =
					if (foundLt) {
						if(constant.isNegative())
							throw new AssertionError("Error 4 in @lemma_:LA");
					}
					else if (foundLe) {
							if(constant.isNegative() || constant.equals(Rational.ZERO))
								throw new AssertionError("Error 3 in @lemma_:LA");
					}
					else if (foundEq)
						if(constant == Rational.ZERO)
							throw new AssertionError("Error 5 in @lemma_:LA");
					
				} else if (termAppInnerAnn.getAnnotations()[0].getKey() == ":CC")
				{
					//Syntactical correctness
					ApplicationTerm termLemmaApp = convertApp(termAppInnerAnn.getSubterm());
					
					pm_func(termLemmaApp,"or");
					
					int arrayShortLength = termLemmaApp.getParameters().length - 1;
					
					// The negated disjuncts
					ApplicationTerm[] termLemmaAppNegDisj = new ApplicationTerm[arrayShortLength]; //Negated Disjuncts WITHOUT not
					
					ApplicationTerm termGoal = convertApp((Term) 
							((Object[]) termAppInnerAnn.getAnnotations()[0].getValue())[0]);
					
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
					
					pm_func(termGoal,"=");
					
					for (Term equality : termLemmaAppNegDisj)
						pm_func(equality,"=");
					
					Object[] annotValues = (Object[]) termAppInnerAnn.getAnnotations()[0].getValue();
					
					/* Get the subpaths. The HashMap contains pairs:
					 * - Key: Start & End of the path as Pair
					 * - Object: Path
					 */
					
					HashMap<SymmetricPair<Term>, Term[]> subpaths =
							new HashMap<SymmetricPair<Term>,Term[]>();
					
					for (int i = 1; i < annotValues.length; i++)
					{
						if (annotValues[i] instanceof String)
							if (annotValues[i] == ":subpath")
								continue;
						
						if (annotValues[i] instanceof Term[])
						{
							Term[] arrayTemp = (Term[]) annotValues[i];
							SymmetricPair<Term> pairTemp =
									new SymmetricPair<Term>(arrayTemp[0],arrayTemp[arrayTemp.length-1]);

							subpaths.put(pairTemp, arrayTemp);
						}
					}
					
					/* Get the premises. The HashMap contains pairs:
					 * - Key: Pair of the left term and the right term (which are equal by premise)
					 * - Object: Array of those terms
					 */
					HashMap<SymmetricPair<Term>, Term[]> premises =
							new HashMap<SymmetricPair<Term>,Term[]>();
											
					for (int i = 0; i < arrayShortLength; i++)
					{
						checkNumber(termLemmaAppNegDisj[i],2);							
						
						SymmetricPair<Term> pairTemp = new SymmetricPair<Term>(
								termLemmaAppNegDisj[i].getParameters()[0],termLemmaAppNegDisj[i].getParameters()[1]);
						premises.put(pairTemp,termLemmaAppNegDisj[i].getParameters());
					}
					
					// Now for the pathfinding
					checkNumber(termGoal,2);
					Term termStart = termGoal.getParameters()[0];
					Term termEnd = termGoal.getParameters()[1];
					
					if (!pathFind(subpaths,premises,termStart,termEnd))
						throw new AssertionError("Error at the end of lemma_:CC");
				} else
				{
					System.out.println("Can't deal with lemmas of type "
							+ termAppInnerAnn.getAnnotations()[0].getKey() + ", therefor...");
					System.out.println("Believed as true: " + termApp.toStringDirect() + " .");
				}				
				
				stackPush(termAppInnerAnn.getSubterm(), term);
				return;
				
			case "@tautology":
				
				// If possible return the un-annotated version
				// Warning: Code duplicates (Random number: 498255)
				if (termApp.getParameters()[0] instanceof ApplicationTerm)
					System.out.println("");
				termAppInnerAnn = convertAnn(termApp.getParameters()[0]);
				
				if (termAppInnerAnn.getAnnotations()[0].getKey() == ":eq")
				{
					ApplicationTerm termOr = convertApp(termAppInnerAnn.getSubterm()); // The term with or
					checkNumber(termOr.getParameters(),2);
					
					boolean term1Negated = false;
					
					Term term1 = termOr.getParameters()[0];
					Term term2 = termOr.getParameters()[1];
					
					if (term1 instanceof ApplicationTerm)
						if (pm_func_weak(convertApp(term1),"not"))
							term1Negated = true;
					
					ApplicationTerm termNegApp = null; // The term t with (not t) 
					ApplicationTerm termPosApp = null; // the term without a not around
					
					if (term1Negated)
					{
						termNegApp = convertApp_hard(convertApp(term1).getParameters()[0]);
						termPosApp = convertApp_hard(term2);
					} else {
						pm_func(term2,"not");

						termNegApp = convertApp_hard(convertApp(term2).getParameters()[0]);
						termPosApp = convertApp_hard(term1);
					}
															
//					ApplicationTerm term1Neg = convertApp(termOr.getParameters()[0]); // The first disjunct, still with "not"
//					ApplicationTerm term1Pure = convertApp_hard(term1Neg.getParameters()[0]); // The first disjunct, not with "not" anymore
//					ApplicationTerm term2 = convertApp_hard(termOr.getParameters()[1]); // The second disjunct
					String funcSymb = termNegApp.getFunction().getName();
					
					pm_func(termOr,"or");
					pm_func(termPosApp,funcSymb);
					
					ApplicationTerm termNegUnif = uniformizeInEquality(termNegApp, smtInterpol);
					ApplicationTerm termPosUnif = uniformizeInEquality(termPosApp, smtInterpol);
															
					if (!uniformedSame(termNegUnif,termPosUnif,smtInterpol))
						throw new AssertionError("Error in @taut_eq");
				} 
				else if (termAppInnerAnn.getAnnotations()[0].getKey() == ":or+")
				{
					ApplicationTerm termOr = convertApp(termAppInnerAnn.getSubterm()); // The term with or
					ApplicationTerm term1Neg = convertApp(termOr.getParameters()[0]); // The first disjunkt, still with "not"
					ApplicationTerm term1Pure = convertApp_hard(term1Neg.getParameters()[0]); // The first disjunkt, not with "not" anymore
					
					HashSet<Term> term1Disjuncts = new HashSet<Term>(); // The disjuncts in term 1
					HashSet<Term> term2NDisjuncts = new HashSet<Term>(); // THe disjuncts in term 2-n
					
					term1Disjuncts.addAll(Arrays.asList(term1Pure.getParameters()));
					for (int i = 1; i < termOr.getParameters().length; i++) //The first (i=0) parameter is left out)
						term2NDisjuncts.add(termOr.getParameters()[i]);
					
					pm_func(termOr,"or");
					pm_func(term1Neg,"not");
					pm_func(term1Pure,"or");
					
					
					if (!term1Disjuncts.equals(term2NDisjuncts))
						throw new AssertionError("Error in @taut_or+");
						
					
					/* Not nice: Not checked if there is a quoted-annotation, but 
					 * otherwise it's still correct
					 */
				} 
				else
				{
					System.out.println("Didn't know the following tautology-rule: " + termAppInnerAnn.getAnnotations()[0].getKey()
							+ "therefor had to believed as true: " + termApp.toStringDirect() + " .");
				}
				
				stackPush(termAppInnerAnn.getSubterm(), term);
				return;
				
			case "@asserted":
				System.out.println("Believed as asserted: " + termApp.getParameters()[0].toStringDirect() + " .");
				/* Just return the part without @asserted */
				stackPush(termApp.getParameters()[0], term);
				return;
				
			case "@rewrite":
				
				/* Treatment:
				 *  - At first check if the rewrite rule was correctly executed.
				 *  - OLD: Secondly, remove the @rewrite and the annotation for later uses in the @eq-function.
				 */
				
				/* Get access to the internal terms */
				termAppInnerAnn = convertAnn(termApp.getParameters()[0]); //The annotated term inside the rewrite-term
				termEqApp = convertApp(termAppInnerAnn.getSubterm()); //The application term inside the annotated term inside the rewrite-term
				
				pm_func(termEqApp, "=");
				
				
				/* Read the rule and handle each differently */
				String rewriteRule = termAppInnerAnn.getAnnotations()[0].getKey();
				if (debug.contains("currently"))
					System.out.println("Rewrite-Rule: " + rewriteRule);
				if (debug.contains("hardTerm"))
					System.out.println("Term: " + term.toStringDirect());
				if (false)
				{} else if (rewriteRule == ":trueNotFalse")
				{
					if (!(termEqApp.getParameters()[1] == smtInterpol.term("false")))
					{
						throw new AssertionError("Error: The second argument of a rewrite of the rule " 
								+ rewriteRule + " should be true, but isn't.\n"
								+ "The term was " + termEqApp.toString());
					}
					
					ApplicationTerm termOldApp = convertApp(termEqApp.getParameters()[0]);
					pm_func(termOldApp,"=");
															
					boolean foundTrue = false;
					boolean foundFalse = false;
					
					for (Term subterm : termOldApp.getParameters())
					{
						if (subterm == smtInterpol.term("false"))
						{
							foundFalse = true;
						}
						if (subterm == smtInterpol.term("true"))
						{
							foundTrue = true;
						}
						
						if (foundFalse && foundTrue)
							return;
					}
					
					throw new AssertionError("Error at the end of rule " + rewriteRule
							+ "!\n The term was " + term.toStringDirect());
					
				} else if (rewriteRule == ":constDiff")
				{					
					if (!(termEqApp.getParameters()[1] == smtInterpol.term("false")))
					{
						throw new AssertionError("Error: The second argument of a rewrite of the rule " 
								+ rewriteRule + " should be false, but isn't.\n"
								+ "The term was " + termEqApp.toString());
					}
					
					ApplicationTerm termOldApp = convertApp(termEqApp.getParameters()[0]);
					pm_func(termOldApp,"=");
					
					HashSet<Term> constTerms = new HashSet<Term>();
					
					// Get all constant terms
					for (Term subterm : termOldApp.getParameters())
					{
						if (subterm instanceof ConstantTerm)
						{
							constTerms.add(subterm);
						} else if (subterm instanceof ApplicationTerm)
						{
							// Maybe a negated constant
							ApplicationTerm subtermApp = convertApp(subterm);
							
							if (pm_func_weak(subtermApp, "-"))
								if (subtermApp.getParameters()[0] instanceof ConstantTerm)
									constTerms.add(subterm);
						}
						
					}
					
					if (debug.contains("newRules"))
					{
						System.out.println("The constant terms are:");
						for (Term termC : constTerms)
							System.out.println (termC.toStringDirect());
					}
					
					// Check if there are two different constant terms
					if (constTerms.size() <= 1)
						throw new AssertionError("Error at the end of rule " + rewriteRule
								+ "!\n The term was " + term.toStringDirect());
					
					
				} else if (rewriteRule == ":eqTrue")
				{									
					ApplicationTerm termOldApp = convertApp(termEqApp.getParameters()[0]);					

					pm_func(termOldApp,"=");
					
					boolean multiconjunct = false;
					ApplicationTerm termNewApp = null; //Not nice: Initialisation as null
					if (termEqApp.getParameters()[1] instanceof ApplicationTerm)
						if (pm_func_weak(convertApp(termEqApp.getParameters()[1]), "and"))
						{
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
					
					if (!oldTerms.contains(smtInterpol.term("true")))
						throw new AssertionError("Error 1 at " + rewriteRule + ".\n The term was " + termEqApp.toString());
					
					/* The line below is needed, to have a short equivalence check, even
					 * if more than one term is "true".
					*/
					newTerms.add(smtInterpol.term("true"));
					
					if(!oldTerms.equals(newTerms))
						throw new AssertionError("Error 2 at " + rewriteRule + ".\n The term was " + termEqApp.toString());
					
					// Not nice: j \notin I' isn't checked, but even if j \in I' it's still correct
					
				} else if (rewriteRule == ":eqFalse")
				{
					ApplicationTerm termOldApp = convertApp(termEqApp.getParameters()[0]);
					ApplicationTerm termNewApp = convertApp(termEqApp.getParameters()[1]);					

					pm_func(termOldApp, "=");
					pm_func(termNewApp, "not");
					
					boolean multidisjunct = false;
					ApplicationTerm termNewAppInnerApp = null; //Not nice: Initialisation as null
					if (termNewApp.getParameters()[0] instanceof ApplicationTerm)
						if (pm_func_weak(convertApp(termNewApp.getParameters()[0]), "or"))
						{
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
					
					if (!oldTerms.contains(smtInterpol.term("false")))
						throw new AssertionError("Error 1 at " + rewriteRule + ".\n The term was " + termEqApp.toString());
					
					/* The line below is needed, to have a short equivalence check, even
					 * if more than one term is "true".
					*/
					newTerms.add(smtInterpol.term("false"));
					
					if(!oldTerms.equals(newTerms))
						throw new AssertionError("Error 2 at " + rewriteRule + ".\n The term was " + termEqApp.toString());
					
					// Not nice: j \notin I' isn't checked, but even if j \in I' it's still correct
				
				} else if (rewriteRule == ":eqSame")
				{
					if (!(termEqApp.getParameters()[1] == smtInterpol.term("true")))
					{
						throw new AssertionError("Error: The second argument of a rewrite of the rule "
								+ rewriteRule + " should be true, but isn't.\n"
								+ "The term was " + termEqApp.toString());
					}
					
					ApplicationTerm termOldApp = convertApp(termEqApp.getParameters()[0]);
					
					pm_func(termOldApp, "=");
															
					Term termComp = termOldApp.getParameters()[0]; //compare-term
					for (Term subterm : termOldApp.getParameters())
						if (subterm != termComp)
							throw new AssertionError("Error 2 at rule " + rewriteRule + "!\n The term was " + term.toStringDirect());
				
				} else if (rewriteRule == ":eqSimp")
				{
					ApplicationTerm termOldApp = convertApp(termEqApp.getParameters()[0]);
					ApplicationTerm termNewApp = convertApp(termEqApp.getParameters()[1]);
					
					pm_func(termOldApp, "=");
					pm_func(termNewApp, "=");
					
					HashSet<Term> oldTerms = new HashSet<Term>();
					HashSet<Term> newTerms = new HashSet<Term>();
					
					oldTerms.addAll(Arrays.asList(termOldApp.getParameters()));
					newTerms.addAll(Arrays.asList(termNewApp.getParameters()));
															
					if(!oldTerms.equals(newTerms))
						throw new AssertionError("Error 1 at " + rewriteRule + ".\n The term was " + termEqApp.toString());
					
					// Not nice: I' \subsetneq I isn't checked, but even if I' \supset I, it's still correct
					// Not nice: Not checked if there aren't two doubled terms in termNewApp, but even if there are, it's still correct
					
				}  else if (rewriteRule == ":eqBinary")
				{					
					ApplicationTerm termOldApp = convertApp(termEqApp.getParameters()[0]);
					ApplicationTerm termNewApp = convertApp(termEqApp.getParameters()[1]);
					ApplicationTerm termNewAppInnerApp = convertApp(termNewApp.getParameters()[0]);
					
					pm_func(termOldApp, "=");
					pm_func(termNewApp, "not");
					
					// Is it a binary equality?
					if (termOldApp.getParameters().length == 2)
					{
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
					
					for (int i = 0; i < termNewAppInnerApp.getParameters().length; i++)
					{
						ApplicationTerm termIneqApp = convertApp(termNewAppInnerApp.getParameters()[i]);
						pm_func(termIneqApp,"not");
						
						arrayNewEqApp[i] = convertApp(termIneqApp.getParameters()[0]);
						pm_func(arrayNewEqApp[i],"=");
					}
					
					boolean[] eqFound = new boolean[arrayNewEqApp.length];
					
					for (int i = 0; i < eqFound.length; i++)
						eqFound[i] = false;
					
					// Look for each two distinct terms (j > i) if there exists a fitting equality
					for (int i = 0; i < arrayOldTerm.length; i++)
					{
						for (int j = i + 1; j < arrayOldTerm.length; j++)
						{
//							boolean found = false;
							for (int k = 0; k < arrayNewEqApp.length; k++)
							{
								if (!eqFound[k])
								{
									if(arrayNewEqApp[k].getParameters()[0] == arrayOldTerm[i]
											&& arrayNewEqApp[k].getParameters()[1] == arrayOldTerm[j])										
										eqFound[k] = true; // found = true;
									
									if(arrayNewEqApp[k].getParameters()[1] == arrayOldTerm[i]
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
									+ arrayNewEqApp[i] + "\n. The term was " + term.toStringDirect());

				}
				else if (rewriteRule == ":distinctBool")
				{
					if (termEqApp.getParameters()[1] != smtInterpol.term("false"))
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
						if (subterm.getSort() != smtInterpol.sort("Bool"))
							throw new AssertionError("Error 2 at " + rewriteRule);
					
				
				} else if (rewriteRule == ":distinctSame")
				{					
					if (termEqApp.getParameters()[1] != smtInterpol.term("false"))
					{
						throw new AssertionError("Error: The second argument of a rewrite of the rule "
								+ rewriteRule + " should be false, but it isn't.\n"
								+ "The term was " + termEqApp.toString());
					}
					
					ApplicationTerm termOldApp = convertApp(termEqApp.getParameters()[0]);
					
					pm_func(termOldApp, "distinct");
					
					// Check if two are the same
					for (int i = 0; i < termOldApp.getParameters().length; i++)
						for (int j = i+1; j < termOldApp.getParameters().length; j++)
							if (termOldApp.getParameters()[i] == termOldApp.getParameters()[j])
								return;
					
					throw new AssertionError("Error at the end of rule " + rewriteRule 
							+ "!\n The term was " + term.toStringDirect());
				
				} 
				else if (rewriteRule == ":distinctNeg")
				{
					if (termEqApp.getParameters()[1] != smtInterpol.term("true"))
					{
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
					if (term1 != negate(term2,smtInterpol)
							&& term2 != negate(term1,smtInterpol))
						throw new AssertionError("Error 2 at " + rewriteRule);
				
				} 
				else if (rewriteRule == ":distinctTrue")
				{
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
					
					if (term1.equals(smtInterpol.term("true")))
						termNotTrue = term2;
					else if (term2.equals(smtInterpol.term("true")))
						termNotTrue = term1;
					else
						throw new AssertionError("Error 1 at " + rewriteRule);						
					
					if (termNewApp.getParameters()[0] != termNotTrue)
						throw new AssertionError("Error 2 at " + rewriteRule);
				
				} 
				else if (rewriteRule == ":distinctFalse")
				{
					Term termNew = termEqApp.getParameters()[1];
					ApplicationTerm termOldApp = convertApp(termEqApp.getParameters()[0]);
					
					pm_func(termOldApp, "distinct");
					
					if (termOldApp.getParameters().length != 2)
						throw new AssertionError("Error 2 at " + rewriteRule);
					
					// Check if one is false
					Term term1 = termOldApp.getParameters()[0];
					Term term2 = termOldApp.getParameters()[1];
					
					Term termNotFalse; // The term on the left side which is not true
					
					if (term1.equals(smtInterpol.term("false")))
						termNotFalse = term2;
					else if (term2.equals(smtInterpol.term("false")))
						termNotFalse = term1;
					else
						throw new AssertionError("Error 1 at " + rewriteRule);						
					
					if (termNew != termNotFalse)
						throw new AssertionError("Error 2 at " + rewriteRule);
				
				} 
				else if (rewriteRule == ":distinctBinary")
				{					
					ApplicationTerm termOldApp = convertApp(termEqApp.getParameters()[0]);
					ApplicationTerm termNewApp = convertApp(termEqApp.getParameters()[1]);
					ApplicationTerm termNewAppInnerApp = convertApp(termNewApp.getParameters()[0]);
					
					pm_func(termOldApp, "distinct");
					
					// Maybe it's the distinctBoolEq-rule
					if (pm_func_weak(termNewApp, "="))
					{
						Term termP1 = termOldApp.getParameters()[0]; // The first Boolean variable
						Term termP2 = termOldApp.getParameters()[1]; // The first Boolean variable
						
						if (termP1.getSort() != smtInterpol.sort("Bool")
								|| termP2.getSort() != smtInterpol.sort("Bool"))
							throw new AssertionError("Error 1 in :distinctBinary_distinctBoolEq");
						
						boolean correctRightSide = false;
						
						// Four cases need to be checked
						if (termNewApp.getParameters()[0].equals(termP1)
								&& termNewApp.getParameters()[1].equals(negate(termP2,smtInterpol)))
							correctRightSide = true;
						
						if (termNewApp.getParameters()[0].equals(termP2)
								&& termNewApp.getParameters()[1].equals(negate(termP1,smtInterpol)))
							correctRightSide = true;
						
						if (termNewApp.getParameters()[1].equals(termP1)
								&& termNewApp.getParameters()[0].equals(negate(termP2,smtInterpol)))
							correctRightSide = true;
						
						if (termNewApp.getParameters()[1].equals(termP2)
								&& termNewApp.getParameters()[0].equals(negate(termP1,smtInterpol)))
							correctRightSide = true;
						
						if (!correctRightSide)
							throw new AssertionError("Error at the end of :distinctBinary_distinctBoolEq");
					}
					else
					{
						pm_func(termNewApp, "not");
						
						// The array which contains the equalities
						Term[] arrayNewEq = null;
						Term[] arrayOldTerm = termOldApp.getParameters(); 
						
					
						if (pm_func_weak(termNewAppInnerApp,"or"))
						{
							arrayNewEq = termNewAppInnerApp.getParameters(); 					 
						} else
						{
							arrayNewEq = termNewApp.getParameters();
						}
						
						boolean[] eqFound = new boolean[arrayNewEq.length];
						
						for (int i = 0; i < eqFound.length; i++)
							eqFound[i] = false;
						
						// Look for each two distinct terms (j > i) if there exists a fitting equality
						for (int i = 0; i < arrayOldTerm.length; i++)
						{
							for (int j = i + 1; j < arrayOldTerm.length; j++)
							{
								boolean found = false;
								for (int k = 0; k < arrayNewEq.length; k++)
								{
									if (!eqFound[k])
									{
										ApplicationTerm termAppTemp = convertApp(arrayNewEq[k]);
										pm_func(termAppTemp, "=");
										
										if(termAppTemp.getParameters()[0] == arrayOldTerm[i]
												&& termAppTemp.getParameters()[1] == arrayOldTerm[j])
										{
											found = true;
											eqFound[k] = true;
										}
										if(termAppTemp.getParameters()[1] == arrayOldTerm[i]
												&& termAppTemp.getParameters()[0] == arrayOldTerm[j])
										{
											found = true;
											eqFound[k] = true;
										}
									}
								}
								
								if (!found)
								{
									throw new AssertionError("Error: Couldn't find the equality that " 
											+ "corresponds to " + arrayOldTerm[i].toStringDirect()
											+ " and " + arrayOldTerm[j].toStringDirect() + ".\n"
											+ "The term was " + term.toStringDirect());
								}
							}
						}
						
						// At last check if each equality is alright
						for (int i = 0; i < eqFound.length; i++)
							if (!eqFound[i])
								throw new AssertionError("Error: Coulnd't associate the equality " 
										+ arrayNewEq[i] + "\n. The term was " + term.toStringDirect());
												
					}
				}
				else if (rewriteRule == ":notSimp")
				{
					/* The first argument of the rewrite has to be the 
					 * double-negated version of the second argument or
					 * "(not true)" iff the second is "false" or
					 * "(not false)" iff the second is "true".
					 */

					
					// Check syntactical correctness
					ApplicationTerm innerAppTermFirstNeg = convertApp(termEqApp.getParameters()[0]);
					pm_func(innerAppTermFirstNeg, "not");
					
					if ((innerAppTermFirstNeg.getParameters()[0] == smtInterpol.term("false") &&
							termEqApp.getParameters()[1] == smtInterpol.term("true"))
						||
						innerAppTermFirstNeg.getParameters()[0] == smtInterpol.term("true") &&
							termEqApp.getParameters()[1] == smtInterpol.term("false"))
					{
						return;
					}
					
					ApplicationTerm innerAppTermSecondNeg = convertApp(innerAppTermFirstNeg.getParameters()[0]);
					pm_func(innerAppTermSecondNeg, "not");
					
					// Check if the rule was executed correctly
					if (innerAppTermSecondNeg.getParameters()[0] != termEqApp.getParameters()[1])
					{
						throw new AssertionError("Error: The rule \"notSimp\" couldn't be verified, because the following "
								+ "two terms aren't the same: " + innerAppTermSecondNeg.getParameters()[0].toString() 
								+ " and " + termEqApp.getParameters()[1].toStringDirect() + ".\n"
								+ "The original term was: " + termApp.toStringDirect());
					}
					// Important: The return is done later, the following is false: 
					// return innerAppTerm.getParameters()[1];
				
				}
				else if (rewriteRule == ":orSimp")
				{
					ApplicationTerm termOldApp = convertApp(termEqApp.getParameters()[0]);
					boolean multidisjunct = true;
					Term termNew = termEqApp.getParameters()[1];
					ApplicationTerm termNewApp = null;

					pm_func(termOldApp,"or");
					
										
					HashSet<Term> oldDisjuncts = new HashSet<Term>();
					HashSet<Term> newDisjuncts = new HashSet<Term>();
					
						
					oldDisjuncts.addAll(Arrays.asList(termOldApp.getParameters()));
					
					oldDisjuncts.remove(smtInterpol.term("false"));
					
					if (oldDisjuncts.size() <= 1)
						multidisjunct = false;
					
					if (multidisjunct)
					{
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
					//newDisjuncts.add(smtInterpol.term("false"));
					
					if(!oldDisjuncts.equals(newDisjuncts))
					{
						newDisjuncts.remove(smtInterpol.term("false"));
						if (!oldDisjuncts.equals(newDisjuncts))
							throw new AssertionError("Error 2 at " + rewriteRule 
									+ ".\n The term was " + termEqApp.toStringDirect());
					}
					// Not nice: I' \subsetneq I isn't checked, but even if I' \supseteq I it's still correct
					// Not nice: The work with false
					
				}
				else if (rewriteRule == ":orTaut")
				{					
					if (!(termEqApp.getParameters()[1] == smtInterpol.term("true")))
					{
						throw new AssertionError("Error: The second argument of a rewrite of the rule "
								+ rewriteRule + " should be true, but it isn't.\n"
								+ "The term was " + termEqApp.toString());
					}
					
					ApplicationTerm termOldApp = convertApp(termEqApp.getParameters()[0]);
					pm_func(termOldApp, "or");
					
					// Case 1: One disjunct is true
					for (Term disjunct : termOldApp.getParameters())
						if (disjunct == smtInterpol.term("true"))
							return;
					
					// Case 2: One disjunct is the negate of another
					for (Term disjunct1 : termOldApp.getParameters())
						for (Term disjunct2 : termOldApp.getParameters())
							if (disjunct1 == negate(disjunct2, smtInterpol))
								return;
					
					throw new AssertionError("Error at the end of rule " + rewriteRule 
							+ "!\n The term was " + term.toStringDirect());						
				}
				else if (rewriteRule == ":iteTrue")
				{									
					ApplicationTerm termOldApp = convertApp(termEqApp.getParameters()[0]);

					pm_func(termOldApp,"ite");
					
					checkNumber(termOldApp.getParameters(),3);
					checkNumber(termEqApp.getParameters(),2);	
					
					//Check syntactical correctness
					if (termOldApp.getParameters()[0] != smtInterpol.term("true"))
						throw new AssertionError("Error 1 at " + rewriteRule);
					
					if (termOldApp.getParameters()[1] != termEqApp.getParameters()[1])
						throw new AssertionError("Error 2 at " + rewriteRule);
				}
				else if (rewriteRule == ":iteFalse")
				{									
					ApplicationTerm termOldApp = convertApp(termEqApp.getParameters()[0]);

					pm_func(termOldApp,"ite");
					
					checkNumber(termOldApp.getParameters(),3);
					checkNumber(termEqApp.getParameters(),2);					
					
					//Check syntactical correctness
					if (termOldApp.getParameters()[0] != smtInterpol.term("false"))
						throw new AssertionError("Error 1 at " + rewriteRule);
					
					if (termOldApp.getParameters()[2] != termEqApp.getParameters()[1])
						throw new AssertionError("Error 2 at " + rewriteRule);
				}
				else if (rewriteRule == ":iteSame")
				{									
					ApplicationTerm termOldApp = convertApp(termEqApp.getParameters()[0]);

					pm_func(termOldApp,"ite");
					
					//Check syntactical correctness					
					if (termOldApp.getParameters()[1] != termEqApp.getParameters()[1])
						throw new AssertionError("Error 2 at " + rewriteRule);
					
					if (termOldApp.getParameters()[2] != termEqApp.getParameters()[1])
						throw new AssertionError("Error 3 at " + rewriteRule);
				}
				else if (rewriteRule == ":iteBool1")
				{									
					ApplicationTerm termOldApp = convertApp(termEqApp.getParameters()[0]);

					pm_func(termOldApp,"ite");
					
					//Check syntactical correctness
					if (termOldApp.getParameters()[0] != termEqApp.getParameters()[1])
						throw new AssertionError("Error 1 at " + rewriteRule);
					
					if (termOldApp.getParameters()[1] != smtInterpol.term("true"))
						throw new AssertionError("Error 2 at " + rewriteRule);
					
					if (termOldApp.getParameters()[2] != smtInterpol.term("false"))
						throw new AssertionError("Error 3 at " + rewriteRule);
				}
				else if (rewriteRule == ":iteBool2")
				{								
					ApplicationTerm termOldApp = convertApp(termEqApp.getParameters()[0]);

					pm_func(termOldApp,"ite");
					
					//Check syntactical correctness
					if (smtInterpol.term("not",termOldApp.getParameters()[0]) 
							!= termEqApp.getParameters()[1])
						throw new AssertionError("Error 1 at " + rewriteRule);
					
					if (termOldApp.getParameters()[1] != smtInterpol.term("false"))
						throw new AssertionError("Error 2 at " + rewriteRule);
					
					if (termOldApp.getParameters()[2] != smtInterpol.term("true"))
						throw new AssertionError("Error 3 at " + rewriteRule);
				}
				else if (rewriteRule == ":iteBool3")
				{									
					ApplicationTerm termOldApp = convertApp(termEqApp.getParameters()[0]);
					ApplicationTerm termNewApp = convertApp(termEqApp.getParameters()[1]);
					
					// Names as in the documentation proof.pdf
					Term t0 = termOldApp.getParameters()[0];
					Term t1 = termOldApp.getParameters()[1];
					Term t2 = termOldApp.getParameters()[2];

					pm_func(termOldApp,"ite");
					pm_func(termNewApp,"or");
					
					//Check syntactical correctness					
					if (t1 != smtInterpol.term("true"))
						throw new AssertionError("Error 2 at " + rewriteRule);

					// or is commutative
					if (termNewApp.getParameters()[0] != t0 && termNewApp.getParameters()[1] != t0)
						throw new AssertionError("Error 4 at " + rewriteRule);
					
					if (termNewApp.getParameters()[0] != t2 && termNewApp.getParameters()[1] != t2)
						throw new AssertionError("Error 5 at " + rewriteRule);					
				}
				else if (rewriteRule == ":iteBool4")
				{									
					ApplicationTerm termOldApp = convertApp(termEqApp.getParameters()[0]);
					checkNumber(termOldApp,3);
					ApplicationTerm termNewApp = convertApp(termEqApp.getParameters()[1]);
					ApplicationTerm termNewAppInnerApp = convertApp(termNewApp.getParameters()[0]);
					checkNumber(termNewAppInnerApp,2);
					
					// Names as in the documentation proof.pdf
					Term t0 = termOldApp.getParameters()[0];
					Term t1 = termOldApp.getParameters()[1];
					Term t2 = termOldApp.getParameters()[2];

					pm_func(termOldApp,"ite");
					pm_func(termNewApp,"not");
					pm_func(termNewAppInnerApp,"or");
					
					//Check syntactical correctness
					if (t1 != smtInterpol.term("false"))
						throw new AssertionError("Error 2 at " + rewriteRule);

					// or is commutative
					if (termNewAppInnerApp.getParameters()[0] != t0 && termNewAppInnerApp.getParameters()[1] != t0)
							throw new AssertionError("Error 4 at " + rewriteRule);
						
					if (termNewAppInnerApp.getParameters()[0] != smtInterpol.term("not",t2)
							&& termNewAppInnerApp.getParameters()[1] != smtInterpol.term("not",t2))
							throw new AssertionError("Error 5 at " + rewriteRule);
									
				}
				else if (rewriteRule == ":iteBool5")
				{								
					ApplicationTerm termOldApp = convertApp(termEqApp.getParameters()[0]);
					ApplicationTerm termNewApp = convertApp(termEqApp.getParameters()[1]);
					
					// Names as in the documentation proof.pdf
					Term t0 = termOldApp.getParameters()[0];
					Term t1 = termOldApp.getParameters()[1];
					Term t2 = termOldApp.getParameters()[2];

					pm_func(termOldApp,"ite");
					pm_func(termNewApp,"or");
					
					//Check syntactical correctness
					if (t2 != smtInterpol.term("true"))
						throw new AssertionError("Error 3 at " + rewriteRule);

					// or is commutative
					if (termNewApp.getParameters()[0] != t1
							&& termNewApp.getParameters()[1] != t1)
							throw new AssertionError("Error 4 at " + rewriteRule);
						
					if (termNewApp.getParameters()[0] != smtInterpol.term("not",t0)
							&& termNewApp.getParameters()[1] != smtInterpol.term("not",t0))
							throw new AssertionError("Error 3 at " + rewriteRule);
					
				}
				else if (rewriteRule == ":iteBool6")
				{			
					ApplicationTerm termOldApp = convertApp(termEqApp.getParameters()[0]);
					ApplicationTerm termNewApp = convertApp(termEqApp.getParameters()[1]);
					ApplicationTerm termNewAppInnerApp = convertApp(termNewApp.getParameters()[0]);
					
					// Names as in the documentation proof.pdf
					Term t0 = termOldApp.getParameters()[0];
					Term t1 = termOldApp.getParameters()[1];
					Term t2 = termOldApp.getParameters()[2];

					pm_func(termOldApp,"ite");
					pm_func(termNewApp,"not");
					pm_func(termNewAppInnerApp,"or");
					
					//Check syntactical correctness
					if (t2 != smtInterpol.term("false"))
						throw new AssertionError("Error 3 at " + rewriteRule);

					// or is commutative
					if (termNewAppInnerApp.getParameters()[0] != smtInterpol.term("not",t0)
							&& termNewAppInnerApp.getParameters()[1] != smtInterpol.term("not",t0))
						throw new AssertionError("Error 4 at " + rewriteRule);
					
					if (termNewAppInnerApp.getParameters()[0] != smtInterpol.term("not",t1)
							&& termNewAppInnerApp.getParameters()[1] != smtInterpol.term("not",t1))
						throw new AssertionError("Error 5 at " + rewriteRule);					
				}
				else if (rewriteRule == ":andToOr")
				{					
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
					
					for (int i = 0; i < termNewAppInnerApp.getParameters().length; i++)
					{
						ApplicationTerm termAppTemp = convertApp(termNewAppInnerApp.getParameters()[i]);
						pm_func(termAppTemp,"not");
						newTermsInner.add(termAppTemp.getParameters()[0]);
					}
					
					if(!oldTerms.equals(newTermsInner))
						throw new AssertionError("Error at rule " + rewriteRule
								+ "!\n The term was " + term.toStringDirect());
				} 
				else if (rewriteRule == ":xorToDistinct")
				{				
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
					
				}
				else if (rewriteRule == ":impToOr")
				{			
					ApplicationTerm termOldApp = convertApp(termEqApp.getParameters()[0]);
					ApplicationTerm termNewApp = convertApp(termEqApp.getParameters()[1]);

					pm_func(termOldApp, "=>");
					pm_func(termNewApp, "or");
					
					// Check if they are the same
					// HashSets are needed to allow permutations
					
					HashSet<Term> oldTerms = new HashSet<Term>();
					HashSet<Term> newTerms = new HashSet<Term>();
					
					for (int i = 0; i < termOldApp.getParameters().length -1; i++)
						oldTerms.add(termOldApp.getParameters()[i]);
					
					Term termImp = termOldApp.getParameters()[termOldApp.getParameters().length-1];
						
					if (termImp != termNewApp.getParameters()[0])
						throw new AssertionError("Error 1 at " + rewriteRule);
					
					for (int i = 1; i < termNewApp.getParameters().length; i++)
					{
						ApplicationTerm termAppTemp = convertApp(termNewApp.getParameters()[i]);
						pm_func(termAppTemp,"not");
						newTerms.add(termAppTemp.getParameters()[0]);
					}
					
					if(!oldTerms.equals(newTerms))
						throw new AssertionError("Error at rule " + rewriteRule	+ "!\n The term was " + term.toStringDirect());
					
					
				} 
				else if (rewriteRule == ":strip")
				{
					//Term which has to be stripped, annotated term
					AnnotatedTerm stripAnnTerm = convertAnn(termEqApp.getParameters()[0]);
					if (stripAnnTerm.getSubterm() != termEqApp.getParameters()[1])
					{
						throw new AssertionError("Error: Couldn't verify a strip-rewrite. Those two terms should be the same but arent"
								+ stripAnnTerm.getSubterm() + "vs. " + termEqApp.getParameters()[1] + ".");
					}
				
				} 
				else if (rewriteRule == ":canonicalSum")
				{
					Term termOld = termEqApp.getParameters()[0];
					Term termNew = termEqApp.getParameters()[1];
					
					if (!calculateTerm(termOld, smtInterpol).equals(
							calculateTerm(termNew, smtInterpol)))
						throw new AssertionError("Error at " + rewriteRule);
				} 
				else if (rewriteRule == ":gtToLeq0" || rewriteRule == ":geqToLeq0"
						|| rewriteRule == ":ltToLeq0" || rewriteRule == ":leqToLeq0")
				{
					ApplicationTerm termNewIneqApp; //the inequality of termAfterRewrite
					
					ApplicationTerm termOldApp = convertApp(termEqApp.getParameters()[0]); //termBeforeRewrite
					ApplicationTerm termNewApp = convertApp(termEqApp.getParameters()[1]);
					
					if (!((rewriteRule == ":gtToLeq0" && pm_func_weak(termOldApp,">"))
							|| (rewriteRule == ":geqToLeq0" && pm_func_weak(termOldApp, ">="))
							|| (rewriteRule == ":ltToLeq0" && pm_func_weak(termOldApp, "<"))
							|| (rewriteRule == ":leqToLeq0" && pm_func_weak(termOldApp, "<="))))
					{
						throw new AssertionError ("Expected not the function symbol "
								+ termOldApp.getFunction().getName() + " for the rule "
								+ rewriteRule + ". \n The term is: " + termEqApp.toString());
					}
					
					Term termT1 = termOldApp.getParameters()[0]; //t_1 and t_2 as in the documentation proof.pdf
					Term termT2 = termOldApp.getParameters()[1];
					
					// The second term may be a negation
					if (rewriteRule == ":ltToLeq0" || rewriteRule == ":gtToLeq0")
					{
						pm_func(termNewApp,"not");
						
						termNewIneqApp = convertApp(termNewApp.getParameters()[0]);
						
					} else
					{
						termNewIneqApp = termNewApp;
					}
					
					pm_func(termNewIneqApp, "<=");
					
					// Warning: Code almost-duplicates (Random number: 29364)
					SMTAffineTerm termAffTemp = calculateTerm(termNewIneqApp.getParameters()[1],smtInterpol);
					isConstant(termAffTemp,Rational.ZERO);
					
					SMTAffineTerm leftside = calculateTerm(termNewIneqApp.getParameters()[0], smtInterpol);

					SMTAffineTerm termT1Aff = calculateTerm(termT1, smtInterpol);
					SMTAffineTerm termT2Aff = calculateTerm(termT2, smtInterpol);
					
					if (rewriteRule == ":gtToLeq0" || rewriteRule == ":leqToLeq0")
					{
						if (!leftside.equals(termT1Aff.add(termT2Aff.negate())))
						{
							throw new AssertionError("Error: Wrong term on the left side of "
									+ "the new inequality. The term was: " + termApp.toStringDirect() + "\n"
									+ "Same should be " + leftside.toStringDirect()
									+ " and " + termT1Aff.add(termT2Aff.negate()).toStringDirect() + "\n"
									+ "Random number: 02653");
						}
						// Then the rule was correctly executed
					} else
					{
						if (!leftside.equals(termT2Aff.add(termT1Aff.negate())))
						{
							throw new AssertionError("Error: Wrong term on the left side of "
									+ "the new inequality. The term was: " + termEqApp.toStringDirect() + "\n"
									+ "Same should be " + leftside.toStringDirect()
									+ " and " + termT2Aff.add(termT1Aff.negate()).toStringDirect() + "\n"
									+ "Random number: 20472");
						}
						// Then the rule was correctly executed
					}				
				
				}
				else if (rewriteRule == ":leqTrue")
				{
					ApplicationTerm termOldApp = convertApp(termEqApp.getParameters()[0]);
					checkNumber(termOldApp,2);

					pm_func(termOldApp,"<=");
										
					SMTAffineTerm constant = calculateTerm(
							convertConst_Neg(termOldApp.getParameters()[0]),smtInterpol);
					
					// Rule-Execution was wrong if c > 0 <=> -c < 0
					if (constant.negate().getConstant().isNegative())
						throw new AssertionError("Error 2 at " + rewriteRule);
					
					SMTAffineTerm termTemp = calculateTerm(termOldApp.getParameters()[1],smtInterpol);
					
					isConstant(termTemp,Rational.ZERO);
					
					if (termEqApp.getParameters()[1] != smtInterpol.term("true"))
						throw new AssertionError("Error 4 at " + rewriteRule);
				}
				else if (rewriteRule == ":leqFalse")
				{
					ApplicationTerm termOldApp = convertApp(termEqApp.getParameters()[0]);

					pm_func(termOldApp,"<=");
										
					SMTAffineTerm constant = calculateTerm(
							convertConst_Neg(termOldApp.getParameters()[0]),smtInterpol);
					
					// Rule-Execution was wrong if c <= 0 <=> c < 0 || c = 0
					if (constant.getConstant().isNegative()
							|| isConstant_weak(constant,Rational.ZERO))
						throw new AssertionError("Error 2 at " + rewriteRule);
					
					SMTAffineTerm termTemp = calculateTerm(termOldApp.getParameters()[1],smtInterpol);
					isConstant(termTemp,Rational.ZERO);
					
					if (termEqApp.getParameters()[1] != smtInterpol.term("false"))
						throw new AssertionError("Error 4 at " + rewriteRule);
				}
				else if (rewriteRule == ":desugar")
				{					
					/* All Int-Parameters of the outermost function
					 * are getting converted into Real-Parameters
					 */
					
					ApplicationTerm termOldApp = convertApp(termEqApp.getParameters()[0]);
					ApplicationTerm termNewApp = convertApp(termEqApp.getParameters()[1]);
					
					// Both must have the same function symbol
					pm_func(termOldApp,termNewApp.getFunction().getName());
					
					if (termOldApp.getParameters().length != termNewApp.getParameters().length)
						throw new AssertionError("Error 1 in :desugar");
					
					for (int i = 0; i < termNewApp.getParameters().length; i++)
					{
						Term paramIOld = termOldApp.getParameters()[i];
						Term paramINew = termNewApp.getParameters()[i];
						if (!paramIOld.equals(paramINew))
						{
							if (!calculateTerm(paramIOld,smtInterpol).isIntegral())
								throw new AssertionError("Error 2 in :desugar");
							
							// Then paramINew has to be either old.0 or (to_real old)
							// Case 1: (to_real old), Case 2: old.0
							boolean correct = false;
							
							if (paramINew instanceof ApplicationTerm)
							{
								// Case 1 and parts of Case 2: (Just handling of the complete Case 1)								
								ApplicationTerm paramINewApp = convertApp(paramINew);
								
								if (pm_func_weak(paramINewApp,"to_real"))								
									if(paramIOld.equals(
											paramINewApp.getParameters()[0]))
										correct = true;
									else
										throw new AssertionError("Error 4 in :desugar");
							}
							
							// Case 2 and parts of Case 1: (Just handling of the complete Case 2)
							if (calculateTerm(paramINew,smtInterpol).getSort() == smtInterpol.sort("Real"))
							{
								// Check for equalitiy, ? and ?.0 have to be equal, therefor .equals doesn't work
								SMTAffineTerm diffZero = calculateTerm(paramINew,smtInterpol).add(
										calculateTerm(paramIOld,smtInterpol).negate());
								if (diffZero.isConstant()
										&& diffZero.getConstant() == Rational.ZERO)
									correct = true;
							}
							
							if (!correct)
								throw new AssertionError("Error 5 in :desugar");							
						}
					}
				}
				else if (rewriteRule == ":divisible")
				{				
					// This rule is a combination of 3-4 sub-rules
										
					// Declaration of the variables which can be declared for all sub-rules + syntactical check 
					ApplicationTerm termOldApp = convertApp(termEqApp.getParameters()[0]);					
					checkNumber(termOldApp,1);
					Term termNew = termEqApp.getParameters()[1];
					
					Term termT = termOldApp.getParameters()[0];
					BigInteger bigIN = termOldApp.getFunction().getIndices()[0]; //bigInteger N
					
					pm_func(termOldApp,"divisible");
					
					if (!termNew.equals(smtInterpol.term("true")) //Old: termNew instanceof ApplicationTerm
							&& !termNew.equals(smtInterpol.term("false"))) 
					{
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
						
						if (termNewAppProd.getParameters()[0] instanceof ConstantTerm)
							if (convertConst(termNewAppProd.getParameters()[0]).getValue().equals(bigIN))
							{
								termNewAppDiv = convertApp(termNewAppProd.getParameters()[1]);
								found = true;
							}
						if (termNewAppProd.getParameters()[1] instanceof ConstantTerm)
							if (convertConst(termNewAppProd.getParameters()[1]).getValue().equals(bigIN))
							{
								termNewAppDiv = convertApp(termNewAppProd.getParameters()[0]);
								found = true;
							}
						
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
					}
					else
					{		
						Rational constT = calculateTerm(convertConst_Neg(termT),smtInterpol).getConstant();
						Rational constN = Rational.valueOf(bigIN,BigInteger.ONE);
						
						if (constT.div(constN).isIntegral())
							if (!termNew.equals(smtInterpol.term("true")))
								throw new AssertionError("Error 6 in divisible");

						if (!constT.div(constN).isIntegral())
							if (!termNew.equals(smtInterpol.term("false")))
								throw new AssertionError("Error 7 in divisible");
								
						// No special treatment of the case n = 1, but it's still correct.
					}
				}
				else if (rewriteRule == ":div1")
				{									
					ApplicationTerm termOldApp = convertApp(termEqApp.getParameters()[0]);

					pm_func(termOldApp,"div");
					
					SMTAffineTerm constant = calculateTerm(
							convertConst_Neg(termOldApp.getParameters()[1]),smtInterpol);
					
					// Rule-Execution was wrong if c != 1
					if (!constant.isConstant())
						throw new AssertionError("Error 1 at " + rewriteRule);					
					if (!(constant.getConstant().equals(Rational.ONE)))
						throw new AssertionError("Error 2 at " + rewriteRule);
					
					if (termEqApp.getParameters()[1] != termOldApp.getParameters()[0])
						throw new AssertionError("Error 3 at " + rewriteRule);
					
				}
				else if (rewriteRule == ":div-1")
				{							
					ApplicationTerm termOldApp = convertApp(termEqApp.getParameters()[0]);

					pm_func(termOldApp,"div");
										
					convertConst_Neg(termOldApp.getParameters()[1]);
					
					SMTAffineTerm constant = calculateTerm(termOldApp.getParameters()[1],smtInterpol);
					
					// Rule-Execution was wrong if c != 1
					if (!constant.negate().isConstant())
						throw new AssertionError("Error 1 at " + rewriteRule);					
					if (!(constant.negate().getConstant().equals(Rational.ONE)))
						throw new AssertionError("Error 2 at " + rewriteRule);
					
					if (!calculateTerm(termEqApp.getParameters()[1],smtInterpol).negate().equals(
							calculateTerm(termOldApp.getParameters()[0],smtInterpol)))
						throw new AssertionError("Error 3 at " + rewriteRule);
				}
				else if (rewriteRule == ":divConst")
				{									
					ApplicationTerm termOldApp = convertApp(termEqApp.getParameters()[0]);

					pm_func(termOldApp,"div");
					
					convertConst_Neg(termOldApp.getParameters()[0]);
					convertConst_Neg(termOldApp.getParameters()[1]);
					
					SMTAffineTerm c1 = calculateTerm(termOldApp.getParameters()[0],smtInterpol);
					SMTAffineTerm c2 = calculateTerm(termOldApp.getParameters()[1],smtInterpol);
					
					SMTAffineTerm d = calculateTerm(termEqApp.getParameters()[1],smtInterpol);
					
					if(!c1.isConstant())
						throw new AssertionError("Error 1 at " + rewriteRule);
					
					if(!c2.isConstant())
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
					
				}
				else if (rewriteRule == ":modulo1")
				{									
					ApplicationTerm termOldApp = convertApp(termEqApp.getParameters()[0]);

					pm_func(termOldApp,"mod");
					
					//Check syntactical correctness
					if(!(termOldApp.getParameters()[0] instanceof ConstantTerm)
							&& !checkInt_weak(termOldApp.getParameters()[0], smtInterpol))
						throw new AssertionError("Error 1 at " + rewriteRule);
					
					convertConst(termOldApp.getParameters()[1]);
					convertConst(termEqApp.getParameters()[1]);
					
					SMTAffineTerm constant1 = calculateTerm(termOldApp.getParameters()[1],smtInterpol);
					SMTAffineTerm constant0 = calculateTerm(termEqApp.getParameters()[1],smtInterpol);						
					
					if (!(constant1.getConstant().equals(Rational.ONE)))
						throw new AssertionError("Error 2 at " + rewriteRule);
					
					if (!(constant0.getConstant().equals(Rational.ZERO)))
						throw new AssertionError("Error 3 at " + rewriteRule);
					
				}
				else if (rewriteRule == ":modulo-1")
				{									
					ApplicationTerm termOldApp = convertApp(termEqApp.getParameters()[0]);

					pm_func(termOldApp,"mod");
					
					//Check syntactical correctness
					if(!(termOldApp.getParameters()[0] instanceof ConstantTerm)
							&& !checkInt_weak(termOldApp.getParameters()[0], smtInterpol))
						throw new AssertionError("Error 1 at " + rewriteRule);
					
					convertConst_Neg(termOldApp.getParameters()[1]);
					convertConst(termEqApp.getParameters()[1]);
					
					SMTAffineTerm constantm1 = calculateTerm(termOldApp.getParameters()[1],smtInterpol);
					SMTAffineTerm constant0 = calculateTerm(termEqApp.getParameters()[1],smtInterpol);						
					
					if (!(constantm1.getConstant().negate().equals(Rational.ONE)))
						throw new AssertionError("Error 2 at " + rewriteRule);
					
					if (!(constant0.getConstant().equals(Rational.ZERO)))
						throw new AssertionError("Error 3 at " + rewriteRule);
					
				}
				else if (rewriteRule == ":moduloConst")
				{
					ApplicationTerm termOldApp = convertApp(termEqApp.getParameters()[0]);

					pm_func(termOldApp,"mod");
					
					//Check syntactical correctness
					if (!(termOldApp.getParameters()[0] instanceof ConstantTerm)
							&& !checkInt_weak(termOldApp.getParameters()[0],smtInterpol))
						throw new AssertionError("Error 1a at " + rewriteRule);
					if (!(termOldApp.getParameters()[1] instanceof ConstantTerm)
							&& !checkInt_weak(termOldApp.getParameters()[1],smtInterpol))
						throw new AssertionError("Error 1b at " + rewriteRule);
					if (!(termEqApp.getParameters()[1] instanceof ConstantTerm)
							&& !checkInt_weak(termEqApp.getParameters()[1],smtInterpol))
						throw new AssertionError("Error 1c at " + rewriteRule);
					
					SMTAffineTerm c1 = calculateTerm(termOldApp.getParameters()[0],smtInterpol);
					SMTAffineTerm c2 = calculateTerm(termOldApp.getParameters()[1],smtInterpol);
					
					SMTAffineTerm d = calculateTerm(termEqApp.getParameters()[1],smtInterpol);
					
					if (c2.getConstant().equals(Rational.ZERO))
						throw new AssertionError("Error 2 at " + rewriteRule);
					
					if (!c1.isIntegral() || !c2.isIntegral() || !d.isIntegral())
						throw new AssertionError("Error 3 at " + rewriteRule);
					
					if (c2.getConstant().isNegative())
					{
						// d = c1 + c2 * ceil(c1/c2)
						if (!d.equals(c1.add(
								c2.mul(c1.div(c2.getConstant()).getConstant().ceil()).negate()
								)))
							throw new AssertionError("Error 4 at " + rewriteRule);
					} else
					{
						if (!d.equals(c1.add(
								c2.mul(c1.div(c2.getConstant()).getConstant().floor()).negate()
								)))
							throw new AssertionError("Error 5 at " + rewriteRule);
					}
				}
				else if (rewriteRule == ":modulo")
				{		
					
					ApplicationTerm termOldMod = convertApp(termEqApp.getParameters()[0]);
					Term termOldX = termOldMod.getParameters()[0];
					Term termOldY = termOldMod.getParameters()[1];										
					ApplicationTerm termNewSum = convertApp(termEqApp.getParameters()[1]);
					
					ApplicationTerm termNewProd;					
					Term termNewNotProd;
					if (termNewSum.getParameters()[0] instanceof ApplicationTerm)
					{
						if (pm_func_weak(termNewSum.getParameters()[0],"*"))
						{
							termNewProd = convertApp(termNewSum.getParameters()[0]);
							termNewNotProd = termNewSum.getParameters()[1];
						} else
						{
							termNewProd = convertApp(termNewSum.getParameters()[1]);
							termNewNotProd = termNewSum.getParameters()[0];
						}
					} else
					{
						termNewProd = convertApp(termNewSum.getParameters()[1]);
						termNewNotProd = termNewSum.getParameters()[0];
					}
					
					ApplicationTerm termNewDiv;
					Term termNewNotDiv;
					if (termNewProd.getParameters()[0] instanceof ApplicationTerm)
					{
						if (pm_func_weak(termNewProd.getParameters()[0],"/")
								|| pm_func_weak(termNewProd.getParameters()[0],"div"))
						{
							termNewDiv = convertApp(termNewProd.getParameters()[0]);
							termNewNotDiv = termNewProd.getParameters()[1];
						} else
						{
							termNewDiv = convertApp(termNewProd.getParameters()[1]);
							termNewNotDiv = termNewProd.getParameters()[0];
						}
					} else
					{
						termNewDiv = convertApp(termNewProd.getParameters()[1]);
						termNewNotDiv = termNewProd.getParameters()[0];
					}
					
					//ApplicationTerm termNewDiv = convertApp(termNewProd.getParameters()[1]);
					
					pm_func(termOldMod,"mod");
					pm_func(termNewSum,"+");
					pm_func(termNewProd,"*");
					if (!pm_func_weak(termNewDiv,"div")
							&& !pm_func_weak(termNewDiv,"/"))
						throw new AssertionError("Error 1 at " + rewriteRule);
					
					if (termNewNotProd != termOldX
							|| !calculateTerm(termNewNotDiv,smtInterpol).equals(
									calculateTerm(termOldY,smtInterpol).negate())
							|| termNewDiv.getParameters()[0] != termOldX
							|| termNewDiv.getParameters()[1] != termOldY)
						throw new AssertionError("Error 2 at " + rewriteRule);
					
				}
				else if (rewriteRule == ":toInt")
				{					
					ApplicationTerm termOldApp = convertApp(termEqApp.getParameters()[0]);
					
					pm_func(termOldApp,"to_int");
					
					// r and v as in the documentation proof.pdf
					Term termV = convertConst_Neg(termEqApp.getParameters()[1]);
					Term termR = termOldApp.getParameters()[0];
					// r can be a positive/negative fraction
					// Case A: Positive Integer, Case B: Negative Integer
					// Case C: Positive Fraction, Case D: Negative Fraction
					
					if (termR instanceof ApplicationTerm) 
					{
						// Case B, C, D:
						ApplicationTerm termRApp = convertApp(termR);
						ApplicationTerm termRInnerApp;
						if (pm_func_weak(termRApp,"-") 
								&& termRApp.getParameters()[0] instanceof ApplicationTerm)
						{
							// Case D:
							termRInnerApp = convertApp(termRApp.getParameters()[0]);
							pm_func(termRInnerApp,"/");
							checkNumber(termRInnerApp,2);
							
							convertConst_Neg(termRInnerApp.getParameters()[0]); // Presumably the neg isn't needed
							convertConst_Neg(termRInnerApp.getParameters()[1]); // Presumably the neg isn't needed
						} else if (pm_func_weak(termRApp,"/"))
						{
							// Case C:
							pm_func(termRApp,"/");
							checkNumber(termRApp,2);
							
							convertConst_Neg(termRApp.getParameters()[0]); // Presumably the neg isn't needed
							convertConst_Neg(termRApp.getParameters()[1]); // Presumably the neg isn't needed
						} else
						{
							// Case B:
							pm_func(termRApp,"-");
							
							convertConst(termRApp.getParameters()[0]);
						}	
					} else
					{
						// Case A:
						convertConst(termR);
					}
					
					if (!calculateTerm(termR,smtInterpol).getConstant().floor().equals( 
							calculateTerm(termV,smtInterpol).getConstant())) 	
						throw new AssertionError("Error 2 at " + rewriteRule);
					
					/* Not nice: Not checked, if v is an integer and
					 * r a real, but it is still correct.
					 */
				}
				else if (rewriteRule == ":toReal")
				{
					ApplicationTerm termOldApp = convertApp(termEqApp.getParameters()[0]);
					
					pm_func(termOldApp,"to_real");
										
					Term termOldC = convertConst_Neg(termOldApp.getParameters()[0]);
					Term termNewC = convertConst_Neg(termEqApp.getParameters()[1]);
					
					if (!calculateTerm(termOldC,smtInterpol).getConstant().equals( 
							calculateTerm(termNewC,smtInterpol).getConstant()))						
						throw new AssertionError("Error 2 at " + rewriteRule);
					
					/* Not nice: Not checked, if cOld is an integer and
					 * cNew a real, but it is still correct.
					 */
				}
				else if (rewriteRule == ":storeOverStore")
				{
					System.out.println("\n \n \n Now finally tested: " + rewriteRule);	 //TODO					
					
					checkNumber(termEqApp.getParameters(),2);
					ApplicationTerm termOldApp = convertApp(termEqApp.getParameters()[0]);
					ApplicationTerm termNewApp = convertApp(termEqApp.getParameters()[1]);
					ApplicationTerm termOldAppInnerApp = convertApp(termOldApp.getParameters()[0]);
					
					checkNumber(termOldApp.getParameters(),3);
					checkNumber(termOldAppInnerApp.getParameters(),3);
					checkNumber(termNewApp.getParameters(),3);
					
					pm_func(termOldApp,"store");
					pm_func(termOldAppInnerApp,"store");
					pm_func(termNewApp,"store");
					
					if (termOldApp.getParameters()[1] != termOldAppInnerApp.getParameters()[1]
							|| termOldApp.getParameters()[1] != termNewApp.getParameters()[1])						
						throw new AssertionError("Error 1 at " + rewriteRule);
					
					if (termOldApp.getParameters()[2] != 
							termNewApp.getParameters()[2])						
						throw new AssertionError("Error 2 at " + rewriteRule);
					
					if (termOldAppInnerApp.getParameters()[0] != 
							termNewApp.getParameters()[0])						
						throw new AssertionError("Error 3 at " + rewriteRule);
					
					/* Not nice: Not checked, if i is an integer, but
					 * it is still correct.
					 */
				}
				else if (rewriteRule == ":selectOverStore")
				{
					System.out.println("\n \n \n Now finally tested: " + rewriteRule);	 //TODO					
					
					checkNumber(termEqApp.getParameters(),2);
					ApplicationTerm termOldApp = convertApp(termEqApp.getParameters()[0]);
					Term termNew = termEqApp.getParameters()[1];
					ApplicationTerm termOldAppInnerApp = convertApp(termOldApp.getParameters()[0]);
					
					checkNumber(termOldApp.getParameters(),2);
					checkNumber(termOldAppInnerApp.getParameters(),3);
					
					pm_func(termOldApp,"select");
					pm_func(termOldAppInnerApp,"store");
					
					if (termOldApp.getParameters()[1] == termOldAppInnerApp.getParameters()[1])
					{
						if (termOldAppInnerApp.getParameters()[2] != termNew)						
							throw new AssertionError("Error 2 at " + rewriteRule);						
					} else
					{
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
				}
				else if (rewriteRule == ":storeRewrite")
				{
					System.out.println("\n \n \n Now finally tested: " + rewriteRule);	 //TODO					
					
					checkNumber(termEqApp.getParameters(),2);
					ApplicationTerm termOldApp = convertApp(termEqApp.getParameters()[0]);
					ApplicationTerm termNewApp = convertApp(termEqApp.getParameters()[1]);
					checkNumber(termNewApp.getParameters(),2);
					ApplicationTerm termNewAppInnerApp = convertApp(termNewApp.getParameters()[0]);
					ApplicationTerm termOldAppInnerApp = null;
					checkNumber(termNewAppInnerApp.getParameters(),2);
					
					Term termA = termNewAppInnerApp.getParameters()[0];
					Term termI = termNewAppInnerApp.getParameters()[1];					
					Term termV = termNewApp.getParameters()[1];

					checkNumber(termOldApp.getParameters(), 2);
					
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
				}
				else if (rewriteRule == ":expand")
				{
					Term termOld = termEqApp.getParameters()[0];
					Term termNew = termEqApp.getParameters()[1];
					
					if (!calculateTerm(termOld,smtInterpol).equals(
							calculateTerm(termNew,smtInterpol)))
						throw new AssertionError("Error in " + rewriteRule);
				}
				else if (rewriteRule == ":flatten")
				{
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
					
					while (disjuncts.size() > 0)
					{
						Term currentDisjunct = disjuncts.get(disjuncts.size()-1);
						disjuncts.remove(currentDisjunct);
						
						boolean currentIsDisjunction = false;
						
						if (currentDisjunct instanceof ApplicationTerm)
							currentIsDisjunction = pm_func_weak(currentDisjunct, "or");
						
						if (currentIsDisjunction)
						{
							ApplicationTerm currentDisjunctApp = convertApp(currentDisjunct);
							disjuncts.addAll(Arrays.asList(currentDisjunctApp.getParameters()));
						} else
						{
							oldDisjuncts.add(currentDisjunct);
						}								
					}		
					
					newDisjuncts.addAll(Arrays.asList(termNewApp.getParameters()));
					
					if (!oldDisjuncts.equals(newDisjuncts))
						throw new AssertionError("Error in the rule " + rewriteRule + "!\n The term was " + term.toStringDirect());					
				
				} else
				{
					System.out.println("Can't handle the following rule " + termAppInnerAnn.getAnnotations()[0].getKey() + ", therefore...");
					System.out.println("...believed as alright to be rewritten: " + termApp.getParameters()[0].toStringDirect() + " .");
				}				
			
				// The second part, cut the @rewrite and the annotation out, both aren't needed for the @eq-function.
				// stackPush(innerAnnTerm.getSubterm(), term);
				return;
				
			case "@intern":
				
				// Step 1: The syntactical check				
				
				termEqApp = convertApp(termApp.getParameters()[0]);
				
				pm_func(termEqApp,"=");
				
				// Step 1,5: Maybe the internal rewrite is just an addition of :quoted
				if (convertApp_hard(termEqApp.getParameters()[0]) ==
						convertApp_hard(termEqApp.getParameters()[1]))
					return;
				// Not nice: Not checked if the annotation really is quoted, but otherwise
				// it's still correct.
				
				/* Step 1,75: Maybe the first term is a negation of a Term t and 
				 * the second is the negation of (! t :quoted) 
				 */
				
				if (termEqApp.getParameters()[0] instanceof ApplicationTerm
						&& termEqApp.getParameters()[1] instanceof ApplicationTerm)
				{
					ApplicationTerm termLeftApp = convertApp(termEqApp.getParameters()[0]); // Term on the left side of the rewrite-"="
					ApplicationTerm termRightApp = convertApp(termEqApp.getParameters()[1]);
					
					if (pm_func_weak(termLeftApp,"not") 
							&& pm_func_weak(termRightApp,"not"))
						if (termRightApp.getParameters()[0] instanceof AnnotatedTerm)
						{
							AnnotatedTerm termRightAppInnerAnn = convertAnn(termRightApp.getParameters()[0]);
							if (termLeftApp.getParameters()[0].equals(
									termRightAppInnerAnn.getSubterm()))
								return;
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
								
				/* Step 4: Get the terms which have to be compared
				 * For this, the (in)equality-term has to be transformed,
				 * depending on the relation-symbol
				 */
								
				if (pm_func_weak(termOldRel,"="))
				{
					// Case 4.1: It's an equality
					if ((firstNeg && !secondNeg)		||		(!firstNeg && secondNeg))
						throw new AssertionError("Error 4.1.1 in " + functionname);
					
					// term_compare = Left Side - Right Side
					SMTAffineTerm termOldCompAff =
							calculateTerm(termOldRel.getParameters()[0],smtInterpol).add(
									calculateTerm(termOldRel.getParameters()[1],smtInterpol).negate());

					SMTAffineTerm termNewCompAff =
							calculateTerm(termNewRel.getParameters()[0],smtInterpol).add(
									calculateTerm(termNewRel.getParameters()[1],smtInterpol).negate());
					
					// Precheck for better runtime - Warning: Code duplicates start here - a random number: 589354
					if (termOldCompAff.equals(termNewCompAff))
						return;
					
					// Check for a multiplication with a rational
					Rational constOld = termOldCompAff.getConstant();
					Rational constNew = termNewCompAff.getConstant();
					
					if (constOld.equals(Rational.ZERO) && constNew.equals(Rational.ZERO))
					{
						// Find the multiplication in a cofactor
						Rational oldGcd = termOldCompAff.getGcd();
						Rational newGcd = termNewCompAff.getGcd();
												
						if (termOldCompAff.mul(newGcd).equals(termNewCompAff)
								|| termNewCompAff.mul(oldGcd).equals(termOldCompAff)) // Note: == doesn't work
							return;
						
						if (termOldCompAff.equals(termNewCompAff.negate())) // Last try
							return;
						System.out.println("Sadly1, I couldn't find a factorial constant in the internal rewrite: "
								+ termApp.getParameters()[0].toStringDirect() + " .");
						return;
					}
										
					if (constOld.equals(Rational.ZERO) || constNew.equals(Rational.ZERO))
						throw new AssertionError("Error 4.1.2 in " + functionname);
					
					// Calculate the factors
					Rational constGcd = constOld.gcd(constNew); // greatest common divisor
					Rational constLcm = constOld.mul(constNew).div(constGcd); // least common multiple
					Rational constOldFactor = constLcm.div(constOld);
					Rational constNewFactor = constLcm.div(constNew);
					
					termOldCompAff = termOldCompAff.mul(constOldFactor);
					termNewCompAff = termNewCompAff.mul(constNewFactor);
					
					if (termOldCompAff.equals(termNewCompAff))
						return;
					
					System.out.println("Sadly1, I couldn't understand the internal rewrite: "
							+ termApp.getParameters()[0].toStringDirect() + " .");
					// Warning: Code duplicates end here - a random number: 589354
				} else
				{
					// Case 4.2: Then both have to be brought to either ... < 0 or ... <= 0
					ApplicationTerm termOldComp = uniformizeInEquality(convertApp_hard(termEqApp.getParameters()[0]), smtInterpol);
					ApplicationTerm termNewComp = uniformizeInEquality(convertApp_hard(termEqApp.getParameters()[1]), smtInterpol);
					
					if (termOldComp.getFunction().getName() != termNewComp.getFunction().getName())
						throw new AssertionError("Error 4.2.2 in " + functionname);
					
					if (!pm_func_weak(termOldComp,"<=") && !pm_func_weak(termOldComp,"<"))
						throw new AssertionError("Error 4.2.3 in " + functionname);
										
					if (!pm_func_weak(termNewComp,"<=") && !pm_func_weak(termNewComp,"<"))
						throw new AssertionError("Error 4.2.4 in " + functionname);
					
					// Just the left side of the inequality
					SMTAffineTerm termOldCompAff = calculateTerm(termOldComp.getParameters()[0],smtInterpol);
					SMTAffineTerm termNewCompAff = calculateTerm(termNewComp.getParameters()[0],smtInterpol);
					
					// Precheck for better runtime - Warning: Code duplicates start here - a random number: 589354
					if (termOldCompAff.equals(termNewCompAff))
						return;
					
					// Check for a multiplication with a rational
					Rational constOld = termOldCompAff.getConstant();
					Rational constNew = termNewCompAff.getConstant();
					
					if (constOld.equals(Rational.ZERO) && constNew.equals(Rational.ZERO))
					{
						// Find the multiplication in a cofactor
						Rational oldGcd = termOldCompAff.getGcd();
						Rational newGcd = termNewCompAff.getGcd();
												
						if (termOldCompAff.mul(newGcd).equals(termNewCompAff)
								|| termNewCompAff.mul(oldGcd).equals(termOldCompAff)) // Note: == doesn't work
							return;
						
						System.out.println("Sadly2, I couldn't find a factorial constant in the internal rewrite: "
								+ termApp.getParameters()[0].toStringDirect() + " .");
						return;
					}
					
					if (constOld.equals(Rational.ZERO) || constNew.equals(Rational.ZERO))
						throw new AssertionError("Error 4.2.5 in " + functionname);
					
					// Calculate the factors
					Rational constGcd = constOld.gcd(constNew); // greatest common divisor
					Rational constLcm = constOld.mul(constNew).div(constGcd); // least common multiple
					Rational constOldFactor = constLcm.div(constOld);
					Rational constNewFactor = constLcm.div(constNew);
					
					termOldCompAff = termOldCompAff.mul(constOldFactor);
					termNewCompAff = termNewCompAff.mul(constNewFactor);
					
					if (termOldCompAff.equals(termNewCompAff))
						return;
					
					System.out.println("Sadly2, I couldn't understand the internal rewrite: "
							+ termApp.getParameters()[0].toStringDirect() + " .");
					// Warning: Code duplicates end here - a random number: 589354
				}
				
				System.out.println("Sadly, I had to believe the following internal rewrite: "
						+ termApp.getParameters()[0].toStringDirect() + " .");
				return;
				
			case "@split":
				
				if (termApp.getParameters().length < 2)
					throw new AssertionError("Error at @split");
				
				stackWalker.push(new WalkerId<Term,String>(term, "split"));
				stackWalker.push(new WalkerId<Term,String>(termApp.getParameters()[0], ""));								
				
				return;
				
			case "@clause":
				
				if (termApp.getParameters().length != 2)
				{
					throw new AssertionError("Error: The clause term has not 2 parameters, it has " 
							+ termApp.getParameters().length + ". The term is " + termApp.toString());
				}

				stackWalker.push(new WalkerId<Term,String>(term, "clause"));
				stackWalker.push(new WalkerId<Term,String>(termApp.getParameters()[1], ""));
				stackWalker.push(new WalkerId<Term,String>(termApp.getParameters()[0], ""));
				return;				
				
			default:
				if (!(functionname.startsWith("@")))
				{
					// The Proof-Checker is so deep, that there is nothing more to unfold
					stackPush(term, term);
				} else
				{
					throw new AssertionError("Error: The Proof-Checker has no routine for the function " + functionname + "."
							+ "The error-causing term is " + termApp);
				}
			}
			
		} else if (term instanceof AnnotatedTerm) {
			
			/* Don't do anything to the annotation, but look at the subterm */
			
			annTerm = (AnnotatedTerm) term;
			
			stackWalker.push(new WalkerId<Term,String>(term,"annot"));
			stackWalker.push(new WalkerId<Term,String>(annTerm.getSubterm(),""));
			stackAnnots.push(annTerm.getAnnotations());
		} else { 
			throw new AssertionError("Error: The Proof-Checker has no routine for the class " + term.getClass() + ".");
		}
	
	}
	
	//Special Walker
	public void walkSpecial(Term term, String type, SMTInterpol smtInterpol)
	{
		// term is just the first term
		
		ApplicationTerm termApp = null; //The first term casted to an ApplicationTerm
		Term[] termArgs = null; //The parameters/arguments of the first term
		if (term instanceof ApplicationTerm)
		{
			termApp = (ApplicationTerm) term;
			termArgs = termApp.getParameters();
		}
		
		switch (type)
		{		
		case "calcParams":
			throw new AssertionError("Error: The case \"calcParams\" is old and shouldn't be reached anymore.");
			
		case "res":
			
			// If one of the non-first parameter is a real disjunction, i.e. a disjunction with
			// at least 2 disjuncts, the non-pivot-disjunct(s) need to be added to the first parameter.
			// disjunctsAdd is the list which memorizes those disjuncts, so they can be added later.
			HashSet<Term> allDisjuncts = new HashSet<Term>();
			
			/* Get the arguments and pivots */
			Term[] pivots = new Term[termArgs.length]; //The zeroth entry has no meaning.
			AnnotatedTerm termArgsIAnn; // The ith argument of the first term, as an annotated term

			/* get pivot: start */
			for (int i = 1; i < termArgs.length; i++) //The 0th argument get's resoluted and has therefor no pivot.
			{
				if (termArgs[i] instanceof AnnotatedTerm)
				{										
					termArgsIAnn = (AnnotatedTerm) termArgs[i];
					
					/* Check if it is a pivot-annotation */
					if (termArgsIAnn.getAnnotations()[0].getKey() != ":pivot")
					{
						throw new AssertionError("Error: The annotation has key " 
								+ termArgsIAnn.getAnnotations()[0].getKey() + " instead of :pivot, " 
								+ "which is required. It's value is: " + termArgsIAnn.getAnnotations()[0].getValue());
					}						
											
					/* Just take the first annotation, because 
					 * it should have exactly one - otherwise 
					 * the proof-checker throws an error */
					if (termArgsIAnn.getAnnotations()[0].getValue() instanceof Term)
					{							
						pivots[i] = (Term) termArgsIAnn.getAnnotations()[0].getValue();
					} else
					{
						throw new AssertionError("Error: The following object was supposed to be a known term but isn't: " 
								+ termArgsIAnn.getAnnotations()[0].getValue().toString() + "It is:" 
								+ termArgsIAnn.getAnnotations()[0].getValue().getClass().getCanonicalName());
					}
					
					if (termArgsIAnn.getAnnotations().length > 1)
					{
						throw new AssertionError("Error: Expected number of annotations was 1, instead it is " + termArgsIAnn.getAnnotations().length + " in this term " + termArgsIAnn);
					}
				} else
				{
					throw new AssertionError("Error: Expected an annotated term as parameter No." + i + ">0 of a "
							+ "resolution term");
				}
			}
			/* get pivot: end */
			
			/* Check if the pivots are really in the second argument */
			
			//The arguments of the first term after the calculation
			Term[] termArgsCalc = new Term[termArgs.length];
			//The arguments of the first term after the calculation as AnnotatedTerms
			AnnotatedTerm[] termArgsCalcAnn = new AnnotatedTerm[termArgsCalc.length];
			
			
			for (int i = termArgsCalc.length - 1; i >= 0; i--)
			{
				if (!stackResults.isEmpty())
				{
					termArgsCalc[i] = stackPop(type);
				} else
				{
					throw new AssertionError("Error: The Resolution needs results, but there are not enough.");
				}
				
				/* termArgsCalc still includes the pivot-annotation. */
				if (i != 0)
				{
					if (termArgsCalc[i] instanceof AnnotatedTerm)
					{
						termArgsCalcAnn[i] = (AnnotatedTerm) termArgsCalc[i];
					} else	{
						throw new AssertionError("Error: This code really shouldn't be reachable! A random number: 23742");
					}					
				}
			}
			
			// Declaration done, now for the real search			

			// Now get the disjuncts of the first argument into the hash set
			
			// The first argument calculated and as an ApplicationTerm
			// this is just needed if argument 0 has more than one disjunct.
			ApplicationTerm termArg0CalcApp = null; //Not nice, but it will just be needed when multiDisjunct holds and then it is initialized properly
			// true iff. argument 0 has more than one disjunct
			boolean multiDisjunct = false; 
			
			if (termArgsCalc[0] instanceof ApplicationTerm)
			{
				termArg0CalcApp = (ApplicationTerm) termArgsCalc[0]; //First Term: The one which gets resoluted
				
				/* Does the clause have one or more disjuncts? */
				/* Assumption: If there is just one clause it doesn't start with an "or" */
				if (termArg0CalcApp.getFunction().getName() == "or")
				{
					multiDisjunct = true;
				}
			}
			
			/* Initialization of the disjunct(s) */			
			if (multiDisjunct)
			{
				// Its disjuncts (Works just if the clause has more than one disjunct)
				allDisjuncts.addAll(Arrays.asList(termArg0CalcApp.getParameters()));
			} else {
				allDisjuncts.add(termArgsCalc[0]);
			}
			
			
			for (int i = 1; i < termArgs.length; i++)
			{
				// Remove the negated pivot from allDisjuncts
				
				if (! allDisjuncts.remove(negate(pivots[i], smtInterpol))) {
					throw new AssertionError("Error: couldn't find the negated pivot "+ pivots[i].toStringDirect() 
							+ " in the intermediate disjunction " +  allDisjuncts.toString());
					
				}

				/* The search for the pivot in the term with the pivot: */
				if (termArgsCalcAnn[i].getSubterm() == pivots[i])
				{
					// The Pivot-term has one disjunct
				} else if (termArgsCalcAnn[i].getSubterm() instanceof ApplicationTerm)
				{
					// The pivot term has more than one disjunct

					// Of the ith argument of the resolution, the subterm as an ApplicationTerm
					ApplicationTerm termArgsCalcAnnISubtApp = (ApplicationTerm) termArgsCalcAnn[i].getSubterm();
					 
					if (termArgsCalcAnnISubtApp.getFunction().getName() != "or")
					{
						throw new AssertionError("Error: Hoped for a disjunction while searching the pivot " 
								+ pivots[i] + " in " + termArgsCalc[i].toStringDirect() + ". But found "
								 + "a function with that symbol: " + termArgsCalcAnnISubtApp.getFunction().getName());
					} 
					
					// For each disjunct we have to check if it's the pivot, if not it has to be added later.
					boolean pivotFound = false;
					for (int j = 0; j < termArgsCalcAnnISubtApp.getParameters().length; j++)
					{
						if (termArgsCalcAnnISubtApp.getParameters()[j] != pivots[i])
						{
							allDisjuncts.add(termArgsCalcAnnISubtApp.getParameters()[j]);
						} else
						{
							pivotFound = true;
						}
					}
					
					if (!pivotFound)
					{
						throw new AssertionError("Error: couldn't find the pivot "+ pivots[i].toStringDirect() 
								+ " in the disjunction " +  termArgsCalcAnnISubtApp.toStringDirect());
					}					
				} else 
				{
					throw new AssertionError("Error: Could NOT find the pivot " + pivots[i] + " in " 
							+ termArgsCalc[i].toStringDirect() + " finden. Before the calculation the term was "
							+ termArgs[i].toStringDirect());
				}
			}
			
			
			/* Different handling for a different number of conjuncts is needed */
			switch (allDisjuncts.size())
			{
			case 0:	
				stackPush(smtInterpol.term("false"), term);
				return;
			case 1:;
				stackPush(allDisjuncts.iterator().next(), term);
				return;
			default:				
				//Build an array that contains only the disjuncts, that have to be returned
				Term[] disjunctsReturn = allDisjuncts.toArray(new Term[allDisjuncts.size()]);

				stackPush(smtInterpol.term("or", disjunctsReturn), term);
				return;
			}
			
			
		case "eq":
			/* Expected: The first argument is unary each other argument binary.
			 * Each not-first argument describes a rewrite of a (sub)term of the first term.
			 * Important is the order, e.g. the rewrite of the second argument has to be executed
			 * before the rewrite of the third argument! 
			 */

			ApplicationTerm[] termAppParamsApp = new ApplicationTerm[termArgs.length]; //Parameters of @eq, uncalculated, application terms
			Term termEdit; //Term which will be edited end ends in the result
			// The i-th parameter of the first term as AnnotatedTerm, which is
			// just needed for @rewrite, i.e. just not for @intern.
			AnnotatedTerm termAppParamsAppIAnn;
			/* The i-th Parameter of the first term, as ...
			 *  - @intern: ApplicationTerm
			 *  - @rewrite: Subterm of the AnnotatedTerm which is an ApplicationTerm
			 *  ["May" stands for Maybe]
			 */
			ApplicationTerm termAppParamsAppIMayAnnApp;
			// Initialization
			for (int i = 0; i < termArgs.length; i++)
			{
				termAppParamsApp[i] = convertApp(termArgs[i]);
				
				// OLD and WRONG: Check, if the params are correct for themselves
				// This was already done, and at this points leads to chaos on the resultStack
				// stackWalker.push(new WalkerId<Term,String>(termAppParamsApp[i],""));
				
			}

			termEdit = stackPop(type); //termAppParamsApp[0];
			
			// Editing the term
			for (int i = 1; i < termArgs.length; i++)
			{				
				if (pm_func_weak(termAppParamsApp[i],"@rewrite"))
				{					
					termAppParamsAppIAnn = convertAnn(termAppParamsApp[i].getParameters()[0]);
					termAppParamsAppIMayAnnApp = convertApp(termAppParamsAppIAnn.getSubterm());
				} 
				else if (pm_func_weak(termAppParamsApp[i],"@intern"))
				{
					termAppParamsAppIMayAnnApp = convertApp(termAppParamsApp[i].getParameters()[0]);
				} 
				else
				{
					throw new AssertionError("Error: An argument of @eq was neither a @rewrite nor " 
							+ "a @intern, it was: " + termAppParamsApp[i].getFunction().getName() + ".");
				}

				pm_func(termAppParamsAppIMayAnnApp, "=");
				
				// Not nice: Can it be, that one has to calculate termDelete or termInsert first?
				termEdit = rewriteTerm(termEdit, termAppParamsAppIMayAnnApp.getParameters()[0], termAppParamsAppIMayAnnApp.getParameters()[1]);
			}
			
			stackPush(termEdit, term);			
			return;			
			
			
		case "clause":

			/* Check if the parameters of clause are two disjunctions (which they should be) */
					
			Term termAppParam1Calc = null;
			Term termAppParam2Calc = null;
			
			//The first Parameter of clause, which is a disjunction, just
			//needed if there is more than one disjunct.
			ApplicationTerm termAppParam1CalcApp = null;
			ApplicationTerm termAppParam2CalcApp = null;
			
			// The disjuncts of each parameter
			HashSet<Term> param1Disjuncts = new HashSet<Term>();
			HashSet<Term> param2Disjuncts = new HashSet<Term>();
			
			// Important: It's correct, that at first the second parameter is read and then the first.
			if (!stackResults.isEmpty())
			{
				termAppParam2Calc = stackPop(type);
			} else
			{
				throw new AssertionError("Error: Clause2 needs a result, but there is none.");
			}
			
			if (!stackResults.isEmpty())
			{
				termAppParam1Calc = stackPop(type);
			} else
			{
				throw new AssertionError("Error: Clause1 needs a result, but there is none.");
			}
			
			boolean multiDisjunct1 = false; // true iff parameter 1 has more than one disjunct
			boolean multiDisjunct2 = false; // true iff parameter 2 has more than one disjunct
			
			if (termAppParam1Calc instanceof ApplicationTerm)				
			{	
				termAppParam1CalcApp = (ApplicationTerm) termAppParam1Calc;
				if (termAppParam1CalcApp.getFunction().getName() == "or")
				{
					multiDisjunct1 = true;				
				}
			}

			if (termAppParam2Calc instanceof ApplicationTerm)				
			{	
				termAppParam2CalcApp = (ApplicationTerm) termAppParam2Calc;
				if (termAppParam2CalcApp.getFunction().getName() == "or")
				{
					multiDisjunct2 = true;					
				}
			} 		
			
			// Initialize the disjuncts			 			
			
			if (multiDisjunct1)
			{
				param1Disjuncts.addAll(Arrays.asList(termAppParam1CalcApp.getParameters()));
			} else
			{
				if (termAppParam1Calc != smtInterpol.term("false"))
						param1Disjuncts.add(termAppParam1Calc);
			}
			
			if (multiDisjunct2)
			{
				param2Disjuncts.addAll(Arrays.asList(termAppParam2CalcApp.getParameters()));
			} else
			{
				if (termAppParam2Calc != smtInterpol.term("false"))
					param2Disjuncts.add(termAppParam2Calc);
			}
			

			/* Check if the clause operation was correct. Each later disjunct has to be in 
			 * the first disjunction and reverse.
			 */
			
			if (!param1Disjuncts.equals(param2Disjuncts))
			{
				throw new AssertionError("Error: The clause-operation didn't permutate correctly!");
			}
											
			stackPush(termAppParam2Calc, term);
			return;
		
		
			
		case "split":
			/* Read the rule and handle each differently */
			AnnotatedTerm termAppSplitInnerAnn = convertAnn(termApp.getParameters()[0]);
			ApplicationTerm termSplitReturnApp = convertApp(termApp.getParameters()[1]);
			ApplicationTerm termOldCalcApp = convertApp(convertAnn(stackPop("split")).getSubterm());
			Term termSplitReturnInner = termSplitReturnApp.getParameters()[0];
									
			String splitRule = termAppSplitInnerAnn.getAnnotations()[0].getKey();
						
			if (debug.contains("currently"))
				System.out.println("Split-Rule: " + splitRule);
			if (debug.contains("hardTerm"))
				System.out.println("Term: " + term.toStringDirect());
			
			if (false)
			{} else if (splitRule == ":notOr")
			{
				pm_func(termSplitReturnApp,"not");
				pm_func(termOldCalcApp, "not");
				ApplicationTerm termOldCalcAppInnerApp = convertApp(termOldCalcApp.getParameters()[0]);
				pm_func(termOldCalcAppInnerApp, "or");				
				
				
				for (Term disjunct : termOldCalcAppInnerApp.getParameters())
				{
					if (disjunct == termSplitReturnInner)
					{
						stackPush(termApp.getParameters()[1], term);
						return;
					}					
				}
				
				throw new AssertionError("Error in \"split\"");
			} 
			else if (splitRule == ":=+1" || splitRule == ":=+2")
			{
				int rr = 2;
				if (splitRule == ":=+1")
					rr = 1;
				
				checkNumber(termApp.getParameters(),2);
				ApplicationTerm termOldApp = termOldCalcApp;//convertApp(termApp.getParameters()[0]);
				checkNumber(termOldApp.getParameters(),2);
				ApplicationTerm termNewApp = termSplitReturnApp;//convertApp(termApp.getParameters()[1]);
				checkNumber(termNewApp.getParameters(),2);
				
				//The term (F1 or F2) which is negated in new term
				Term termNewNeg = termOldApp.getParameters()[2-rr];
				Term termNewPos = termOldApp.getParameters()[rr-1];
				
				pm_func(termOldApp,"=");
				pm_func(termNewApp,"or");
				
				if (termNewApp.getParameters()[rr-1] != smtInterpol.term("not",termNewNeg)
						&& termNewApp.getParameters()[2-rr] != smtInterpol.term("not",termNewNeg))
					throw new AssertionError("Error 1 at " + splitRule);
				
				if (termNewApp.getParameters()[rr-1] != termNewPos
						&& termNewApp.getParameters()[2-rr] != termNewPos)
					throw new AssertionError("Error 2 at " + splitRule);
				
				/* Not nice: Not checked, if the F are boolean, which
				 * they should.
				 */
				
				stackPush(termApp.getParameters()[1], term);
				return;
			}
			else if (splitRule == ":=-1" || splitRule == ":=-2")
			{
				checkNumber(termApp.getParameters(),2);
				ApplicationTerm termOldApp = termOldCalcApp;
				checkNumber(termOldApp.getParameters(),1);
				ApplicationTerm termNewApp = termSplitReturnApp;
				checkNumber(termNewApp.getParameters(),2);
				ApplicationTerm termOldAppInnerApp = convertApp(termOldApp.getParameters()[0]);
				checkNumber(termOldAppInnerApp.getParameters(),2);
				
				Term termF1 = termOldAppInnerApp.getParameters()[0];
				Term termF2 = termOldAppInnerApp.getParameters()[1];
				
				pm_func(termOldApp,"not");
				pm_func(termOldAppInnerApp,"=");
				pm_func(termNewApp,"or");
				
				if (splitRule == ":=-1")
				{
					// or is commutative
					if (termNewApp.getParameters()[0] != termF1
						&& termNewApp.getParameters()[1] != termF1)
						throw new AssertionError("Error 1 at " + splitRule);
				
					if (termNewApp.getParameters()[0] != termF2
						&& termNewApp.getParameters()[1] != termF2)
						throw new AssertionError("Error 2 at " + splitRule);
				}
				else
				{
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
					
				stackPush(termApp.getParameters()[1], term);
				return;
			}
			else if (splitRule == ":ite+1" || splitRule == ":ite+2")
			{
				checkNumber(termApp.getParameters(),2);
				ApplicationTerm termOldApp = termOldCalcApp;
				checkNumber(termOldApp.getParameters(),3);
				ApplicationTerm termNewApp = termSplitReturnApp;
				checkNumber(termNewApp.getParameters(),2);
				
				Term termF1 = termOldApp.getParameters()[0];
				Term termF2 = termOldApp.getParameters()[1];
				Term termF3 = termOldApp.getParameters()[2];
				
				pm_func(termOldApp,"ite");
				pm_func(termNewApp,"or");
				
				if (splitRule == ":ite+2")
				{
					// or is commutative
					if (termNewApp.getParameters()[0] != termF1
							&& termNewApp.getParameters()[1] != termF1)
							throw new AssertionError("Error 1a at " + splitRule);
					
					if (termNewApp.getParameters()[0] != termF3
							&& termNewApp.getParameters()[1] != termF3)
							throw new AssertionError("Error 1b at " + splitRule);
				}
				else
				{					
					if (termNewApp.getParameters()[0] != termF2
						&& termNewApp.getParameters()[1] != termF2)
						throw new AssertionError("Error 2a at " + splitRule);
					
					if (termNewApp.getParameters()[0] != smtInterpol.term("not", termF1)
						&& termNewApp.getParameters()[1] != smtInterpol.term("not", termF1))
						throw new AssertionError("Error 2b at " + splitRule);
				}
					
						
				
				/* Not nice: Not checked, if the F are boolean, which
				 * they should.
				 */
				
			stackPush(termApp.getParameters()[1], term);
			return;
			
			}
			else if (splitRule == ":ite-1" || splitRule == ":ite-2")
			{
				checkNumber(termApp.getParameters(),2);
				ApplicationTerm termOldApp = termOldCalcApp;
				ApplicationTerm termOldAppInnerApp = convertApp(termOldApp.getParameters()[0]);
				checkNumber(termOldAppInnerApp.getParameters(),3);
				ApplicationTerm termNewApp = termSplitReturnApp;
				checkNumber(termNewApp.getParameters(),2);				
				
				Term termF1 = termOldAppInnerApp.getParameters()[0];
				Term termF2 = termOldAppInnerApp.getParameters()[1];
				Term termF3 = termOldAppInnerApp.getParameters()[2];
				
				pm_func(termOldApp,"not");
				pm_func(termOldAppInnerApp,"ite");
				pm_func(termNewApp,"or");
				
				if (splitRule == ":ite-2")
				{
					// or is commutative
					if (termNewApp.getParameters()[0] != termF1
						&& termNewApp.getParameters()[1] != termF1)
						throw new AssertionError("Error 1 at " + splitRule);
				
					if (termNewApp.getParameters()[0] != smtInterpol.term("not", termF3)
						&& termNewApp.getParameters()[1] != smtInterpol.term("not", termF3))
						throw new AssertionError("Error 2 at " + splitRule);
				}
				else
				{
					ApplicationTerm termNewAppInner2App = convertApp(termNewApp.getParameters()[1]);
					ApplicationTerm termNewAppInner1App = convertApp(termNewApp.getParameters()[0]);
				
					pm_func(termNewAppInner1App,"not");
					pm_func(termNewAppInner2App,"not");
					
					// or is commutative
					if (termNewAppInner1App.getParameters()[0] != termF1
						&& termNewAppInner2App.getParameters()[1] != termF1)
						throw new AssertionError("Error 3 at " + splitRule);

					if (termNewAppInner1App.getParameters()[0] != termF1
						&& termNewAppInner2App.getParameters()[1] != termF2)
						throw new AssertionError("Error 4 at " + splitRule);
				}
				
				/* Not nice: Not checked, if the F are boolean, which
				 * they should.
				 */
					
			stackPush(termApp.getParameters()[1], term);
			return;
			} 
			else
			{
				throw new AssertionError ("Error: The following split-rule hasn't been "
						 + "implemented yet: " + splitRule);
			}			
			
		case "annot":
			Term subtermCalc = stackPop(type);
			Annotation[] annots = stackAnnots.pop();
			Term returnTerm = smtInterpol.annotate(subtermCalc, annots);
			
			stackPush(returnTerm, term);
			return;
			
		default:
			throw new AssertionError("Error: Couldn't walk with the key " + type);
		}
	}
	
	/* For each parameter create a Walker, which calculates it */
	public void calcParams(ApplicationTerm termApp)
	{
		Term[] params = termApp.getParameters();
		
		for (int i = params.length - 1; i >= 0; i--)
		{			
			//Calculating in the arguments (of the resolution/equality) proven formulas
			stackWalker.push(new WalkerId<Term,String>(params[i],""));
		}
	}
	
	public void stackPush(Term pushTerm, Term keyTerm)
	{
		pcCache.put(keyTerm, pushTerm);
		stackResults.push(pushTerm);
		stackResultsDebug.push(keyTerm);
	}
	
	// The string is just for debugging, later it can be completely removed.
	public Term stackPop(String type)
	{
		if (stackResults.size() == 0 || stackResultsDebug.size() == 0)
		{
			throw new AssertionError("Error: The debug-stack or the result-stack has size 0: "
					+ "debug-size: " + stackResultsDebug.size() + ", result-size: " + stackResults.size());
		}
		
		if (stackResults.size() !=  stackResultsDebug.size())
		{
			throw new AssertionError("Error: The debug-stack and the result-stack have different size: "
					+ "debug-size: " + stackResultsDebug.size() + ", result-size: " + stackResults.size()
					+ " at: " + type);
		}
		
		Term returnTerm = stackResults.pop();
		Term debugTerm = stackResultsDebug.pop();
		
		if (pcCache.get(debugTerm) !=  returnTerm)
		{
			throw new AssertionError("Error: The debugger couldn't associate " + returnTerm.toStringDirect()
					+ " with " + debugTerm.toStringDirect() + " at " + type);
		}
		
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
				if (t == termDelete)
				{
					setResult(termInsert);
				} else if (isQuoted(t)) {
					setResult(t);
				} else {
					super.convert(t);
				}
			}
		}.transform(termOrig);
		
		
	}
		
	
	public class WalkerId<T, S> { 
		  public final Term t; 
		  public final String s; 
		  public WalkerId(Term t, String s) { 
		    this.t = t; 
		    this.s = s; 
		  } 
	}
	
	// Calculate an SMTAffineTerm
	SMTAffineTerm calculateTerm(Term term, SMTInterpol smtInterpol)
	{
		if (debug.contains("calculateTerm"))
			System.out.println("Calculate the term: " + term.toStringDirect());
		if (term instanceof ApplicationTerm)
		{
			ApplicationTerm termApp = (ApplicationTerm) term;
			SMTAffineTerm resultTerm;
			if (pm_func_weak(termApp,"+"))
			{
				if (termApp.getParameters().length < 1)
					throw new AssertionError("Error 1 in add in calculateTerm with term " + term.toStringDirect());
				resultTerm =
						SMTAffineTerm.create(termApp.getSort().getName() == "Real"
						                        ? smtInterpol.decimal("0.0") :
						smtInterpol.numeral("0"));
				for (Term summand : termApp.getParameters())
				{	
					resultTerm = resultTerm.add(calculateTerm(summand, smtInterpol));
				}					
				return resultTerm;
			}
			
			else if (pm_func_weak(termApp, "-"))
			{
				if (termApp.getParameters().length == 1)
					return (calculateTerm(termApp.getParameters()[0], smtInterpol).negate());
				
				if (termApp.getParameters().length == 2)
					return calculateTerm(termApp.getParameters()[0],smtInterpol).add(
							calculateTerm(termApp.getParameters()[1],smtInterpol).negate());
				
				throw new AssertionError("Error: The term with a \"-\" didn't have <= 2 arguments. The term was "
						+ term.toStringDirect());
			}
			
			else if (pm_func_weak(termApp, "*"))
			{
				if (termApp.getParameters().length != 2)
					throw new AssertionError("Error in mul in calculateTerm with term " + term.toStringDirect());
				
				SMTAffineTerm factor1 = calculateTerm(termApp.getParameters()[0], smtInterpol);
				SMTAffineTerm factor2 = calculateTerm(termApp.getParameters()[1], smtInterpol);
				if (factor1.isConstant())					
					return SMTAffineTerm.create(factor1.getConstant(), factor2);
				if (factor2.isConstant())					
					return SMTAffineTerm.create(factor2.getConstant(), factor1);
				throw new AssertionError("Error: Couldn't find the constant in the SMTAffineTerm multiplication. "
						+ "The term was " + termApp.toStringDirect());
			}
			
			else if (pm_func_weak(termApp, "/"))
			{
				if (termApp.getParameters().length != 2)
					throw new AssertionError("Error 1 in div in calculateTerm with term " + term.toStringDirect());
				SMTAffineTerm divident = calculateTerm(termApp.getParameters()[0], smtInterpol);
				SMTAffineTerm divisor = calculateTerm(termApp.getParameters()[1], smtInterpol);
				
				if (divisor.isConstant())
					return SMTAffineTerm.create(divident.getConstant().div(divisor.getConstant()), smtInterpol.sort("Real"));
					// Not nice: use of "Real"
				
				throw new AssertionError("Error: Couldn't find the constant in the SMTAffineTerm division. "
						+ "The term was " + termApp.toStringDirect());
			}
			
			else if (pm_func_weak(termApp, "=")
					|| pm_func_weak(termApp, "<=")
					|| pm_func_weak(termApp, "<")
					|| pm_func_weak(termApp, ">")
					|| pm_func_weak(termApp, ">="))
			{
				if (termApp.getParameters().length != 2)
					throw new AssertionError("Error 1 in = in calculateTerm with term " + term.toStringDirect());
				
				SMTAffineTerm leftSide = calculateTerm(termApp.getParameters()[0],smtInterpol);
				SMTAffineTerm rightSide = calculateTerm(termApp.getParameters()[1],smtInterpol);
				
				SMTAffineTerm leftSideNew =  leftSide.add(rightSide.negate());
				SMTAffineTerm rightSideNew =  rightSide.add(rightSide.negate()); //=0
				SMTAffineTerm[]	sides = new SMTAffineTerm[2];
				try {
					sides[0] = leftSideNew.div(leftSideNew.getGcd());
				} catch (NoSuchElementException var)
				{
					sides[0] = leftSideNew;
				}

				try {
					sides[1] = rightSideNew.div(rightSideNew.getGcd());
				} catch (NoSuchElementException var)
				{
					sides[1] = rightSideNew;
				}

				return SMTAffineTerm.create(smtInterpol.term(termApp.getFunction().getName(), sides));
			
			} else
			{
				//Throwing an Error would be wrong, because of self-defined functions.
				Term[] termAppParamsCalc = new Term[termApp.getParameters().length];
				for (int i = 0; i < termApp.getParameters().length; i++)
					termAppParamsCalc[i] = calculateTerm(termApp.getParameters()[i], smtInterpol);
				
				return SMTAffineTerm.create(smtInterpol.term(termApp.getFunction().getName(),
						termAppParamsCalc));
			}
		
		
						
		} else if (term instanceof ConstantTerm)
		{
			return SMTAffineTerm.create(term);
		}
		else if (term instanceof SMTAffineTerm)
		{
			return (SMTAffineTerm) term;
		}
		else
			throw new AssertionError("Error 3 in calculateTerm with term " + term.toStringDirect());
	}
	
	ApplicationTerm convertApp (Term term, String debugString)
	{
		if (debug.contains("convertApp"))
			System.out.println("Der untere Aufruf hat die ID: " + debugString);
		
		return convertApp(term);
	}
	
	ApplicationTerm convertApp (Term term)
	{
		if (debug.contains("convertApp"))
			System.out.println("Aufruf");
		
		if (!(term instanceof ApplicationTerm))
		{
			throw new AssertionError("Error: The following term should be an ApplicationTerm, "
					+ "but is of the class " + term.getClass().getSimpleName() + ".\n"
					+ "The term was: " + term.toString());
		}
		
		return (ApplicationTerm) term;
	}
	
	ApplicationTerm convertApp_hard (Term term)
	{
		if (term instanceof AnnotatedTerm)
			return convertApp(((AnnotatedTerm) term).getSubterm(), "annot");
		
		return convertApp(term, "hard");
	}
	
	AnnotatedTerm convertAnn (Term term)
	{
		if (!(term instanceof AnnotatedTerm))
		{
			throw new AssertionError("Error: The following term should be an AnnotatedTerm, "
					+ "but is of the class " + term.getClass().getSimpleName() + ".\n"
					+ "The term was: " + term.toString());
		}
		
		return (AnnotatedTerm) term;
	}
	
	ConstantTerm convertConst (Term term)
	{
		if (!(term instanceof ConstantTerm))
		{
			throw new AssertionError("Error: The following term should be a ConstantTerm, "
					+ "but is of the class " + term.getClass().getSimpleName() + ".\n"
					+ "The term was: " + term.toString());
		}
		
		return (ConstantTerm) term;
	}
	
	Term convertConst_Neg (Term term)
	{
		if (term instanceof ConstantTerm)
		{
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
	
	boolean checkInt_weak(Term term, SMTInterpol smtInterpol)
	{
		if (term.getSort() == smtInterpol.sort("Int"))
			return true;
		
		// Then it must be a negative Integer
		
		ApplicationTerm termApp = convertApp(term);
		pm_func(termApp,"-");
		
		if (termApp.getParameters()[0].getSort() == smtInterpol.sort("Int"))
			return true;
	
		return false;
//		throw new AssertionError("Error: The following term should be an Integer, "
//				+ "but is of the sort " + term.getSort().getName() + ".\n"
//				+ "The term was: " + term.toString());
	}
	
	// Now some pattern-match-functions.

	//Throws an error if the pattern doesn't match
	void pm_func(ApplicationTerm termApp, String pattern)
	{
		if (!termApp.getFunction().getName().equals(pattern))
			throw new AssertionError("Error: The pattern \"" + pattern
					+ "\" was supposed to be the function symbol of " + termApp.toStringDirect() + "\n"
					+ "Instead it was " + termApp.getFunction().getName());
	}
	
	void pm_func(Term term, String pattern)
	{
		pm_func(convertApp(term),pattern);
	}
	
	boolean pm_func_weak(ApplicationTerm termApp, String pattern)
	{
		return termApp.getFunction().getName().equals(pattern);
	}
	
	// Does this function make any sense?
	boolean pm_func_weak(Term term, String pattern)
	{
		if (term instanceof ApplicationTerm)
			return pm_func_weak((ApplicationTerm) term, pattern);
		
		throw new AssertionError("Expected an ApplicationTerm in func_weak!");
	}
	
	void pm_annot(AnnotatedTerm termAnn, String pattern)
	{
		if (termAnn.getAnnotations()[0].getKey() != pattern)
			throw new AssertionError("Error: The pattern \"" + pattern
					+ "\" was supposed to be the annotation of " + termAnn.toString() + "\n"
					+ "Instead it was " + termAnn.getAnnotations()[0].toString());
		
		if (termAnn.getAnnotations().length != 1)
			throw new AssertionError("Error: A term has " + termAnn.getAnnotations().length + " annotations,"
					+ ", but was supposed to have just one.");	
	}
	
	void checkNumber(Term[] termArray, int n)
	{
		if (termArray.length < n)
			throw new AssertionError("Error: "
					+ "The array " + termArray.toString() + " is to short!"
					+ "\n It should have lentgh " + n);
	}
	
	void checkNumber(ApplicationTerm termApp, int n)
	{
		if (termApp.getParameters().length < n)
			throw new AssertionError("Error: "
					+ "The parameter-array of " + termApp.toStringDirect() + " is to short!"
					+ "\n It should have lentgh " + n);
	}
	
	
	boolean pathFind(HashMap<SymmetricPair<Term>,Term[]> subpaths, HashMap<SymmetricPair<Term>,Term[]> premises,
			Term termStart, Term termEnd)
	{
		if (debug.contains("LemmaCC"))
			System.out.println("Searching for a way from " + termStart.toStringDirect()
					+ " to " + termEnd.toStringDirect());
		
		// Are the terms already equal?
		if (termStart == termEnd)
			return true;
		
		SymmetricPair<Term> searchPair = new SymmetricPair<Term>(termStart, termEnd);
		
		/* The reason for checking the premises before the subpaths is,
		 * that the subpaths may contain the same equality as the premises, which
		 * could lead to infinite loops.
		 */
		
		// Is the searched equality already a premise?
		if(premises.containsKey(searchPair))
			return true;
		
		// Does a path for the searched equality exist?
		if(subpaths.containsKey(searchPair))
		{
			Term[] path = subpaths.remove(searchPair);
			Term nextStep = path[1];
			Term[] pathCut = new Term[path.length-1];
			for (int i = 0; i < pathCut.length; i++)
				pathCut[i] = path[i+1];
			subpaths.put(new SymmetricPair<Term>(nextStep,termEnd), pathCut);
			if (pathFind(subpaths,premises,termStart,nextStep))
				return pathFind(subpaths,premises,nextStep,termEnd);
			else
				return false;
		}
		
		/* So the pair can't be found, then
		 * it must be a pair of two functions with the same
		 * function symbol and parameters which can be found.
		 */
		
		// Syntactical correctness
		ApplicationTerm termStartApp = convertApp(termStart);
		ApplicationTerm termEndApp = convertApp(termEnd);
		
		pm_func(termStartApp,termEndApp.getFunction().getName());
		
		if (termStartApp.getParameters().length == 0
				|| termStartApp.getParameters().length != termEndApp.getParameters().length)
			throw new AssertionError("Error 1 in pathfinding");
		
		// Semantical Correctness
		
		// true iff for each parameter-pair a path can be found
		boolean returnVal = true;
		
		for (int i = 0; i < termStartApp.getParameters().length; i++)
		{
			returnVal = returnVal &&
					pathFind(subpaths, premises, termStartApp.getParameters()[i], termEndApp.getParameters()[i]);
		}
		
		return returnVal;
	}
	
	ApplicationTerm uniformizeInEquality(ApplicationTerm termApp, SMTInterpol smtInterpol)
	{
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
		checkNumber(termIneq.getParameters(),2);
		
		// Take everything to the left side
		
		SMTAffineTerm termLeft = calculateTerm(termIneq.getParameters()[0], smtInterpol);
		SMTAffineTerm termRight = calculateTerm(termIneq.getParameters()[1], smtInterpol);
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
		if (relation == ">=")
		{
			termLeftNew = termLeftNew.negate();
			relation = "<=";
		} else if (relation == ">")
		{
			termLeftNew = termLeftNew.negate();
			relation = "<";
		}
		
		// Extra-Case for Integers
		if (onlyInts(termLeftNew, smtInterpol) && relation == "<")
		{
			termLeftNew = termLeftNew.add(Rational.ONE);
			relation = "<=";
		}
		
		// Now build the to-be-returned term
		Term[] params = new Term[2];
		params[0] = termLeftNew;
		
		if (!termLeftNew.getSort().isNumericSort())
			throw new AssertionError("Error 2 in uniformizeInequality");
		
		params[1] = (Rational.ZERO).toTerm(termLeftNew.getSort());		
		
		return convertApp(smtInterpol.term(relation, params), "unif2");
	}
	
	boolean onlyInts(Term term, SMTInterpol smtInterpol)
	{
		if (term instanceof AnnotatedTerm)
			return onlyInts(((AnnotatedTerm) term).getSubterm(), smtInterpol);
		else if (term instanceof ApplicationTerm)
		{
			ApplicationTerm termApp = convertApp(term);
			for (Term param : termApp.getParameters())
				if (!onlyInts(param, smtInterpol))
					return false;
			return true;
		} 
		else if (term instanceof SMTAffineTerm)
		{
			SMTAffineTerm termAff = (SMTAffineTerm) term;

			return termAff.isIntegral();
		} else
		{
			// So the term is constant
			
			return term.getSort().equals(smtInterpol.sort("Int"));			
		}			
	}
	
	void isConstant(SMTAffineTerm term, Rational constant)
	{
		if (!isConstant_weak(term, constant))
			throw new AssertionError("The following term should be the "
						+ "constant " + constant.toString() + " but isn't: "
						+ term.toStringDirect());
	}

	boolean isConstant_weak(SMTAffineTerm term, Rational constant)
	{
		if (!term.isConstant() || term.getConstant() != constant)
			return false;
		return true;
	}
	
	boolean uniformedSame(ApplicationTerm term1, ApplicationTerm term2, SMTInterpol smtInterpol)
	{
		if (term1.equals(term2))
			return true;
		
		SMTAffineTerm term1leftAff = calculateTerm(term1.getParameters()[0],smtInterpol);
		SMTAffineTerm term2leftAff = calculateTerm(term1.getParameters()[0],smtInterpol);
		
		if (term1leftAff.equals(term2leftAff))
			return true; //Should be unreachable
		
		// Maybe one side of the equation is the negation of the other
		if (term1leftAff.equals(term2leftAff.negate()))
			return true; //Should be unreachable
		
		return false;
	}	
}