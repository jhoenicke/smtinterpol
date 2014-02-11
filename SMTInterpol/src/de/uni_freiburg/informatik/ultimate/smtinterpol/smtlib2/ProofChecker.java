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


//import java.util.ArrayList;
//import java.util.HashMap;
import java.util.*;

public class ProofChecker extends SMTInterpol {
	
	HashSet<String> debug = new HashSet<String>(); // Just for debugging
	
	// Not nice: returns are spread over the code, all could be in the end
	HashMap<Term, Term> pcCache; //Proof Checker Cache
	
	// Declarations for the Walker
	Stack<WalkerId<Term,String>> stackWalker = new Stack<WalkerId<Term,String>>();
	Stack<Term> stackResults = new Stack<Term>();
	Stack<Term> stackResultsDebug = new Stack<Term>();
	//Not nice: Is this really necessary?:
	Stack<Annotation[]> stackAnnots = new Stack<Annotation[]>();
	
	public boolean check(Term res, SMTInterpol smtInterpol) {
		
		// Just for debugging
		//debug.add("currently");
		//debug.add("passt");
		//debug.add("hardTerm");
		//debug.add("LemmaLAadd");
		//debug.add("calculateTerm");
		
		// Initializing the proof-checker-cache
		pcCache = new HashMap<Term, Term>();
				
		Term resCalc;
		// Now non-recursive:
		stackWalker.push(new WalkerId<Term,String>(new FormulaUnLet().unlet(res),""));
		WalkerId<Term,String> currentWalker;
		
		
		while (!stackWalker.isEmpty())
		{
			// Just for debugging
			/*
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
			System.out.println("");*/
			
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
			//System.out.println("On top was: " + resCalc.toStringDirect());
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
	
	// Does ProgramCounterStuff and unfolding
	public ArrayList<Integer> afterUnfoldPc(ArrayList<Integer> pfpc)	
	{
		pfpc.remove(pfpc.size()-1);
		
		// Iterate the last element
		pfpc.set(pfpc.size()-1, pfpc.get(pfpc.size()-1) + 1);
		
		return pfpc;
	}
	
	public void walk(Term term, SMTInterpol smtInterpol)
	{
		/* Non-recursive */
		/* Takes proof, returns proven formula */
		//System.out.println("Term: " + term.toStringDirect());
		
		/* Check the cache, if the unfolding step was already done */
		if (pcCache.containsKey(term))
		{
			if (pcCache.get(term) == null)
			{
				throw new AssertionError("Error: The term " + term.toString() + " was already "
						+ "calculated, but isn't in the cache.");
			}
			//System.out.println("Calculation of the term " + res.toStringDirect() 
			//		+ " is known: " + pcCache.get(res).toStringDirect());
			stackPush(pcCache.get(term), term);
			return;
		}
				
		/* Declaration of variables used later */
		String functionname;
		//Not nice: Initialization as null.
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
			
			/* Look at the function of the application-term and treat each different */
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
				//TODO: Implement rule-reader
				
				// If possible return the un-annotated version
				// Warning: Code duplicates (Random number: 498255)
				if (termApp.getParameters()[0] instanceof ApplicationTerm)
					System.out.println("");
				termAppInnerAnn = convertAnn(termApp.getParameters()[0]);
				
				if (termAppInnerAnn.getAnnotations()[0].getKey() == ":LA")
				{
					ApplicationTerm termLemmaApp = convertApp(termAppInnerAnn.getSubterm());
					
					pm_func(termLemmaApp,"or");
					
					int arrayLength = termLemmaApp.getParameters().length;
					ApplicationTerm[] termLemmaAppNegApp = new ApplicationTerm[arrayLength];
					AnnotatedTerm[] termLemmaAppNegAppInnerAnn = new AnnotatedTerm[arrayLength];
					ApplicationTerm[] termLemmaEq = new ApplicationTerm[arrayLength];
					SMTAffineTerm[] termLemmaCheck = new SMTAffineTerm[arrayLength];
					
					//Now get the numbers:
					Term[] numbers = (Term[]) termAppInnerAnn.getAnnotations()[0].getValue();
					Rational[] numbersSMT = new Rational[numbers.length];
					
					for (int i = 0; i < numbers.length; i++)
						numbersSMT[i] = calculateTerm(numbers[i], smtInterpol).getConstant();
					
					//boolean foundGe = false; // found greater-equal (>=)
					//boolean foundGt = false; // found greater-than (>)
					boolean foundLe = false; // found lower-equal (<=)
					boolean foundLt = false; // found lower-than (<)
					boolean foundNeg = false; // has the i-th component a negation?
					for (int i = 0; i < arrayLength; i++)
					{
						// Maybe there's no negation
						foundNeg = (termLemmaApp.getParameters()[i] instanceof ApplicationTerm);
						
						//Syntactical correctness
						if (foundNeg)
						{
							termLemmaAppNegApp[i] = convertApp(termLemmaApp.getParameters()[i]);
							if (termLemmaAppNegApp[i].getParameters()[0] instanceof ApplicationTerm)
								System.out.println("");
							termLemmaAppNegAppInnerAnn[i] = convertAnn(termLemmaAppNegApp[i].getParameters()[0]);
						}
						else
						{
							if (termLemmaApp.getParameters()[i] instanceof ApplicationTerm)
								System.out.println("");
							termLemmaAppNegAppInnerAnn[i] = convertAnn(termLemmaApp.getParameters()[i]);
						}

						if (!(termLemmaAppNegAppInnerAnn[i].getSubterm() instanceof ApplicationTerm))
							System.out.println("");
						termLemmaEq[i] = convertApp(termLemmaAppNegAppInnerAnn[i].getSubterm());
						termLemmaCheck[i] = calculateTerm(termLemmaEq[i].getParameters()[0], smtInterpol);
						
						if (foundNeg)
							pm_func(termLemmaAppNegApp[i],"not");
						pm_annot(termLemmaAppNegAppInnerAnn[i],":quoted");
						
						// Semantical correctness
						if (foundNeg)
						{
							//Important: foundGe = ...< is correct, since >= \equiv (not <)
							/*if (//foundGe && pm_func_weak(termLemmaEq[i],">") ||
									foundLe && pm_func_weak(termLemmaEq[i],"<"))
								throw new AssertionError("Error 1 in @lemma_:LA");*/
							
							//foundGe = foundGe || pm_func_weak(termLemmaEq[i],"<");
							//foundLe = foundLe || pm_func_weak(termLemmaEq[i],">");
							if (pm_func_weak(termLemmaEq[i],"<="))
							{
								//The inequality must be inverted, but not here
								if(numbersSMT[i].isNegative())
									throw new AssertionError("Error 2c in @lemma_:LA");
								//termLemmaCheck[i] = termLemmaCheck[i].negate(); //WRONG! Wird implizit über die Koeffizienten negiert
								//numbersSMT[i] = SMTAffineTerm.create( //WRONG!!
									//	numbersSMT[i], SMTAffineTerm.create(smtInterpol.numeral("-1"))).getConstant();
								foundLe = true;
								continue;
							}

							if (pm_func_weak(termLemmaEq[i],"<"))
							{
								if(numbersSMT[i].isNegative())
									throw new AssertionError("Error 2e in @lemma_:LA");
								foundLt = true;
								continue;
							}
							
							pm_func(termLemmaEq[i],"=");
						}
						else
						{
							/*if (//foundGe && pm_func_weak(termLemmaEq[i],"<=") ||
									foundLe && pm_func_weak(termLemmaEq[i],">="))
								throw new AssertionError("Error 2a in @lemma_:LA");*/
							
							// foundGe = foundGe || pm_func_weak(termLemmaEq[i],">=");
							// foundLe = foundLe || pm_func_weak(termLemmaEq[i],"<=");
							
							//The inequality must be inverted
							if(!numbersSMT[i].isNegative())
								throw new AssertionError("Error 2d in @lemma_:LA");
							
							if (pm_func_weak(termLemmaEq[i],"<="))
							{
								foundLt = true;
								continue;
							}
							if (pm_func_weak(termLemmaEq[i],"<"))
							{
								foundLe = true;
								continue;
							}
							
							throw new AssertionError("Error 2b in @lemma_:LA");
						}
					}
					
					//if((foundLe || foundLt && (foundGt || foundGe))
					//	throw new AssertionError("Error 3a in @lemma_:LA");
					
					for(ApplicationTerm equality : termLemmaEq)
					{
						// Not nice: Use of "0+0=0" (Important: Needs to take care of both 0 and 0.0)
						// Warning: Code almost-duplicates (Random number: 29364)
						SMTAffineTerm termAffTemp = calculateTerm(equality.getParameters()[1],smtInterpol);
						if (!(termAffTemp.equals(termAffTemp.add(termAffTemp))))
							throw new AssertionError("Error 3b in @lemma_:LA: " + equality.getParameters()[1].toStringDirect());
					}
					
					SMTAffineTerm result = termLemmaCheck[0].mul(numbersSMT[0]);
					//System.out.println("Result: " + result.toStringDirect());
					
					for (int i = 1; i < numbersSMT.length; i++)
					{
						if (debug.contains("LemmaLAadd"))
						{
							System.out.println("Term ohne mult: " + termLemmaCheck[i].toStringDirect());
							System.out.println("mult: " + numbersSMT[i]);
							System.out.println("Term mit mult: " + termLemmaCheck[i].mul(numbersSMT[i]).toStringDirect());
						}
						result = result.add(termLemmaCheck[i].mul(numbersSMT[i]));
						if(debug.contains("LemmaLAadd"))
							System.out.println("Result: " + result.toStringDirect());
					}
					
					if (!result.isConstant())
						throw new AssertionError("Error 4 in @lemma_:LA!: " + result.toStringDirect());
					
					// Explanation of how the logic behind the lemmata works:
					// It's a proof via contradiction, i.e. the negation of the whole lemma leads to a contradiction.
					// Since it's a disjunction, it's negation will be a conjunction of the negated disjuncts.
					// That means we can argue, that every negated disjunct has to hold, and this leads to a disjunction.
					// We just want terms with =0, <0 or <=0 which results in:
					//  * not a < 0	<=>	a >= 0	<=> -a <= 0
					//  * not a <= 0	<=>	a > 0	<=> -a < 0
					// Then we multiply each equation with an integer and sum them all up, which should lead to this contradiction
					// (x = 0) + (y <= 0) --> x+y <= 0
					// (x <= 0) + (y < 0) --> x+y < 0
					// So, e.g., if we have a (x < 0)-term, the proof is correct, if x+... is at least 0, this will lead to a contradiction
					
					// Not nice: Laborious if-condition: result = 0
					if (!foundLe && !foundLt && result.add(result).equals(result))
						throw new AssertionError("Error 5 in @lemma_:LA!");
					
					// Not nice: Result > 0 	<=> not result <= 0
					if (!foundLt && foundLe
							&& (result.getConstant().isNegative()
							|| result.add(result).equals(result)))
						throw new AssertionError("Error 6 in @lemma_:LA!");
					
					// Not nice: Result >= 0		<=> not result < 0
					if (foundLt
							&& result.getConstant().isNegative())
						throw new AssertionError("Error 7 in @lemma_:LA!");
					
					// Result < 0
//					if (foundNeg && (foundGe || foundGt)
//							&& result.getConstant().isNegative())
//						throw new AssertionError("Error 7 in @lemma_:LA!");
					
					if (debug.contains("passt"))
					{
						//if (foundGe)
							//System.out.println("Passt, da " + result + " !< 0");
						//else
						if (foundLe)
							System.out.println("Passt, da " + result + " !> 0");
						else
							System.out.println("Passt, da " + result + " != 0");
					}
					
					
				} else if (termAppInnerAnn.getAnnotations()[0].getKey() == ":CC")
				{
					//Syntactical correctness
					ApplicationTerm termLemmaApp = convertApp(termAppInnerAnn.getSubterm());
					
					pm_func(termLemmaApp,"or");
					
					int arrayLength = termLemmaApp.getParameters().length;
					
					ApplicationTerm[] termLemmaAppIApp = new ApplicationTerm[arrayLength];
					termLemmaAppIApp[0] = null; //The first component has no meaning
					for (int i = 1; i < arrayLength; i++)
					{
						termLemmaAppIApp[i] = convertApp(termLemmaApp.getParameters()[i]);
						pm_func(termLemmaAppIApp[i],"not");
					}
					
					// Get the equalities, the annotations are ignored
					// The first equality is the goal, the others are the premises
					ApplicationTerm[] termLemmaEqApp = new ApplicationTerm[arrayLength];
					termLemmaEqApp[0] = convertApp_hard(termLemmaApp.getParameters()[0]);
					pm_func(termLemmaEqApp[0],"=");
					for (int i = 1; i < arrayLength; i++)
					{
						termLemmaEqApp[i] = convertApp_hard(termLemmaAppIApp[i].getParameters()[0]);
						pm_func(termLemmaEqApp[i],"=");
					}
					
					Object[] annotValues = (Object[]) termAppInnerAnn.getAnnotations()[0].getValue();
					
					if (!annotValues[0].equals(termLemmaEqApp[0]))
						throw new AssertionError("Error 1 in lemma_:CC");
					
					// Get the subpaths
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
					
					// Get the premises
					HashMap<SymmetricPair<Term>, Term[]> premises =
							new HashMap<SymmetricPair<Term>,Term[]>();
					
					for (int i = 1; i < arrayLength; i++)
					{
						SymmetricPair<Term> pairTemp = new SymmetricPair<Term>(
								termLemmaEqApp[i].getParameters()[0],termLemmaEqApp[i].getParameters()[1]);
						premises.put(pairTemp,termLemmaEqApp[i].getParameters());
					}
					
					// Now for the pathfinding
					Term termStart = termLemmaEqApp[0].getParameters()[0];
					Term termEnd = termLemmaEqApp[0].getParameters()[1];
					
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
				System.out.println("Believed as true: " + termApp.toStringDirect() + " ."); //TODO: Implement rule-reader
				
				// If possible return the un-annotated version
				// Warning: Code duplicates (Random number: 498255)
				if (termApp.getParameters()[0] instanceof ApplicationTerm)
					System.out.println("");
				termAppInnerAnn = convertAnn(termApp.getParameters()[0]);
				
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
				if (termApp.getParameters()[0] instanceof AnnotatedTerm)
				{
					termAppInnerAnn = (AnnotatedTerm) termApp.getParameters()[0]; //The annotated term inside the rewrite-term
				} else
				{
					throw new AssertionError("Expected an annotated term inside any rewrite-term, but the following term doesn't have one: " + termApp.getParameters()[0]);
				}
				if (termAppInnerAnn.getSubterm() instanceof ApplicationTerm)
				{
					termEqApp = (ApplicationTerm) termAppInnerAnn.getSubterm(); //The application term inside the annotated term inside the rewrite-term
				} else
				{
					throw new AssertionError("Expected an application term inside the annotated term inside a rewrite-term, but the following term is none: " + termAppInnerAnn.getSubterm());
				}
				if (termEqApp.getFunction().getName() != "=")
				{
					System.out.println("A random number: 440358"); // Can be used to differ between two same-sounding errors
					throw new AssertionError("Error: The following terms should have = as function symbol, but it has: " + termEqApp.getFunction().getName());
				}
				
				/* Read the rule and handle each differently */
				String rewriteRule = termAppInnerAnn.getAnnotations()[0].getKey();
				if (debug.contains("currently"))
					System.out.println("Rule: " + rewriteRule);
				if (debug.contains("hardTerm"))
					System.out.println("Term: " + term.toStringDirect());
				if (false)
				{} else if (rewriteRule == ":trueNotFalse")
				{
					System.out.println("\n \n \n Now finally tested: " + rewriteRule); //TODO
					
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
					
				} else if (rewriteRule == ":eqTrue")
				{
					System.out.println("\n \n \n Now finally tested: " + rewriteRule);	 //TODO
															
					ApplicationTerm termOldApp = convertApp(termEqApp.getParameters()[0]);
					ApplicationTerm termNewApp = convertApp(termEqApp.getParameters()[1]);

					pm_func(termOldApp,"=");
					pm_func(termNewApp,"and");
										
					HashSet<Term> oldTerms = new HashSet<Term>();
					HashSet<Term> newTerms = new HashSet<Term>();
					
					oldTerms.addAll(Arrays.asList(termOldApp.getParameters()));
					newTerms.addAll(Arrays.asList(termNewApp.getParameters()));
					
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
					System.out.println("\n \n \n Now finally tested: " + rewriteRule);	 //TODO
					
					ApplicationTerm termOldApp = convertApp(termEqApp.getParameters()[0]);
					ApplicationTerm termNewApp = convertApp(termEqApp.getParameters()[1]);
					ApplicationTerm termNewAppInnerApp = convertApp(termNewApp.getParameters()[0]);

					pm_func(termOldApp, "=");
					pm_func(termNewApp, "not");
					pm_func(termNewAppInnerApp, "or");
					
					HashSet<Term> oldTerms = new HashSet<Term>();
					HashSet<Term> newTerms = new HashSet<Term>();
					
					oldTerms.addAll(Arrays.asList(termOldApp.getParameters()));
					newTerms.addAll(Arrays.asList(termNewAppInnerApp.getParameters()));
					
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
					System.out.println("\n \n \n Now finally tested: " + rewriteRule); //TODO
					
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
					System.out.println("\n \n \n Now finally tested: " + rewriteRule);	 //TODO
					
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
					
				} else if (rewriteRule == ":distinctSame")
				{
					
					if (!(termEqApp.getParameters()[1] == smtInterpol.term("false")))
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
				
				} else if (rewriteRule == ":distinctBinary")
				{					
					ApplicationTerm termOldApp = convertApp(termEqApp.getParameters()[0]);
					ApplicationTerm termNewApp = convertApp(termEqApp.getParameters()[1]);
					ApplicationTerm termNewAppInnerApp = convertApp(termNewApp.getParameters()[0]);
					
					pm_func(termNewApp, "not");
					pm_func(termOldApp, "distinct");
					
					// The array which contains the equalities
					Term[] arrayNewEq = null;
					Term[] arrayOldTerm = termOldApp.getParameters(); 
					
				
					if (termNewAppInnerApp.getFunction().getName() == "or")
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
							throw new AssertionError("Error: Coulnd't associate the equality " + arrayNewEq[i] + "\n. The term was " + term.toStringDirect());
					
					// So it is correct
				}
				
				else if (rewriteRule == ":notSimp")
				{
					// The first argument of the rewrite has to be the double-negated version of the second argument
					//ApplicationTerm innerAppTermFirstNeg; //The first negation inside the first argument
					//ApplicationTerm innerAppTermSecondNeg; //The second negation inside the first argument
					
					// Check syntactical correctness
					ApplicationTerm innerAppTermFirstNeg = convertApp(termEqApp.getParameters()[0]);
					pm_func(innerAppTermFirstNeg, "not");
					
					// TODO: Needs testing!
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
						throw new AssertionError("Error at rule " + rewriteRule	+ "!\n The term was " + term.toStringDirect());
					
					
				} else if (rewriteRule == ":strip")
				{
					//Term which has to be stripped, annotated term
//					if (termEqApp.getParameters()[0] instanceof ApplicationTerm)
//						System.out.println("");
					AnnotatedTerm stripAnnTerm = convertAnn(termEqApp.getParameters()[0]);
					if (stripAnnTerm.getSubterm() != termEqApp.getParameters()[1])
					{
						throw new AssertionError("Error: Couldn't verify a strip-rewrite. Those two terms should be the same but arent"
								+ stripAnnTerm.getSubterm() + "vs. " + termEqApp.getParameters()[1] + ".");
					}
				
				} else if (rewriteRule == ":gtToLeq0" || rewriteRule == ":geqToLeq0"
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
					// Not nice: Use of "0+0=0" (Important: Needs to take care of both 0 and 0.0)
					// Warning: Code almost-duplicates (Random number: 29364)
					SMTAffineTerm termAffTemp = calculateTerm(termNewIneqApp.getParameters()[1],smtInterpol);
					if (!(termAffTemp.equals(termAffTemp.add(termAffTemp))))
						throw new AssertionError("Error: Expected an Inequality ... <= 0 as a result "
								+ "of the rule " + rewriteRule + ", but the result is " + termNewApp.toString());
					
					SMTAffineTerm leftside = calculateTerm(termNewIneqApp.getParameters()[0], smtInterpol);

					SMTAffineTerm termT1Aff = calculateTerm(termT1, smtInterpol);
					SMTAffineTerm termT2Aff = calculateTerm(termT2, smtInterpol);
					
					if (rewriteRule == ":gtToLeq0" || rewriteRule == ":leqToLeq0")
					{
						if (!leftside.equals(termT1Aff.add(termT2Aff.negate())))
						{
							throw new AssertionError("Error: Wrong term on the left side of "
									+ "the new inequality. The term was: " + termEqApp.toStringDirect() + "\n"
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
				
				} else if (rewriteRule == ":flatten")
				{
					ApplicationTerm termOldApp = convertApp(termEqApp.getParameters()[0]);
					ApplicationTerm termNewApp = convertApp(termEqApp.getParameters()[1]);
					ApplicationTerm termOldAppInnerApp = convertApp(termOldApp.getParameters()[0]);
					
					// Assumption: The first argument of the outer disjunction is the inner disjunction
					pm_func(termNewApp, "or");
					pm_func(termOldApp, "or");
					pm_func(termOldAppInnerApp, "or");
					
					HashSet<Term> oldDisjuncts = new HashSet<Term>();
					HashSet<Term> newDisjuncts = new HashSet<Term>();
									
					oldDisjuncts.addAll(Arrays.asList(termOldAppInnerApp.getParameters()));
					for (int i = 1; i < termOldApp.getParameters().length; i++)
						oldDisjuncts.add(termOldApp.getParameters()[i]);
					newDisjuncts.addAll(Arrays.asList(termNewApp.getParameters()));
					
					if (!oldDisjuncts.equals(newDisjuncts))
						throw new AssertionError("Error in the rule " + rewriteRule + "!\n The term was " + term.toStringDirect());
					
				
				} else
				{
					System.out.println("Can't handle the following rule " + termAppInnerAnn.getAnnotations()[0].getKey() + ", therefore...");
					System.out.println("...believed as alright to be rewritten: " + termApp.getParameters()[0].toStringDirect() + " ."); //Not nice: Too few rules
				}				
			
				// The second part, cut the @rewrite and the annotation out, both aren't needed for the @eq-function.
				// stackPush(innerAnnTerm.getSubterm(), term);
				return;
				
			case "@intern":
				//TODO: Implement rule-reader
				
				// Trying to get the rewrite:
				// First the syntactical check
				
				termEqApp = convertApp(termApp.getParameters()[0]);
				
				pm_func(termEqApp,"=");
				
//				Term termBeforeRewrite = termEqApp.getParameters()[0]; //The subterm which gets rewritten
//				Term termAfterRewrite  = termEqApp.getParameters()[1]; //The new subterm, which will replace the old one
				
				boolean firstNeg = false;
				boolean secondNeg = false;
				
				if (termEqApp.getParameters()[0] instanceof ApplicationTerm)
					if (((ApplicationTerm) termEqApp.getParameters()[0]).getFunction().getName() == "not")
						firstNeg = true;
				
				if (termEqApp.getParameters()[1] instanceof ApplicationTerm)
					if (((ApplicationTerm) termEqApp.getParameters()[1]).getFunction().getName() == "not")
						secondNeg = true;
				
				ApplicationTerm termOldComp;
				ApplicationTerm termNewComp;
				// The annotations are not important for the correctness-check
				if (firstNeg)
					termOldComp = convertApp_hard(
							((ApplicationTerm) termEqApp.getParameters()[0]).getParameters()[0]);
				else
					termOldComp = convertApp_hard(termEqApp.getParameters()[0]);
				
				if(secondNeg)
					termNewComp = convertApp_hard(
							((ApplicationTerm) termEqApp.getParameters()[1]).getParameters()[0]);
				else
					termNewComp = convertApp_hard(termEqApp.getParameters()[1]);
				
				//System.out.println("BothOrig" + termEqApp.toStringDirect());
				//System.out.println("NewConvert" + termNewComp.toStringDirect());
				
				//<->
				if ((firstNeg && secondNeg)		||		(!firstNeg && !secondNeg))
					if(!calculateTerm(termOldComp,smtInterpol).equals(
						calculateTerm(termNewComp,smtInterpol)))
						System.out.println("Sadly, I couldn't understand the internal rewrite: "
						+ termApp.getParameters()[0].toStringDirect() + " .");
					else
						return;
				
				//xor
				if ((pm_func_weak(termOldComp,"<=") && pm_func_weak(termNewComp,"<"))
						|| (pm_func_weak(termOldComp,"<") && pm_func_weak(termNewComp,"<=")))
				{
					if ((calculateTerm(termOldComp.getParameters()[0],smtInterpol).mul(
							calculateTerm(smtInterpol.numeral("-1"),smtInterpol).getConstant())).equals(
									calculateTerm(termNewComp.getParameters()[0],smtInterpol))
						&& termOldComp.getParameters()[1] == termNewComp.getParameters()[1])
						return;
					// If it's an integer-logic, it could be a x <= 0  <--> -x < 1 transformation
					// Not nice: Use of Strings
					if (term.getTheory().getLogic().toString() == "QF_LIA")
					{
						String addNumber = "";
						if (firstNeg)
							addNumber = "1";
						else
							addNumber = "-1";
				
						if (((calculateTerm(termOldComp.getParameters()[0],smtInterpol).add(
										calculateTerm(smtInterpol.numeral(addNumber),smtInterpol)).mul(
												calculateTerm(smtInterpol.numeral("-1"),smtInterpol).getConstant()))).equals(
										calculateTerm(termNewComp.getParameters()[0],smtInterpol))
							&& termOldComp.getParameters()[1] == termNewComp.getParameters()[1])
							return;
					}
				}
				
				System.out.println("Sadly, I had to believe the following internal rewrite: "
						+ termApp.getParameters()[0].toStringDirect() + " .");
				return;
				
				
				//throw new AssertionError("Error at the end of intern!");
				
//				boolean understoodInternalRewrite = false;
//				if (termAfterRewrite instanceof AnnotatedTerm)
//				{
//					AnnotatedTerm termAfterRewriteAnn = (AnnotatedTerm) termAfterRewrite;
//					if (termAfterRewriteAnn.getSubterm() == termBeforeRewrite
//							&& termAfterRewriteAnn.getAnnotations().length == 1
//							&& termAfterRewriteAnn.getAnnotations()[0].getKey() == ":quoted")
//					{
//						understoodInternalRewrite = true;
//					}
//				}
//				
//				if (!understoodInternalRewrite)
//				{
//					System.out.println("Believed as alright to be (intern) rewritten: "
//							+ termApp.getParameters()[0].toStringDirect() + " .");
//				} /*else {
//					System.out.println("Understood internal rewrite.");
//				}*/
				
				
				
				//stackPush(appTerm.getParameters()[0], term);
				//return;
				
			case "@split":
				// TODO: Check if the first argument contains the second argument
				
				/* At this point there is no access to the other arguments, so it
				 * can't be checked here if the first argument is the same as the last argument of 
				 * the last argument. */
				
				stackPush(termApp.getParameters()[1], term); //Not nice: Kann da auch etwas stehen was eigentlich aufgefaltet werden sollte?
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
			/* res is an AnnotatedTerm */
			
			/* Annotations no more get just removed, this was incorrect */
			
			annTerm = (AnnotatedTerm) term;
			
			//System.out.println("Current annotation1:" + annTerm.getAnnotations()[0].toString());
			
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
		//System.out.println("TermSp: " + term.toStringDirect());
		//System.out.println("Current Special: " + type);
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
											
					/* Just take the first annotation, because it should have exactly one - otherwise the proof-checker throws an error */
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
				/* Not nice: Assumption: If there is just one clause it doesn't start with an "or" - is that correct?*/
				if (termArg0CalcApp.getFunction().getName() == "or")
				{
					multiDisjunct = true;
				}
			}
			
			/* Initialization of the disjunct(s) */			
			if (multiDisjunct)
			{
				//His disjuncts (Works just if the clause has more than one disjunct)
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
				if (!(termArgs[i] instanceof ApplicationTerm))
				{
					throw new AssertionError("Error: The following terms should be an application term but isn't: " + termArgs[i]);				
				}
				termAppParamsApp[i] = (ApplicationTerm) termArgs[i];
				
				// OLD and WRONG: Check, if the params are correct for themselves
				// This was already done, and at this points leads to chaos on the resultStack
				// stackWalker.push(new WalkerId<Term,String>(termAppParamsApp[i],""));
				
			}

			termEdit = stackPop(type); //termAppParamsApp[0];
			
			// Editing
			for (int i = 1; i < termArgs.length; i++)
			{
				if (termAppParamsApp[i].getFunction().getName() != "@rewrite"
						&& termAppParamsApp[i].getFunction().getName() != "@intern")
				{
					throw new AssertionError("Error: An argument of @eq was neither a @rewrite nor a @intern, it was: " + termAppParamsApp[i].getFunction().getName() + ".");							
				}
				
				if (termAppParamsApp[i].getFunction().getName() == "@rewrite")
				{
					if (!(termAppParamsApp[i].getParameters()[0] instanceof AnnotatedTerm))
					{
						throw new AssertionError("Error: Expected an annotated term inside a "
								+ "rewrite-term. Random number: 47295");
					}
					termAppParamsAppIAnn = (AnnotatedTerm) termAppParamsApp[i].getParameters()[0];
					
					
					if (!(termAppParamsAppIAnn.getSubterm() instanceof ApplicationTerm))
					{
						throw new AssertionError("Error: Expected an Application-Term inside a "
								+ "Annotation of a rewrite-term. Random number: 56720");
					}
					termAppParamsAppIMayAnnApp = (ApplicationTerm) termAppParamsAppIAnn.getSubterm();
				} else
				{
					// So it's an @intern
					if (!(termAppParamsApp[i].getParameters()[0] instanceof ApplicationTerm))
					{
						throw new AssertionError("Error: Expected an Application-Term inside a "
								+ "a intern-term. Random number: 20573");
					}
					termAppParamsAppIMayAnnApp = (ApplicationTerm) termAppParamsApp[i].getParameters()[0];
				}

				
				if (termAppParamsAppIMayAnnApp.getFunction().getName() != "=")
				{
					System.out.println("A random number: 582046"); // Can be used to differ between two same-sounding errors
					throw new AssertionError("Error: The following terms should have = as function symbol, but it has: " + termAppParamsApp[i].getFunction().getName() + "\n"
							 + "Term: " + termAppParamsApp[i].toStringDirect() + " calculated from " + termArgs[i].toStringDirect()); 
				}
				
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
			if (termApp.getFunction().getName() == "+")
			{
				if (termApp.getParameters().length < 1)
					throw new AssertionError("Error 1 in add in calculateTerm with term " + term.toStringDirect());
				resultTerm = SMTAffineTerm.create(smtInterpol.numeral("0"));
				for (Term summand : termApp.getParameters())
					resultTerm = resultTerm.add(calculateTerm(summand, smtInterpol));
				return resultTerm;
			}
			
			else if (termApp.getFunction().getName() == "-")
			{
				if (termApp.getParameters().length == 1)
					return (calculateTerm(termApp.getParameters()[0], smtInterpol).negate());
				
				throw new AssertionError("Error: The term with a \"-\" didn't have 1 argument. The term was "
						+ term.toStringDirect());
			}
			
			else if (termApp.getFunction().getName() == "*")
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
			
			else if (termApp.getFunction().getName() == "/")
			{
				if (termApp.getParameters().length != 2)
					throw new AssertionError("Error 1 in div in calculateTerm with term " + term.toStringDirect());
				SMTAffineTerm divident = calculateTerm(termApp.getParameters()[0], smtInterpol);
				SMTAffineTerm divisor = calculateTerm(termApp.getParameters()[1], smtInterpol);
				
				if (divisor.isConstant())
					return divident.div(divisor.getConstant());
				
				throw new AssertionError("Error: Couldn't find the constant in the SMTAffineTerm division. "
						+ "The term was " + termApp.toStringDirect());
			}
			
			else if (termApp.getFunction().getName() == "="
					|| termApp.getFunction().getName() == "<="
					|| termApp.getFunction().getName() == "<"
					|| termApp.getFunction().getName() == ">"
					|| termApp.getFunction().getName() == ">=")
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
			return SMTAffineTerm.create(term);
		else
			throw new AssertionError("Error 3 in calculateTerm with term " + term.toStringDirect());
	}
	
	ApplicationTerm convertApp (Term term)
	{
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
			return convertApp(((AnnotatedTerm) term).getSubterm());
		
		return convertApp(term);
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
	
	// Now some pattern-match-functions.

	//Throws an error if the pattern doesn't match
	void pm_func(ApplicationTerm termApp, String pattern)
	{
		if (termApp.getFunction().getName() != pattern)
			throw new AssertionError("Error: The pattern \"" + pattern
					+ "\" was supposed to be the function symbol of " + termApp.toStringDirect() + "\n"
					+ "Instead it was " + termApp.getFunction().getName());
	}
	
	boolean pm_func_weak(ApplicationTerm termApp, String pattern)
	{
		if (termApp.getFunction().getName() != pattern)
			return false;
		return true;
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
	
	
	boolean pathFind(HashMap<SymmetricPair<Term>,Term[]> subpaths, HashMap<SymmetricPair<Term>,Term[]> premises,
			Term termStart, Term termEnd)
	{
	
		System.out.println("Searching for a way from " + termStart.toStringDirect()
				+ " to " + termEnd.toStringDirect());
//		if (termStart == termEnd)
//			return true;
		
		SymmetricPair<Term> searchPair = new SymmetricPair<Term>(termStart, termEnd);
		
		/* The reason for checking the premises before the subpaths is,
		 * that the subpaths may contain the same equality as the premises, which
		 * could lead to infinite loops.
		 */
		if(premises.containsKey(searchPair))
			return true;
		
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
		
		boolean returnVal = true;
		
		for (int i = 0; i < termStartApp.getParameters().length; i++)
		{
			returnVal = returnVal &&
					pathFind(subpaths, premises, termStartApp.getParameters()[i], termEndApp.getParameters()[i]);
		}
		
		return returnVal;
		//throw new AssertionError("Error in lemma_:CC: I have no idea how to get from "
		//	+ termStart.toStringDirect() + " to " + termEnd.toStringDirect());
	}
}