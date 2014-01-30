package de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2;

import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm; //May not be needed
import de.uni_freiburg.informatik.ultimate.logic.Term;
//import java.util.ArrayList;
//import java.util.HashMap;
import java.util.*;

public class ProofChecker extends SMTInterpol {
	
	// Not nice: returns are spread over the code, all could be in the end
	HashMap<Term, Term> pcCache; //Proof Checker Cache
	// Not nice: The level should be 0
	// Level of proof-checker-power
	int powLev = 1;
	//SMTInterpol smtInterpolGlobal;
	
	// Declarations for the Walker
	Stack<WalkerId> stackWalker = new Stack<WalkerId>();
	Stack<Term> stackResults = new Stack<Term>();
	//Not nice: Is this really necessary?:
	Stack<Annotation[]> stackAnnots = new Stack<Annotation[]>();
	//Stack<String> stackTest = new Stack<String>();
	
	public boolean check(Term res, SMTInterpol smtInterpol) {
		
		//pfpc is the ProofChecker-Program-Counter and is just needed for debugging
		//ArrayList<Integer> pfpc = new ArrayList<Integer>();
		//pfpc.add(0);
		
		//smtInterpolGlobal = smtInterpol;
		
		// Initializing the proof-checker-cache
		pcCache = new HashMap<Term, Term>();
		
		Term resCalc;
		// recursive:
		// resCalc = unfold(res, smtInterpol, pfpc);	
		// Now non-recursive:
		stackWalker.push(new WalkerId(res,""));
		WalkerId currentWalker;
		/*stackTest.push("a");
		stackTest.push("b");
		stackTest.push("c");
		System.out.println("First: " + stackTest.pop());
		System.out.println("Next: " + stackTest.pop());*/
		
		while (!stackWalker.isEmpty())
		{
			// Just for debugging
			/*for (int i = 0; i < stackWalker.size(); i++)
			{
				System.out.println("Walker(" + i + "): [" + stackWalker.elementAt(i).t.toStringDirect()
						+ "," + stackWalker.elementAt(i).s + "]");
			}
			System.out.println("");
			
			for (int i = 0; i < stackResults.size(); i++)
			{
				System.out.println("Result(" + i + "): " + stackResults.elementAt(i));
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
			//System.out.println("Größe2: " + stackResults.size());
		}		
		
		if (!stackResults.isEmpty())
		{
			resCalc = stackResults.pop();
		} else
		{
			throw new AssertionError("Error: At the end of verifying the proof, there is no result left.");
		}
		
		
		//System.out.println("Am Ende kommt heraus: " + resCalc.toStringDirect());
		
		if (resCalc == smtInterpol.term("false"))
		{
			return true;
		} else {
			return false;
		}
		
		
	}
	
	// non-recursive, not used anymore
	public Term unfold(Term res, SMTInterpol smtInterpol, ArrayList<Integer> pfpc) {
		
		// The proof-checker should use the non-recursive function:
		throw new AssertionError ("Error: Trying to use the old non-recursive function!");
		
		/* The first version of this function is recursive, later it should be non-recursive */
		/* Takes proof, returns proven formula */
		
		/* Just for debugging */
		/*
		if (pfpc.size() >= 6)
		{
			if (pfpc.get(3) == 3 && pfpc.get(4) == 6)
			{
				//System.out.println("Currently looking at: " + res.toStringDirect());
			}
		}*/
		
		/* Check the cache, if the unfolding step was already done *//*
		if (pcCache.containsKey(res))
		{
			if (pcCache.get(res) == null)
			{
				throw new AssertionError("Error: The term " + res.toString() + " was already "
						+ "calculated, but isn't in the cache.");
			}
			//System.out.println("Unfold von Term " + res.toStringDirect() 
			//		+ " ist bekannt: " + pcCache.get(res).toStringDirect());
			//System.out.println("++");
			return pcCache.get(res);
		}*/
		
		/* Just for debugging */
		
		/* Declaration of variables used later */
		/*String functionname;
		Term params[];
		Term paramsCalc[]; //parameters after calculation
		Term paramCheck = null; //parameter that is getting checked.
		//Not nice: Initialization as null.
		AnnotatedTerm innerAnnTerm;
		ApplicationTerm innerAppTerm;
		AnnotatedTerm annTerm;
		Term pivots[];*/		
		
		/* Look at the class of the term and treat each different */
		/*if (res instanceof ApplicationTerm) 
		{			*/
			/* res is an ApplicationTerm */
//			ApplicationTerm appTerm = (ApplicationTerm) res;
//			
//			/* Get the function and parameters */
//			functionname = appTerm.getFunction().getName();
//			params = appTerm.getParameters();
//			paramsCalc = new Term[params.length]; //The arguments of the resolution function after the unfolding-calculation
//			
			/* Just for debugging */
			//System.out.println("Currently looking at: " + functionname);
			//System.out.println("Current PF-Program-Counter: " + pfpc.toString());
			
			/* Look at the function of the application-term and treat each different */
//			switch (functionname)
//			{
//			case "@res":
//				/* Not nice: This function is expected to have as first argument the clause which is used
//				 * further, after the pivots are deleted.
//				 */
//				
//				/*if (pfpc.size() >= 5)
//				{
//					if (pfpc.get(3) == 3 && pfpc.get(4) == 6 && pfpc.get(5) >= 1 && pfpc.get(5) <= 2)
//					{
//						System.out.println("Resolution: " + appTerm.toStringDirect());
//					}
//				}*/
//
//				
//				ArrayList<Term> disjunctsAdd = new ArrayList<Term>();
//				
//				/* Get the arguments and pivots */
//				pivots = new Term[params.length]; //The zeroth entry has no meaning. 
//				
//				for (int i = 0; i < params.length; i++)
//				{
//					/* get pivot: start */
//					if (params[i] instanceof AnnotatedTerm)
//					{
//						/* One should check this */						
//						innerAnnTerm = (AnnotatedTerm) params[i];
//						
//						/* Check if it is a pivot-annotation */
//						if (innerAnnTerm.getAnnotations()[0].getKey() != ":pivot")
//						{
//							throw new AssertionError("Error: The annotation has key " + innerAnnTerm.getAnnotations()[0].getKey() + " instead of :pivot, " 
//									+ "which is required. It's value is: " + innerAnnTerm.getAnnotations()[0].getValue());
//						}						
//												
//						/* Just take the first annotation, because it should have exactly one - otherwise the proof-checker throws a warning */
//						if (innerAnnTerm.getAnnotations()[0].getValue() instanceof AnnotatedTerm
//								 ||
//								 innerAnnTerm.getAnnotations()[0].getValue() instanceof ApplicationTerm
//								 ||
//								 innerAnnTerm.getAnnotations()[0].getValue() instanceof ConstantTerm)
//						{							
//							pivots[i] = (Term) innerAnnTerm.getAnnotations()[0].getValue();
//							//System.out.println("Das Pivot ist: " + pivots[i].toStringDirect());
//						} else
//						{
//							throw new AssertionError("Error: The following object was supposed to be a known term but isn't: " + 
//									innerAnnTerm.getAnnotations()[0].getValue().toString() + "It is:" + 
//									innerAnnTerm.getAnnotations()[0].getValue().getClass().getCanonicalName());
//						}
//						
//						if (innerAnnTerm.getAnnotations().length > 1)
//						{
//							throw new AssertionError("Error: Expected number of annotations was 1, instead it is " + innerAnnTerm.getAnnotations().length + " in this term " + innerAnnTerm);
//						}
//					}
//					/* get pivot: end */
//					
//					//Calculating in the arguments (of the resolution) proven formulas
//					//System.out.println("Olive: Berechne: " + params[i].toString());
//					pfpc.add(0);
//					paramsCalc[i] = unfold(params[i], smtInterpol, pfpc);
//					pfpc = afterUnfoldPc(pfpc);
//					//System.out.println("Olive: Ergibt: " + paramsCalc[i].toStringDirect());
//				}
//				
//				// Debug
//				//System.out.println("Nach Abarbeiten der unfolds ist PC = " + pfpc);
//				
//				
//				/* OLD: Searching the pivots and deleting them in the first clause */
//				/* Check if the pivots are really in the second argument */
//				AnnotatedTerm[] paramsCut = new AnnotatedTerm[paramsCalc.length];
//				
//				for (int i = 1; i < pivots.length; i++)
//				{
//					/* paramsCalc still includes the pivot-annotation. This has to be cutted out */
//					if (paramsCalc[i] instanceof AnnotatedTerm)
//					{
//						paramsCut[i] = (AnnotatedTerm) paramsCalc[i];
//					} else	{
//						throw new AssertionError("Error: This code really shouldn't be reachable! A random number: 23742");
//					}
//					
//					// TODO
//					// TODO: Can it be that e.g. pivot 4 deletes a disjunct which pivot 1 added?
//					// TODO
//					/* The search for the pivot in the term with the pivot: */
//					if (paramsCut[i].getSubterm() == pivots[i])
//					{
//						// The Pivot-term has one disjunct
//						//System.out.println("Konnte das Pivot " + pivots[i] + " in " + paramsCalc[i].toStringDirect() + " finden.");
//						//Term[] disjunctsAdd = new Term[0];  
//					} else if (paramsCut[i].getSubterm() instanceof ApplicationTerm && powLev == 0)
//					{
//						// The pivot term has more than one disjunct
//						ApplicationTerm paramsCutIApp = (ApplicationTerm) paramsCut[i].getSubterm();
//						 
//						if (paramsCutIApp.getFunction().getApplicationString() != "or")
//						{
//							throw new AssertionError("Error: Hoped for a disjunction while searching the pivot " 
//									+ pivots[i] + " in " + paramsCalc[i].toStringDirect() + ". But found "
//									 + "a function with that symbol: " + paramsCutIApp.getFunction().getApplicationString());
//						} 
//						
//						//Term[] disjunctsAdd = new Term[paramsCutIApp.getParameters().length-1];
//						// TODO: Is there a need to find out if two terms are the same?
//						
//						// How the following for-loop works:
//						// For disjunct we have to check if it's the pivot, if not it has to be added later.
//						// If it is, only then k won't be counted up, which avoids the error.
//						// That means if we go out of the loop without an error, we know, that the pivot has been found.
//						int k = 0; // Counts through the disjuncts 
//						for (int j = 0; j < disjunctsAdd.size(); j++)
//						{
//							if (paramsCutIApp.getParameters()[j] != pivots[i])
//							{
//								if (k < disjunctsAdd.size())
//								{
//									disjunctsAdd.add(paramsCutIApp.getParameters()[j]);
//									k++;
//								} else
//								{
//									throw new AssertionError("Error: couldn't find the pivot "+ pivots[i].toStringDirect() 
//											+ " in the disjunction " +  paramsCutIApp.toStringDirect());
//								}
//								
//							} else
//							{
//								System.out.println("Found the pivot " + pivots[i].toStringDirect() 
//										+ "in the disjunction" + paramsCutIApp.toStringDirect() + "!");
//							}
//						}
//					} else if (powLev > 0)
//					{
//						//System.out.println("Warning: The level of power had an effect.");
//					} else
//					{
//						throw new AssertionError("Error: Konnte das Pivot " + pivots[i] + " NICHT in " + paramsCalc[i].toStringDirect() + " finden.");
//						
//					}
//				}
//				
//				// Not nice: Not tested: Clause has just one disjunct (and therefore no "or")
//				
//				Term disjuncts[];
//				Term innerParams[];
//				//String pivotstr = "";
//				//String disjunctstr = "";
//								
//				boolean multiDisjunct = false;
//				innerAppTerm = null; //Not nice, but it will just be needed when multiDisjunct holds and then it is initialized properly
//				if (paramsCalc[0] instanceof ApplicationTerm)
//				{
//					innerAppTerm = (ApplicationTerm) paramsCalc[0]; //First Term: The one which gets resoluted
//					
//					/* Does the clause have one or more disjuncts? */
//					/* Not nice: Assumption: If there is just one clause it doesn't start with an "or" - is that correct?*/
//					if (innerAppTerm.getFunction().getName() == "or")
//					{
//						multiDisjunct = true;
//					}
//				}
//				
//				/* Initialization of the disjunct(s) */
//				
//				if (multiDisjunct)
//				{
//					innerParams = innerAppTerm.getParameters();	//His disjuncts (Works just if the clause has more than one disjunct)
//					disjuncts = new Term[innerParams.length];
//					for (int i = 0; i < innerParams.length; i++)
//					{
//						disjuncts[i] = innerParams[i];
//					}
//				} else {
//					disjuncts = new Term[1];
//					disjuncts[0] = paramsCalc[0];
//				}
//				
//				boolean[] disjunctsOK = new boolean[disjuncts.length];
//				
//				if (multiDisjunct)
//				{
//					for (int i = 0; i < disjuncts.length; i++)
//					{
//						disjunctsOK[i] = true;
//					}
//				} else {
//					disjunctsOK[0] = true;
//				}
//				
//				
//				if (true)
//					
//					/* Compare all disjuncts with pivots (un-annotated) */
//					for (int i = 0; i < disjuncts.length; i++)
//					{
//						
//						/* Delete the disjunct if there is a fitting pivot */
//						for (int j = 1; j < pivots.length; j++) //Not nice: Expects (j != 0), that the first clause is the one which gets resoluted.
//						{
//							/* Check if one negates the other, if so delete the disjunct */
//							//System.out.println("Vergleiche: " + disjuncts[i].toStringDirect() + " vs. " + pivots[j].toStringDirect());
//							//System.out.println("Mit: " + disjuncts[i].toStringDirect() + " vs. " + negate(pivots[j], smtInterpol).toStringDirect());
//							//System.out.println("Ohne: " + negate(disjuncts[i], smtInterpol) + " vs. " + pivots[j]);					
//							if (disjuncts[i] == negate(pivots[j], smtInterpol)									
//									)
//							{
//								//System.out.println("Treffer! \n");
//								disjunctsOK[i] = false;
//							} /*else
//							{
//								System.out.println("Kein Treffer \n");
//							}	*/						
//						}						
//					}
//					
//					/* Count the remaining disjuncts */
//					int c = 0;
//					for (int i = 0; i < disjuncts.length; i++)
//					{
//						if (disjunctsOK[i])
//							c++;
//					}
//					//System.out.println("Von " + disjuncts.length + " Disjunktionen sind noch "
//					//		+ c + " übrig.");
//					//System.out.println("c = " + c);
//					c += disjunctsAdd.size();
//					//System.out.println("c = " + c);
//					/*if (disjunctsAdd.size() > 0)
//					{
//						System.out.println("\n Konnte mit Liste der Größe " + disjunctsAdd.size() + " umgehen. \n");
//					}*/
//					
//					/* Different handling for a different number of conjuncts is needed */
//					switch (c)
//					{
//					case 0:	
//						//System.out.println("Red");
//						pcCache.put(res, smtInterpol.term("false"));
//						return smtInterpol.term("false");
//					case 1:
//						//System.out.println("Green");
//						for (int i = 0; i < disjuncts.length; i++)
//						{
//							if (disjunctsOK[i])
//							{	
//								if (pfpc.size() >= 5)
//								{
//									if (pfpc.get(3) == 3 && pfpc.get(4) == 6)
//									{
//										System.out.println("ReturningA: " + disjuncts[i].toStringDirect());
//									}
//								}
//
//								pcCache.put(res, disjuncts[i]);
//								return disjuncts[i];
//							}
//						}
//						
//						// So the one element has to be in the list
//						System.out.println("ReturningB: " + disjunctsAdd.get(0).toStringDirect());
//						pcCache.put(res, disjunctsAdd.get(0));
//						return disjunctsAdd.get(0);
//					default:
//						//System.out.println("Blue");
//						// Note nice: The whole case is untested.
//						
//						//Build an array that contains only the disjuncts, that have to be returned
//						Term[] disjunctsReturn = new Term[c];
//						int d = 0; //Counts through the disjuncts
//						//System.out.println("Counter...");
//						for (int i = 0; i < disjuncts.length; i ++)
//						{
//							if (disjunctsOK[i])
//							{
//								if (d < c)
//								{
//									disjunctsReturn[d] = disjuncts[i];
//									d++;
//								} else {
//									throw new AssertionError("Error: A total unexpected miscalculation occured. Random number: 638402");
//								}
//							} /*else
//							{
//								System.out.println("| (" + d + "," + i + ")");
//							}*/
//						}
//						if (disjunctsReturn.length - d != disjunctsAdd.size())
//						{
//							throw new AssertionError("Error: I'd like to fill up the to be returned disjuncts with "
//									+ "the list of \"to be added\"-disjuncts, but the size doesn't fit. The list has "
//									+ "size " + disjunctsAdd.size() + " and there is/are " 
//									+ (disjunctsReturn.length - d) + " = " + disjunctsReturn.length + " - "
//									+ d + " free space(s).");									
//						}
//						
//						// Now add the "to be added"-disjuncts
//						int p = 0; //counts through the list
//						while (d < disjunctsReturn.length)
//						{
//							disjunctsReturn[d] = disjunctsAdd.get(p);
//							//disjunctsReturn[d] = disjunctsAdd.remove(0); Could bet more effective, but is untested
//							d++;
//							p++;
//						}
//						
//						/*if (pfpc.size() >= 5)
//						{
//							if (pfpc.get(3) == 3 && pfpc.get(4) == 6)
//							{
//								System.out.println("Returning: " + disjunctsReturn.toString());
//							}
//						}*/
//						pcCache.put(res, smtInterpol.term("or", disjunctsReturn));						
//						return smtInterpol.term("or", disjunctsReturn);
//					}
//				/*} else
//				{
//					throw new AssertionError("Expected an application term inside the first argument, but the following term doesn't have one: " + params[0]);
//					//innerAppTerm = (ApplicationTerm) smtInterpol.term("false");
//				}*/
//				
//			case "@eq":
//				/* Expected: The first argument is unary each other argument binary.
//				 * Then for each n>=0 the nth argument describes one term rewritten by an equal new term, 
//				 * where the two terms
//				 *  - nth argument's last argument
//				 *  - (n+1)th argument's first argument 
//				 *  are the same and for each n >= 1:
//				 *  - nth argument's first argument is rewritten by the equal term's
//				 *    nth argument's second argument. */
//				/* This works just for rewrite, not for intern */
//
//				ApplicationTerm[] paramsApp = new ApplicationTerm[params.length]; //Parameters of @eq, uncalculated, application terms
//				ApplicationTerm paramsCalcIApp; //The ith parameter of @eq, calculated, application term
//						
//				for (int i = 0; i < params.length; i++)
//				{
//					pfpc.add(0);
//					paramsCalc[i] = unfold(params[i], smtInterpol, pfpc);	//Parameters of @eq, calculated, terms
//					pfpc = afterUnfoldPc(pfpc);
//					
//					if (params[i] instanceof ApplicationTerm)
//					{
//						paramsApp[i] = (ApplicationTerm) params[i];
//					} else
//					{
//						throw new AssertionError("Error: The following terms should be an application term but isn't: " + params[i]);
//					}
//					/* The first argument is unary, and requires therefore different treatment */
//					if (i == 0)
//						paramCheck = paramsCalc[0];
//					else
//					{
//						/* It has to be an ApplicationTerm with function symbol "=". Everything else should throw an error */
//						if (paramsCalc[i] instanceof ApplicationTerm)
//						{
//							paramsCalcIApp = (ApplicationTerm) paramsCalc[i];										
//						} else
//						{
//							throw new AssertionError("Expected an application term inside any rewrite-term, but the following term doesn't have one: " + paramsCalc[i]);							
//						} 
//												
//						if (paramsCalcIApp.getFunction().getApplicationString() != "=")
//						{
//							System.out.println("A random number: 582046"); // Can be used to differ between two same-sounding errors
//							throw new AssertionError("Error: The following terms should have = as function symbol, but it has: " + paramsCalcIApp.getFunction().getApplicationString() + "\n"
//									 + "Term: " + paramsCalcIApp.toStringDirect() + " calculated from " + params[i].toStringDirect()); 
//						}
//						
//						
//						if (paramsApp[i].getFunction().getName() != "@rewrite" && paramsApp[i].getFunction().getName() != "@intern")
//						{
//							throw new AssertionError("Error: An argument of @eq was neither a @rewrite nor a @intern, it was: " + paramsApp[i].getFunction().getName() + ".");							
//						}
//							
//						//Note: paramCheck was declared in the last for-loop
//						if (paramsApp[i].getFunction().getName() == "@rewrite" && paramCheck != paramsCalcIApp.getParameters()[0])
//						{
//							throw new AssertionError("Error: The following terms should be the same but aren't: " + paramCheck + " vs. " + paramsCalcIApp.getParameters()[0]);
//						} 
//						else if (paramsApp[i].getFunction().getName() == "@rewrite")
//						{
//							/* Preparation for the next comparison */
//							paramCheck = paramsCalcIApp.getParameters()[1];								
//						}
//						else if (paramsApp[i].getFunction().getName() == "@intern") //The equality is not needed 
//						{
//							Term rewrittenTerm = internalRewrite(paramCheck, paramsCalcIApp.getParameters()[0], paramsCalcIApp.getParameters()[1], smtInterpol);
//							
//							if (rewrittenTerm == paramCheck){
//								throw new AssertionError("Error: Couldn't understand the internal rewrite of " + paramCheck.toStringDirect() + " with the rule: " + 
//										paramsCalcIApp.getParameters()[0].toStringDirect() + " --> " + paramsCalcIApp.getParameters()[1].toStringDirect());
//							}
//							
//							//System.out.println("Alter Term: " + paramCheck.toStringDirect());
//							//System.out.println("Gebe zurück: " + rewrittenTerm.toStringDirect());
//							pcCache.put(res, rewrittenTerm);
//							return rewrittenTerm;
//							
//							/*
//							// First Case: They are just the same 
//							if (paramCheck == paramsCalcIApp.getParameters()[0])
//							{
//								// Preparation for the next comparison 
//								paramCheck = paramsCalcIApp.getParameters()[1];
//							}
//							
//							// Second case: Partial rewrite of the first term. 
//							// Not nice: Assumption: The rewrite goes at maximum two layers deep 
//							// Not nice: Maybe missing rules /
//							
//							else 
//							{
//								if (!(paramCheck instanceof ApplicationTerm))							
//								{
//									throw new AssertionError("Error: The following term was assumed to be an application term but isn't: " + paramCheck);
//								}
//								ApplicationTerm paramCheckApp = (ApplicationTerm) paramCheck;
//								
//								if (paramCheckApp.getParameters()[0] == paramsCalcIApp.getParameters()[0])
//								{
//									// Preparation for the next comparison 
//									paramCheck = smtInterpol.term(paramCheckApp.getFunction().getName(), paramsCalcIApp.getParameters()[1]);							
//								} else
//								{
//									// Last chance: Check one layer deeper 
//									throw new AssertionError("Error: Couldn't understand the internal rewrite of " + paramCheck.toStringDirect() + " with the rule: " + 
//											paramsCalcIApp.getParameters()[0].toStringDirect() + " --> " + paramsCalcIApp.getParameters()[1].toStringDirect());
//								}
//							}*/
//						}
//						else
//						{
//							System.out.println("This code shouldn't be reachable, a random number: 473957");
//						}
//					}
//				}
//				pcCache.put(res, paramCheck);
//				return paramCheck;
//				
//			case "@lemma":
//				System.out.println("Believed as true: " + appTerm.toStringDirect() + " ."); //TODO: Implement rule-reader
//				
//				// If possible return the un-annotated version
//				// Warning: Code duplicates (Random number: 498255) 
//				if (appTerm.getParameters()[0] instanceof AnnotatedTerm)
//				{
//					innerAnnTerm = (AnnotatedTerm) appTerm.getParameters()[0];
//					pcCache.put(res, innerAnnTerm.getSubterm());
//					return innerAnnTerm.getSubterm();
//				} else
//				{
//					throw new AssertionError("Expected an annotated term inside any lemma-term, but the following term doesn't have one: " + appTerm.getParameters()[0]);
//				}
//				
//			case "@tautology":
//				System.out.println("Believed as true: " + appTerm.toStringDirect() + " ."); //TODO: Implement rule-reader
//				
//				// If possible return the un-annotated version
//				// Warning: Code duplicates (Random number: 498255)
//				if (appTerm.getParameters()[0] instanceof AnnotatedTerm)
//				{
//					innerAnnTerm = (AnnotatedTerm) appTerm.getParameters()[0];
//					pcCache.put(res, innerAnnTerm.getSubterm());
//					return innerAnnTerm.getSubterm();
//				} else
//				{
//					throw new AssertionError("Expected an annotated term inside any tautology-term, but the following term doesn't have one: " + appTerm.getParameters()[0]);
//					//return appTerm.getParameters()[0];
//				}
//				
//			case "@asserted":
//				System.out.println("Believed as asserted: " + appTerm.getParameters()[0].toStringDirect() + " .");
//				/* Just return the part without @asserted */ 
//				pcCache.put(res, appTerm.getParameters()[0]);
//				return appTerm.getParameters()[0]; 
//				//break;
//				
//			case "@rewrite":
//				
//				/* At this point there is no access to the other arguments, so it
//				 * can't be checked here if the first argument is the same as the last argument of 
//				 * the last argument. */
//				
//				/* Treatment:
//				 *  - At first check if the rewrite rule was correctly executed.
//				 *  - Secondly, remove the @rewrite and the annotation for later uses in the @eq-function.
//				 */
//				
//				/* Get access to the internal terms */
//				if (appTerm.getParameters()[0] instanceof AnnotatedTerm)
//				{
//					innerAnnTerm = (AnnotatedTerm) appTerm.getParameters()[0]; //The annotated term inside the rewrite-term
//				} else
//				{
//					throw new AssertionError("Expected an annotated term inside any rewrite-term, but the following term doesn't have one: " + appTerm.getParameters()[0]);					
//				}
//				if (innerAnnTerm.getSubterm() instanceof ApplicationTerm)
//				{
//					innerAppTerm = (ApplicationTerm) innerAnnTerm.getSubterm(); //The application term inside the annotated term inside the rewrite-term
//				} else
//				{
//					throw new AssertionError("Expected an application term inside the annotated term inside a rewrite-term, but the following term is none: " + innerAnnTerm.getSubterm());					
//				}
//				if (innerAppTerm.getFunction().getApplicationString() != "=")
//				{
//					System.out.println("A random number: 440358"); // Can be used to differ between two same-sounding errors
//					throw new AssertionError("Error: The following terms should have = as function symbol, but it has: " + innerAppTerm.getFunction().getApplicationString());					
//				}
//				
//				
//				/* Read the rule and handle each differently */
//				if (innerAnnTerm.getAnnotations()[0].getKey() == ":strip")
//				{
//					if (innerAppTerm.getParameters()[0] instanceof AnnotatedTerm)
//					{
//						AnnotatedTerm stripAnnTerm = (AnnotatedTerm) innerAppTerm.getParameters()[0]; //Term which has to be stripped, annotated term
//						if (stripAnnTerm.getSubterm() != innerAppTerm.getParameters()[1])
//						{
//							throw new AssertionError("Error: Couldn't verify a strip-rewrite. Those two terms should be the same but arent" 
//									+ stripAnnTerm.getSubterm() + "vs. " + innerAppTerm.getParameters()[1] + ".");
//						} /*else // Not needed
//						{
//							System.out.println("Verified a strip-rule");
//						}*/
//					} else
//					{
//						throw new AssertionError("Error: The first argument of a rewrite equality was expected to be " 
//								+ "an annotated term, because the rule is strip. The error-causing term is" + innerAppTerm.getParameters()[0] + ".");
//					}
//				} else if (innerAnnTerm.getAnnotations()[0].getKey() == ":notSimp")
//				{
//					// The first argument of the rewrite has to be the double-negated version of the second argument
//					ApplicationTerm innerAppTermFirstNeg; //The first negation inside the first argument
//					ApplicationTerm innerAppTermSecondNeg; //The second negation inside the first argument
//					
//					// Check syntactical correctness
//					if (!(innerAppTerm.getParameters()[0] instanceof ApplicationTerm))
//					{
//						throw new AssertionError("Error: " + innerAppTerm.getParameters()[0].toString() 
//								+ "should be a double-negated ApplicationTerm but isn't even an ApplicationTerm. "
//								+ "It's of the class: " + innerAppTerm.getParameters()[0].getClass().getName());
//					}
//					
//					innerAppTermFirstNeg = (ApplicationTerm) innerAppTerm.getParameters()[0];
//					
//					if (!((innerAppTermFirstNeg.getParameters()[0] instanceof ApplicationTerm) 
//							&& (innerAppTermFirstNeg.getFunction().getName() == "not")))
//					{
//						throw new AssertionError("Error: " + innerAppTerm.getParameters()[0].toString() 
//								+ "should be a double-negated ApplicationTerm, it is an ApplicationTerm, but "
//								+ "either the the function isn't \"not\" or the inside is no ApplicationTerm. "
//								+ "The function is " + innerAppTermFirstNeg.getFunction().getName() + " and the "
//								+ "class of the subterm is: " + innerAppTermFirstNeg.getParameters()[0].getClass().getName());
//								
//					}
//					
//					innerAppTermSecondNeg = (ApplicationTerm) innerAppTermFirstNeg.getParameters()[0];
//					
//					if (!(innerAppTermSecondNeg.getFunction().getName() == "not"))
//					{
//						throw new AssertionError("Error: " + innerAppTerm.getParameters()[0].toString() 
//								+ "should be a double-negated ApplicationTerm, but it is just once negated. The inner"
//								+ "isn't \"not\", it's " + innerAppTermSecondNeg.getFunction().getName() + ".");
//					}
//					
//					// Check if the rule was executed correctly
//					
//					if (innerAppTermSecondNeg.getParameters()[0] != innerAppTerm.getParameters()[1])
//					{
//						throw new AssertionError("Error: The rule \"notSimp\" couldn't be verified, because the following "
//								+ "two terms aren't the same: " + innerAppTermSecondNeg.getParameters()[0].toString() 
//								+ " and " + innerAppTerm.getParameters()[1].toStringDirect() + ".\n"
//								+ "The original term was: " + appTerm.toStringDirect());
//					}
//					
//					// Important: The return is done later, the following is false: 
//					// return innerAppTerm.getParameters()[1];
//					
//				} else
//				{
//					System.out.println("Can't handle the following rule " + innerAnnTerm.getAnnotations()[0].getKey() + ", therefore...");
//					System.out.println("...believed as alright to be rewritten: " + appTerm.getParameters()[0].toStringDirect() + " ."); //Not nice: Too few rules
//				}				
//			
//				
//				// The second part, cut the @rewrite and the annotation out, both aren't needed for the @eq-function.
//				pcCache.put(res, innerAnnTerm.getSubterm());
//				return innerAnnTerm.getSubterm();				
//				
//				
//			case "@intern":
//				
//				/* At this point there is no access to the other arguments, so it
//				 * can't be checked here if the first argument is the same as the last argument of 
//				 * the last argument. */
//				
//				System.out.println("Believed as alright to be (intern) rewritten: " + appTerm.getParameters()[0].toStringDirect() + " ."); //TODO: Implement rule-reader
//				pcCache.put(res, appTerm.getParameters()[0]);
//				return appTerm.getParameters()[0];
//				
//			case "@split":
//				// TODO: Check if the first argument contains the second argument
//				
//				/* At this point there is no access to the other arguments, so it
//				 * can't be checked here if the first argument is the same as the last argument of 
//				 * the last argument. */
//				
//				//return unfold(appTerm.getParameters()[1], smtInterpol);
//				//System.out.println("Split hat " + appTerm.getParameters().length + " Argumente.");
//				//System.out.println("Splitte " + appTerm.getParameters()[0].toString() + " und nehme " + appTerm.getParameters()[1].toString());
//				pcCache.put(res, appTerm.getParameters()[1]);
//				return appTerm.getParameters()[1]; //Not nice: Kann da auch etwas stehen was eigentlich aufgefaltet werden sollte?
//				
//			case "@clause":
//				//throw new AssertionError("Error: The routine for the function " + functionname + " is under construction.");
//				//System.out.println("Clause erreicht!"); //: " + appTerm.toStringDirect());				
//				
//				/* Check if the parameters of clause are two disjunctions (which they should be) */
//				
//				ApplicationTerm paramDisjunct1; //The first Parameter of clause, which is a disjunct
//				ApplicationTerm paramDisjunct2;
//				
//				if (appTerm.getParameters().length != 2)
//				{
//					throw new AssertionError("Error: The clause term has not 2 parameters, it has " 
//							+ appTerm.getParameters().length + ". The term is " + appTerm.toString());
//				}
//								
//
//				pfpc.add(0);
//				Term param1Calc = unfold(appTerm.getParameters()[0], smtInterpol, pfpc);
//				pfpc = afterUnfoldPc(pfpc);				
//
//				pfpc.add(0);
//				Term param2Calc = unfold(appTerm.getParameters()[1], smtInterpol, pfpc);
//				pfpc = afterUnfoldPc(pfpc);
//				
//				
//				if (!(param1Calc instanceof ApplicationTerm)
//					|| !(param2Calc instanceof ApplicationTerm))
//				{
//					throw new AssertionError("Error: The clause-term has one parameter which isn't an application"
//							+ "term. The first parameter " + param1Calc + " is of the class"
//							+ param1Calc.getClass().getName() + " and the second paramter " 
//							+ param2Calc + " is of the class "
//							+ param2Calc.getClass().getName() + ".");							
//				}
//				
//				paramDisjunct1 = (ApplicationTerm) param1Calc;
//				paramDisjunct2 = (ApplicationTerm) param2Calc;				
//				
//				if (paramDisjunct1.getFunction().getApplicationString() != "or"
//						|| paramDisjunct2.getFunction().getApplicationString() != "or")
//					{
//						throw new AssertionError("Error: The clause-term has one parameter which isn't a disjunction"
//								+ ". The first parameter " + paramDisjunct1 + " has the function symbol "
//								+ paramDisjunct1.getFunction().getApplicationString() + " and the second paramter " 
//								+ paramDisjunct2 + " has the function symbol "
//								+ paramDisjunct2.getFunction().getApplicationString() + ".");							
//					}
//											
//				
//				/* Check if the clause operation was correct. Each later disjunct has to be in the first disjunction.
//				 *  Actually more has to hold, but this is enough for the proof to be correct.
//				 */
//				
//				Term[] paramDisjunct1Disjuncts = paramDisjunct1.getParameters(); //Just needed to fasten things up.
//				Term[] paramDisjunct2Disjuncts = paramDisjunct2.getParameters();
//				
//				for (int i = 0; i < paramDisjunct2Disjuncts.length; i++)
//				{
//					boolean found = false;
//					for (int j = 0; j < paramDisjunct1Disjuncts.length; j++)
//					{
//						if (paramDisjunct1Disjuncts[j] == paramDisjunct2Disjuncts[i])
//						{
//							found = true;
//						}
//					}
//					if (!found)
//					{
//						throw new AssertionError("Error: Couldn't find the disjunct " 
//								+ paramDisjunct2Disjuncts[i].toString() + " in the disjunction "
//								+ paramDisjunct1.toString() + ".");
//					}
//				}
//				
//												
//				pcCache.put(res, paramDisjunct2);
//				return paramDisjunct2;
//				
//			default:
//				if (!(functionname.startsWith("@")))
//				{
//					// Not nice: The Proof-Checker shouldn't do that
//					System.out.println("Out of mysterious reasons the Proof-Checker made contact with "
//							+ "the function symbol " + functionname + ". The Proof-Checker will take a step back.");
//					System.out.println("The mysterious term is: " + appTerm.toStringDirect());
//					pcCache.put(res, appTerm);
//					return appTerm;
//				}
//				
//				throw new AssertionError("Error: The Proof-Checker has no routine for the function " + functionname + "."
//						+ "The error-causing term is " + appTerm);
//			}
//			
//		} else if (res instanceof AnnotatedTerm) {
//			/* res is an AnnotatedTerm */
//			
//			/* Annotations no more get just removed, this was incorrect */
//			
//			/* Assumption: There is no need to unfold stuff HERE inside an annotation 
//			 * (because if that's needed the function on the outside will take care */
//			/* This assumption may be wrong! */
//			
//			annTerm = (AnnotatedTerm) res;
//			
//			pcCache.put(res, smtInterpol.annotate(unfold(annTerm.getSubterm(), smtInterpol, pfpc), annTerm.getAnnotations()));
//			return smtInterpol.annotate(unfold(annTerm.getSubterm(), smtInterpol, pfpc), annTerm.getAnnotations());
//			
//		} else { 
//			throw new AssertionError("Error: The Proof-Checker has no routine for the class " + res.getClass() + ".");
//		}
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


	public Term internalRewrite(Term bigTerm, Term oldTerm, Term newTerm, SMTInterpol smtInterpol)
	{
		/* This function will dig into the bigFormula,
		 * find each occurence of oldTerm and will replace it with newTerm. */
		if (bigTerm == oldTerm)
		{
			return newTerm;
		}
		if (bigTerm instanceof AnnotatedTerm)
		{
			AnnotatedTerm bigTermAnn = (AnnotatedTerm) bigTerm;
			
			return smtInterpol.annotate(
					internalRewrite(bigTermAnn.getSubterm(), oldTerm, newTerm, smtInterpol), 
					bigTermAnn.getAnnotations());
		} 
		if (bigTerm instanceof ApplicationTerm)
		{
			ApplicationTerm bigTermApp = (ApplicationTerm) bigTerm;
			Term[] paramsRewrite = new Term[bigTermApp.getParameters().length];
			for (int i = 0; i < paramsRewrite.length; i++)
			{
				paramsRewrite[i] = internalRewrite(bigTermApp.getParameters()[i], oldTerm, newTerm, smtInterpol);
			}			
			
			return smtInterpol.term(
					bigTermApp.getFunction().getApplicationString(),
					paramsRewrite);
		}
		
		if (bigTerm instanceof ConstantTerm)
		{
			return bigTerm;
		}
		
		throw new AssertionError("Error: Couldn't handle the internal rewrite of " + bigTerm.toString() 
				+ ", because it has the class " + bigTerm.getClass().getName());
	}
	
	//Does ProgramCounterStuff and unfolding
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
			//System.out.println("Unfold von Term " + res.toStringDirect() 
			//		+ " ist bekannt: " + pcCache.get(res).toStringDirect());
			//System.out.println("++");
			stackResults.push(pcCache.get(term));
		}
				
		/* Declaration of variables used later */
		String functionname;
		//Term params[];
		//Term paramsCalc[]; //parameters after calculation
		//Term paramCheck = null; //parameter that is getting checked.
		//Not nice: Initialization as null.
		AnnotatedTerm innerAnnTerm;
		ApplicationTerm innerAppTerm;
		AnnotatedTerm annTerm;
		Term pivots[];		
		
		/* Look at the class of the term and treat each different */
		if (term instanceof ApplicationTerm) 
		{			
			/* It is an ApplicationTerm */
			ApplicationTerm appTerm = (ApplicationTerm) term;
			
			/* Get the function and parameters */
			functionname = appTerm.getFunction().getName();
			//params = appTerm.getParameters();
			//paramsCalc = new Term[params.length]; //The arguments of the resolution function after the unfolding-calculation
			
			/* Just for debugging */
			//System.out.println("Currently looking at: " + functionname);
			//System.out.println("Current PF-Program-Counter: " + pfpc.toString());
			
			/* Look at the function of the application-term and treat each different */
			switch (functionname)
			{
			case "@res":
				/* Alright: This function is expected to have as first argument the clause which is used
				 * further, after the pivots are deleted.
				 */
				
				stackWalker.push(new WalkerId(appTerm, "res"));
				stackWalker.push(new WalkerId(appTerm, "calcParams"));
				break;
				
			case "@eq":
				stackWalker.push(new WalkerId(appTerm, "eq"));
				stackWalker.push(new WalkerId(appTerm, "calcParams"));
				break;
				
			case "@lemma":
				System.out.println("Believed as true: " + appTerm.toStringDirect() + " ."); //TODO: Implement rule-reader
				
				// If possible return the un-annotated version
				// Warning: Code duplicates (Random number: 498255) 
				if (appTerm.getParameters()[0] instanceof AnnotatedTerm)
				{
					innerAnnTerm = (AnnotatedTerm) appTerm.getParameters()[0];
					pcCache.put(term, innerAnnTerm.getSubterm());
					stackResults.push(innerAnnTerm.getSubterm());
				} else
				{
					throw new AssertionError("Expected an annotated term inside any lemma-term, but the following term doesn't have one: " + appTerm.getParameters()[0]);
				}
				break;
				
			case "@tautology":
				System.out.println("Believed as true: " + appTerm.toStringDirect() + " ."); //TODO: Implement rule-reader
				
				// If possible return the un-annotated version
				// Warning: Code duplicates (Random number: 498255)
				if (appTerm.getParameters()[0] instanceof AnnotatedTerm)
				{
					innerAnnTerm = (AnnotatedTerm) appTerm.getParameters()[0];
					pcCache.put(term, innerAnnTerm.getSubterm());
					stackResults.push(innerAnnTerm.getSubterm());
				} else
				{
					throw new AssertionError("Expected an annotated term inside any tautology-term, but the following term doesn't have one: " + appTerm.getParameters()[0]);
					//return appTerm.getParameters()[0];
				}
				break;
				
			case "@asserted":
				System.out.println("Believed as asserted: " + appTerm.getParameters()[0].toStringDirect() + " .");
				/* Just return the part without @asserted */ 
				pcCache.put(term, appTerm.getParameters()[0]);
				stackResults.push(appTerm.getParameters()[0]); 
				break;
				
			case "@rewrite":
				
				/* At this point there is no access to the other arguments, so it
				 * can't be checked here if the first argument is the same as the last argument of 
				 * the last argument. */
				
				/* Treatment:
				 *  - At first check if the rewrite rule was correctly executed.
				 *  - Secondly, remove the @rewrite and the annotation for later uses in the @eq-function.
				 */
				
				/* Get access to the internal terms */
				if (appTerm.getParameters()[0] instanceof AnnotatedTerm)
				{
					innerAnnTerm = (AnnotatedTerm) appTerm.getParameters()[0]; //The annotated term inside the rewrite-term
				} else
				{
					throw new AssertionError("Expected an annotated term inside any rewrite-term, but the following term doesn't have one: " + appTerm.getParameters()[0]);					
				}
				if (innerAnnTerm.getSubterm() instanceof ApplicationTerm)
				{
					innerAppTerm = (ApplicationTerm) innerAnnTerm.getSubterm(); //The application term inside the annotated term inside the rewrite-term
				} else
				{
					throw new AssertionError("Expected an application term inside the annotated term inside a rewrite-term, but the following term is none: " + innerAnnTerm.getSubterm());					
				}
				if (innerAppTerm.getFunction().getApplicationString() != "=")
				{
					System.out.println("A random number: 440358"); // Can be used to differ between two same-sounding errors
					throw new AssertionError("Error: The following terms should have = as function symbol, but it has: " + innerAppTerm.getFunction().getApplicationString());					
				}
				
				
				/* Read the rule and handle each differently */
				if (innerAnnTerm.getAnnotations()[0].getKey() == ":strip")
				{
					if (innerAppTerm.getParameters()[0] instanceof AnnotatedTerm)
					{
						AnnotatedTerm stripAnnTerm = (AnnotatedTerm) innerAppTerm.getParameters()[0]; //Term which has to be stripped, annotated term
						if (stripAnnTerm.getSubterm() != innerAppTerm.getParameters()[1])
						{
							throw new AssertionError("Error: Couldn't verify a strip-rewrite. Those two terms should be the same but arent" 
									+ stripAnnTerm.getSubterm() + "vs. " + innerAppTerm.getParameters()[1] + ".");
						} /*else // Not needed
						{
							System.out.println("Verified a strip-rule");
						}*/
					} else
					{
						throw new AssertionError("Error: The first argument of a rewrite equality was expected to be " 
								+ "an annotated term, because the rule is strip. The error-causing term is" + innerAppTerm.getParameters()[0] + ".");
					}
				} else if (innerAnnTerm.getAnnotations()[0].getKey() == ":notSimp")
				{
					// The first argument of the rewrite has to be the double-negated version of the second argument
					ApplicationTerm innerAppTermFirstNeg; //The first negation inside the first argument
					ApplicationTerm innerAppTermSecondNeg; //The second negation inside the first argument
					
					// Check syntactical correctness
					if (!(innerAppTerm.getParameters()[0] instanceof ApplicationTerm))
					{
						throw new AssertionError("Error: " + innerAppTerm.getParameters()[0].toString() 
								+ "should be a double-negated ApplicationTerm but isn't even an ApplicationTerm. "
								+ "It's of the class: " + innerAppTerm.getParameters()[0].getClass().getName());
					}
					
					innerAppTermFirstNeg = (ApplicationTerm) innerAppTerm.getParameters()[0];
					
					if (!((innerAppTermFirstNeg.getParameters()[0] instanceof ApplicationTerm) 
							&& (innerAppTermFirstNeg.getFunction().getName() == "not")))
					{
						throw new AssertionError("Error: " + innerAppTerm.getParameters()[0].toString() 
								+ "should be a double-negated ApplicationTerm, it is an ApplicationTerm, but "
								+ "either the the function isn't \"not\" or the inside is no ApplicationTerm. "
								+ "The function is " + innerAppTermFirstNeg.getFunction().getName() + " and the "
								+ "class of the subterm is: " + innerAppTermFirstNeg.getParameters()[0].getClass().getName());
								
					}
					
					innerAppTermSecondNeg = (ApplicationTerm) innerAppTermFirstNeg.getParameters()[0];
					
					if (!(innerAppTermSecondNeg.getFunction().getName() == "not"))
					{
						throw new AssertionError("Error: " + innerAppTerm.getParameters()[0].toString() 
								+ "should be a double-negated ApplicationTerm, but it is just once negated. The inner"
								+ "isn't \"not\", it's " + innerAppTermSecondNeg.getFunction().getName() + ".");
					}
					
					// Check if the rule was executed correctly
					
					if (innerAppTermSecondNeg.getParameters()[0] != innerAppTerm.getParameters()[1])
					{
						throw new AssertionError("Error: The rule \"notSimp\" couldn't be verified, because the following "
								+ "two terms aren't the same: " + innerAppTermSecondNeg.getParameters()[0].toString() 
								+ " and " + innerAppTerm.getParameters()[1].toStringDirect() + ".\n"
								+ "The original term was: " + appTerm.toStringDirect());
					}
					
					// Important: The return is done later, the following is false: 
					// return innerAppTerm.getParameters()[1];
					
				} else
				{
					System.out.println("Can't handle the following rule " + innerAnnTerm.getAnnotations()[0].getKey() + ", therefore...");
					System.out.println("...believed as alright to be rewritten: " + appTerm.getParameters()[0].toStringDirect() + " ."); //Not nice: Too few rules
				}				
			
				
				// The second part, cut the @rewrite and the annotation out, both aren't needed for the @eq-function.
				pcCache.put(term, innerAnnTerm.getSubterm());
				stackResults.push(innerAnnTerm.getSubterm());				
				break;
				
			case "@intern":
				
				/* At this point there is no access to the other arguments, so it
				 * can't be checked here if the first argument is the same as the last argument of 
				 * the last argument. */
				
				System.out.println("Believed as alright to be (intern) rewritten: " + appTerm.getParameters()[0].toStringDirect() + " ."); //TODO: Implement rule-reader
				pcCache.put(term, appTerm.getParameters()[0]);
				stackResults.push(appTerm.getParameters()[0]);
				break;
				
			case "@split":
				// TODO: Check if the first argument contains the second argument
				
				/* At this point there is no access to the other arguments, so it
				 * can't be checked here if the first argument is the same as the last argument of 
				 * the last argument. */
				
				//return unfold(appTerm.getParameters()[1], smtInterpol);
				//System.out.println("Split hat " + appTerm.getParameters().length + " Argumente.");
				//System.out.println("Splitte " + appTerm.getParameters()[0].toString() + " und nehme " + appTerm.getParameters()[1].toString());
				pcCache.put(term, appTerm.getParameters()[1]);
				stackResults.push(appTerm.getParameters()[1]); //Not nice: Kann da auch etwas stehen was eigentlich aufgefaltet werden sollte?
				break;
				
			case "@clause":
				//throw new AssertionError("Error: The routine for the function " + functionname + " is under construction.");
				//System.out.println("Clause erreicht!"); //: " + appTerm.toStringDirect());				
				
				
				
				if (appTerm.getParameters().length != 2)
				{
					throw new AssertionError("Error: The clause term has not 2 parameters, it has " 
							+ appTerm.getParameters().length + ". The term is " + appTerm.toString());
				}
								

				stackWalker.push(new WalkerId(term, "clause"));
				stackWalker.push(new WalkerId(appTerm.getParameters()[1], ""));
				stackWalker.push(new WalkerId(appTerm.getParameters()[0], ""));
				break;				
				
			default:
				if (!(functionname.startsWith("@")))
				{
					// Not nice: The Proof-Checker shouldn't do that
					System.out.println("Out of mysterious reasons the Proof-Checker made contact with "
							+ "the function symbol " + functionname + ". The Proof-Checker will take a step back.");
					System.out.println("The mysterious term is: " + appTerm.toStringDirect());
					pcCache.put(term, appTerm);
					stackWalker.push(new WalkerId(appTerm, ""));
				}
				
				throw new AssertionError("Error: The Proof-Checker has no routine for the function " + functionname + "."
						+ "The error-causing term is " + appTerm);
			}
			
		} else if (term instanceof AnnotatedTerm) {
			/* res is an AnnotatedTerm */
			
			/* Annotations no more get just removed, this was incorrect */
			
			/* Assumption: There is no need to unfold stuff HERE inside an annotation 
			 * (because if that's needed the function on the outside will take care */
			/* This assumption may be wrong! */
			
			annTerm = (AnnotatedTerm) term;
			
			//Not nice: Creating an application term for no real reason
			/*System.out.println("Test");
			Term tempTerm = smtInterpol.term("not", term);
			System.out.println("TempTerm: " + tempTerm.toStringDirect());
			ApplicationTerm appTerm = (ApplicationTerm) tempTerm;
			System.out.println("AppTerm: " + appTerm.toStringDirect());*/
			stackWalker.push(new WalkerId(term,"annot"));
			stackWalker.push(new WalkerId(annTerm.getSubterm(),""));
			stackAnnots.push(annTerm.getAnnotations());
		} else { 
			throw new AssertionError("Error: The Proof-Checker has no routine for the class " + term.getClass() + ".");
		}
	
	}
	
	//Special Walker
	public void walkSpecial(Term term, String type, SMTInterpol smtInterpol)
	{
		//System.out.println("TermSp: " + term.toStringDirect());
		
		ApplicationTerm appTerm = null;
		Term[] params = null;
		if (term instanceof ApplicationTerm)
		{
			appTerm = (ApplicationTerm) term;
			params = appTerm.getParameters();
		}
		
		//Term[] paramsCalc = new Term[params.length]; //The arguments of the resolution function after the unfolding-calculation
		Term paramCheck = null; //parameter that is getting checked.
		//Not nice: Initialization as null.
		
		switch (type)
		{		
		case "calcParams":			
			for (int i = 0; i < params.length; i++)
			{
				//Calculating in the arguments (of the resolution) proven formulas
				stackWalker.push(new WalkerId(params[i],""));
				//System.out.println("Parameter: " + params[i].toStringDirect());
			}
			break;
			
			
			
		case "res":

			//System.out.println("Case: \"res\"");
			
			ArrayList<Term> disjunctsAdd = new ArrayList<Term>();
			
			/* Get the arguments and pivots */
			Term[] pivots = new Term[params.length]; //The zeroth entry has no meaning.
			AnnotatedTerm innerAnnTerm;
			
			for (int i = 0; i < params.length; i++)
			{
				/* get pivot: start */
				if (params[i] instanceof AnnotatedTerm)
				{										
					innerAnnTerm = (AnnotatedTerm) params[i];
					
					/* Check if it is a pivot-annotation */
					if (innerAnnTerm.getAnnotations()[0].getKey() != ":pivot")
					{
						throw new AssertionError("Error: The annotation has key " + innerAnnTerm.getAnnotations()[0].getKey() + " instead of :pivot, " 
								+ "which is required. It's value is: " + innerAnnTerm.getAnnotations()[0].getValue());
					}						
											
					/* Just take the first annotation, because it should have exactly one - otherwise the proof-checker throws a warning */
					if (innerAnnTerm.getAnnotations()[0].getValue() instanceof AnnotatedTerm
							 ||
							 innerAnnTerm.getAnnotations()[0].getValue() instanceof ApplicationTerm
							 ||
							 innerAnnTerm.getAnnotations()[0].getValue() instanceof ConstantTerm)
					{							
						pivots[i] = (Term) innerAnnTerm.getAnnotations()[0].getValue();
						//System.out.println("Das Pivot ist: " + pivots[i].toStringDirect());
					} else
					{
						throw new AssertionError("Error: The following object was supposed to be a known term but isn't: " + 
								innerAnnTerm.getAnnotations()[0].getValue().toString() + "It is:" + 
								innerAnnTerm.getAnnotations()[0].getValue().getClass().getCanonicalName());
					}
					
					if (innerAnnTerm.getAnnotations().length > 1)
					{
						throw new AssertionError("Error: Expected number of annotations was 1, instead it is " + innerAnnTerm.getAnnotations().length + " in this term " + innerAnnTerm);
					}
				}
				/* get pivot: end */
			}
			
			/* Check if the pivots are really in the second argument */
			Term[] paramsCalcRes = new Term[params.length];
			AnnotatedTerm[] paramsCut = new AnnotatedTerm[paramsCalcRes.length];
			
			for (int i = 0; i < paramsCalcRes.length; i++)
			{
				if (!stackResults.isEmpty())
				{
					paramsCalcRes[i] = stackResults.pop();					
				} else
				{
					throw new AssertionError("Error: The Resolution needs results, but there are none.");
				}
				
			}			
			
			for (int i = 1; i < params.length; i++)
			{
				/* paramsCalc still includes the pivot-annotation. This has to be cutted out */
				if (paramsCalcRes[i] instanceof AnnotatedTerm)
				{
					paramsCut[i] = (AnnotatedTerm) paramsCalcRes[i];
				} else	{
					throw new AssertionError("Error: This code really shouldn't be reachable! A random number: 23742");
				}
				
				// TODO
				// TODO: Can it be that e.g. pivot 4 deletes a disjunct which pivot 1 added?
				// TODO
				/* The search for the pivot in the term with the pivot: */
				if (paramsCut[i].getSubterm() == pivots[i])
				{
					// The Pivot-term has one disjunct
					//System.out.println("Konnte das Pivot " + pivots[i] + " in " + paramsCalc[i].toStringDirect() + " finden.");
					//Term[] disjunctsAdd = new Term[0];  
				} else if (paramsCut[i].getSubterm() instanceof ApplicationTerm && powLev == 0)
				{
					// The pivot term has more than one disjunct
					ApplicationTerm paramsCutIApp = (ApplicationTerm) paramsCut[i].getSubterm();
					 
					if (paramsCutIApp.getFunction().getApplicationString() != "or")
					{
						throw new AssertionError("Error: Hoped for a disjunction while searching the pivot " 
								+ pivots[i] + " in " + paramsCalcRes[i].toStringDirect() + ". But found "
								 + "a function with that symbol: " + paramsCutIApp.getFunction().getApplicationString());
					} 
					
					//Term[] disjunctsAdd = new Term[paramsCutIApp.getParameters().length-1];
					// TODO: Is there a need to find out if two terms are the same?
					
					// How the following for-loop works:
					// For disjunct we have to check if it's the pivot, if not it has to be added later.
					// If it is, only then k won't be counted up, which avoids the error.
					// That means if we go out of the loop without an error, we know, that the pivot has been found.
					int k = 0; // Counts through the disjuncts 
					for (int j = 0; j < disjunctsAdd.size(); j++)
					{
						if (paramsCutIApp.getParameters()[j] != pivots[i])
						{
							if (k < disjunctsAdd.size())
							{
								disjunctsAdd.add(paramsCutIApp.getParameters()[j]);
								k++;
							} else
							{
								throw new AssertionError("Error: couldn't find the pivot "+ pivots[i].toStringDirect() 
										+ " in the disjunction " +  paramsCutIApp.toStringDirect());
							}
							
						} else
						{
							System.out.println("Found the pivot " + pivots[i].toStringDirect() 
									+ "in the disjunction" + paramsCutIApp.toStringDirect() + "!");
						}
					}
				} else if (powLev > 0)
				{
					//System.out.println("Warning: The level of power had an effect.");
				} else
				{
					throw new AssertionError("Error: Konnte das Pivot " + pivots[i] + " NICHT in " + paramsCalcRes[i].toStringDirect() + " finden.");
					
				}
			}
			
			// Not nice: Not tested: Clause has just one disjunct (and therefore no "or")
			
			Term disjuncts[];
			Term innerParams[];
			//String pivotstr = "";
			//String disjunctstr = "";
							
			boolean multiDisjunct = false;
			ApplicationTerm innerAppTerm = null; //Not nice, but it will just be needed when multiDisjunct holds and then it is initialized properly
			if (paramsCalcRes[0] instanceof ApplicationTerm)
			{
				innerAppTerm = (ApplicationTerm) paramsCalcRes[0]; //First Term: The one which gets resoluted
				
				/* Does the clause have one or more disjuncts? */
				/* Not nice: Assumption: If there is just one clause it doesn't start with an "or" - is that correct?*/
				if (innerAppTerm.getFunction().getName() == "or")
				{
					multiDisjunct = true;
				}
			}
			
			/* Initialization of the disjunct(s) */
			
			if (multiDisjunct)
			{
				innerParams = innerAppTerm.getParameters();	//His disjuncts (Works just if the clause has more than one disjunct)
				disjuncts = new Term[innerParams.length];
				for (int i = 0; i < innerParams.length; i++)
				{
					disjuncts[i] = innerParams[i];
				}
			} else {
				disjuncts = new Term[1];
				disjuncts[0] = paramsCalcRes[0];
			}
			
			boolean[] disjunctsOK = new boolean[disjuncts.length];
			
			if (multiDisjunct)
			{
				for (int i = 0; i < disjuncts.length; i++)
				{
					disjunctsOK[i] = true;
				}
			} else {
				disjunctsOK[0] = true;
			}
			
			//if (true)
				
			/* Compare all disjuncts with pivots (un-annotated) */
			for (int i = 0; i < disjuncts.length; i++)
			{
				
				/* Delete the disjunct if there is a fitting pivot */
				for (int j = 1; j < params.length; j++) //Not nice: Expects (j != 0), that the first clause is the one which gets resoluted.
				{
					/* Check if one negates the other, if so delete the disjunct */
					//System.out.println("Vergleiche: " + disjuncts[i].toStringDirect() + " vs. " + pivots[j].toStringDirect());
					//System.out.println("Mit: " + disjuncts[i].toStringDirect() + " vs. " + negate(pivots[j], smtInterpol).toStringDirect());
					//System.out.println("Ohne: " + negate(disjuncts[i], smtInterpol) + " vs. " + pivots[j]);					
					if (disjuncts[i] == negate(pivots[j], smtInterpol))
					{
						//System.out.println("Treffer! \n");
						disjunctsOK[i] = false;
					} /*else
					{
						System.out.println("Kein Treffer \n");
					}	*/						
				}						
			}
			
			/* Count the remaining disjuncts */
			int c = 0;
			for (int i = 0; i < disjuncts.length; i++)
			{
				if (disjunctsOK[i])
					c++;
			}
			//System.out.println("Von " + disjuncts.length + " Disjunktionen sind noch "
			//		+ c + " übrig.");
			//System.out.println("c = " + c);
			c += disjunctsAdd.size();
			//System.out.println("c = " + c);
			/*if (disjunctsAdd.size() > 0)
			{
				System.out.println("\n Konnte mit Liste der Größe " + disjunctsAdd.size() + " umgehen. \n");
			}*/
			
			
			/* Different handling for a different number of conjuncts is needed */
			switch (c)
			{
			case 0:	
				//System.out.println("Red");
				pcCache.put(appTerm, smtInterpol.term("false"));
				stackResults.push(smtInterpol.term("false"));
				break;
			case 1:
				//System.out.println("Green");
				boolean outerBreak = false;
				for (int i = 0; i < disjuncts.length; i++)
				{
					if (disjunctsOK.length <= i)
					{
						throw new AssertionError("Error: disjunctsOK ist zu kurz: " 
								+ disjunctsOK.length + " statt " + disjuncts.length + ".");
					}
					if (disjunctsOK[i])
					{	
						pcCache.put(appTerm, disjuncts[i]);
						stackResults.push(disjuncts[i]);
						outerBreak = true;
						break;
					}					
				}
				if (outerBreak)
					break;				
				
				// So the one element has to be in the list
				if (disjunctsAdd.size() == 0)
				{
					throw new AssertionError("Error: Couldn't find the one disjunct I shall return.");
				}
				//System.out.println("ReturningB: " + disjunctsAdd.get(0).toStringDirect());
				
				pcCache.put(appTerm, disjunctsAdd.get(0));
				stackResults.push(disjunctsAdd.get(0));
				break;
			default:
				//System.out.println("Blue");
				// Note nice: The whole case is untested.
				
				//Build an array that contains only the disjuncts, that have to be returned
				Term[] disjunctsReturn = new Term[c];
				int d = 0; //Counts through the disjuncts
				//System.out.println("Counter...");
				for (int i = 0; i < disjuncts.length; i ++)
				{
					if (disjunctsOK[i])
					{
						if (d < c)
						{
							disjunctsReturn[d] = disjuncts[i];
							d++;
						} else {
							throw new AssertionError("Error: A total unexpected miscalculation occured. Random number: 638402");
						}
					} /*else
					{
						System.out.println("| (" + d + "," + i + ")");
					}*/
				}
				if (disjunctsReturn.length - d != disjunctsAdd.size())
				{
					throw new AssertionError("Error: I'd like to fill up the to be returned disjuncts with "
							+ "the list of \"to be added\"-disjuncts, but the size doesn't fit. The list has "
							+ "size " + disjunctsAdd.size() + " and there is/are " 
							+ (disjunctsReturn.length - d) + " = " + disjunctsReturn.length + " - "
							+ d + " free space(s).");									
				}
				
				// Now add the "to be added"-disjuncts
				int p = 0; //counts through the list
				while (d < disjunctsReturn.length)
				{
					disjunctsReturn[d] = disjunctsAdd.get(p);
					//disjunctsReturn[d] = disjunctsAdd.remove(0); Could bet more effective, but is untested
					d++;
					p++;
				}
				
				/*if (pfpc.size() >= 5)
				{
					if (pfpc.get(3) == 3 && pfpc.get(4) == 6)
					{
						System.out.println("Returning: " + disjunctsReturn.toString());
					}
				}*/
				pcCache.put(appTerm, smtInterpol.term("or", disjunctsReturn));						
				stackResults.push(smtInterpol.term("or", disjunctsReturn));
				break;
			}
			/*} else
			{
				throw new AssertionError("Expected an application term inside the first argument, but the following term doesn't have one: " + params[0]);
				//innerAppTerm = (ApplicationTerm) smtInterpol.term("false");
			}*/
			
			break;
			
			
			
		case "eq":
			/* Expected: The first argument is unary each other argument binary.
			 * Then for each n>=0 the nth argument describes one term rewritten by an equal new term, 
			 * where the two terms
			 *  - nth argument's last argument
			 *  - (n+1)th argument's first argument 
			 *  are the same and for each n >= 1:
			 *  - nth argument's first argument is rewritten by the equal term's
			 *    nth argument's second argument. */
			/* This works just for rewrite, not for intern */

			ApplicationTerm[] paramsApp = new ApplicationTerm[params.length]; //Parameters of @eq, uncalculated, application terms
			ApplicationTerm paramsCalcIApp; //The ith parameter of @eq, calculated, application term
			Term[] paramsCalcEq = new Term[params.length]; //			
			
			for (int i = 0; i < params.length; i++)
			{
				//pfpc.add(0);
				if (!stackResults.isEmpty())
				{
					paramsCalcEq[i] = stackResults.pop();	//Parameters of @eq, calculated, terms					
				} else
				{
					throw new AssertionError("Error: Eq needs results, but there are none.");
				}
				
				//pfpc = afterUnfoldPc(pfpc);
				
				if (params[i] instanceof ApplicationTerm)
				{
					paramsApp[i] = (ApplicationTerm) params[i];
				} else
				{
					throw new AssertionError("Error: The following terms should be an application term but isn't: " + params[i]);
				}
				/* The first argument is unary, and requires therefore different treatment */
				if (i == 0)
					paramCheck = paramsCalcEq[0];
				else
				{
					/* It has to be an ApplicationTerm with function symbol "=". Everything else should throw an error */
					if (paramsCalcEq[i] instanceof ApplicationTerm)
					{
						paramsCalcIApp = (ApplicationTerm) paramsCalcEq[i];										
					} else
					{
						throw new AssertionError("Expected an application term inside any rewrite-term, but the following term doesn't have one: " + paramsCalcEq[i]);							
					} 
											
					if (paramsCalcIApp.getFunction().getApplicationString() != "=")
					{
						System.out.println("A random number: 582046"); // Can be used to differ between two same-sounding errors
						throw new AssertionError("Error: The following terms should have = as function symbol, but it has: " + paramsCalcIApp.getFunction().getApplicationString() + "\n"
								 + "Term: " + paramsCalcIApp.toStringDirect() + " calculated from " + params[i].toStringDirect()); 
					}
					
					
					if (paramsApp[i].getFunction().getName() != "@rewrite" && paramsApp[i].getFunction().getName() != "@intern")
					{
						throw new AssertionError("Error: An argument of @eq was neither a @rewrite nor a @intern, it was: " + paramsApp[i].getFunction().getName() + ".");							
					}
						
					//Note: paramCheck was declared in the last for-loop
					if (paramsApp[i].getFunction().getName() == "@rewrite" && paramCheck != paramsCalcIApp.getParameters()[0])
					{
						throw new AssertionError("Error: The following terms should be the same but aren't: " + paramCheck + " vs. " + paramsCalcIApp.getParameters()[0]);
					} 
					else if (paramsApp[i].getFunction().getName() == "@rewrite")
					{
						/* Preparation for the next comparison */
						paramCheck = paramsCalcIApp.getParameters()[1];								
					}
					else if (paramsApp[i].getFunction().getName() == "@intern") //The equality is not needed 
					{
						Term rewrittenTerm = internalRewrite(paramCheck, paramsCalcIApp.getParameters()[0], paramsCalcIApp.getParameters()[1], smtInterpol);
						
						if (rewrittenTerm == paramCheck){
							throw new AssertionError("Error: Couldn't understand the internal rewrite of " + paramCheck.toStringDirect() + " with the rule: " + 
									paramsCalcIApp.getParameters()[0].toStringDirect() + " --> " + paramsCalcIApp.getParameters()[1].toStringDirect());
						}
						
						//System.out.println("Alter Term: " + paramCheck.toStringDirect());
						//System.out.println("Gebe zurück: " + rewrittenTerm.toStringDirect());
						pcCache.put(appTerm, rewrittenTerm);
						stackResults.push(rewrittenTerm);
						break;
					}
					else
					{
						System.out.println("This code shouldn't be reachable, a random number: 473957");
					}
				}
			}
			pcCache.put(appTerm, paramCheck);
			stackResults.push(paramCheck);
			
			break;
			
			
			
		case "clause":

			/* Check if the parameters of clause are two disjunctions (which they should be) */
			
			ApplicationTerm paramDisjunct1; //The first Parameter of clause, which is a disjunct
			ApplicationTerm paramDisjunct2;
			
			Term param1Calc = null;
			Term param2Calc = null;
			
			if (!stackResults.isEmpty())
			{
				param1Calc = stackResults.pop();
			} else
			{
				throw new AssertionError("Error: Clause1 needs a result, but there is none.");
			}
			
			if (!stackResults.isEmpty())
			{
				param2Calc = stackResults.pop();
			} else
			{
				throw new AssertionError("Error: Clause1 needs a result, but there is none.");
			}
			
			if (!(param1Calc instanceof ApplicationTerm)
				|| !(param2Calc instanceof ApplicationTerm))
			{
				throw new AssertionError("Error: The clause-term has one parameter which isn't an application"
						+ "term. The first parameter " + param1Calc + " is of the class"
						+ param1Calc.getClass().getName() + " and the second paramter " 
						+ param2Calc + " is of the class "
						+ param2Calc.getClass().getName() + ".");							
			}
			
			paramDisjunct1 = (ApplicationTerm) param1Calc;
			paramDisjunct2 = (ApplicationTerm) param2Calc;				
			
			if (paramDisjunct1.getFunction().getApplicationString() != "or"
					|| paramDisjunct2.getFunction().getApplicationString() != "or")
				{
					throw new AssertionError("Error: The clause-term has one parameter which isn't a disjunction"
							+ ". The first parameter " + paramDisjunct1 + " has the function symbol "
							+ paramDisjunct1.getFunction().getApplicationString() + " and the second paramter " 
							+ paramDisjunct2 + " has the function symbol "
							+ paramDisjunct2.getFunction().getApplicationString() + ".");							
				}
										
			
			/* Check if the clause operation was correct. Each later disjunct has to be in the first disjunction.
			 *  Actually more has to hold, but this is enough for the proof to be correct.
			 */
			
			Term[] paramDisjunct1Disjuncts = paramDisjunct1.getParameters(); //Just needed to fasten things up.
			Term[] paramDisjunct2Disjuncts = paramDisjunct2.getParameters();
			
			for (int i = 0; i < paramDisjunct2Disjuncts.length; i++)
			{
				boolean found = false;
				for (int j = 0; j < paramDisjunct1Disjuncts.length; j++)
				{
					if (paramDisjunct1Disjuncts[j] == paramDisjunct2Disjuncts[i])
					{
						found = true;
					}
				}
				if (!found)
				{
					throw new AssertionError("Error: Couldn't find the disjunct " 
							+ paramDisjunct2Disjuncts[i].toString() + " in the disjunction "
							+ paramDisjunct1.toString() + ".");
				}
			}
			
											
			pcCache.put(appTerm, paramDisjunct2);
			stackResults.push(paramDisjunct2);
			break;
			
			
		case "annot":
			//System.out.println("Case: \"annot\"");
			// Not nice: No writing in the cache, but it's not too bad
			// because on layer deeper there's cache-writing
			//pcCache.put(term, smtInterpolGlobal.annotate(unfold(, smtInterpolGlobal, pfpc), annTerm.getAnnotations()));
			stackResults.push(smtInterpol.annotate(stackResults.pop(), stackAnnots.pop()));
			break;			
			
		default:
			throw new AssertionError("Error: Couldn't walk with the key " + type);
		}
	}
		
	
	public class WalkerId<T, S> { 
		  public final Term t; 
		  public final String s; 
		  public WalkerId(Term t, String s) { 
		    this.t = t; 
		    this.s = s; 
		  } 
	}
}





