package de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2;

// import de.uni_freiburg.informatik.ultimate.logic.LoggingScript;
import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
//import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm; //May not be needed
//import de.uni_freiburg.informatik.ultimate.logic.Logics;
//import de.uni_freiburg.informatik.ultimate.logic.NoopScript;
//import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;

public class ProofChecker extends SMTInterpol {
	public boolean check(Term res, SMTInterpol smtInterpol) {
		
		Term resCalc;		
		resCalc = unfold(res, smtInterpol);
		//System.out.println("White");
		
		//System.err.out("Warnung: Auswertung im Proof-Checker fehlt");
		
		//System.out.println("Am Ende kommt heraus: " + resCalc.toStringDirect());
		
		if (resCalc == smtInterpol.term("false"))
		{
			return true;
		} else {
			return false;
		}
		
		
	}
	
	public Term unfold(Term res, SMTInterpol smtInterpol) {
		
		/* The first version of this function is recursive, later it should be non-recursive */
		/* Takes proof, returns proven formula */
		
		/* Declaration of variables used later */
		String functionname;
		Term params[];
		Term paramsCalc[]; //parameters after calculation
		Term paramCheck = null; //noopscript.term("false"); //parameter that is getting checked.
		//Not nice: Initialization as null.
		AnnotatedTerm innerAnnTerm;
		ApplicationTerm innerAppTerm;
		AnnotatedTerm annTerm;
		Term pivots[];		
		
		/* Look at the class of the term and treat each different */
		if (res instanceof ApplicationTerm) 
		{			
			/* res is an ApplicationTerm */
			ApplicationTerm appTerm = (ApplicationTerm) res;
			
			/* Get the function and parameters */
			functionname = appTerm.getFunction().getName();
			params = appTerm.getParameters();
			paramsCalc = new Term[params.length]; //The arguments of the resolution function after the unfolding-calculation
			
			/* Look at the function of the application-term and treat each different */
			switch (functionname)
			{
			case "@res":
				/* Not nice: This function is expected to have as first argument the clause which is used
				 * further, after the pivots are deleted.
				 */
				
				/* Get the arguments and pivots */
				pivots = new Term[params.length];
				
				for (int i = 0; i < params.length; i++)
				{
					/* get pivot: start */
					if (params[i] instanceof AnnotatedTerm)
					{
						/* One should check this */						
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
					
					//Calculating in the arguments (of the resolution) proven formulas 
					paramsCalc[i] = unfold(params[i], smtInterpol);
					
					//System.out.println("ParamsCalc[" + i + "]: " + paramsCalc[i].toStringDirect());
					//unfold(params[i], smtInterpol);
					
				}
				
				
				/* Searching the pivots and deleting them in the first clause */
				AnnotatedTerm[] paramsCut = new AnnotatedTerm[paramsCalc.length];
				
				for (int i = 1; i < pivots.length; i++)
				{
					/* paramsCalc still includes the pivot-annotation. This has to be cutted out */
					if (paramsCalc[i] instanceof AnnotatedTerm)
					{
						paramsCut[i] = (AnnotatedTerm) paramsCalc[i];
					} else	{
						throw new AssertionError("Error: This code really shouldn't be reachable! A random number: 23742");
					}
					
					/* The search for the pivot: */
					if (paramsCut[i].getSubterm() != pivots[i])
					{
						throw new AssertionError("Error: Konnte das Pivot " + pivots[i] + " NICHT in " + paramsCalc[i].toStringDirect() + " finden.");
					} else {
						//System.out.println("Grashüpfer: Konnte das Pivot " + pivots[i] + " in " + paramsCalc[i] + " finden.");
					}
					
				}
				
				// Not nice: Not tested: Clause has just one disjunct (and therefore no "or")
				
				Term disjuncts[];
				Term innerParams[];
				//String pivotstr = "";
				//String disjunctstr = "";
								
				boolean multiDisjunct = false;
				innerAppTerm = null; //Not nice, but it will just be needed when multiDisjunct holds and then it is initialized properly
				if (paramsCalc[0] instanceof ApplicationTerm)
				{
					innerAppTerm = (ApplicationTerm) paramsCalc[0]; //First Term: The one which gets resoluted
					
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
					disjuncts[0] = paramsCalc[0];
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
				
				
				if (true)
					
					/* Compare all disjuncts with pivots (un-annotated) */
					for (int i = 0; i < disjuncts.length; i++)
					{
						
						/* Delete the disjunct if there is a fitting pivot */
						for (int j = 1; j < pivots.length; j++) //Not nice: Expects (j != 0), that the first clause is the one which gets resoluted.
						{
							/* Check if one negates the other, if so delete the disjunct */
							//System.out.println("Vergleiche: " + disjuncts[i].toStringDirect() + " vs. " + pivots[j].toStringDirect());
							//System.out.println("Mit: " + disjuncts[i].toStringDirect() + " vs. " + negate(pivots[j], smtInterpol).toStringDirect());
							//System.out.println("Ohne: " + negate(disjuncts[i], smtInterpol) + " vs. " + pivots[j]);					
							if (disjuncts[i] == negate(pivots[j], smtInterpol)
									//|| pivots[j] == negate(disjuncts[i], smtInterpol) //Presumption: This line is not necessary
									)
							{
								//System.out.println("Treffer! \n");
								//disjuncts[i] = smtInterpol.term("false");//noopscript.term("false");
								disjunctsOK[i] = false;
							} else
							{
								//System.out.println("Kein Treffer \n");
							}							
						}						
					}
					
					/* Count the remaining disjuncts */
					int c = 0;
					for (int i = 0; i < disjuncts.length; i++)
					{
						if (disjunctsOK[i])
							c++;
					}
					
					/* Different handling for a different number of conjuncts is needed */
					switch (c)
					{
					case 0:	
						System.out.println("Blue");
						return smtInterpol.term("false");
					case 1:
						System.out.println("Red");
						for (int i = 0; i < disjuncts.length; i++)
						{
							if (disjunctsOK[i])
								{return disjuncts[i];}
						}						
					default:
						System.out.println("Green");
						// Note nice: The whole case is untested.
						
						//Build an array that contains only the discunts, that have to be returned
						Term[] disjunctsReturn = new Term[c];
						int d = 0; //Counts through the disjuncts 
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
								
							}
						}
						
						return smtInterpol.term("or", disjunctsReturn);
												
						//throw new AssertionError("Error: Can't deal with multiple (" + c + ") remaining disjuncts after resolution");	
					}
				/*} else
				{
					throw new AssertionError("Expected an application term inside the first argument, but the following term doesn't have one: " + params[0]);
					//innerAppTerm = (ApplicationTerm) smtInterpol.term("false");
				}*/
				
				
				//throw new AssertionError("This place shouldn't be reached. Some random number: 143789");				
				//break;
				
			case "@eq":
				/* Expected: The first argument is unary each other argument binary.
				 * Then for each n>=0 the nth argument describes one term rewritten by an equal new term, 
				 * where the two terms
				 *  - nth argument's last argument
				 *  - (n+1)th argument's first argument 
				 *  are the same and for each n >= 1:
				 *  - nth argument's first argument is rewritten by the equal term's
				 *    nth argument's second argument. */
				/* This works just for rewrite, not for intern */

				ApplicationTerm[] paramsApp = new ApplicationTerm[params.length];
						
				for (int i = 0; i < params.length; i++)
				{

					paramsCalc[i] = unfold(params[i], smtInterpol);					
					if (params[i] instanceof ApplicationTerm)
					{
						paramsApp[i] = (ApplicationTerm) params[i];
					} else
					{
						throw new AssertionError("Error: The following terms should be an application term but isn't: " + params[i]);
					}
					/* The first argument is unary, and requires therefore different treatment */
					if (i == 0)
						paramCheck = paramsCalc[i];
					else
					{
						/* It has to be an ApplicationTerm with function symbol "=". Everything else should throw an error */
						if (paramsCalc[i] instanceof ApplicationTerm)
						{
							innerAppTerm = (ApplicationTerm) paramsCalc[i];												
						} else
						{
							throw new AssertionError("Expected an application term inside any rewrite-term, but the following term doesn't have one: " + paramsCalc[i]);
							//innerAppTerm = (ApplicationTerm) smtInterpol.term("false"); //TODO: The noopscript-stuff throws an error.
						} 
						// TODO: Missing: Checking of =
						
						/* TODO: Check if the terms of the different arguments are really the same */
						if (paramCheck != innerAppTerm.getParameters()[0] && innerAppTerm.getFunction().getName() == "@rewrite")
						{
							throw new AssertionError("Error: The following terms should be the same but aren't: " + paramCheck + " vs. " + innerAppTerm.getParameters()[0]);
						} 
						else if (paramsApp[i].getFunction().getName() == "@rewrite")
						{
							System.out.println("Believed as the same: " + paramCheck + " vs. " + innerAppTerm.getParameters()[0]);
							
							/* Preparation for the next comparison */
							paramCheck = innerAppTerm.getParameters()[1];
							
						} 
						else if (paramsApp[i].getFunction().getName() == "@intern")
						{
							System.out.println("Believed the internal rewrite: " + paramCheck + " vs. " + innerAppTerm.getParameters()[0]);
							
							if (paramCheck == innerAppTerm.getParameters()[0])
							{
								paramCheck = innerAppTerm.getParameters()[1];
							}
							else 
							{
								if (!(paramCheck instanceof ApplicationTerm))							
								{
									throw new AssertionError("Error: The following terms should be an application term but isn't: " + paramCheck);
								}
								ApplicationTerm paramCheckApp = (ApplicationTerm) paramCheck;							
								if (paramCheckApp.getParameters()[0] == innerAppTerm.getParameters()[0])
								{
									/* Preparation for the next comparison */
									paramCheck = smtInterpol.term(paramCheckApp.getFunction().getName(), innerAppTerm.getParameters()[1]);							
								} else
								{
									throw new AssertionError("Error: Couldn't understand the internal rewrite of " + paramCheck.toStringDirect() + " with the rule: " + 
											innerAppTerm.getParameters()[0].toStringDirect() + " --> " + innerAppTerm.getParameters()[1].toStringDirect());
								}
							}
							
						} else
						{
							System.out.println("Case: " + paramsApp[i].getFunction().getName());
							throw new AssertionError("Error: This message shouldn't be reachable. Random number: 225643");
						}
						
						
						
					}
				}
				return paramCheck; // break;
				
			case "@lemma":
				System.out.println("Believed as true: " + appTerm.toStringDirect() + " .");
				
				// If possible return the un-annotated version
				// Warning: Code duplicates (Random number: 498255) 
				if (appTerm.getParameters()[0] instanceof AnnotatedTerm)
				{
					innerAnnTerm = (AnnotatedTerm) appTerm.getParameters()[0];
					//System.out.println("Apple:");
					//System.out.println("Apple:" + res.toStringDirect());
					return innerAnnTerm.getSubterm();
					//return smtInterpol.term("false");
				} else
				{
					throw new AssertionError("Expected an annotated term inside any lemma-term, but the following term doesn't have one: " + appTerm.getParameters()[0]);
					//return appTerm.getParameters()[0];
				}
				
			case "@tautology":
				System.out.println("Believed as true: " + appTerm.toStringDirect() + " .");
				
				// If possible return the un-annotated version
				// Warning: Code duplicates (Random number: 498255)
				if (appTerm.getParameters()[0] instanceof AnnotatedTerm)
				{
					innerAnnTerm = (AnnotatedTerm) appTerm.getParameters()[0];
					return innerAnnTerm.getSubterm();
				} else
				{
					throw new AssertionError("Expected an annotated term inside any tautology-term, but the following term doesn't have one: " + appTerm.getParameters()[0]);
					//return appTerm.getParameters()[0];
				}
				
			case "@asserted":
				System.out.println("Believed as asserted: " + appTerm.getParameters()[0].toStringDirect() + " .");
				/* Just return the part without @asserted */ 
				return appTerm.getParameters()[0]; 
				//break;
				
			case "@rewrite":
				
				/* At this point there is no access to the other arguments, so it
				 * can't be checked here if the first argument is the same as the last argument of 
				 * the last argument. */
				
				System.out.println("Believed as alright to be rewritten: " + appTerm.getParameters()[0].toStringDirect() + " .");
				
				// If possible return the un-annotated version
				// Warning: Code duplicates (Random number: 498255)				
				if (appTerm.getParameters()[0] instanceof AnnotatedTerm)
				{
					innerAnnTerm = (AnnotatedTerm) appTerm.getParameters()[0];
					return innerAnnTerm.getSubterm();
				} else
				{
					throw new AssertionError("Expected an annotated term inside any rewrite-term, but the following term doesn't have one: " + appTerm.getParameters()[0]);
					//return appTerm.getParameters()[0];
				}
				
				
			case "@intern":
				
				/* At this point there is no access to the other arguments, so it
				 * can't be checked here if the first argument is the same as the last argument of 
				 * the last argument. */
				
				System.out.println("Believed as alright to be (intern) rewritten: " + appTerm.getParameters()[0].toStringDirect() + " .");
				return appTerm.getParameters()[0];
				
			case "@split":
				
				/* TODO: Build this */
				
				/* At this point there is no access to the other arguments, so it
				 * can't be checked here if the first argument is the same as the last argument of 
				 * the last argument. */
				
				System.out.println("Believed the splitting rule for: " + appTerm.getParameters()[0].toStringDirect() + " .");
				//return unfold(appTerm.getParameters()[1], smtInterpol);
				return appTerm.getParameters()[1]; //TODO: Kann da auch etwas stehen was eigentlich aufgefaltet werden sollte?
				
			case "@clause":
				/* TODO: Build this */
				throw new AssertionError("Error: The routine for the function " + functionname + " is under construction.");				
				
			default:
				throw new AssertionError("Error: The Proof-Checker has no routine for the function " + functionname + ".");
			}
			
		} else if (res instanceof AnnotatedTerm) {
			/* res is an AnnotatedTerm */
			
			/* Annotations no more get just removed, this was incorrect */
			
			/* Not Nice: Assumption: There is no need to unfold stuff HERE inside an annotation (beacuse if that's needed the function on the outside will take care */
			/* This assumption may be wrong! */
			
			annTerm = (AnnotatedTerm) res;

			//return annTerm;
			return smtInterpol.annotate(unfold(annTerm.getSubterm(), smtInterpol), annTerm.getAnnotations());
			
		} else { 
			throw new AssertionError("Error: The Proof-Checker has no routine for the class " + res.getClass() + ".");
		}
		//return res;
	}
	
	public Term negate(Term formula, SMTInterpol smtInterpol)
	{
		//boolean positive = true;
		
		if (formula instanceof ApplicationTerm)
		{
			ApplicationTerm appFormula = (ApplicationTerm) formula;
			//Not nice: String used!
			if (appFormula.getFunction().getName() == "not")
			{
				//positive = false;
				return appFormula.getParameters()[0];
			}
		}
		
		//Formula is not negative
		return smtInterpol.term("not", formula);
	}
}










