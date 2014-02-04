package de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2;

import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
//import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm; //May not be needed
//import de.uni_freiburg.informatik.ultimate.logic.FormulaUnLet;
//import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;
//import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
//import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;

//import java.util.ArrayList;
//import java.util.HashMap;
import java.util.*;

public class ProofChecker extends SMTInterpol {
	
	// Not nice: returns are spread over the code, all could be in the end
	HashMap<Term, Term> pcCache; //Proof Checker Cache
	// Not nice: The level should be 0
	// Level of proof-checker-power
	int powLev = 2; //Not nice: Best is 0
	
	// Declarations for the Walker
	Stack<WalkerId<Term,String>> stackWalker = new Stack<WalkerId<Term,String>>();
	Stack<Term> stackResults = new Stack<Term>();
	Stack<Term> stackResultsDebug = new Stack<Term>();
	//Not nice: Is this really necessary?:
	Stack<Annotation[]> stackAnnots = new Stack<Annotation[]>();
	
	public boolean check(Term res, SMTInterpol smtInterpol) {
		
		// Initializing the proof-checker-cache
		pcCache = new HashMap<Term, Term>();
		
		Term resCalc;
		// Now non-recursive:
		stackWalker.push(new WalkerId<Term,String>(res,""));
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
		AnnotatedTerm innerAnnTerm;
		ApplicationTerm innerAppTerm;
		AnnotatedTerm annTerm;
		
		/* Look at the class of the term and treat each different */
		if (term instanceof ApplicationTerm) 
		{			
			/* It is an ApplicationTerm */
			ApplicationTerm appTerm = (ApplicationTerm) term;
			
			/* Get the function and parameters */
			functionname = appTerm.getFunction().getName();
			
			/* Just for debugging */
			//System.out.println("Currently looking at: " + functionname);
			
			/* Look at the function of the application-term and treat each different */
			switch (functionname)
			{
			case "@res":
				/* Alright: This function is expected to have as first argument the clause which is used
				 * further, after the pivots are deleted.
				 */
				
				stackWalker.push(new WalkerId<Term,String>(appTerm, "res"));
				calcParams(appTerm);
				return;
				
			case "@eq":
				stackWalker.push(new WalkerId<Term,String>(appTerm, "eq"));
				calcParams(appTerm);
				return;
				
			case "@lemma":
				System.out.println("Believed as true: " + appTerm.toStringDirect() + " ."); //TODO: Implement rule-reader
				
				// If possible return the un-annotated version
				// Warning: Code duplicates (Random number: 498255) 
				if (appTerm.getParameters()[0] instanceof AnnotatedTerm)
				{
					innerAnnTerm = (AnnotatedTerm) appTerm.getParameters()[0];
					stackPush(innerAnnTerm.getSubterm(), term);
				} else
				{
					throw new AssertionError("Expected an annotated term inside any lemma-term, but the following term doesn't have one: " + appTerm.getParameters()[0]);
				}
				return;
				
			case "@tautology":
				System.out.println("Believed as true: " + appTerm.toStringDirect() + " ."); //TODO: Implement rule-reader
				
				// If possible return the un-annotated version
				// Warning: Code duplicates (Random number: 498255)
				if (appTerm.getParameters()[0] instanceof AnnotatedTerm)
				{
					innerAnnTerm = (AnnotatedTerm) appTerm.getParameters()[0];
					stackPush(innerAnnTerm.getSubterm(), term);
				} else
				{
					throw new AssertionError("Expected an annotated term inside any tautology-term, but the following term doesn't have one: " + appTerm.getParameters()[0]);
				}
				return;
				
			case "@asserted":
				System.out.println("Believed as asserted: " + appTerm.getParameters()[0].toStringDirect() + " .");
				/* Just return the part without @asserted */ 
				stackPush(appTerm.getParameters()[0], term); 
				return;
				
			case "@rewrite":
				
				/* At this point there is no access to the other arguments, so it
				 * can't be checked here if the first argument is the same as the last argument of 
				 * the last argument. */
				
				/* Treatment:
				 *  - At first check if the rewrite rule was correctly executed.
				 *  - OLD: Secondly, remove the @rewrite and the annotation for later uses in the @eq-function.
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
				if (innerAppTerm.getFunction().getName() != "=")
				{
					System.out.println("A random number: 440358"); // Can be used to differ between two same-sounding errors
					throw new AssertionError("Error: The following terms should have = as function symbol, but it has: " + innerAppTerm.getFunction().getName());					
				}
				
				//System.out.println("Rule: " + innerAnnTerm.getAnnotations()[0].getKey());
				//System.out.println("Term: " + term.toStringDirect());
				
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
						}
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
								+ " should be a double-negated ApplicationTerm but isn't even an ApplicationTerm. "
								+ "It's of the class: " + innerAppTerm.getParameters()[0].getClass().getName());
					}
					
					innerAppTermFirstNeg = (ApplicationTerm) innerAppTerm.getParameters()[0];
					
					if (!((innerAppTermFirstNeg.getParameters()[0] instanceof ApplicationTerm) 
							&& (innerAppTermFirstNeg.getFunction().getName() == "not")))
					{
						throw new AssertionError("Error: " + innerAppTerm.getParameters()[0].toString() 
								+ " should be a double-negated ApplicationTerm, it is an ApplicationTerm, but "
								+ "either the the function isn't \"not\" or the inside is no ApplicationTerm. "
								+ "The function is " + innerAppTermFirstNeg.getFunction().getName() + " and the "
								+ "class of the subterm is: " + innerAppTermFirstNeg.getParameters()[0].getClass().getName());
								
					}
					
					innerAppTermSecondNeg = (ApplicationTerm) innerAppTermFirstNeg.getParameters()[0];
					boolean simpleTransf = false; //Checks if it was just a simple "true <-> false"-transformation
					
					if (!(innerAppTermSecondNeg.getFunction().getName() == "not"))
					{
						// Not nice: Use of strings
						if (!(innerAppTermSecondNeg.getFunction().getName() == "false" && 
								innerAppTerm.getParameters()[1] == smtInterpol.term("true"))
							&&
							!(innerAppTermSecondNeg.getFunction().getName() == "true" && 
								innerAppTerm.getParameters()[1] == smtInterpol.term("false")))
						{
							System.out.println(innerAppTermSecondNeg.getFunction().getName() + " and "
									+ innerAppTerm.getParameters()[1].toStringDirect());
							System.out.println("The term: " + term.toStringDirect());
							throw new AssertionError("Error: " + innerAppTerm.getParameters()[0].toString() 
									+ " should be a double-negated ApplicationTerm, but it is just once negated. The inner"
									+ " isn't \"not\", it's " + innerAppTermSecondNeg.getFunction().getName() + ".");							
						} else
						{
							simpleTransf = true;
						}
					}
					
					// Check if the rule was executed correctly
					if (!simpleTransf && innerAppTermSecondNeg.getParameters()[0] != innerAppTerm.getParameters()[1])
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
				// stackPush(innerAnnTerm.getSubterm(), term);
				return;
				
			case "@intern":
				
				/* At this point there is no access to the other arguments, so it
				 * can't be checked here if the first argument is the same as the last argument of 
				 * the last argument. */
				
				System.out.println("Believed as alright to be (intern) rewritten: " + appTerm.getParameters()[0].toStringDirect() + " ."); //TODO: Implement rule-reader
				//stackPush(appTerm.getParameters()[0], term);
				return;
				
			case "@split":
				// TODO: Check if the first argument contains the second argument
				
				/* At this point there is no access to the other arguments, so it
				 * can't be checked here if the first argument is the same as the last argument of 
				 * the last argument. */
				
				stackPush(appTerm.getParameters()[1], term); //Not nice: Kann da auch etwas stehen was eigentlich aufgefaltet werden sollte?
				return;
				
			case "@clause":
				
				if (appTerm.getParameters().length != 2)
				{
					throw new AssertionError("Error: The clause term has not 2 parameters, it has " 
							+ appTerm.getParameters().length + ". The term is " + appTerm.toString());
				}

				stackWalker.push(new WalkerId<Term,String>(term, "clause"));
				stackWalker.push(new WalkerId<Term,String>(appTerm.getParameters()[1], ""));
				stackWalker.push(new WalkerId<Term,String>(appTerm.getParameters()[0], ""));
				return;				
				
			default:
				if (!(functionname.startsWith("@")))
				{
					// The Proof-Checker is so deep, that there is nothing more to unfold
					stackPush(term, term);
				} else
				{
					throw new AssertionError("Error: The Proof-Checker has no routine for the function " + functionname + "."
							+ "The error-causing term is " + appTerm);	
				}
			}
			
		} else if (term instanceof AnnotatedTerm) {
			/* res is an AnnotatedTerm */
			
			/* Annotations no more get just removed, this was incorrect */
			
			/* OLD: Assumption: There is no need to unfold stuff HERE inside an annotation 
			 * (because if that's needed the function on the outside will take care */
			/* This assumption may be wrong! */
			
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
			ArrayList<Term> disjunctsAdd = new ArrayList<Term>();
			
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
						throw new AssertionError("Error: The annotation has key " + termArgsIAnn.getAnnotations()[0].getKey() + " instead of :pivot, " 
								+ "which is required. It's value is: " + termArgsIAnn.getAnnotations()[0].getValue());
					}						
											
					/* Just take the first annotation, because it should have exactly one - otherwise the proof-checker throws an error */
					if (termArgsIAnn.getAnnotations()[0].getValue() instanceof Term)
					{							
						pivots[i] = (Term) termArgsIAnn.getAnnotations()[0].getValue();
					} else
					{
						throw new AssertionError("Error: The following object was supposed to be a known term but isn't: " + 
								termArgsIAnn.getAnnotations()[0].getValue().toString() + "It is:" + 
								termArgsIAnn.getAnnotations()[0].getValue().getClass().getCanonicalName());
					}
					
					if (termArgsIAnn.getAnnotations().length > 1)
					{
						throw new AssertionError("Error: Expected number of annotations was 1, instead it is " + termArgsIAnn.getAnnotations().length + " in this term " + termArgsIAnn);
					}
				} else
				{
					throw new AssertionError("Error: Expected an annotated term as No." + i + ">0 of a "
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
			for (int i = 1; i < termArgs.length; i++)
			{
				// TODO
				// TODO: Can it be that e.g. pivot 4 deletes a disjunct which pivot 1 added?
				// TODO
				
				/* The search for the pivot in the term with the pivot: */
				if (termArgsCalcAnn[i].getSubterm() == pivots[i])
				{
					// The Pivot-term has one disjunct
				} else if (termArgsCalcAnn[i].getSubterm() instanceof ApplicationTerm && powLev == 0)
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
					
					// TODO: Is there a need to find out if two terms are the same?
					
					// How the following for-loop works:
					// For each disjunct we have to check if it's the pivot, if not it has to be added later.
					// If it is, only then k won't be counted up, which avoids the error.
					// That means if we go out of the loop without an error, we know, that the pivot has been found.
					//int k = 0; // Counts through the disjuncts
					boolean pivotFound = false;
					
					//System.out.print("Size(" + i + "/" + termArgs.length + "): " + disjunctsAdd.size());
					for (int j = 0; j < termArgsCalcAnnISubtApp.getParameters().length; j++)
					{
						if (termArgsCalcAnnISubtApp.getParameters()[j] != pivots[i])
						{
							disjunctsAdd.add(termArgsCalcAnnISubtApp.getParameters()[j]);
						} else
						{
							pivotFound = true;
						}
					}
					//System.out.println(" -> " + disjunctsAdd.size());
					if (!pivotFound)
					{
						throw new AssertionError("Error: couldn't find the pivot "+ pivots[i].toStringDirect() 
								+ " in the disjunction " +  termArgsCalcAnnISubtApp.toStringDirect());
					}					
				} else if (powLev > 0)
				{
					//System.out.println("Warning: The level of power had an effect.");
				} else
				{
					throw new AssertionError("Error: Could NOT find the pivot " + pivots[i] + " in " 
							+ termArgsCalc[i].toStringDirect() + " finden. Before the calculation the term was "
							+ termArgs[i].toStringDirect());
				}
			}
			
			// Now get the disjuncts of the first argument into an array
			Term termArg0Disjuncts[];
			
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
				termArg0Disjuncts = termArg0CalcApp.getParameters();
			} else {
				termArg0Disjuncts = new Term[1];
				termArg0Disjuncts[0] = termArgsCalc[0];
			}
			
			// true iff the disjunct is not a negated pivot
			boolean[] disjunctsNotPivot = new boolean[termArg0Disjuncts.length];
			
			// Initialization

			for (int i = 0; i < termArg0Disjuncts.length; i++)
			{
				disjunctsNotPivot[i] = true;
			}
				
			/* Compare all disjuncts with pivots (un-annotated) */
			for (int i_disj = 0; i_disj < termArg0Disjuncts.length; i_disj++)
			{
				
				/* Delete the disjunct if there is a fitting pivot */
				for (int j_pivot = 1; j_pivot < termArgs.length; j_pivot++) //Not nice: Expects (j != 0), that the first clause is the one which gets resoluted.
				{
					/* Check if one negates the other, if so delete the disjunct */
					//System.out.println("Vergleiche: " + disjuncts[i].toStringDirect() + " vs. " + pivots[j].toStringDirect());
					//System.out.println("Mit: " + disjuncts[i].toStringDirect() + " vs. " + negate(pivots[j], smtInterpol).toStringDirect());
					if (termArg0Disjuncts[i_disj] == negate(pivots[j_pivot], smtInterpol))
					{
						//System.out.println("Treffer! \n");
						disjunctsNotPivot[i_disj] = false;
					} /*else
					{
						System.out.println("Kein Treffer \n");
					}	*/						
				}						
			}
			
			/* Count the remaining disjuncts */
			int count_disj = 0;
			for (int i = 0; i < termArg0Disjuncts.length; i++)
			{
				if (disjunctsNotPivot[i])
					count_disj++;
			}
			
//			if (disjunctsAdd.size() > 0)
//			{
//				System.out.print("count_disj: " + count_disj);
//			}
			count_disj += disjunctsAdd.size();
//			if (disjunctsAdd.size() > 0)
//			{
//				System.out.println(" -> " + count_disj);
//			}
			
			
			/* Different handling for a different number of conjuncts is needed */
			switch (count_disj)
			{
			case 0:	
				//System.out.println("Red");
				stackPush(smtInterpol.term("false"), term);
				return;
			case 1:
				//System.out.println("Green");
				for (int i = 0; i < termArg0Disjuncts.length; i++)
				{
					if (i >= disjunctsNotPivot.length)
					{
						throw new AssertionError("Error: disjunctsNotPivot ist zu kurz: " 
								+ disjunctsNotPivot.length + " statt " + termArg0Disjuncts.length + ".");
					}
					if (disjunctsNotPivot[i])
					{	
						stackPush(termArg0Disjuncts[i], term);					
						return;
					}					
				}			
				
				// So the one element has to be in the list
				if (disjunctsAdd.size() == 0)
				{
					throw new AssertionError("Error: Couldn't find the one disjunct I shall return.");
				}
												
				stackPush(disjunctsAdd.get(0), term);
				return;
			default:
				//System.out.println("Blue");
				
				//Build an array that contains only the disjuncts, that have to be returned
				Term[] disjunctsReturn = new Term[count_disj];
				int i_disjRet = 0; //Counts through the to be returned disjuncts
				
				// i_disjOrig counts through the original disjuncts
				for (int i_disjOrig = 0; i_disjOrig < termArg0Disjuncts.length; i_disjOrig ++) 
				{
					if (disjunctsNotPivot[i_disjOrig])
					{
						if (i_disjRet < count_disj) //Makes sense, since count_disj = disjunctsReturn.length;
						{
							disjunctsReturn[i_disjRet] = termArg0Disjuncts[i_disjOrig];
							i_disjRet++;
						} else {
							throw new AssertionError("Error: A total unexpected miscalculation occured. Random number: 638402");
						}
					}
				}
				if (disjunctsReturn.length - i_disjRet != disjunctsAdd.size())
				{
					throw new AssertionError("Error: I'd like to fill up the to be returned disjuncts with "
							+ "the list of \"to be added\"-disjuncts, but the size doesn't fit. The list has "
							+ "size " + disjunctsAdd.size() + " and there is/are " 
							+ (disjunctsReturn.length - i_disjRet) + " = " + disjunctsReturn.length + " - "
							+ i_disjRet + " free space(s).");									
				}
				
				// Now add the "to be added"-disjuncts
				int p = 0; //counts through the list
				while (i_disjRet < disjunctsReturn.length)
				{
					disjunctsReturn[i_disjRet] = disjunctsAdd.get(p);
					//disjunctsReturn[d] = disjunctsAdd.remove(0); Could bet more effective, but is untested
					i_disjRet++;
					p++;
				}
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
			Term[] termAppParam1CalcDisjuncts = null;
			Term[] termAppParam2CalcDisjuncts = null;
			
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
				termAppParam1CalcDisjuncts = termAppParam1CalcApp.getParameters(); //Just needed to fasten things up.
			} else
			{
				termAppParam1CalcDisjuncts = new Term[1];
				termAppParam1CalcDisjuncts[0] = termAppParam1Calc;
			}
			
			if (multiDisjunct2)
			{
				termAppParam2CalcDisjuncts = termAppParam2CalcApp.getParameters(); //Just needed to fasten things up.
			} else
			{
				termAppParam2CalcDisjuncts = new Term[1];
				termAppParam2CalcDisjuncts[0] = termAppParam2Calc;
			}
			

			/* Check if the clause operation was correct. Each later disjunct has to be in the first disjunction.
			 *  OLD: Actually more has to hold, but this is enough for the proof to be correct.
			 *  TODO: That must be wrong, it's a permutation!
			 */
			
			boolean found;
			boolean[] foundArray = new boolean[termAppParam1CalcDisjuncts.length];
			for (int j = 0; j < termAppParam1CalcDisjuncts.length; j++)
			{
				foundArray[j] = false;
			}
			
			
			for (int i = 0; i < termAppParam2CalcDisjuncts.length; i++)
			{
				found = false;
				// TODO: Is the following sentence correct?: False counts as always found, since it's the empty disjunction
				if (termAppParam2CalcDisjuncts[i] == smtInterpol.term("false"))
				{
					found = true;
				}
				
				for (int j = 0; j < termAppParam1CalcDisjuncts.length && !found; j++)
				{
					if (termAppParam1CalcDisjuncts[j] == termAppParam2CalcDisjuncts[i])
					{
						foundArray[j] = true;
						found = true;
						//break; Not needed, because of the condition in the for-loop
					}
				}
				if (!found && powLev < 2)
				{
					throw new AssertionError("Error: Couldn't find the disjunct " 
							+ termAppParam2CalcDisjuncts[i].toStringDirect() + " in the disjunction "
							+ termAppParam1Calc.toStringDirect() + ".");
				} else if (!found)
				{
					//System.out.println("Warning: The level of power had an effect.");
				}
			}
			
			// TODO: Is this really necessary?
			for (int j = 0; j < termAppParam1CalcDisjuncts.length; j++)
			{
				if (!foundArray[j]  && powLev < 1)
				{
					throw new AssertionError("Error: Couldn't reverse-find the disjunct " 
							+ termAppParam1CalcDisjuncts[j].toStringDirect() + " in the disjunction "
							+ termAppParam2Calc.toStringDirect() + ".");
				}
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
	public void calcParams(ApplicationTerm appTerm)
	{
		Term[] params = appTerm.getParameters();
		
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
			@Override
			public void convert(Term t) {
				if (t == termDelete)
				{
					setResult(termInsert);
				} else
				{
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
}





