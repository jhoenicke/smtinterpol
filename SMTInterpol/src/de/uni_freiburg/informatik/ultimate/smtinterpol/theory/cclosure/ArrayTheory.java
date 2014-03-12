/*
 * Copyright (C) 2014 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.Clausifier;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Clause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.ITheory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;
import de.uni_freiburg.informatik.ultimate.smtinterpol.model.Model;
import de.uni_freiburg.informatik.ultimate.smtinterpol.model.SharedTermEvaluator;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CCAppTerm.Parent;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.WeakEQEntry.EntryPair;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.SymmetricPair;
import de.uni_freiburg.informatik.ultimate.util.ScopedArrayList;
import de.uni_freiburg.informatik.ultimate.util.ScopedHashSet;

/**
 * Array theory solver based on weak equivalence classes.
 * 
 * TODO For this version, I always explain paths that already exist.  It might
 * be a good idea to shorten the lemmas generated by this solver by introducing
 * new equality literals instead of adding paths.
 * @author Juergen Christ
 */
public class ArrayTheory implements ITheory {

	private final Clausifier mClausifier;
	private final CClosure mCClosure;
	
	private final int mSelectFunNum;
//	private final int mStoreFunNum;
	
	private final ScopedArrayList<CCTerm> mArrays =
			new ScopedArrayList<CCTerm>();
	private final ScopedHashSet<CCTerm> mStores =
			new ScopedHashSet<CCTerm>();
	
	private final ArrayDeque<Literal> mSuggestions = new ArrayDeque<Literal>();
	
	private HashMap<SymmetricPair<CCTerm>, WeakEQEntry> mWeakEq;
	
	private final Logger mLogger;
	
	/// Cache for the congruence roots;
	Set<CCTerm> mCongRoots = null;
	private boolean mSelectsComputed = false;
	
	// =============== STATISTICS ===============
	private int mNumInstsSelect = 0;
	private int mNumInstsEq = 0;
	private int mNumSuggestions = 0;
	private int mNumBuildWeakEQ = 0;
	private int mNumAddStores = 0;
	private int mNumMerges = 0;
	private int mNumModuloEdges = 0;
	private long mTimeBuildWeakEq = 0;
	private long mTimeBuildWeakEqi = 0;
	
	private int mNumArrays = 0;
	
	public ArrayTheory(Clausifier clausifier, CClosure cclosure) {
		mClausifier = clausifier;
		mCClosure = cclosure;
		mCClosure.initArrays();
//		mStoreFunNum = mCClosure.getStoreNum();
		mSelectFunNum = mCClosure.getSelectNum();
		mLogger = mCClosure.mEngine.getLogger();
	}
	
	@Override
	public Clause startCheck() {
		return null;
	}

	@Override
	public void endCheck() {
		// Nothing to do
	}

	@Override
	public Clause setLiteral(Literal literal) {
		return null;
	}

	@Override
	public void backtrackLiteral(Literal literal) {
		// Nothing to do
	}

	@Override
	public Clause checkpoint() {
		return null;
	}

	@Override
	public Clause computeConflictClause() {
		// Reinit the cache
		mCongRoots = null;
		buildWeakEq();
		computeSelects();
		boolean foundLemma = computeSelectOverWeakeq();
		if (!foundLemma) {
			buildWeakEQi();
			clearSelects();
			computeWeakeqExt();
		}
		// Free the cache
		clearSelects();
		mCongRoots = null;
		// We have to recompute mWeakEq every time since it might have changed
		mWeakEq = null;
		return null;
	}

	@Override
	public Literal getPropagatedLiteral() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Clause getUnitClause(Literal literal) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Literal getSuggestion() {
		while (!mSuggestions.isEmpty()) {
			Literal lit = mSuggestions.poll();
			if (lit.getAtom().getDecideStatus() == null) {
				++mNumSuggestions;
				return lit;
			}
		}
		return null;
	}

	@Override
	public void printStatistics(Logger logger) {
		if (logger.isInfoEnabled()) {
			logger.info(String.format(
					"Array: #Arrays: %d, #BuildWeakEQ: %d, #ModEdges: %d, "
					+ "#addStores: %d, #merges: %d", mNumArrays,
					mNumBuildWeakEQ, mNumModuloEdges, mNumAddStores, mNumMerges));
			logger.info("Path Suggestions: " + mNumSuggestions);
			logger.info(String.format(
					"Insts: ReadOverWeakEQ: %d, WeakeqExt: %d",
					mNumInstsSelect, mNumInstsEq));
			logger.info(String.format("Time: BuildWeakEq: %d, BuildWeakEqi: %d",
					mTimeBuildWeakEq, mTimeBuildWeakEqi));
		}

	}

	@Override
	public void dumpModel(Logger logger) {
		// TODO Auto-generated method stub

	}

	@Override
	public void increasedDecideLevel(int currentDecideLevel) {
		// Nothing to do
	}

	@Override
	public void decreasedDecideLevel(int currentDecideLevel) {
		// Nothing to do
	}

	@Override
	public Clause backtrackComplete() {
		mSuggestions.clear();
		mWeakEq = null;
		mCongRoots = null;
		clearSelects();
		return null;
	}

	@Override
	public void restart(int iteration) {
		// Nothing to do
	}

	@Override
	public void removeAtom(DPLLAtom atom) {
		// Nothing to do
	}

	@Override
	public Object push() {
		mArrays.beginScope();
		mStores.beginScope();
		return Integer.valueOf(mNumArrays);
	}

	@Override
	public void pop(Object object, int targetlevel) {
		mNumArrays = ((Integer) object).intValue();
		mStores.endScope();
		mArrays.endScope();
	}

	@Override
	public Object[] getStatistics() {
		return new Object[]{
			":Array", new Object[][]{
				{"NumArrays", mNumArrays},
				{"BuildWeakEQ", mNumBuildWeakEQ},
				{"AddStores", mNumAddStores},
				{"Merges", mNumMerges},
				{"ModuloEdges", mNumModuloEdges},
				{"PathSuggestions", mNumSuggestions},
				{"ReadOverWeakeq", mNumInstsSelect},
				{"WeakeqExt", mNumInstsEq},
				{"Times", new Object[][]{
					{"BuildWeakEq", mTimeBuildWeakEq},
					{"BuildWeakEqi", mTimeBuildWeakEqi}
				}}
			}};
	}

	@Override
	public void fillInModel(Model model, Theory t, SharedTermEvaluator ste) {
		// TODO Auto-generated method stub

	}
	
	public void notifyArray(CCTerm array, boolean isStore) {
		if (isStore)
			mStores.add(array);
		else
			mArrays.add(array);
		array.initArray(mNumArrays++);
	}
	
	static CCTerm getArrayFromStore(CCTerm store) {
		return ((CCAppTerm) ((CCAppTerm) 
				((CCAppTerm) store).getFunc()).getFunc()).getArg();
	}
	
	static CCTerm getIndexFromStore(CCTerm store) {
		return ((CCAppTerm) ((CCAppTerm) store).getFunc()).getArg();
	}
	
	static CCTerm getValueFromStore(CCTerm store) {
		return ((CCAppTerm) store).getArg();
	}
	
	private final boolean isInOrder(SymmetricPair<CCTerm> idx) {
		return idx.getFirst().mArrayNum < idx.getSecond().mArrayNum;
	}
	
	private void buildWeakEq() {
		if (mWeakEq != null)
			return;
//		System.err.println("Num Stores: " + mStores.size());
//		System.err.println("Start buildWeakEq");
		++mNumBuildWeakEQ;
		long startTime = System.nanoTime();
		mWeakEq = new HashMap<SymmetricPair<CCTerm>, WeakEQEntry>();
		Deque<SymmetricPair<CCTerm>> todo = new ArrayDeque<SymmetricPair<CCTerm>>();
		// Add all stores
		for (CCTerm store : mStores) {
			CCTerm array = getArrayFromStore(store);
			if (store.mRepStar != array.mRepStar) {
				SymmetricPair<CCTerm> idx =
						new SymmetricPair<CCTerm>(store.mRepStar, array.mRepStar);
				WeakEQEntry entry = mWeakEq.get(idx);
				if (entry == null) {
					entry = new WeakEQEntry();
					mWeakEq.put(idx, entry);
				}
				if (entry.addStore(store)) {
					++mNumAddStores;
					todo.add(idx);
				}
			}
		}
		Set<CCTerm> roots = getCongruenceRoots();
//		System.err.println("Num Congroots: " + roots.size());
		// saturate
		SymmetricPair<CCTerm> next;
		while ((next = todo.poll()) != null) {
			assert next.getFirst() == next.getFirst().mRepStar;
			assert next.getSecond() == next.getSecond().mRepStar;
//			System.err.println(todo.size());
			for (CCTerm root : roots) {
				assert root == root.mRepStar;
				if (root != next.getFirst() && root != next.getSecond()) {
					// Extend path from left
					SymmetricPair<CCTerm> idxLeft =
							new SymmetricPair<CCTerm>(root, next.getFirst());
					WeakEQEntry left = mWeakEq.get(idxLeft);
					if (!todo.contains(idxLeft) && left != null) {
						assert left.invariant(idxLeft.getFirst(), idxLeft.getSecond());
						SymmetricPair<CCTerm> leftRes =
								new SymmetricPair<CCTerm>(root, next.getSecond());
						WeakEQEntry res = mWeakEq.get(leftRes);
						if (res == null) {
//							System.err.println("New entry for " + leftRes);
							res = new WeakEQEntry();
							mWeakEq.put(leftRes, res);
						}
						WeakEQEntry right = mWeakEq.get(next);
						assert right != null;
						assert right.invariant(next.getFirst(), next.getSecond());
						assert res.invariant(leftRes.getFirst(), leftRes.getSecond());
//						System.err.println("Merging " + res + " <= " + left + " Y " + right);
						if (res.merge(left, isInOrder(idxLeft), right, 
								isInOrder(next), isInOrder(leftRes))) {
//							System.err.println("Merged " + idxLeft + " Y " + next);
							assert res.invariant(leftRes.getFirst(), leftRes.getSecond());
//							System.err.println("Success: " + res);
							++mNumMerges;
							todo.add(leftRes);
						}
					}
					// Extend path to the right
					SymmetricPair<CCTerm> idxRight =
							new SymmetricPair<CCTerm>(next.getSecond(), root);
					WeakEQEntry right = mWeakEq.get(idxRight);
					if (!todo.contains(idxRight) && right != null) {
						assert right.invariant(idxRight.getFirst(), idxRight.getSecond());
						SymmetricPair<CCTerm> rightRes =
								new SymmetricPair<CCTerm>(next.getFirst(), root);
						WeakEQEntry res = mWeakEq.get(rightRes);
						if (res == null) {
//							System.err.println("New entry for " + rightRes);
							res = new WeakEQEntry();
							mWeakEq.put(rightRes, res);
						}
						left = mWeakEq.get(next);
						assert left != null;
						assert left.invariant(next.getFirst(), next.getSecond());
						assert res.invariant(rightRes.getFirst(), rightRes.getSecond());
//						System.err.println("Merging " + res + " <= " + left + " Y " + right);
						if (res.merge(left, isInOrder(next), right,
								isInOrder(idxRight), isInOrder(rightRes))) {
//							System.err.println("Merged " + next + " Y " + idxRight);
							assert res.invariant(rightRes.getFirst(), rightRes.getSecond());
//							System.err.println("Success");
							++mNumMerges;
							todo.add(rightRes);
						}
					}
				}
			}
		}
		mTimeBuildWeakEq += (System.nanoTime() - startTime);
//		System.err.println("End buildWeakEq");
	}
	
	private void buildWeakEQi() {
		assert mSelectsComputed : "Need selects per eq class";
		long startTime = System.nanoTime();
		ArrayList<SymmetricPair<CCTerm>> changed =
				new ArrayList<SymmetricPair<CCTerm>>();
		// init
		for (Entry<SymmetricPair<CCTerm>, WeakEQEntry> me : mWeakEq.entrySet()) {
			for (Entry<CCTerm, EntryPair> weakme
					: me.getValue().getEntries().entrySet()) {
				if (weakme.getValue() == null) {
					WeakEQiEntry modi = findCongruentSelect(
							me.getKey().getFirst(), me.getKey().getSecond(),
							weakme.getKey(), isInOrder(me.getKey()));
					if (modi != null) {
						++mNumModuloEdges;
						me.getValue().addModEdge(weakme.getKey(), modi);
						changed.add(me.getKey());
					}
				}
			}
		}
		// saturate
		Set<CCTerm> roots = getCongruenceRoots();
		for (SymmetricPair<CCTerm> p : changed) {
			WeakEQEntry pentry = mWeakEq.get(p);
			for (CCTerm u : roots) {
				if (u == p.getSecond())
					continue;
				WeakEQEntry ufpath = mWeakEq.get(
						new SymmetricPair<CCTerm>(u, p.getFirst()));
				if (ufpath == null)
					continue;
				for (CCTerm v : roots) {
					if (u == v || v == p.getFirst())
						continue;
					WeakEQEntry svpath = mWeakEq.get(
							new SymmetricPair<CCTerm>(p.getSecond(), v));
					if (svpath == null)
						continue;
					WeakEQEntry uvpath = mWeakEq.get(
							new SymmetricPair<CCTerm>(u, v));
					if (uvpath == null)
						continue;
					for (Entry<CCTerm, WeakEQiEntry> e
							: pentry.getModuloEdges().entrySet()) {
						CCTerm idx = e.getKey();
						if (uvpath.getConnection(idx) == null
								&& uvpath.getModuloPath(idx) == null) {
							// Check u -- p.getFirst()
							if (ufpath.getConnection(idx) == null)
								continue;
							// Check p.getSecond() -- v
							if (svpath.getConnection(idx) == null)
								continue;
							// add weakeq modulo i path
							uvpath.addModEdge(idx,
									new WeakEQiEntry(p.getFirst(), p.getSecond(),
											u.mArrayNum < v.mArrayNum));
						}
					}
				}
			}
		}
		mTimeBuildWeakEqi += (System.nanoTime() - startTime);
	}
	
	private void computeSelects() {
		if (mSelectsComputed)
			return;
		Set<CCTerm> roots = getCongruenceRoots();
		for (CCTerm root : roots) {
			HashMap<CCTerm, CCAppTerm> selects = new HashMap<CCTerm, CCAppTerm>();
			CCParentInfo info = root.mCCPars.getExistingParentInfo(mSelectFunNum);
			if (info != null) {
				for (CCAppTerm.Parent pa : info.mCCParents) {
					CCParentInfo selectas = pa.getData().mRepStar.mCCPars
							.getExistingParentInfo(0);
					for (CCAppTerm.Parent spa : selectas.mCCParents) {
						CCAppTerm select = spa.getData();
						selects.put(select.mArg.mRepStar, select);
					}
				}
			}
			root.mSelects = selects;
		}
		mSelectsComputed = true;
	}
	
	private void clearSelects() {
		if (mSelectsComputed) {
			Set<CCTerm> roots = getCongruenceRoots();
			for (CCTerm root : roots)
				root.mSelects = null;
			mSelectsComputed = false;
		}
	}
	
	/**
	 * Compute all read-over-weakeq instances.
	 * @return <code>true</code> if and only if we found a new instance.
	 */
	private boolean computeSelectOverWeakeq() {
		boolean res = false;
		for (Entry<SymmetricPair<CCTerm>, WeakEQEntry> me : mWeakEq.entrySet()) {
			CCTerm left = me.getKey().getFirst();
			CCTerm right = me.getKey().getSecond();
			Map<CCTerm, CCAppTerm> leftselects = left.mSelects;
			Map<CCTerm, CCAppTerm> rightselects = right.mSelects;
			if (leftselects.size() > rightselects.size()) {
				CCTerm tmp = left;
				left = right;
				right = tmp;
				Map<CCTerm, CCAppTerm> tmpselects = leftselects;
				leftselects = rightselects;
				rightselects = tmpselects;
			}
			// Now, leftselects is the smaller map
			for (Entry<CCTerm, CCAppTerm> sel : leftselects.entrySet()) {
				if (me.getValue().getConnection(sel.getKey()) == null)
					// There are only paths with at least one edge labeled by
					// something congruent to sel.getKey()
					// ==> read-over-weakeq not applicable
					continue;
				CCAppTerm rightsel = rightselects.get(sel.getKey());
				if (rightsel != null
						&& sel.getValue().mRepStar != rightsel.mRepStar) {
					// Found an instance
					++mNumInstsSelect;
					WeakCongruencePath path = new WeakCongruencePath(this);
					Clause lemma = path.computeSelectOverWeakEQ(
							sel.getValue(), rightsel, mWeakEq,
							mCClosure.mEngine.isProofGenerationEnabled(),
							mSuggestions);
					if (mLogger.isDebugEnabled())
						mLogger.debug("AL sw: " + lemma);
					// TODO Should we really add all lemmata
					// TODO Maybe use n-watched clause to propagate
					// I learn clauses here to have them removed by clause GC
					mCClosure.mEngine.learnClause(lemma);
					res = true;
				}
			}
		}
		return res;
	}
	
	/**
	 * Compute all weakeq-ext instances.
	 * @return <code>true</code> if and only if we found a new instance.
	 */
	private boolean computeWeakeqExt() {
		boolean res = false;
		for (Entry<SymmetricPair<CCTerm>, WeakEQEntry> me : mWeakEq.entrySet()) {
			// We simply check if there is a path for all store indices in
			// WeakEQEntry here.
			boolean equal = true;
			for (Entry<CCTerm, EntryPair> storepath
					: me.getValue().getEntries().entrySet()) {
				if (storepath.getValue() == null) {
					WeakEQiEntry modulo =
							me.getValue().getModuloPath(storepath.getKey());
					if (modulo == null) {
						equal = false;
						break;
					}
				}
			}
			if (equal) {
				// We found an instance
				++mNumInstsEq;
				WeakCongruencePath path = new WeakCongruencePath(this);
				Clause lemma = path.computeWeakeqExt(
						me.getKey().getFirst(), me.getKey().getSecond(),
						me.getValue(), mWeakEq,
						mCClosure.mEngine.isProofGenerationEnabled(),
						mSuggestions);
				if (mLogger.isDebugEnabled())
					mLogger.debug("AL we: " + lemma);
				// TODO Should we really add all lemmata
				// TODO Maybe use n-watched clause to propagate
				// I learn clauses here to have them removed by clause GC
				mCClosure.mEngine.learnClause(lemma);
				res = true;
			}
		}
		return res;
	}

	private Set<CCTerm> getCongruenceRoots() {
		if (mCongRoots == null) {
			mCongRoots = new HashSet<CCTerm>();
			for (CCTerm a : mArrays)
				mCongRoots.add(a.getRepresentative());
			for (CCTerm a : mStores)
				mCongRoots.add(a.getRepresentative());
		}
		return mCongRoots;
	}

	/**
	 * Find two selects in the congruence classes of <code>left</code> resp.
	 * <code>right</code> such that the both select an index congruent to
	 * <code>idx</code> and the selects are congruent.
	 * @param left  The left array.
	 * @param right The right array.
	 * @param idx   The index to search selects for.
	 * @param order Is the pair in the expected order?
	 * @return Information about congruent selects or <code>null</code> if no
	 *         congruent selects exist.
	 */
	private WeakEQiEntry findCongruentSelect(
			CCTerm left, CCTerm right, CCTerm idx, boolean order) {
		assert left.mRepStar == left;
		assert right.mRepStar == right;
		assert idx.mRepStar == idx;
		CCParentInfo selects =
			idx.mCCPars.getExistingParentInfo(mSelectFunNum + 1);
		CCAppTerm leftSelect = null;
		CCAppTerm rightSelect = null;
		if (selects != null) {
			// selects are all select terms where the index is congruent to idx
			for (Parent pa : selects.mCCParents) {
				CCTerm array = ((CCAppTerm) pa.getData().mFunc).mArg;
				if (leftSelect == null && array.mRepStar == left) {
					// found read on left
					leftSelect = pa.getData();
					if (rightSelect != null)
						return leftSelect.mRepStar == rightSelect.mRepStar
							? new WeakEQiEntry(leftSelect, rightSelect, order)
								: null;
				}
				if (rightSelect == null && array.mRepStar == right) {
					// found read on right
					rightSelect = pa.getData();
					if (leftSelect != null)
						return leftSelect.mRepStar == rightSelect.mRepStar
							? new WeakEQiEntry(leftSelect, rightSelect, order)
								: null;
				}
			}
		}
		return null;
	}
	
	CClosure getCClosure() {
		return mCClosure;
	}
	
	Clausifier getClausifier() {
		return mClausifier;
	}
	
	boolean isStore(CCTerm term) {
		return mStores.contains(term);
	}
}
