/*
 * Copyright (C) 2009-2014 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.smtinterpol.interpolate;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Clause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;
import de.uni_freiburg.informatik.ultimate.smtinterpol.interpolate.CCInterpolator.PathInfo.PathEnd;
import de.uni_freiburg.informatik.ultimate.smtinterpol.interpolate.Interpolator.LitInfo;
import de.uni_freiburg.informatik.ultimate.smtinterpol.interpolate.Interpolator.Occurrence;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.ArrayAnnotation;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CCAppTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CCBaseTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CCEquality;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CCTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.SymmetricPair;

public class ArrayInterpolator extends CCInterpolator {
	HashMap<SymmetricPair<CCTerm>, CCEquality> mDisequalities;
	HashMap<SymmetricPair<CCTerm>, HashMap<CCTerm, WeakPathInfo>> mWeakPaths;
	
	class WeakPathInfo extends PathInfo {
		CCTerm mIndex;
		
		class WeakPathEnd extends PathEnd {
			int[]    mNumDiffs;
			CCTerm[] mIndexConstraints;
			CCTerm[] mSharedIndex;
		}
		
		public WeakPathInfo(CCTerm[] path, CCTerm index) {
			super(path);
			mIndex = index;
		}
		
		private boolean isCongruence(CCAppTerm app1, CCAppTerm app2) {
			while (true) {
				if (!mWeakPaths.containsKey(
						new SymmetricPair<CCTerm>(app1.getArg(), app2.getArg())))
					return false;
				if (app1.getFunc() == app2.getFunc())
					return true;
				if (!(app1.getFunc() instanceof CCAppTerm)
					|| !(app2.getFunc() instanceof CCAppTerm))
					return false;
				app1 = (CCAppTerm) app1.getFunc();
				app2 = (CCAppTerm) app2.getFunc();
			}
		}
		
		private boolean isSelectStep(CCAppTerm app1, CCAppTerm app2) {
			if (!(app1.getFunc() instanceof CCAppTerm)
				|| !(app2.getFunc() instanceof CCAppTerm))
				return false;
			
			CCAppTerm selArray1 = (CCAppTerm) app1.getFunc();
			CCAppTerm selArray2 = (CCAppTerm) app2.getFunc();
			if (selArray1.getFunc() != selArray2.getFunc()
				|| !(selArray1.getFunc() instanceof CCBaseTerm))
				return false;
			if (!((CCBaseTerm) selArray1.getFunc()).isFunctionSymbol()
				|| ((CCBaseTerm) selArray1.getFunc()).getFunctionSymbol()
					.getName() != "select")
				return false;
			if (!mPaths.containsKey(
					new SymmetricPair<CCTerm>(app1.getArg(), app2.getArg())))
				return false;
			HashMap<CCTerm, WeakPathInfo> weakPaths = mWeakPaths.get(
					new SymmetricPair<CCTerm>(selArray1.getArg(), 
							selArray2.getArg()));
			if (weakPaths == null)
				return false;
			return weakPaths.containsKey(app1.getArg())
				|| weakPaths.containsKey(app2.getArg());
		}
		
		public void interpolatePathInfo() {
			if (mComputed)
				return;
			Occurrence headOccur = 
					mInterpolator.getOccurrence(mPath[0].getFlatTerm());
			mHead = mIndex == null ? new PathEnd() : new WeakPathEnd();
			mTail = mIndex == null ? new PathEnd() : new WeakPathEnd();
			mTail.closeAPath(mHead, null, headOccur);
			mTail.openAPath(mHead, null, headOccur);
			
			for (int i = 0; i < mPath.length - 1; i++) {
				CCTerm left = mPath[i];
				CCTerm right = mPath[i + 1];
				CCEquality lit =
						mEqualities.get(new SymmetricPair<CCTerm>(left, right));
				if (lit != null) {
					LitInfo info = mInterpolator.getLiteralInfo(lit);
					Term boundaryTerm;
					boundaryTerm = mPath[i].toSMTTerm(mTheory);
					if (info.getMixedVar() == null) {
						mTail.closeAPath(mHead, boundaryTerm, info);
						mTail.openAPath(mHead, boundaryTerm, info);
					} else {
						mTail.closeAPath(mHead, boundaryTerm, info);
						mTail.openAPath(mHead, boundaryTerm, info);
						Occurrence occ = mInterpolator.getOccurrence(
								mPath[i + 1].getFlatTerm());
						boundaryTerm = info.getMixedVar();
						mTail.closeAPath(mHead, boundaryTerm, occ);
						mTail.openAPath(mHead, boundaryTerm, occ);
					}
					continue;
				}
				if (left instanceof CCAppTerm && right instanceof CCAppTerm) {
					CCAppTerm leftApp = (CCAppTerm) left;
					CCAppTerm rightApp = (CCAppTerm) right;
					if (isCongruence(leftApp, rightApp)) {
						mTail.mergeCongPath(mHead, leftApp, rightApp);
						continue;
					}
					if (isSelectStep(leftApp, rightApp)) {
						mTail.mergeSelect(mHead, leftApp, rightApp);
						continue;
					}
				}
				// TODO Handle select in weak path.
				throw new UnsupportedOperationException(
						"Cannot interpolate weakeq-ext");
			}
			mComputed = true;
		}
	}


	public ArrayInterpolator(Interpolator interpolator) {
		super(interpolator);
	}
	
	public void collectLiterals(Clause cl) {
		mDisequalities = new HashMap<SymmetricPair<CCTerm>,  CCEquality>();
		super.collectLiterals(cl);
		for (int i = 0; i < cl.getSize(); i++) {
			Literal lit = cl.getLiteral(i);
			if (lit instanceof CCEquality) {
				CCEquality eq = (CCEquality) lit;
				SymmetricPair<CCTerm> pair =
						new SymmetricPair<CCTerm>(eq.getLhs(), eq.getRhs());
				mDisequalities.put(pair, eq);
			}
		}
	}

	public WeakPathInfo collectPaths(CCTerm[][] paths, CCTerm[] weakIndices) {
		assert paths.length == weakIndices.length;
		WeakPathInfo mainPath = null;
		mPaths = new HashMap<SymmetricPair<CCTerm>, PathInfo>();
		mWeakPaths = new HashMap<SymmetricPair<CCTerm>,
				HashMap<CCTerm, WeakPathInfo>>();
		for (int i = 0; i < paths.length; i++) {
			CCTerm first = paths[i][0];
			CCTerm last = paths[i][paths[i].length - 1];
			WeakPathInfo pathInfo = new WeakPathInfo(paths[i], weakIndices[i]);
			SymmetricPair<CCTerm> pair = new SymmetricPair<CCTerm>(first, last);
			if (weakIndices[i] == null) {
				mPaths.put(pair, pathInfo);
			} else {
				HashMap<CCTerm, WeakPathInfo> weakMap = mWeakPaths.get(pair);
				if (weakMap == null) {
					weakMap = new HashMap<CCTerm, WeakPathInfo>();
					mWeakPaths.put(pair, weakMap);
				}
				weakMap.put(weakIndices[i], pathInfo);
			}
			if (i == 0)
				mainPath = pathInfo;
		}
		return mainPath;
	}

	@SuppressWarnings("unchecked")
	public Interpolant[] computeInterpolants(Clause cl, ArrayAnnotation annot) {
		mInterpolants = new Set[mNumInterpolants];
		for (int i = 0; i < mNumInterpolants; i++)
			mInterpolants[i] = new HashSet<Term>();
		collectLiterals(cl);
		PathInfo mainPath = collectPaths(annot.getPaths(), 
				annot.getWeakIndices());

		mainPath.interpolatePathInfo();
		CCEquality diseq = annot.getDiseq();
		if (diseq != null)
			mainPath.addDiseq(diseq);
		mainPath.close();
		mEqualities = null;
		mDisequalities = null;
		mPaths = null;
		Interpolant[] interpolants = new Interpolant[mNumInterpolants];
		for (int i = 0; i < mNumInterpolants; i++) {
			interpolants[i] = new Interpolant(
					mTheory.and(mInterpolants[i].toArray(
							new Term[mInterpolants[i].size()])));
		}
		mInterpolants = null;
		return interpolants;
	}
}
