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
package de.uni_freiburg.informatik.ultimate.smtinterpol.model;

import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.FormulaUnLet;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.Clausifier;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.BooleanVarAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.ITheory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.ArrayTheory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CClosure;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.linar.LinArSolve;

/**
 * A model represented as injection between integers and domain values.  The
 * integers should be positive.  Furthermore, the model reserves <code>-1</code>
 * for undefined values, <code>0</code> for the default value, and
 * <code>1</code> for the second value.
 * @author Juergen Christ
 */
public class Model implements de.uni_freiburg.informatik.ultimate.logic.Model {
	
	private final HashMap<Sort, SortInterpretation> mSorts =
		new HashMap<Sort, SortInterpretation>();
	
	private final HashMap<Sort, ArraySortInterpretation> mArraySorts =
			new HashMap<Sort, ArraySortInterpretation>();
	
	private final BoolSortInterpretation mBoolSort;
	
	private final NumericSortInterpretation mNumSorts;
	
	private final HashMap<FunctionSymbol, FunctionValue> mFuncVals =
		new HashMap<FunctionSymbol, FunctionValue>();
	
	private final Theory mTheory;
	
	private final ModelEvaluator mEval;
	
	private final FormulaUnLet mUnlet = new FormulaUnLet(
			FormulaUnLet.UnletType.EXPAND_DEFINITIONS);
	
	private final boolean mPartialModel;
	
	public Model(Clausifier clausifier, Theory t, boolean partial) {
		mTheory = t;
		mPartialModel = partial;
		mBoolSort = new BoolSortInterpretation();
		mNumSorts = new NumericSortInterpretation();
		// Extract Boolean model
		FunctionValue trueValue = new FunctionValue(mBoolSort.getTrueIdx());
		FunctionValue falseValue = new FunctionValue(mBoolSort.getFalseIdx());
		for (BooleanVarAtom atom : clausifier.getBooleanVars()) {
			ApplicationTerm at = (ApplicationTerm) atom.getSMTFormula(t);
			FunctionValue value;
			if (atom.getDecideStatus() == null)
				value = atom.getPreferredStatus() == atom 
						? trueValue : falseValue;
			else
				value = atom.getDecideStatus() == atom ? trueValue : falseValue;
			mFuncVals.put(at.getFunction(), value);
		}
		// Extract different theories
		CClosure cc = clausifier.getCClosure();
		LinArSolve la = null;
		ArrayTheory array = null;
		for (ITheory theory : clausifier.getEngine().getAttachedTheories()) {
			if (theory instanceof LinArSolve)
				la = (LinArSolve) theory;
			else if (theory instanceof ArrayTheory)
				array = (ArrayTheory) theory;
			else if (theory != cc)
				throw new InternalError(
					"Modelproduction for theory not implemented: " + theory);
		}
		SharedTermEvaluator ste = new SharedTermEvaluator(la);
		if (la != null)
			la.fillInModel(this, t, ste);
		if (cc != null)
			cc.fillInModel(this, t, ste);
		if (array != null)
			array.fillInModel(this, t, ste);
		mEval = new ModelEvaluator(this);
	}
	
	public int getFalseIdx() {
		return mBoolSort.getFalseIdx();
	}
	
	public int getTrueIdx() {
		return mBoolSort.getTrueIdx();
	}
	
	public int extendNumeric(FunctionSymbol fsym, Rational rat) {
		assert fsym.getReturnSort().isNumericSort();
		int idx = mNumSorts.extend(rat);
		mFuncVals.put(fsym, new FunctionValue(idx));
		return idx;
	}
	
	public int putNumeric(Rational rat) {
		return mNumSorts.extend(rat);
	}
	
	public int extendFresh(Sort s) {
		if (s.isArraySort()) {
			ArraySortInterpretation si = mArraySorts.get(s);
			if (si == null) {
				si = new ArraySortInterpretation(
						provideSortInterpretation(s.getArguments()[0]),
						provideSortInterpretation(s.getArguments()[1]));
				mArraySorts.put(s, si);
			}
			return si.extendFresh();
		}
		SortInterpretation si = mSorts.get(s);
		if (si == null) {
			si = new FiniteSortInterpretation();
			mSorts.put(s, si);
		}
		return si.extendFresh();
	}
	
	public FunctionValue map(FunctionSymbol fs, int value) {
		FunctionValue res = mFuncVals.get(fs);
		if (res == null) {
			res = new FunctionValue(value);
			mFuncVals.put(fs, res);
		}
		assert res.getDefault() == value;
		return res;
	}
	
	public FunctionValue map(FunctionSymbol fs, int[] args, int value) {
		assert fs.getParameterSorts().length == args.length;
		FunctionValue val = mFuncVals.get(fs);
		if (val == null) {
			val = new FunctionValue();
			mFuncVals.put(fs, val);
		}
		val.put(value, args);
		return val;
	}
	
	Term getUndefined(Sort s) {
		FunctionSymbol fsym = mTheory.getFunctionWithResult(
				"@undefined", null, s);
		return mTheory.term(fsym);
	}

	
	@Override
	public Term evaluate(Term input) {
		Term unletted = mUnlet.unlet(input);
		return mEval.evaluate(unletted);
	}

	@Override
	public Map<Term, Term> evaluate(Term[] input) {
		LinkedHashMap<Term, Term> values = new LinkedHashMap<Term, Term>();
		for (Term t : input)
			values.put(t, evaluate(t));
		return values;
	}
	
	public String toString() {
		ModelFormatter mf = new ModelFormatter(mTheory, this);
		if (!mSorts.isEmpty())
			mf.appendComment("Sort interpretations");
		for (Map.Entry<Sort, SortInterpretation> me : mSorts.entrySet())
			mf.appendSortInterpretation(me.getValue(), me.getKey());
		// Only if we printed ";; Sort interpretations" we should print the
		// delimiting comment ";; Function interpretations"
		if (!mSorts.isEmpty())
			mf.appendComment("Function interpretations");
		for (Map.Entry<FunctionSymbol, FunctionValue> me : mFuncVals.entrySet())
			if (!me.getKey().isIntern())
				mf.appendValue(me.getKey(), me.getValue(), mTheory);
		return mf.finish();
	}
	
	Theory getTheory() {
		return mTheory;
	}

	public boolean isPartialModel() {
		return mPartialModel;
	}

	public BoolSortInterpretation getBoolSortInterpretation() {
		return mBoolSort;
	}
	
	public NumericSortInterpretation getNumericSortInterpretation() {
		return mNumSorts;
	}

	public SortInterpretation provideSortInterpretation(Sort sort) {
		if (sort.isNumericSort())
			return mNumSorts;
		if (sort == mTheory.getBooleanSort())
			return mBoolSort;
		
		if (sort.isArraySort()) {
			ArraySortInterpretation array = mArraySorts.get(sort);
			if (array == null) {
				array = new ArraySortInterpretation(
						provideSortInterpretation(sort.getArguments()[0]),
						provideSortInterpretation(sort.getArguments()[1]));
				mArraySorts.put(sort, array);
			}
			return array;
		}
		SortInterpretation res = mSorts.get(sort);
		if (res == null) {
			res = new FiniteSortInterpretation();
			mSorts.put(sort, res);
		}
		return res;
	}

	public FunctionValue getFunctionValue(FunctionSymbol fs) {
		return mFuncVals.get(fs);
	}
	
	public Term toModelTerm(int idx, Sort resultSort) {
		if (idx == -1)
			return getUndefined(resultSort);
		if (resultSort == mTheory.getBooleanSort())
			return mBoolSort.get(idx, resultSort, mTheory);
		if (resultSort.isNumericSort()) {
			Rational val = mNumSorts.get(idx);
			return val.toTerm(resultSort);
		}
		if (resultSort.isArraySort()) {
			ArraySortInterpretation array = mArraySorts.get(resultSort);
			if (array == null) {
				if (mPartialModel)
					return getUndefined(resultSort);
				array = new ArraySortInterpretation(
						provideSortInterpretation(resultSort.getArguments()[0]),
						provideSortInterpretation(resultSort.getArguments()[1]));
				mArraySorts.put(resultSort, array);
			}
			return array.get(idx, resultSort, mTheory);
		}
		SortInterpretation si = mSorts.get(resultSort);
		if (si == null) {
			if (mPartialModel)
				return getUndefined(resultSort);
			si = new FiniteSortInterpretation();
			si.ensureCapacity(idx + 1);
		}
		return si.get(idx, resultSort, mTheory);
	}

	public ArraySortInterpretation getArrayInterpretation(Sort arraySort) {
		// FIXME might not exist
		return mArraySorts.get(arraySort);
	}

}
