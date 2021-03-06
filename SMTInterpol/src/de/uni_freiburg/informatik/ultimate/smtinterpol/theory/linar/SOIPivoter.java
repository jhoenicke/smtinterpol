package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.linar;

import java.math.BigInteger;
import java.util.Map.Entry;
import java.util.SortedMap;
import java.util.SortedSet;
import java.util.TreeMap;
import java.util.TreeSet;

import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Clause;

/**
 * The sum of infeasibility pivoter. This implements the pivoting strategy of [KBD2013]. The core idea is to optimize
 * all out of bounds variables at the same time by minimizing the sum of the error for each bound. The error of a bound
 * is the amount that an out of bound variable is currently larger resp. smaller than its bound. The algorithm ensures
 * that each pivoting step will not increase the sum of errors. We only consider bounds that were set as external
 * literals, not derived composites bounds, for two reasons: (1) the derived bounds will be upheld automatically, and
 * (2) pivoting may create new derived composites bound which messes up the global optimization goal.
 *
 * <p>
 * We have to be very precise with the epsilons and even consider a variable out of bounds if it has a strict bound and
 * the epsilon value is not large enough. Otherwise we again mess up the global optimization goal. When we reach a
 * plateau we follow a Bland like strategy as outlined in the paper.
 *
 * <p>
 * The core of this pivoter is fixOobs(), which runs until an error is found, or a rational solution is achieved.
 *
 * <dl>
 * <dt>[KBD2013]</dt>
 * <dd>T. King, C. Barret, B. Dutertre: Simplex with sum of infeasibilities for SMT. FMCAD 2013</dd>
 * </dl>
 *
 * @author hoenicke
 *
 */
public class SOIPivoter {

	LinArSolve mSolver;
	/** The current coefficients for the sum of out of bounds variables expressed using the current column variables. */
	SortedMap<LinVar, Rational> mSOIVar;
	/** The current value for the sum of infeasibility */
	ExactInfinitesimalNumber mSOIValue;
	/** The limiter describing the next pivot step. */
	FreedomLimiter mBestLimiter;

	public SOIPivoter(final LinArSolve solver) {
		mSolver = solver;
	}

	/**
	 * Compute the virtual Sum Of Infeasibility variable and its value.
	 *
	 * @return true if there is a variable that is out of bound.
	 */
	public boolean computeSOI() {
		boolean isOOB = false;
		mSOIValue = ExactInfinitesimalNumber.ZERO;
		mSOIVar = new TreeMap<>();
		for (final LinVar var : mSolver.mLinvars) {
			boolean isUpper;
			ExactInfinitesimalNumber diff = var.getValue().isub(var.getLowerBound());
			if (diff.signum() > 0) {
				isUpper = false;
				mSOIValue = mSOIValue.add(diff);
			} else {
				diff = var.getValue().isub(var.getUpperBound());
				if (diff.signum() < 0) {
					isUpper = true;
					mSOIValue = mSOIValue.sub(diff);
				} else {
					continue;
				}
			}

			isOOB = true;
			// now we have found an out of bound variable.
			// isUpper is true if we violate the upper bound.
			// mSoiValue is already updated.
			// Next step: Update soiVar by adding the row of coefficients.

			BigInteger divisor = var.mHeadEntry.mCoeff;
			if (isUpper) {
				divisor = divisor.negate();
			}
			for (MatrixEntry entry = var.mHeadEntry.mNextInRow; entry != var.mHeadEntry; entry = entry.mNextInRow) {
				Rational coeff = Rational.valueOf(entry.mCoeff, divisor);
				final Rational oldValue = mSOIVar.get(entry.mColumn);
				if (oldValue != null) {
					coeff = coeff.add(oldValue);
				}
				mSOIVar.put(entry.mColumn, coeff);
			}
		}
		return isOOB;
	}

	/**
	 * Check if SOI cannot be strictly decreased by any pivot step.
	 * As a side effect it also updates mBestLimiter to be the one used for Bland pivoting strategy.
	 * @return true if SOI cannot be decreased.
	 */
	public boolean checkZeroFreedom() {
		boolean firstColumn = true;
		mBestLimiter = null;
		for (final Entry<LinVar, Rational> entry : mSOIVar.entrySet()) {
			final LinVar colVar = entry.getKey();
			Rational coeff = entry.getValue();
			if (coeff.signum() == 0) {
				continue;
			}
			// for negative coeff: check if we cannot increase var to lower the soi.
			// otherwise check if we cannot decrease var to lower the SOI.  In both cases the variable can be skipped.
			if (colVar.getValue().equals(coeff.signum() < 0 ? colVar.getUpperBound() : colVar.getLowerBound())) {
				continue;
			}

			for (MatrixEntry me = colVar.mHeadEntry.mNextInCol; true; me = me.mNextInCol) {
				if (me == colVar.mHeadEntry) {
					/* we got round and weight did not toggle: we can pivot */
					mBestLimiter = null;
					return false;
				}
				final LinVar rowVar = me.mRow;
				final Rational weight = Rational.valueOf(me.mCoeff, rowVar.mHeadEntry.mCoeff.negate());
				final LAReason bound = weight.signum() == coeff.signum() ? rowVar.mLowerLiteral : rowVar.mUpperLiteral;
				if (bound != null && rowVar.getValue().equals(new ExactInfinitesimalNumber(bound.getBound()))) {
					// check if this entry would be used by Bland strategy (first column, smallest row variable)
					if (firstColumn &&
							(mBestLimiter == null || mBestLimiter.getRowVar().compareTo(rowVar) > 0)) {
						mBestLimiter = new FreedomLimiter(ExactInfinitesimalNumber.ZERO, weight, bound.getBound(), me);
					}

					// make weight the opposite sign of coeff and add it, to decrease absolute value of coeff.
					if (weight.signum() == coeff.signum()) {
						weight.negate();
					}
					coeff = coeff.add(weight);
					/* if adding the weight changed the sign, this column has zero freedom. Break the loop. */
					if (coeff.signum() != -weight.signum()) {
						break;
					}
				}
			}
			assert mBestLimiter != null;
			firstColumn = false;
		}
		assert firstColumn || mBestLimiter != null;
		// we got through all columns -> freedom cannot be decreased.
		return true;
	}

	public MatrixEntry findPivot() {
		ExactInfinitesimalNumber bestDiff = new ExactInfinitesimalNumber(Rational.MONE);
		LinVar bestVar = null;
		mBestLimiter = null;
		for (final Entry<LinVar, Rational> entry : mSOIVar.entrySet()) {
			final LinVar colVar = entry.getKey();
			final Rational coeff = entry.getValue();
			if (coeff.signum() == 0) {
				continue;
			}
			// for negative coeff: check if we cannot increase var to lower the soi.
			// otherwise check if we cannot decrease var to lower the SOI.  In both cases the variable can be skipped.
			if (colVar.getValue().equals(coeff.signum() < 0 ? colVar.getUpperBound() : colVar.getLowerBound())) {
				continue;
			}

			// mSolver.mEngine.getLogger().debug("Column %2$s * %1$s", colVar, coeff);

			// Variable may be feasible to lower the soi.  Check how much we can lower the soi by changing this variable.
			// For this collect all bounds on all variables and sort them by the time until they are hit.
			final SortedSet<FreedomLimiter> bounds = new TreeSet<>();
			{
				final InfinitesimalNumber colBound = coeff.signum() > 0 ? colVar.getLowerBound() : colVar.getUpperBound();
				if (!colBound.isInfinity()) {
					final ExactInfinitesimalNumber colFreedom = colVar.getValue().isub(colBound).abs();
					bounds.add(new FreedomLimiter(colFreedom, Rational.ONE, colBound,
							colVar.mHeadEntry));
				}
			}
			for (MatrixEntry me = colVar.mHeadEntry.mNextInCol; me != colVar.mHeadEntry; me = me.mNextInCol) {
				final LinVar rowVar = me.mRow;
				Rational weight = Rational.valueOf(me.mCoeff, rowVar.mHeadEntry.mCoeff);
				if (coeff.signum() < 0) {
					weight = weight.negate();
				}
				if (rowVar.mLowerLiteral != null) {
					final InfinitesimalNumber bound = rowVar.mLowerLiteral.getBound();
					final ExactInfinitesimalNumber diff = rowVar.getValue().isub(bound);
					// a difference of zero counts as negative, because it means the rowVar is in bound.
					if (weight.signum() * (2 * diff.signum() - 1) > 0) {
						final ExactInfinitesimalNumber freedom = diff.div(weight);
						assert freedom.signum() >= 0;
						final FreedomLimiter limiter = new FreedomLimiter(freedom, weight, bound, me);
						bounds.add(limiter);
					}
				}
				if (rowVar.mUpperLiteral != null) {
					final InfinitesimalNumber bound = rowVar.mUpperLiteral.getBound();
					final ExactInfinitesimalNumber diff = rowVar.getValue().isub(bound);
					// a difference of zero counts as positive, because it means the rowVar is in bound.
					if (weight.signum() * (2 * diff.signum() + 1) > 0) {
						final ExactInfinitesimalNumber freedom = diff.div(weight);
						assert freedom.signum() >= 0;
						final FreedomLimiter limiter = new FreedomLimiter(freedom, weight, bound, me);
						bounds.add(limiter);
					}
				}
			}
			// mSolver.mEngine.getLogger().debug(bounds);
			Rational weight = coeff.abs();
			ExactInfinitesimalNumber lastFreedom = new ExactInfinitesimalNumber(Rational.ZERO);
			ExactInfinitesimalNumber soidiff = new ExactInfinitesimalNumber(Rational.ZERO);
			// mSolver.mEngine.getLogger().debug("Candidates: %s + %s", colVar, bounds);
			for (final FreedomLimiter limiter : bounds) {
				soidiff = soidiff.add(limiter.mFreedom.sub(lastFreedom).mul(weight));
				lastFreedom = limiter.mFreedom;
				weight = weight.sub(limiter.getWeight().abs());
				if (weight.signum() <= 0) {
					// with this variable we reach pivoting point.
					// mSolver.mEngine.getLogger().debug("Candidate: %s", limiter);
					// mSolver.mEngine.getLogger().debug("soi diff: %s", soidiff);
					if (bestDiff.compareTo(soidiff) < 0) {
						bestDiff = soidiff;
						bestVar = colVar;
						mBestLimiter = limiter;
						if (limiter.mFreedom.signum() == 0) {
							mBestLimiter = bounds.first();
						}
						if (bestDiff.equals(mSOIValue)) {
							mSolver.mEngine.getLogger().debug("Solved it!", bestDiff);
							return limiter.getMatrixEntry();
						}
					}
					break;
				}
			}
			assert (weight.signum() <= 0);
		}
		mSolver.mEngine.getLogger().debug("Best Candidate: (%s)", bestDiff);
		if (bestVar != null) {
			return mBestLimiter.getMatrixEntry();
		}
		return null;
	}

	public Clause computeConflict() {
		final Explainer explainer = new Explainer(mSolver, mSolver.mEngine.isProofGenerationEnabled(), null);
		for (final LinVar var : mSolver.mLinvars) {
			if (var.getValue().isub(var.getLowerBound()).signum() > 0) {
				var.mLowerLiteral.explain(explainer, InfinitesimalNumber.ZERO, Rational.MONE);
			} else if (var.getValue().isub(var.getUpperBound()).signum() < 0) {
				var.mUpperLiteral.explain(explainer, InfinitesimalNumber.ZERO, Rational.ONE);
			}
		}
		for (final Entry<LinVar, Rational> entry : mSOIVar.entrySet()) {
			final LinVar colVar = entry.getKey();
			final Rational coeff = entry.getValue();
			if (coeff.signum() == 0) {
				continue;
			}
			final LiteralReason reason = coeff.signum() < 0 ? colVar.mUpperLiteral : colVar.mLowerLiteral;
			reason.explain(explainer, InfinitesimalNumber.ZERO, coeff.negate());
		}
		return explainer.createClause(mSolver.mEngine);
	}

	public Clause fixOobs() {
		mSolver.mEngine.getLogger().debug("=== fixoobs ===");
		while (true) {
			if (!computeSOI()) {
				return null;
			}
			if (mSolver.mEngine.getLogger().isDebugEnabled()) {
				mSolver.mEngine.getLogger().debug("SOI: %s.%04d", mSOIValue.getRealValue().floor(),
						mSOIValue.getRealValue().frac().mul(BigInteger.valueOf(10000)).floor().numerator().intValue());
			}
			MatrixEntry candidate = findPivot();
			if (candidate == null) {
				return computeConflict();
			}
			// inner loop if we didn't make progress
			int blandPivotStep = 0;
			while (mBestLimiter.mFreedom.signum() == 0) {
				mSolver.pivot(mBestLimiter.getMatrixEntry());
				mSolver.mNumPivotsBland++;
				blandPivotStep++;
				final Clause conflict = mSolver.checkPendingBoundPropagations();
				if (conflict != null) {
					mSolver.mEngine.getLogger().debug("Conflict on pivoting after %d Bland pivot steps",
							blandPivotStep);
					return conflict;
				}
				computeSOI();
				if (checkZeroFreedom()) {
					if (mBestLimiter == null) {
						mSolver.mEngine.getLogger().debug("Conflict after %d Bland pivot steps", blandPivotStep);
						return computeConflict();
					}
				} else {
					mSolver.mEngine.getLogger().debug("Finished %d Bland pivot steps", blandPivotStep);
					candidate = findPivot();
					assert mBestLimiter.mFreedom.signum() > 0;
				}
			}

			LinVar row;
			if (candidate.mNextInRow != null) {
				row = candidate.mRow;
				mSolver.pivot(candidate);
			} else {
				row = candidate.mColumn;
			}
			mSolver.updateVariableValue(row, new ExactInfinitesimalNumber(mBestLimiter.mBound));
			final Clause conflict = mSolver.checkPendingBoundPropagations();
			if (conflict != null) {
				return conflict;
			}
		}
	}

	private static class FreedomLimiter implements Comparable<FreedomLimiter> {
		ExactInfinitesimalNumber mFreedom;
		Rational mWeight;
		InfinitesimalNumber mBound;
		MatrixEntry mEntry;

		public FreedomLimiter(final ExactInfinitesimalNumber freedom, final Rational weight, final InfinitesimalNumber bound,
				final MatrixEntry entry) {
			assert freedom.signum() >= 0;
			mFreedom = freedom;
			mWeight = weight;
			mBound = bound;
			mEntry = entry;
		}

		@Override
		public int compareTo(final FreedomLimiter other) {
			final int freedomCmp = mFreedom.compareTo(other.mFreedom);
			if (freedomCmp != 0) {
				return freedomCmp;
			}
			return mEntry.mRow.compareTo(other.mEntry.mRow);
		}

		public Rational getWeight() {
			return mWeight;
		}

		public MatrixEntry getMatrixEntry() {
			return mEntry;
		}

		public LinVar getRowVar() {
			return mEntry.mRow;
		}

		@Override
		public String toString() {
			return "Freedom[" + mFreedom + ",(" + mEntry.mRow + ")," + mWeight + "]";
		}
	}
}
