-- lean-constellation: managed-imports-begin
import PositiveDefiniteTreeLattice.Main.RootedEstimates.Prelude
import Mathlib.Algebra.Order.Group.Unbundled.Abs
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `rationalUnitIntervalIntegerDistance`

Let `k` and `N` be integers and let `tau` be a rational number. Assume

`(k : ℚ) < tau` and `tau < (k : ℚ) + 1`.

Then the distance from `tau` to the arbitrary integer `N` bounds both endpoint distances below:

`min (tau - (k : ℚ)) ((k : ℚ) + 1 - tau) ≤ |tau - (N : ℚ)|`.

## Sources

- Source `solution.tex`, lines 129–148

## Proof outline

Put `m := min (tau - (k : ℚ)) ((k : ℚ) + 1 - tau)`. The strict hypotheses place `tau` between the
consecutive integers `k` and `k + 1`. Integer discreteness, discharged by `omega` together with cast
normalization, gives the exhaustive split `N ≤ k` or `k + 1 ≤ N`.

If `N ≤ k`, then `tau - (N : ℚ) ≥ tau - (k : ℚ) > 0`. Rewrite the absolute value with
`abs_of_nonneg`; the defining lower bound for `min` gives `m ≤ tau - (k : ℚ) ≤ |tau - (N : ℚ)|`. If
`k + 1 ≤ N`, then `(N : ℚ) - tau ≥ (k : ℚ) + 1 - tau > 0`. Rewrite the absolute value with
`abs_of_nonpos` and obtain `m ≤ (k : ℚ) + 1 - tau ≤ |tau - (N : ℚ)|`. The remaining cast and
linear-order rearrangements are lightweight ordered-field calculations. This is the
distance-to-integers endpoint argument in b_0010 lines 129–148.

## Proof sources

- Source `solution.tex`, lines 129–148

## Proof dependencies

- `abs_of_nonneg` from `Mathlib.Algebra.Order.Group.Unbundled.Abs`
- `abs_of_nonpos` from `Mathlib.Algebra.Order.Group.Unbundled.Abs`
-/
theorem rationalUnitIntervalIntegerDistance (k N : ℤ) (tau : ℚ)
    (hk_lt_tau : (k : ℚ) < tau) (htau_lt_k_one : tau < (k : ℚ) + 1) :
    min (tau - (k : ℚ)) ((k : ℚ) + 1 - tau) ≤ |tau - (N : ℚ)| := by
  by_cases hNk : N ≤ k
  · have hNkQ : (N : ℚ) ≤ (k : ℚ) := by
      exact_mod_cast hNk
    rw [abs_of_nonneg]
    · exact le_trans (min_le_left _ _) (by linarith)
    · linarith
  · have hkN : k + 1 ≤ N := by omega
    have hkNQ : (k : ℚ) + 1 ≤ (N : ℚ) := by
      exact_mod_cast hkN
    rw [abs_of_nonpos]
    · exact le_trans (min_le_right _ _) (by linarith)
    · linarith
