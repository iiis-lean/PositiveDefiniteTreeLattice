[← Public API](../PUBLIC_API.md) · [Public boundaries](../PUBLIC_BOUNDARIES.md) · [Complete graph](../DECLARATION_GRAPH.md)

# `unitIntervalCompensationNonneg`

A distance lower bound compensates the negative quadratic inside a unit interval.

- Kind: `theorem`
- Node: `Main.RootedEstimates`
- Module: `PositiveDefiniteTreeLattice.Main.RootedEstimates.Theorems.unitIntervalCompensationNonneg`
- State: `proved`
- Revision status: `committed`
- Repository completion: `graph_proved`
- Compatibility `formal_code`: final proof projection

## Statement NL

Let `gamma`, `tau`, and `D` be rational numbers and let `k` be an integer. Assume `0 < gamma < 1`, `(k : ℚ) < tau`, `tau < (k : ℚ) + 1`, and

`D ≥ min (tau - (k : ℚ)) ((k : ℚ) + 1 - tau)`.

Then

`0 ≤ gamma * (tau - (k : ℚ)) * (tau - (k : ℚ) - 1) + D`.

## Statement Formal

```lean
-- lean-constellation: managed-imports-begin
import PositiveDefiniteTreeLattice.Main.RootedEstimates.Prelude
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `unitIntervalCompensationNonneg`

Let `gamma`, `tau`, and `D` be rational numbers and let `k` be an integer. Assume `0 < gamma < 1`,
`(k : ℚ) < tau`, `tau < (k : ℚ) + 1`, and

`D ≥ min (tau - (k : ℚ)) ((k : ℚ) + 1 - tau)`.

Then

`0 ≤ gamma * (tau - (k : ℚ)) * (tau - (k : ℚ) - 1) + D`.

## Sources

- Source `solution.tex`, lines 129–152
-/
theorem unitIntervalCompensationNonneg (gamma tau D : ℚ) (k : ℤ)
    (hgamma_pos : 0 < gamma) (hgamma_lt_one : gamma < 1)
    (hk_lt_tau : (k : ℚ) < tau) (htau_lt_k_one : tau < (k : ℚ) + 1)
    (hD : D ≥ min (tau - (k : ℚ)) ((k : ℚ) + 1 - tau)) :
    0 ≤ gamma * (tau - (k : ℚ)) * (tau - (k : ℚ) - 1) + D := by
  sorry
```

## Proof NL

Use the closing estimate from solution.tex, lines 129–152. Set `α = tau - (k : ℚ)` and `β = (k : ℚ) + 1 - tau`; the strict interval hypotheses give `0 < α`, `0 < β`, and `α + β = 1`. Rewrite the quadratic term as `-gamma * α * β`. It is enough, by the hypothesis on `D`, to prove `gamma * α * β ≤ min α β`. Split on `α ≤ β`: rewrite the minimum with `min_eq_left`, then use `β ≤ 1` and `gamma < 1` together with positivity to show `gamma * α * β ≤ α`. In the opposite branch, rewrite with `min_eq_right` and symmetrically use `α ≤ 1` to show `gamma * α * β ≤ β`. Finish by transitivity with `hD` and ordered-ring normalization. No project declaration is used.

## Proof Formal

```lean
-- lean-constellation: managed-imports-begin
import PositiveDefiniteTreeLattice.Main.RootedEstimates.Prelude
import Mathlib.Order.Defs.LinearOrder
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `unitIntervalCompensationNonneg`

Let `gamma`, `tau`, and `D` be rational numbers and let `k` be an integer. Assume `0 < gamma < 1`,
`(k : ℚ) < tau`, `tau < (k : ℚ) + 1`, and

`D ≥ min (tau - (k : ℚ)) ((k : ℚ) + 1 - tau)`.

Then

`0 ≤ gamma * (tau - (k : ℚ)) * (tau - (k : ℚ) - 1) + D`.

## Sources

- Source `solution.tex`, lines 129–152

## Proof outline

Use the closing estimate from solution.tex, lines 129–152. Set `α = tau - (k : ℚ)` and `β = (k : ℚ)
+ 1 - tau`; the strict interval hypotheses give `0 < α`, `0 < β`, and `α + β = 1`. Rewrite the
quadratic term as `-gamma * α * β`. It is enough, by the hypothesis on `D`, to prove `gamma * α * β
≤ min α β`. Split on `α ≤ β`: rewrite the minimum with `min_eq_left`, then use `β ≤ 1` and `gamma <
1` together with positivity to show `gamma * α * β ≤ α`. In the opposite branch, rewrite with
`min_eq_right` and symmetrically use `α ≤ 1` to show `gamma * α * β ≤ β`. Finish by transitivity
with `hD` and ordered-ring normalization. No project declaration is used.

## Proof sources

- Source `solution.tex`, lines 129–152

## Proof dependencies

- `min_eq_left` from `Mathlib.Order.Defs.LinearOrder`
- `min_eq_right` from `Mathlib.Order.Defs.LinearOrder`
-/
theorem unitIntervalCompensationNonneg (gamma tau D : ℚ) (k : ℤ)
    (hgamma_pos : 0 < gamma) (hgamma_lt_one : gamma < 1)
    (hk_lt_tau : (k : ℚ) < tau) (htau_lt_k_one : tau < (k : ℚ) + 1)
    (hD : D ≥ min (tau - (k : ℚ)) ((k : ℚ) + 1 - tau)) :
    0 ≤ gamma * (tau - (k : ℚ)) * (tau - (k : ℚ) - 1) + D := by
  let x : ℚ := tau - (k : ℚ)
  let y : ℚ := (k : ℚ) + 1 - tau
  have hx : 0 ≤ x := by
    dsimp [x]
    linarith
  have hy : 0 ≤ y := by
    dsimp [y]
    linarith
  have hsum : x + y = 1 := by
    dsimp [x, y]
    ring
  have hgamma : gamma ≤ 1 := le_of_lt hgamma_lt_one
  have hgamma_nonneg : 0 ≤ gamma := le_of_lt hgamma_pos
  have hproduct_nonneg : 0 ≤ gamma * x * y :=
    mul_nonneg (mul_nonneg hgamma_nonneg hx) hy
  have hbound : gamma * x * y ≤ min x y := by
    by_cases hxy : x ≤ y
    · rw [min_eq_left hxy]
      have hy_one : y ≤ 1 := by linarith
      have hgy : gamma * y ≤ 1 := by
        calc
          gamma * y ≤ 1 * y := mul_le_mul_of_nonneg_right hgamma hy
          _ ≤ 1 := by simpa using hy_one
      calc
        gamma * x * y = x * (gamma * y) := by ring
        _ ≤ x * 1 := mul_le_mul_of_nonneg_left hgy hx
        _ = x := by ring
    · have hyx : y ≤ x := le_of_not_ge hxy
      rw [min_eq_right hyx]
      have hx_one : x ≤ 1 := by linarith
      have hgx : gamma * x ≤ 1 := by
        calc
          gamma * x ≤ 1 * x := mul_le_mul_of_nonneg_right hgamma hx
          _ ≤ 1 := by simpa using hx_one
      calc
        gamma * x * y = y * (gamma * x) := by ring
        _ ≤ y * 1 := mul_le_mul_of_nonneg_left hgx hy
        _ = y := by ring
  have hD' : D ≥ min x y := by simpa [x, y] using hD
  have hquadratic :
      gamma * (tau - (k : ℚ)) * (tau - (k : ℚ) - 1) = -gamma * x * y := by
    dsimp [x, y]
    ring
  nlinarith [hproduct_nonneg]
```

## Proof dependencies

- `Mathlib:Mathlib.Order.Defs.LinearOrder.min_eq_left`
- `Mathlib:Mathlib.Order.Defs.LinearOrder.min_eq_right`

## Sources

- `solution.tex:129-152`
