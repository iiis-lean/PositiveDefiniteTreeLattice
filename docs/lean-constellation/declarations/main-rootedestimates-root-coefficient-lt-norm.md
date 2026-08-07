[← Public API](../PUBLIC_API.md) · [Public boundaries](../PUBLIC_BOUNDARIES.md)

# `root_coefficient_lt_norm`

A nonzero vector in an admissible rooted tree has root coefficient strictly below its treePairing norm.

- Kind: `theorem`
- Node: `Main.RootedEstimates`
- Module: `PositiveDefiniteTreeLattice.Main.RootedEstimates.Theorems.root_coefficient_lt_norm`
- State: `proved`
- Revision status: `committed`
- Repository completion: `graph_proved`
- Formal code: final proof projection

## Lean code

```lean
-- lean-constellation: managed-imports-begin
import PositiveDefiniteTreeLattice.Main.RootedEstimates.Prelude
import Mathlib.Algebra.Order.Ring.Cast
import Mathlib.LinearAlgebra.Matrix.PosDef
import PositiveDefiniteTreeLattice.Main.RootedEstimates.Theorems.rootCoordinateSqLeCapacityMulTreePairing
import PositiveDefiniteTreeLattice.Main.RootedEstimates.Theorems.treePairingCastEqRootedGramQuadratic
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `root_coefficient_lt_norm`

For a finite graph `G` with the existing decidability instances, an integer weight function `w`, a
root `rho`, and an admissibility hypothesis `hAdm : IsAdmissibleRootedTree G w rho`, let `x : V → ℤ`
be an integral coordinate vector with `hx : x ≠ 0`.  The exact public theorem
`PositiveDefiniteTreeLattice.root_coefficient_lt_norm` asserts the strict integer inequality

`x rho < PositiveDefiniteTreeLattice.treePairing G w x x`.

Equivalently, the integral tree-pairing norm satisfies `0 < PositiveDefiniteTreeLattice.treePairing
G w x x - x rho`.  The statement retains the exact root coordinate, integral pairing model,
admissibility hypothesis, and nonzero-vector hypothesis from the source.

## Sources

- Source `solution.tex`, lines 155–159

## Statement dependencies

- `Main.LatticeFoundations::treePairingAnchor` → `PositiveDefiniteTreeLattice.treePairing` from
  `PositiveDefiniteTreeLattice.Main.LatticeFoundations.Defs.treePairingAnchor`
- `Main.RootedCapacity::IsAdmissibleRootedTree` → `IsAdmissibleRootedTree` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.IsAdmissibleRootedTree`

## Proof outline

Write `N := PositiveDefiniteTreeLattice.treePairing G w x x` and `xQ : V → ℚ := fun v => (x v : ℚ)`.
Destructure `hAdm` to obtain `hPos : Matrix.PosDef (rootedGram G w)`.  The coordinatewise cast
vector is nonzero: otherwise function extensionality and injectivity of the integer cast would
contradict `hx`.  Hence `hPos.dotProduct_mulVec_pos hxQ` gives strict positivity of the rational
rootedGram quadratic form.  Rewrite it through the proved `treePairingCastEqRootedGramQuadratic G w
x`, and use cast/order normalization to obtain `0 < N` in `ℤ`.

Split on `x rho ≤ 0`, exactly as in the source.  In this case, combine `0 < N` with `x rho ≤ 0` by
integer linear arithmetic to conclude `x rho < N`.

In the remaining case obtain `0 < x rho`.  Let `gamma := rootedCapacity G w rho`.  The proved Cauchy
bridge `rootCoordinateSqLeCapacityMulTreePairing G w rho hAdm x` gives
`(x rho : ℚ)^2 ≤ gamma * (N : ℚ)`.
From `PositiveDefiniteTreeLattice.capacity_pos_lt_one G w rho hAdm`, use `gamma < 1` and the
already-established `(N : ℚ) > 0` to get the strict bound
`(x rho : ℚ)^2 < (N : ℚ)`.
Since `x rho` is a positive integer, ordered-ring arithmetic gives `x rho ≤ (x rho)^2`; cast this
inequality to `ℚ`, compose it with the strict rational bound, and transport the resulting strict
inequality back to `ℤ`.  This proves the exact public conclusion `x rho < treePairing G w x x`, with
no nonzero condition beyond the original `hx` and no change of graph, root, or pairing model.  It is
the source argument in solution.tex lines 155–180.

## Proof sources

- Source `solution.tex`, lines 155–180

## Proof dependencies

- `Int.cast_le` from `Mathlib.Algebra.Order.Ring.Cast`
- `Int.cast_lt` from `Mathlib.Algebra.Order.Ring.Cast`
- `Matrix.PosDef.dotProduct_mulVec_pos` from `Mathlib.LinearAlgebra.Matrix.PosDef`
- `Main.RootedCapacity::IsAdmissibleRootedTree` → `IsAdmissibleRootedTree` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.IsAdmissibleRootedTree`
- `Main.RootedCapacity::capacity_pos_lt_one` → `PositiveDefiniteTreeLattice.capacity_pos_lt_one`
  from `PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.capacity_pos_lt_one`
- `Main.RootedCapacity::rootedGram` → `rootedGram` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedGram`
- `Main.RootedEstimates::rootCoordinateSqLeCapacityMulTreePairing` →
  `rootCoordinateSqLeCapacityMulTreePairing` from `PositiveDefiniteTreeLattice.Main.RootedEstimates.
  Theorems.rootCoordinateSqLeCapacityMulTreePairing`
- `Main.RootedEstimates::treePairingCastEqRootedGramQuadratic` →
  `treePairingCastEqRootedGramQuadratic` from
  `PositiveDefiniteTreeLattice.Main.RootedEstimates.Theorems.treePairingCastEqRootedGramQuadratic`
-/
theorem PositiveDefiniteTreeLattice.root_coefficient_lt_norm {V : Type*} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (w : V → ℤ) (rho : V)
    (hAdm : IsAdmissibleRootedTree G w rho) (x : V → ℤ) (hx : x ≠ 0) :
    x rho < treePairing G w x x := by
  classical
  have hCauchy := rootCoordinateSqLeCapacityMulTreePairing G w rho hAdm x
  have hcap := capacity_pos_lt_one G w rho hAdm
  rcases hAdm with ⟨hG, hPos, hw, hchildren⟩
  let xQ : V → ℚ := fun v => (x v : ℚ)
  have hxQ : xQ ≠ 0 := by
    intro hxQ
    apply hx
    funext v
    have hv : (x v : ℚ) = 0 := by
      simpa [xQ] using congrFun hxQ v
    exact_mod_cast hv
  have hquad : 0 < xQ ⬝ᵥ Matrix.mulVec (rootedGram G w) xQ := by
    simpa using hPos.dotProduct_mulVec_pos hxQ
  have hNQ : 0 < (↑(treePairing G w x x) : ℚ) := by
    rw [treePairingCastEqRootedGramQuadratic]
    simpa [xQ] using hquad
  have hN : 0 < treePairing G w x x := by
    exact_mod_cast hNQ
  by_cases hroot : x rho ≤ 0
  · omega
  · have hroot_pos : 0 < x rho := lt_of_not_ge hroot
    have hgamma_lt : rootedCapacity G w rho < 1 := hcap.2
    have hgamma_mul_lt : rootedCapacity G w rho *
        (↑(treePairing G w x x) : ℚ) < (↑(treePairing G w x x) : ℚ) := by
      nlinarith
    have hsq_lt : (x rho : ℚ) ^ 2 < (↑(treePairing G w x x) : ℚ) :=
      lt_of_le_of_lt hCauchy hgamma_mul_lt
    have hroot_sq : x rho ≤ (x rho) ^ 2 := by
      nlinarith
    have hroot_sqQ : (x rho : ℚ) ≤ (x rho : ℚ) ^ 2 := by
      exact_mod_cast hroot_sq
    have hroot_ltQ : (x rho : ℚ) < (↑(treePairing G w x x) : ℚ) :=
      lt_of_le_of_lt hroot_sqQ hsq_lt
    exact_mod_cast hroot_ltQ
```

## Statement dependencies

- `current repo:Main.LatticeFoundations.treePairingAnchor`
- `current repo:Main.RootedCapacity.IsAdmissibleRootedTree`

## Proof dependencies

- `Mathlib:Mathlib.Algebra.Order.Ring.Cast.Int.cast_le`
- `Mathlib:Mathlib.Algebra.Order.Ring.Cast.Int.cast_lt`
- `Mathlib:Mathlib.LinearAlgebra.Matrix.PosDef.Matrix.PosDef.dotProduct_mulVec_pos`
- `current repo:Main.RootedCapacity.IsAdmissibleRootedTree`
- `current repo:Main.RootedCapacity.capacity_pos_lt_one`
- `current repo:Main.RootedCapacity.rootedGram`
- `current repo:Main.RootedEstimates.rootCoordinateSqLeCapacityMulTreePairing`
- `current repo:Main.RootedEstimates.treePairingCastEqRootedGramQuadratic`

## Sources

- `solution.tex:155-159`
