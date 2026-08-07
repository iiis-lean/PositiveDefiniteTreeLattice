-- lean-constellation: managed-imports-begin
import PositiveDefiniteTreeLattice.Main.LatticeFoundations.Prelude
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import PositiveDefiniteTreeLattice.Main.LatticeFoundations.Defs.treePairingAnchor
import PositiveDefiniteTreeLattice.Main.LatticeFoundations.Defs.vertexVectorAnchor
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `treePairing_vertexVector_self`

For a finite type `V` with decidable equality, a simple graph `G : SimpleGraph V` with decidable
adjacency, an integer-valued weight function `weight : V → ℤ`, and a vertex `v : V`, the
self-pairing of the unit coordinate function is its vertex weight:

`treePairing G weight (vertexVector v) (vertexVector v) = weight v`.

## Sources

- Source `formal_target.lean`, lines 7–15
- Source `problem.tex`, lines 13–23

## Statement dependencies

- `Main.LatticeFoundations::treePairingAnchor` → `PositiveDefiniteTreeLattice.treePairing` from
  `PositiveDefiniteTreeLattice.Main.LatticeFoundations.Defs.treePairingAnchor`
- `Main.LatticeFoundations::vertexVectorAnchor` → `PositiveDefiniteTreeLattice.vertexVector` from
  `PositiveDefiniteTreeLattice.Main.LatticeFoundations.Defs.vertexVectorAnchor`

## Proof outline

Unfold `PositiveDefiniteTreeLattice.treePairing` and `PositiveDefiniteTreeLattice.vertexVector`.
Evaluate the outer finite sum: every term away from `v` vanishes because the unit coordinate is zero
there, while the term at `v` has first factor `1`.  In its neighbor sum, every unit-coordinate value
is zero: the only possible nonzero index would be `v`, but `SimpleGraph.notMem_neighborFinset_self`
rules out a loop at `v`.  Simplifying these finite sums and the remaining integer arithmetic leaves
`weight v`.

## Proof dependencies

- `Finset.sum_eq_single` from `Mathlib.Algebra.BigOperators.Group.Finset.Basic`
- `Finset.sum_eq_zero` from `Mathlib.Algebra.BigOperators.Group.Finset.Basic`
- `SimpleGraph.notMem_neighborFinset_self` from `Mathlib.Combinatorics.SimpleGraph.Finite`
- `Main.LatticeFoundations::treePairingAnchor` → `PositiveDefiniteTreeLattice.treePairing` from
  `PositiveDefiniteTreeLattice.Main.LatticeFoundations.Defs.treePairingAnchor`
- `Main.LatticeFoundations::vertexVectorAnchor` → `PositiveDefiniteTreeLattice.vertexVector` from
  `PositiveDefiniteTreeLattice.Main.LatticeFoundations.Defs.vertexVectorAnchor`
-/
theorem PositiveDefiniteTreeLattice.treePairing_vertexVector_self {V : Type*} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (weight : V → ℤ) (v : V) :
    PositiveDefiniteTreeLattice.treePairing G weight (PositiveDefiniteTreeLattice.vertexVector v)
      (PositiveDefiniteTreeLattice.vertexVector v) = weight v := by
  unfold PositiveDefiniteTreeLattice.treePairing PositiveDefiniteTreeLattice.vertexVector
  rw [Finset.sum_eq_single v]
  · have hnot : v ∉ G.neighborFinset v := G.notMem_neighborFinset_self v
    have hsum : (∑ w ∈ G.neighborFinset v, if w = v then (1 : ℤ) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro w hw
      have hwv : w ≠ v := by
        intro h
        subst w
        exact hnot hw
      simp [hwv]
    simp [hsum]
  · intro b _ hb
    simp [hb]
  · simp
