-- lean-constellation: managed-imports-begin
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Prelude
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Finite
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `treePairing_vertexVector_vertexVector`

For every finite integer-weighted simple graph `G` satisfying the tree hypothesis `G.IsTree`, weight
function `w`, and vertices `u` and `v`, the pairing of the corresponding vertex vectors is
`treePairing G w (vertexVector u) (vertexVector v) = if u = v then w u else if G.Adj u v then -1
else 0`.
Equivalently, diagonal basis entries are the vertex weights, distinct adjacent basis entries are
`-1`, and distinct nonadjacent basis entries are `0`.

## Sources

- Source `solution.tex`, lines 57–64

## Statement dependencies

- `SimpleGraph.IsTree` from `Mathlib.Combinatorics.SimpleGraph.Acyclic`
- `Main.LatticeFoundations::treePairingAnchor` → `PositiveDefiniteTreeLattice.treePairing` from
  `PositiveDefiniteTreeLattice.Main.LatticeFoundations.Defs.treePairingAnchor`
- `Main.LatticeFoundations::vertexVectorAnchor` → `PositiveDefiniteTreeLattice.vertexVector` from
  `PositiveDefiniteTreeLattice.Main.LatticeFoundations.Defs.vertexVectorAnchor`

## Proof outline

Case split on `u = v`.

* In the diagonal case, substitute `v = u`. The goal reduces by simplification to the public
provider theorem `PositiveDefiniteTreeLattice.treePairing_vertexVector_self G w u`; the tree
hypothesis is not needed for this algebraic basis-entry calculation.

* In the distinct case, unfold only `PositiveDefiniteTreeLattice.treePairing` and
`PositiveDefiniteTreeLattice.vertexVector`. Use `Finset.sum_eq_single u` to evaluate the outer
finite sum: all coordinates other than `u` vanish, and the remaining expression is the negative of
the neighbor sum of the unit vector at `v`. Split on `G.Adj u v`. If adjacent, rewrite `v ∈
G.neighborFinset u` with `SimpleGraph.mem_neighborFinset` and use `Finset.sum_eq_single v`; every
other neighbor coordinate is zero, so the neighbor sum is `1` and the result is `-1`. If
nonadjacent, `SimpleGraph.mem_neighborFinset` shows that no neighbor can equal `v`; apply
`Finset.sum_eq_zero` to make the neighbor sum `0`, yielding `0`. In both branches, finish by
simplifying the relevant equality/inequality hypotheses.

This route uses the accepted public definitions `PositiveDefiniteTreeLattice.treePairing` and
`PositiveDefiniteTreeLattice.vertexVector`, and the accepted diagonal provider
`PositiveDefiniteTreeLattice.treePairing_vertexVector_self`.

## Proof sources

- Source `formal_target.lean`, lines 7–15

## Proof dependencies

- `Finset.sum_eq_single` from `Mathlib.Algebra.BigOperators.Group.Finset.Basic`
- `Finset.sum_eq_zero` from `Mathlib.Algebra.BigOperators.Group.Finset.Basic`
- `SimpleGraph.mem_neighborFinset` from `Mathlib.Combinatorics.SimpleGraph.Finite`
- `Main.LatticeFoundations::treePairingAnchor` → `PositiveDefiniteTreeLattice.treePairing` from
  `PositiveDefiniteTreeLattice.Main.LatticeFoundations.Defs.treePairingAnchor`
- `Main.LatticeFoundations::treePairing_vertexVector_self` →
  `PositiveDefiniteTreeLattice.treePairing_vertexVector_self` from
  `PositiveDefiniteTreeLattice.Main.LatticeFoundations.Theorems.treePairing_vertexVector_self`
- `Main.LatticeFoundations::vertexVectorAnchor` → `PositiveDefiniteTreeLattice.vertexVector` from
  `PositiveDefiniteTreeLattice.Main.LatticeFoundations.Defs.vertexVectorAnchor`
-/
theorem treePairing_vertexVector_vertexVector {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.IsTree) (w : V → ℤ) (u v : V) :
    PositiveDefiniteTreeLattice.treePairing G w
        (PositiveDefiniteTreeLattice.vertexVector u)
        (PositiveDefiniteTreeLattice.vertexVector v) =
      if u = v then w u else if G.Adj u v then -1 else 0 := by
  have _hG : G.IsTree := hG
  by_cases huv : u = v
  · subst v
    simp [PositiveDefiniteTreeLattice.treePairing_vertexVector_self]
  · simp only [huv, if_false]
    unfold PositiveDefiniteTreeLattice.treePairing PositiveDefiniteTreeLattice.vertexVector
    rw [Finset.sum_eq_single u]
    · simp only [if_pos, one_mul, huv, if_false, mul_zero, zero_sub]
      by_cases hadj : G.Adj u v
      · rw [if_pos hadj]
        have hv_mem : v ∈ G.neighborFinset u := (G.mem_neighborFinset u v).mpr hadj
        rw [Finset.sum_eq_single v]
        · simp
        · intro b _ hbu
          simp [hbu]
        · intro hv_not_mem
          exact (hv_not_mem hv_mem).elim
      · rw [if_neg hadj]
        have hsum : (G.neighborFinset u).sum (fun x => if x = v then (1 : ℤ) else 0) = 0 := by
          apply Finset.sum_eq_zero
          intro x hx
          have hxv : x ≠ v := by
            intro h
            subst x
            exact hadj ((G.mem_neighborFinset u v).mp hx)
          simp [hxv]
        simp [hsum]
    · intro b _ hbu
      simp [hbu]
    · simp
