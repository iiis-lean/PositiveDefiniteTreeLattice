[← Public API](../PUBLIC_API.md) · [Public boundaries](../PUBLIC_BOUNDARIES.md) · [Complete graph](../DECLARATION_GRAPH.md)

# `treePairing_symm`

The weighted simple-graph pairing is symmetric.

- Kind: `theorem`
- Node: `Main.LatticeFoundations`
- Module: `PositiveDefiniteTreeLattice.Main.LatticeFoundations.Theorems.treePairing_symm`
- State: `proved`
- Revision status: `committed`
- Repository completion: `graph_proved`
- Compatibility `formal_code`: final proof projection

## Statement NL

For a finite type `V` with decidable equality, a simple graph `G : SimpleGraph V` with decidable adjacency, an integer-valued weight function `weight : V → ℤ`, and functions `x y : V → ℤ`, the pairing is symmetric:

`treePairing G weight x y = treePairing G weight y x`.

## Statement Formal

```lean
-- lean-constellation: managed-imports-begin
import PositiveDefiniteTreeLattice.Main.LatticeFoundations.Prelude
import PositiveDefiniteTreeLattice.Main.LatticeFoundations.Defs.treePairingAnchor
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `treePairing_symm`

For a finite type `V` with decidable equality, a simple graph `G : SimpleGraph V` with decidable
adjacency, an integer-valued weight function `weight : V → ℤ`, and functions `x y : V → ℤ`, the
pairing is symmetric:

`treePairing G weight x y = treePairing G weight y x`.

## Statement dependencies

- `Main.LatticeFoundations::treePairingAnchor` → `PositiveDefiniteTreeLattice.treePairing` from
  `PositiveDefiniteTreeLattice.Main.LatticeFoundations.Defs.treePairingAnchor`
-/
theorem PositiveDefiniteTreeLattice.treePairing_symm {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (weight : V → ℤ) (x y : V → ℤ) :
    PositiveDefiniteTreeLattice.treePairing G weight x y =
      PositiveDefiniteTreeLattice.treePairing G weight y x := by
  sorry
```

## Proof NL

Unfold `PositiveDefiniteTreeLattice.treePairing` and separate it into its weighted diagonal contribution and its adjacency contribution.  The diagonal sums agree after commuting integer multiplication.  For the adjacency term, rewrite each `G.neighborFinset u` using `SimpleGraph.neighborFinset_eq_filter`; use `SimpleGraph.adj_comm` to identify the filtered ordered-pair condition with its swapped version, and apply `Finset.sum_comm` to exchange the two finite indices.  The swapped double sum is the adjacency contribution of `treePairing G weight y x`; normalize the signs and products with `ring` to conclude.

## Proof Formal

```lean
-- lean-constellation: managed-imports-begin
import PositiveDefiniteTreeLattice.Main.LatticeFoundations.Prelude
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import PositiveDefiniteTreeLattice.Main.LatticeFoundations.Defs.treePairingAnchor
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `treePairing_symm`

For a finite type `V` with decidable equality, a simple graph `G : SimpleGraph V` with decidable
adjacency, an integer-valued weight function `weight : V → ℤ`, and functions `x y : V → ℤ`, the
pairing is symmetric:

`treePairing G weight x y = treePairing G weight y x`.

## Statement dependencies

- `Main.LatticeFoundations::treePairingAnchor` → `PositiveDefiniteTreeLattice.treePairing` from
  `PositiveDefiniteTreeLattice.Main.LatticeFoundations.Defs.treePairingAnchor`

## Proof outline

Unfold `PositiveDefiniteTreeLattice.treePairing` and separate it into its weighted diagonal
contribution and its adjacency contribution.  The diagonal sums agree after commuting integer
multiplication.  For the adjacency term, rewrite each `G.neighborFinset u` using
`SimpleGraph.neighborFinset_eq_filter`; use `SimpleGraph.adj_comm` to identify the filtered
ordered-pair condition with its swapped version, and apply `Finset.sum_comm` to exchange the two
finite indices.  The swapped double sum is the adjacency contribution of `treePairing G weight y x`;
normalize the signs and products with `ring` to conclude.

## Proof dependencies

- `Finset.sum_congr` from `Mathlib.Algebra.BigOperators.Group.Finset.Basic`
- `Finset.sum_filter` from `Mathlib.Algebra.BigOperators.Group.Finset.Basic`
- `Finset.sum_sub_distrib` from `Mathlib.Algebra.BigOperators.Group.Finset.Defs`
- `Finset.sum_comm` from `Mathlib.Algebra.BigOperators.Group.Finset.Sigma`
- `Finset.mul_sum` from `Mathlib.Algebra.BigOperators.Ring.Finset`
- `SimpleGraph.adj_comm` from `Mathlib.Combinatorics.SimpleGraph.Basic`
- `SimpleGraph.neighborFinset_eq_filter` from `Mathlib.Combinatorics.SimpleGraph.Finite`
- `Main.LatticeFoundations::treePairingAnchor` → `PositiveDefiniteTreeLattice.treePairing` from
  `PositiveDefiniteTreeLattice.Main.LatticeFoundations.Defs.treePairingAnchor`
-/
theorem PositiveDefiniteTreeLattice.treePairing_symm {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (weight : V → ℤ) (x y : V → ℤ) :
    PositiveDefiniteTreeLattice.treePairing G weight x y =
      PositiveDefiniteTreeLattice.treePairing G weight y x := by
  unfold PositiveDefiniteTreeLattice.treePairing
  have hEdge : (∑ u, x u * ∑ v ∈ G.neighborFinset u, y v) =
      ∑ u, y u * ∑ v ∈ G.neighborFinset u, x v := by
    simp_rw [SimpleGraph.neighborFinset_eq_filter]
    simp only [Finset.sum_filter]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro v _
    apply Finset.sum_congr rfl
    intro u _
    by_cases h : G.Adj u v
    · have h' : G.Adj v u := (G.adj_comm u v).mp h
      simp [h, h']
      ring
    · have h' : ¬ G.Adj v u := by
        intro h'
        exact h ((G.adj_comm v u).mp h')
      simp [h, h']
  have hDiag : (∑ u, x u * (weight u * y u)) =
      ∑ u, y u * (weight u * x u) := by
    apply Finset.sum_congr rfl
    intro u _
    ring
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, hEdge, hDiag]
```

## Statement dependencies

- `current repo:Main.LatticeFoundations.treePairingAnchor`

## Proof dependencies

- `Mathlib:Mathlib.Algebra.BigOperators.Group.Finset.Basic.Finset.sum_congr`
- `Mathlib:Mathlib.Algebra.BigOperators.Group.Finset.Basic.Finset.sum_filter`
- `Mathlib:Mathlib.Algebra.BigOperators.Group.Finset.Defs.Finset.sum_sub_distrib`
- `Mathlib:Mathlib.Algebra.BigOperators.Group.Finset.Sigma.Finset.sum_comm`
- `Mathlib:Mathlib.Algebra.BigOperators.Ring.Finset.Finset.mul_sum`
- `Mathlib:Mathlib.Combinatorics.SimpleGraph.Basic.SimpleGraph.adj_comm`
- `Mathlib:Mathlib.Combinatorics.SimpleGraph.Finite.SimpleGraph.neighborFinset_eq_filter`
- `current repo:Main.LatticeFoundations.treePairingAnchor`
