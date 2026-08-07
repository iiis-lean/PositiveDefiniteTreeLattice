-- lean-constellation: managed-imports-begin
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Prelude
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Card
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildCount
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.rootedNeighborFinset_eq_insert_predecessor
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `rootedChildCount_add_one_eq_degree`

In the namespace `PositiveDefiniteTreeLattice`, let `V` be a finite type with decidable equality,
let `G : SimpleGraph V` have decidable adjacency, let `hG : G.IsTree`, and fix vertices `ρ x : V`
with `x ≠ ρ`. Then

`rootedChildCount G hG ρ x + 1 = G.degree x`.

Thus every nonroot vertex has ambient degree exactly one greater than its rooted child count.

## Sources

- Source `solution.tex`, lines 194–204

## Statement dependencies

- `SimpleGraph.IsTree` from `Mathlib.Combinatorics.SimpleGraph.Acyclic`
- `SimpleGraph.degree` from `Mathlib.Combinatorics.SimpleGraph.Finite`
- `Main.RootedCapacity::rootedChildCount` → `rootedChildCount` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildCount`

## Proof outline

Obtain `⟨p, hp_not_child, hneighbors⟩` from the accepted private theorem
`rootedNeighborFinset_eq_insert_predecessor G hG ρ x hx`.  Here

`hp_not_child : p ∉ rootedChildren G hG ρ x` and
`hneighbors : G.neighborFinset x = insert p (rootedChildren G hG ρ x)`.

Unfold `rootedChildCount`.  Calculate
`(rootedChildren G hG ρ x).card + 1` as the cardinality of
`insert p (rootedChildren G hG ρ x)` using the verified
`Finset.card_insert_of_notMem hp_not_child`.  Rewrite that finset with
`hneighbors.symm`, then close with the verified
`SimpleGraph.card_neighborFinset_eq_degree`.  The resulting equality is
exactly `rootedChildCount G hG ρ x + 1 = G.degree x`.

All proof steps preserve the stated generic binders; no weighted, admissibility,
capacity, or component-specific fact is introduced.

## Proof sources

- Source `solution.tex`, lines 194–204

## Proof dependencies

- `SimpleGraph.card_neighborFinset_eq_degree` from `Mathlib.Combinatorics.SimpleGraph.Finite`
- `Finset.card_insert_of_notMem` from `Mathlib.Data.Finset.Card`
- `Main.RootedCapacity::rootedNeighborFinset_eq_insert_predecessor` →
  `rootedNeighborFinset_eq_insert_predecessor` from `PositiveDefiniteTreeLattice.Main.RootedCapacity
  .Theorems.rootedNeighborFinset_eq_insert_predecessor`
-/
theorem PositiveDefiniteTreeLattice.rootedChildCount_add_one_eq_degree {V : Type*} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.IsTree)
    (ρ x : V) (hx : x ≠ ρ) :
    rootedChildCount G hG ρ x + 1 = G.degree x := by
  obtain ⟨p, hp, hneighbors⟩ :=
    rootedNeighborFinset_eq_insert_predecessor G hG ρ x hx
  unfold rootedChildCount
  calc
    (rootedChildren G hG ρ x).card + 1 = (insert p (rootedChildren G hG ρ x)).card :=
      (Finset.card_insert_of_notMem hp).symm
    _ = (G.neighborFinset x).card := by rw [hneighbors]
    _ = G.degree x := G.card_neighborFinset_eq_degree x
