[← Public API](../PUBLIC_API.md) · [Public boundaries](../PUBLIC_BOUNDARIES.md)

# `rootedChildComponent_card_lt`

A rooted child-side component has strictly fewer vertices than its ambient finite tree.

- Kind: `theorem`
- Node: `Main.RootedCapacity`
- Module: `PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.rootedChildComponent_card_lt`
- State: `proved`
- Revision status: `committed`
- Repository completion: `graph_proved`
- Formal code: final proof projection

## Lean code

```lean
-- lean-constellation: managed-imports-begin
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Prelude
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.Fintype.Card
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildComponent
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildren
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.rootedChildComponent_parent_not_mem
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `rootedChildComponent_card_lt`

Let `V` be a finite decidable vertex type and let `G` be a graph with decidable adjacency and tree
witness `hG : G.IsTree`. Fix an ambient root, a vertex `parent`, and a vertex `c` such that `c`
belongs to the existing `rootedChildren` Finset of `parent` (so `parent` and `c` are the
corresponding oriented parent–child edge; this includes the case of a root child).

Then the existing child-side component determined by that edge is strictly smaller than the ambient
vertex type:
```
Fintype.card (rootedChildComponent G parent c) < Fintype.card V.
```
Here the component is exactly the existing subtype obtained by deleting the undirected parent–child
edge. The result has no weight or admissibility hypothesis and is oriented for applying an induction
hypothesis to each rooted child subtree.

## Sources

- Source `solution.tex`, lines 74–81

## Statement dependencies

- `SimpleGraph.IsTree` from `Mathlib.Combinatorics.SimpleGraph.Acyclic`
- `Main.RootedCapacity::rootedChildComponent` → `rootedChildComponent` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildComponent`
- `Main.RootedCapacity::rootedChildren` → `rootedChildren` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildren`

## Proof outline

Work classically and retain the statement’s local `Fintype (rootedChildComponent G parent c)`
instance.  Unfold membership in `rootedChildren G hG ρ parent` just enough to extract the adjacency
witness `hpc : G.Adj parent c` from `hc`; no root-orientation property beyond that witness is
needed.

Use the canonical coercion `f : rootedChildComponent G parent c → V`, `f x := (x : V)`.  It is
injective by subtype extensionality (`Subtype.val_injective`).  Apply the exact finite-cardinality
lemma `Fintype.card_lt_of_injective_of_notMem f` once it is shown that `parent ∉ Set.range f`.

For that range exclusion, suppose `parent = f x` for a component vertex `x`.  The already proved
structural cut lemma `rootedChildComponent_parent_not_mem G parent c hG hpc x` says `(x : V) ≠
parent`, contradicting the assumed equality.  Thus `parent` is a concrete ambient vertex absent from
the subtype inclusion’s range, and the cardinality lemma concludes `Fintype.card
(rootedChildComponent G parent c) < Fintype.card V`.

The route uses only the existing deleted-edge component and tree/child data; it introduces no
weight, admissibility, or additional graph assumptions.

## Proof sources

- Source `solution.tex`, lines 74–81

## Proof dependencies

- `Fintype.card_lt_of_injective_of_notMem` from `Mathlib.Data.Fintype.Card`
- `Main.RootedCapacity::rootedChildComponent` → `rootedChildComponent` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildComponent`
- `Main.RootedCapacity::rootedChildComponent_parent_not_mem` → `rootedChildComponent_parent_not_mem`
  from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.rootedChildComponent_parent_not_mem`
- `Main.RootedCapacity::rootedChildren` → `rootedChildren` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildren`
-/
theorem rootedChildComponent_card_lt {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.IsTree) (ρ parent c : V)
    (hc : c ∈ rootedChildren G hG ρ parent) :
    letI : Fintype (rootedChildComponent G parent c) := Fintype.ofFinite _
    Fintype.card (rootedChildComponent G parent c) < Fintype.card V := by
  classical
  letI : Fintype (rootedChildComponent G parent c) := Fintype.ofFinite _
  have hpc : G.Adj parent c := by
    simp only [rootedChildren, Finset.mem_filter, Finset.mem_univ, true_and] at hc
    exact hc.choose
  refine Fintype.card_lt_of_injective_of_notMem
    (fun x : rootedChildComponent G parent c => (x : V)) Subtype.val_injective (b := parent) ?_
  rintro ⟨x, hx⟩
  exact (rootedChildComponent_parent_not_mem G parent c hG hpc x) hx
```

## Statement dependencies

- `Mathlib:Mathlib.Combinatorics.SimpleGraph.Acyclic.SimpleGraph.IsTree`
- `current repo:Main.RootedCapacity.rootedChildComponent`
- `current repo:Main.RootedCapacity.rootedChildren`

## Proof dependencies

- `Mathlib:Mathlib.Data.Fintype.Card.Fintype.card_lt_of_injective_of_notMem`
- `current repo:Main.RootedCapacity.rootedChildComponent`
- `current repo:Main.RootedCapacity.rootedChildComponent_parent_not_mem`
- `current repo:Main.RootedCapacity.rootedChildren`

## Sources

- `solution.tex:74-81`
