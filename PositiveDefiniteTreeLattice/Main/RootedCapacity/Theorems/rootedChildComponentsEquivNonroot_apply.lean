-- lean-constellation: managed-imports-begin
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Prelude
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Fintype.Defs
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildComponent
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildComponentsEquivNonroot
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildren
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.rootedChildComponent_parent_not_mem
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `rootedChildComponentsEquivNonroot_apply`

Let V be a finite type with decidable equality, let G be a simple graph on V with decidable
adjacency, let hG : G.IsTree, let ρ : V, let

c : {c : V // c ∈ rootedChildren G hG ρ ρ},

and let x : rootedChildComponent G ρ c.1. Let hcAdj : G.Adj ρ c.1 be the adjacency fact extracted
from c.property by unfolding rootedChildren. Then the forward map of
rootedChildComponentsEquivNonroot has the following equality in the full nonroot subtype:

rootedChildComponentsEquivNonroot G hG ρ ⟨c, x⟩
= ⟨(x : V), rootedChildComponent_parent_not_mem G ρ c.1 hG hcAdj x⟩
  : {v : V // v ≠ ρ}.

The equality retains the nonroot proofs as part of its target; it evaluates only the equivalence’s
forward inclusion and does not unfold or simplify its partition-chosen inverse.

## Sources

- Source `solution.tex`, lines 57–62

## Statement dependencies

- `SimpleGraph.IsTree` from `Mathlib.Combinatorics.SimpleGraph.Acyclic`
- `Finset.mem_filter` from `Mathlib.Data.Finset.Filter`
- `Finset.mem_univ` from `Mathlib.Data.Fintype.Defs`
- `Main.RootedCapacity::rootedChildComponent` → `rootedChildComponent` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildComponent`
- `Main.RootedCapacity::rootedChildComponent_parent_not_mem` → `rootedChildComponent_parent_not_mem`
  from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.rootedChildComponent_parent_not_mem`
- `Main.RootedCapacity::rootedChildComponentsEquivNonroot` → `rootedChildComponentsEquivNonroot`
  from `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildComponentsEquivNonroot`
- `Main.RootedCapacity::rootedChildren` → `rootedChildren` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildren`

## Proof outline

Work classically and unfold the statement's local `hcAdj` proof, retaining its full subtype-valued
equality target. Expose `rootedChildComponentsEquivNonroot G hG ρ` only far enough to project its
forward map `toFun`; do not unfold or simplify its `invFun` field, so the partition-selected inverse
is never reduced.

At the sigma input `⟨c,x⟩`, the exposed forward map is definitionally the subtype
`⟨(x : V), rootedChildComponent_parent_not_mem G ρ c.1 hG hAdj x⟩`,
where `hAdj` is obtained from `c.property` by the same `rootedChildren` filter simplification as the
statement's `hcAdj`. The underlying vertex on this subtype is definitionally `(x : V)`.

Apply `Subtype.ext` to the desired equality. The coerced-vertex goal is reflexive, so close it by
`rfl`; proof irrelevance discharges the potentially different proofs of `(x : V) ≠ ρ`. This proves
equality in the complete nonroot subtype, precisely the form needed to rewrite reindex indices, and
uses neither the inverse partition choice nor any reverse-evaluation statement.

## Proof sources

- Source `solution.tex`, lines 57–62

## Proof dependencies

- `Main.RootedCapacity::rootedChildComponent` → `rootedChildComponent` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildComponent`
- `Main.RootedCapacity::rootedChildComponent_parent_not_mem` → `rootedChildComponent_parent_not_mem`
  from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.rootedChildComponent_parent_not_mem`
- `Main.RootedCapacity::rootedChildComponentsEquivNonroot` → `rootedChildComponentsEquivNonroot`
  from `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildComponentsEquivNonroot`
- `Main.RootedCapacity::rootedChildren` → `rootedChildren` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildren`
-/
theorem rootedChildComponentsEquivNonroot_apply {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.IsTree) (ρ : V)
    (c : {c : V // c ∈ rootedChildren G hG ρ ρ}) (x : rootedChildComponent G ρ c.1) :
    let hcAdj : G.Adj ρ c.1 := by
      have hc := c.property
      simp only [rootedChildren, Finset.mem_filter, Finset.mem_univ, true_and] at hc
      exact hc.1
    rootedChildComponentsEquivNonroot G hG ρ ⟨c, x⟩ =
      ⟨(x : V), rootedChildComponent_parent_not_mem G ρ c.1 hG hcAdj x⟩ := by
  classical
  dsimp
  apply Subtype.ext
  rfl
