[← Public API](../PUBLIC_API.md) · [Public boundaries](../PUBLIC_BOUNDARIES.md)

# `rootedEdgeClassification`

Every edge of a finite rooted tree is a root-child edge or an edge internal to one unique root-child component.

- Kind: `theorem`
- Node: `Main.RootedCapacity`
- Module: `PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.rootedEdgeClassification`
- State: `proved`
- Revision status: `committed`
- Repository completion: `graph_proved`
- Formal code: final proof projection

## Lean code

```lean
-- lean-constellation: managed-imports-begin
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Prelude
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Walk.Basic
import Mathlib.Combinatorics.SimpleGraph.Walk.Operations
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Set.Insert
import Mathlib.Data.Sym.Sym2
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildComponent
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildren
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.rootedChildComponent_adj_mem
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.rootedChildComponent_partition
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `rootedEdgeClassification`

Let `V` be a finite type with decidable equality, let `G : SimpleGraph V` have decidable adjacency,
let `hG : G.IsTree`, and fix a root `ρ` and ordered vertices `u v : V`. Then `G.Adj u v` holds if
and only if either:

1. `u = ρ` and `v ∈ rootedChildren G hG ρ ρ`, or `v = ρ` and `u ∈ rootedChildren G hG ρ ρ`; or
2. there exists a unique `c ∈ rootedChildren G hG ρ ρ` for which there are vertices `u_c v_c :
rootedChildComponent G ρ c` satisfying `(u_c : V) = u` and `(v_c : V) = v`, and `u_c` and `v_c` are
adjacent in the `toSimpleGraph` of that child component.

The unique component case retains both subtype witnesses, their ambient coercion equalities, and
local component adjacency, so an ambient ordered neighbor-edge can be reindexed directly as a local
ordered edge. The theorem is in namespace `PositiveDefiniteTreeLattice`, with full name
`PositiveDefiniteTreeLattice.rootedEdgeClassification`.

## Statement dependencies

- `SimpleGraph.ConnectedComponent.toSimpleGraph` from
  `Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected`
- `Main.RootedCapacity::rootedChildComponent` → `rootedChildComponent` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildComponent`
- `Main.RootedCapacity::rootedChildren` → `rootedChildren` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildren`

## Proof outline

Work classically and prove the displayed equivalence.

For the forward implication, first split on u = ρ. In that branch substitute u and then split on v =
ρ. If also v = ρ, substitute v and close the impossible hypothesis G.Adj ρ ρ by SimpleGraph.irrefl;
this simultaneous-root branch produces no classification witness. Only in the remaining u = ρ, v ≠ ρ
subcase, unfold rootedChildren and apply Finset.mem_filter. Supply the ambient root edge, the empty
walk from ρ to itself, and identify the chosen unique path to v with the one-edge walk by
(hG.existsUnique_path ρ v).unique and SimpleGraph.Walk.IsPath.of_adj. This gives the first
root-child alternative.

In the complementary u ≠ ρ branch, split on v = ρ. Only in this root-incident subcase, unfold
rootedChildren and apply Finset.mem_filter, using the symmetric ambient edge, the empty walk, and
the same unique-path argument; this gives the second root-child alternative. In the remaining u ≠ ρ,
v ≠ ρ subcase, apply rootedChildComponent_partition G hG ρ u to obtain its unique child c, its
child-membership proof, and u ∈ rootedChildComponent G ρ c. Let uC be the resulting subtype vertex.
Apply rootedChildComponent_adj_mem G hG ρ ρ c to uC, the original adjacency, and v ≠ ρ, producing v
∈ rootedChildComponent G ρ c, hence a subtype vertex vC.

For the required local edge witness, show the ambient edge s(u,v) is not the deleted edge s(ρ,c). By
Sym2.eq_iff, equality would either force u = ρ or force v = ρ, contradicting the two nonroot
branches. Thus SimpleGraph.deleteEdges_adj turns the ambient adjacency into adjacency of
G.deleteEdges {s(ρ,c)}. After unfolding rootedChildComponent and ConnectedComponent.toSimpleGraph,
this is exactly the induced local adjacency of uC and vC. Package the child membership, subtype
coercion equalities, and this edge proof as the ∃! witness. For uniqueness, if another child d has
the packaged witnesses, use the ambient coercion equality of its uD to turn uD.property into u ∈
rootedChildComponent G ρ d; then the uniqueness field of rootedChildComponent_partition G hG ρ u
gives d = c.

For the reverse implication, unfold each root-child membership through rootedChildren and
Finset.mem_filter to recover the root-to-opposite-endpoint adjacency (symmetrizing for the second
orientation). In the component alternative, extract the unique witness and its local edge, rewrite
using the two subtype-coercion equalities, unfold ConnectedComponent.toSimpleGraph to obtain
deleted-graph adjacency, and take the first conjunct of SimpleGraph.deleteEdges_adj to recover G.Adj
u v.

This proof route uses only generic rooted-tree and deleted-edge component data; it introduces no
weights, capacity facts, pairing, estimates, or TreePathSeparation results.

## Proof dependencies

- `SimpleGraph.IsTree.existsUnique_path` from `Mathlib.Combinatorics.SimpleGraph.Acyclic`
- `SimpleGraph.irrefl` from `Mathlib.Combinatorics.SimpleGraph.Basic`
- `SimpleGraph.ConnectedComponent.toSimpleGraph` from
  `Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected`
- `SimpleGraph.deleteEdges_adj` from `Mathlib.Combinatorics.SimpleGraph.DeleteEdges`
- `SimpleGraph.Walk.IsPath.of_adj` from `Mathlib.Combinatorics.SimpleGraph.Paths`
- `SimpleGraph.Walk.cons` from `Mathlib.Combinatorics.SimpleGraph.Walk.Basic`
- `SimpleGraph.Walk.nil` from `Mathlib.Combinatorics.SimpleGraph.Walk.Basic`
- `SimpleGraph.Walk.concat` from `Mathlib.Combinatorics.SimpleGraph.Walk.Operations`
- `Finset.mem_filter` from `Mathlib.Data.Finset.Filter`
- `Finset.mem_univ` from `Mathlib.Data.Fintype.Defs`
- `Set.mem_singleton_iff` from `Mathlib.Data.Set.Insert`
- `Sym2.eq_iff` from `Mathlib.Data.Sym.Sym2`
- `Main.RootedCapacity::rootedChildComponent_adj_mem` → `rootedChildComponent_adj_mem` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.rootedChildComponent_adj_mem`
- `Main.RootedCapacity::rootedChildComponent_partition` → `rootedChildComponent_partition` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.rootedChildComponent_partition`
-/
theorem PositiveDefiniteTreeLattice.rootedEdgeClassification {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.IsTree) (ρ u v : V) :
    G.Adj u v ↔
      (u = ρ ∧ v ∈ rootedChildren G hG ρ ρ) ∨
        (v = ρ ∧ u ∈ rootedChildren G hG ρ ρ) ∨
          ∃! c : V, c ∈ rootedChildren G hG ρ ρ ∧
            ∃ uC vC : rootedChildComponent G ρ c,
              (uC : V) = u ∧ (vC : V) = v ∧
                (rootedChildComponent G ρ c).toSimpleGraph.Adj uC vC := by
  classical
  constructor
  · intro huv
    by_cases hu : u = ρ
    · subst u
      by_cases hv : v = ρ
      · subst v
        exact (G.irrefl huv).elim
      · left
        refine ⟨rfl, ?_⟩
        simp only [rootedChildren, Finset.mem_filter, Finset.mem_univ, true_and]
        have hsingle : (hG.existsUnique_path ρ v).choose =
            SimpleGraph.Walk.cons huv .nil := by
          apply (hG.existsUnique_path ρ v).unique
          · exact (hG.existsUnique_path ρ v).choose_spec.1
          · exact SimpleGraph.Walk.IsPath.of_adj huv
        refine ⟨huv, .nil, SimpleGraph.Walk.IsPath.nil, ?_⟩
        simpa [SimpleGraph.Walk.concat] using hsingle
    · by_cases hv : v = ρ
      · subst v
        right
        left
        refine ⟨rfl, ?_⟩
        simp only [rootedChildren, Finset.mem_filter, Finset.mem_univ, true_and]
        have hsingle : (hG.existsUnique_path ρ u).choose =
            SimpleGraph.Walk.cons huv.symm .nil := by
          apply (hG.existsUnique_path ρ u).unique
          · exact (hG.existsUnique_path ρ u).choose_spec.1
          · exact SimpleGraph.Walk.IsPath.of_adj huv.symm
        refine ⟨huv.symm, .nil, SimpleGraph.Walk.IsPath.nil, ?_⟩
        simpa [SimpleGraph.Walk.concat] using hsingle
      · right
        right
        obtain ⟨c, ⟨hc, huc⟩, hc_unique⟩ :=
          rootedChildComponent_partition G hG ρ u hu
        let uC : rootedChildComponent G ρ c := ⟨u, huc⟩
        have hvc : v ∈ rootedChildComponent G ρ c :=
          rootedChildComponent_adj_mem G hG ρ ρ c hc uC v huv hv
        let vC : rootedChildComponent G ρ c := ⟨v, hvc⟩
        have hnot : s(u, v) ∉ ({s(ρ, c)} : Set (Sym2 V)) := by
          simp only [Set.mem_singleton_iff]
          intro h
          rcases Sym2.eq_iff.mp h with h | h
          · exact hu h.1
          · exact hv h.2
        have hdeleted : (G.deleteEdges {s(ρ, c)}).Adj u v := by
          rw [SimpleGraph.deleteEdges_adj]
          exact ⟨huv, hnot⟩
        have hlocal : (rootedChildComponent G ρ c).toSimpleGraph.Adj uC vC := by
          simpa [uC, vC, rootedChildComponent,
            SimpleGraph.ConnectedComponent.toSimpleGraph] using hdeleted
        refine ⟨c, ⟨hc, uC, vC, rfl, rfl, hlocal⟩, ?_⟩
        intro d hd
        rcases hd with ⟨hdc, uD, vD, huD, hvD, hlocalD⟩
        apply hc_unique d
        refine ⟨hdc, ?_⟩
        rw [← huD]
        exact uD.property
  · intro h
    rcases h with hroot | hroot | hcomponent
    · rcases hroot with ⟨rfl, hc⟩
      rw [rootedChildren] at hc
      rcases Finset.mem_filter.mp hc with ⟨_, hρv, _⟩
      exact hρv
    · rcases hroot with ⟨rfl, hc⟩
      rw [rootedChildren] at hc
      rcases Finset.mem_filter.mp hc with ⟨_, hρu, _⟩
      exact hρu.symm
    · rcases hcomponent with ⟨c, ⟨hc, uC, vC, huC, hvC, hlocal⟩, _⟩
      rw [← huC, ← hvC]
      have hdeleted : (G.deleteEdges {s(ρ, c)}).Adj (uC : V) (vC : V) := by
        simpa [rootedChildComponent,
          SimpleGraph.ConnectedComponent.toSimpleGraph] using hlocal
      exact (SimpleGraph.deleteEdges_adj.mp hdeleted).1
```

## Statement dependencies

- `Mathlib:Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected.SimpleGraph.ConnectedComponent.toSimpleGraph`
- `current repo:Main.RootedCapacity.rootedChildComponent`
- `current repo:Main.RootedCapacity.rootedChildren`

## Proof dependencies

- `Mathlib:Mathlib.Combinatorics.SimpleGraph.Acyclic.SimpleGraph.IsTree.existsUnique_path`
- `Mathlib:Mathlib.Combinatorics.SimpleGraph.Basic.SimpleGraph.irrefl`
- `Mathlib:Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected.SimpleGraph.ConnectedComponent.toSimpleGraph`
- `Mathlib:Mathlib.Combinatorics.SimpleGraph.DeleteEdges.SimpleGraph.deleteEdges_adj`
- `Mathlib:Mathlib.Combinatorics.SimpleGraph.Paths.SimpleGraph.Walk.IsPath.of_adj`
- `Mathlib:Mathlib.Combinatorics.SimpleGraph.Walk.Basic.SimpleGraph.Walk.cons`
- `Mathlib:Mathlib.Combinatorics.SimpleGraph.Walk.Basic.SimpleGraph.Walk.nil`
- `Mathlib:Mathlib.Combinatorics.SimpleGraph.Walk.Operations.SimpleGraph.Walk.concat`
- `Mathlib:Mathlib.Data.Finset.Filter.Finset.mem_filter`
- `Mathlib:Mathlib.Data.Fintype.Defs.Finset.mem_univ`
- `Mathlib:Mathlib.Data.Set.Insert.Set.mem_singleton_iff`
- `Mathlib:Mathlib.Data.Sym.Sym2.Sym2.eq_iff`
- `current repo:Main.RootedCapacity.rootedChildComponent_adj_mem`
- `current repo:Main.RootedCapacity.rootedChildComponent_partition`
