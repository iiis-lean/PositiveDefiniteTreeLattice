-- lean-constellation: managed-imports-begin
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Prelude
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Set.Insert
import Mathlib.Data.Sym.Sym2
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildComponent
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildren
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.rootedChildComponent_parent_not_mem
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `rootedChildComponent_adj_mem`

Let `V` be a finite type, let `G : SimpleGraph V` have decidable adjacency, and let `hG : G.IsTree`.
Fix a root `ρ`, vertices `parent` and `c`, and a membership proof `hc : c ∈ rootedChildren G hG ρ
parent`. If `x : rootedChildComponent G parent c`, `z : V`, `G.Adj (x : V) z`, and `z ≠ parent`,
then `z ∈ rootedChildComponent G parent c`.

Thus, in the existing deleted-parent-child-edge connected-component representation, every ambient
neighbor of a child-component vertex other than the parent endpoint remains in that same child
component.

## Statement dependencies

- `Main.RootedCapacity::rootedChildComponent` → `rootedChildComponent` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildComponent`
- `Main.RootedCapacity::rootedChildren` → `rootedChildren` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildren`

## Proof outline

Work classically. First unfold `rootedChildren` in `hc` and use `Finset.mem_filter` to extract the
parent--child adjacency
`hpc : G.Adj parent c`; the remaining unique-path witness is irrelevant here.

Apply `rootedChildComponent_parent_not_mem G parent c hG hpc x` to obtain
`hxp : (x : V) ≠ parent`.  To preserve the ambient edge in the deleted graph, prove
`s((x : V), z) ∉ ({s(parent, c)} : Finset (Sym2 V))`.  If it were the deleted edge, use
`Sym2.eq_iff`: the orientation `(x : V) = parent, z = c` contradicts `hxp`, while the swapped
orientation
`(x : V) = c, z = parent` contradicts `hz`.  Hence `SimpleGraph.deleteEdges_adj` turns `hxz` into
`(G.deleteEdges {s(parent, c)}).Adj (x : V) z`.

Finally, unfold `rootedChildComponent` only to identify `x.property` as membership in
`(G.deleteEdges {s(parent, c)}).connectedComponentMk c`.  Apply
`SimpleGraph.ConnectedComponent.mem_supp_of_adj_mem_supp` to that membership and the deleted-graph
adjacency,
then fold the definition back to obtain `z ∈ rootedChildComponent G parent c`.

This uses no weights, admissibility, capacity facts, or TreePathSeparation results.

## Proof dependencies

- `SimpleGraph.ConnectedComponent.mem_supp_of_adj_mem_supp` from
  `Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected`
- `SimpleGraph.deleteEdges_adj` from `Mathlib.Combinatorics.SimpleGraph.DeleteEdges`
- `Finset.mem_filter` from `Mathlib.Data.Finset.Filter`
- `Set.mem_singleton_iff` from `Mathlib.Data.Set.Insert`
- `Sym2.eq_iff` from `Mathlib.Data.Sym.Sym2`
- `Main.RootedCapacity::rootedChildComponent_parent_not_mem` → `rootedChildComponent_parent_not_mem`
  from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.rootedChildComponent_parent_not_mem`
-/
theorem rootedChildComponent_adj_mem {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.IsTree) (ρ parent c : V)
    (hc : c ∈ rootedChildren G hG ρ parent) (x : rootedChildComponent G parent c) (z : V)
    (hxz : G.Adj (x : V) z) (hz : z ≠ parent) : z ∈ rootedChildComponent G parent c := by
  classical
  rw [rootedChildren] at hc
  rcases Finset.mem_filter.mp hc with ⟨_, hpc, _⟩
  have hxp : (x : V) ≠ parent := rootedChildComponent_parent_not_mem G parent c hG hpc x
  have hnot : s((x : V), z) ∉ ({s(parent, c)} : Set (Sym2 V)) := by
    simp only [Set.mem_singleton_iff]
    intro h
    rcases Sym2.eq_iff.mp h with h | h
    · exact hxp h.1
    · exact hz h.2
  have hxz' : (G.deleteEdges {s(parent, c)}).Adj (x : V) z := by
    rw [SimpleGraph.deleteEdges_adj]
    exact ⟨hxz, hnot⟩
  have hx_mem : (x : V) ∈ (G.deleteEdges {s(parent, c)}).connectedComponentMk c := by
    simpa only [rootedChildComponent] using x.property
  have hz_mem : z ∈ (G.deleteEdges {s(parent, c)}).connectedComponentMk c :=
    SimpleGraph.ConnectedComponent.mem_supp_of_adj_mem_supp _ hx_mem hxz'
  simpa only [rootedChildComponent] using hz_mem
