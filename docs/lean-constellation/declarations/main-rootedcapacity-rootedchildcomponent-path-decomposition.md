[← Public API](../PUBLIC_API.md) · [Public boundaries](../PUBLIC_BOUNDARIES.md)

# `rootedChildComponent_path_decomposition`

Ambient root paths to a child component factor through the child root.

- Kind: `theorem`
- Node: `Main.RootedCapacity`
- Module: `PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.rootedChildComponent_path_decomposition`
- State: `proved`
- Revision status: `committed`
- Repository completion: `graph_proved`
- Formal code: final proof projection

## Lean code

```lean
-- lean-constellation: managed-imports-begin
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Prelude
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Walk.Maps
import Mathlib.Combinatorics.SimpleGraph.Walk.Operations
import Mathlib.Data.List.Nodup
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildComponent
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildren
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `rootedChildComponent_path_decomposition`

For a finite vertex type `V` with decidable equality, a simple graph `G : SimpleGraph V`, a tree
proof `hG : G.IsTree`, an ambient root `ρ : V`, vertices `parent c : V`, a hypothesis `hc : c ∈
rootedChildren G hG ρ parent`, and `x : rootedChildComponent G parent c`, the chosen unique ambient
path from `ρ` to `(x : V)` factors through `c`.  More precisely, the unique path
`(hG.existsUnique_path ρ (x : V)).choose` is the concatenation of `(hG.existsUnique_path ρ
c).choose` with `(hG.existsUnique_path c (x : V)).choose`, with the shared endpoint `c` and
endpoints `ρ` and `(x : V)` preserved.  This is a path-decomposition equality, not merely a
reachability or support-membership assertion; it assumes no weight, admissibility, or matrix
condition.

## Sources

- Source `solution.tex`, lines 48–61

## Statement dependencies

- `SimpleGraph.IsTree` from `Mathlib.Combinatorics.SimpleGraph.Acyclic`
- `SimpleGraph.IsTree.existsUnique_path` from `Mathlib.Combinatorics.SimpleGraph.Acyclic`
- `SimpleGraph.Walk.append` from `Mathlib.Combinatorics.SimpleGraph.Walk.Operations`
- `Main.RootedCapacity::rootedChildComponent` → `rootedChildComponent` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildComponent`
- `Main.RootedCapacity::rootedChildren` → `rootedChildren` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildren`

## Proof outline

Unfold `rootedChildren` in `hc`. Its filtered-membership witness supplies an oriented edge `hpc :
G.Adj parent c`, a walk `q : G.Walk ρ parent`, and the equality identifying the chosen `ρ`–`c` path
with `q.concat hpc`.

Establish `hroot : (G.deleteEdges {s(parent, c)}).Reachable ρ parent` by retaining the
root-to-parent walk `q` after the cut. The equality from `hc` makes `q.concat hpc` the chosen simple
tree path from `ρ` to `c`. Hence its root-to-parent prefix cannot traverse the terminal undirected
edge `s(parent,c)`: such a traversal would force `c` to occur in the prefix and again as the
terminal endpoint after concatenation, contradicting simplicity. Transport the resulting
edge-avoidance of `q` to a walk in `G.deleteEdges {s(parent,c)}`, giving the required reachability.

For `hx : (G.deleteEdges {s(parent,c)}).Reachable c (x : V)`, unfold `rootedChildComponent`. The
subtype/component-membership fact `x.property` says that `x` belongs to the connected component
represented by `connectedComponentMk c`; convert that membership (equivalently, equality of the two
connected-component representatives) directly to deleted-graph reachability from `c` to `(x : V)`.

Apply `PositiveDefiniteTreeLattice.uniquePath_eq_append_through_cut G hG ρ parent c (x : V) hpc
hroot hx`. Finally unfold `PositiveDefiniteTreeLattice.uniquePath`; its `Classical.choose` paths are
definitionally the `(hG.existsUnique_path _ _).choose` walks occurring in the accepted statement, so
the provider conclusion closes the exact retained equality by `simpa`.

## Proof sources

- Source `solution.tex`, lines 48–61

## Proof dependencies

- `SimpleGraph.ConnectedComponent.connectedComponentMk_mem` from
  `Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected`
- `SimpleGraph.ConnectedComponent.reachable_of_mem_supp` from
  `Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected`
- `SimpleGraph.Walk.toDeleteEdges` from `Mathlib.Combinatorics.SimpleGraph.Walk.Maps`
- `SimpleGraph.Walk.edges_concat` from `Mathlib.Combinatorics.SimpleGraph.Walk.Operations`
- `List.nodup_concat` from `Mathlib.Data.List.Nodup`
- `Main.RootedCapacity::rootedChildComponent` → `rootedChildComponent` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildComponent`
- `Main.RootedCapacity::rootedChildren` → `rootedChildren` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildren`
- `Main.TreePathSeparation::uniquePath` → `uniquePath` from
  `PositiveDefiniteTreeLattice.Main.TreePathSeparation.Defs.uniquePath`
- `Main.TreePathSeparation::uniquePath_eq_append_through_cut` →
  `PositiveDefiniteTreeLattice.uniquePath_eq_append_through_cut` from
  `PositiveDefiniteTreeLattice.Main.TreePathSeparation.Theorems.uniquePath_eq_append_through_cut`
-/
theorem rootedChildComponent_path_decomposition {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.IsTree) (ρ parent c : V)
    (hc : c ∈ rootedChildren G hG ρ parent) (x : rootedChildComponent G parent c) :
    (hG.existsUnique_path ρ (x : V)).choose =
      (hG.existsUnique_path ρ c).choose.append
        (hG.existsUnique_path c (x : V)).choose := by
  classical
  simp only [rootedChildren, Finset.mem_filter, Finset.mem_univ, true_and] at hc
  obtain ⟨hpc, q, hq, hqeq⟩ := hc
  have hpath : (q.concat hpc).IsPath := by
    rw [← hqeq]
    exact (hG.existsUnique_path ρ c).choose_spec.1
  have havoids : ∀ e, e ∈ q.edges → e ∉ ({s(parent, c)} : Set (Sym2 V)) := by
    intro e he hes
    rw [Set.mem_singleton_iff] at hes
    subst e
    have hnodup : (q.edges.concat s(parent, c)).Nodup := by
      simpa only [SimpleGraph.Walk.edges_concat] using hpath.edges_nodup
    exact (List.nodup_concat q.edges s(parent, c)).mp hnodup |>.1 he
  have hroot : (G.deleteEdges {s(parent, c)}).Reachable ρ parent := by
    exact ⟨q.toDeleteEdges {s(parent, c)} havoids⟩
  have hx : (G.deleteEdges {s(parent, c)}).Reachable c (x : V) := by
    apply SimpleGraph.ConnectedComponent.reachable_of_mem_supp
    · exact SimpleGraph.ConnectedComponent.connectedComponentMk_mem
    · change (x : V) ∈ (G.deleteEdges {s(parent, c)}).connectedComponentMk c
      exact x.property
  simpa only [uniquePath] using
    PositiveDefiniteTreeLattice.uniquePath_eq_append_through_cut G hG ρ parent c (x : V)
      hpc hroot hx
```

## Statement dependencies

- `Mathlib:Mathlib.Combinatorics.SimpleGraph.Acyclic.SimpleGraph.IsTree`
- `Mathlib:Mathlib.Combinatorics.SimpleGraph.Acyclic.SimpleGraph.IsTree.existsUnique_path`
- `Mathlib:Mathlib.Combinatorics.SimpleGraph.Walk.Operations.SimpleGraph.Walk.append`
- `current repo:Main.RootedCapacity.rootedChildComponent`
- `current repo:Main.RootedCapacity.rootedChildren`

## Proof dependencies

- `Mathlib:Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected.SimpleGraph.ConnectedComponent.connectedComponentMk_mem`
- `Mathlib:Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected.SimpleGraph.ConnectedComponent.reachable_of_mem_supp`
- `Mathlib:Mathlib.Combinatorics.SimpleGraph.Walk.Maps.SimpleGraph.Walk.toDeleteEdges`
- `Mathlib:Mathlib.Combinatorics.SimpleGraph.Walk.Operations.SimpleGraph.Walk.edges_concat`
- `Mathlib:Mathlib.Data.List.Nodup.List.nodup_concat`
- `current repo:Main.RootedCapacity.rootedChildComponent`
- `current repo:Main.RootedCapacity.rootedChildren`
- `current repo:Main.TreePathSeparation.uniquePath`
- `current repo:Main.TreePathSeparation.uniquePath_eq_append_through_cut`

## Sources

- `solution.tex:48-61`
