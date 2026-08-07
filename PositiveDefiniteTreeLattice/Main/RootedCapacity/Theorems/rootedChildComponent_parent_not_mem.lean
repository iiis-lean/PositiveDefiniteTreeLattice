-- lean-constellation: managed-imports-begin
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Prelude
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildComponent
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `rootedChildComponent_parent_not_mem`

For a finite vertex type `V` with decidable equality, a simple graph `G : SimpleGraph V`, vertices
`parent c : V`, a tree hypothesis `hG : G.IsTree`, and an adjacency hypothesis `hpc : G.Adj parent
c`, every vertex of the child-side cut component differs from `parent`: for every `x :
rootedChildComponent G parent c`, `(x : V) ≠ parent`.  Equivalently, `parent` is not a vertex of the
connected component containing `c` after deleting exactly the singleton undirected edge joining
`parent` and `c`.  No weight, root-orientation, admissibility, matrix, or positive-definiteness
hypothesis is assumed.

## Sources

- Source `solution.tex`, lines 48–61

## Statement dependencies

- `SimpleGraph.IsTree` from `Mathlib.Combinatorics.SimpleGraph.Acyclic`
- `Main.RootedCapacity::rootedChildComponent` → `rootedChildComponent` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildComponent`

## Proof outline

Fix a component vertex `x : rootedChildComponent G parent c` and suppose `(x : V) = parent`. Unfold
`rootedChildComponent`; the subtype property of `x` then gives membership of `parent` in the support
of the connected component `C := (G.deleteEdges {s(parent, c)}).connectedComponentMk c`. The
canonical member `c ∈ C.supp` and `SimpleGraph.ConnectedComponent.reachable_of_mem_supp` yield a
cut-graph reachability witness `(G.deleteEdges {s(parent, c)}).Reachable c parent`.

Pair this reachability with the reversed adjacency `hpc.symm : G.Adj c parent`. Apply
`SimpleGraph.adj_and_reachable_delete_edges_iff_exists_cycle` to obtain a cycle in the original
graph `G` containing the deleted undirected edge `s(parent, c)`. This contradicts `hG.isAcyclic`,
whose definition excludes every graph cycle.

Thus no component-subtype vertex can coerce to `parent`. The argument uses exactly the singleton
deleted edge `{s(parent, c)}` and introduces no weight, root-orientation, admissibility, matrix, or
positive-definiteness assumptions.

## Proof dependencies

- `SimpleGraph.ConnectedComponent.connectedComponentMk_mem` from
  `Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected`
- `SimpleGraph.ConnectedComponent.reachable_of_mem_supp` from
  `Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected`
- `SimpleGraph.adj_and_reachable_delete_edges_iff_exists_cycle` from
  `Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected`
- `SimpleGraph.deleteEdges` from `Mathlib.Combinatorics.SimpleGraph.DeleteEdges`
- `Main.RootedCapacity::rootedChildComponent` → `rootedChildComponent` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildComponent`
-/
theorem rootedChildComponent_parent_not_mem {V : Type*} (G : SimpleGraph V) (parent c : V)
    (hG : G.IsTree) (hpc : G.Adj parent c) :
    ∀ x : rootedChildComponent G parent c, (x : V) ≠ parent := by
  classical
  intro x hx
  have hx_mem : (x : V) ∈ (G.deleteEdges {s(parent, c)}).connectedComponentMk c := by
    simpa only [rootedChildComponent] using x.property
  have hparent_mem : parent ∈ (G.deleteEdges {s(parent, c)}).connectedComponentMk c := by
    simpa only [hx] using hx_mem
  have hc_mem : c ∈ (G.deleteEdges {s(parent, c)}).connectedComponentMk c :=
    SimpleGraph.ConnectedComponent.connectedComponentMk_mem
  have hreach : (G.deleteEdges {s(parent, c)}).Reachable parent c :=
    SimpleGraph.ConnectedComponent.reachable_of_mem_supp _ hparent_mem hc_mem
  obtain ⟨u, cycle, hcycle, _⟩ :=
    (SimpleGraph.adj_and_reachable_delete_edges_iff_exists_cycle.mp
      ⟨hpc, hreach⟩)
  exact hG.isAcyclic cycle hcycle
