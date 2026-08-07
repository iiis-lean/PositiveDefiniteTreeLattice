-- lean-constellation: managed-imports-begin
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Prelude
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildComponent
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `rootedChildComponent_isTree`

For any vertex type `V`, simple graph `G : SimpleGraph V`, vertices `parent c : V`, and hypothesis
`hG : G.IsTree`, the induced graph on the deleted-edge component is a tree: `(rootedChildComponent G
parent c).toSimpleGraph.IsTree`.  The statement imposes no adjacency or rooted-child condition on
`parent` and `c`, and no weight, admissibility, positive-definiteness, or scalar hypothesis.

## Sources

- Source `solution.tex`, lines 48–61

## Statement dependencies

- `SimpleGraph.IsTree` from `Mathlib.Combinatorics.SimpleGraph.Acyclic`
- `SimpleGraph.ConnectedComponent.toSimpleGraph` from
  `Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected`
- `Main.RootedCapacity::rootedChildComponent` → `rootedChildComponent` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildComponent`

## Proof outline

Unfold the committed definition `rootedChildComponent`; its component is definitionally
`(G.deleteEdges {s(parent, c)}).connectedComponentMk c`.

Let `Gcut := G.deleteEdges {s(parent, c)}`. First prove `Gcut.IsAcyclic` bottom-up from
`hG.isAcyclic`: apply `SimpleGraph.IsAcyclic.anti` to the subgraph relation `Gcut ≤ G`. For an
adjacency of `Gcut`, unfold/rewrite `SimpleGraph.deleteEdges_adj` and retain the original-`G`
adjacency component, so this local relation needs no hypothesis on `parent`, `c`, or their
adjacency.

Finally apply `SimpleGraph.IsAcyclic.isTree_connectedComponent` to that acyclicity proof and the
component `Gcut.connectedComponentMk c`. After unfolding `rootedChildComponent`, this is exactly the
requested induced graph. The route deliberately introduces no rooted-child, weight, admissibility,
or positive-definiteness assumptions: every connected component of an edge-deleted tree is a tree.

## Proof dependencies

- `SimpleGraph.IsAcyclic.anti` from `Mathlib.Combinatorics.SimpleGraph.Acyclic`
- `SimpleGraph.IsAcyclic.isTree_connectedComponent` from `Mathlib.Combinatorics.SimpleGraph.Acyclic`
- `SimpleGraph.connectedComponentMk` from `Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected`
- `SimpleGraph.deleteEdges` from `Mathlib.Combinatorics.SimpleGraph.DeleteEdges`
- `SimpleGraph.deleteEdges_adj` from `Mathlib.Combinatorics.SimpleGraph.DeleteEdges`
- `Main.RootedCapacity::rootedChildComponent` → `rootedChildComponent` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildComponent`
-/
theorem rootedChildComponent_isTree {V : Type*} (G : SimpleGraph V) (parent c : V)
    (hG : G.IsTree) : (rootedChildComponent G parent c).toSimpleGraph.IsTree := by
  unfold rootedChildComponent
  apply SimpleGraph.IsAcyclic.isTree_connectedComponent
  apply SimpleGraph.IsAcyclic.anti ?_ hG.isAcyclic
  intro v w hvw
  exact (G.deleteEdges_adj.mp hvw).1
