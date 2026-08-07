-- lean-constellation: managed-imports-begin
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Prelude
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `rootedChildComponent`

For a finite vertex type `V`, a simple graph `G : SimpleGraph V`, and vertices `parent c : V`,
define `rootedChildComponent G parent c` to be the connected component containing `c` in the graph
obtained from `G` by deleting the singleton set containing the undirected edge joining `parent` and
`c`: `(G.deleteEdges {edge parent c}).connectedComponentMk c`.  No adjacency, child-membership,
tree, or admissibility hypothesis is part of this definition.  On the finite vertex type, this
connected component has a finite subtype and its induced graph is available through
`ConnectedComponent.toSimpleGraph`, so subsequent statements can use it as the child-rooted graph
with a restricted weight.

## Sources

- Source `solution.tex`, lines 48–50

## Statement dependencies

- `SimpleGraph.connectedComponentMk` from `Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected`
- `SimpleGraph.deleteEdges` from `Mathlib.Combinatorics.SimpleGraph.DeleteEdges`
-/
def rootedChildComponent {V : Type*} (G : SimpleGraph V) (parent c : V) :
    (G.deleteEdges {s(parent, c)}).ConnectedComponent :=
  (G.deleteEdges {s(parent, c)}).connectedComponentMk c
