-- lean-constellation: managed-imports-begin
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Prelude
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildComponent
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `rootedChildRoot`

For any vertex type `V`, simple graph `G : SimpleGraph V`, and vertices `parent c : V`, define
`rootedChildRoot G parent c` to be the subtype element of `rootedChildComponent G parent c` whose
underlying vertex is `c`.  Its membership proof is `ConnectedComponent.connectedComponentMk_mem`,
since `rootedChildComponent G parent c` is the connected component containing `c` after the
designated edge deletion.  Thus `(rootedChildRoot G parent c : V) = c`, providing the canonical root
argument for constructions on the induced child component.  The definition assumes no tree,
adjacency, admissibility, finiteness, decidability, or weight condition.

## Sources

- Source `solution.tex`, lines 48–50

## Statement dependencies

- `SimpleGraph.ConnectedComponent.connectedComponentMk_mem` from
  `Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected`
- `Main.RootedCapacity::rootedChildComponent` → `rootedChildComponent` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildComponent`
-/
def rootedChildRoot {V : Type*} (G : SimpleGraph V) (parent c : V) :
    rootedChildComponent G parent c :=
  ⟨c, by
    unfold rootedChildComponent
    exact SimpleGraph.ConnectedComponent.connectedComponentMk_mem⟩
