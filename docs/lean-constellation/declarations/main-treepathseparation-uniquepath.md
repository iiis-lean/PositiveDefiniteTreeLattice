[← Public API](../PUBLIC_API.md) · [Public boundaries](../PUBLIC_BOUNDARIES.md)

# `uniquePath`

The canonical chosen simple walk between two vertices of a finite simple tree.

- Kind: `def`
- Node: `Main.TreePathSeparation`
- Module: `PositiveDefiniteTreeLattice.Main.TreePathSeparation.Defs.uniquePath`
- State: `declared`
- Revision status: `committed`
- Repository completion: `graph_proved`
- Formal code: final statement projection

## Lean code

```lean
-- lean-constellation: managed-imports-begin
import PositiveDefiniteTreeLattice.Main.TreePathSeparation.Prelude
import Mathlib.Combinatorics.SimpleGraph.Acyclic
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `uniquePath`

For a finite vertex type `V`, a simple graph `G` on `V`, a tree certificate `hG : G.IsTree`, and
vertices `v w : V`, define `uniquePath G hG v w : G.Walk v w` to be the walk component of the unique
path witness supplied by `hG.existsUnique_path v w`. Thus the construction has exactly the endpoints
`v` and `w` in its type, keeps `hG` as an explicit parameter, and selects the tree's unique path
rather than an arbitrary walk.

## Statement dependencies

- `SimpleGraph.IsTree.existsUnique_path` from `Mathlib.Combinatorics.SimpleGraph.Acyclic`
-/
noncomputable def uniquePath {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hG : G.IsTree) (v w : V) : G.Walk v w :=
  Classical.choose (hG.existsUnique_path v w)
```

## Statement dependencies

- `Mathlib:Mathlib.Combinatorics.SimpleGraph.Acyclic.SimpleGraph.IsTree.existsUnique_path`
