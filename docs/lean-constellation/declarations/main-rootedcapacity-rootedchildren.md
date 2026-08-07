[← Public API](../PUBLIC_API.md) · [Public boundaries](../PUBLIC_BOUNDARIES.md)

# `rootedChildren`

The finite set of children of a vertex in a finite tree rooted at a chosen vertex.

- Kind: `definition`
- Node: `Main.RootedCapacity`
- Module: `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildren`
- State: `declared`
- Revision status: `committed`
- Repository completion: `graph_proved`
- Formal code: final statement projection

## Lean code

```lean
-- lean-constellation: managed-imports-begin
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Prelude
import Mathlib.Combinatorics.SimpleGraph.Acyclic
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `rootedChildren`

For a finite simple graph `G` that is a tree, a chosen root `ρ`, and a vertex `y`, define
`rootedChildren G ρ y` to be the finite set of vertices `z` adjacent to `y` for which the unique
simple path in `G` from `ρ` to `z` reaches `y` immediately before `z`.  Thus the edges of `G` are
oriented away from `ρ`, and this set is exactly the children of `y` in that rooted orientation.

## Sources

- Source `solution.tex`, lines 33–34

## Statement dependencies

- `SimpleGraph.IsTree.existsUnique_path` from `Mathlib.Combinatorics.SimpleGraph.Acyclic`
-/
noncomputable def rootedChildren {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hG : G.IsTree) (ρ y : V) : Finset V :=
  by
    classical
    exact Finset.univ.filter fun z =>
      ∃ h : G.Adj y z, ∃ q : G.Walk ρ y, q.IsPath ∧
        (hG.existsUnique_path ρ z).choose = q.concat h
```

## Statement dependencies

- `Mathlib:Mathlib.Combinatorics.SimpleGraph.Acyclic.SimpleGraph.IsTree.existsUnique_path`

## Sources

- `solution.tex:33-34`
