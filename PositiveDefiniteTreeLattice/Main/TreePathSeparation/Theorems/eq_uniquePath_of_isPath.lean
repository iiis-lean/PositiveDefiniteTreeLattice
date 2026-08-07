-- lean-constellation: managed-imports-begin
import PositiveDefiniteTreeLattice.Main.TreePathSeparation.Prelude
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Logic.ExistsUnique
import PositiveDefiniteTreeLattice.Main.TreePathSeparation.Defs.uniquePath
import PositiveDefiniteTreeLattice.Main.TreePathSeparation.Theorems.uniquePath_isPath
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `eq_uniquePath_of_isPath`

For a finite vertex type `V`, a simple graph `G` on `V`, a tree certificate `hG : G.IsTree`,
vertices `v w : V`, and a walk `p : G.Walk v w`, if `p.IsPath`, then `p = uniquePath G hG v w`. Thus
every simple walk with these same endpoints in the tree agrees with the canonical chosen walk, with
no cut, component, rooted-capacity, weighted, or matrix assumptions.

## Statement dependencies

- `SimpleGraph.Walk.IsPath` from `Mathlib.Combinatorics.SimpleGraph.Paths`
- `Main.TreePathSeparation::uniquePath` → `uniquePath` from
  `PositiveDefiniteTreeLattice.Main.TreePathSeparation.Defs.uniquePath`

## Proof outline

Apply the uniqueness clause of `hG.existsUnique_path v w` to the two walks with endpoints `v` and
`w`: the given walk `p`, whose pathhood is `hp`, and the canonical walk `uniquePath G hG v w`, whose
pathhood is supplied by the proved helper `uniquePath_isPath G hG v w`. The resulting equality is
exactly `p = uniquePath G hG v w`.

Concretely, the Proof Formal worker can use `exact (hG.existsUnique_path v w).unique hp
(uniquePath_isPath G hG v w)`. This preserves the original graph, tree witness, endpoints, and walk,
with no cut, component, rooted-capacity, weighted, or matrix assumptions.

## Proof sources

- Source `solution.tex`, lines 33–64

## Proof dependencies

- `SimpleGraph.IsTree.existsUnique_path` from `Mathlib.Combinatorics.SimpleGraph.Acyclic`
- `ExistsUnique.unique` from `Mathlib.Logic.ExistsUnique`
- `Main.TreePathSeparation::uniquePath_isPath` → `uniquePath_isPath` from
  `PositiveDefiniteTreeLattice.Main.TreePathSeparation.Theorems.uniquePath_isPath`
-/
theorem eq_uniquePath_of_isPath {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hG : G.IsTree) (v w : V) (p : G.Walk v w) (hp : p.IsPath) :
    p = uniquePath G hG v w := by
  exact (hG.existsUnique_path v w).unique hp (uniquePath_isPath G hG v w)
