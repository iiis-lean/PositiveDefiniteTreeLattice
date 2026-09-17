[← Public API](../PUBLIC_API.md) · [Public boundaries](../PUBLIC_BOUNDARIES.md) · [Complete graph](../DECLARATION_GRAPH.md)

# `uniquePath_isPath`

The canonical chosen tree walk is a simple path.

- Kind: `theorem`
- Node: `Main.TreePathSeparation`
- Module: `PositiveDefiniteTreeLattice.Main.TreePathSeparation.Theorems.uniquePath_isPath`
- State: `proved`
- Revision status: `committed`
- Repository completion: `graph_proved`
- Compatibility `formal_code`: final proof projection

## Statement NL

For a finite vertex type `V`, a simple graph `G` on `V`, a tree certificate `hG : G.IsTree`, and vertices `v w : V`, the canonical walk `uniquePath G hG v w` is a simple path: `(uniquePath G hG v w).IsPath`. The theorem uses exactly the same graph, tree certificate, and endpoints as `uniquePath`, and introduces no cut, reachability, rooted-capacity, weighted, or matrix assumptions.

## Statement Formal

```lean
-- lean-constellation: managed-imports-begin
import PositiveDefiniteTreeLattice.Main.TreePathSeparation.Prelude
import Mathlib.Combinatorics.SimpleGraph.Paths
import PositiveDefiniteTreeLattice.Main.TreePathSeparation.Defs.uniquePath
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `uniquePath_isPath`

For a finite vertex type `V`, a simple graph `G` on `V`, a tree certificate `hG : G.IsTree`, and
vertices `v w : V`, the canonical walk `uniquePath G hG v w` is a simple path: `(uniquePath G hG v
w).IsPath`. The theorem uses exactly the same graph, tree certificate, and endpoints as
`uniquePath`, and introduces no cut, reachability, rooted-capacity, weighted, or matrix assumptions.

## Statement dependencies

- `SimpleGraph.Walk.IsPath` from `Mathlib.Combinatorics.SimpleGraph.Paths`
- `Main.TreePathSeparation::uniquePath` → `uniquePath` from
  `PositiveDefiniteTreeLattice.Main.TreePathSeparation.Defs.uniquePath`
-/
theorem uniquePath_isPath {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hG : G.IsTree) (v w : V) : (uniquePath G hG v w).IsPath := by
  sorry
```

## Proof NL

Unfold `uniquePath G hG v w`. By its definition, this walk is `Classical.choose (hG.existsUnique_path v w)`. The witness theorem `SimpleGraph.IsTree.existsUnique_path` states that there is a unique walk from `v` to `w` satisfying `IsPath`; hence `Classical.choose_spec (hG.existsUnique_path v w)` gives precisely `(uniquePath G hG v w).IsPath` after simplification by the definition of `uniquePath`.

This preserves the original finite graph, tree witness, and endpoints exactly. It introduces no cut, reachability, rooted-capacity, weighted, or matrix hypotheses.

## Proof Formal

```lean
-- lean-constellation: managed-imports-begin
import PositiveDefiniteTreeLattice.Main.TreePathSeparation.Prelude
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Paths
import PositiveDefiniteTreeLattice.Main.TreePathSeparation.Defs.uniquePath
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `uniquePath_isPath`

For a finite vertex type `V`, a simple graph `G` on `V`, a tree certificate `hG : G.IsTree`, and
vertices `v w : V`, the canonical walk `uniquePath G hG v w` is a simple path: `(uniquePath G hG v
w).IsPath`. The theorem uses exactly the same graph, tree certificate, and endpoints as
`uniquePath`, and introduces no cut, reachability, rooted-capacity, weighted, or matrix assumptions.

## Statement dependencies

- `SimpleGraph.Walk.IsPath` from `Mathlib.Combinatorics.SimpleGraph.Paths`
- `Main.TreePathSeparation::uniquePath` → `uniquePath` from
  `PositiveDefiniteTreeLattice.Main.TreePathSeparation.Defs.uniquePath`

## Proof outline

Unfold `uniquePath G hG v w`. By its definition, this walk is `Classical.choose
(hG.existsUnique_path v w)`. The witness theorem `SimpleGraph.IsTree.existsUnique_path` states that
there is a unique walk from `v` to `w` satisfying `IsPath`; hence `Classical.choose_spec
(hG.existsUnique_path v w)` gives precisely `(uniquePath G hG v w).IsPath` after simplification by
the definition of `uniquePath`.

This preserves the original finite graph, tree witness, and endpoints exactly. It introduces no cut,
reachability, rooted-capacity, weighted, or matrix hypotheses. The remaining Lean proof should be
`simpa only [uniquePath] using Classical.choose_spec (hG.existsUnique_path v w)`.

## Proof sources

- Source `solution.tex`, lines 33–64

## Proof dependencies

- `SimpleGraph.IsTree.existsUnique_path` from `Mathlib.Combinatorics.SimpleGraph.Acyclic`
- `Main.TreePathSeparation::uniquePath` → `uniquePath` from
  `PositiveDefiniteTreeLattice.Main.TreePathSeparation.Defs.uniquePath`
-/
theorem uniquePath_isPath {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hG : G.IsTree) (v w : V) : (uniquePath G hG v w).IsPath := by
  simpa only [uniquePath] using (Classical.choose_spec (hG.existsUnique_path v w)).1
```

## Statement dependencies

- `Mathlib:Mathlib.Combinatorics.SimpleGraph.Paths.SimpleGraph.Walk.IsPath`
- `current repo:Main.TreePathSeparation.uniquePath`

## Proof dependencies

- `Mathlib:Mathlib.Combinatorics.SimpleGraph.Acyclic.SimpleGraph.IsTree.existsUnique_path`
- `current repo:Main.TreePathSeparation.uniquePath`
