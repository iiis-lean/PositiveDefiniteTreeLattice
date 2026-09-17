[← Public API](../PUBLIC_API.md) · [Public boundaries](../PUBLIC_BOUNDARIES.md) · [Complete graph](../DECLARATION_GRAPH.md)

# `uniquePath_eq_append_through_cut`

A chosen finite-tree path factors through the child endpoint of an oriented edge cut.

- Kind: `theorem`
- Node: `Main.TreePathSeparation`
- Module: `PositiveDefiniteTreeLattice.Main.TreePathSeparation.Theorems.uniquePath_eq_append_through_cut`
- State: `proved`
- Revision status: `committed`
- Repository completion: `graph_proved`
- Compatibility `formal_code`: final proof projection

## Statement NL

The public theorem `PositiveDefiniteTreeLattice.uniquePath_eq_append_through_cut` has the following statement. Let `{V : Type*}` carry `[Fintype V]`, let `G : SimpleGraph V`, let `hG : G.IsTree`, and let `root parent c x : V`. Assume `hpc : G.Adj parent c`, `hroot : (G.deleteEdges {s(parent, c)}).Reachable root parent`, and `hx : (G.deleteEdges {s(parent, c)}).Reachable c x`. Then

`uniquePath G hG root x = (uniquePath G hG root c).append (uniquePath G hG c x)`.

This is an exact chosen-path factorization through `c`: it preserves the root-to-`x`, root-to-`c`, and `c`-to-`x` path objects and their endpoints, and adds no assumptions or RootedCapacity-specific terminology.

## Statement Formal

```lean
-- lean-constellation: managed-imports-begin
import PositiveDefiniteTreeLattice.Main.TreePathSeparation.Prelude
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Combinatorics.SimpleGraph.Walk.Operations
import PositiveDefiniteTreeLattice.Main.TreePathSeparation.Defs.uniquePath
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `uniquePath_eq_append_through_cut`

The public theorem `PositiveDefiniteTreeLattice.uniquePath_eq_append_through_cut` has the following
statement. Let `{V : Type*}` carry `[Fintype V]`, let `G : SimpleGraph V`, let `hG : G.IsTree`, and
let `root parent c x : V`. Assume `hpc : G.Adj parent c`, `hroot : (G.deleteEdges {s(parent,
c)}).Reachable root parent`, and `hx : (G.deleteEdges {s(parent, c)}).Reachable c x`. Then

`uniquePath G hG root x = (uniquePath G hG root c).append (uniquePath G hG c x)`.

This is an exact chosen-path factorization through `c`: it preserves the root-to-`x`, root-to-`c`,
and `c`-to-`x` path objects and their endpoints, and adds no assumptions or RootedCapacity-specific
terminology.

## Statement dependencies

- `SimpleGraph.Reachable` from `Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected`
- `SimpleGraph.deleteEdges` from `Mathlib.Combinatorics.SimpleGraph.DeleteEdges`
- `SimpleGraph.Walk.append` from `Mathlib.Combinatorics.SimpleGraph.Walk.Operations`
- `Main.TreePathSeparation::uniquePath` → `uniquePath` from
  `PositiveDefiniteTreeLattice.Main.TreePathSeparation.Defs.uniquePath`
-/
theorem PositiveDefiniteTreeLattice.uniquePath_eq_append_through_cut
    {V : Type*} [Fintype V] (G : SimpleGraph V) (hG : G.IsTree)
    (root parent c x : V) (hpc : G.Adj parent c)
    (hroot : (G.deleteEdges {s(parent, c)}).Reachable root parent)
    (hx : (G.deleteEdges {s(parent, c)}).Reachable c x) :
    uniquePath G hG root x =
      (uniquePath G hG root c).append (uniquePath G hG c x) := by
  sorry
```

## Proof NL

Let `p := (uniquePath G hG root c).append (uniquePath G hG c x)`. The proved bridge `uniquePath_append_isPath_through_cut G hG root parent c x hpc hroot hx` gives `p.IsPath` with endpoints `root` and `x`.

Apply the proved uniqueness eliminator `eq_uniquePath_of_isPath G hG root x p` to this pathhood proof. It yields `p = uniquePath G hG root x`. Take symmetry to obtain exactly `uniquePath G hG root x = (uniquePath G hG root c).append (uniquePath G hG c x)`.

Thus the proof preserves every copied binder and all three chosen path objects, and introduces no additional hypothesis or RootedCapacity terminology.

## Proof Formal

```lean
-- lean-constellation: managed-imports-begin
import PositiveDefiniteTreeLattice.Main.TreePathSeparation.Prelude
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Combinatorics.SimpleGraph.Walk.Operations
import PositiveDefiniteTreeLattice.Main.TreePathSeparation.Defs.uniquePath
import PositiveDefiniteTreeLattice.Main.TreePathSeparation.Theorems.eq_uniquePath_of_isPath
import PositiveDefiniteTreeLattice.Main.TreePathSeparation.Theorems.uniquePath_append_isPath_through_cut
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `uniquePath_eq_append_through_cut`

The public theorem `PositiveDefiniteTreeLattice.uniquePath_eq_append_through_cut` has the following
statement. Let `{V : Type*}` carry `[Fintype V]`, let `G : SimpleGraph V`, let `hG : G.IsTree`, and
let `root parent c x : V`. Assume `hpc : G.Adj parent c`, `hroot : (G.deleteEdges {s(parent,
c)}).Reachable root parent`, and `hx : (G.deleteEdges {s(parent, c)}).Reachable c x`. Then

`uniquePath G hG root x = (uniquePath G hG root c).append (uniquePath G hG c x)`.

This is an exact chosen-path factorization through `c`: it preserves the root-to-`x`, root-to-`c`,
and `c`-to-`x` path objects and their endpoints, and adds no assumptions or RootedCapacity-specific
terminology.

## Statement dependencies

- `SimpleGraph.Reachable` from `Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected`
- `SimpleGraph.deleteEdges` from `Mathlib.Combinatorics.SimpleGraph.DeleteEdges`
- `SimpleGraph.Walk.append` from `Mathlib.Combinatorics.SimpleGraph.Walk.Operations`
- `Main.TreePathSeparation::uniquePath` → `uniquePath` from
  `PositiveDefiniteTreeLattice.Main.TreePathSeparation.Defs.uniquePath`

## Proof outline

Let `p := (uniquePath G hG root c).append (uniquePath G hG c x)`. The proved bridge
`uniquePath_append_isPath_through_cut G hG root parent c x hpc hroot hx` gives `p.IsPath` with
endpoints `root` and `x`.

Apply the proved uniqueness eliminator `eq_uniquePath_of_isPath G hG root x p` to this pathhood
proof. It yields `p = uniquePath G hG root x`. Take symmetry to obtain exactly `uniquePath G hG root
x = (uniquePath G hG root c).append (uniquePath G hG c x)`.

Thus the proof preserves every copied binder and all three chosen path objects, and introduces no
additional hypothesis or RootedCapacity terminology.

## Proof sources

- Source `solution.tex`, lines 33–64

## Proof dependencies

- `Main.TreePathSeparation::eq_uniquePath_of_isPath` → `eq_uniquePath_of_isPath` from
  `PositiveDefiniteTreeLattice.Main.TreePathSeparation.Theorems.eq_uniquePath_of_isPath`
- `Main.TreePathSeparation::uniquePath_append_isPath_through_cut` →
  `uniquePath_append_isPath_through_cut` from `PositiveDefiniteTreeLattice.Main.TreePathSeparation.T
  heorems.uniquePath_append_isPath_through_cut`
-/
theorem PositiveDefiniteTreeLattice.uniquePath_eq_append_through_cut
    {V : Type*} [Fintype V] (G : SimpleGraph V) (hG : G.IsTree)
    (root parent c x : V) (hpc : G.Adj parent c)
    (hroot : (G.deleteEdges {s(parent, c)}).Reachable root parent)
    (hx : (G.deleteEdges {s(parent, c)}).Reachable c x) :
    uniquePath G hG root x =
      (uniquePath G hG root c).append (uniquePath G hG c x) := by
  exact (eq_uniquePath_of_isPath G hG root x
    ((uniquePath G hG root c).append (uniquePath G hG c x))
    (uniquePath_append_isPath_through_cut G hG root parent c x hpc hroot hx)).symm
```

## Statement dependencies

- `Mathlib:Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected.SimpleGraph.Reachable`
- `Mathlib:Mathlib.Combinatorics.SimpleGraph.DeleteEdges.SimpleGraph.deleteEdges`
- `Mathlib:Mathlib.Combinatorics.SimpleGraph.Walk.Operations.SimpleGraph.Walk.append`
- `current repo:Main.TreePathSeparation.uniquePath`

## Proof dependencies

- `current repo:Main.TreePathSeparation.eq_uniquePath_of_isPath`
- `current repo:Main.TreePathSeparation.uniquePath_append_isPath_through_cut`
