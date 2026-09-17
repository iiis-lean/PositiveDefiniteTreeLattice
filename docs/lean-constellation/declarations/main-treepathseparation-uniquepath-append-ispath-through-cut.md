[← Public API](../PUBLIC_API.md) · [Public boundaries](../PUBLIC_BOUNDARIES.md) · [Complete graph](../DECLARATION_GRAPH.md)

# `uniquePath_append_isPath_through_cut`

The append of the chosen root-to-child and child-to-vertex paths is simple across the oriented cut.

- Kind: `theorem`
- Node: `Main.TreePathSeparation`
- Module: `PositiveDefiniteTreeLattice.Main.TreePathSeparation.Theorems.uniquePath_append_isPath_through_cut`
- State: `proved`
- Revision status: `committed`
- Repository completion: `graph_proved`
- Compatibility `formal_code`: final proof projection

## Statement NL

For `{V} [Fintype V]`, a simple graph `G` on `V`, a tree certificate `hG : G.IsTree`, and vertices `root parent c x : V`, assume `hpc : G.Adj parent c`, `hroot : (G.deleteEdges {s(parent, c)}).Reachable root parent`, and `hx : (G.deleteEdges {s(parent, c)}).Reachable c x`. Then the exact append of the two chosen paths is a simple path:

`((uniquePath G hG root c).append (uniquePath G hG c x)).IsPath`.

This has precisely the consumer-side binders and cut hypotheses of `PositiveDefiniteTreeLattice.uniquePath_support_separated_by_cut`; it neither adds assumptions nor changes the endpoints or chosen path objects.

## Statement Formal

```lean
-- lean-constellation: managed-imports-begin
import PositiveDefiniteTreeLattice.Main.TreePathSeparation.Prelude
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Walk.Operations
import PositiveDefiniteTreeLattice.Main.TreePathSeparation.Defs.uniquePath
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `uniquePath_append_isPath_through_cut`

For `{V} [Fintype V]`, a simple graph `G` on `V`, a tree certificate `hG : G.IsTree`, and vertices
`root parent c x : V`, assume `hpc : G.Adj parent c`, `hroot : (G.deleteEdges {s(parent,
c)}).Reachable root parent`, and `hx : (G.deleteEdges {s(parent, c)}).Reachable c x`. Then the exact
append of the two chosen paths is a simple path:

`((uniquePath G hG root c).append (uniquePath G hG c x)).IsPath`.

This has precisely the consumer-side binders and cut hypotheses of
`PositiveDefiniteTreeLattice.uniquePath_support_separated_by_cut`; it neither adds assumptions nor
changes the endpoints or chosen path objects.

## Statement dependencies

- `SimpleGraph.Reachable` from `Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected`
- `SimpleGraph.deleteEdges` from `Mathlib.Combinatorics.SimpleGraph.DeleteEdges`
- `SimpleGraph.Walk.IsPath` from `Mathlib.Combinatorics.SimpleGraph.Paths`
- `SimpleGraph.Walk.append` from `Mathlib.Combinatorics.SimpleGraph.Walk.Operations`
- `Main.TreePathSeparation::uniquePath` → `uniquePath` from
  `PositiveDefiniteTreeLattice.Main.TreePathSeparation.Defs.uniquePath`
-/
theorem uniquePath_append_isPath_through_cut {V : Type*} [Fintype V]
    (G : SimpleGraph V) (hG : G.IsTree) (root parent c x : V)
    (hpc : G.Adj parent c)
    (hroot : (G.deleteEdges {s(parent, c)}).Reachable root parent)
    (hx : (G.deleteEdges {s(parent, c)}).Reachable c x) :
    ((uniquePath G hG root c).append (uniquePath G hG c x)).IsPath := by
  sorry
```

## Proof NL

Let `p := uniquePath G hG root c` and `q := uniquePath G hG c x`. The proved helper `uniquePath_isPath` gives `p.IsPath` and `q.IsPath`; by `Walk.isPath_def`, both supports are nodup.

Use the exact public cut theorem `PositiveDefiniteTreeLattice.uniquePath_support_separated_by_cut G hG root parent c x hpc hroot hx` to show `p.support.Disjoint q.support.tail`. Indeed, if a vertex belongs to both lists, it belongs to both full supports, so the cut theorem makes it equal to `c`. But `c` is the first vertex of `q` and `q.IsPath` makes `q.support` nodup, so `c ∉ q.support.tail` (equivalently, use `Walk.mem_support_iff` and the nodup contradiction).

Finally rewrite the support of the exact target append with `Walk.support_append` as `p.support ++ q.support.tail`. The nodup proofs for `p.support` and `q.support.tail`, together with the displayed disjointness, give nodup of that appended list. Apply the reverse direction of `Walk.isPath_def` to conclude `(p.append q).IsPath`. This uses precisely the copied cut hypotheses and exact chosen path objects, with no additional assumptions.

## Proof Formal

```lean
-- lean-constellation: managed-imports-begin
import PositiveDefiniteTreeLattice.Main.TreePathSeparation.Prelude
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Walk.Basic
import Mathlib.Combinatorics.SimpleGraph.Walk.Operations
import PositiveDefiniteTreeLattice.Main.TreePathSeparation.Defs.uniquePath
import PositiveDefiniteTreeLattice.Main.TreePathSeparation.Theorems.uniquePath_isPath
import PositiveDefiniteTreeLattice.Main.TreePathSeparation.Theorems.uniquePath_support_separated_by_cut
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `uniquePath_append_isPath_through_cut`

For `{V} [Fintype V]`, a simple graph `G` on `V`, a tree certificate `hG : G.IsTree`, and vertices
`root parent c x : V`, assume `hpc : G.Adj parent c`, `hroot : (G.deleteEdges {s(parent,
c)}).Reachable root parent`, and `hx : (G.deleteEdges {s(parent, c)}).Reachable c x`. Then the exact
append of the two chosen paths is a simple path:

`((uniquePath G hG root c).append (uniquePath G hG c x)).IsPath`.

This has precisely the consumer-side binders and cut hypotheses of
`PositiveDefiniteTreeLattice.uniquePath_support_separated_by_cut`; it neither adds assumptions nor
changes the endpoints or chosen path objects.

## Statement dependencies

- `SimpleGraph.Reachable` from `Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected`
- `SimpleGraph.deleteEdges` from `Mathlib.Combinatorics.SimpleGraph.DeleteEdges`
- `SimpleGraph.Walk.IsPath` from `Mathlib.Combinatorics.SimpleGraph.Paths`
- `SimpleGraph.Walk.append` from `Mathlib.Combinatorics.SimpleGraph.Walk.Operations`
- `Main.TreePathSeparation::uniquePath` → `uniquePath` from
  `PositiveDefiniteTreeLattice.Main.TreePathSeparation.Defs.uniquePath`

## Proof outline

Let `p := uniquePath G hG root c` and `q := uniquePath G hG c x`. The proved helper
`uniquePath_isPath` gives `p.IsPath` and `q.IsPath`; by `Walk.isPath_def`, both supports are nodup.

Use the exact public cut theorem `PositiveDefiniteTreeLattice.uniquePath_support_separated_by_cut G
hG root parent c x hpc hroot hx` to show `p.support.Disjoint q.support.tail`. Indeed, if a vertex
belongs to both lists, it belongs to both full supports, so the cut theorem makes it equal to `c`.
But `c` is the first vertex of `q` and `q.IsPath` makes `q.support` nodup, so `c ∉ q.support.tail`
(equivalently, use `Walk.mem_support_iff` and the nodup contradiction).

Finally rewrite the support of the exact target append with `Walk.support_append` as `p.support ++
q.support.tail`. The nodup proofs for `p.support` and `q.support.tail`, together with the displayed
disjointness, give nodup of that appended list. Apply the reverse direction of `Walk.isPath_def` to
conclude `(p.append q).IsPath`. This uses precisely the copied cut hypotheses and exact chosen path
objects, with no additional assumptions.

## Proof sources

- Source `solution.tex`, lines 33–64

## Proof dependencies

- `SimpleGraph.Walk.isPath_def` from `Mathlib.Combinatorics.SimpleGraph.Paths`
- `SimpleGraph.Walk.cons_tail_support` from `Mathlib.Combinatorics.SimpleGraph.Walk.Basic`
- `SimpleGraph.Walk.support_append` from `Mathlib.Combinatorics.SimpleGraph.Walk.Operations`
- `Main.TreePathSeparation::uniquePath_isPath` → `uniquePath_isPath` from
  `PositiveDefiniteTreeLattice.Main.TreePathSeparation.Theorems.uniquePath_isPath`
- `Main.TreePathSeparation::uniquePath_support_separated_by_cut` →
  `PositiveDefiniteTreeLattice.uniquePath_support_separated_by_cut` from
  `PositiveDefiniteTreeLattice.Main.TreePathSeparation.Theorems.uniquePath_support_separated_by_cut`
-/
theorem uniquePath_append_isPath_through_cut {V : Type*} [Fintype V]
    (G : SimpleGraph V) (hG : G.IsTree) (root parent c x : V)
    (hpc : G.Adj parent c)
    (hroot : (G.deleteEdges {s(parent, c)}).Reachable root parent)
    (hx : (G.deleteEdges {s(parent, c)}).Reachable c x) :
    ((uniquePath G hG root c).append (uniquePath G hG c x)).IsPath := by
  let p : G.Walk root c := uniquePath G hG root c
  let q : G.Walk c x := uniquePath G hG c x
  have hp : p.IsPath := by
    dsimp [p]
    exact uniquePath_isPath G hG root c
  have hq : q.IsPath := by
    dsimp [q]
    exact uniquePath_isPath G hG c x
  have hctail : c ∉ q.support.tail := by
    have hq_nodup := hq.support_nodup
    rw [← q.cons_tail_support] at hq_nodup
    exact (List.nodup_cons.mp hq_nodup).1
  change (p.append q).IsPath
  apply (SimpleGraph.Walk.isPath_def _).mpr
  rw [SimpleGraph.Walk.support_append, List.nodup_append]
  refine ⟨hp.support_nodup, hq.support_nodup.tail, ?_⟩
  intro y hyp w hyq hyw
  subst w
  have hyq_full : y ∈ q.support := List.mem_of_mem_tail hyq
  have hyc : y = c :=
    (PositiveDefiniteTreeLattice.uniquePath_support_separated_by_cut
      G hG root parent c x y hpc hroot hx).mp ⟨hyp, hyq_full⟩
  subst y
  exact hctail hyq
```

## Statement dependencies

- `Mathlib:Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected.SimpleGraph.Reachable`
- `Mathlib:Mathlib.Combinatorics.SimpleGraph.DeleteEdges.SimpleGraph.deleteEdges`
- `Mathlib:Mathlib.Combinatorics.SimpleGraph.Paths.SimpleGraph.Walk.IsPath`
- `Mathlib:Mathlib.Combinatorics.SimpleGraph.Walk.Operations.SimpleGraph.Walk.append`
- `current repo:Main.TreePathSeparation.uniquePath`

## Proof dependencies

- `Mathlib:Mathlib.Combinatorics.SimpleGraph.Paths.SimpleGraph.Walk.isPath_def`
- `Mathlib:Mathlib.Combinatorics.SimpleGraph.Walk.Basic.SimpleGraph.Walk.cons_tail_support`
- `Mathlib:Mathlib.Combinatorics.SimpleGraph.Walk.Operations.SimpleGraph.Walk.support_append`
- `current repo:Main.TreePathSeparation.uniquePath_isPath`
- `current repo:Main.TreePathSeparation.uniquePath_support_separated_by_cut`
