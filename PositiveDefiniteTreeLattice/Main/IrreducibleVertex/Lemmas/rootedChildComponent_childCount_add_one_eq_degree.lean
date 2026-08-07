-- lean-constellation: managed-imports-begin
import PositiveDefiniteTreeLattice.Main.IrreducibleVertex.Prelude
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Fintype.EquivFin
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

noncomputable local instance rootedChildComponentFintype {V : Type*} [Fintype V]
    (G : SimpleGraph V) (v c : V) : Fintype (rootedChildComponent G v c) :=
  Fintype.ofFinite _

noncomputable local instance rootedChildComponentDecidableAdj {V : Type*} (G : SimpleGraph V)
    (v c : V) : DecidableRel (rootedChildComponent G v c).toSimpleGraph.Adj :=
  by
    classical
    infer_instance

/--
# lean-constellation target: `rootedChildComponent_childCount_add_one_eq_degree`

Let `V` be a finite type with decidable equality, let `G : SimpleGraph V` have decidable adjacency
and satisfy `h_tree : G.IsTree`, and let `v c : V` with `hc : c ∈ rootedChildren G h_tree v v`. For
every `x : rootedChildComponent G v c`, `rootedChildCount (rootedChildComponent G v c).toSimpleGraph
(rootedChildComponent_isTree G v c h_tree) (rootedChildRoot G v c) x + 1 = G.degree (x : V)` as
natural numbers.

## Sources

- Source `solution.tex`, lines 199–203

## Statement dependencies

- `SimpleGraph.IsTree` from `Mathlib.Combinatorics.SimpleGraph.Acyclic`
- `SimpleGraph.ConnectedComponent.toSimpleGraph` from
  `Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected`
- `SimpleGraph.degree` from `Mathlib.Combinatorics.SimpleGraph.Finite`
- `Main.RootedCapacity::rootedChildComponent` → `rootedChildComponent` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildComponent`
- `Main.RootedCapacity::rootedChildComponent_isTree` → `rootedChildComponent_isTree` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.rootedChildComponent_isTree`
- `Main.RootedCapacity::rootedChildCount` → `rootedChildCount` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildCount`
- `Main.RootedCapacity::rootedChildRoot` → `rootedChildRoot` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildRoot`
- `Main.RootedCapacity::rootedChildren` → `rootedChildren` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildren`

## Proof outline

First rewrite the component child count with the accepted restriction theorem
`rootedChildCount_rootedChildComponent G h_tree v v c hc x`. It reduces the goal to
`rootedChildCount G h_tree v (x : V) + 1 = G.degree (x : V)`.

Extract `G.Adj v c` from `hc` by unfolding membership in `rootedChildren`. Then
`rootedChildComponent_parent_not_mem G v c h_tree hvc x` proves `(x : V) ≠ v`. Choose the unique
simple path from `v` to `(x : V)` using `SimpleGraph.IsTree.existsUnique_path`; since the endpoints
differ, take its final predecessor `p`, so `G.Adj p (x : V)`.

Prove the finite-neighbor partition
`G.neighborFinset (x : V) = insert p (rootedChildren G h_tree v (x : V))`.
The predecessor is not a rooted child: otherwise the unique paths to `p` obtained by truncating the
path to `x` and by the child condition disagree. Conversely, every neighbor `y` distinct from `p` is
a rooted child: append the edge `(x,y)` to the unique path from `v` to `x`; acyclicity shows this
append is a simple path, and uniqueness identifies it with the canonical path to `y`, exactly the
membership criterion for `rootedChildren`.

Take cardinalities of this disjoint insert. Unfold `rootedChildCount` and the finite-graph degree
definition (`degree` is the card of `neighborFinset`) to obtain the required natural-number
equality. This is specialized to the deleted component and keeps the ambient degree unchanged.

## Proof sources

- Source `solution.tex`, lines 199–203

## Proof dependencies

- `Finset.mem_filter` from `Mathlib.Data.Finset.Filter`
- `Fintype.ofFinite` from `Mathlib.Data.Fintype.EquivFin`
- `Main.RootedCapacity::rootedChildComponent_parent_not_mem` → `rootedChildComponent_parent_not_mem`
  from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.rootedChildComponent_parent_not_mem`
- `Main.RootedCapacity::rootedChildCount_add_one_eq_degree` →
  `PositiveDefiniteTreeLattice.rootedChildCount_add_one_eq_degree` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.rootedChildCount_add_one_eq_degree`
- `Main.RootedCapacity::rootedChildCount_rootedChildComponent` →
  `rootedChildCount_rootedChildComponent` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.rootedChildCount_rootedChildComponent`
- `Main.RootedCapacity::rootedChildren` → `rootedChildren` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildren`
-/
theorem PositiveDefiniteTreeLattice.rootedChildComponent_childCount_add_one_eq_degree
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (h_tree : G.IsTree) (v c : V) (hc : c ∈ rootedChildren G h_tree v v)
    (x : rootedChildComponent G v c) :
    rootedChildCount (rootedChildComponent G v c).toSimpleGraph
        (rootedChildComponent_isTree G v c h_tree) (rootedChildRoot G v c) x + 1 =
      G.degree (x : V) := by
  classical
  have hvc : G.Adj v c := by
    rw [rootedChildren, Finset.mem_filter] at hc
    exact hc.2.choose
  have hxv : (x : V) ≠ v :=
    rootedChildComponent_parent_not_mem G v c h_tree hvc x
  calc
    rootedChildCount (rootedChildComponent G v c).toSimpleGraph
          (rootedChildComponent_isTree G v c h_tree) (rootedChildRoot G v c) x +
        1 = rootedChildCount G h_tree v (x : V) + 1 := by
      congr 1
      simpa [rootedChildCount, rootedChildren] using
        (rootedChildCount_rootedChildComponent G h_tree v v c hc x)
    _ = G.degree (x : V) := rootedChildCount_add_one_eq_degree G h_tree v (x : V) hxv
