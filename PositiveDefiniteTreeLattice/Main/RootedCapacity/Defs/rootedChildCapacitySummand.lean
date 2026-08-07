-- lean-constellation: managed-imports-begin
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Prelude
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedCapacity
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildComponent
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildRoot
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildren
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `rootedChildCapacitySummand`

Let `V` be a finite decidable type, let `G : SimpleGraph V` have decidable adjacency, let `hG :
G.IsTree`, let `w : V → ℤ`, let `ρ : V`, and let `c : {c : V // c ∈ rootedChildren G hG ρ ρ}` be an
attached child of the root.  Put `C := rootedChildComponent G ρ c.1`.  Define
`rootedChildCapacitySummand G hG w ρ c : ℚ` to be the rooted capacity of the child-side rooted
weighted graph

`rootedCapacity C.toSimpleGraph (fun x : C => w (x : V)) (rootedChildRoot G ρ c.1)`.

The definition fixes internally one canonical finite-type and decidable-adjacency instance
convention for this component graph, so the displayed rational quantity is stable under later
finite-sum use.  It uses exactly the deleted-edge connected component rooted at the child, its
induced simple graph, the restriction of the original integer weight, and that child as its root.
It assumes neither admissibility nor positivity.

## Sources

- Source `solution.tex`, lines 47–68

## Statement dependencies

- `SimpleGraph.ConnectedComponent.instFinite` from
  `Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected`
- `SimpleGraph.ConnectedComponent.toSimpleGraph` from
  `Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected`
- `SimpleGraph.deleteEdges` from `Mathlib.Combinatorics.SimpleGraph.DeleteEdges`
- `Main.RootedCapacity::rootedCapacity` → `rootedCapacity` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedCapacity`
- `Main.RootedCapacity::rootedChildComponent` → `rootedChildComponent` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildComponent`
- `Main.RootedCapacity::rootedChildRoot` → `rootedChildRoot` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildRoot`
- `Main.RootedCapacity::rootedChildren` → `rootedChildren` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildren`
-/
noncomputable def rootedChildCapacitySummand {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.IsTree) (w : V → ℤ) (ρ : V)
    (c : {c : V // c ∈ rootedChildren G hG ρ ρ}) : ℚ :=
  let C := rootedChildComponent G ρ c.1
  letI : Fintype C := Fintype.ofFinite C
  letI : DecidableRel C.toSimpleGraph.Adj := by
    intro x y
    change Decidable ((G.deleteEdges {s(ρ, c.1)}).Adj (x : V) (y : V))
    infer_instance
  rootedCapacity C.toSimpleGraph (fun x : C => w (x : V)) (rootedChildRoot G ρ c.1)
