[← Public API](../PUBLIC_API.md) · [Public boundaries](../PUBLIC_BOUNDARIES.md) · [Complete graph](../DECLARATION_GRAPH.md)

# `rootedChildCapacitySum`

The rooted capacity is the reciprocal of the root weight minus the sum of child-component capacities.

- Kind: `definition`
- Node: `Main.RootedCapacity`
- Module: `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildCapacitySum`
- State: `declared`
- Revision status: `committed`
- Repository completion: `graph_proved`
- Compatibility `formal_code`: final statement projection

## Statement NL

Let `V` be a finite decidable type, let `G : SimpleGraph V` have decidable adjacency, let `hG : G.IsTree`, let `w : V → ℤ`, and let `ρ : V`.  Define the rational child-capacity aggregate `rootedChildCapacitySum G hG w ρ : ℚ` by the finite sum over the attached root-child subtype:

`Finset.univ.sum (fun c : {c : V // c ∈ rootedChildren G hG ρ ρ} => rootedChildCapacitySummand G hG w ρ c)`.

Equivalently, this is `∑ c : {c : V // c ∈ rootedChildren G hG ρ ρ}, rootedChildCapacitySummand G hG w ρ c`.  Thus it is exactly the sum of the rational capacities of the deleted-edge child components, with each component's restricted integer weight and child root supplied by the public summand definition.  The aggregate directly invokes that named summand and introduces no component-local instances or unfolding of its body.  It assumes neither admissibility nor positivity.

## Statement Formal

```lean
-- lean-constellation: managed-imports-begin
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Prelude
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Data.Fintype.Defs
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildCapacitySummand
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildren
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `rootedChildCapacitySum`

Let `V` be a finite decidable type, let `G : SimpleGraph V` have decidable adjacency, let `hG :
G.IsTree`, let `w : V → ℤ`, and let `ρ : V`.  Define the rational child-capacity aggregate
`rootedChildCapacitySum G hG w ρ : ℚ` by the finite sum over the attached root-child subtype:

`Finset.univ.sum (fun c : {c : V // c ∈ rootedChildren G hG ρ ρ} => rootedChildCapacitySummand G hG
w ρ c)`.

Equivalently, this is `∑ c : {c : V // c ∈ rootedChildren G hG ρ ρ}, rootedChildCapacitySummand G hG
w ρ c`.  Thus it is exactly the sum of the rational capacities of the deleted-edge child components,
with each component's restricted integer weight and child root supplied by the public summand
definition.  The aggregate directly invokes that named summand and introduces no component-local
instances or unfolding of its body.  It assumes neither admissibility nor positivity.

## Sources

- Source `solution.tex`, lines 47–52

## Statement dependencies

- `Finset.sum` from `Mathlib.Algebra.BigOperators.Group.Finset.Defs`
- `Finset.univ` from `Mathlib.Data.Fintype.Defs`
- `Main.RootedCapacity::rootedChildCapacitySummand` → `rootedChildCapacitySummand` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildCapacitySummand`
- `Main.RootedCapacity::rootedChildren` → `rootedChildren` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildren`
-/
noncomputable def rootedChildCapacitySum {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.IsTree) (w : V → ℤ) (ρ : V) : ℚ :=
  Finset.univ.sum fun c : {c : V // c ∈ rootedChildren G hG ρ ρ} =>
    rootedChildCapacitySummand G hG w ρ c
```

## Proof NL

Not recorded.

## Proof Formal

Not recorded.

## Statement dependencies

- `Mathlib:Mathlib.Algebra.BigOperators.Group.Finset.Defs.Finset.sum`
- `Mathlib:Mathlib.Data.Fintype.Defs.Finset.univ`
- `current repo:Main.RootedCapacity.rootedChildCapacitySummand`
- `current repo:Main.RootedCapacity.rootedChildren`

## Sources

- `solution.tex:47-52`
