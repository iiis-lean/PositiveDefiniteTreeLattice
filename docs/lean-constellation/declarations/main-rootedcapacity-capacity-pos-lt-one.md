[← Public API](../PUBLIC_API.md) · [Public boundaries](../PUBLIC_BOUNDARIES.md)

# `capacity_pos_lt_one`

The capacity of an admissible rooted weighted tree lies strictly between zero and one.

- Kind: `theorem`
- Node: `Main.RootedCapacity`
- Module: `PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.capacity_pos_lt_one`
- State: `proved`
- Revision status: `committed`
- Repository completion: `graph_proved`
- Formal code: final proof projection

## Lean code

```lean
-- lean-constellation: managed-imports-begin
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Prelude
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Nat.Init
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.IsAdmissibleRootedTree
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedCapacity
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildCapacitySum
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildComponent
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildCount
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildRoot
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildren
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.IsAdmissibleRootedTree_rootedChildComponent
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.rootedCapacity_lt_one_of_card_le
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.rootedCapacity_pos
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.rootedCapacity_recursion
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.rootedChildComponent_card_lt
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `capacity_pos_lt_one`

In namespace `PositiveDefiniteTreeLattice`, declare the public theorem
`PositiveDefiniteTreeLattice.capacity_pos_lt_one`.

For every finite decidable vertex type, graph `G` with decidable adjacency, integer weight `w`, root
`ρ`, and admissibility witness `hAdm : IsAdmissibleRootedTree G w ρ`, the existing rational capacity
satisfies exactly
```
0 < rootedCapacity G w ρ ∧ rootedCapacity G w ρ < 1.
```

This preserves the existing rational total-inverse definition of `rootedCapacity` and introduces no
supplementary tree, positivity, denominator, weight, or component assumptions. The conjunction has
the stated lower-then-upper order: its lower bound is the existing `rootedCapacity_pos`, while its
upper bound is the source’s strict child-subtree induction together with the existing capacity
recursion.

## Sources

- Source `solution.tex`, lines 47–82

## Statement dependencies

- `Main.RootedCapacity::IsAdmissibleRootedTree` → `IsAdmissibleRootedTree` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.IsAdmissibleRootedTree`
- `Main.RootedCapacity::rootedCapacity` → `rootedCapacity` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedCapacity`

## Proof outline

Work classically.  The lower half of the conjunction is exactly `rootedCapacity_pos G w ρ hAdm`.
For the upper half, prove a stronger cardinal-indexed predicate by `Nat.strong_induction_on`: for
each natural `n`, it asserts the `< 1` conclusion for every finite decidable rooted
graph/weight/root/admissibility datum whose ambient vertex type has Fintype cardinality `n`.
Quantifying over the whole datum is essential, since the induction hypothesis must be instantiated
on the dependent child-component subtype.

Fix one such datum, retain the original `hAdm`, and destruct a copy as `⟨hG, hPos, hTwo, hCount⟩`.
Put `S := rootedChildren G hG ρ ρ`.  For every `c ∈ S`, install the standard local `Fintype` and
decidable-adjacency instances for `C := rootedChildComponent G ρ c`.  The proved
`rootedChildComponent_card_lt G hG ρ ρ c hc` gives `Fintype.card C < Fintype.card V`.  The proved
`IsAdmissibleRootedTree_rootedChildComponent G w ρ ρ c hG hc hAdm` supplies the child admissibility
witness.  Apply the strong induction hypothesis at this smaller cardinality and child data to obtain
`rootedCapacity C.toSimpleGraph (fun x : C => w (x : V)) (rootedChildRoot G ρ c) < 1`.

Split on `S.Nonempty`.  If it is nonempty, unfold `rootedChildCapacitySum` only to identify its
summands with these child capacities (aligning the finite and decidable-adjacency instances by proof
irrelevance).  `Finset.sum_lt_sum_of_nonempty` applied pointwise to the child bounds yields
`rootedChildCapacitySum G hG w ρ < (S.card : ℚ)`.
Unfold `rootedChildCount` in `hCount ρ` and cast its integer inequality to `ℚ`, obtaining `(S.card :
ℚ) + 1 ≤ w ρ`.  Therefore the recursion denominator
`(w ρ : ℚ) - rootedChildCapacitySum G hG w ρ` is strictly greater than `1` (and hence positive).
Rewrite with `rootedCapacity_recursion G hG w ρ hAdm`; `div_lt_one` converts the denominator
inequality into the desired reciprocal bound.

If `S` is empty, `rootedChildCapacitySum` is zero by its finite-sum definition.  The admissibility
clause `hTwo ρ : (2 : ℤ) ≤ w ρ`, after casting to `ℚ`, gives `1 < (w ρ : ℚ)`.  The same recursion
rewrite and `div_lt_one` prove the upper bound.  This is the formal child-free/base branch of the
source induction.  No additional admissibility, denominator, or replacement-capacity assumption is
introduced.

## Proof sources

- Source `solution.tex`, lines 47–82

## Proof dependencies

- `Finset.sum_lt_sum_of_nonempty` from `Mathlib.Algebra.Order.BigOperators.Group.Finset`
- `div_lt_one` from `Mathlib.Algebra.Order.Field.Basic`
- `Nat.strong_induction_on` from `Mathlib.Data.Nat.Init`
- `Main.RootedCapacity::IsAdmissibleRootedTree` → `IsAdmissibleRootedTree` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.IsAdmissibleRootedTree`
- `Main.RootedCapacity::IsAdmissibleRootedTree_rootedChildComponent` →
  `IsAdmissibleRootedTree_rootedChildComponent` from `PositiveDefiniteTreeLattice.Main.RootedCapacit
  y.Theorems.IsAdmissibleRootedTree_rootedChildComponent`
- `Main.RootedCapacity::rootedCapacity` → `rootedCapacity` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedCapacity`
- `Main.RootedCapacity::rootedCapacity_lt_one_of_card_le` → `rootedCapacity_lt_one_of_card_le` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.rootedCapacity_lt_one_of_card_le`
- `Main.RootedCapacity::rootedCapacity_pos` → `rootedCapacity_pos` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.rootedCapacity_pos`
- `Main.RootedCapacity::rootedCapacity_recursion` → `rootedCapacity_recursion` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.rootedCapacity_recursion`
- `Main.RootedCapacity::rootedChildCapacitySum` → `rootedChildCapacitySum` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildCapacitySum`
- `Main.RootedCapacity::rootedChildComponent` → `rootedChildComponent` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildComponent`
- `Main.RootedCapacity::rootedChildComponent_card_lt` → `rootedChildComponent_card_lt` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.rootedChildComponent_card_lt`
- `Main.RootedCapacity::rootedChildCount` → `rootedChildCount` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildCount`
- `Main.RootedCapacity::rootedChildRoot` → `rootedChildRoot` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildRoot`
- `Main.RootedCapacity::rootedChildren` → `rootedChildren` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildren`
-/
theorem PositiveDefiniteTreeLattice.capacity_pos_lt_one {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (w : V → ℤ) (ρ : V)
    (hAdm : IsAdmissibleRootedTree G w ρ) :
    0 < rootedCapacity G w ρ ∧ rootedCapacity G w ρ < 1 := by
  constructor
  · exact rootedCapacity_pos G w ρ hAdm
  · exact rootedCapacity_lt_one_of_card_le (Fintype.card V) G w ρ hAdm le_rfl
```

## Statement dependencies

- `current repo:Main.RootedCapacity.IsAdmissibleRootedTree`
- `current repo:Main.RootedCapacity.rootedCapacity`

## Proof dependencies

- `Mathlib:Mathlib.Algebra.Order.BigOperators.Group.Finset.Finset.sum_lt_sum_of_nonempty`
- `Mathlib:Mathlib.Algebra.Order.Field.Basic.div_lt_one`
- `Mathlib:Mathlib.Data.Nat.Init.Nat.strong_induction_on`
- `current repo:Main.RootedCapacity.IsAdmissibleRootedTree`
- `current repo:Main.RootedCapacity.IsAdmissibleRootedTree_rootedChildComponent`
- `current repo:Main.RootedCapacity.rootedCapacity`
- `current repo:Main.RootedCapacity.rootedCapacity_lt_one_of_card_le`
- `current repo:Main.RootedCapacity.rootedCapacity_pos`
- `current repo:Main.RootedCapacity.rootedCapacity_recursion`
- `current repo:Main.RootedCapacity.rootedChildCapacitySum`
- `current repo:Main.RootedCapacity.rootedChildComponent`
- `current repo:Main.RootedCapacity.rootedChildComponent_card_lt`
- `current repo:Main.RootedCapacity.rootedChildCount`
- `current repo:Main.RootedCapacity.rootedChildRoot`
- `current repo:Main.RootedCapacity.rootedChildren`

## Sources

- `solution.tex:47-82`
