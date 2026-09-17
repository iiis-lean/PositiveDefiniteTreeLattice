[← Public API](../PUBLIC_API.md) · [Public boundaries](../PUBLIC_BOUNDARIES.md) · [Complete graph](../DECLARATION_GRAPH.md)

# `rootedChildCapacitySum_lt_card_of_forall_lt_one`

Exact per-child capacity bounds strictly bound the aggregate child-capacity sum by the number of root children.

- Kind: `theorem`
- Node: `Main.RootedCapacity`
- Module: `PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.rootedChildCapacitySum_lt_card_of_forall_lt_one`
- State: `proved`
- Revision status: `committed`
- Repository completion: `graph_proved`
- Compatibility `formal_code`: final proof projection

## Statement NL

Let `V` be a finite decidable type, let `G : SimpleGraph V` have decidable adjacency, let `hG : G.IsTree`, let `w : V → ℤ`, and let `ρ : V`.  Put `S := rootedChildren G hG ρ ρ`.  If `S.Nonempty` and every attached child `c : {c : V // c ∈ S}` satisfies

`rootedChildCapacitySummand G hG w ρ c < 1`,

then

`rootedChildCapacitySum G hG w ρ < (S.card : ℚ)`.

This is the strict rational bound for the sum of the capacities of the root's child components.  It retains the attached child subtype and the cardinality of exactly `S`, and assumes neither admissibility nor positivity.

## Statement Formal

```lean
-- lean-constellation: managed-imports-begin
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Prelude
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Empty
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildCapacitySum
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildCapacitySummand
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildren
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `rootedChildCapacitySum_lt_card_of_forall_lt_one`

Let `V` be a finite decidable type, let `G : SimpleGraph V` have decidable adjacency, let `hG :
G.IsTree`, let `w : V → ℤ`, and let `ρ : V`.  Put `S := rootedChildren G hG ρ ρ`.  If `S.Nonempty`
and every attached child `c : {c : V // c ∈ S}` satisfies

`rootedChildCapacitySummand G hG w ρ c < 1`,

then

`rootedChildCapacitySum G hG w ρ < (S.card : ℚ)`.

This is the strict rational bound for the sum of the capacities of the root's child components.  It
retains the attached child subtype and the cardinality of exactly `S`, and assumes neither
admissibility nor positivity.

## Sources

- Source `solution.tex`, lines 74–80

## Statement dependencies

- `Finset.card` from `Mathlib.Data.Finset.Card`
- `Finset.Nonempty` from `Mathlib.Data.Finset.Empty`
- `Main.RootedCapacity::rootedChildCapacitySum` → `rootedChildCapacitySum` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildCapacitySum`
- `Main.RootedCapacity::rootedChildCapacitySummand` → `rootedChildCapacitySummand` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildCapacitySummand`
- `Main.RootedCapacity::rootedChildren` → `rootedChildren` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildren`
-/
theorem rootedChildCapacitySum_lt_card_of_forall_lt_one {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.IsTree) (w : V → ℤ) (ρ : V)
    (hS : (rootedChildren G hG ρ ρ).Nonempty)
    (hcapacity : ∀ c : {c : V // c ∈ rootedChildren G hG ρ ρ},
      rootedChildCapacitySummand G hG w ρ c < 1) :
    rootedChildCapacitySum G hG w ρ < ((rootedChildren G hG ρ ρ).card : ℚ) := by
  sorry
```

## Proof NL

Let S := rootedChildren G hG ρ ρ and let I := {c : V // c ∈ S}. Do not unfold the attached-child summand. Unfold only rootedChildCapacitySum, so the left-hand side is Finset.univ.sum of the same function c ↦ rootedChildCapacitySummand G hG w ρ c on I.

Use hS to choose an element of S and hence prove that (Finset.univ : Finset I) is nonempty. Apply Finset.sum_lt_sum_of_nonempty to this univ finset, comparing the summand function with the constant function c ↦ (1 : ℚ). Its pointwise strict hypothesis is exactly hcapacity c.

The resulting right-hand side is the sum of 1 over all attached children. Simplify it to (Fintype.card I : ℚ), then use Fintype.card_coe S to identify Fintype.card I with S.card. This yields exactly rootedChildCapacitySum G hG w ρ < (S.card : ℚ). No admissibility or positivity fact is used; no component instance, raw-child conversion, or aggregate-attachment theorem is introduced.

## Proof Formal

```lean
-- lean-constellation: managed-imports-begin
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Prelude
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Empty
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Defs
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildCapacitySum
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildCapacitySummand
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildren
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `rootedChildCapacitySum_lt_card_of_forall_lt_one`

Let `V` be a finite decidable type, let `G : SimpleGraph V` have decidable adjacency, let `hG :
G.IsTree`, let `w : V → ℤ`, and let `ρ : V`.  Put `S := rootedChildren G hG ρ ρ`.  If `S.Nonempty`
and every attached child `c : {c : V // c ∈ S}` satisfies

`rootedChildCapacitySummand G hG w ρ c < 1`,

then

`rootedChildCapacitySum G hG w ρ < (S.card : ℚ)`.

This is the strict rational bound for the sum of the capacities of the root's child components.  It
retains the attached child subtype and the cardinality of exactly `S`, and assumes neither
admissibility nor positivity.

## Sources

- Source `solution.tex`, lines 74–80

## Statement dependencies

- `Finset.card` from `Mathlib.Data.Finset.Card`
- `Finset.Nonempty` from `Mathlib.Data.Finset.Empty`
- `Main.RootedCapacity::rootedChildCapacitySum` → `rootedChildCapacitySum` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildCapacitySum`
- `Main.RootedCapacity::rootedChildCapacitySummand` → `rootedChildCapacitySummand` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildCapacitySummand`
- `Main.RootedCapacity::rootedChildren` → `rootedChildren` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildren`

## Proof outline

Let S := rootedChildren G hG ρ ρ and let I := {c : V // c ∈ S}. Do not unfold the attached-child
summand. Unfold only rootedChildCapacitySum, so the left-hand side is Finset.univ.sum of the same
function c ↦ rootedChildCapacitySummand G hG w ρ c on I.

Use hS to choose an element of S and hence prove that (Finset.univ : Finset I) is nonempty. Apply
Finset.sum_lt_sum_of_nonempty to this univ finset, comparing the summand function with the constant
function c ↦ (1 : ℚ). Its pointwise strict hypothesis is exactly hcapacity c.

The resulting right-hand side is the sum of 1 over all attached children. Simplify it to
(Fintype.card I : ℚ), then use Fintype.card_coe S to identify Fintype.card I with S.card. This
yields exactly rootedChildCapacitySum G hG w ρ < (S.card : ℚ). No admissibility or positivity fact
is used; no component instance, raw-child conversion, or aggregate-attachment theorem is introduced.

## Proof sources

- Source `solution.tex`, lines 74–80

## Proof dependencies

- `Finset.sum_lt_sum_of_nonempty` from `Mathlib.Algebra.Order.BigOperators.Group.Finset`
- `Fintype.card_coe` from `Mathlib.Data.Fintype.Card`
- `Finset.mem_univ` from `Mathlib.Data.Fintype.Defs`
- `Main.RootedCapacity::rootedChildCapacitySum` → `rootedChildCapacitySum` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildCapacitySum`
- `Main.RootedCapacity::rootedChildCapacitySummand` → `rootedChildCapacitySummand` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildCapacitySummand`
- `Main.RootedCapacity::rootedChildren` → `rootedChildren` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildren`
-/
theorem rootedChildCapacitySum_lt_card_of_forall_lt_one {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.IsTree) (w : V → ℤ) (ρ : V)
    (hS : (rootedChildren G hG ρ ρ).Nonempty)
    (hcapacity : ∀ c : {c : V // c ∈ rootedChildren G hG ρ ρ},
      rootedChildCapacitySummand G hG w ρ c < 1) :
    rootedChildCapacitySum G hG w ρ < ((rootedChildren G hG ρ ρ).card : ℚ) := by
  classical
  have huniv : (Finset.univ : Finset {c : V // c ∈ rootedChildren G hG ρ ρ}).Nonempty := by
    rcases hS with ⟨c, hc⟩
    exact ⟨⟨c, hc⟩, Finset.mem_univ _⟩
  have hsum :
      (∑ c : {c : V // c ∈ rootedChildren G hG ρ ρ},
        rootedChildCapacitySummand G hG w ρ c) <
      ∑ _ : {c : V // c ∈ rootedChildren G hG ρ ρ}, (1 : ℚ) :=
    Finset.sum_lt_sum_of_nonempty huniv (by
      intro c hc
      exact hcapacity c)
  unfold rootedChildCapacitySum
  simpa [Fintype.card_coe] using hsum
```

## Statement dependencies

- `Mathlib:Mathlib.Data.Finset.Card.Finset.card`
- `Mathlib:Mathlib.Data.Finset.Empty.Finset.Nonempty`
- `current repo:Main.RootedCapacity.rootedChildCapacitySum`
- `current repo:Main.RootedCapacity.rootedChildCapacitySummand`
- `current repo:Main.RootedCapacity.rootedChildren`

## Proof dependencies

- `Mathlib:Mathlib.Algebra.Order.BigOperators.Group.Finset.Finset.sum_lt_sum_of_nonempty`
- `Mathlib:Mathlib.Data.Fintype.Card.Fintype.card_coe`
- `Mathlib:Mathlib.Data.Fintype.Defs.Finset.mem_univ`
- `current repo:Main.RootedCapacity.rootedChildCapacitySum`
- `current repo:Main.RootedCapacity.rootedChildCapacitySummand`
- `current repo:Main.RootedCapacity.rootedChildren`

## Sources

- `solution.tex:74-80`
