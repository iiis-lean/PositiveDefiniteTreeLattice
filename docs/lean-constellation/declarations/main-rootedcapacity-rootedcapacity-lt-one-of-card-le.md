[← Public API](../PUBLIC_API.md) · [Public boundaries](../PUBLIC_BOUNDARIES.md) · [Complete graph](../DECLARATION_GRAPH.md)

# `rootedCapacity_lt_one_of_card_le`

An admissible rooted tree whose vertex cardinality is bounded by n has capacity strictly below one.

- Kind: `theorem`
- Node: `Main.RootedCapacity`
- Module: `PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.rootedCapacity_lt_one_of_card_le`
- State: `proved`
- Revision status: `committed`
- Repository completion: `graph_proved`
- Compatibility `formal_code`: final proof projection

## Statement NL

For every natural number `n`, every finite decidable vertex type, graph `G` with decidable adjacency, integer weight `w`, root `ρ`, and admissibility witness `hAdm : IsAdmissibleRootedTree G w ρ`, if
```
Fintype.card V ≤ n,
```
then the existing rational capacity satisfies
```
rootedCapacity G w ρ < 1.
```

The theorem is private and is indexed by the explicit natural upper bound `n`, with all rooted-tree data universally quantified beneath that index. It preserves the existing component, root, weight, capacity, and rational total-inverse semantics, adds no stronger admissibility or denominator hypothesis, and does not invoke the public theorem `capacity_pos_lt_one`. It is oriented to provide precisely the upper half of that public interface after ordinary induction on `n`.

## Statement Formal

```lean
-- lean-constellation: managed-imports-begin
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Prelude
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.IsAdmissibleRootedTree
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedCapacity
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `rootedCapacity_lt_one_of_card_le`

For every natural number `n`, every finite decidable vertex type, graph `G` with decidable
adjacency, integer weight `w`, root `ρ`, and admissibility witness `hAdm : IsAdmissibleRootedTree G
w ρ`, if
```
Fintype.card V ≤ n,
```
then the existing rational capacity satisfies
```
rootedCapacity G w ρ < 1.
```

The theorem is private and is indexed by the explicit natural upper bound `n`, with all rooted-tree
data universally quantified beneath that index. It preserves the existing component, root, weight,
capacity, and rational total-inverse semantics, adds no stronger admissibility or denominator
hypothesis, and does not invoke the public theorem `capacity_pos_lt_one`. It is oriented to provide
precisely the upper half of that public interface after ordinary induction on `n`.

## Sources

- Source `solution.tex`, lines 74–81

## Statement dependencies

- `Main.RootedCapacity::IsAdmissibleRootedTree` → `IsAdmissibleRootedTree` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.IsAdmissibleRootedTree`
- `Main.RootedCapacity::rootedCapacity` → `rootedCapacity` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedCapacity`
-/

theorem rootedCapacity_lt_one_of_card_le (n : ℕ) {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (w : V → ℤ) (ρ : V)
    (hAdm : IsAdmissibleRootedTree G w ρ) (hcard : Fintype.card V ≤ n) :
    rootedCapacity G w ρ < 1 := by
  sorry
```

## Proof NL

Prove the statement by ordinary induction on n, generalizing the finite vertex type and all rooted data. In the n = 0 case, the explicit root ρ gives Nonempty V, hence Fintype.card V > 0; this contradicts hcard : Fintype.card V ≤ 0.

For the successor step, destruct hAdm as ⟨hG, hPos, hTwo, hRootWeight⟩, retaining hG to index the root-child finset S := rootedChildren G hG ρ ρ. For each attached child c : {c : V // c ∈ S}, use rootedChildComponent_card_lt G hG ρ ρ c.1 c.2 together with hcard : Fintype.card V ≤ n + 1 to obtain Fintype.card (rootedChildComponent G ρ c.1) ≤ n by elementary Nat successor arithmetic. Apply the induction hypothesis to this child component, its induced graph, the restricted weight, and rootedChildRoot G ρ c.1. Its admissibility input is IsAdmissibleRootedTree_rootedChildComponent G w ρ ρ c.1 hG c.2 hAdm.

At this one fixed c only, unfold rootedChildCapacitySummand. Its built-in deleted-edge component, restricted weight, child root, and canonical local instances make the induction-hypothesis conclusion exactly rootedChildCapacitySummand G hG w ρ c < 1. Do not construct any new raw-child instances or normalize the aggregate manually. This yields the required pointwise named-summand bound for every c.

Split on S.Nonempty. In the nonempty branch, apply rootedChildCapacitySum_lt_card_of_forall_lt_one G hG w ρ hS to the pointwise bounds, obtaining A := rootedChildCapacitySum G hG w ρ < (S.card : ℚ). In the empty branch, use Finset.not_nonempty_iff_eq_empty to rewrite S to ∅, then unfold only rootedChildCapacitySum and simplify its Finset.univ sum to obtain A = 0.

In the nonempty branch, unfold rootedChildCount only in the root-weight field hRootWeight ρ, so it gives ((S.card : ℤ) + 1) ≤ w ρ. Cast this inequality to ℚ and combine it with A < (S.card : ℚ) to show 1 < (w ρ : ℚ) - A. In the empty branch, the hTwo ρ bound gives (2 : ℚ) ≤ w ρ; together with A = 0 it again gives 1 < (w ρ : ℚ) - A. In either case let d := (w ρ : ℚ) - rootedChildCapacitySum G hG w ρ, retain 0 < d from 1 < d, and rewrite rootedCapacity using rootedCapacity_recursion G hG w ρ hAdm. Invoke rootedCapacity_pos G w ρ hAdm for the positive-capacity order context, then apply div_lt_one₀ to 0 < d and 1 < d to conclude 1 / d < 1. This never uses capacity_pos_lt_one.

## Proof Formal

```lean
-- lean-constellation: managed-imports-begin
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Prelude
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.Ring.Cast
import Mathlib.Data.Finset.Empty
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.IsAdmissibleRootedTree
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedCapacity
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildCapacitySum
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildCapacitySummand
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildComponent
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildCount
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildRoot
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildren
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.IsAdmissibleRootedTree_rootedChildComponent
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.rootedCapacity_pos
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.rootedCapacity_recursion
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.rootedChildCapacitySum_lt_card_of_forall_lt_one
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.rootedChildComponent_card_lt
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `rootedCapacity_lt_one_of_card_le`

For every natural number `n`, every finite decidable vertex type, graph `G` with decidable
adjacency, integer weight `w`, root `ρ`, and admissibility witness `hAdm : IsAdmissibleRootedTree G
w ρ`, if
```
Fintype.card V ≤ n,
```
then the existing rational capacity satisfies
```
rootedCapacity G w ρ < 1.
```

The theorem is private and is indexed by the explicit natural upper bound `n`, with all rooted-tree
data universally quantified beneath that index. It preserves the existing component, root, weight,
capacity, and rational total-inverse semantics, adds no stronger admissibility or denominator
hypothesis, and does not invoke the public theorem `capacity_pos_lt_one`. It is oriented to provide
precisely the upper half of that public interface after ordinary induction on `n`.

## Sources

- Source `solution.tex`, lines 74–81

## Statement dependencies

- `Main.RootedCapacity::IsAdmissibleRootedTree` → `IsAdmissibleRootedTree` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.IsAdmissibleRootedTree`
- `Main.RootedCapacity::rootedCapacity` → `rootedCapacity` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedCapacity`

## Proof outline

Prove the statement by ordinary induction on n, generalizing the finite vertex type and all rooted
data. In the n = 0 case, the explicit root ρ gives Nonempty V, hence Fintype.card V > 0; this
contradicts hcard : Fintype.card V ≤ 0.

For the successor step, destruct hAdm as ⟨hG, hPos, hTwo, hRootWeight⟩, retaining hG to index the
root-child finset S := rootedChildren G hG ρ ρ. For each attached child c : {c : V // c ∈ S}, use
rootedChildComponent_card_lt G hG ρ ρ c.1 c.2 together with hcard : Fintype.card V ≤ n + 1 to obtain
Fintype.card (rootedChildComponent G ρ c.1) ≤ n by elementary Nat successor arithmetic. Apply the
induction hypothesis to this child component, its induced graph, the restricted weight, and
rootedChildRoot G ρ c.1. Its admissibility input is IsAdmissibleRootedTree_rootedChildComponent G w
ρ ρ c.1 hG c.2 hAdm.

At this one fixed c only, unfold rootedChildCapacitySummand. Its built-in deleted-edge component,
restricted weight, child root, and canonical local instances make the induction-hypothesis
conclusion exactly rootedChildCapacitySummand G hG w ρ c < 1. Do not construct any new raw-child
instances or normalize the aggregate manually. This yields the required pointwise named-summand
bound for every c.

Split on S.Nonempty. In the nonempty branch, apply rootedChildCapacitySum_lt_card_of_forall_lt_one G
hG w ρ hS to the pointwise bounds, obtaining A := rootedChildCapacitySum G hG w ρ < (S.card : ℚ). In
the empty branch, use Finset.not_nonempty_iff_eq_empty to rewrite S to ∅, then unfold only
rootedChildCapacitySum and simplify its Finset.univ sum to obtain A = 0.

In the nonempty branch, unfold rootedChildCount only in the root-weight field hRootWeight ρ, so it
gives ((S.card : ℤ) + 1) ≤ w ρ. Cast this inequality to ℚ and combine it with A < (S.card : ℚ) to
show 1 < (w ρ : ℚ) - A. In the empty branch, the hTwo ρ bound gives (2 : ℚ) ≤ w ρ; together with A =
0 it again gives 1 < (w ρ : ℚ) - A. In either case let d := (w ρ : ℚ) - rootedChildCapacitySum G hG
w ρ, retain 0 < d from 1 < d, and rewrite rootedCapacity using rootedCapacity_recursion G hG w ρ
hAdm. Invoke rootedCapacity_pos G w ρ hAdm for the positive-capacity order context, then apply
div_lt_one₀ to 0 < d and 1 < d to conclude 1 / d < 1. This never uses capacity_pos_lt_one.

## Proof sources

- Source `solution.tex`, lines 74–81

## Proof dependencies

- `div_lt_one₀` from `Mathlib.Algebra.Order.GroupWithZero.Basic`
- `Int.cast_le` from `Mathlib.Algebra.Order.Ring.Cast`
- `Finset.not_nonempty_iff_eq_empty` from `Mathlib.Data.Finset.Empty`
- `Fintype.card_pos` from `Mathlib.Data.Fintype.Card`
- `Fintype.ofFinite` from `Mathlib.Data.Fintype.EquivFin`
- `Main.RootedCapacity::IsAdmissibleRootedTree` → `IsAdmissibleRootedTree` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.IsAdmissibleRootedTree`
- `Main.RootedCapacity::IsAdmissibleRootedTree_rootedChildComponent` →
  `IsAdmissibleRootedTree_rootedChildComponent` from `PositiveDefiniteTreeLattice.Main.RootedCapacit
  y.Theorems.IsAdmissibleRootedTree_rootedChildComponent`
- `Main.RootedCapacity::rootedCapacity` → `rootedCapacity` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedCapacity`
- `Main.RootedCapacity::rootedCapacity_pos` → `rootedCapacity_pos` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.rootedCapacity_pos`
- `Main.RootedCapacity::rootedCapacity_recursion` → `rootedCapacity_recursion` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.rootedCapacity_recursion`
- `Main.RootedCapacity::rootedChildCapacitySum` → `rootedChildCapacitySum` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildCapacitySum`
- `Main.RootedCapacity::rootedChildCapacitySum_lt_card_of_forall_lt_one` →
  `rootedChildCapacitySum_lt_card_of_forall_lt_one` from `PositiveDefiniteTreeLattice.Main.RootedCap
  acity.Theorems.rootedChildCapacitySum_lt_card_of_forall_lt_one`
- `Main.RootedCapacity::rootedChildCapacitySummand` → `rootedChildCapacitySummand` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildCapacitySummand`
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
theorem rootedCapacity_lt_one_of_card_le (n : ℕ) {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (w : V → ℤ) (ρ : V)
    (hAdm : IsAdmissibleRootedTree G w ρ) (hcard : Fintype.card V ≤ n) :
    rootedCapacity G w ρ < 1 := by
  induction n generalizing V with
  | zero =>
      letI : Nonempty V := ⟨ρ⟩
      exact (Nat.not_lt_of_ge hcard Fintype.card_pos).elim
  | succ n ih =>
      classical
      rcases hAdm with ⟨hG, hPos, hTwo, hRootWeight⟩
      have hAdm0 : IsAdmissibleRootedTree G w ρ :=
        ⟨hG, hPos, hTwo, hRootWeight⟩
      let S := rootedChildren G hG ρ ρ
      have hchild : ∀ c : {c : V // c ∈ S},
          rootedChildCapacitySummand G hG w ρ c < 1 := by
        intro c
        dsimp only [rootedChildCapacitySummand]
        let C := rootedChildComponent G ρ c.1
        letI : Fintype C := Fintype.ofFinite C
        letI : DecidableRel C.toSimpleGraph.Adj := by
          intro x y
          change Decidable ((G.deleteEdges {s(ρ, c.1)}).Adj (x : V) (y : V))
          infer_instance
        have hchildCapacity :
            rootedCapacity C.toSimpleGraph (fun x : C => w (x : V))
              (rootedChildRoot G ρ c.1) < 1 := by
          have hlt : Fintype.card C < Fintype.card V := by
            simpa only [C] using rootedChildComponent_card_lt G hG ρ ρ c.1 c.2
          have hle : Fintype.card C ≤ n :=
            Nat.le_of_lt_succ (hlt.trans_le hcard)
          exact ih C.toSimpleGraph (fun x : C => w (x : V))
            (rootedChildRoot G ρ c.1)
            (IsAdmissibleRootedTree_rootedChildComponent G w ρ ρ c.1 hG c.2 hAdm0) hle
        exact hchildCapacity
      have hden : 1 < (w ρ : ℚ) - rootedChildCapacitySum G hG w ρ := by
        by_cases hS : S.Nonempty
        · have hsum : rootedChildCapacitySum G hG w ρ < (S.card : ℚ) := by
            simpa only [S] using
              rootedChildCapacitySum_lt_card_of_forall_lt_one G hG w ρ hS hchild
          have hweight : ((S.card : ℤ) + 1) ≤ w ρ := by
            simpa only [S, rootedChildCount] using hRootWeight ρ
          have hweightQ : ((S.card : ℚ) + 1) ≤ (w ρ : ℚ) := by
            exact_mod_cast hweight
          linarith
        · have hsum : rootedChildCapacitySum G hG w ρ = 0 := by
            have hS' : ¬(rootedChildren G hG ρ ρ).Nonempty := by
              simpa only [S] using hS
            letI : IsEmpty {c : V // c ∈ rootedChildren G hG ρ ρ} :=
              ⟨fun c => hS' ⟨c.1, c.2⟩⟩
            unfold rootedChildCapacitySum
            simp
          have htwoQ : (2 : ℚ) ≤ (w ρ : ℚ) := by
            exact_mod_cast hTwo ρ
          rw [hsum]
          linarith
      have hcapacity_pos : 0 < rootedCapacity G w ρ :=
        rootedCapacity_pos G w ρ hAdm0
      calc
        rootedCapacity G w ρ = 1 / ((w ρ : ℚ) - rootedChildCapacitySum G hG w ρ) :=
          rootedCapacity_recursion G hG w ρ hAdm0
        _ < 1 := (div_lt_one₀ (by linarith)).2 hden
```

## Statement dependencies

- `current repo:Main.RootedCapacity.IsAdmissibleRootedTree`
- `current repo:Main.RootedCapacity.rootedCapacity`

## Proof dependencies

- `Mathlib:Mathlib.Algebra.Order.GroupWithZero.Basic.div_lt_one₀`
- `Mathlib:Mathlib.Algebra.Order.Ring.Cast.Int.cast_le`
- `Mathlib:Mathlib.Data.Finset.Empty.Finset.not_nonempty_iff_eq_empty`
- `Mathlib:Mathlib.Data.Fintype.Card.Fintype.card_pos`
- `Mathlib:Mathlib.Data.Fintype.EquivFin.Fintype.ofFinite`
- `current repo:Main.RootedCapacity.IsAdmissibleRootedTree`
- `current repo:Main.RootedCapacity.IsAdmissibleRootedTree_rootedChildComponent`
- `current repo:Main.RootedCapacity.rootedCapacity`
- `current repo:Main.RootedCapacity.rootedCapacity_pos`
- `current repo:Main.RootedCapacity.rootedCapacity_recursion`
- `current repo:Main.RootedCapacity.rootedChildCapacitySum`
- `current repo:Main.RootedCapacity.rootedChildCapacitySum_lt_card_of_forall_lt_one`
- `current repo:Main.RootedCapacity.rootedChildCapacitySummand`
- `current repo:Main.RootedCapacity.rootedChildComponent`
- `current repo:Main.RootedCapacity.rootedChildComponent_card_lt`
- `current repo:Main.RootedCapacity.rootedChildCount`
- `current repo:Main.RootedCapacity.rootedChildRoot`
- `current repo:Main.RootedCapacity.rootedChildren`

## Sources

- `solution.tex:74-81`
