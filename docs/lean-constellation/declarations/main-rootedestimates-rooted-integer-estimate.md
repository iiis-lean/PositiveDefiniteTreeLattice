[← Public API](../PUBLIC_API.md) · [Public boundaries](../PUBLIC_BOUNDARIES.md)

# `rooted_integer_estimate`

The source quadratic rooted estimate for integer vectors and integer k.

- Kind: `theorem`
- Node: `Main.RootedEstimates`
- Module: `PositiveDefiniteTreeLattice.Main.RootedEstimates.Theorems.rooted_integer_estimate`
- State: `proved`
- Revision status: `committed`
- Repository completion: `graph_proved`
- Formal code: final proof projection

## Lean code

```lean
-- lean-constellation: managed-imports-begin
import PositiveDefiniteTreeLattice.Main.RootedEstimates.Prelude
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Nat.Init
import PositiveDefiniteTreeLattice.Main.RootedEstimates.Theorems.consecutiveIntegerProductNonneg
import PositiveDefiniteTreeLattice.Main.RootedEstimates.Theorems.rationalUnitIntervalIntegerDistance
import PositiveDefiniteTreeLattice.Main.RootedEstimates.Theorems.rootedCapacityInvEqSub
import PositiveDefiniteTreeLattice.Main.RootedEstimates.Theorems.rootedEstimateInductionAggregation
import PositiveDefiniteTreeLattice.Main.RootedEstimates.Theorems.treePairingRootedChildDecomposition
import PositiveDefiniteTreeLattice.Main.RootedEstimates.Theorems.unitIntervalCompensationNonneg
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `rooted_integer_estimate`

For a finite decidable simple graph `G` on `V`, an integer weight function `w : V → ℤ`, and a root
`rho`, assume `hG : IsAdmissibleRootedTree G w rho`.  For every integral coordinate vector `x : V →
ℤ` and every integer `k`, the exact public theorem
`PositiveDefiniteTreeLattice.rooted_integer_estimate` asserts the rational inequality

`0 ≤ (↑(treePairing G w x x) : ℚ) - (2 * (k : ℚ) + 1) * (x rho : ℚ) + rootedCapacity G w rho * (k :
ℚ) * ((k : ℚ) + 1)`.

Thus the integral tree-pairing norm, the exact root coordinate, and the rooted rational capacity
occur with the source’s unchanged signs and conclusion direction.  The finite and decidable
structure assumed is only that required to form the existing tree-pairing and rooted-capacity APIs.

## Sources

- Source `solution.tex`, lines 84–89

## Statement dependencies

- `Main.LatticeFoundations::treePairingAnchor` → `PositiveDefiniteTreeLattice.treePairing` from
  `PositiveDefiniteTreeLattice.Main.LatticeFoundations.Defs.treePairingAnchor`
- `Main.RootedCapacity::IsAdmissibleRootedTree` → `IsAdmissibleRootedTree` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.IsAdmissibleRootedTree`
- `Main.RootedCapacity::rootedCapacity` → `rootedCapacity` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedCapacity`

## Proof outline

Prove the exact public statement by strong induction on Fintype.card V, with the induction predicate
generalized over the finite vertex type, graph, weights, root, admissibility witness, integer
coordinate vector, and integer k. Destructure the admissibility witness once to obtain the tree
witness hT : G.IsTree; retain the original admissibility proposition for the capacity and
child-admissibility APIs.

Base case: hT and the chosen root imply the card is at least one, so the minimal case has card V =
1. The vertex type is then subsingleton, hence rootedChildren is empty. Use
treePairingRootedChildDecomposition to reduce treePairing G w x x to w rho * (x rho)^2, and
rootedCapacityInvEqSub (with the zero child-capacity sum) to rewrite the capacity relation. The
positive capacity from PositiveDefiniteTreeLattice.capacity_pos_lt_one lets ordered-field
normalization rewrite the target as a positive rational multiple of the integer product (w rho * x
rho - k) * (w rho * x rho - k - 1). Apply consecutiveIntegerProductNonneg and cast/order
normalization to conclude.

Induction step: for each c in rootedChildren G hT rho rho, let C be rootedChildComponent G rho c,
with its induced graph, restricted weight and restricted coordinate vector, child root, and child
capacity gamma_c = rootedChildCapacitySummand G hT w rho ⟨c,hc⟩.
IsAdmissibleRootedTree_rootedChildComponent supplies admissibility of C, and
rootedChildComponent_card_lt supplies its strict cardinality bound. Invoke the strong induction
hypothesis on C twice, first at the integer a := x rho and then at a - 1. After rearranging each
conclusion over the rationals, these are exactly the two source bounds for the child self-pairing
minus 2*a*s_c, where s_c is x at the child root. Apply twoBoundsGiveAbsLowerBound to obtain the
source lower bound -gamma_c*a^2 + |s_c - gamma_c*a|. Sum it over the children with
Finset.sum_le_sum.

Use treePairingRootedChildDecomposition and Int.cast_sum to substitute the integral root/child
decomposition. Unfold rootedChildCapacitySum and rootedChildCapacitySummand so that the summed child
capacities are the same gamma_c just used in the induction. Apply rootedCapacityInvEqSub, and use 0
< gamma < 1 from capacity_pos_lt_one. With tau := (a : Q) / gamma and D := sum_c |s_c - gamma_c*a|,
ordered-field/ring normalization gives the source inequality
E >= gamma * (tau - k) * (tau - k - 1) + D,
where E is the target left-hand expression.

For the exterior cases, split into tau <= k and k + 1 <= tau. In either case the two factors of the
quadratic have the same sign, so their product is nonnegative; gamma is positive and D is a finite
sum of nonnegative absolute values. Thus E is nonnegative.

For the interior case k < tau < k + 1, define the integer N := w rho * a - sum_c s_c. The
capacity-inverse identity and finite-sum algebra give tau - (N : Q) = sum_c (s_c - gamma_c*a).
Finset.abs_sum_le_sum_abs yields |tau - (N : Q)| <= D. Apply rationalUnitIntervalIntegerDistance to
get the endpoint minimum below that absolute value, hence below D. Finally
unitIntervalCompensationNonneg, using 0 < gamma < 1 and the strict interval hypotheses, proves gamma
* (tau-k) * (tau-k-1) + D is nonnegative. Combine with the earlier lower bound for E. This is
exactly the b_0010 argument from lines 84–153 and preserves the required casts, root coordinate, and
conclusion direction.

## Proof sources

- Source `solution.tex`, lines 84–153

## Proof dependencies

- `Finset.sum_attach` from `Mathlib.Algebra.BigOperators.Group.Finset.Basic`
- `Finset.sum_congr` from `Mathlib.Algebra.BigOperators.Group.Finset.Basic`
- `Finset.sum_eq_zero` from `Mathlib.Algebra.BigOperators.Group.Finset.Basic`
- `Finset.sum_sub_distrib` from `Mathlib.Algebra.BigOperators.Group.Finset.Defs`
- `Finset.sum_mul` from `Mathlib.Algebra.BigOperators.Ring.Finset`
- `Int.cast_sum` from `Mathlib.Algebra.BigOperators.Ring.Finset`
- `Finset.abs_sum_le_sum_abs` from `Mathlib.Algebra.Order.BigOperators.Group.Finset`
- `Finset.sum_nonneg` from `Mathlib.Algebra.Order.BigOperators.Group.Finset`
- `Fintype.card_le_one_iff_subsingleton` from `Mathlib.Data.Fintype.EquivFin`
- `Nat.strong_induction_on` from `Mathlib.Data.Nat.Init`
- `Main.RootedCapacity::capacity_pos_lt_one` → `PositiveDefiniteTreeLattice.capacity_pos_lt_one`
  from `PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.capacity_pos_lt_one`
- `Main.RootedCapacity::rootedChildCapacitySum` → `rootedChildCapacitySum` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildCapacitySum`
- `Main.RootedCapacity::rootedChildCapacitySummand` → `rootedChildCapacitySummand` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildCapacitySummand`
- `Main.RootedCapacity::rootedChildren` → `rootedChildren` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildren`
- `Main.RootedEstimates::consecutiveIntegerProductNonneg` → `consecutiveIntegerProductNonneg` from
  `PositiveDefiniteTreeLattice.Main.RootedEstimates.Theorems.consecutiveIntegerProductNonneg`
- `Main.RootedEstimates::rationalUnitIntervalIntegerDistance` →
  `rationalUnitIntervalIntegerDistance` from
  `PositiveDefiniteTreeLattice.Main.RootedEstimates.Theorems.rationalUnitIntervalIntegerDistance`
- `Main.RootedEstimates::rootedCapacityInvEqSub` → `rootedCapacityInvEqSub` from
  `PositiveDefiniteTreeLattice.Main.RootedEstimates.Theorems.rootedCapacityInvEqSub`
- `Main.RootedEstimates::rootedEstimateInductionAggregation` → `rootedEstimateInductionAggregation`
  from
  `PositiveDefiniteTreeLattice.Main.RootedEstimates.Theorems.rootedEstimateInductionAggregation`
- `Main.RootedEstimates::treePairingRootedChildDecomposition` →
  `treePairingRootedChildDecomposition` from
  `PositiveDefiniteTreeLattice.Main.RootedEstimates.Theorems.treePairingRootedChildDecomposition`
- `Main.RootedEstimates::unitIntervalCompensationNonneg` → `unitIntervalCompensationNonneg` from
  `PositiveDefiniteTreeLattice.Main.RootedEstimates.Theorems.unitIntervalCompensationNonneg`
-/
theorem PositiveDefiniteTreeLattice.rooted_integer_estimate {V : Type*} [Fintype V]
    [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (w : V → ℤ) (rho : V)
    (hG : IsAdmissibleRootedTree G w rho) (x : V → ℤ) (k : ℤ) :
    0 ≤ (↑(treePairing G w x x) : ℚ) - (2 * (k : ℚ) + 1) * (x rho : ℚ) +
  rootedCapacity G w rho * (k : ℚ) * ((k : ℚ) + 1) := by
  classical
  let P : ℕ → Prop := fun n =>
    ∀ {W : Type _} [Fintype W] [DecidableEq W] (H : SimpleGraph W)
      [DecidableRel H.Adj] (weight : W → ℤ) (r : W), Fintype.card W = n →
        IsAdmissibleRootedTree H weight r → ∀ (y : W → ℤ) (m : ℤ),
          0 ≤ (↑(treePairing H weight y y) : ℚ) - (2 * (m : ℚ) + 1) * (y r : ℚ) +
            rootedCapacity H weight r * (m : ℚ) * ((m : ℚ) + 1)
  have hP : ∀ n, P n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro W instW decW H decAdjW weight r hcard hAdm y m
      have hT : H.IsTree := hAdm.choose
      have hsingleton_base (hsingle : Fintype.card W = 1) :
          0 ≤ (↑(treePairing H weight y y) : ℚ) -
            (2 * (m : ℚ) + 1) * (y r : ℚ) +
              rootedCapacity H weight r * (m : ℚ) * ((m : ℚ) + 1) := by
        have hsub : Subsingleton W :=
          Fintype.card_le_one_iff_subsingleton.mp (by omega)
        have hchildren : rootedChildren H hT r r = ∅ := by
          ext c
          constructor
          · intro hc
            rw [rootedChildren] at hc
            rcases Finset.mem_filter.mp hc with ⟨_, hadj, _⟩
            have hcr : c = r := hsub.elim _ _
            subst c
            exact (H.loopless.irrefl _ hadj).elim
          · simp
        have hpair : treePairing H weight y y = weight r * (y r) ^ 2 := by
          simpa [hchildren] using treePairingRootedChildDecomposition H hT weight y r
        have hcapsum : rootedChildCapacitySum H hT weight r = 0 := by
          unfold rootedChildCapacitySum
          apply Finset.sum_eq_zero
          intro c _
          exfalso
          have hcempty : c.1 ∈ (∅ : Finset W) := by
            simpa only [← hchildren] using c.2
          simp at hcempty
        have hinv : (rootedCapacity H weight r)⁻¹ = (weight r : ℚ) := by
          rw [rootedCapacityInvEqSub H hT weight r hAdm, hcapsum]
          simp
        have hgamma_pos : 0 < rootedCapacity H weight r :=
          (PositiveDefiniteTreeLattice.capacity_pos_lt_one H weight r hAdm).1
        let z : ℤ := weight r * y r - m
        have hz : 0 ≤ z * (z - 1) := consecutiveIntegerProductNonneg z
        have hzQ : 0 ≤ (↑(z * (z - 1)) : ℚ) := by
          exact_mod_cast hz
        have hbase_eq :
            (↑(treePairing H weight y y) : ℚ) -
                (2 * (m : ℚ) + 1) * (y r : ℚ) +
                  rootedCapacity H weight r * (m : ℚ) * ((m : ℚ) + 1) =
              rootedCapacity H weight r * (↑(z * (z - 1)) : ℚ) := by
          rw [hpair]
          push_cast
          dsimp [z]
          push_cast
          rw [← hinv]
          field_simp [ne_of_gt hgamma_pos]
          ring
        rw [hbase_eq]
        exact mul_nonneg (le_of_lt hgamma_pos) hzQ
      by_cases hsingle : Fintype.card W = 1
      · exact hsingleton_base hsingle
      · have hagg := rootedEstimateInductionAggregation H weight r hT hAdm y m
          (fun {U} instU decU K decAdjU weightU rU hlt hAdmU z q => by
            exact ih (Fintype.card U) (by simpa [← hcard] using hlt)
              K weightU rU rfl hAdmU z q)
        let a : ℤ := y r
        let gamma : ℚ := rootedCapacity H weight r
        let tau : ℚ := (a : ℚ) / gamma
        letI : Fintype {c : W // c ∈ rootedChildren H hT r r} := Fintype.ofFinite _
        let D : ℚ := ∑ c : {c : W // c ∈ rootedChildren H hT r r},
          |(y c.1 : ℚ) - rootedChildCapacitySummand H hT weight r c * (a : ℚ)|
        have hagg' :
            (↑(treePairing H weight y y) : ℚ) - (2 * (m : ℚ) + 1) * (a : ℚ) +
                gamma * (m : ℚ) * ((m : ℚ) + 1) ≥
              gamma * (tau - (m : ℚ)) * (tau - (m : ℚ) - 1) + D := by
          simpa [a, gamma, tau, D] using hagg
        have hgamma_pos : 0 < gamma := by
          simpa [gamma] using (PositiveDefiniteTreeLattice.capacity_pos_lt_one H weight r hAdm).1
        have hgamma_nonneg : 0 ≤ gamma := le_of_lt hgamma_pos
        have hD_nonneg : 0 ≤ D := by
          dsimp [D]
          apply Finset.sum_nonneg
          intro c _
          exact abs_nonneg _
        by_cases hleft : tau ≤ (m : ℚ)
        · have hquad : 0 ≤ gamma * (tau - (m : ℚ)) * (tau - (m : ℚ) - 1) := by
            rw [mul_assoc]
            exact mul_nonneg hgamma_nonneg
              (mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith))
          dsimp [a, gamma] at hagg' ⊢
          nlinarith
        by_cases hright : (m : ℚ) + 1 ≤ tau
        · have hquad : 0 ≤ gamma * (tau - (m : ℚ)) * (tau - (m : ℚ) - 1) := by
            rw [mul_assoc]
            exact mul_nonneg hgamma_nonneg (mul_nonneg (by linarith) (by linarith))
          dsimp [a, gamma] at hagg' ⊢
          nlinarith
        have hm_lt_tau : (m : ℚ) < tau := lt_of_not_ge hleft
        have htau_lt_m_one : tau < (m : ℚ) + 1 := lt_of_not_ge hright
        have hgamma_lt_one : gamma < 1 := by
          simpa [gamma] using (PositiveDefiniteTreeLattice.capacity_pos_lt_one H weight r hAdm).2
        have hgamma_ne : gamma ≠ 0 := ne_of_gt hgamma_pos
        have hinv : gamma⁻¹ = (weight r : ℚ) - rootedChildCapacitySum H hT weight r := by
          simpa [gamma] using rootedCapacityInvEqSub H hT weight r hAdm
        have hcap_sum :
            (∑ c : {c : W // c ∈ rootedChildren H hT r r},
              rootedChildCapacitySummand H hT weight r c) =
              rootedChildCapacitySum H hT weight r := by
          unfold rootedChildCapacitySum
          apply Finset.sum_congr
          · ext c
            simp
          · intro c _
            rfl
        have hy_sum :
            (∑ c : {c : W // c ∈ rootedChildren H hT r r}, (y c.1 : ℚ)) =
              ∑ c ∈ rootedChildren H hT r r, (y c : ℚ) := by
          calc
            (∑ c : {c : W // c ∈ rootedChildren H hT r r}, (y c.1 : ℚ)) =
                ∑ c ∈ (rootedChildren H hT r r).attach, (y c.1 : ℚ) := by
                  rw [show (Finset.univ : Finset {c : W // c ∈ rootedChildren H hT r r}) =
                    (rootedChildren H hT r r).attach by
                    ext c
                    simp]
            _ = ∑ c ∈ rootedChildren H hT r r, (y c : ℚ) :=
              Finset.sum_attach (rootedChildren H hT r r) (fun c => (y c : ℚ))
        have herror_sum :
            (∑ c : {c : W // c ∈ rootedChildren H hT r r},
              ((y c.1 : ℚ) - rootedChildCapacitySummand H hT weight r c * (a : ℚ))) =
                (∑ c ∈ rootedChildren H hT r r, (y c : ℚ)) -
                  rootedChildCapacitySum H hT weight r * (a : ℚ) := by
          rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hy_sum, hcap_sum]
        let N : ℤ := weight r * a - ∑ c ∈ rootedChildren H hT r r, y c
        have htau_N : tau - (N : ℚ) =
            ∑ c : {c : W // c ∈ rootedChildren H hT r r},
              ((y c.1 : ℚ) - rootedChildCapacitySummand H hT weight r c * (a : ℚ)) := by
          dsimp [tau, N]
          push_cast
          rw [div_eq_mul_inv, hinv, herror_sum]
          ring
        have habs : |tau - (N : ℚ)| ≤ D := by
          dsimp [D]
          rw [htau_N]
          exact Finset.abs_sum_le_sum_abs _ _
        have hD : D ≥ min (tau - (m : ℚ)) ((m : ℚ) + 1 - tau) :=
          le_trans (rationalUnitIntervalIntegerDistance m N tau hm_lt_tau htau_lt_m_one) habs
        have hcomp := unitIntervalCompensationNonneg gamma tau D m hgamma_pos hgamma_lt_one
          hm_lt_tau htau_lt_m_one hD
        dsimp [a, gamma] at hagg' ⊢
        nlinarith
  exact hP (Fintype.card V) G w rho rfl hG x k
```

## Statement dependencies

- `current repo:Main.LatticeFoundations.treePairingAnchor`
- `current repo:Main.RootedCapacity.IsAdmissibleRootedTree`
- `current repo:Main.RootedCapacity.rootedCapacity`

## Proof dependencies

- `Mathlib:Mathlib.Algebra.BigOperators.Group.Finset.Basic.Finset.sum_attach`
- `Mathlib:Mathlib.Algebra.BigOperators.Group.Finset.Basic.Finset.sum_congr`
- `Mathlib:Mathlib.Algebra.BigOperators.Group.Finset.Basic.Finset.sum_eq_zero`
- `Mathlib:Mathlib.Algebra.BigOperators.Group.Finset.Defs.Finset.sum_sub_distrib`
- `Mathlib:Mathlib.Algebra.BigOperators.Ring.Finset.Finset.sum_mul`
- `Mathlib:Mathlib.Algebra.BigOperators.Ring.Finset.Int.cast_sum`
- `Mathlib:Mathlib.Algebra.Order.BigOperators.Group.Finset.Finset.abs_sum_le_sum_abs`
- `Mathlib:Mathlib.Algebra.Order.BigOperators.Group.Finset.Finset.sum_nonneg`
- `Mathlib:Mathlib.Data.Fintype.EquivFin.Fintype.card_le_one_iff_subsingleton`
- `Mathlib:Mathlib.Data.Nat.Init.Nat.strong_induction_on`
- `current repo:Main.RootedCapacity.capacity_pos_lt_one`
- `current repo:Main.RootedCapacity.rootedChildCapacitySum`
- `current repo:Main.RootedCapacity.rootedChildCapacitySummand`
- `current repo:Main.RootedCapacity.rootedChildren`
- `current repo:Main.RootedEstimates.consecutiveIntegerProductNonneg`
- `current repo:Main.RootedEstimates.rationalUnitIntervalIntegerDistance`
- `current repo:Main.RootedEstimates.rootedCapacityInvEqSub`
- `current repo:Main.RootedEstimates.rootedEstimateInductionAggregation`
- `current repo:Main.RootedEstimates.treePairingRootedChildDecomposition`
- `current repo:Main.RootedEstimates.unitIntervalCompensationNonneg`

## Sources

- `solution.tex:84-89`
