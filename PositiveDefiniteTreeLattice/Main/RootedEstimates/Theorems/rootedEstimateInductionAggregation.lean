-- lean-constellation: managed-imports-begin
import PositiveDefiniteTreeLattice.Main.RootedEstimates.Prelude
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import PositiveDefiniteTreeLattice.Main.RootedEstimates.Theorems.rootedCapacityInvEqSub
import PositiveDefiniteTreeLattice.Main.RootedEstimates.Theorems.rootedChildInductionAbsBound
import PositiveDefiniteTreeLattice.Main.RootedEstimates.Theorems.treePairingInstanceIndependent
import PositiveDefiniteTreeLattice.Main.RootedEstimates.Theorems.treePairingRootedChildDecomposition
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

universe u

/--
# lean-constellation target: `rootedEstimateInductionAggregation`

Fix one universe `u`.  Let `V : Type u` carry the finite and decidable data required by the existing
APIs, let `G` be a rooted integer-weighted tree on `V` with root `rho`, weight `w`, and
admissibility hypothesis `hT : IsAdmissibleRootedTree G w rho`, and let `x : V → ℤ` and `k : ℤ`.
The generalized smaller-tree induction hypothesis is quantified over finite rooted admissible trees
whose vertex types also lie in this same universe `u` and have strictly smaller cardinality.

Put `a := x rho`, `gamma := rootedCapacity G w rho`, and `tau := (a : ℚ) / gamma`.  After
specializing that hypothesis through `rootedChildInductionAbsBound` for every `c ∈ rootedChildren G
hT rho rho`, this theorem asserts the rational inequality

`(↑(treePairing G w x x) : ℚ) - (2 * (k : ℚ) + 1) * (a : ℚ) + gamma * (k : ℚ) * ((k : ℚ) + 1) ≥
gamma * (tau - (k : ℚ)) * (tau - (k : ℚ) - 1) + ∑ c ∈ rootedChildren G hT rho rho, |(x c : ℚ) -
rootedChildCapacitySummand G hT w rho ⟨c, hc⟩ * (a : ℚ)|`.

The child sum has exactly the rooted-children index and the rooted child-capacity summand of each
`⟨c, hc⟩`.  This is source inequality (1), obtained by aggregating the child component pairings and
their root-boundary contribution through the proved rooted pairing decomposition and the rooted
capacity identity.

## Sources

- Source `solution.tex`, lines 102–127

## Statement dependencies

- `Main.LatticeFoundations::treePairingAnchor` → `PositiveDefiniteTreeLattice.treePairing` from
  `PositiveDefiniteTreeLattice.Main.LatticeFoundations.Defs.treePairingAnchor`
- `Main.RootedCapacity::IsAdmissibleRootedTree` → `IsAdmissibleRootedTree` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.IsAdmissibleRootedTree`
- `Main.RootedCapacity::rootedCapacity` → `rootedCapacity` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedCapacity`
- `Main.RootedCapacity::rootedChildCapacitySummand` → `rootedChildCapacitySummand` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildCapacitySummand`
- `Main.RootedCapacity::rootedChildren` → `rootedChildren` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildren`

## Proof outline

Work with the single explicit universe `u` in the statement, and unfold the local `a`, `gamma`,
`tau`, and rooted-children `Fintype` binders.  For each subtype child `c : {c : V // c ∈
rootedChildren G hT rho rho}`, apply the proved same-universe bridge
`rootedChildInductionAbsBound G w rho hT hAdm x c.1 c.2 hIH`.
It supplies precisely the rational inequality for the pairing on `rootedChildComponent G rho c.1`,
with its restricted weight and coordinate vector, lower-bounded by
`- rootedChildCapacitySummand G hT w rho c * (a : ℚ)^2 + |(x c.1 : ℚ) - rootedChildCapacitySummand G
hT w rho c * (a : ℚ)|`.

Apply `Finset.sum_le_sum` over `Finset.univ` to these child bounds.  Use distributivity to collect
the child pairing terms, the boundary terms `2*a*x c`, and the capacity summands.  Rewrite the
ambient integral pairing with `treePairingRootedChildDecomposition G hT w x rho`; then use
`Int.cast_sum` (including the nested finite sums) and ring normalization to turn its rational cast
into the aggregated left side.  This keeps exactly the child-component pairings, restricted
coordinates, and root boundary contribution from lines 102–110.

Set `D` to the resulting `∑ c, |(x c.1 : ℚ) - rootedChildCapacitySummand G hT w rho c * (a : ℚ)|`.
Unfold `rootedChildCapacitySum`, so its finite sum is the same child index and summand.  From
`PositiveDefiniteTreeLattice.capacity_pos_lt_one G w rho hAdm`, obtain `gamma ≠ 0`.  Rewrite
`rootedCapacityInvEqSub G hT w rho hAdm` and use the definition of `tau = (a : ℚ) / gamma`;
field/ring normalization converts the remaining root term into
`gamma * (tau - (k : ℚ)) * (tau - (k : ℚ) - 1)`.
Combining this equality with the summed lower bound yields the formal conclusion, with the stated
`≥` direction.  This is exactly the aggregation and capacity calculation in solution.tex lines
102–127 (source inequality (1)).

## Proof sources

- Source `solution.tex`, lines 102–127

## Proof dependencies

- `Finset.sum_add_distrib` from `Mathlib.Algebra.BigOperators.Group.Finset.Basic`
- `Finset.sum_attach` from `Mathlib.Algebra.BigOperators.Group.Finset.Basic`
- `Finset.sum_congr` from `Mathlib.Algebra.BigOperators.Group.Finset.Basic`
- `Finset.sum_neg_distrib` from `Mathlib.Algebra.BigOperators.Group.Finset.Defs`
- `Finset.sum_sub_distrib` from `Mathlib.Algebra.BigOperators.Group.Finset.Defs`
- `Finset.mul_sum` from `Mathlib.Algebra.BigOperators.Ring.Finset`
- `Finset.sum_mul` from `Mathlib.Algebra.BigOperators.Ring.Finset`
- `Int.cast_sum` from `Mathlib.Algebra.BigOperators.Ring.Finset`
- `Finset.sum_le_sum` from `Mathlib.Algebra.Order.BigOperators.Group.Finset`
- `Main.RootedCapacity::capacity_pos_lt_one` → `PositiveDefiniteTreeLattice.capacity_pos_lt_one`
  from `PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.capacity_pos_lt_one`
- `Main.RootedCapacity::rootedChildCapacitySum` → `rootedChildCapacitySum` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildCapacitySum`
- `Main.RootedCapacity::rootedChildCapacitySummand` → `rootedChildCapacitySummand` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildCapacitySummand`
- `Main.RootedEstimates::rootedCapacityInvEqSub` → `rootedCapacityInvEqSub` from
  `PositiveDefiniteTreeLattice.Main.RootedEstimates.Theorems.rootedCapacityInvEqSub`
- `Main.RootedEstimates::rootedChildInductionAbsBound` → `rootedChildInductionAbsBound` from
  `PositiveDefiniteTreeLattice.Main.RootedEstimates.Theorems.rootedChildInductionAbsBound`
- `Main.RootedEstimates::treePairingInstanceIndependent` → `treePairingInstanceIndependent` from
  `PositiveDefiniteTreeLattice.Main.RootedEstimates.Theorems.treePairingInstanceIndependent`
- `Main.RootedEstimates::treePairingRootedChildDecomposition` →
  `treePairingRootedChildDecomposition` from
  `PositiveDefiniteTreeLattice.Main.RootedEstimates.Theorems.treePairingRootedChildDecomposition`
-/
theorem rootedEstimateInductionAggregation {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (w : V → ℤ) (rho : V) (hT : G.IsTree)
    (hAdm : IsAdmissibleRootedTree G w rho) (x : V → ℤ) (k : ℤ)
    (hIH : ∀ {W : Type u} [Fintype W] [DecidableEq W] (H : SimpleGraph W)
      [DecidableRel H.Adj] (weight : W → ℤ) (r : W), Fintype.card W < Fintype.card V →
        IsAdmissibleRootedTree H weight r → ∀ (y : W → ℤ) (m : ℤ),
          0 ≤ (↑(PositiveDefiniteTreeLattice.treePairing H weight y y) : ℚ) -
            (2 * (m : ℚ) + 1) * (y r : ℚ) + rootedCapacity H weight r * (m : ℚ) *
              ((m : ℚ) + 1)) :
    let a : ℤ := x rho
    let gamma : ℚ := rootedCapacity G w rho
    let tau : ℚ := (a : ℚ) / gamma
    letI : Fintype {c : V // c ∈ rootedChildren G hT rho rho} := Fintype.ofFinite _
    (↑(PositiveDefiniteTreeLattice.treePairing G w x x) : ℚ) -
        (2 * (k : ℚ) + 1) * (a : ℚ) + gamma * (k : ℚ) * ((k : ℚ) + 1) ≥
      gamma * (tau - (k : ℚ)) * (tau - (k : ℚ) - 1) +
        ∑ c : {c : V // c ∈ rootedChildren G hT rho rho},
          |(x c.1 : ℚ) - rootedChildCapacitySummand G hT w rho c * (a : ℚ)| := by
  classical
  dsimp only
  let a : ℤ := x rho
  let gamma : ℚ := rootedCapacity G w rho
  let tau : ℚ := (a : ℚ) / gamma
  letI : Fintype {c : V // c ∈ rootedChildren G hT rho rho} := Fintype.ofFinite _
  have hchild (c : {c : V // c ∈ rootedChildren G hT rho rho}) :
      let C := rootedChildComponent G rho c.1
      letI : Fintype C := Fintype.ofFinite C
      letI : DecidableEq C := Classical.decEq C
      letI : DecidableRel C.toSimpleGraph.Adj := by
        intro u v
        change Decidable ((G.deleteEdges {s(rho, c.1)}).Adj (u : V) (v : V))
        infer_instance
      (↑(PositiveDefiniteTreeLattice.treePairing C.toSimpleGraph (fun u => w (u : V))
        (fun u => x (u : V)) (fun u => x (u : V))) : ℚ) -
          2 * (a : ℚ) * (x c.1 : ℚ) ≥
        -rootedChildCapacitySummand G hT w rho c * (a : ℚ) ^ 2 +
          |(x c.1 : ℚ) - rootedChildCapacitySummand G hT w rho c * (a : ℚ)| := by
    simpa [a] using
      (rootedChildInductionAbsBound G w rho hT hAdm x c.1 c.2 hIH)
  let lower : {c : V // c ∈ rootedChildren G hT rho rho} → ℚ := fun c =>
    -rootedChildCapacitySummand G hT w rho c * (a : ℚ) ^ 2 +
      |(x c.1 : ℚ) - rootedChildCapacitySummand G hT w rho c * (a : ℚ)|
  let upper : {c : V // c ∈ rootedChildren G hT rho rho} → ℚ := fun c =>
    let C := rootedChildComponent G rho c.1
    letI : Fintype C := Fintype.ofFinite C
    letI : DecidableEq C := fun u v => u.instDecidableEq v
    letI : DecidableRel C.toSimpleGraph.Adj := by
      intro u v
      change Decidable ((G.deleteEdges {s(rho, c.1)}).Adj (u : V) (v : V))
      infer_instance
    (↑(PositiveDefiniteTreeLattice.treePairing C.toSimpleGraph (fun u => w (u : V))
      (fun u => x (u : V)) (fun u => x (u : V))) : ℚ) -
        2 * (a : ℚ) * (x c.1 : ℚ)
  have htransport (c : {c : V // c ∈ rootedChildren G hT rho rho}) :
      let C := rootedChildComponent G rho c.1
      letI : Fintype C := Fintype.ofFinite C
      letI : DecidableEq C := Classical.decEq C
      letI : DecidableRel C.toSimpleGraph.Adj := by
        intro u v
        change Decidable ((G.deleteEdges {s(rho, c.1)}).Adj (u : V) (v : V))
        infer_instance
      let leftPairing := PositiveDefiniteTreeLattice.treePairing C.toSimpleGraph
        (fun u => w (u : V)) (fun u => x (u : V)) (fun u => x (u : V))
      letI : DecidableEq C := fun u v => u.instDecidableEq v
      leftPairing = PositiveDefiniteTreeLattice.treePairing C.toSimpleGraph
        (fun u => w (u : V)) (fun u => x (u : V)) (fun u => x (u : V)) := by
    dsimp only
    apply treePairingInstanceIndependent
  have hsum : (∑ c, lower c) ≤ ∑ c, upper c := by
    apply Finset.sum_le_sum
    intro c _
    dsimp [lower, upper]
    rw [← htransport c]
    exact hchild c
  let upperRaw : V → ℚ := fun c =>
    let C := rootedChildComponent G rho c
    letI : Fintype C := Fintype.ofFinite C
    letI : DecidableEq C := Classical.decEq C
    letI : DecidableRel C.toSimpleGraph.Adj := by
      intro u v
      change Decidable ((G.deleteEdges {s(rho, c)}).Adj (u : V) (v : V))
      infer_instance
    (↑(PositiveDefiniteTreeLattice.treePairing C.toSimpleGraph (fun u => w (u : V))
      (fun u => x (u : V)) (fun u => x (u : V))) : ℚ) -
        2 * (a : ℚ) * (x c : ℚ)
  have hupper (c : {c : V // c ∈ rootedChildren G hT rho rho}) :
      upper c = upperRaw c.1 := by
    dsimp [upper, upperRaw]
    exact congrArg (fun z : ℤ => (z : ℚ) - 2 * (a : ℚ) * (x c.1 : ℚ))
      (htransport c).symm
  have hsumUpper : (∑ c, upper c) =
      (∑ c ∈ rootedChildren G hT rho rho, upperRaw c) := by
    calc
      (∑ c, upper c) = (∑ c ∈ (rootedChildren G hT rho rho).attach, upper c) := by
        rw [show (Finset.univ : Finset {c : V // c ∈ rootedChildren G hT rho rho}) =
          (rootedChildren G hT rho rho).attach by
          ext c
          simp]
      _ = (∑ c ∈ (rootedChildren G hT rho rho).attach, upperRaw c.1) := by
        apply Finset.sum_congr rfl
        intro c _
        exact hupper c
      _ = (∑ c ∈ rootedChildren G hT rho rho, upperRaw c) :=
        Finset.sum_attach _ _
  have hpair :
      (↑(PositiveDefiniteTreeLattice.treePairing G w x x) : ℚ) =
        (w rho : ℚ) * (a : ℚ) ^ 2 +
          (∑ c ∈ rootedChildren G hT rho rho, upperRaw c) := by
    rw [treePairingRootedChildDecomposition G hT w x rho]
    push_cast
    simp only [upperRaw, rootedChildRoot]
    rw [Finset.sum_sub_distrib, Finset.mul_sum]
    ring
  have hlower :
      (∑ c, lower c) =
        -(∑ c, rootedChildCapacitySummand G hT w rho c) * (a : ℚ) ^ 2 +
          ∑ c, |(x c.1 : ℚ) - rootedChildCapacitySummand G hT w rho c * (a : ℚ)| := by
    dsimp [lower]
    rw [Finset.sum_add_distrib]
    conv_lhs =>
      arg 1
      rw [show (fun c : {c : V // c ∈ rootedChildren G hT rho rho} =>
          -rootedChildCapacitySummand G hT w rho c * (a : ℚ) ^ 2) =
        fun c => -(rootedChildCapacitySummand G hT w rho c * (a : ℚ) ^ 2) by
          funext c
          ring]
    rw [Finset.sum_neg_distrib, ← Finset.sum_mul]
    ring
  have hgamma :
      (∑ c, rootedChildCapacitySummand G hT w rho c) =
        rootedChildCapacitySum G hT w rho := by
    unfold rootedChildCapacitySum
    apply Finset.sum_congr
    · ext c
      simp
    · intro c _
      rfl
  have hmain :
      (↑(PositiveDefiniteTreeLattice.treePairing G w x x) : ℚ) ≥
        ((w rho : ℚ) - rootedChildCapacitySum G hT w rho) * (a : ℚ) ^ 2 +
          ∑ c, |(x c.1 : ℚ) - rootedChildCapacitySummand G hT w rho c * (a : ℚ)| := by
    rw [hpair, ← hsumUpper, ← hgamma]
    nlinarith [hsum, hlower]
  have hgamma_pos : 0 < gamma := by
    simpa [gamma] using (PositiveDefiniteTreeLattice.capacity_pos_lt_one G w rho hAdm).1
  have hgamma_ne : gamma ≠ 0 := ne_of_gt hgamma_pos
  have hinv : gamma⁻¹ = (w rho : ℚ) - rootedChildCapacitySum G hT w rho := by
    simpa [gamma] using rootedCapacityInvEqSub G hT w rho hAdm
  have halgebra :
      ((w rho : ℚ) - rootedChildCapacitySum G hT w rho) * (a : ℚ) ^ 2 -
          (2 * (k : ℚ) + 1) * (a : ℚ) + gamma * (k : ℚ) * ((k : ℚ) + 1) =
        gamma * (tau - (k : ℚ)) * (tau - (k : ℚ) - 1) := by
    rw [← hinv]
    dsimp [tau]
    field_simp [hgamma_ne]
    ring
  nlinarith [hmain, halgebra]
