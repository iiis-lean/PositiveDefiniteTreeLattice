-- lean-constellation: managed-imports-begin
import PositiveDefiniteTreeLattice.Main.IrreducibleVertex.Prelude
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Finite
import PositiveDefiniteTreeLattice.Main.IrreducibleVertex.Lemmas.pairing_decomposition_at_unique_underweight
import PositiveDefiniteTreeLattice.Main.IrreducibleVertex.Lemmas.rootedChildCapacitySum_lt_weight_of_unique_underweight
import PositiveDefiniteTreeLattice.Main.IrreducibleVertex.Lemmas.rootedChildComponent_isAdmissible_of_unique_underweight
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `normalized_pairing_positive_of_unique_underweight`

Let `V` be a finite type with decidable equality, let `G : SimpleGraph V` have decidable adjacency,
let `weight : V → ℤ`, let `v : V`, and let `z : V → ℤ`. Suppose `h_tree : G.IsTree`, `h_positive : ∀
x : V → ℤ, x ≠ 0 → 0 < treePairing G weight x x`, `h_unique_underweight : ∃! u : V, weight u <
(G.degree u : ℤ)`, `hv : weight v < (G.degree v : ℤ)`, `h_two : ∀ x : V, 2 ≤ weight x`, `hz_nonzero
: z ≠ 0`, and `hzv_nonneg : 0 ≤ z v`. Then the shifted self-pairing is strictly positive:

`0 < treePairing G weight z z + treePairing G weight (vertexVector v) z`.

## Sources

- Source `solution.tex`, lines 215–241

## Statement dependencies

- `SimpleGraph.IsTree` from `Mathlib.Combinatorics.SimpleGraph.Acyclic`
- `SimpleGraph.degree` from `Mathlib.Combinatorics.SimpleGraph.Finite`
- `Main.LatticeFoundations::treePairingAnchor` → `PositiveDefiniteTreeLattice.treePairing` from
  `PositiveDefiniteTreeLattice.Main.LatticeFoundations.Defs.treePairingAnchor`
- `Main.LatticeFoundations::vertexVectorAnchor` → `PositiveDefiniteTreeLattice.vertexVector` from
  `PositiveDefiniteTreeLattice.Main.LatticeFoundations.Defs.vertexVectorAnchor`

## Proof outline

Let I be the finite subtype of canonical rooted children of v for h_tree. Rewrite the target with
the proved local equality pairing_decomposition_at_unique_underweight G h_tree weight v z, in its
accepted left-to-right orientation:
`treePairing G weight z z + treePairing G weight (vertexVector v) z =
 weight v * z v * (z v + 1) + ∑ c : I, (treePairing C_c w_c z_c z_c - (2 * z v + 1) * z_c ρ_c)`,
where C_c is exactly rootedChildComponent G v c.1, z_c and w_c are the restrictions, and ρ_c is
exactly rootedChildRoot G v c.1. For every c, extract G.Adj v c.1 from c.property and use
rootedChildComponent_isAdmissible_of_unique_underweight with h_tree, h_positive,
h_unique_underweight, hv, and h_two to obtain admissibility of C_c. Put p := z v and split using
hzv_nonneg.

For the p≥1 branch, fix c : I and install the same explicit local data used by the capacity summand:
`Fintype C_c := Fintype.ofFinite C_c`, `DecidableEq C_c := Classical.decEq C_c`, and `DecidableRel
C_c.toSimpleGraph.Adj` by reduction to `(G.deleteEdges {s(v,c.1)}).Adj`. Apply
PositiveDefiniteTreeLattice.rooted_integer_estimate to C_c, its restriction z_c, root ρ_c, and k :=
p. The resulting capacity is the particular `@rootedCapacity C_c fintype_est decEq_est decAdj_est
w_c ρ_c`. Unfold rootedChildCapacitySummand: it has the same C_c, w_c, and ρ_c but its canonical
`Fintype.ofFinite`, inferred `DecidableEq`, and reduced adjacency instances. Use
rootedCapacity_instance_irrel in its verified left-to-right orientation, with these two Fintype,
DecidableEq, and DecidableRel triples, to rewrite the estimate capacity exactly to
`rootedChildCapacitySummand G h_tree weight v c`. This is the canonical capacity-instance bridge; no
alternate component or root is introduced.

Sum the resulting rational inequalities over I with Finset.sum_le_sum. Unfold rootedChildCapacitySum
and use Finset.sum_congr to identify the finite sum of those exact rootedChildCapacitySummand terms.
After distributing casts, sums, and the common factor `(p : ℚ) * ((p : ℚ) + 1)`, combine
rootedChildCapacitySum_lt_weight_of_unique_underweight with p≥1 to obtain the strict rational lower
bound
`0 < ((weight v : ℚ) - rootedChildCapacitySum G h_tree weight v) * (p : ℚ) * ((p : ℚ) + 1)`
and hence strict positivity of the rational cast of the decomposed integer right-hand side.

For p = 0, the accepted decomposition reduces to the finite sum of `treePairing C_c w_c z_c z_c -
z_c ρ_c`, using the same canonical root ρ_c. A zero restriction gives a zero summand; a nonzero
restriction gives a strictly positive summand by root_coefficient_lt_norm applied to the same
admissibility witness and root ρ_c. Thus every summand is nonnegative. Since hz_nonzero and p = 0
yield a nonroot coordinate of z with nonzero value, rootedChildComponent_partition places it in a
canonical child component whose restriction is nonzero. Finset.sum_pos_iff_of_nonneg then gives a
strictly positive sum.

In either branch, first retain the strict inequality in ℚ for the cast of the exact decomposed
right-hand side. Use strict order preservation of the integer-to-rational cast (for example
exact_mod_cast) to obtain strict positivity of that integer right-hand side, then rewrite it back by
the accepted equality pairing_decomposition_at_unique_underweight in its left-to-right orientation.
This yields exactly `0 < treePairing G weight z z + treePairing G weight (vertexVector v) z`; use
treePairing symmetry only if a final Lean normalization requires that accepted orientation.

## Proof sources

- Source `solution.tex`, lines 215–241

## Proof dependencies

- `Finset.single_le_sum` from `Mathlib.Algebra.Order.BigOperators.Group.Finset`
- `Finset.sum_le_sum` from `Mathlib.Algebra.Order.BigOperators.Group.Finset`
- `Finset.sum_nonneg` from `Mathlib.Algebra.Order.BigOperators.Group.Finset`
- `Finset.sum_pos_iff_of_nonneg` from `Mathlib.Algebra.Order.BigOperators.Group.Finset`
- `Main.IrreducibleVertex::pairing_decomposition_at_unique_underweight` →
  `PositiveDefiniteTreeLattice.pairing_decomposition_at_unique_underweight` from `PositiveDefiniteTr
  eeLattice.Main.IrreducibleVertex.Lemmas.pairing_decomposition_at_unique_underweight`
- `Main.IrreducibleVertex::rootedChildCapacitySum_lt_weight_of_unique_underweight` →
  `rootedChildCapacitySum_lt_weight_of_unique_underweight` from `PositiveDefiniteTreeLattice.Main.Ir
  reducibleVertex.Lemmas.rootedChildCapacitySum_lt_weight_of_unique_underweight`
- `Main.IrreducibleVertex::rootedChildComponent_isAdmissible_of_unique_underweight` →
  `PositiveDefiniteTreeLattice.rootedChildComponent_isAdmissible_of_unique_underweight` from `Positi
  veDefiniteTreeLattice.Main.IrreducibleVertex.Lemmas.rootedChildComponent_isAdmissible_of_unique_un
  derweight`
- `Main.RootedCapacity::rootedCapacity_instance_irrel` → `rootedCapacity_instance_irrel` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.rootedCapacity_instance_irrel`
- `Main.RootedCapacity::rootedChildCapacitySum` → `rootedChildCapacitySum` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildCapacitySum`
- `Main.RootedCapacity::rootedChildCapacitySummand` → `rootedChildCapacitySummand` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildCapacitySummand`
- `Main.RootedCapacity::rootedChildComponent_partition` → `rootedChildComponent_partition` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.rootedChildComponent_partition`
- `Main.RootedCapacity::rootedChildRoot` → `rootedChildRoot` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildRoot`
- `Main.RootedEstimates::root_coefficient_lt_norm` →
  `PositiveDefiniteTreeLattice.root_coefficient_lt_norm` from
  `PositiveDefiniteTreeLattice.Main.RootedEstimates.Theorems.root_coefficient_lt_norm`
- `Main.RootedEstimates::rooted_integer_estimate` →
  `PositiveDefiniteTreeLattice.rooted_integer_estimate` from
  `PositiveDefiniteTreeLattice.Main.RootedEstimates.Theorems.rooted_integer_estimate`
-/
theorem PositiveDefiniteTreeLattice.normalized_pairing_positive_of_unique_underweight
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (weight : V → ℤ) (v : V) (z : V → ℤ) (h_tree : G.IsTree)
    (h_positive : ∀ x : V → ℤ, x ≠ 0 → 0 < treePairing G weight x x)
    (h_unique_underweight : ∃! u : V, weight u < (G.degree u : ℤ))
    (hv : weight v < (G.degree v : ℤ)) (h_two : ∀ x : V, 2 ≤ weight x)
    (hz_nonzero : z ≠ 0) (hzv_nonneg : 0 ≤ z v) :
    0 < treePairing G weight z z + treePairing G weight (vertexVector v) z := by
  classical
  rw [pairing_decomposition_at_unique_underweight G h_tree weight v z]
  let I := {c : V // c ∈ rootedChildren G h_tree v v}
  letI : Fintype I := Fintype.ofFinite I
  letI : ∀ c : I, Fintype (rootedChildComponent G v c.1) := fun c =>
    Fintype.ofFinite _
  letI : ∀ c : I, DecidableEq (rootedChildComponent G v c.1) := fun c => Classical.decEq _
  letI : ∀ c : I, DecidableRel (rootedChildComponent G v c.1).toSimpleGraph.Adj := fun c => by
    intro x y
    change Decidable ((G.deleteEdges {s(v, c.1)}).Adj (x : V) (y : V))
    infer_instance
  have hAdm (c : I) : IsAdmissibleRootedTree (rootedChildComponent G v c.1).toSimpleGraph
      (fun x => weight (x : V)) (rootedChildRoot G v c.1) := by
    have hvc : G.Adj v c.1 := by
      have hc := c.property
      obtain ⟨hvc, _⟩ := by
        simpa only [rootedChildren, Finset.mem_filter, Finset.mem_univ, true_and] using hc
      exact hvc
    have hraw := rootedChildComponent_isAdmissible_of_unique_underweight G weight v c.1 h_tree
      h_positive h_unique_underweight hv h_two hvc
    exact (isAdmissibleRootedTree_instance_irrel _ _ _ _ _ _ _ _ _).mp hraw
  by_cases hp : 1 ≤ z v
  · have hpoint (c : I) :
        0 ≤ (↑(treePairing (rootedChildComponent G v c.1).toSimpleGraph
          (fun x => weight (x : V)) (fun x => z (x : V)) (fun x => z (x : V))) : ℚ) -
          (2 * (z v : ℚ) + 1) * (z (rootedChildRoot G v c.1) : ℚ) +
            rootedChildCapacitySummand G h_tree weight v c * (z v : ℚ) * ((z v : ℚ) + 1) := by
      have h := rooted_integer_estimate (rootedChildComponent G v c.1).toSimpleGraph
        (fun x => weight (x : V)) (rootedChildRoot G v c.1) (hAdm c)
        (fun x => z (x : V)) (z v)
      convert h using 1
      unfold rootedChildCapacitySummand
      exact congrArg (fun t : ℚ =>
        (↑(treePairing (rootedChildComponent G v c.1).toSimpleGraph
          (fun x => weight (x : V)) (fun x => z (x : V)) (fun x => z (x : V))) : ℚ) -
          (2 * (z v : ℚ) + 1) * (z (rootedChildRoot G v c.1) : ℚ) +
            t * (z v : ℚ) * ((z v : ℚ) + 1))
        (rootedCapacity_instance_irrel _ _ _ _ _ _ _ _ _)
    have hsum : 0 ≤ (∑ c : I, ((↑(treePairing (rootedChildComponent G v c.1).toSimpleGraph
          (fun x => weight (x : V)) (fun x => z (x : V)) (fun x => z (x : V))) : ℚ) -
          (2 * (z v : ℚ) + 1) * (z (rootedChildRoot G v c.1) : ℚ) +
            rootedChildCapacitySummand G h_tree weight v c * (z v : ℚ) * ((z v : ℚ) + 1))) := by
      exact Finset.sum_nonneg fun c _ => hpoint c
    have hgap := rootedChildCapacitySum_lt_weight_of_unique_underweight G h_tree weight v
      h_positive h_unique_underweight hv h_two
    have hfac : 0 < (z v : ℚ) * ((z v : ℚ) + 1) := by
      have hpQ : (1 : ℚ) ≤ z v := by exact_mod_cast hp
      nlinarith
    have hgapfac : 0 < ((weight v : ℚ) - rootedChildCapacitySum G h_tree weight v) *
        ((z v : ℚ) * ((z v : ℚ) + 1)) := by
      exact mul_pos (sub_pos.mpr hgap) hfac
    have hsum' : 0 ≤
        (∑ c : I, ((↑(treePairing (rootedChildComponent G v c.1).toSimpleGraph
            (fun x => weight (x : V)) (fun x => z (x : V)) (fun x => z (x : V))) : ℚ) -
            (2 * (z v : ℚ) + 1) * (z (rootedChildRoot G v c.1) : ℚ))) +
          ∑ c : I, rootedChildCapacitySummand G h_tree weight v c *
            (z v : ℚ) * ((z v : ℚ) + 1) := by
      rw [← Finset.sum_add_distrib]
      exact hsum
    have hcapfac : (∑ c : I, rootedChildCapacitySummand G h_tree weight v c *
        (z v : ℚ) * ((z v : ℚ) + 1)) = rootedChildCapacitySum G h_tree weight v *
          ((z v : ℚ) * ((z v : ℚ) + 1)) := by
      have hF : (inferInstance : Fintype I) =
          Finset.Subtype.fintype (rootedChildren G h_tree v v) := Subsingleton.elim _ _
      unfold rootedChildCapacitySum
      rw [← hF]
      simp_rw [mul_assoc]
      rw [Finset.sum_mul]
    rw [hcapfac] at hsum'
    have hposQ : 0 < (weight v : ℚ) * (z v : ℚ) * ((z v : ℚ) + 1) +
        (∑ c : I, ((↑(treePairing (rootedChildComponent G v c.1).toSimpleGraph
            (fun x => weight (x : V)) (fun x => z (x : V)) (fun x => z (x : V))) : ℚ) -
            (2 * (z v : ℚ) + 1) * (z (rootedChildRoot G v c.1) : ℚ))) := by
      nlinarith
    have hF : (inferInstance : Fintype I) =
        Finset.Subtype.fintype (rootedChildren G h_tree v v) := Subsingleton.elim _ _
    rw [← hF]
    exact_mod_cast hposQ
  · have hp0 : z v = 0 := by omega
    have hterm_nonneg (c : I) :
        0 ≤ treePairing (rootedChildComponent G v c.1).toSimpleGraph
          (fun x => weight (x : V)) (fun x => z (x : V)) (fun x => z (x : V)) -
          z (rootedChildRoot G v c.1) := by
      by_cases hc : (fun x : rootedChildComponent G v c.1 => z (x : V)) = 0
      · have hpair : treePairing (rootedChildComponent G v c.1).toSimpleGraph
            (fun x => weight (x : V)) (fun x => z (x : V)) (fun x => z (x : V)) = 0 := by
          rw [hc]
          unfold treePairing
          simp
        have hroot : z (rootedChildRoot G v c.1) = 0 := by
          exact congrFun hc _
        omega
      · exact le_of_lt (sub_pos.mpr (root_coefficient_lt_norm
          (rootedChildComponent G v c.1).toSimpleGraph (fun x => weight (x : V))
          (rootedChildRoot G v c.1) (hAdm c) (fun x => z (x : V)) hc))
    have hnonzero_component : ∃ c : I,
        (fun x : rootedChildComponent G v c.1 => z (x : V)) ≠ 0 := by
      by_contra hnone
      push Not at hnone
      apply hz_nonzero
      funext x
      by_cases hx : x = v
      · subst x
        exact hp0
      · obtain ⟨c, ⟨hcchild, hxC⟩, _⟩ := rootedChildComponent_partition G h_tree v x hx
        let cI : I := ⟨c, hcchild⟩
        have hzero := hnone cI
        exact congrFun hzero ⟨x, hxC⟩
    obtain ⟨c, hc⟩ := hnonzero_component
    have hterm_pos : 0 < treePairing (rootedChildComponent G v c.1).toSimpleGraph
        (fun x => weight (x : V)) (fun x => z (x : V)) (fun x => z (x : V)) -
        z (rootedChildRoot G v c.1) := by
      exact sub_pos.mpr (root_coefficient_lt_norm
        (rootedChildComponent G v c.1).toSimpleGraph (fun x => weight (x : V))
        (rootedChildRoot G v c.1) (hAdm c) (fun x => z (x : V)) hc)
    have hsum_pos : 0 < ∑ c : I,
        (treePairing (rootedChildComponent G v c.1).toSimpleGraph
          (fun x => weight (x : V)) (fun x => z (x : V)) (fun x => z (x : V)) -
          z (rootedChildRoot G v c.1)) := by
      exact lt_of_lt_of_le hterm_pos
        (Finset.single_le_sum (fun i _ => hterm_nonneg i) (Finset.mem_univ c))
    have hF : (inferInstance : Fintype I) =
        Finset.Subtype.fintype (rootedChildren G h_tree v v) := Subsingleton.elim _ _
    rw [hp0]
    simp only [mul_zero, zero_mul, zero_add, one_mul]
    rw [← hF]
    exact hsum_pos
