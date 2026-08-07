-- lean-constellation: managed-imports-begin
import PositiveDefiniteTreeLattice.Main.IrreducibleVertex.Prelude
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Int.Cast.Basic
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Matrix.Mul
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `pairing_decomposition_at_unique_underweight`

Let `V` be a finite type with decidable equality, let `G : SimpleGraph V` have decidable adjacency
and satisfy `h_tree : G.IsTree`, let `weight : V → ℤ`, and let `v : V` and `z : V → ℤ`. Put `p := z
v`. For each canonical child `c : {c // c ∈ rootedChildren G h_tree v v}`, use the direct
restriction `y_c : rootedChildComponent G v c.1 → ℤ` given by `y_c x = z (x : V)`, and put `s_c :=
y_c (rootedChildRoot G v c.1)`. Then

`treePairing G weight z z + treePairing G weight (vertexVector v) z`

equals

`weight v * p * (p + 1) + ∑ c : {c // c ∈ rootedChildren G h_tree v v}, (treePairing
(rootedChildComponent G v c.1).toSimpleGraph (fun x => weight (x : V)) y_c y_c - (2 * p + 1) *
s_c)`.

Here the finite sum is over exactly the provider-owned rooted-child subtype, and the component
pairing and root value use the direct restriction above.

## Sources

- Source `solution.tex`, lines 220–226

## Statement dependencies

- `Finset.sum` from `Mathlib.Algebra.BigOperators.Group.Finset.Defs`
- `SimpleGraph.IsTree` from `Mathlib.Combinatorics.SimpleGraph.Acyclic`
- `SimpleGraph.ConnectedComponent.toSimpleGraph` from
  `Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected`
- `Main.LatticeFoundations::treePairingAnchor` → `PositiveDefiniteTreeLattice.treePairing` from
  `PositiveDefiniteTreeLattice.Main.LatticeFoundations.Defs.treePairingAnchor`
- `Main.LatticeFoundations::vertexVectorAnchor` → `PositiveDefiniteTreeLattice.vertexVector` from
  `PositiveDefiniteTreeLattice.Main.LatticeFoundations.Defs.vertexVectorAnchor`
- `Main.RootedCapacity::rootedChildComponent` → `rootedChildComponent` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildComponent`
- `Main.RootedCapacity::rootedChildRoot` → `rootedChildRoot` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildRoot`
- `Main.RootedCapacity::rootedChildren` → `rootedChildren` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildren`

## Proof outline

Work classically and retain the provider-owned child index I = {c : V // c in rootedChildren G
h_tree v v}. For c : I let C_c = rootedChildComponent G v c.1, rho_c = rootedChildRoot G v c.1, and
y_c : C_c -> Int be exactly x |-> z (x : V), as in the formal statement. Let S be the sigma type of
pairs (c, x) with x : C_c, let R = {u : V // u != v}, and use the existing equivalence e =
(rootedChildComponentsEquivNonroot G h_tree v).symm : R equivalently S. No new restriction or
component wrapper is introduced.

First prove the elementary coordinate-expansion fact for the existing vertexVector API: every
integral function x : V -> Int is the finite sum over u of x u times vertexVector u. Pointwise,
Finset.sum_eq_single leaves exactly the u-coordinate. Apply treePairing_add_left,
treePairing_add_right, and the corresponding local scalar identities obtained by unfolding
treePairing once to derive the rational coordinate formula
cast(treePairing G weight x y)
= sum over a,b : V of cast(x a) * rootedGram G weight a b * cast(y b).
The same one-line coordinate calculation applies to each C_c and its restricted weight. This is only
a local cast normalization between the integral pairing and rootedGram; the final equation is
returned to Int.

Split the ambient double coordinate sum into the root coordinate v and the nonroot coordinates using
Finset.sum_erase_add. Reindex the nonroot coordinates through e.
rootedChildComponentsEquivNonroot_apply identifies the resulting coefficient at (c,x) with z (x :
V), i.e. the stated direct restriction y_c x. rootedChildComponent_parent_not_mem ensures no
component coordinate is the root coordinate. Fintype.sum_sigma flattens the reindexed sigma sum into
the outer finite sum over c : I and its C_c fibers.

For the nonroot/nonroot block, apply rootedNonrootGram_reindex_childBlocks pointwise.
Matrix.blockDiagonal'_apply' makes the c,d block zero when c != d, so every cross-child contribution
vanishes. In the c = d block, use rootedGram_rootedChildComponent to rewrite the remaining entry to
the component Gram entry, and use the component version of the coordinate formula. This produces
exactly
sum over c : I of cast(treePairing C_c restrictedWeight y_c y_c).

For the two root/nonroot sums, apply the finite-sum form of
rootedGram_root_rootedChildComponent_support to the rational coefficient function x |-> cast(y_c x).
It evaluates each root/component interaction to -cast(y_c rho_c). The root/root entry is weight v by
treePairing_vertexVector_self (equivalently treePairing_vertexVector_vertexVector). Combining the
root-root, two symmetric root/component, and diagonal component terms gives, after ring
normalization,
cast(treePairing G weight z z + treePairing G weight (vertexVector v) z)
= cast(weight v * z v * (z v + 1)
  + sum over c : I of
      (treePairing C_c restrictedWeight y_c y_c
       - (2 * z v + 1) * z rho_c)).
Use exact_mod_cast to conclude the accepted integral equality.

## Proof sources

- Source `solution.tex`, lines 220–226

## Proof dependencies

- `Finset.sum_biUnion` from `Mathlib.Algebra.BigOperators.Group.Finset.Basic`
- `Finset.sum_erase_add` from `Mathlib.Algebra.BigOperators.Group.Finset.Basic`
- `Equiv.sum_comp` from `Mathlib.Algebra.BigOperators.Group.Finset.Defs`
- `Int.cast_sum` from `Mathlib.Algebra.BigOperators.Ring.Finset`
- `Int.cast_mul` from `Mathlib.Algebra.Ring.Int.Defs`
- `Fintype.sum_sigma` from `Mathlib.Data.Fintype.BigOperators`
- `Int.cast_add` from `Mathlib.Data.Int.Cast.Basic`
- `Matrix.blockDiagonal'_apply'` from `Mathlib.Data.Matrix.Block`
- `Matrix.dotProduct_mulVec` from `Mathlib.Data.Matrix.Mul`
- `Matrix.mulVec_apply` from `Mathlib.Data.Matrix.Mul`
- `Main.LatticeFoundations::treePairing_add_left` →
  `PositiveDefiniteTreeLattice.treePairing_add_left` from
  `PositiveDefiniteTreeLattice.Main.LatticeFoundations.Theorems.treePairing_add_left`
- `Main.LatticeFoundations::treePairing_add_right` →
  `PositiveDefiniteTreeLattice.treePairing_add_right` from
  `PositiveDefiniteTreeLattice.Main.LatticeFoundations.Theorems.treePairing_add_right`
- `Main.LatticeFoundations::treePairing_symm` → `PositiveDefiniteTreeLattice.treePairing_symm` from
  `PositiveDefiniteTreeLattice.Main.LatticeFoundations.Theorems.treePairing_symm`
- `Main.LatticeFoundations::treePairing_vertexVector_self` →
  `PositiveDefiniteTreeLattice.treePairing_vertexVector_self` from
  `PositiveDefiniteTreeLattice.Main.LatticeFoundations.Theorems.treePairing_vertexVector_self`
- `Main.RootedCapacity::rootedChildComponent` → `rootedChildComponent` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildComponent`
- `Main.RootedCapacity::rootedChildComponent_parent_not_mem` → `rootedChildComponent_parent_not_mem`
  from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.rootedChildComponent_parent_not_mem`
- `Main.RootedCapacity::rootedChildComponent_partition` → `rootedChildComponent_partition` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.rootedChildComponent_partition`
- `Main.RootedCapacity::rootedChildComponentsEquivNonroot` → `rootedChildComponentsEquivNonroot`
  from `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildComponentsEquivNonroot`
- `Main.RootedCapacity::rootedChildComponentsEquivNonroot_apply` →
  `rootedChildComponentsEquivNonroot_apply` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.rootedChildComponentsEquivNonroot_apply`
- `Main.RootedCapacity::rootedChildRoot` → `rootedChildRoot` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildRoot`
- `Main.RootedCapacity::rootedChildren` → `rootedChildren` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildren`
- `Main.RootedCapacity::rootedGram` → `rootedGram` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedGram`
- `Main.RootedCapacity::rootedGram_bilinear_eq_treePairing_cast` →
  `rootedGram_bilinear_eq_treePairing_cast` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.rootedGram_bilinear_eq_treePairing_cast`
- `Main.RootedCapacity::rootedGram_root_nonroot_linear_eq_sum_childRoots` →
  `rootedGram_root_nonroot_linear_eq_sum_childRoots` from `PositiveDefiniteTreeLattice.Main.RootedCa
  pacity.Theorems.rootedGram_root_nonroot_linear_eq_sum_childRoots`
- `Main.RootedCapacity::rootedGram_root_rootedChildComponent_support` →
  `rootedGram_root_rootedChildComponent_support` from `PositiveDefiniteTreeLattice.Main.RootedCapaci
  ty.Theorems.rootedGram_root_rootedChildComponent_support`
- `Main.RootedCapacity::rootedGram_rootedChildComponent` → `rootedGram_rootedChildComponent` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.rootedGram_rootedChildComponent`
- `Main.RootedCapacity::rootedNonrootGram_reindex_childBlocks` →
  `rootedNonrootGram_reindex_childBlocks` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.rootedNonrootGram_reindex_childBlocks`
- `Main.RootedCapacity::rootedNonroot_quadratic_eq_sum_childQuadratics` →
  `rootedNonroot_quadratic_eq_sum_childQuadratics` from `PositiveDefiniteTreeLattice.Main.RootedCapa
  city.Theorems.rootedNonroot_quadratic_eq_sum_childQuadratics`
- `Main.RootedCapacity::treePairing_vertexVector_vertexVector` →
  `treePairing_vertexVector_vertexVector` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.treePairing_vertexVector_vertexVector`
-/
theorem PositiveDefiniteTreeLattice.pairing_decomposition_at_unique_underweight
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (h_tree : G.IsTree) (weight : V → ℤ) (v : V) (z : V → ℤ) :
    treePairing G weight z z + treePairing G weight (vertexVector v) z =
      weight v * z v * (z v + 1) +
        ∑ c : {c // c ∈ rootedChildren G h_tree v v},
          letI : Fintype (rootedChildComponent G v c.1) := Fintype.ofFinite _
          letI : DecidableRel (rootedChildComponent G v c.1).toSimpleGraph.Adj := by
            intro x y
            change Decidable ((G.deleteEdges {s(v, c.1)}).Adj (x : V) (y : V))
            infer_instance
          treePairing (rootedChildComponent G v c.1).toSimpleGraph
              (fun x => weight (x : V)) (fun x => z (x : V)) (fun x => z (x : V)) -
            (2 * z v + 1) * z (rootedChildRoot G v c.1) := by
  classical
  let R := {x : V // x ≠ v}
  let I := {c : V // c ∈ rootedChildren G h_tree v v}
  let S := Σ c : I, rootedChildComponent G v c.1
  let e : R ≃ S := (rootedChildComponentsEquivNonroot G h_tree v).symm
  let a : R → ℚ := fun x => (z x.1 : ℚ)
  have sum_split (f : V → ℚ) :
      (∑ x, f x) = f v + ∑ x : R, f x.1 := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ v)]
    rw [Finset.sum_subtype (p := fun x => x ≠ v) (Finset.univ.erase v) (by simp)]
    ring
  letI : ∀ c : I, Fintype (rootedChildComponent G v c.1) := fun c =>
    Fintype.ofFinite _
  letI : ∀ c : I, DecidableRel (rootedChildComponent G v c.1).toSimpleGraph.Adj := fun c => by
    intro x y
    change Decidable ((G.deleteEdges {s(v, c.1)}).Adj (x : V) (y : V))
    infer_instance
  have hquadratic := rootedNonroot_quadratic_eq_sum_childQuadratics G h_tree weight v a
  have hlinear := rootedGram_root_nonroot_linear_eq_sum_childRoots G h_tree weight v a
  have hbilinear := rootedGram_bilinear_eq_treePairing_cast G weight z z
  have hchild (c : I) := rootedGram_bilinear_eq_treePairing_cast
    (rootedChildComponent G v c.1).toSimpleGraph (fun x => weight (x : V))
    (fun x => z (x : V)) (fun x => z (x : V))
  simp only [a, Equiv.symm_symm, rootedChildComponentsEquivNonroot_apply] at hquadratic hlinear
  have hquadratic' := hquadratic.trans (Finset.sum_congr rfl fun c _ => hchild c)
  have hsplit :
      (∑ u : V, ∑ t : V, (z u : ℚ) * rootedGram G weight u t * (z t : ℚ)) =
        (z v : ℚ) * rootedGram G weight v v * (z v : ℚ) +
          (z v : ℚ) * (∑ r : R, rootedGram G weight v r.1 * (z r.1 : ℚ)) +
          (∑ r : R, (z r.1 : ℚ) * rootedGram G weight r.1 v) * (z v : ℚ) +
          ∑ r : R, ∑ s : R,
            (z r.1 : ℚ) * (rootedGram G weight).submatrix Subtype.val Subtype.val r s *
              (z s.1 : ℚ) := by
    calc
      _ = (∑ t : V, (z v : ℚ) * rootedGram G weight v t * (z t : ℚ)) +
          ∑ r : R, ∑ t : V, (z r.1 : ℚ) * rootedGram G weight r.1 t * (z t : ℚ) :=
        sum_split _
      _ = ((z v : ℚ) * rootedGram G weight v v * (z v : ℚ) +
          ∑ s : R, (z v : ℚ) * rootedGram G weight v s.1 * (z s.1 : ℚ)) +
          ∑ r : R, ((z r.1 : ℚ) * rootedGram G weight r.1 v * (z v : ℚ) +
            ∑ s : R, (z r.1 : ℚ) * rootedGram G weight r.1 s.1 * (z s.1 : ℚ)) := by
        rw [sum_split (fun t => (z v : ℚ) * rootedGram G weight v t * (z t : ℚ))]
        congr 1
        apply Finset.sum_congr rfl
        intro r _
        exact sum_split _
      _ = _ := by
        simp only [Matrix.submatrix_apply]
        rw [Finset.sum_add_distrib]
        rw [Finset.mul_sum, Finset.sum_mul]
        ring_nf
  have hroot := rootedGram_bilinear_eq_treePairing_cast G weight
    (vertexVector v) (vertexVector v)
  simp only [vertexVector, Int.cast_ite, Int.cast_one, Int.cast_zero, ite_mul, one_mul, zero_mul,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte,
    treePairing_vertexVector_self] at hroot
  have hpairvz := rootedGram_bilinear_eq_treePairing_cast G weight (vertexVector v) z
  simp only [vertexVector, Int.cast_ite, Int.cast_one, Int.cast_zero, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ,
    ↓reduceIte] at hpairvz
  apply (Int.cast_injective : Function.Injective (fun n : ℤ => (n : ℚ)))
  push_cast
  rw [← hbilinear, ← hpairvz, hsplit]
  rw [sum_split (fun x => rootedGram G weight v x * (z x : ℚ))]
  rw [hroot, hlinear.1, hlinear.2, hquadratic']
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring
