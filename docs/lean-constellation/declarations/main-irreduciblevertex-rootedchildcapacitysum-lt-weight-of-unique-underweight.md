[← Public API](../PUBLIC_API.md) · [Public boundaries](../PUBLIC_BOUNDARIES.md) · [Complete graph](../DECLARATION_GRAPH.md)

# `rootedChildCapacitySum_lt_weight_of_unique_underweight`

At the unique underweighted vertex, the total capacity of attached rooted components is strictly below its weight.

- Kind: `lemma`
- Node: `Main.IrreducibleVertex`
- Module: `PositiveDefiniteTreeLattice.Main.IrreducibleVertex.Lemmas.rootedChildCapacitySum_lt_weight_of_unique_underweight`
- State: `proved`
- Revision status: `committed`
- Repository completion: `graph_proved`
- Compatibility `formal_code`: final proof projection

## Statement NL

Let `V` be a finite type with decidable equality, let `G : SimpleGraph V` have decidable adjacency, let `weight : V → ℤ`, and let `v : V`. Suppose `h_tree : G.IsTree`, `h_positive : ∀ x : V → ℤ, x ≠ 0 → 0 < treePairing G weight x x`, `h_unique_underweight : ∃! u : V, weight u < (G.degree u : ℤ)`, `hv : weight v < (G.degree v : ℤ)`, and `h_two : ∀ x : V, 2 ≤ weight x`. Then the canonical sum of the capacities of the rooted child-side components at `v` is strictly below the integral weight at `v`, viewed in `ℚ`:

`rootedChildCapacitySum G h_tree weight v < (weight v : ℚ)`.

## Statement Formal

```lean
-- lean-constellation: managed-imports-begin
import PositiveDefiniteTreeLattice.Main.IrreducibleVertex.Prelude
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Finite
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `rootedChildCapacitySum_lt_weight_of_unique_underweight`

Let `V` be a finite type with decidable equality, let `G : SimpleGraph V` have decidable adjacency,
let `weight : V → ℤ`, and let `v : V`. Suppose `h_tree : G.IsTree`, `h_positive : ∀ x : V → ℤ, x ≠ 0
→ 0 < treePairing G weight x x`, `h_unique_underweight : ∃! u : V, weight u < (G.degree u : ℤ)`, `hv
: weight v < (G.degree v : ℤ)`, and `h_two : ∀ x : V, 2 ≤ weight x`. Then the canonical sum of the
capacities of the rooted child-side components at `v` is strictly below the integral weight at `v`,
viewed in `ℚ`:

`rootedChildCapacitySum G h_tree weight v < (weight v : ℚ)`.

## Sources

- Source `solution.tex`, lines 204–208

## Statement dependencies

- `SimpleGraph.IsTree` from `Mathlib.Combinatorics.SimpleGraph.Acyclic`
- `SimpleGraph.degree` from `Mathlib.Combinatorics.SimpleGraph.Finite`
- `Main.LatticeFoundations::treePairingAnchor` → `PositiveDefiniteTreeLattice.treePairing` from
  `PositiveDefiniteTreeLattice.Main.LatticeFoundations.Defs.treePairingAnchor`
- `Main.RootedCapacity::rootedChildCapacitySum` → `rootedChildCapacitySum` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildCapacitySum`
-/
lemma rootedChildCapacitySum_lt_weight_of_unique_underweight
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.IsTree) (weight : V → ℤ) (v : V)
    (h_positive : ∀ x : V → ℤ, x ≠ 0 →
      0 < PositiveDefiniteTreeLattice.treePairing G weight x x)
    (h_unique_underweight : ∃! u : V, weight u < (G.degree u : ℤ))
    (hv : weight v < (G.degree v : ℤ)) (h_two : ∀ x : V, 2 ≤ weight x) :
    rootedChildCapacitySum G hG weight v < (weight v : ℚ) := by
  sorry
```

## Proof NL

Work classically, preserving the accepted parameters G, hG, weight, v, h_positive, h_unique_underweight, hv, and h_two. Define:
- R := {x : V // x ≠ v}
- I := {c : V // c ∈ rootedChildren G hG v v}
- S := Σ c : I, rootedChildComponent G v c.1
- D := (rootedGram G weight).submatrix Subtype.val Subtype.val : Matrix R R ℚ.

Use exactly the finite, decidable-equality, and restricted-adjacency instances of rootedNonrootGram_reindex_childBlocks_inv_of_child_admissible, so its I, S, and child matrices are definitionally the present ones.

For each c : I, unpack c.property with rootedChildren to get hvc : G.Adj v c.1. The proved theorem PositiveDefiniteTreeLattice.rootedChildComponent_isAdmissible_of_unique_underweight G weight v c.1 hG h_positive h_unique_underweight hv h_two hvc supplies the exact pointwise premise of rootedNonrootGram_reindex_childBlocks_inv_of_child_admissible. Instantiate it:
Matrix.reindex e e D⁻¹ = Matrix.blockDiagonal' (fun c => (B c)⁻¹),
where e = (rootedChildComponentsEquivNonroot G hG v).symm and B c is the rooted Gram matrix of the c-component.

Establish invertibility before using D⁻¹. Let hQ := PositiveDefiniteTreeLattice.rootedGram_posDef_of_integer_positive G weight h_positive. By the exact principal-submatrix transport
hDpos : Matrix.PosDef D := hQ.submatrix Subtype.val_injective
from Matrix.PosDef.submatrix, D is positive definite; it is definitionally the nonroot lower-right block in rootedGram_reindex_rootNonroot_blocks G weight v. Hence hDunit : IsUnit D := hDpos.isUnit by Matrix.PosDef.isUnit. Install the local instance letI : Invertible D := hDunit.invertible using IsUnit.invertible. Then Matrix.mul_inv_cancel_right_of_invertible (A := D) (1 : Matrix R R ℚ), composed with Matrix.mulVec_mulVec, yields the concrete cancellation:
D *ᵥ (D⁻¹ *ᵥ z) = z for every z : R → ℚ.
Thus no inverse cancellation or ambient rooted admissibility is assumed.

Let η := Equiv.sumCompl (fun x : V => x = v) and M := Matrix.reindex η.symm η.symm (rootedGram G weight). Rewrite M with rootedGram_reindex_rootNonroot_blocks G weight v as Matrix.fromBlocks A B C D, with the root type left and R right. Transport strict positivity explicitly: for x : {x : V // x = v} ⊕ R → ℚ, apply hQ.dotProduct_mulVec_pos to x ∘ η.symm. Rewrite its quadratic form using Matrix.reindex_apply and Matrix.dotProduct_mulVec. This proves the required positive-definite inequality for M rather than assuming it after reindexing.

Let r₀ : {x : V // x = v} := ⟨v, rfl⟩ and choose x with x (Sum.inl r₀) = 1 and x (Sum.inr r) = -(D⁻¹ *ᵥ Ccol) r, where Ccol r := C r r₀. This x is nonzero at Sum.inl r₀. Expand M *ᵥ x using Matrix.fromBlocks_mulVec and the exact entry lemmas Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, and Matrix.fromBlocks_apply₂₁. The root diagonal is explicit: the block identity reduces A r₀ r₀ to rootedGram G weight v v, and simp [rootedGram, treePairing_vertexVector_vertexVector G hG weight v v] proves A r₀ r₀ = (weight v : ℚ). With D *ᵥ (D⁻¹ *ᵥ Ccol) = Ccol, the expanded dot product normalizes to:
0 < (weight v : ℚ) - ∑ r : R, B r₀ r * (D⁻¹ *ᵥ Ccol) r.
This is the strict source Schur-complement inequality, not a semidefinite replacement.

Compute the inverse scalar precisely. Use Matrix.reindex_apply and rootedChildComponentsEquivNonroot_apply at every sigma coordinate ⟨c, x⟩ : S, so it is exactly the coerced nonroot vertex with its supplied proof of inequality to v. Expand the two products with Matrix.mul_apply and rewrite the sums over S using Fintype.sum_sigma. Apply Matrix.blockDiagonal'_apply': for distinct outer child indices its if_neg branch is zero, which removes every off-diagonal child term. On a fixed c-block, the pointwise and summation conclusions of rootedGram_root_rootedChildComponent_support G hG weight v c reduce the root row and column to -1 at rootedChildRoot G v c.1 and zero elsewhere. Finset.sum_eq_single collapses each supported fiber. Therefore:
∑ r : R, B r₀ r * (D⁻¹ *ᵥ Ccol) r
= ∑ c : I, (B c)⁻¹ (rootedChildRoot G v c.1) (rootedChildRoot G v c.1).

Finally unfold rootedChildCapacitySum, rootedChildCapacitySummand, and rootedCapacity. The right-hand side is definitionally rootedChildCapacitySum G hG weight v. Substitute it into the strict inequality and rearrange to conclude exactly rootedChildCapacitySum G hG weight v < (weight v : ℚ).

## Proof Formal

```lean
-- lean-constellation: managed-imports-begin
import PositiveDefiniteTreeLattice.Main.IrreducibleVertex.Prelude
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Invertible.Basic
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Logic.Equiv.Sum
import PositiveDefiniteTreeLattice.Main.IrreducibleVertex.Lemmas.rootedChildComponent_isAdmissible_of_unique_underweight
import PositiveDefiniteTreeLattice.Main.IrreducibleVertex.Lemmas.rootedGram_posDef_of_integer_positive
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `rootedChildCapacitySum_lt_weight_of_unique_underweight`

Let `V` be a finite type with decidable equality, let `G : SimpleGraph V` have decidable adjacency,
let `weight : V → ℤ`, and let `v : V`. Suppose `h_tree : G.IsTree`, `h_positive : ∀ x : V → ℤ, x ≠ 0
→ 0 < treePairing G weight x x`, `h_unique_underweight : ∃! u : V, weight u < (G.degree u : ℤ)`, `hv
: weight v < (G.degree v : ℤ)`, and `h_two : ∀ x : V, 2 ≤ weight x`. Then the canonical sum of the
capacities of the rooted child-side components at `v` is strictly below the integral weight at `v`,
viewed in `ℚ`:

`rootedChildCapacitySum G h_tree weight v < (weight v : ℚ)`.

## Sources

- Source `solution.tex`, lines 204–208

## Statement dependencies

- `SimpleGraph.IsTree` from `Mathlib.Combinatorics.SimpleGraph.Acyclic`
- `SimpleGraph.degree` from `Mathlib.Combinatorics.SimpleGraph.Finite`
- `Main.LatticeFoundations::treePairingAnchor` → `PositiveDefiniteTreeLattice.treePairing` from
  `PositiveDefiniteTreeLattice.Main.LatticeFoundations.Defs.treePairingAnchor`
- `Main.RootedCapacity::rootedChildCapacitySum` → `rootedChildCapacitySum` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildCapacitySum`

## Proof outline

Work classically, preserving the accepted parameters G, hG, weight, v, h_positive,
h_unique_underweight, hv, and h_two. Define:
- R := {x : V // x ≠ v}
- I := {c : V // c ∈ rootedChildren G hG v v}
- S := Σ c : I, rootedChildComponent G v c.1
- D := (rootedGram G weight).submatrix Subtype.val Subtype.val : Matrix R R ℚ.

Use exactly the finite, decidable-equality, and restricted-adjacency instances of
rootedNonrootGram_reindex_childBlocks_inv_of_child_admissible, so its I, S, and child matrices are
definitionally the present ones.

For each c : I, unpack c.property with rootedChildren to get hvc : G.Adj v c.1. The proved theorem
PositiveDefiniteTreeLattice.rootedChildComponent_isAdmissible_of_unique_underweight G weight v c.1
hG h_positive h_unique_underweight hv h_two hvc supplies the exact pointwise premise of
rootedNonrootGram_reindex_childBlocks_inv_of_child_admissible. Instantiate it:
Matrix.reindex e e D⁻¹ = Matrix.blockDiagonal' (fun c => (B c)⁻¹),
where e = (rootedChildComponentsEquivNonroot G hG v).symm and B c is the rooted Gram matrix of the
c-component.

Establish invertibility before using D⁻¹. Let hQ :=
PositiveDefiniteTreeLattice.rootedGram_posDef_of_integer_positive G weight h_positive. By the exact
principal-submatrix transport
hDpos : Matrix.PosDef D := hQ.submatrix Subtype.val_injective
from Matrix.PosDef.submatrix, D is positive definite; it is definitionally the nonroot lower-right
block in rootedGram_reindex_rootNonroot_blocks G weight v. Hence hDunit : IsUnit D := hDpos.isUnit
by Matrix.PosDef.isUnit. Install the local instance letI : Invertible D := hDunit.invertible using
IsUnit.invertible. Then Matrix.mul_inv_cancel_right_of_invertible (A := D) (1 : Matrix R R ℚ),
composed with Matrix.mulVec_mulVec, yields the concrete cancellation:
D *ᵥ (D⁻¹ *ᵥ z) = z for every z : R → ℚ.
Thus no inverse cancellation or ambient rooted admissibility is assumed.

Let η := Equiv.sumCompl (fun x : V => x = v) and M := Matrix.reindex η.symm η.symm (rootedGram G
weight). Rewrite M with rootedGram_reindex_rootNonroot_blocks G weight v as Matrix.fromBlocks A B C
D, with the root type left and R right. Transport strict positivity explicitly: for x : {x : V // x
= v} ⊕ R → ℚ, apply hQ.dotProduct_mulVec_pos to x ∘ η.symm. Rewrite its quadratic form using
Matrix.reindex_apply and Matrix.dotProduct_mulVec. This proves the required positive-definite
inequality for M rather than assuming it after reindexing.

Let r₀ : {x : V // x = v} := ⟨v, rfl⟩ and choose x with x (Sum.inl r₀) = 1 and x (Sum.inr r) = -(D⁻¹
*ᵥ Ccol) r, where Ccol r := C r r₀. This x is nonzero at Sum.inl r₀. Expand M *ᵥ x using
Matrix.fromBlocks_mulVec and the exact entry lemmas Matrix.fromBlocks_apply₁₁,
Matrix.fromBlocks_apply₁₂, and Matrix.fromBlocks_apply₂₁. The root diagonal is explicit: the block
identity reduces A r₀ r₀ to rootedGram G weight v v, and simp [rootedGram,
treePairing_vertexVector_vertexVector G hG weight v v] proves A r₀ r₀ = (weight v : ℚ). With D *ᵥ
(D⁻¹ *ᵥ Ccol) = Ccol, the expanded dot product normalizes to:
0 < (weight v : ℚ) - ∑ r : R, B r₀ r * (D⁻¹ *ᵥ Ccol) r.
This is the strict source Schur-complement inequality, not a semidefinite replacement.

Compute the inverse scalar precisely. Use Matrix.reindex_apply and
rootedChildComponentsEquivNonroot_apply at every sigma coordinate ⟨c, x⟩ : S, so it is exactly the
coerced nonroot vertex with its supplied proof of inequality to v. Expand the two products with
Matrix.mul_apply and rewrite the sums over S using Fintype.sum_sigma. Apply
Matrix.blockDiagonal'_apply': for distinct outer child indices its if_neg branch is zero, which
removes every off-diagonal child term. On a fixed c-block, the pointwise and summation conclusions
of rootedGram_root_rootedChildComponent_support G hG weight v c reduce the root row and column to -1
at rootedChildRoot G v c.1 and zero elsewhere. Finset.sum_eq_single collapses each supported fiber.
Therefore:
∑ r : R, B r₀ r * (D⁻¹ *ᵥ Ccol) r
= ∑ c : I, (B c)⁻¹ (rootedChildRoot G v c.1) (rootedChildRoot G v c.1).

Finally unfold rootedChildCapacitySum, rootedChildCapacitySummand, and rootedCapacity. The
right-hand side is definitionally rootedChildCapacitySum G hG weight v. Substitute it into the
strict inequality and rearrange to conclude exactly rootedChildCapacitySum G hG weight v < (weight v
: ℚ).

## Proof sources

- Source `solution.tex`, lines 204–208

## Proof dependencies

- `Finset.sum_eq_single` from `Mathlib.Algebra.BigOperators.Group.Finset.Basic`
- `Fintype.sum_unique` from `Mathlib.Algebra.BigOperators.Group.Finset.Basic`
- `IsUnit.invertible` from `Mathlib.Algebra.Group.Invertible.Basic`
- `Fintype.sum_sigma` from `Mathlib.Data.Fintype.BigOperators`
- `Matrix.blockDiagonal'_apply'` from `Mathlib.Data.Matrix.Block`
- `Matrix.fromBlocks_apply₁₁` from `Mathlib.Data.Matrix.Block`
- `Matrix.fromBlocks_apply₁₂` from `Mathlib.Data.Matrix.Block`
- `Matrix.fromBlocks_apply₂₁` from `Mathlib.Data.Matrix.Block`
- `Matrix.fromBlocks_mulVec` from `Mathlib.Data.Matrix.Block`
- `Matrix.dotProduct_mulVec` from `Mathlib.Data.Matrix.Mul`
- `Matrix.mulVec_mulVec` from `Mathlib.Data.Matrix.Mul`
- `Matrix.mul_apply` from `Mathlib.Data.Matrix.Mul`
- `Matrix.reindex_apply` from `Mathlib.LinearAlgebra.Matrix.Defs`
- `Matrix.schur_complement_eq₂₂` from `Mathlib.LinearAlgebra.Matrix.Hermitian`
- `Matrix.mul_inv_cancel_right_of_invertible` from `Mathlib.LinearAlgebra.Matrix.NonsingularInverse`
- `Matrix.PosDef` from `Mathlib.LinearAlgebra.Matrix.PosDef`
- `Matrix.PosDef.dotProduct_mulVec_pos` from `Mathlib.LinearAlgebra.Matrix.PosDef`
- `Matrix.PosDef.isUnit` from `Mathlib.LinearAlgebra.Matrix.PosDef`
- `Matrix.PosDef.submatrix` from `Mathlib.LinearAlgebra.Matrix.PosDef`
- `Equiv.sumCompl` from `Mathlib.Logic.Equiv.Sum`
- `Main.IrreducibleVertex::rootedChildComponent_isAdmissible_of_unique_underweight` →
  `PositiveDefiniteTreeLattice.rootedChildComponent_isAdmissible_of_unique_underweight` from `Positi
  veDefiniteTreeLattice.Main.IrreducibleVertex.Lemmas.rootedChildComponent_isAdmissible_of_unique_un
  derweight`
- `Main.IrreducibleVertex::rootedGram_posDef_of_integer_positive` →
  `PositiveDefiniteTreeLattice.rootedGram_posDef_of_integer_positive` from
  `PositiveDefiniteTreeLattice.Main.IrreducibleVertex.Lemmas.rootedGram_posDef_of_integer_positive`
- `Main.RootedCapacity::isAdmissibleRootedTree_instance_irrel` →
  `isAdmissibleRootedTree_instance_irrel` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.isAdmissibleRootedTree_instance_irrel`
- `Main.RootedCapacity::rootedCapacity` → `rootedCapacity` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedCapacity`
- `Main.RootedCapacity::rootedCapacity_instance_irrel` → `rootedCapacity_instance_irrel` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.rootedCapacity_instance_irrel`
- `Main.RootedCapacity::rootedChildCapacitySum` → `rootedChildCapacitySum` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildCapacitySum`
- `Main.RootedCapacity::rootedChildCapacitySummand` → `rootedChildCapacitySummand` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildCapacitySummand`
- `Main.RootedCapacity::rootedChildComponent` → `rootedChildComponent` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildComponent`
- `Main.RootedCapacity::rootedChildComponentsEquivNonroot_apply` →
  `rootedChildComponentsEquivNonroot_apply` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.rootedChildComponentsEquivNonroot_apply`
- `Main.RootedCapacity::rootedChildRoot` → `rootedChildRoot` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildRoot`
- `Main.RootedCapacity::rootedChildren` → `rootedChildren` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildren`
- `Main.RootedCapacity::rootedGram` → `rootedGram` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedGram`
- `Main.RootedCapacity::rootedGram_reindex_rootNonroot_blocks` →
  `rootedGram_reindex_rootNonroot_blocks` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.rootedGram_reindex_rootNonroot_blocks`
- `Main.RootedCapacity::rootedGram_root_rootedChildComponent_support` →
  `rootedGram_root_rootedChildComponent_support` from `PositiveDefiniteTreeLattice.Main.RootedCapaci
  ty.Theorems.rootedGram_root_rootedChildComponent_support`
- `Main.RootedCapacity::rootedNonrootGram_reindex_childBlocks_inv_of_child_admissible` →
  `rootedNonrootGram_reindex_childBlocks_inv_of_child_admissible` from `PositiveDefiniteTreeLattice.
  Main.RootedCapacity.Theorems.rootedNonrootGram_reindex_childBlocks_inv_of_child_admissible`
- `Main.RootedCapacity::treePairing_vertexVector_vertexVector` →
  `treePairing_vertexVector_vertexVector` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.treePairing_vertexVector_vertexVector`
-/
lemma rootedChildCapacitySum_lt_weight_of_unique_underweight
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.IsTree) (weight : V → ℤ) (v : V)
    (h_positive : ∀ x : V → ℤ, x ≠ 0 →
      0 < PositiveDefiniteTreeLattice.treePairing G weight x x)
    (h_unique_underweight : ∃! u : V, weight u < (G.degree u : ℤ))
    (hv : weight v < (G.degree v : ℤ)) (h_two : ∀ x : V, 2 ≤ weight x) :
    rootedChildCapacitySum G hG weight v < (weight v : ℚ) := by
  classical
  let R := {x : V // x ≠ v}
  let I := {c : V // c ∈ rootedChildren G hG v v}
  let S := Σ c : I, rootedChildComponent G v c.1
  let e : R ≃ S := (rootedChildComponentsEquivNonroot G hG v).symm
  let D : Matrix R R ℚ := (rootedGram G weight).submatrix Subtype.val Subtype.val
  letI : Fintype I := Fintype.ofFinite I
  letI : ∀ c : I, Fintype (rootedChildComponent G v c.1) :=
    fun c => Fintype.ofFinite _
  letI : ∀ c : I, DecidableEq (rootedChildComponent G v c.1) :=
    fun c => Classical.decEq _
  letI : ∀ c : I, DecidableRel (G.deleteEdges {s(v, c.1)}).Adj :=
    fun c => Classical.decRel _
  letI : ∀ c : I, DecidableRel (rootedChildComponent G v c.1).toSimpleGraph.Adj :=
    fun c => Classical.decRel _
  let B : ∀ c : I,
      Matrix (rootedChildComponent G v c.1) (rootedChildComponent G v c.1) ℚ := fun c =>
    rootedGram (rootedChildComponent G v c.1).toSimpleGraph (fun x => weight (x : V))
  have hChild : ∀ c : I, IsAdmissibleRootedTree (rootedChildComponent G v c.1).toSimpleGraph
      (fun x => weight (x : V)) (rootedChildRoot G v c.1) := by
    intro c
    obtain ⟨hvc, _⟩ := by
      simpa only [rootedChildren, Finset.mem_filter, Finset.mem_univ, true_and] using c.property
    have hraw := PositiveDefiniteTreeLattice.rootedChildComponent_isAdmissible_of_unique_underweight
      G weight v c.1 hG h_positive h_unique_underweight hv h_two hvc
    exact (isAdmissibleRootedTree_instance_irrel _ _ _ _ _ _ _ _ _).mp hraw
  have hBlock : Matrix.reindex e e D⁻¹ = Matrix.blockDiagonal' (fun c => (B c)⁻¹) := by
    exact rootedNonrootGram_reindex_childBlocks_inv_of_child_admissible G hG weight v hChild
  let U := {x : V // x = v}
  let A : Matrix U U ℚ := (rootedGram G weight).submatrix Subtype.val Subtype.val
  let B₀ : Matrix U R ℚ := (rootedGram G weight).submatrix Subtype.val Subtype.val
  let C : Matrix R U ℚ := (rootedGram G weight).submatrix Subtype.val Subtype.val
  let r : U := ⟨v, rfl⟩
  have hDinv (j x : R) : D⁻¹ j x =
      Matrix.blockDiagonal' (fun c => (B c)⁻¹) (e j) (e x) := by
    have h := congrFun (congrFun hBlock (e j)) (e x)
    change D⁻¹ (e.symm (e j)) (e.symm (e x)) =
      Matrix.blockDiagonal' (fun c => (B c)⁻¹) (e j) (e x) at h
    simpa using h
  have hinner (c : I) (x : rootedChildComponent G v c.1) :
      ∑ t : S, B₀ r (e.symm t) *
        Matrix.blockDiagonal' (fun c => (B c)⁻¹) t ⟨c, x⟩ =
          -((B c)⁻¹ (rootedChildRoot G v c.1) x) := by
    rw [Fintype.sum_sigma]
    rw [Finset.sum_eq_single c]
    · simp only [Matrix.blockDiagonal'_apply', dif_pos]
      have hc : G.Adj v c.1 := by
        have hc' := c.property
        obtain ⟨hc, _⟩ := by
          simpa only [rootedChildren, Finset.mem_filter, Finset.mem_univ, true_and] using hc'
        exact hc
      have he (y : rootedChildComponent G v c.1) :
          e.symm ⟨c, y⟩ =
            ⟨(y : V), rootedChildComponent_parent_not_mem G v c.1 hG hc y⟩ := by
        change rootedChildComponentsEquivNonroot G hG v ⟨c, y⟩ = _
        exact rootedChildComponentsEquivNonroot_apply G hG v c y
      have hsupport := (rootedGram_root_rootedChildComponent_support G hG weight v c).2
      convert (hsupport (fun y => (B c)⁻¹ y x)).1 using 1
      · simp [B₀, r, Matrix.submatrix_apply, he]
    · intro d _ hdc
      simp [Matrix.blockDiagonal'_apply', hdc]
    · simp
  have hcap (c : I) : (B c)⁻¹ (rootedChildRoot G v c.1) (rootedChildRoot G v c.1) =
      rootedChildCapacitySummand G hG weight v c := by
    unfold rootedChildCapacitySummand rootedCapacity B
    exact rootedCapacity_instance_irrel _ _ _ _ _ _ _ _ _
  have hquad : (B₀ * D⁻¹ * C) r r = rootedChildCapacitySum G hG weight v := by
    rw [Matrix.mul_apply (M := B₀ * D⁻¹) (N := C)]
    simp_rw [Matrix.mul_apply (M := B₀) (N := D⁻¹)]
    calc
      (∑ x : R, (∑ j : R, B₀ r j * D⁻¹ j x) * C x r) =
          ∑ x : R, (∑ j : R, B₀ r j *
            Matrix.blockDiagonal' (fun c => (B c)⁻¹) (e j) (e x)) * C x r := by
        apply Finset.sum_congr rfl
        intro x _
        congr 1
        apply Finset.sum_congr rfl
        intro j _
        rw [hDinv]
      _ = ∑ z : S, (∑ t : S, B₀ r (e.symm t) *
          Matrix.blockDiagonal' (fun c => (B c)⁻¹) t z) * C (e.symm z) r := by
        rw [← e.sum_comp]
        apply Finset.sum_congr rfl
        intro x _
        rw [← e.sum_comp]
        simp
      _ = ∑ c : I, ∑ x : rootedChildComponent G v c.1,
          (∑ t : S, B₀ r (e.symm t) *
            Matrix.blockDiagonal' (fun c => (B c)⁻¹) t ⟨c, x⟩) * C (e.symm ⟨c, x⟩) r := by
        rw [Fintype.sum_sigma]
      _ = rootedChildCapacitySum G hG weight v := by
        calc
          (∑ c : I, ∑ x : rootedChildComponent G v c.1,
              (∑ t : S, B₀ r (e.symm t) *
                Matrix.blockDiagonal' (fun c => (B c)⁻¹) t ⟨c, x⟩) * C (e.symm ⟨c, x⟩) r) =
              ∑ c : I, ∑ x : rootedChildComponent G v c.1,
                (-((B c)⁻¹ (rootedChildRoot G v c.1) x)) * C (e.symm ⟨c, x⟩) r := by
            apply Finset.sum_congr rfl
            intro c _
            apply Finset.sum_congr rfl
            intro x _
            rw [hinner]
          _ = ∑ c : I, (B c)⁻¹ (rootedChildRoot G v c.1) (rootedChildRoot G v c.1) := by
            apply Finset.sum_congr rfl
            intro c _
            have hc : G.Adj v c.1 := by
              have hc' := c.property
              obtain ⟨hc, _⟩ := by
                simpa only [rootedChildren, Finset.mem_filter, Finset.mem_univ, true_and]
                  using hc'
              exact hc
            have he (x : rootedChildComponent G v c.1) :
                e.symm ⟨c, x⟩ =
                  ⟨(x : V), rootedChildComponent_parent_not_mem G v c.1 hG hc x⟩ := by
              change rootedChildComponentsEquivNonroot G hG v ⟨c, x⟩ = _
              exact rootedChildComponentsEquivNonroot_apply G hG v c x
            have hsupport := (rootedGram_root_rootedChildComponent_support G hG weight v c).2
            convert (hsupport (fun x => -((B c)⁻¹ (rootedChildRoot G v c.1) x))).2 using 1
            · simp [C, r, Matrix.submatrix_apply, he]
            · simp
          _ = rootedChildCapacitySum G hG weight v := by
            unfold rootedChildCapacitySum
            have hF : (inferInstance : Fintype I) =
                Finset.Subtype.fintype (rootedChildren G hG v v) := Subsingleton.elim _ _
            rw [← hF]
            apply Finset.sum_congr rfl
            intro c _
            exact hcap c
  let η := Equiv.sumCompl (fun x : V => x = v)
  let M := Matrix.fromBlocks A B₀ C D
  have hM : Matrix.reindex η.symm η.symm (rootedGram G weight) = M := by
    dsimp [M, A, B₀, C, D, η]
    exact rootedGram_reindex_rootNonroot_blocks G weight v
  have hQ : Matrix.PosDef (rootedGram G weight) :=
    PositiveDefiniteTreeLattice.rootedGram_posDef_of_integer_positive G weight h_positive
  have hMPos : Matrix.PosDef M := by
    rw [← hM]
    exact hQ.submatrix η.injective
  have hDPos : Matrix.PosDef D := by
    dsimp [D]
    exact hQ.submatrix Subtype.val_injective
  have hC : C = Matrix.conjTranspose B₀ := by
    ext x y
    have h := congrFun (congrFun hMPos.1.eq (Sum.inr x)) (Sum.inl y)
    simpa only [M, Matrix.conjTranspose_apply, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₁₂] using h.symm
  letI : Invertible D := hDPos.isUnit.invertible
  let x₀ : U → ℚ := fun _ => 1
  let y₀ : R → ℚ := -(Matrix.mulVec (D⁻¹ * Matrix.conjTranspose B₀) x₀)
  let z : U ⊕ R → ℚ := Sum.elim x₀ y₀
  have hxy : z ≠ 0 := by
    intro hzero
    have hrzero := congrFun hzero (Sum.inl r)
    simp [z, x₀] at hrzero
  have hpos : 0 < dotProduct (star z)
      (Matrix.mulVec (Matrix.fromBlocks A B₀ (Matrix.conjTranspose B₀) D) z) := by
    rw [← hC]
    simpa only [M] using hMPos.dotProduct_mulVec_pos hxy
  have hsc := Matrix.schur_complement_eq₂₂ A B₀ x₀ y₀ hDPos.1
  have hpos' := hpos
  rw [Matrix.dotProduct_mulVec] at hpos'
  have hsc' : Matrix.vecMul z (Matrix.fromBlocks A B₀ (Matrix.conjTranspose B₀) D) ⬝ᵥ z =
      Matrix.vecMul x₀ (A - B₀ * D⁻¹ * Matrix.conjTranspose B₀) ⬝ᵥ x₀ := by
    simpa [z, y₀, Matrix.mulVec, Matrix.mul_assoc] using hsc
  have hschurpos : 0 < Matrix.vecMul x₀
      (A - B₀ * D⁻¹ * Matrix.conjTranspose B₀) ⬝ᵥ x₀ := by
    rw [← hsc']
    exact hpos'
  letI : Subsingleton U := ⟨fun x y => Subtype.ext (by simp [x.property, y.property])⟩
  letI : Unique U := { default := r, uniq := fun x => Subsingleton.elim _ _ }
  have hscalar (Q : Matrix U U ℚ) : Matrix.vecMul x₀ Q ⬝ᵥ x₀ = Q r r := by
    simp only [Matrix.vecMul, dotProduct, x₀]
    rw [Fintype.sum_unique, Fintype.sum_unique]
    simp [show (default : U) = r from Subsingleton.elim _ _]
  have hgap : 0 < A r r - (B₀ * D⁻¹ * C) r r := by
    have hgap' : 0 < ((A - B₀ * D⁻¹ * Matrix.conjTranspose B₀) r r) := by
      rw [← hscalar (A - B₀ * D⁻¹ * Matrix.conjTranspose B₀)]
      exact hschurpos
    rw [← hC] at hgap'
    simpa only [Matrix.sub_apply] using hgap'
  have hA : A r r = (weight v : ℚ) := by
    dsimp [A, r]
    unfold rootedGram
    rw [treePairing_vertexVector_vertexVector G hG weight]
    simp
  rw [hA, hquad] at hgap
  linarith
```

## Statement dependencies

- `Mathlib:Mathlib.Combinatorics.SimpleGraph.Acyclic.SimpleGraph.IsTree`
- `Mathlib:Mathlib.Combinatorics.SimpleGraph.Finite.SimpleGraph.degree`
- `current repo:Main.LatticeFoundations.treePairingAnchor`
- `current repo:Main.RootedCapacity.rootedChildCapacitySum`

## Proof dependencies

- `Mathlib:Mathlib.Algebra.BigOperators.Group.Finset.Basic.Finset.sum_eq_single`
- `Mathlib:Mathlib.Algebra.BigOperators.Group.Finset.Basic.Fintype.sum_unique`
- `Mathlib:Mathlib.Algebra.Group.Invertible.Basic.IsUnit.invertible`
- `Mathlib:Mathlib.Data.Fintype.BigOperators.Fintype.sum_sigma`
- `Mathlib:Mathlib.Data.Matrix.Block.Matrix.blockDiagonal'_apply'`
- `Mathlib:Mathlib.Data.Matrix.Block.Matrix.fromBlocks_apply₁₁`
- `Mathlib:Mathlib.Data.Matrix.Block.Matrix.fromBlocks_apply₁₂`
- `Mathlib:Mathlib.Data.Matrix.Block.Matrix.fromBlocks_apply₂₁`
- `Mathlib:Mathlib.Data.Matrix.Block.Matrix.fromBlocks_mulVec`
- `Mathlib:Mathlib.Data.Matrix.Mul.Matrix.dotProduct_mulVec`
- `Mathlib:Mathlib.Data.Matrix.Mul.Matrix.mulVec_mulVec`
- `Mathlib:Mathlib.Data.Matrix.Mul.Matrix.mul_apply`
- `Mathlib:Mathlib.LinearAlgebra.Matrix.Defs.Matrix.reindex_apply`
- `Mathlib:Mathlib.LinearAlgebra.Matrix.Hermitian.Matrix.schur_complement_eq₂₂`
- `Mathlib:Mathlib.LinearAlgebra.Matrix.NonsingularInverse.Matrix.mul_inv_cancel_right_of_invertible`
- `Mathlib:Mathlib.LinearAlgebra.Matrix.PosDef.Matrix.PosDef`
- `Mathlib:Mathlib.LinearAlgebra.Matrix.PosDef.Matrix.PosDef.dotProduct_mulVec_pos`
- `Mathlib:Mathlib.LinearAlgebra.Matrix.PosDef.Matrix.PosDef.isUnit`
- `Mathlib:Mathlib.LinearAlgebra.Matrix.PosDef.Matrix.PosDef.submatrix`
- `Mathlib:Mathlib.Logic.Equiv.Sum.Equiv.sumCompl`
- `current repo:Main.IrreducibleVertex.rootedChildComponent_isAdmissible_of_unique_underweight`
- `current repo:Main.IrreducibleVertex.rootedGram_posDef_of_integer_positive`
- `current repo:Main.RootedCapacity.isAdmissibleRootedTree_instance_irrel`
- `current repo:Main.RootedCapacity.rootedCapacity`
- `current repo:Main.RootedCapacity.rootedCapacity_instance_irrel`
- `current repo:Main.RootedCapacity.rootedChildCapacitySum`
- `current repo:Main.RootedCapacity.rootedChildCapacitySummand`
- `current repo:Main.RootedCapacity.rootedChildComponent`
- `current repo:Main.RootedCapacity.rootedChildComponentsEquivNonroot_apply`
- `current repo:Main.RootedCapacity.rootedChildRoot`
- `current repo:Main.RootedCapacity.rootedChildren`
- `current repo:Main.RootedCapacity.rootedGram`
- `current repo:Main.RootedCapacity.rootedGram_reindex_rootNonroot_blocks`
- `current repo:Main.RootedCapacity.rootedGram_root_rootedChildComponent_support`
- `current repo:Main.RootedCapacity.rootedNonrootGram_reindex_childBlocks_inv_of_child_admissible`
- `current repo:Main.RootedCapacity.treePairing_vertexVector_vertexVector`

## Sources

- `solution.tex:204-208`
