[← Public API](../PUBLIC_API.md) · [Public boundaries](../PUBLIC_BOUNDARIES.md)

# `rootedCapacity_recursion`

The rooted capacity is the reciprocal of the root weight minus the sum of child-component capacities.

- Kind: `theorem`
- Node: `Main.RootedCapacity`
- Module: `PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.rootedCapacity_recursion`
- State: `proved`
- Revision status: `committed`
- Repository completion: `graph_proved`
- Formal code: final proof projection

## Lean code

```lean
-- lean-constellation: managed-imports-begin
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Prelude
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Invertible.Basic
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Matrix.Diagonal
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Logic.Equiv.Sum
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.IsAdmissibleRootedTree
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedCapacity
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildCapacitySum
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedGram
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.rootedGram_reindex_rootNonroot_blocks
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.rootedGram_rootNonroot_blocks_invertible
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.rootedNonroot_inverse_quadratic
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.treePairing_vertexVector_vertexVector
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `rootedCapacity_recursion`

For every finite decidable vertex type `V`, simple graph `G` with decidable adjacency, tree witness
`hG : G.IsTree`, integer weight `w : V → ℤ`, root `ρ : V`, and admissibility witness `hAdm :
IsAdmissibleRootedTree G w ρ`, the existing rational rooted capacity satisfies
```
rootedCapacity G w ρ =
  1 / ((w ρ : ℚ) - rootedChildCapacitySum G hG w ρ).
```

This is the reciprocal Schur-complement recursion with the original rational total-inverse meaning
of `rootedCapacity` and the existing raw-root-child sum `rootedChildCapacitySum`.  In particular, it
introduces no nonzero-denominator hypothesis: the denominator is supplied by the positive-definite
rooted Gram situation already contained in `hAdm`.  The equality is oriented from capacity to the
exact scalar expression needed by the subsequent strict capacity bound.

## Sources

- Source `solution.tex`, lines 57–72

## Statement dependencies

- `SimpleGraph.IsTree` from `Mathlib.Combinatorics.SimpleGraph.Acyclic`
- `Main.RootedCapacity::IsAdmissibleRootedTree` → `IsAdmissibleRootedTree` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.IsAdmissibleRootedTree`
- `Main.RootedCapacity::rootedCapacity` → `rootedCapacity` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedCapacity`
- `Main.RootedCapacity::rootedChildCapacitySum` → `rootedChildCapacitySum` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildCapacitySum`

## Proof outline

Work classically. Destructure `hAdm` and use proof irrelevance to identify its stored tree
witness with the explicit `hG`; retain the resulting positive-definiteness proof
`hPos : Matrix.PosDef (rootedGram G w)`.

Let `R := {v : V // v ≠ ρ}` and use the root/nonroot equivalence
`e := Equiv.sumCompl (fun v : V => v = ρ)`. Reindex `rootedGram G w` along the corresponding
equivalence from `V` to the sum of the root singleton and `R`. By matrix extensionality and the
basis-entry formula, identify this reindexed matrix with
`Matrix.fromBlocks A B C D`, where `A` is the singleton root block with entry `(w ρ : ℚ)`,
`D = (rootedGram G w).submatrix Subtype.val Subtype.val`, and `B,C` are the exact root
row/column blocks. Keep this as a matrix equality; do not change the capacity or child-component
definitions.

Use `hPos.submatrix` on the nonroot inclusion to obtain `D.PosDef`, hence `D.isUnit`.
Transport `hPos.isUnit` across the reindex/block equality to get the full block matrix unit.
Install the resulting invertibility instances for `D` and `Matrix.fromBlocks A B C D`, and then
use `Matrix.invertibleOfFromBlocks₂₂Invertible A B C D` for the Schur complement
`S := A - B * ⅟D * C`. Thus no separate nonzero-denominator hypothesis is introduced.

Apply `Matrix.invOf_fromBlocks₂₂_eq A B C D`; its upper-left block is `⅟S`. Rewrite each
`invOf` to the rational total inverse using `Matrix.invOf_eq_nonsing_inv`, and use
`Matrix.inv_reindex` to transport the full inverse back to `(rootedGram G w)⁻¹`. Evaluate the
root singleton diagonal. Unfold only `rootedCapacity` at this final point and use
`Matrix.inv_subsingleton` plus singleton-block simplification to reduce that entry to the scalar
inverse of
`(w ρ : ℚ) - (B * D⁻¹ * C)` at the unique root index.

Finally expand the matrix product entry into its finite double sum. The root-row factor, inverse
entry, and root-column factor are exactly the formal left side of
`rootedNonroot_inverse_quadratic G hG w ρ hAdm`; rewrite it to
`rootedChildCapacitySum G hG w ρ`. Simplify the singleton scalar inverse to
`1 / ((w ρ : ℚ) - rootedChildCapacitySum G hG w ρ)`, preserving the stated orientation.

## Proof sources

- Source `solution.tex`, lines 57–72

## Proof dependencies

- `Finset.sum_congr` from `Mathlib.Algebra.BigOperators.Group.Finset.Basic`
- `Finset.sum_comm` from `Mathlib.Algebra.BigOperators.Group.Finset.Sigma`
- `Finset.sum_mul` from `Mathlib.Algebra.BigOperators.Ring.Finset`
- `inv_eq_one_div` from `Mathlib.Algebra.Group.Defs`
- `IsUnit.invertible` from `Mathlib.Algebra.Group.Invertible.Basic`
- `Ring.inverse_eq_inv` from `Mathlib.Algebra.GroupWithZero.Units.Basic`
- `Matrix.fromBlocks` from `Mathlib.Data.Matrix.Block`
- `Matrix.fromBlocks_apply₁₁` from `Mathlib.Data.Matrix.Block`
- `Matrix.diagonal_apply_eq` from `Mathlib.Data.Matrix.Diagonal`
- `Matrix.mul_apply` from `Mathlib.Data.Matrix.Mul`
- `Matrix.reindex_apply` from `Mathlib.LinearAlgebra.Matrix.Defs`
- `Matrix.sub_apply` from `Mathlib.LinearAlgebra.Matrix.Defs`
- `Matrix.submatrix_apply` from `Mathlib.LinearAlgebra.Matrix.Defs`
- `Matrix.invOf_eq_nonsing_inv` from `Mathlib.LinearAlgebra.Matrix.NonsingularInverse`
- `Matrix.inv_reindex` from `Mathlib.LinearAlgebra.Matrix.NonsingularInverse`
- `Matrix.inv_subsingleton` from `Mathlib.LinearAlgebra.Matrix.NonsingularInverse`
- `Matrix.PosDef.isUnit` from `Mathlib.LinearAlgebra.Matrix.PosDef`
- `Matrix.PosDef.submatrix` from `Mathlib.LinearAlgebra.Matrix.PosDef`
- `Matrix.invOf_fromBlocks₂₂_eq` from `Mathlib.LinearAlgebra.Matrix.SchurComplement`
- `Matrix.invertibleOfFromBlocks₂₂Invertible` from `Mathlib.LinearAlgebra.Matrix.SchurComplement`
- `Equiv.sumCompl` from `Mathlib.Logic.Equiv.Sum`
- `Main.RootedCapacity::IsAdmissibleRootedTree` → `IsAdmissibleRootedTree` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.IsAdmissibleRootedTree`
- `Main.RootedCapacity::rootedCapacity` → `rootedCapacity` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedCapacity`
- `Main.RootedCapacity::rootedChildCapacitySum` → `rootedChildCapacitySum` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildCapacitySum`
- `Main.RootedCapacity::rootedGram` → `rootedGram` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedGram`
- `Main.RootedCapacity::rootedGram_reindex_rootNonroot_blocks` →
  `rootedGram_reindex_rootNonroot_blocks` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.rootedGram_reindex_rootNonroot_blocks`
- `Main.RootedCapacity::rootedGram_rootNonroot_blocks_invertible` →
  `rootedGram_rootNonroot_blocks_invertible` from `PositiveDefiniteTreeLattice.Main.RootedCapacity.T
  heorems.rootedGram_rootNonroot_blocks_invertible`
- `Main.RootedCapacity::rootedNonroot_inverse_quadratic` → `rootedNonroot_inverse_quadratic` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.rootedNonroot_inverse_quadratic`
- `Main.RootedCapacity::treePairing_vertexVector_vertexVector` →
  `treePairing_vertexVector_vertexVector` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.treePairing_vertexVector_vertexVector`
-/
theorem rootedCapacity_recursion {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.IsTree) (w : V → ℤ) (ρ : V)
    (hAdm : IsAdmissibleRootedTree G w ρ) :
    rootedCapacity G w ρ = 1 / ((w ρ : ℚ) - rootedChildCapacitySum G hG w ρ) := by
  classical
  let U := {v : V // v = ρ}
  let R := {v : V // v ≠ ρ}
  let e := Equiv.sumCompl (fun v : V => v = ρ)
  let A : Matrix U U ℚ := (rootedGram G w).submatrix Subtype.val Subtype.val
  let B : Matrix U R ℚ := (rootedGram G w).submatrix Subtype.val Subtype.val
  let C : Matrix R U ℚ := (rootedGram G w).submatrix Subtype.val Subtype.val
  let D : Matrix R R ℚ := (rootedGram G w).submatrix Subtype.val Subtype.val
  let M := Matrix.fromBlocks A B C D
  let r : U := ⟨ρ, rfl⟩
  have hM : Matrix.reindex e.symm e.symm (rootedGram G w) = M := by
    dsimp [M, A, B, C, D, e]
    exact rootedGram_reindex_rootNonroot_blocks G w ρ
  have hPos : Matrix.PosDef (rootedGram G w) := by
    rcases hAdm with ⟨_, hPos, _, _⟩
    exact hPos
  have hPosD : Matrix.PosDef D := by
    dsimp [D]
    exact hPos.submatrix Subtype.val_injective
  have hUnitM : IsUnit M := by
    dsimp [M, A, B, C, D]
    exact rootedGram_rootNonroot_blocks_invertible G w ρ hAdm
  letI : Invertible D := hPosD.isUnit.invertible
  letI : Invertible M := hUnitM.invertible
  let S := A - B * ⅟D * C
  letI : Invertible S := Matrix.invertibleOfFromBlocks₂₂Invertible A B C D
  have hMinv : M⁻¹ = Matrix.reindex e.symm e.symm ((rootedGram G w)⁻¹) := by
    rw [← hM]
    exact Matrix.inv_reindex e.symm e.symm (rootedGram G w)
  have hSchur : M⁻¹ =
      Matrix.fromBlocks S⁻¹ (-(S⁻¹ * B * D⁻¹))
        (-(D⁻¹ * C * S⁻¹)) (D⁻¹ + D⁻¹ * C * S⁻¹ * B * D⁻¹) := by
    calc
      M⁻¹ = ⅟M := (Matrix.invOf_eq_nonsing_inv M).symm
      _ = Matrix.fromBlocks (⅟S) (-(⅟S * B * ⅟D))
          (-(⅟D * C * ⅟S)) (⅟D + ⅟D * C * ⅟S * B * ⅟D) :=
        Matrix.invOf_fromBlocks₂₂_eq A B C D
      _ = Matrix.fromBlocks S⁻¹ (-(S⁻¹ * B * D⁻¹))
          (-(D⁻¹ * C * S⁻¹)) (D⁻¹ + D⁻¹ * C * S⁻¹ * B * D⁻¹) := by
        rw [Matrix.invOf_eq_nonsing_inv S, Matrix.invOf_eq_nonsing_inv D]
  have hroot : (rootedGram G w)⁻¹ ρ ρ = M⁻¹ (.inl r) (.inl r) := by
    rw [hMinv, Matrix.reindex_apply]
    rfl
  have hquad : (B * D⁻¹ * C) r r = rootedChildCapacitySum G hG w ρ := by
    rw [Matrix.mul_apply (M := B * D⁻¹) (N := C)]
    simp_rw [Matrix.mul_apply (M := B) (N := D⁻¹)]
    calc
      (∑ x, (∑ j, B r j * D⁻¹ j x) * C x r) =
          ∑ x, ∑ j, (B r j * D⁻¹ j x) * C x r := by
        apply Finset.sum_congr rfl
        intro x hx
        exact Finset.sum_mul Finset.univ _ _
      _ = ∑ j, ∑ x, (B r j * D⁻¹ j x) * C x r := Finset.sum_comm
      _ = rootedChildCapacitySum G hG w ρ := by
        simpa only [B, C, D, r, Matrix.submatrix_apply] using
          rootedNonroot_inverse_quadratic G hG w ρ hAdm
  unfold rootedCapacity
  rw [hroot, hSchur, Matrix.fromBlocks_apply₁₁]
  rw [Matrix.inv_subsingleton S, Matrix.diagonal_apply_eq]
  dsimp only [S]
  rw [Matrix.sub_apply, Matrix.invOf_eq_nonsing_inv D]
  change Ring.inverse (A r r - (B * D⁻¹ * C) r r) = _
  rw [hquad]
  have hA : A r r = (w ρ : ℚ) := by
    dsimp [A, r]
    unfold rootedGram
    rw [treePairing_vertexVector_vertexVector G hG w]
    simp
  rw [hA]
  rw [Ring.inverse_eq_inv, inv_eq_one_div]
```

## Statement dependencies

- `Mathlib:Mathlib.Combinatorics.SimpleGraph.Acyclic.SimpleGraph.IsTree`
- `current repo:Main.RootedCapacity.IsAdmissibleRootedTree`
- `current repo:Main.RootedCapacity.rootedCapacity`
- `current repo:Main.RootedCapacity.rootedChildCapacitySum`

## Proof dependencies

- `Mathlib:Mathlib.Algebra.BigOperators.Group.Finset.Basic.Finset.sum_congr`
- `Mathlib:Mathlib.Algebra.BigOperators.Group.Finset.Sigma.Finset.sum_comm`
- `Mathlib:Mathlib.Algebra.BigOperators.Ring.Finset.Finset.sum_mul`
- `Mathlib:Mathlib.Algebra.Group.Defs.inv_eq_one_div`
- `Mathlib:Mathlib.Algebra.Group.Invertible.Basic.IsUnit.invertible`
- `Mathlib:Mathlib.Algebra.GroupWithZero.Units.Basic.Ring.inverse_eq_inv`
- `Mathlib:Mathlib.Data.Matrix.Block.Matrix.fromBlocks`
- `Mathlib:Mathlib.Data.Matrix.Block.Matrix.fromBlocks_apply₁₁`
- `Mathlib:Mathlib.Data.Matrix.Diagonal.Matrix.diagonal_apply_eq`
- `Mathlib:Mathlib.Data.Matrix.Mul.Matrix.mul_apply`
- `Mathlib:Mathlib.LinearAlgebra.Matrix.Defs.Matrix.reindex_apply`
- `Mathlib:Mathlib.LinearAlgebra.Matrix.Defs.Matrix.sub_apply`
- `Mathlib:Mathlib.LinearAlgebra.Matrix.Defs.Matrix.submatrix_apply`
- `Mathlib:Mathlib.LinearAlgebra.Matrix.NonsingularInverse.Matrix.invOf_eq_nonsing_inv`
- `Mathlib:Mathlib.LinearAlgebra.Matrix.NonsingularInverse.Matrix.inv_reindex`
- `Mathlib:Mathlib.LinearAlgebra.Matrix.NonsingularInverse.Matrix.inv_subsingleton`
- `Mathlib:Mathlib.LinearAlgebra.Matrix.PosDef.Matrix.PosDef.isUnit`
- `Mathlib:Mathlib.LinearAlgebra.Matrix.PosDef.Matrix.PosDef.submatrix`
- `Mathlib:Mathlib.LinearAlgebra.Matrix.SchurComplement.Matrix.invOf_fromBlocks₂₂_eq`
- `Mathlib:Mathlib.LinearAlgebra.Matrix.SchurComplement.Matrix.invertibleOfFromBlocks₂₂Invertible`
- `Mathlib:Mathlib.Logic.Equiv.Sum.Equiv.sumCompl`
- `current repo:Main.RootedCapacity.IsAdmissibleRootedTree`
- `current repo:Main.RootedCapacity.rootedCapacity`
- `current repo:Main.RootedCapacity.rootedChildCapacitySum`
- `current repo:Main.RootedCapacity.rootedGram`
- `current repo:Main.RootedCapacity.rootedGram_reindex_rootNonroot_blocks`
- `current repo:Main.RootedCapacity.rootedGram_rootNonroot_blocks_invertible`
- `current repo:Main.RootedCapacity.rootedNonroot_inverse_quadratic`
- `current repo:Main.RootedCapacity.treePairing_vertexVector_vertexVector`

## Sources

- `solution.tex:57-72`
