-- lean-constellation: managed-imports-begin
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Prelude
import Mathlib.Algebra.Group.Invertible.Basic
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Logic.Equiv.Sum
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.IsAdmissibleRootedTree
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedGram
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.rootedGram_reindex_rootNonroot_blocks
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `rootedGram_rootNonroot_blocks_invertible`

For every finite decidable vertex type `V`, graph `G` with decidable adjacency, integer weight `w`,
root `ρ`, and admissibility witness `hAdm : IsAdmissibleRootedTree G w ρ`, use exactly the
root/nonroot data from `rootedGram_reindex_rootNonroot_blocks`:
`P := {v : V // v = ρ}`, `R := {v : V // v ≠ ρ}`,
`e := Equiv.sumCompl (fun v : V => v = ρ)`, and the four `rootedGram G w` submatrices `A, B, C, D`
along `Subtype.val`, with
`D = (rootedGram G w).submatrix Subtype.val Subtype.val : Matrix R R ℚ`.

Then the corresponding full root/nonroot block matrix is a unit:
`IsUnit (Matrix.fromBlocks A B C D)`.

This private representation theorem transports the positive-definite rational `rootedGram` supplied
by `hAdm` to exactly the canonical reindexed block matrix. It introduces no additional tree,
positivity, or invertibility assumption; a consumer may obtain the needed local `Invertible`
instance from this `IsUnit` result.

## Sources

- Source `solution.tex`, lines 57–72

## Statement dependencies

- `Matrix.fromBlocks` from `Mathlib.Data.Matrix.Block`
- `Matrix.submatrix` from `Mathlib.LinearAlgebra.Matrix.Defs`
- `Equiv.sumCompl` from `Mathlib.Logic.Equiv.Sum`
- `Main.RootedCapacity::IsAdmissibleRootedTree` → `IsAdmissibleRootedTree` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.IsAdmissibleRootedTree`
- `Main.RootedCapacity::rootedGram` → `rootedGram` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedGram`

## Proof outline

Work classically and unfold the admissibility witness only far enough to obtain its `hPD :
Matrix.PosDef (rootedGram G w)` field; the remaining tree and weight clauses are not used.  By
`Matrix.PosDef.isUnit`, obtain `hUnit : IsUnit (rootedGram G w)`, and install the local matrix
instance `letI := hUnit.invertible`.  This is an instance for the Gram matrix only, not an instance
derived from `hAdm`.

Let `e := Equiv.sumCompl (fun v : V => v = ρ) : P ⊕ R ≃ V`, with `P := {v : V // v = ρ}` and `R :=
{v : V // v ≠ ρ}`.  Apply `Matrix.submatrixEquivInvertible (rootedGram G w) e e` to obtain an
`Invertible` instance for the reindexed matrix: by `Matrix.reindex_apply`, its carrier is
definitionally `Matrix.reindex e.symm e.symm (rootedGram G w)`.  Convert this local instance back to
the theorem-shaped conclusion `IsUnit` using `isUnit_of_invertible`.

Finally, rewrite that unit assertion by the already proved `rootedGram_reindex_rootNonroot_blocks G
w ρ`.  Equality transport changes precisely the reindexed Gram matrix into the displayed
`Matrix.fromBlocks` of the four `Subtype.val` submatrices, including the unchanged nonroot `D`
block.  This yields the required `IsUnit` conclusion with no extra positivity, tree, or nonzero
assumptions, and lets the parent install its own `letI := ... .invertible` when applying the
Schur-complement formula.

## Proof sources

- Source `solution.tex`, lines 57–72

## Proof dependencies

- `IsUnit.invertible` from `Mathlib.Algebra.Group.Invertible.Basic`
- `isUnit_of_invertible` from `Mathlib.Algebra.Group.Invertible.Basic`
- `Matrix.reindex_apply` from `Mathlib.LinearAlgebra.Matrix.Defs`
- `Matrix.submatrixEquivInvertible` from `Mathlib.LinearAlgebra.Matrix.NonsingularInverse`
- `Matrix.PosDef.isUnit` from `Mathlib.LinearAlgebra.Matrix.PosDef`
- `Equiv.sumCompl` from `Mathlib.Logic.Equiv.Sum`
- `Main.RootedCapacity::IsAdmissibleRootedTree` → `IsAdmissibleRootedTree` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.IsAdmissibleRootedTree`
- `Main.RootedCapacity::rootedGram` → `rootedGram` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedGram`
- `Main.RootedCapacity::rootedGram_reindex_rootNonroot_blocks` →
  `rootedGram_reindex_rootNonroot_blocks` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.rootedGram_reindex_rootNonroot_blocks`
-/

theorem rootedGram_rootNonroot_blocks_invertible {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (w : V → ℤ) (ρ : V)
    (hAdm : IsAdmissibleRootedTree G w ρ) :
    IsUnit
      (Matrix.fromBlocks
        ((rootedGram G w).submatrix
          (Subtype.val : {v : V // v = ρ} → V) Subtype.val)
        ((rootedGram G w).submatrix
          (Subtype.val : {v : V // v = ρ} → V) Subtype.val)
        ((rootedGram G w).submatrix Subtype.val
          (Subtype.val : {v : V // v = ρ} → V))
        ((rootedGram G w).submatrix Subtype.val Subtype.val) :
        Matrix ({v : V // v = ρ} ⊕ {v : V // v ≠ ρ})
          ({v : V // v = ρ} ⊕ {v : V // v ≠ ρ}) ℚ) := by
  classical
  rcases hAdm with ⟨_, hPD, _, _⟩
  let e := Equiv.sumCompl (fun v : V => v = ρ)
  letI : Invertible (rootedGram G w) := hPD.isUnit.invertible
  letI : Invertible (Matrix.reindex e.symm e.symm (rootedGram G w)) := by
    rw [Matrix.reindex_apply]
    exact Matrix.submatrixEquivInvertible _ e e
  have hUnit : IsUnit (Matrix.reindex e.symm e.symm (rootedGram G w)) :=
    isUnit_of_invertible (Matrix.reindex e.symm e.symm (rootedGram G w))
  rw [show e = Equiv.sumCompl (fun v : V => v = ρ) by rfl,
    rootedGram_reindex_rootNonroot_blocks] at hUnit
  exact hUnit
