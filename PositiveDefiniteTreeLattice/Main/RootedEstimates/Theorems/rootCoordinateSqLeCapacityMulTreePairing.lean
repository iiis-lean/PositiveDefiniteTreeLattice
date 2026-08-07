-- lean-constellation: managed-imports-begin
import PositiveDefiniteTreeLattice.Main.RootedEstimates.Prelude
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Group.Invertible.Basic
import Mathlib.Algebra.Notation.Pi.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.SesquilinearForm.Basic
import PositiveDefiniteTreeLattice.Main.RootedEstimates.Theorems.treePairingCastEqRootedGramQuadratic
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `rootCoordinateSqLeCapacityMulTreePairing`

Let `G` be a finite rooted integer-weighted graph on `V`, with weight `w`, root `rho`, and
admissibility hypothesis `hT : IsAdmissibleRootedTree G w rho`.  For every integral coordinate
vector `x : V → ℤ`, the exact rational root-coordinate estimate is

`(x rho : ℚ)^2 ≤ rootedCapacity G w rho * (↑(PositiveDefiniteTreeLattice.treePairing G w x x) : ℚ)`.

The inequality uses the existing rational rooted capacity, the same integral vector and exact root
coordinate, and the integral tree pairing cast to `ℚ`.  It is asserted for all `x`, including the
zero vector; no nonzero hypothesis is required.

## Sources

- Source `solution.tex`, lines 165–175

## Statement dependencies

- `Main.LatticeFoundations::treePairingAnchor` → `PositiveDefiniteTreeLattice.treePairing` from
  `PositiveDefiniteTreeLattice.Main.LatticeFoundations.Defs.treePairingAnchor`
- `Main.RootedCapacity::IsAdmissibleRootedTree` → `IsAdmissibleRootedTree` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.IsAdmissibleRootedTree`
- `Main.RootedCapacity::rootedCapacity` → `rootedCapacity` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedCapacity`

## Proof outline

Let `M := rootedGram G w`.  Destructure `hT` and retain its `hPos : Matrix.PosDef M`.  The proved
scalar-extension bridge `treePairingCastEqRootedGramQuadratic G w x` rewrites the cast tree-pairing
factor to the quadratic form `q(x) := xQ ⬝ᵥ M *ᵥ xQ`, where `xQ v := (x v : ℚ)`.

Use `hPos` to build the Cauchy inputs for `M.toBilin'`.  Its positivity condition follows by cases
on a rational vector `y`: the zero case is immediate, and the nonzero case is `le_of_lt
(hPos.dotProduct_mulVec_pos hy)`, rewritten using `Matrix.toBilin'_apply'`.  Its symmetry follows
from the Hermitian component of `hPos`, `Matrix.isHermitian_iff_isSymm` over `ℚ`, and
`Matrix.isSymm_toBilin'_iff_isSymm`.

Let `e := Pi.single rho 1` and `z := M⁻¹ *ᵥ e`.  From `hPos.isUnit`, install the associated
`Invertible M` instance and use `Matrix.mul_inv_of_invertible` together with `Matrix.mulVec_mulVec`.
The following are direct finite matrix calculations, not new helpers: first, `M *ᵥ z = e`; hence
`M.toBilin' xQ z = xQ rho` after `Matrix.toBilin'_apply'` and simplification of `Pi.single`.
Second, the same identity gives `M.toBilin' z z = z rho`; expand the final coordinate of `z` with
`Matrix.mulVec_eq_sum` and `Pi.single_apply` to obtain `z rho = M⁻¹ rho rho = rootedCapacity G w
rho` by the definition of rootedCapacity.  These are the formal counterparts of the inverse-Gram
root dual vector and its squared norm in lines 165–170.

Apply `LinearMap.BilinForm.apply_sq_le_of_symm` to `M.toBilin'`, `xQ`, and `z`.  Rewrite its left
factor with the root-coordinate calculation, its first right factor with the scalar-extension
bridge, and its second right factor with the capacity calculation.  The result is exactly `(x rho :
ℚ)^2 ≤ rootedCapacity G w rho * ↑(treePairing G w x x)`, including the stated direction.  No nonzero
assumption on `x` is used.

## Proof sources

- Source `solution.tex`, lines 165–175

## Proof dependencies

- `Finset.sum_ite_eq'` from `Mathlib.Algebra.BigOperators.Group.Finset.Piecewise`
- `IsUnit.invertible` from `Mathlib.Algebra.Group.Invertible.Basic`
- `Pi.single_apply` from `Mathlib.Algebra.Notation.Pi.Basic`
- `Matrix.mulVec_eq_sum` from `Mathlib.Data.Matrix.Mul`
- `Matrix.mulVec_mulVec` from `Mathlib.Data.Matrix.Mul`
- `Matrix.isSymm_toBilin'_iff_isSymm` from `Mathlib.LinearAlgebra.Matrix.BilinearForm`
- `Matrix.toBilin'_apply'` from `Mathlib.LinearAlgebra.Matrix.BilinearForm`
- `Matrix.isHermitian_iff_isSymm` from `Mathlib.LinearAlgebra.Matrix.Hermitian`
- `Matrix.mul_inv_of_invertible` from `Mathlib.LinearAlgebra.Matrix.NonsingularInverse`
- `Matrix.PosDef.dotProduct_mulVec_pos` from `Mathlib.LinearAlgebra.Matrix.PosDef`
- `Matrix.PosDef.isUnit` from `Mathlib.LinearAlgebra.Matrix.PosDef`
- `LinearMap.BilinForm.apply_sq_le_of_symm` from `Mathlib.LinearAlgebra.SesquilinearForm.Basic`
- `Main.RootedCapacity::IsAdmissibleRootedTree` → `IsAdmissibleRootedTree` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.IsAdmissibleRootedTree`
- `Main.RootedCapacity::rootedCapacity` → `rootedCapacity` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedCapacity`
- `Main.RootedCapacity::rootedGram` → `rootedGram` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedGram`
- `Main.RootedEstimates::treePairingCastEqRootedGramQuadratic` →
  `treePairingCastEqRootedGramQuadratic` from
  `PositiveDefiniteTreeLattice.Main.RootedEstimates.Theorems.treePairingCastEqRootedGramQuadratic`
-/
theorem rootCoordinateSqLeCapacityMulTreePairing {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (w : V → ℤ) (rho : V)
    (hT : IsAdmissibleRootedTree G w rho) (x : V → ℤ) :
    (x rho : ℚ) ^ 2 ≤ rootedCapacity G w rho *
      (↑(PositiveDefiniteTreeLattice.treePairing G w x x) : ℚ) := by
  classical
  rcases hT with ⟨hG, hPos, hw, hchildren⟩
  let M : Matrix V V ℚ := rootedGram G w
  let xQ : V → ℚ := fun v => (x v : ℚ)
  let e : V → ℚ := Pi.single rho 1
  let z : V → ℚ := Matrix.mulVec (M⁻¹) e
  have hPosM : M.PosDef := by
    simpa [M] using hPos
  letI : Invertible M := hPosM.isUnit.invertible
  have hMz : Matrix.mulVec M z = e := by
    simp [z, Matrix.mulVec_mulVec]
  have hnonneg : ∀ y : V → ℚ, 0 ≤ M.toBilin' y y := by
    intro y
    by_cases hy : y = 0
    · subst y
      simp
    · rw [Matrix.toBilin'_apply']
      exact le_of_lt (by simpa using hPosM.dotProduct_mulVec_pos hy)
  have hsymM : M.IsSymm := by
    rw [← Matrix.isHermitian_iff_isSymm]
    exact hPosM.1
  have hsym : M.toBilin'.IsSymm := Matrix.isSymm_toBilin'_iff_isSymm.mpr hsymM
  have hsym' : LinearMap.IsSymm M.toBilin' := by
    refine ⟨?_⟩
    intro a b
    simpa using hsym.eq a b
  have hxz : M.toBilin' xQ z = xQ rho := by
    rw [Matrix.toBilin'_apply', hMz]
    simp [xQ, e, dotProduct, Pi.single_apply, Finset.sum_ite_eq']
  have hzrho : z rho = rootedCapacity G w rho := by
    dsimp [z]
    rw [Matrix.mulVec_eq_sum, Finset.sum_apply]
    simp only [Pi.smul_apply, Matrix.transpose_apply, MulOpposite.smul_eq_mul_unop]
    simp only [MulOpposite.unop_op, e, Pi.single_apply, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq']
    simp only [Finset.mem_univ, ↓reduceIte, rootedCapacity, M]
  have hzz : M.toBilin' z z = rootedCapacity G w rho := by
    rw [Matrix.toBilin'_apply', hMz]
    simpa [e, dotProduct, Pi.single_apply, Finset.sum_ite_eq'] using hzrho
  have hxx : M.toBilin' xQ xQ =
      (↑(PositiveDefiniteTreeLattice.treePairing G w x x) : ℚ) := by
    rw [Matrix.toBilin'_apply']
    symm
    simpa [M, xQ] using treePairingCastEqRootedGramQuadratic G w x
  calc
    (x rho : ℚ) ^ 2 = (M.toBilin' xQ z) ^ 2 := by
      simpa [xQ] using congrArg (fun q : ℚ => q ^ 2) hxz.symm
    _ ≤ M.toBilin' xQ xQ * M.toBilin' z z :=
      LinearMap.BilinForm.apply_sq_le_of_symm M.toBilin' hnonneg hsym' xQ z
    _ = rootedCapacity G w rho *
        (↑(PositiveDefiniteTreeLattice.treePairing G w x x) : ℚ) := by
      rw [hxx, hzz, mul_comm]
