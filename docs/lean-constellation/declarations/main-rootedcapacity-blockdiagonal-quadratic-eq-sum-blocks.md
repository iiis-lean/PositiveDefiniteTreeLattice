[← Public API](../PUBLIC_API.md) · [Public boundaries](../PUBLIC_BOUNDARIES.md) · [Complete graph](../DECLARATION_GRAPH.md)

# `blockDiagonal_quadratic_eq_sum_blocks`

A dependent block-diagonal rational quadratic double sum splits into the sum of its within-fiber quadratic double sums.

- Kind: `theorem`
- Node: `Main.RootedCapacity`
- Module: `PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.blockDiagonal_quadratic_eq_sum_blocks`
- State: `proved`
- Revision status: `committed`
- Repository completion: `graph_proved`
- Compatibility `formal_code`: final proof projection

## Statement NL

For every finite index type `I`, every family `S : I → Type` with finite fibers, every rational matrix family `B : ∀ c, Matrix (S c) (S c) ℚ`, and every coefficient function `b : (Σ c, S c) → ℚ`, the ordered quadratic double sum of `Matrix.blockDiagonal' B` is the sum of the ordered within-fiber quadratic double sums:

`∑ u : Σ c, S c, ∑ v : Σ c, S c, b u * Matrix.blockDiagonal' B u v * b v = ∑ c : I, ∑ x : S c, ∑ y : S c, b ⟨c, x⟩ * B c x y * b ⟨c, y⟩`.

The assertion is generic in the finite dependent index family and introduces no rooted-tree data, representation equivalences, or additional assumptions.

## Statement Formal

```lean
-- lean-constellation: managed-imports-begin
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Prelude
import Mathlib.Data.Matrix.Block
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `blockDiagonal_quadratic_eq_sum_blocks`

For every finite index type `I`, every family `S : I → Type` with finite fibers, every rational
matrix family `B : ∀ c, Matrix (S c) (S c) ℚ`, and every coefficient function `b : (Σ c, S c) → ℚ`,
the ordered quadratic double sum of `Matrix.blockDiagonal' B` is the sum of the ordered within-fiber
quadratic double sums:

`∑ u : Σ c, S c, ∑ v : Σ c, S c, b u * Matrix.blockDiagonal' B u v * b v = ∑ c : I, ∑ x : S c, ∑ y :
S c, b ⟨c, x⟩ * B c x y * b ⟨c, y⟩`.

The assertion is generic in the finite dependent index family and introduces no rooted-tree data,
representation equivalences, or additional assumptions.

## Sources

- Source `solution.tex`, lines 57–68

## Statement dependencies

- `Matrix.blockDiagonal'` from `Mathlib.Data.Matrix.Block`
-/
theorem blockDiagonal_quadratic_eq_sum_blocks
    (I : Type*) [Fintype I]
    (S : I → Type*) [∀ c, Fintype (S c)]
    (B : ∀ c, Matrix (S c) (S c) ℚ)
    (b : (Σ c, S c) → ℚ) :
    letI : DecidableEq I := Classical.decEq I
    (∑ u : Σ c, S c, ∑ v : Σ c, S c,
        b u * Matrix.blockDiagonal' B u v * b v) =
      ∑ c : I, ∑ x : S c, ∑ y : S c,
        b ⟨c, x⟩ * B c x y * b ⟨c, y⟩ := by
  sorry
```

## Proof NL

Introduce the local classical `DecidableEq I` required by the accepted statement. Expand both finite sums over the Sigma type with `Fintype.sum_sigma`, so the left-hand side is indexed by an outer source fiber `c`, an element `x : S c`, a target fiber `d`, and an element `y : S d`.

For each fixed `c` and `x`, collapse the target-fiber sum with `Fintype.sum_eq_single c`. The surviving `d = c` summand is rewritten using `Matrix.blockDiagonal'_apply'`; after substituting the equality proof, its dependent cast reduces and gives exactly `b ⟨c, x⟩ * B c x y * b ⟨c, y⟩`. For every `d ≠ c`, the same entry lemma makes the block-diagonal entry zero, hence the entire within-fiber sum is zero by simplification. This leaves precisely the stated sum over `c`, `x`, and `y`.

This is a direct finite-sum implementation of the source’s block direct-sum identity, uses no rooted-tree objects or auxiliary equivalences, and requires no helper declaration beyond the three verified Mathlib facts.

## Proof Formal

```lean
-- lean-constellation: managed-imports-begin
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Prelude
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Matrix.Block
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `blockDiagonal_quadratic_eq_sum_blocks`

For every finite index type `I`, every family `S : I → Type` with finite fibers, every rational
matrix family `B : ∀ c, Matrix (S c) (S c) ℚ`, and every coefficient function `b : (Σ c, S c) → ℚ`,
the ordered quadratic double sum of `Matrix.blockDiagonal' B` is the sum of the ordered within-fiber
quadratic double sums:

`∑ u : Σ c, S c, ∑ v : Σ c, S c, b u * Matrix.blockDiagonal' B u v * b v = ∑ c : I, ∑ x : S c, ∑ y :
S c, b ⟨c, x⟩ * B c x y * b ⟨c, y⟩`.

The assertion is generic in the finite dependent index family and introduces no rooted-tree data,
representation equivalences, or additional assumptions.

## Sources

- Source `solution.tex`, lines 57–68

## Statement dependencies

- `Matrix.blockDiagonal'` from `Mathlib.Data.Matrix.Block`

## Proof outline

Introduce the local classical `DecidableEq I` required by the accepted statement. Expand both finite
sums over the Sigma type with `Fintype.sum_sigma`, so the left-hand side is indexed by an outer
source fiber `c`, an element `x : S c`, a target fiber `d`, and an element `y : S d`.

For each fixed `c` and `x`, collapse the target-fiber sum with `Fintype.sum_eq_single c`. The
surviving `d = c` summand is rewritten using `Matrix.blockDiagonal'_apply'`; after substituting the
equality proof, its dependent cast reduces and gives exactly `b ⟨c, x⟩ * B c x y * b ⟨c, y⟩`. For
every `d ≠ c`, the same entry lemma makes the block-diagonal entry zero, hence the entire
within-fiber sum is zero by simplification. This leaves precisely the stated sum over `c`, `x`, and
`y`.

This is a direct finite-sum implementation of the source’s block direct-sum identity, uses no
rooted-tree objects or auxiliary equivalences, and requires no helper declaration beyond the three
verified Mathlib facts.

## Proof sources

- Source `solution.tex`, lines 57–68

## Proof dependencies

- `Finset.sum_congr` from `Mathlib.Algebra.BigOperators.Group.Finset.Basic`
- `Fintype.sum_eq_single` from `Mathlib.Data.Fintype.BigOperators`
- `Fintype.sum_sigma` from `Mathlib.Data.Fintype.BigOperators`
- `Matrix.blockDiagonal'_apply'` from `Mathlib.Data.Matrix.Block`
-/
theorem blockDiagonal_quadratic_eq_sum_blocks
    (I : Type*) [Fintype I]
    (S : I → Type*) [∀ c, Fintype (S c)]
    (B : ∀ c, Matrix (S c) (S c) ℚ)
    (b : (Σ c, S c) → ℚ) :
    letI : DecidableEq I := Classical.decEq I
    (∑ u : Σ c, S c, ∑ v : Σ c, S c,
        b u * Matrix.blockDiagonal' B u v * b v) =
      ∑ c : I, ∑ x : S c, ∑ y : S c,
        b ⟨c, x⟩ * B c x y * b ⟨c, y⟩ := by
  classical
  simp_rw [Fintype.sum_sigma]
  simp only [Matrix.blockDiagonal'_apply']
  apply Finset.sum_congr rfl
  intro c hc
  apply Finset.sum_congr rfl
  intro x hx
  rw [Fintype.sum_eq_single c]
  · simp
  · intro d hdc
    have hcd : c ≠ d := Ne.symm hdc
    simp [hcd]
```

## Statement dependencies

- `Mathlib:Mathlib.Data.Matrix.Block.Matrix.blockDiagonal'`

## Proof dependencies

- `Mathlib:Mathlib.Algebra.BigOperators.Group.Finset.Basic.Finset.sum_congr`
- `Mathlib:Mathlib.Data.Fintype.BigOperators.Fintype.sum_eq_single`
- `Mathlib:Mathlib.Data.Fintype.BigOperators.Fintype.sum_sigma`
- `Mathlib:Mathlib.Data.Matrix.Block.Matrix.blockDiagonal'_apply'`

## Sources

- `solution.tex:57-68`
