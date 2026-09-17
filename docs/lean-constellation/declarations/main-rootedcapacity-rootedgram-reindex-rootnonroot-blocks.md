[← Public API](../PUBLIC_API.md) · [Public boundaries](../PUBLIC_BOUNDARIES.md) · [Complete graph](../DECLARATION_GRAPH.md)

# `rootedGram_reindex_rootNonroot_blocks`

Reindexing rootedGram by the root/nonroot split equals its exact four-block Matrix.fromBlocks decomposition.

- Kind: `theorem`
- Node: `Main.RootedCapacity`
- Module: `PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.rootedGram_reindex_rootNonroot_blocks`
- State: `proved`
- Revision status: `committed`
- Repository completion: `graph_proved`
- Compatibility `formal_code`: final proof projection

## Statement NL

For every finite decidable vertex type `V`, graph `G` with decidable adjacency, integer weight `w`, and root `ρ`, set
`P := {v : V // v = ρ}`, `R := {v : V // v ≠ ρ}`, and
`e := Equiv.sumCompl (fun v : V => v = ρ) : P ⊕ R ≃ V`.

Then reindexing `rootedGram G w` along `e` on both axes is exactly the full block matrix
`Matrix.fromBlocks A B C D`, where `A`, `B`, `C`, and `D` are respectively the root/root, root/nonroot, nonroot/root, and nonroot/nonroot submatrices of `rootedGram G w` obtained using `Subtype.val`.  In particular, the lower-right block is definitionally the nonroot principal block
`D = (rootedGram G w).submatrix Subtype.val Subtype.val : Matrix R R ℚ`,
with this precise index type and orientation.

This is a purely entrywise matrix decomposition: it assumes neither a tree witness, admissibility, positivity, nor invertibility, and it leaves all four entries unevaluated beyond their indicated submatrix definitions.

## Statement Formal

```lean
-- lean-constellation: managed-imports-begin
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Prelude
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Logic.Equiv.Sum
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedGram
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `rootedGram_reindex_rootNonroot_blocks`

For every finite decidable vertex type `V`, graph `G` with decidable adjacency, integer weight `w`,
and root `ρ`, set
`P := {v : V // v = ρ}`, `R := {v : V // v ≠ ρ}`, and
`e := Equiv.sumCompl (fun v : V => v = ρ) : P ⊕ R ≃ V`.

Then reindexing `rootedGram G w` along `e` on both axes is exactly the full block matrix
`Matrix.fromBlocks A B C D`, where `A`, `B`, `C`, and `D` are respectively the root/root,
root/nonroot, nonroot/root, and nonroot/nonroot submatrices of `rootedGram G w` obtained using
`Subtype.val`.  In particular, the lower-right block is definitionally the nonroot principal block
`D = (rootedGram G w).submatrix Subtype.val Subtype.val : Matrix R R ℚ`,
with this precise index type and orientation.

This is a purely entrywise matrix decomposition: it assumes neither a tree witness, admissibility,
positivity, nor invertibility, and it leaves all four entries unevaluated beyond their indicated
submatrix definitions.

## Sources

- Source `solution.tex`, lines 57–64

## Statement dependencies

- `Matrix.fromBlocks` from `Mathlib.Data.Matrix.Block`
- `Matrix.reindex` from `Mathlib.LinearAlgebra.Matrix.Defs`
- `Matrix.submatrix` from `Mathlib.LinearAlgebra.Matrix.Defs`
- `Equiv.sumCompl` from `Mathlib.Logic.Equiv.Sum`
- `Main.RootedCapacity::rootedGram` → `rootedGram` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedGram`
-/

theorem rootedGram_reindex_rootNonroot_blocks {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (w : V → ℤ) (ρ : V) :
    Matrix.reindex (Equiv.sumCompl fun v : V => v = ρ).symm
        (Equiv.sumCompl fun v : V => v = ρ).symm (rootedGram G w) =
      Matrix.fromBlocks
        ((rootedGram G w).submatrix Subtype.val Subtype.val)
        ((rootedGram G w).submatrix Subtype.val Subtype.val)
        ((rootedGram G w).submatrix Subtype.val Subtype.val)
        ((rootedGram G w).submatrix Subtype.val Subtype.val) := by
  sorry
```

## Proof NL

Let `P := {v : V // v = ρ}`, `R := {v : V // v ≠ ρ}`, and `e := Equiv.sumCompl (fun v : V => v = ρ) : P ⊕ R ≃ V`.  The formal left-hand side is `Matrix.reindex e.symm e.symm (rootedGram G w)`, since `Matrix.reindex` is supplied the equivalence from the original vertex index to the sum index.

Apply `Matrix.ext` and split both sum indices, giving the four cases `(Sum.inl p, Sum.inl q)`, `(Sum.inl p, Sum.inr r)`, `(Sum.inr r, Sum.inl p)`, and `(Sum.inr r, Sum.inr s)`.  In each case unfold `Matrix.reindex_apply` and the corresponding entry of `Matrix.fromBlocks`; use `Matrix.fromBlocks_apply₁₁` and `Matrix.fromBlocks_apply₂₂` for the diagonal cases, while the two mixed entries reduce definitionally.  The value of `e` on each branch is the relevant `Subtype.val`, so every resulting equality is exactly the matching `rootedGram` submatrix entry.  Thus no evaluation of Gram entries, and no graph/tree, admissibility, positivity, or inverse input, is required.

In particular, the bottom-right case identifies the `R × R` block with `(rootedGram G w).submatrix Subtype.val Subtype.val` with its displayed orientation, so the equality can rewrite the nonroot block directly in the later Schur-complement argument.

## Proof Formal

```lean
-- lean-constellation: managed-imports-begin
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Prelude
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Logic.Equiv.Sum
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedGram
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `rootedGram_reindex_rootNonroot_blocks`

For every finite decidable vertex type `V`, graph `G` with decidable adjacency, integer weight `w`,
and root `ρ`, set
`P := {v : V // v = ρ}`, `R := {v : V // v ≠ ρ}`, and
`e := Equiv.sumCompl (fun v : V => v = ρ) : P ⊕ R ≃ V`.

Then reindexing `rootedGram G w` along `e` on both axes is exactly the full block matrix
`Matrix.fromBlocks A B C D`, where `A`, `B`, `C`, and `D` are respectively the root/root,
root/nonroot, nonroot/root, and nonroot/nonroot submatrices of `rootedGram G w` obtained using
`Subtype.val`.  In particular, the lower-right block is definitionally the nonroot principal block
`D = (rootedGram G w).submatrix Subtype.val Subtype.val : Matrix R R ℚ`,
with this precise index type and orientation.

This is a purely entrywise matrix decomposition: it assumes neither a tree witness, admissibility,
positivity, nor invertibility, and it leaves all four entries unevaluated beyond their indicated
submatrix definitions.

## Sources

- Source `solution.tex`, lines 57–64

## Statement dependencies

- `Matrix.fromBlocks` from `Mathlib.Data.Matrix.Block`
- `Matrix.reindex` from `Mathlib.LinearAlgebra.Matrix.Defs`
- `Matrix.submatrix` from `Mathlib.LinearAlgebra.Matrix.Defs`
- `Equiv.sumCompl` from `Mathlib.Logic.Equiv.Sum`
- `Main.RootedCapacity::rootedGram` → `rootedGram` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedGram`

## Proof outline

Let `P := {v : V // v = ρ}`, `R := {v : V // v ≠ ρ}`, and `e := Equiv.sumCompl (fun v : V => v = ρ)
: P ⊕ R ≃ V`.  The formal left-hand side is `Matrix.reindex e.symm e.symm (rootedGram G w)`, since
`Matrix.reindex` is supplied the equivalence from the original vertex index to the sum index.

Apply `Matrix.ext` and split both sum indices, giving the four cases `(Sum.inl p, Sum.inl q)`,
`(Sum.inl p, Sum.inr r)`, `(Sum.inr r, Sum.inl p)`, and `(Sum.inr r, Sum.inr s)`.  In each case
unfold `Matrix.reindex_apply` and the corresponding entry of `Matrix.fromBlocks`; use
`Matrix.fromBlocks_apply₁₁` and `Matrix.fromBlocks_apply₂₂` for the diagonal cases, while the two
mixed entries reduce definitionally.  The value of `e` on each branch is the relevant `Subtype.val`,
so every resulting equality is exactly the matching `rootedGram` submatrix entry.  Thus no
evaluation of Gram entries, and no graph/tree, admissibility, positivity, or inverse input, is
required.

In particular, the bottom-right case identifies the `R × R` block with `(rootedGram G w).submatrix
Subtype.val Subtype.val` with its displayed orientation, so the equality can rewrite the nonroot
block directly in the later Schur-complement argument.

## Proof sources

- Source `solution.tex`, lines 57–64

## Proof dependencies

- `Matrix.fromBlocks_apply₁₁` from `Mathlib.Data.Matrix.Block`
- `Matrix.fromBlocks_apply₂₂` from `Mathlib.Data.Matrix.Block`
- `Matrix.ext` from `Mathlib.LinearAlgebra.Matrix.Defs`
- `Matrix.reindex_apply` from `Mathlib.LinearAlgebra.Matrix.Defs`
- `Equiv.sumCompl` from `Mathlib.Logic.Equiv.Sum`
- `Main.RootedCapacity::rootedGram` → `rootedGram` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedGram`
-/
theorem rootedGram_reindex_rootNonroot_blocks {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (w : V → ℤ) (ρ : V) :
    Matrix.reindex (Equiv.sumCompl fun v : V => v = ρ).symm
        (Equiv.sumCompl fun v : V => v = ρ).symm (rootedGram G w) =
      Matrix.fromBlocks
        ((rootedGram G w).submatrix Subtype.val Subtype.val)
        ((rootedGram G w).submatrix Subtype.val Subtype.val)
        ((rootedGram G w).submatrix Subtype.val Subtype.val)
        ((rootedGram G w).submatrix Subtype.val Subtype.val) := by
  ext i j
  rcases i with p | r <;> rcases j with q | s <;> rfl
```

## Statement dependencies

- `Mathlib:Mathlib.Data.Matrix.Block.Matrix.fromBlocks`
- `Mathlib:Mathlib.LinearAlgebra.Matrix.Defs.Matrix.reindex`
- `Mathlib:Mathlib.LinearAlgebra.Matrix.Defs.Matrix.submatrix`
- `Mathlib:Mathlib.Logic.Equiv.Sum.Equiv.sumCompl`
- `current repo:Main.RootedCapacity.rootedGram`

## Proof dependencies

- `Mathlib:Mathlib.Data.Matrix.Block.Matrix.fromBlocks_apply₁₁`
- `Mathlib:Mathlib.Data.Matrix.Block.Matrix.fromBlocks_apply₂₂`
- `Mathlib:Mathlib.LinearAlgebra.Matrix.Defs.Matrix.ext`
- `Mathlib:Mathlib.LinearAlgebra.Matrix.Defs.Matrix.reindex_apply`
- `Mathlib:Mathlib.Logic.Equiv.Sum.Equiv.sumCompl`
- `current repo:Main.RootedCapacity.rootedGram`

## Sources

- `solution.tex:57-64`
