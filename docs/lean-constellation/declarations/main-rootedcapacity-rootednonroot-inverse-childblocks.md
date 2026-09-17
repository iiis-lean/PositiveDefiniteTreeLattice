[← Public API](../PUBLIC_API.md) · [Public boundaries](../PUBLIC_BOUNDARIES.md) · [Complete graph](../DECLARATION_GRAPH.md)

# `rootedNonroot_inverse_childBlocks`

The inverse nonroot Gram block restricts to child Gram inverses and vanishes across distinct child components.

- Kind: `theorem`
- Node: `Main.RootedCapacity`
- Module: `PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.rootedNonroot_inverse_childBlocks`
- State: `proved`
- Revision status: `committed`
- Repository completion: `graph_proved`
- Compatibility `formal_code`: final proof projection

## Statement NL

For every finite decidable vertex type with the existing finite decidable tree structure, integer vertex weights, chosen root ρ, and admissibility hypothesis, let `e := rootedChildComponentsEquivNonroot` be the canonical equivalence from the dependent Sigma type of a root child together with a vertex of its `rootedChildComponent` to the subtype of nonroot vertices.  Then reindexing the rational total inverse of the nonroot principal block of `rootedGram` along `e` is equal to the dependent block diagonal matrix whose block at each root child is the rational total inverse of that child component's existing `rootedGram`.

Equivalently, for Sigma indices `⟨c, x⟩` and `⟨d, y⟩`, the reindexed inverse entry is the child `rootedGram` inverse entry when `c = d`, and is zero when `c ≠ d`.  Thus the result gives the same inverse transport as before directly in Sigma/equivalence coordinates, with no ambient nonroot-subtype embedding or proof-term argument, and it is oriented for rewriting the nonroot inverse quadratic form into the sum of child capacities.

## Statement Formal

```lean
-- lean-constellation: managed-imports-begin
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Prelude
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.IsAdmissibleRootedTree
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildComponent
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildComponentsEquivNonroot
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildren
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedGram
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `rootedNonroot_inverse_childBlocks`

For every finite decidable vertex type with the existing finite decidable tree structure, integer
vertex weights, chosen root ρ, and admissibility hypothesis, let `e :=
rootedChildComponentsEquivNonroot` be the canonical equivalence from the dependent Sigma type of a
root child together with a vertex of its `rootedChildComponent` to the subtype of nonroot vertices.
Then reindexing the rational total inverse of the nonroot principal block of `rootedGram` along `e`
is equal to the dependent block diagonal matrix whose block at each root child is the rational total
inverse of that child component's existing `rootedGram`.

Equivalently, for Sigma indices `⟨c, x⟩` and `⟨d, y⟩`, the reindexed inverse entry is the child
`rootedGram` inverse entry when `c = d`, and is zero when `c ≠ d`.  Thus the result gives the same
inverse transport as before directly in Sigma/equivalence coordinates, with no ambient
nonroot-subtype embedding or proof-term argument, and it is oriented for rewriting the nonroot
inverse quadratic form into the sum of child capacities.

## Sources

- Source `solution.tex`, lines 57–68

## Statement dependencies

- `Matrix.blockDiagonal'` from `Mathlib.Data.Matrix.Block`
- `Matrix.reindex` from `Mathlib.LinearAlgebra.Matrix.Defs`
- `Matrix.submatrix` from `Mathlib.LinearAlgebra.Matrix.Defs`
- `Matrix.inv` from `Mathlib.LinearAlgebra.Matrix.NonsingularInverse`
- `Main.RootedCapacity::IsAdmissibleRootedTree` → `IsAdmissibleRootedTree` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.IsAdmissibleRootedTree`
- `Main.RootedCapacity::rootedChildComponent` → `rootedChildComponent` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildComponent`
- `Main.RootedCapacity::rootedChildComponentsEquivNonroot` → `rootedChildComponentsEquivNonroot`
  from `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildComponentsEquivNonroot`
- `Main.RootedCapacity::rootedChildren` → `rootedChildren` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildren`
- `Main.RootedCapacity::rootedGram` → `rootedGram` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedGram`
-/

theorem rootedNonroot_inverse_childBlocks {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.IsTree) (w : V → ℤ) (ρ : V)
    (hAdm : IsAdmissibleRootedTree G w ρ) :
    Matrix.reindex (rootedChildComponentsEquivNonroot G hG ρ).symm
        (rootedChildComponentsEquivNonroot G hG ρ).symm
        (((rootedGram G w).submatrix Subtype.val Subtype.val)⁻¹) =
      Matrix.blockDiagonal' (fun c : rootedChildren G hG ρ ρ => by
        letI : Fintype (rootedChildComponent G ρ c) := Fintype.ofFinite _
        letI : DecidableRel (rootedChildComponent G ρ c).toSimpleGraph.Adj := Classical.decRel _
        exact (rootedGram (rootedChildComponent G ρ c).toSimpleGraph (fun x => w x))⁻¹) := by
  sorry
```

## Proof NL

The canonical equivalence from the nonroot subtype to the dependent Sigma child index is
e : {v : V // v ≠ ρ} ≃ Σ c : rootedChildren G hG ρ ρ, rootedChildComponent G ρ c :=
(rootedChildComponentsEquivNonroot G hG ρ).symm.
The local nonroot block D := (rootedGram G w).submatrix Subtype.val Subtype.val and the dependent child-Gram family B in the statement are aligned under the retained component-instance convention, so no ambient-subtype embedding is part of the representation.

The proved block decomposition rootedNonrootGram_reindex_childBlocks G hG w ρ has orientation Matrix.reindex e e D = Matrix.blockDiagonal' B. Applying congrArg (fun M => M⁻¹) and Matrix.inv_reindex identifies the inverse of the left side with Matrix.reindex e e (D⁻¹), with no symmetry or e.symm reorientation.

The proved rootedChildGram_blockDiagonal_inv G hG w ρ hAdm identifies (Matrix.blockDiagonal' B)⁻¹ with Matrix.blockDiagonal' (fun c => (B c)⁻¹) under the same child-component instance convention. Chaining these equalities yields the required inverse transport entirely in canonical Sigma/equivalence coordinates while preserving the rational total inverse and the original conclusion direction.

## Proof Formal

```lean
-- lean-constellation: managed-imports-begin
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Prelude
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.IsAdmissibleRootedTree
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildComponent
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildComponentsEquivNonroot
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildren
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedGram
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.rootedChildGram_blockDiagonal_inv
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.rootedNonrootGram_reindex_childBlocks
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `rootedNonroot_inverse_childBlocks`

For every finite decidable vertex type with the existing finite decidable tree structure, integer
vertex weights, chosen root ρ, and admissibility hypothesis, let `e :=
rootedChildComponentsEquivNonroot` be the canonical equivalence from the dependent Sigma type of a
root child together with a vertex of its `rootedChildComponent` to the subtype of nonroot vertices.
Then reindexing the rational total inverse of the nonroot principal block of `rootedGram` along `e`
is equal to the dependent block diagonal matrix whose block at each root child is the rational total
inverse of that child component's existing `rootedGram`.

Equivalently, for Sigma indices `⟨c, x⟩` and `⟨d, y⟩`, the reindexed inverse entry is the child
`rootedGram` inverse entry when `c = d`, and is zero when `c ≠ d`.  Thus the result gives the same
inverse transport as before directly in Sigma/equivalence coordinates, with no ambient
nonroot-subtype embedding or proof-term argument, and it is oriented for rewriting the nonroot
inverse quadratic form into the sum of child capacities.

## Sources

- Source `solution.tex`, lines 57–68

## Statement dependencies

- `Matrix.blockDiagonal'` from `Mathlib.Data.Matrix.Block`
- `Matrix.reindex` from `Mathlib.LinearAlgebra.Matrix.Defs`
- `Matrix.submatrix` from `Mathlib.LinearAlgebra.Matrix.Defs`
- `Matrix.inv` from `Mathlib.LinearAlgebra.Matrix.NonsingularInverse`
- `Main.RootedCapacity::IsAdmissibleRootedTree` → `IsAdmissibleRootedTree` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.IsAdmissibleRootedTree`
- `Main.RootedCapacity::rootedChildComponent` → `rootedChildComponent` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildComponent`
- `Main.RootedCapacity::rootedChildComponentsEquivNonroot` → `rootedChildComponentsEquivNonroot`
  from `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildComponentsEquivNonroot`
- `Main.RootedCapacity::rootedChildren` → `rootedChildren` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildren`
- `Main.RootedCapacity::rootedGram` → `rootedGram` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedGram`

## Proof outline

Work classically, keeping the accepted canonical equivalence
`e : {v : V // v ≠ ρ} ≃ Σ c : rootedChildren G hG ρ ρ, rootedChildComponent G ρ c :=
(rootedChildComponentsEquivNonroot G hG ρ).symm` from the nonroot subtype to the dependent
Sigma child index.  Unfold only the theorem statement's local notation enough to align the nonroot
principal block `D := (rootedGram G w).submatrix Subtype.val Subtype.val` and the existing
dependent child-Gram family `B`; do not introduce any ambient-subtype embedding.

Apply the proved block decomposition
`rootedNonrootGram_reindex_childBlocks G hG w ρ`, whose exact orientation is
`Matrix.reindex e e D = Matrix.blockDiagonal' B`.  Apply
`congrArg (fun M => M⁻¹)` to this equality.  Rewrite the inverse of its left-hand reindex with
`Matrix.inv_reindex e e D`.  Because both reindex equivalences are the same `e`, this yields
exactly the accepted target left side `Matrix.reindex e e (D⁻¹)`, with no symmetry or
`e.symm` reorientation.

For the right-hand side, apply the proved
`rootedChildGram_blockDiagonal_inv G hG w ρ hAdm`.  Its retained child-component instance
convention gives
`(Matrix.blockDiagonal' B)⁻¹ = Matrix.blockDiagonal' (fun c => (B c)⁻¹)`.
Use only definitional simplification to align that local dependent child-Gram family with the
statement's family, then chain the equalities.  This yields the required inverse transport entirely
in canonical Sigma/equivalence coordinates, preserving the rational total inverse and the original
conclusion direction.

## Proof sources

- Source `solution.tex`, lines 57–68

## Proof dependencies

- `Matrix.inv_reindex` from `Mathlib.LinearAlgebra.Matrix.NonsingularInverse`
- `Main.RootedCapacity::rootedChildGram_blockDiagonal_inv` → `rootedChildGram_blockDiagonal_inv`
  from `PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.rootedChildGram_blockDiagonal_inv`
- `Main.RootedCapacity::rootedNonrootGram_reindex_childBlocks` →
  `rootedNonrootGram_reindex_childBlocks` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.rootedNonrootGram_reindex_childBlocks`
-/
theorem rootedNonroot_inverse_childBlocks {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.IsTree) (w : V → ℤ) (ρ : V)
    (hAdm : IsAdmissibleRootedTree G w ρ) :
    Matrix.reindex (rootedChildComponentsEquivNonroot G hG ρ).symm
        (rootedChildComponentsEquivNonroot G hG ρ).symm
        (((rootedGram G w).submatrix Subtype.val Subtype.val)⁻¹) =
      Matrix.blockDiagonal' (fun c : rootedChildren G hG ρ ρ => by
        letI : Fintype (rootedChildComponent G ρ c) := Fintype.ofFinite _
        letI : DecidableRel (rootedChildComponent G ρ c).toSimpleGraph.Adj := Classical.decRel _
        exact (rootedGram (rootedChildComponent G ρ c).toSimpleGraph (fun x => w x))⁻¹) := by
  classical
  let I := {c : V // c ∈ rootedChildren G hG ρ ρ}
  let childInstances : ∀ c : I,
      Fintype (rootedChildComponent G ρ c.1) ×
        DecidableRel (rootedChildComponent G ρ c.1).toSimpleGraph.Adj := fun c =>
    ⟨Fintype.ofFinite _, by
      intro x y
      change Decidable ((G.deleteEdges {s(ρ, c.1)}).Adj (x : V) (y : V))
      infer_instance⟩
  letI : ∀ c : I, Fintype (rootedChildComponent G ρ c.1) :=
    fun c => (childInstances c).1
  letI : ∀ c : I, DecidableRel (rootedChildComponent G ρ c.1).toSimpleGraph.Adj :=
    fun c => (childInstances c).2
  letI : Fintype (Σ c : I, rootedChildComponent G ρ c.1) := inferInstance
  rw [← Matrix.inv_reindex]
  rw [rootedNonrootGram_reindex_childBlocks G hG w ρ]
  convert rootedChildGram_blockDiagonal_inv G hG w ρ hAdm using 1
  all_goals simp only
  apply Matrix.ext
  rintro ⟨c, x⟩ ⟨d, y⟩
  rw [Matrix.blockDiagonal'_apply', Matrix.blockDiagonal'_apply']
  by_cases hcd : c = d
  · subst d
    simp only [dif_pos]
    have hdec : Classical.decRel (rootedChildComponent G ρ c.1).toSimpleGraph.Adj =
        (childInstances c).2 := Subsingleton.elim _ _
    rw [hdec]
  · simp only [dif_neg hcd]
```

## Statement dependencies

- `Mathlib:Mathlib.Data.Matrix.Block.Matrix.blockDiagonal'`
- `Mathlib:Mathlib.LinearAlgebra.Matrix.Defs.Matrix.reindex`
- `Mathlib:Mathlib.LinearAlgebra.Matrix.Defs.Matrix.submatrix`
- `Mathlib:Mathlib.LinearAlgebra.Matrix.NonsingularInverse.Matrix.inv`
- `current repo:Main.RootedCapacity.IsAdmissibleRootedTree`
- `current repo:Main.RootedCapacity.rootedChildComponent`
- `current repo:Main.RootedCapacity.rootedChildComponentsEquivNonroot`
- `current repo:Main.RootedCapacity.rootedChildren`
- `current repo:Main.RootedCapacity.rootedGram`

## Proof dependencies

- `Mathlib:Mathlib.LinearAlgebra.Matrix.NonsingularInverse.Matrix.inv_reindex`
- `current repo:Main.RootedCapacity.rootedChildGram_blockDiagonal_inv`
- `current repo:Main.RootedCapacity.rootedNonrootGram_reindex_childBlocks`

## Sources

- `solution.tex:57-68`
