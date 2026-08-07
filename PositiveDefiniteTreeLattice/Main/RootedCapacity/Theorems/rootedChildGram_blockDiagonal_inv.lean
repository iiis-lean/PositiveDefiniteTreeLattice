-- lean-constellation: managed-imports-begin
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Prelude
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Matrix.Diagonal
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.PosDef
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.IsAdmissibleRootedTree
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildComponent
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildren
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedGram
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.IsAdmissibleRootedTree_rootedChildComponent
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `rootedChildGram_blockDiagonal_inv`

Let V be a finite type with decidable equality, let G be a simple graph on V with decidable
adjacency, let hG : G.IsTree, let w : V → ℤ, let ρ : V, and suppose hAdm : IsAdmissibleRootedTree G
w ρ. Index root children by

I := {c : V // c ∈ rootedChildren G hG ρ ρ},

and define the dependent rational child-Gram family, with the canonical finite and
decidable-adjacency instances for each component, by

B c := rootedGram (rootedChildComponent G ρ c.1).toSimpleGraph
  (fun x : rootedChildComponent G ρ c.1 => w (x : V)).

Then the total inverse of the dependent block-diagonal child Gram matrix is the dependent block
diagonal of the total inverses of its exact child blocks:

(Matrix.blockDiagonal' B)⁻¹ = Matrix.blockDiagonal' (fun c => (B c)⁻¹).

The statement uses the same dependent Sigma index type and rational matrix inverse as the
child-block decomposition, without strengthening the ambient hypotheses or changing the child-Gram
representation.

## Sources

- Source `solution.tex`, lines 57–68

## Statement dependencies

- `SimpleGraph.IsTree` from `Mathlib.Combinatorics.SimpleGraph.Acyclic`
- `SimpleGraph.ConnectedComponent.toSimpleGraph` from
  `Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected`
- `SimpleGraph.deleteEdges` from `Mathlib.Combinatorics.SimpleGraph.DeleteEdges`
- `Matrix.blockDiagonal'` from `Mathlib.Data.Matrix.Block`
- `Matrix.inv` from `Mathlib.LinearAlgebra.Matrix.NonsingularInverse`
- `Main.RootedCapacity::IsAdmissibleRootedTree` → `IsAdmissibleRootedTree` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.IsAdmissibleRootedTree`
- `Main.RootedCapacity::rootedChildComponent` → `rootedChildComponent` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildComponent`
- `Main.RootedCapacity::rootedChildren` → `rootedChildren` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildren`
- `Main.RootedCapacity::rootedGram` → `rootedGram` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedGram`

## Proof outline

Work classically, introducing the statement's let-bound `I`, `childInstances`, the two induced
per-child instances, `B`, and the Sigma Fintype as local definitions. Retain `childInstances`
throughout: do not use broad `dsimp` or unfold it. In particular, all references to a child
component use exactly the statement's instance projections `(childInstances c).1` and
`(childInstances c).2`, so the block family, its inverse family, and the sigma block-multiplication
instance remain definitionally aligned.

For each `c : I`, use `c.property` as the root-child membership in
`IsAdmissibleRootedTree_rootedChildComponent G w ρ ρ c.1 hG c.property hAdm`.
Read its positive-definiteness field using the retained component instances; it is definitionally
the matrix `B c`. Apply `Matrix.PosDef.isUnit` and then `Matrix.isUnit_iff_isUnit_det` to obtain
`hdet c : IsUnit (B c).det`.

Let `A := Matrix.blockDiagonal' B` and
`E := Matrix.blockDiagonal' (fun c => (B c)⁻¹)`, without unfolding either family. Use
`Matrix.blockDiagonal'_mul` to rewrite
`E * A` as the block diagonal of `(B c)⁻¹ * B c`. Replace every block by `1` using
`Matrix.nonsing_inv_mul (hdet c)`. Establish that the resulting `Matrix.blockDiagonal' (fun c => 1)`
is the identity on the same dependent Sigma type by `Matrix.ext` and `Matrix.blockDiagonal'_apply'`:
the equal-label branch has the canonical retained dependent cast and agrees with the identity entry,
while the unequal-label branch is zero.

This gives `E * A = 1`; applying `Matrix.inv_eq_left_inv` yields `A⁻¹ = E`. If useful for
normalization, derive the right product analogously with `Matrix.mul_nonsing_inv`, but do not change
the retained instance convention. Unfold only the local aliases `A` and `E` at the final line,
obtaining the exact private conclusion
`(Matrix.blockDiagonal' B)⁻¹ = Matrix.blockDiagonal' (fun c => (B c)⁻¹)`.
The proof adds no hypotheses, generic theorem, or child-Gram representation change.

## Proof sources

- Source `solution.tex`, lines 57–68

## Proof dependencies

- `Matrix.blockDiagonal'_apply'` from `Mathlib.Data.Matrix.Block`
- `Matrix.blockDiagonal'_mul` from `Mathlib.Data.Matrix.Block`
- `Matrix.one_apply` from `Mathlib.Data.Matrix.Diagonal`
- `Matrix.ext` from `Mathlib.LinearAlgebra.Matrix.Defs`
- `Matrix.inv_eq_left_inv` from `Mathlib.LinearAlgebra.Matrix.NonsingularInverse`
- `Matrix.isUnit_iff_isUnit_det` from `Mathlib.LinearAlgebra.Matrix.NonsingularInverse`
- `Matrix.mul_nonsing_inv` from `Mathlib.LinearAlgebra.Matrix.NonsingularInverse`
- `Matrix.nonsing_inv_mul` from `Mathlib.LinearAlgebra.Matrix.NonsingularInverse`
- `Matrix.PosDef.isUnit` from `Mathlib.LinearAlgebra.Matrix.PosDef`
- `Main.RootedCapacity::IsAdmissibleRootedTree` → `IsAdmissibleRootedTree` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.IsAdmissibleRootedTree`
- `Main.RootedCapacity::IsAdmissibleRootedTree_rootedChildComponent` →
  `IsAdmissibleRootedTree_rootedChildComponent` from `PositiveDefiniteTreeLattice.Main.RootedCapacit
  y.Theorems.IsAdmissibleRootedTree_rootedChildComponent`
- `Main.RootedCapacity::rootedChildComponent` → `rootedChildComponent` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildComponent`
- `Main.RootedCapacity::rootedChildren` → `rootedChildren` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildren`
- `Main.RootedCapacity::rootedGram` → `rootedGram` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedGram`
-/
theorem rootedChildGram_blockDiagonal_inv {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.IsTree) (w : V → ℤ) (ρ : V)
    (hAdm : IsAdmissibleRootedTree G w ρ) :
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
    let B : ∀ c : I,
        Matrix (rootedChildComponent G ρ c.1) (rootedChildComponent G ρ c.1) ℚ := fun c =>
      rootedGram (rootedChildComponent G ρ c.1).toSimpleGraph
        (fun x : rootedChildComponent G ρ c.1 => w (x : V))
    letI : Fintype (Σ c : I, rootedChildComponent G ρ c.1) := inferInstance
    (Matrix.blockDiagonal' B)⁻¹ = Matrix.blockDiagonal' (fun c : I => (B c)⁻¹) := by
  classical
  dsimp only
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
  let B : ∀ c : I,
      Matrix (rootedChildComponent G ρ c.1) (rootedChildComponent G ρ c.1) ℚ := fun c =>
    rootedGram (rootedChildComponent G ρ c.1).toSimpleGraph
      (fun x : rootedChildComponent G ρ c.1 => w (x : V))
  letI : Fintype (Σ c : I, rootedChildComponent G ρ c.1) := inferInstance
  change (Matrix.blockDiagonal' B)⁻¹ = Matrix.blockDiagonal' (fun c : I => (B c)⁻¹)
  have hdet : ∀ c : I, IsUnit (B c).det := by
    intro c
    obtain ⟨-, hpos, -, -⟩ :=
      IsAdmissibleRootedTree_rootedChildComponent G w ρ ρ c.1 hG c.2 hAdm
    exact (Matrix.isUnit_iff_isUnit_det _).mp hpos.isUnit
  apply Matrix.inv_eq_left_inv
  rw [← Matrix.blockDiagonal'_mul]
  apply Matrix.ext
  rintro ⟨c, x⟩ ⟨d, y⟩
  rw [Matrix.blockDiagonal'_apply']
  by_cases hcd : c = d
  · subst d
    simp only [dif_pos]
    rw [Matrix.nonsing_inv_mul _ (hdet c)]
    simp [Matrix.one_apply]
  · rw [dif_neg hcd]
    simp [hcd]
