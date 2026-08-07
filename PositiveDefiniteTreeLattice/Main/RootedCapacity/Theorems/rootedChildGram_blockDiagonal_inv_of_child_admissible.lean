-- lean-constellation: managed-imports-begin
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Prelude
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Matrix.Diagonal
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.PosDef
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.IsAdmissibleRootedTree
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildComponent
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildRoot
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildren
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedGram
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `rootedChildGram_blockDiagonal_inv_of_child_admissible`

Let `V` be a finite type with decidable equality, let `G` be a simple graph on `V` with decidable
adjacency, let `hG : G.IsTree`, let `w : V → ℤ`, and let `ρ : V`. Index the attached root children
by

`I := {c : V // c ∈ rootedChildren G hG ρ ρ}`.

For each `c : I`, use the canonical `Fintype.ofFinite` instances and the deleted-edge `DecidableRel`
convention to form the child-side component `rootedChildComponent G ρ c.1`, its canonical root
`rootedChildRoot G ρ c.1`, and the exact dependent rational Gram family

`B c := rootedGram (rootedChildComponent G ρ c.1).toSimpleGraph (fun x : rootedChildComponent G ρ
c.1 => w (x : V))`.

Assume pointwise child admissibility, with these same local instances:

`∀ c : I, IsAdmissibleRootedTree (rootedChildComponent G ρ c.1).toSimpleGraph (fun x => w (x : V))
(rootedChildRoot G ρ c.1)`.

Then the total rational inverse of the dependent block-diagonal child Gram matrix is the dependent
block diagonal of the total inverses of its exact child blocks:

`(Matrix.blockDiagonal' B)⁻¹ = Matrix.blockDiagonal' (fun c => (B c)⁻¹)`.

This preserves the dependent Sigma index and exact child-Gram representation while replacing ambient
admissibility by precisely the pointwise attached-child hypotheses.

## Sources

- Source `solution.tex`, lines 57–68

## Statement dependencies

- `SimpleGraph.IsTree` from `Mathlib.Combinatorics.SimpleGraph.Acyclic`
- `SimpleGraph.ConnectedComponent.toSimpleGraph` from
  `Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected`
- `SimpleGraph.deleteEdges` from `Mathlib.Combinatorics.SimpleGraph.DeleteEdges`
- `Fintype.ofFinite` from `Mathlib.Data.Fintype.EquivFin`
- `Matrix.blockDiagonal'` from `Mathlib.Data.Matrix.Block`
- `Matrix.inv` from `Mathlib.LinearAlgebra.Matrix.NonsingularInverse`
- `Main.RootedCapacity::IsAdmissibleRootedTree` → `IsAdmissibleRootedTree` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.IsAdmissibleRootedTree`
- `Main.RootedCapacity::rootedChildComponent` → `rootedChildComponent` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildComponent`
- `Main.RootedCapacity::rootedChildRoot` → `rootedChildRoot` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildRoot`
- `Main.RootedCapacity::rootedChildren` → `rootedChildren` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildren`
- `Main.RootedCapacity::rootedGram` → `rootedGram` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedGram`

## Proof outline

Work classically and introduce the statement’s let-bound attached-child subtype `I`, its shared
`Fintype.ofFinite` and deleted-edge `DecidableRel` instances, the dependent Gram family `B`, and the
Sigma Fintype. Retain these let-bound instances throughout; in particular, do not use broad `dsimp`
or recreate child-component instances, since the family `B`, its inverse family, and
`Matrix.blockDiagonal'_mul` must remain definitionally aligned.

Let `hChild` be the pointwise admissibility hypothesis. For each `c : I`, specialize `hChild c` and
destruct the definition `IsAdmissibleRootedTree`. Its positive-definiteness component is, under the
retained local instances, exactly `(B c).PosDef`; no ambient admissibility hypothesis or use of
`IsAdmissibleRootedTree_rootedChildComponent` is needed. Apply `Matrix.PosDef.isUnit` and
`Matrix.isUnit_iff_isUnit_det` to obtain `hdet c : IsUnit (B c).det`.

Set `A := Matrix.blockDiagonal' B` and `E := Matrix.blockDiagonal' (fun c => (B c)⁻¹)`. Use
`Matrix.blockDiagonal'_mul` to identify `E * A` with the block diagonal family `fun c => (B c)⁻¹ * B
c`. Rewrite every block using `Matrix.nonsing_inv_mul (hdet c)`. Prove `Matrix.blockDiagonal' (fun c
=> 1) = 1` on the same dependent Sigma index by `Matrix.ext` and `Matrix.blockDiagonal'_apply'`:
equal outer labels reduce, with the canonical dependent cast, to the identity entry, while unequal
labels give zero; normalize the identity entries with `Matrix.one_apply`.

Thus `E * A = 1`, and `Matrix.inv_eq_left_inv` gives `A⁻¹ = E`. Unfold only the local aliases in the
final step, yielding exactly `(Matrix.blockDiagonal' B)⁻¹ = Matrix.blockDiagonal' (fun c => (B
c)⁻¹)`. This uses precisely the child-wise admissibility premise and preserves the declared child
indices, matrices, total inverse, and local-instance convention.

## Proof sources

- Source `solution.tex`, lines 57–68

## Proof dependencies

- `Matrix.blockDiagonal'_apply'` from `Mathlib.Data.Matrix.Block`
- `Matrix.blockDiagonal'_mul` from `Mathlib.Data.Matrix.Block`
- `Matrix.one_apply` from `Mathlib.Data.Matrix.Diagonal`
- `Matrix.ext` from `Mathlib.LinearAlgebra.Matrix.Defs`
- `Matrix.inv_eq_left_inv` from `Mathlib.LinearAlgebra.Matrix.NonsingularInverse`
- `Matrix.isUnit_iff_isUnit_det` from `Mathlib.LinearAlgebra.Matrix.NonsingularInverse`
- `Matrix.nonsing_inv_mul` from `Mathlib.LinearAlgebra.Matrix.NonsingularInverse`
- `Matrix.PosDef.isUnit` from `Mathlib.LinearAlgebra.Matrix.PosDef`
- `Main.RootedCapacity::IsAdmissibleRootedTree` → `IsAdmissibleRootedTree` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.IsAdmissibleRootedTree`
-/
theorem rootedChildGram_blockDiagonal_inv_of_child_admissible {V : Type*} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.IsTree) (w : V → ℤ)
    (ρ : V) :
    let I := {c : V // c ∈ rootedChildren G hG ρ ρ}
    letI : Fintype I := Fintype.ofFinite I
    letI : ∀ c : I, Fintype (rootedChildComponent G ρ c.1) :=
      fun c => Fintype.ofFinite (rootedChildComponent G ρ c.1)
    letI : ∀ c : I, DecidableEq (rootedChildComponent G ρ c.1) :=
      fun c => Classical.decEq (rootedChildComponent G ρ c.1)
    letI : ∀ c : I, DecidableRel (G.deleteEdges {s(ρ, c.1)}).Adj :=
      fun c => Classical.decRel (G.deleteEdges {s(ρ, c.1)}).Adj
    letI : ∀ c : I, DecidableRel (rootedChildComponent G ρ c.1).toSimpleGraph.Adj :=
      fun c => Classical.decRel (rootedChildComponent G ρ c.1).toSimpleGraph.Adj
    let B : ∀ c : I,
        Matrix (rootedChildComponent G ρ c.1) (rootedChildComponent G ρ c.1) ℚ := fun c =>
      rootedGram (rootedChildComponent G ρ c.1).toSimpleGraph (fun x => w (x : V))
    (∀ c : I, IsAdmissibleRootedTree (rootedChildComponent G ρ c.1).toSimpleGraph
      (fun x => w (x : V)) (rootedChildRoot G ρ c.1)) →
      (Matrix.blockDiagonal' B)⁻¹ = Matrix.blockDiagonal' (fun c => (B c)⁻¹) := by
  classical
  intros
  rename_i I B hChild
  letI : Fintype I := Fintype.ofFinite I
  letI : ∀ c : I, Fintype (rootedChildComponent G ρ c.1) :=
    fun c => Fintype.ofFinite _
  letI : ∀ c : I, DecidableEq (rootedChildComponent G ρ c.1) :=
    fun c => Classical.decEq _
  letI : ∀ c : I, DecidableRel (G.deleteEdges {s(ρ, c.1)}).Adj :=
    fun c => Classical.decRel _
  letI : ∀ c : I, DecidableRel (rootedChildComponent G ρ c.1).toSimpleGraph.Adj :=
    fun c => Classical.decRel _
  have hdet : ∀ c : I, IsUnit (B c).det := by
    intro c
    exact (Matrix.isUnit_iff_isUnit_det _).mp (hChild c).2.1.isUnit
  have hmul : ∀ c : I, (B c)⁻¹ * B c = 1 := by
    intro c
    exact Matrix.nonsing_inv_mul (B c) (hdet c)
  apply Matrix.inv_eq_left_inv
  rw [← Matrix.blockDiagonal'_mul]
  simp only [hmul]
  ext ⟨c, x⟩ ⟨d, y⟩
  by_cases h : c = d
  · subst d
    simp [Matrix.one_apply]
  · simp [Matrix.blockDiagonal'_apply', h]
