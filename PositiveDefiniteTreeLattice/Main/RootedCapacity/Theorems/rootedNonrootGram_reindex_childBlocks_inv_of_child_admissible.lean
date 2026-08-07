-- lean-constellation: managed-imports-begin
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Prelude
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.IsAdmissibleRootedTree
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildComponent
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildComponentsEquivNonroot
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildRoot
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildren
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedGram
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.rootedChildGram_blockDiagonal_inv_of_child_admissible
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.rootedNonrootGram_reindex_childBlocks
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

private theorem rootedGram_instance_irrel {U : Type*} (f f' : Fintype U)
    (d d' : DecidableEq U) (H : SimpleGraph U) (r r' : DecidableRel H.Adj) (w : U → ℤ) :
    @rootedGram U f d H r w = @rootedGram U f' d' H r' w := by
  have hf : f = f' := Subsingleton.elim _ _
  have hd : d = d' := Subsingleton.elim _ _
  have hr : r = r' := Subsingleton.elim _ _
  cases hf
  cases hd
  cases hr
  rfl

/--
# lean-constellation target: `rootedNonrootGram_reindex_childBlocks_inv_of_child_admissible`

Let `V` be a finite decidable type, `G` a tree with decidable adjacency, `hG : G.IsTree`, `w : V →
ℤ`, and `ρ : V`.

Define `R := {v : V // v ≠ ρ}`, `I := {c : V // c ∈ rootedChildren G hG ρ ρ}`, and `S := Σ c : I,
rootedChildComponent G ρ c.1`. Use exactly the canonical equivalence `e : R ≃ S :=
(rootedChildComponentsEquivNonroot G hG ρ).symm`, and let `D : Matrix R R ℚ := (rootedGram G
w).submatrix Subtype.val Subtype.val`.

For each `c : I`, under the established canonical `Fintype`, `DecidableEq`, and `DecidableRel`
conventions for `rootedChildComponent G ρ c.1`, define one shared family `B c := rootedGram
(rootedChildComponent G ρ c.1).toSimpleGraph (fun x => w (x : V))`.

Assume only that every attached child component is admissible at its child root:
`∀ c : I, IsAdmissibleRootedTree (rootedChildComponent G ρ c.1).toSimpleGraph (fun x => w (x : V))
(rootedChildRoot G ρ c.1)`.
Then
`Matrix.reindex e e D⁻¹ = Matrix.blockDiagonal' (fun c => (B c)⁻¹)`.

No ambient admissibility assumption on `G` is made.

## Sources

- Source `solution.tex`, lines 57–68

## Statement dependencies

- `SimpleGraph.IsTree` from `Mathlib.Combinatorics.SimpleGraph.Acyclic`
- `SimpleGraph.ConnectedComponent.toSimpleGraph` from
  `Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected`
- `SimpleGraph.deleteEdges` from `Mathlib.Combinatorics.SimpleGraph.DeleteEdges`
- `Fintype.ofFinite` from `Mathlib.Data.Fintype.EquivFin`
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
- `Main.RootedCapacity::rootedChildRoot` → `rootedChildRoot` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildRoot`
- `Main.RootedCapacity::rootedChildren` → `rootedChildren` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildren`
- `Main.RootedCapacity::rootedGram` → `rootedGram` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedGram`

## Proof outline

Introduce the pointwise child-admissibility hypothesis after unfolding the theorem's local `let`
bindings, retaining the exact `R`, `I`, `S`, `e`, `D`, and shared `B` family fixed by the accepted
statement.

Use `Matrix.inv_reindex e e D` in the reverse direction to rewrite `Matrix.reindex e e D⁻¹` as
`(Matrix.reindex e e D)⁻¹`. Rewrite the matrix inside this inverse using the proved provider
`rootedNonrootGram_reindex_childBlocks G hG w ρ`; this yields `(Matrix.blockDiagonal' B)⁻¹` under
the same canonical child-component instances.

Apply `rootedChildGram_blockDiagonal_inv_of_child_admissible G hG w ρ hChild`. Its only hypothesis
is exactly the current pointwise child-component admissibility assumption and its conclusion is the
desired `Matrix.blockDiagonal' (fun c => (B c)⁻¹)`. Finish with `simpa` only to unfold the
syntactically shared local family/instances if Lean exposes their reducible lets. No ambient
admissibility, capacity, or quadratic identity is used.

## Proof sources

- Source `solution.tex`, lines 57–68

## Proof dependencies

- `Matrix.inv_reindex` from `Mathlib.LinearAlgebra.Matrix.NonsingularInverse`
- `Main.RootedCapacity::rootedChildGram_blockDiagonal_inv_of_child_admissible` →
  `rootedChildGram_blockDiagonal_inv_of_child_admissible` from `PositiveDefiniteTreeLattice.Main.Roo
  tedCapacity.Theorems.rootedChildGram_blockDiagonal_inv_of_child_admissible`
- `Main.RootedCapacity::rootedNonrootGram_reindex_childBlocks` →
  `rootedNonrootGram_reindex_childBlocks` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.rootedNonrootGram_reindex_childBlocks`
-/
theorem rootedNonrootGram_reindex_childBlocks_inv_of_child_admissible {V : Type*} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.IsTree) (w : V → ℤ)
    (ρ : V) :
    let R := {v : V // v ≠ ρ}
    let I := {c : V // c ∈ rootedChildren G hG ρ ρ}
    let S := Σ c : I, rootedChildComponent G ρ c.1
    let e : R ≃ S := (rootedChildComponentsEquivNonroot G hG ρ).symm
    let D : Matrix R R ℚ := (rootedGram G w).submatrix Subtype.val Subtype.val
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
      Matrix.reindex e e D⁻¹ = Matrix.blockDiagonal' (fun c => (B c)⁻¹) := by
  classical
  dsimp only
  intro hChild
  rw [← Matrix.inv_reindex]
  rw [rootedNonrootGram_reindex_childBlocks]
  have hB : ∀ c : {c : V // c ∈ rootedChildren G hG ρ ρ},
      (let C := rootedChildComponent G ρ c.1
       letI : Fintype C := Fintype.ofFinite C
       letI : DecidableRel C.toSimpleGraph.Adj := by
         intro x y
         change Decidable ((G.deleteEdges {s(ρ, c.1)}).Adj (x : V) (y : V))
         infer_instance
       rootedGram C.toSimpleGraph (fun x : C => w (x : V))) =
        rootedGram (rootedChildComponent G ρ c.1).toSimpleGraph (fun x => w (x : V)) := by
    intro c
    apply rootedGram_instance_irrel
  have hB' : ∀ c : {c : V // c ∈ rootedChildren G hG ρ ρ},
      (let C := rootedChildComponent G ρ c.1
       letI : Fintype C := Fintype.ofFinite C
       letI : DecidableEq C := Classical.decEq C
       letI : DecidableRel (G.deleteEdges {s(ρ, c.1)}).Adj := Classical.decRel _
       letI : DecidableRel C.toSimpleGraph.Adj := Classical.decRel _
       rootedGram C.toSimpleGraph (fun x : C => w (x : V))) =
        rootedGram (rootedChildComponent G ρ c.1).toSimpleGraph (fun x => w (x : V)) := by
    intro c
    apply rootedGram_instance_irrel
  convert rootedChildGram_blockDiagonal_inv_of_child_admissible G hG w ρ hChild using 1
  · simp only [hB, hB']
    let I := {c : V // c ∈ rootedChildren G hG ρ ρ}
    let S := Σ c : I, rootedChildComponent G ρ c.1
    have matrixInvInstanceIrrel (f f' : Fintype S) (d d' : DecidableEq S)
        (A : Matrix S S ℚ) :
        @Inv.inv (Matrix S S ℚ) (@Matrix.inv S ℚ f d _) A =
          @Inv.inv (Matrix S S ℚ) (@Matrix.inv S ℚ f' d' _) A := by
      have hf : f = f' := Subsingleton.elim _ _
      have hd : d = d' := Subsingleton.elim _ _
      cases hf
      cases hd
      rfl
    apply matrixInvInstanceIrrel
