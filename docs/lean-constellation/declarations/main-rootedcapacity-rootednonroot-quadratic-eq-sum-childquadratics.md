[← Public API](../PUBLIC_API.md) · [Public boundaries](../PUBLIC_BOUNDARIES.md)

# `rootedNonroot_quadratic_eq_sum_childQuadratics`

The nonroot rooted-Gram quadratic form splits canonically as the sum of the child-component quadratic forms.

- Kind: `theorem`
- Node: `Main.RootedCapacity`
- Module: `PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.rootedNonroot_quadratic_eq_sum_childQuadratics`
- State: `proved`
- Revision status: `committed`
- Repository completion: `graph_proved`
- Formal code: final proof projection

## Lean code

```lean
-- lean-constellation: managed-imports-begin
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Prelude
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Data.Fintype.EquivFin
import Mathlib.LinearAlgebra.Matrix.Defs
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildComponent
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildComponentsEquivNonroot
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildren
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedGram
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.blockDiagonal_quadratic_eq_sum_blocks
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.rootedNonrootGram_reindex_childBlocks
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `rootedNonroot_quadratic_eq_sum_childQuadratics`

Let `V` be a finite vertex type with decidable equality, let `G : SimpleGraph V` have decidable
adjacency and satisfy `hG : G.IsTree`, let `w : V → ℤ`, and fix `ρ : V`. Use exactly the convention
of `rootedNonrootGram_reindex_childBlocks`: set `R := {v : V // v ≠ ρ}`, `I := {c : V // c ∈
rootedChildren G hG ρ ρ}`, `S c := rootedChildComponent G ρ c.1`, `e : R ≃ Σ c : I, S c :=
(rootedChildComponentsEquivNonroot G hG ρ).symm`, and `D : Matrix R R ℚ := (rootedGram G
w).submatrix Subtype.val Subtype.val`. For each `c : I`, let `B c` be the rooted Gram matrix of the
child-component graph `(S c).toSimpleGraph` with the coefficient function induced by `w`, using the
same component `Fintype` and decidable-adjacency instances as in that reindex theorem.

Then, for every coefficient function `a : R → ℚ`, the ordered nonroot quadratic double sum splits
into the ordered within-child quadratic double sums:

`∑ x : R, ∑ y : R, a x * D x y * a y = ∑ c : I, ∑ x : S c, ∑ y : S c, a (e.symm ⟨c, x⟩) * B c x y *
a (e.symm ⟨c, y⟩)`.

This public statement leaves no cross-child or Sigma-wide remainder and adds no admissibility,
unique-underweight, integral pairing, or root-interaction hypothesis.

## Sources

- Source `solution.tex`, lines 57–68

## Statement dependencies

- `Fintype.ofFinite` from `Mathlib.Data.Fintype.EquivFin`
- `Matrix.submatrix` from `Mathlib.LinearAlgebra.Matrix.Defs`
- `Main.RootedCapacity::rootedChildComponent` → `rootedChildComponent` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildComponent`
- `Main.RootedCapacity::rootedChildComponentsEquivNonroot` → `rootedChildComponentsEquivNonroot`
  from `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildComponentsEquivNonroot`
- `Main.RootedCapacity::rootedChildren` → `rootedChildren` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildren`
- `Main.RootedCapacity::rootedGram` → `rootedGram` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedGram`

## Proof outline

Work under `classical`, unfold only the accepted local `R`, Sigma-family `S`, equivalence `e`,
nonroot block `D`, and the already fixed component instances/family `B`, then introduce the
arbitrary coefficient function `a : R → ℚ`.

Transport the outer and inner ordered finite sums from `R` to the Sigma type using `(e.symm.sum_comp
_).symm` twice. The transported coefficient at `u : Σ c, S c` is exactly `a (e.symm u)`. Change the
transported matrix entry `D (e.symm u) (e.symm v)` to the corresponding entry of `Matrix.reindex e e
D`; this uses the existing orientation of `e` without introducing a new representation or
equivalence.

Rewrite `Matrix.reindex e e D` by the proved `rootedNonrootGram_reindex_childBlocks G hG w ρ`, whose
`R`, Sigma fibers, component `Fintype` instances, and child rooted-Gram family are definitionally
the same canonical ones fixed in the public statement. The goal is then the generic dependent
block-diagonal quadratic identity with coefficient function `fun u => a (e.symm u)`. Apply the
proved private provider `blockDiagonal_quadratic_eq_sum_blocks`; its right-hand side is
definitionally the required sum over each child component and leaves no cross-child or Sigma-wide
remainder.

Thus the proof is solely two equivalence-sum transports, the committed child-block reindex equality,
and the committed finite-sum helper; it adds no admissibility or other hypotheses.

## Proof sources

- Source `solution.tex`, lines 57–62

## Proof dependencies

- `Finset.sum_congr` from `Mathlib.Algebra.BigOperators.Group.Finset.Basic`
- `Equiv.sum_comp` from `Mathlib.Algebra.BigOperators.Group.Finset.Defs`
- `Matrix.reindex` from `Mathlib.LinearAlgebra.Matrix.Defs`
- `Main.RootedCapacity::blockDiagonal_quadratic_eq_sum_blocks` →
  `blockDiagonal_quadratic_eq_sum_blocks` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.blockDiagonal_quadratic_eq_sum_blocks`
- `Main.RootedCapacity::rootedNonrootGram_reindex_childBlocks` →
  `rootedNonrootGram_reindex_childBlocks` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.rootedNonrootGram_reindex_childBlocks`
-/
theorem rootedNonroot_quadratic_eq_sum_childQuadratics {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.IsTree) (w : V → ℤ) (ρ : V) :
    let R := {v : V // v ≠ ρ}
    let S := Σ c : {c : V // c ∈ rootedChildren G hG ρ ρ}, rootedChildComponent G ρ c.1
    let e : R ≃ S := (rootedChildComponentsEquivNonroot G hG ρ).symm
    let D : Matrix R R ℚ := (rootedGram G w).submatrix Subtype.val Subtype.val
    letI : ∀ c : {c : V // c ∈ rootedChildren G hG ρ ρ},
        Fintype (rootedChildComponent G ρ c.1) := fun c =>
      Fintype.ofFinite (rootedChildComponent G ρ c.1)
    let B : ∀ c : {c : V // c ∈ rootedChildren G hG ρ ρ},
        Matrix (rootedChildComponent G ρ c.1) (rootedChildComponent G ρ c.1) ℚ := fun c =>
      let C := rootedChildComponent G ρ c.1
      letI : Fintype C := Fintype.ofFinite C
      letI : DecidableRel C.toSimpleGraph.Adj := by
        intro x y
        change Decidable ((G.deleteEdges {s(ρ, c.1)}).Adj (x : V) (y : V))
        infer_instance
      rootedGram C.toSimpleGraph (fun x : C => w (x : V))
    ∀ a : R → ℚ,
      (∑ x : R, ∑ y : R, a x * D x y * a y) =
        ∑ c : {c : V // c ∈ rootedChildren G hG ρ ρ},
          ∑ x : rootedChildComponent G ρ c.1,
            ∑ y : rootedChildComponent G ρ c.1,
              a (e.symm ⟨c, x⟩) * B c x y * a (e.symm ⟨c, y⟩) := by
  classical
  dsimp only
  intro a
  letI : ∀ c : {c : V // c ∈ rootedChildren G hG ρ ρ},
      Fintype (rootedChildComponent G ρ c.1) := fun c =>
    Fintype.ofFinite (rootedChildComponent G ρ c.1)
  let B : ∀ c : {c : V // c ∈ rootedChildren G hG ρ ρ},
      Matrix (rootedChildComponent G ρ c.1) (rootedChildComponent G ρ c.1) ℚ := fun c =>
    let C := rootedChildComponent G ρ c.1
    letI : Fintype C := Fintype.ofFinite C
    letI : DecidableRel C.toSimpleGraph.Adj := by
      intro x y
      change Decidable ((G.deleteEdges {s(ρ, c.1)}).Adj (x : V) (y : V))
      infer_instance
    rootedGram C.toSimpleGraph (fun x : C => w (x : V))
  rw [((rootedChildComponentsEquivNonroot G hG ρ).sum_comp
    (fun x : {v : V // v ≠ ρ} =>
      ∑ y : {v : V // v ≠ ρ}, a x *
        (rootedGram G w).submatrix Subtype.val Subtype.val x y * a y)).symm]
  calc
    _ = ∑ i : (Σ c : {c : V // c ∈ rootedChildren G hG ρ ρ},
        rootedChildComponent G ρ c.1),
        ∑ j : (Σ c : {c : V // c ∈ rootedChildren G hG ρ ρ},
          rootedChildComponent G ρ c.1),
          a ((rootedChildComponentsEquivNonroot G hG ρ) i) *
            (rootedGram G w).submatrix Subtype.val Subtype.val
              ((rootedChildComponentsEquivNonroot G hG ρ) i)
              ((rootedChildComponentsEquivNonroot G hG ρ) j) *
            a ((rootedChildComponentsEquivNonroot G hG ρ) j) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [((rootedChildComponentsEquivNonroot G hG ρ).sum_comp
        (fun y : {v : V // v ≠ ρ} =>
          a ((rootedChildComponentsEquivNonroot G hG ρ) i) *
            (rootedGram G w).submatrix Subtype.val Subtype.val
              ((rootedChildComponentsEquivNonroot G hG ρ) i) y * a y)).symm]
    _ = _ := by
      change (∑ i : (Σ c : {c : V // c ∈ rootedChildren G hG ρ ρ},
          rootedChildComponent G ρ c.1),
          ∑ j : (Σ c : {c : V // c ∈ rootedChildren G hG ρ ρ},
            rootedChildComponent G ρ c.1),
            a ((rootedChildComponentsEquivNonroot G hG ρ) i) *
              Matrix.reindex (rootedChildComponentsEquivNonroot G hG ρ).symm
                (rootedChildComponentsEquivNonroot G hG ρ).symm
                ((rootedGram G w).submatrix Subtype.val Subtype.val) i j *
              a ((rootedChildComponentsEquivNonroot G hG ρ) j)) =
          ∑ c : {c : V // c ∈ rootedChildren G hG ρ ρ},
            ∑ x : rootedChildComponent G ρ c.1,
              ∑ y : rootedChildComponent G ρ c.1,
                a ((rootedChildComponentsEquivNonroot G hG ρ) ⟨c, x⟩) *
                  B c x y *
                  a ((rootedChildComponentsEquivNonroot G hG ρ) ⟨c, y⟩)
      rw [rootedNonrootGram_reindex_childBlocks G hG w ρ]
      convert blockDiagonal_quadratic_eq_sum_blocks
        {c : V // c ∈ rootedChildren G hG ρ ρ}
        (fun c => rootedChildComponent G ρ c.1)
        B
        (fun i => a ((rootedChildComponentsEquivNonroot G hG ρ) i))
        using 1
      · have hdec :
            (fun c d : {c : V // c ∈ rootedChildren G hG ρ ρ} => c.instDecidableEq d) =
              Classical.decEq {c : V // c ∈ rootedChildren G hG ρ ρ} :=
          Subsingleton.elim _ _
        rw [hdec]
```

## Statement dependencies

- `Mathlib:Mathlib.Data.Fintype.EquivFin.Fintype.ofFinite`
- `Mathlib:Mathlib.LinearAlgebra.Matrix.Defs.Matrix.submatrix`
- `current repo:Main.RootedCapacity.rootedChildComponent`
- `current repo:Main.RootedCapacity.rootedChildComponentsEquivNonroot`
- `current repo:Main.RootedCapacity.rootedChildren`
- `current repo:Main.RootedCapacity.rootedGram`

## Proof dependencies

- `Mathlib:Mathlib.Algebra.BigOperators.Group.Finset.Basic.Finset.sum_congr`
- `Mathlib:Mathlib.Algebra.BigOperators.Group.Finset.Defs.Equiv.sum_comp`
- `Mathlib:Mathlib.LinearAlgebra.Matrix.Defs.Matrix.reindex`
- `current repo:Main.RootedCapacity.blockDiagonal_quadratic_eq_sum_blocks`
- `current repo:Main.RootedCapacity.rootedNonrootGram_reindex_childBlocks`

## Sources

- `solution.tex:57-68`
