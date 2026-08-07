-- lean-constellation: managed-imports-begin
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Prelude
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.IsAdmissibleRootedTree
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildCapacitySum
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildCapacitySummand
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildComponentsEquivNonroot
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildRoot
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildren
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedGram
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.rootedChildComponent_parent_not_mem
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.rootedChildComponent_partition
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.rootedChildComponentsEquivNonroot_apply
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.rootedGram_root_nonroot
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.rootedNonroot_inverse_childBlocks
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.treePairing_vertexVector_vertexVector
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `rootedNonroot_inverse_quadratic`

Let V be a finite type with decidable equality, let G be a simple graph on V with decidable
adjacency, let hG : G.IsTree, let w : V → ℤ, let ρ : V, and suppose hAdm : IsAdmissibleRootedTree G
w ρ. Put

R := {v : V // v ≠ ρ}

and let D : Matrix R R ℚ be the principal nonroot submatrix

D := (rootedGram G w).submatrix Subtype.val Subtype.val.

Then the explicit finite inverse quadratic form of the root row equals the child-capacity sum:

∑ x : R, ∑ y : R,
  rootedGram G w ρ (x : V) * D⁻¹ x y * rootedGram G w (y : V) ρ
  = rootedChildCapacitySum G hG w ρ.

The equality uses the rational total inverse of this exact nonroot principal submatrix and the
existing dependent child-capacity definition.

## Sources

- Source `solution.tex`, lines 57–68

## Statement dependencies

- `Finset.sum` from `Mathlib.Algebra.BigOperators.Group.Finset.Defs`
- `SimpleGraph.IsTree` from `Mathlib.Combinatorics.SimpleGraph.Acyclic`
- `Matrix.submatrix` from `Mathlib.LinearAlgebra.Matrix.Defs`
- `Matrix.inv` from `Mathlib.LinearAlgebra.Matrix.NonsingularInverse`
- `Main.RootedCapacity::IsAdmissibleRootedTree` → `IsAdmissibleRootedTree` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.IsAdmissibleRootedTree`
- `Main.RootedCapacity::rootedChildCapacitySum` → `rootedChildCapacitySum` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildCapacitySum`
- `Main.RootedCapacity::rootedGram` → `rootedGram` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedGram`

## Proof outline

Let R and D be the nonroot subtype and its principal Gram block from the accepted statement. Work
classically. Put E := rootedChildComponentsEquivNonroot G hG ρ. Reindex each of the two finite
R-sums along E from the Sigma type of an attached root child and a vertex of its deleted-edge
component. Use `rootedChildComponentsEquivNonroot_apply` to rewrite E ⟨c,x⟩ as the ambient nonroot
vertex with value (x : V), without unfolding E's inverse partition choice; then use `Equiv.sum_comp`
and `Finset.sum_sigma'`.

Replace the reindexed inverse block by `rootedNonroot_inverse_childBlocks G hG w ρ hAdm`. At Sigma
indices, `Matrix.reindex_apply` followed by `Matrix.blockDiagonal'_apply'` says that the inverse
entry is zero for distinct attached-child indices c and d, and for c = d it is the entry of the
inverse rooted Gram matrix of the component indexed by c.

Here is the required root-factor calculation for a fixed attached child c and x :
rootedChildComponent G ρ c.1. Extract hρc : G.Adj ρ c.1 from c.property by the defining membership
clause of `rootedChildren`. Then `rootedChildComponent_parent_not_mem G ρ c.1 hG hρc x` gives hxρ :
(x : V) ≠ ρ. For the row, rewrite the E-image with `rootedChildComponentsEquivNonroot_apply` and
apply `rootedGram_root_nonroot G hG w ρ (x : V) hxρ`.

For the column, do not appeal to an unnamed symmetry. Unfold `rootedGram` at `rootedGram G w (x : V)
ρ` and apply `treePairing_vertexVector_vertexVector G hG w (x : V) ρ`. The hxρ branch removes the
diagonal alternative, and `SimpleGraph.adj_comm` rewrites the remaining `G.Adj (x : V) ρ` test to
`G.Adj ρ (x : V)`. Thus the column is exactly the same `if (x : V) ∈ rootedChildren G hG ρ ρ then
(-1 : ℚ) else 0` as the row.

Prove the precise component support equivalence
`(x : V) ∈ rootedChildren G hG ρ ρ ↔ x = rootedChildRoot G ρ c.1`.
The reverse implication is c.property after coercing `rootedChildRoot`. For the forward implication,
apply the uniqueness clause of `rootedChildComponent_partition G hG ρ (x : V) hxρ`: the candidate
c.1 has c.property and x.property, while the candidate (x : V) has the assumed root-child membership
and belongs to its own deleted-edge component by the canonical member `rootedChildRoot G ρ (x : V)`.
Uniqueness yields (x : V) = c.1; subtype extensionality yields the displayed equality. This argument
is applied separately to the row index x and column index y in the same component.

Consequently, after off-component entries vanish, `Finset.sum_eq_single` twice reduces the c-th
two-variable component sum to the one term x = y = rootedChildRoot G ρ c.1. Its two root factors are
(-1) and (-1), so the term is the diagonal inverse entry of that same child's rooted Gram matrix.
Rewrite this entry directly as `rootedChildCapacitySummand G hG w ρ c`, using the summand's built-in
deleted-edge component, restricted weight, child root, and canonical local instances. Do not invoke
`rootedChildCapacitySum_attach`, recreate raw-child instances, introduce a conversion lemma, or
unfold partition choices. Finally unfold only `rootedChildCapacitySum`; its `Finset.univ` sum is
exactly the outer attached-child sum just obtained.

## Proof sources

- Source `solution.tex`, lines 57–68

## Proof dependencies

- `Finset.sum_eq_single` from `Mathlib.Algebra.BigOperators.Group.Finset.Basic`
- `Equiv.sum_comp` from `Mathlib.Algebra.BigOperators.Group.Finset.Defs`
- `Finset.sum_sigma'` from `Mathlib.Algebra.BigOperators.Group.Finset.Sigma`
- `SimpleGraph.adj_comm` from `Mathlib.Combinatorics.SimpleGraph.Basic`
- `Matrix.blockDiagonal'_apply'` from `Mathlib.Data.Matrix.Block`
- `Matrix.reindex_apply` from `Mathlib.LinearAlgebra.Matrix.Defs`
- `Main.RootedCapacity::rootedChildCapacitySum` → `rootedChildCapacitySum` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildCapacitySum`
- `Main.RootedCapacity::rootedChildCapacitySummand` → `rootedChildCapacitySummand` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildCapacitySummand`
- `Main.RootedCapacity::rootedChildComponent_parent_not_mem` → `rootedChildComponent_parent_not_mem`
  from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.rootedChildComponent_parent_not_mem`
- `Main.RootedCapacity::rootedChildComponent_partition` → `rootedChildComponent_partition` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.rootedChildComponent_partition`
- `Main.RootedCapacity::rootedChildComponentsEquivNonroot` → `rootedChildComponentsEquivNonroot`
  from `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildComponentsEquivNonroot`
- `Main.RootedCapacity::rootedChildComponentsEquivNonroot_apply` →
  `rootedChildComponentsEquivNonroot_apply` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.rootedChildComponentsEquivNonroot_apply`
- `Main.RootedCapacity::rootedChildRoot` → `rootedChildRoot` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildRoot`
- `Main.RootedCapacity::rootedChildren` → `rootedChildren` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildren`
- `Main.RootedCapacity::rootedGram` → `rootedGram` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedGram`
- `Main.RootedCapacity::rootedGram_root_nonroot` → `rootedGram_root_nonroot` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.rootedGram_root_nonroot`
- `Main.RootedCapacity::rootedNonroot_inverse_childBlocks` → `rootedNonroot_inverse_childBlocks`
  from `PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.rootedNonroot_inverse_childBlocks`
- `Main.RootedCapacity::treePairing_vertexVector_vertexVector` →
  `treePairing_vertexVector_vertexVector` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.treePairing_vertexVector_vertexVector`
-/
theorem rootedNonroot_inverse_quadratic {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.IsTree) (w : V → ℤ) (ρ : V)
    (hAdm : IsAdmissibleRootedTree G w ρ) :
    let R := {v : V // v ≠ ρ}
    let D : Matrix R R ℚ := (rootedGram G w).submatrix Subtype.val Subtype.val
    (Finset.sum Finset.univ fun x : R =>
      Finset.sum Finset.univ fun y : R =>
        rootedGram G w ρ (x : V) * D⁻¹ x y * rootedGram G w (y : V) ρ) =
      rootedChildCapacitySum G hG w ρ := by
  classical
  dsimp
  let E := rootedChildComponentsEquivNonroot G hG ρ
  have hE (c : {c : V // c ∈ rootedChildren G hG ρ ρ})
      (x : rootedChildComponent G ρ c.1) :
      E ⟨c, x⟩ =
        ⟨(x : V), rootedChildComponent_parent_not_mem G ρ c.1 hG
          (by
            have hc := c.property
            simp only [rootedChildren, Finset.mem_filter, Finset.mem_univ, true_and] at hc
            exact hc.1) x⟩ := by
    simpa only [E] using rootedChildComponentsEquivNonroot_apply G hG ρ c x
  have hsupport (c : {c : V // c ∈ rootedChildren G hG ρ ρ})
      (x : rootedChildComponent G ρ c.1) :
      (x : V) ∈ rootedChildren G hG ρ ρ ↔ x = rootedChildRoot G ρ c.1 := by
    constructor
    · intro hx
      obtain ⟨a, ha, hua⟩ :=
        rootedChildComponent_partition G hG ρ (x : V)
          (rootedChildComponent_parent_not_mem G ρ c.1 hG
            (by
              have hc := c.property
              simp only [rootedChildren, Finset.mem_filter, Finset.mem_univ, true_and] at hc
              exact hc.1) x)
      have hc : c.1 = a := hua c.1 ⟨c.property, x.property⟩
      have hx' : (x : V) = a := hua (x : V)
        ⟨hx, (rootedChildRoot G ρ (x : V)).property⟩
      apply Subtype.ext
      simpa [rootedChildRoot] using hx'.trans hc.symm
    · rintro rfl
      exact c.property
  have hrow (c : {c : V // c ∈ rootedChildren G hG ρ ρ})
      (x : rootedChildComponent G ρ c.1) :
      rootedGram G w ρ (E ⟨c, x⟩ : V) =
        if (x : V) ∈ rootedChildren G hG ρ ρ then (-1 : ℚ) else 0 := by
    rw [hE c x]
    exact rootedGram_root_nonroot G hG w ρ (x : V)
      (rootedChildComponent_parent_not_mem G ρ c.1 hG
        (by
          have hc := c.property
          simp only [rootedChildren, Finset.mem_filter, Finset.mem_univ, true_and] at hc
          exact hc.1) x)
  have hcolumn (c : {c : V // c ∈ rootedChildren G hG ρ ρ})
      (x : rootedChildComponent G ρ c.1) :
      rootedGram G w (E ⟨c, x⟩ : V) ρ =
        if (x : V) ∈ rootedChildren G hG ρ ρ then (-1 : ℚ) else 0 := by
    rw [hE c x]
    have hsymm : rootedGram G w (x : V) ρ = rootedGram G w ρ (x : V) := by
      unfold rootedGram
      rw [treePairing_vertexVector_vertexVector G hG w]
      rw [treePairing_vertexVector_vertexVector G hG w]
      have hx : (x : V) ≠ ρ :=
        rootedChildComponent_parent_not_mem G ρ c.1 hG
          (by
            have hc := c.property
            simp only [rootedChildren, Finset.mem_filter, Finset.mem_univ, true_and] at hc
            exact hc.1) x
      simp [hx, hx.symm, SimpleGraph.adj_comm]
    rw [hsymm]
    exact rootedGram_root_nonroot G hG w ρ (x : V)
      (rootedChildComponent_parent_not_mem G ρ c.1 hG
        (by
          have hc := c.property
          simp only [rootedChildren, Finset.mem_filter, Finset.mem_univ, true_and] at hc
          exact hc.1) x)
  have hinv (c d : {c : V // c ∈ rootedChildren G hG ρ ρ})
      (x : rootedChildComponent G ρ c.1) (y : rootedChildComponent G ρ d.1) :
      ((rootedGram G w).submatrix Subtype.val Subtype.val)⁻¹
          (E ⟨c, x⟩) (E ⟨d, y⟩) =
        (Matrix.blockDiagonal' (fun c : rootedChildren G hG ρ ρ => by
          letI : Fintype (rootedChildComponent G ρ c.1) := Fintype.ofFinite _
          letI : DecidableRel (rootedChildComponent G ρ c.1).toSimpleGraph.Adj :=
            Classical.decRel _
          exact (rootedGram (rootedChildComponent G ρ c.1).toSimpleGraph
            (fun z => w (z : V)))⁻¹)) ⟨c, x⟩ ⟨d, y⟩ := by
    have h := congrFun
      (congrFun (rootedNonroot_inverse_childBlocks G hG w ρ hAdm) ⟨c, x⟩) ⟨d, y⟩
    simpa only [E, Equiv.symm_symm, Matrix.reindex_apply, Matrix.submatrix_apply] using h
  have hdec (c : {c : V // c ∈ rootedChildren G hG ρ ρ}) :
      Classical.decRel (rootedChildComponent G ρ c.1).toSimpleGraph.Adj =
        (by
          intro x y
          change Decidable ((G.deleteEdges {s(ρ, c.1)}).Adj (x : V) (y : V))
          infer_instance) := Subsingleton.elim _ _
  rw [← E.sum_comp]
  simp_rw [← E.sum_comp]
  rw [Fintype.sum_sigma]
  simp_rw [Fintype.sum_sigma]
  unfold rootedChildCapacitySum
  refine Finset.sum_congr rfl ?_
  intro c hc
  rw [Finset.sum_eq_single (rootedChildRoot G ρ c.1)]
  · rw [Finset.sum_eq_single c]
    · rw [Finset.sum_eq_single (rootedChildRoot G ρ c.1)]
      · simp only [hrow, hcolumn, hinv, hsupport, if_pos,
          Matrix.blockDiagonal'_apply', dite_true, mul_neg, neg_mul, neg_neg]
        rw [hdec c]
        simp [rootedChildCapacitySummand, rootedCapacity]
      · intro y _ hy
        simp [hcolumn c y, hsupport c y, hy]
      · simp
    · intro d _ hdc
      apply Finset.sum_eq_zero
      intro y hy
      have hcd : c ≠ d := fun h => hdc h.symm
      simp [hinv c d (rootedChildRoot G ρ c.1) y,
        Matrix.blockDiagonal'_apply', hcd]
    · simp
  · intro x _ hx
    apply Finset.sum_eq_zero
    intro d hd
    apply Finset.sum_eq_zero
    intro y hy
    simp [hrow c x, hsupport c x, hx]
  · simp
