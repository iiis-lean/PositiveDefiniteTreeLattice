[← Public API](../PUBLIC_API.md) · [Public boundaries](../PUBLIC_BOUNDARIES.md) · [Complete graph](../DECLARATION_GRAPH.md)

# `rootedGram_posDef_of_integer_positive`

Integer positivity of the tree pairing yields positive definiteness of the rational rooted Gram matrix.

- Kind: `lemma`
- Node: `Main.IrreducibleVertex`
- Module: `PositiveDefiniteTreeLattice.Main.IrreducibleVertex.Lemmas.rootedGram_posDef_of_integer_positive`
- State: `proved`
- Revision status: `committed`
- Repository completion: `graph_proved`
- Compatibility `formal_code`: final proof projection

## Statement NL

Let `V` be a finite type with decidable equality, let `G : SimpleGraph V` have decidable adjacency, and let `weight : V → ℤ`. If `h_positive : ∀ x : V → ℤ, x ≠ 0 → 0 < treePairing G weight x x`, then the rational matrix `rootedGram G weight` is positive definite: `Matrix.PosDef (rootedGram G weight)`.

## Statement Formal

```lean
-- lean-constellation: managed-imports-begin
import PositiveDefiniteTreeLattice.Main.IrreducibleVertex.Prelude
import Mathlib.LinearAlgebra.Matrix.PosDef
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `rootedGram_posDef_of_integer_positive`

Let `V` be a finite type with decidable equality, let `G : SimpleGraph V` have decidable adjacency,
and let `weight : V → ℤ`. If `h_positive : ∀ x : V → ℤ, x ≠ 0 → 0 < treePairing G weight x x`, then
the rational matrix `rootedGram G weight` is positive definite: `Matrix.PosDef (rootedGram G
weight)`.

## Sources

- Source `solution.tex`, line 196

## Statement dependencies

- `Matrix.PosDef` from `Mathlib.LinearAlgebra.Matrix.PosDef`
- `Main.LatticeFoundations::treePairingAnchor` → `PositiveDefiniteTreeLattice.treePairing` from
  `PositiveDefiniteTreeLattice.Main.LatticeFoundations.Defs.treePairingAnchor`
- `Main.RootedCapacity::rootedGram` → `rootedGram` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedGram`
-/
theorem PositiveDefiniteTreeLattice.rootedGram_posDef_of_integer_positive {V : Type*} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (weight : V → ℤ)
    (h_positive : ∀ x : V → ℤ, x ≠ 0 → 0 < PositiveDefiniteTreeLattice.treePairing G weight x x) :
    Matrix.PosDef (rootedGram G weight) := by
  sorry
```

## Proof NL

Apply `Matrix.PosDef.of_dotProduct_mulVec_pos`. For Hermitian symmetry, unfold `rootedGram` and `Matrix.IsHermitian`; the off-diagonal entries are equal after applying the tracked symmetry theorem `treePairing_symm` to the two vertex vectors (over `ℚ`, conjugation is trivial).

For strict positivity, fix a nonzero rational coordinate vector `q : V → ℚ` (equivalently the finite-support vector required by `Matrix.PosDef`). Since `V` is finite, clear the finitely many coordinate denominators: choose a positive natural `D` divisible by every denominator and define an integer vector `z` by `(z u : ℚ) = D * q u`. The nonzeroness of `q` and `D ≠ 0` give `z ≠ 0`.

Establish the representation identity
`((treePairing G weight z z : ℤ) : ℚ) = (D : ℚ)^2 * (star q ⬝ᵥ (rootedGram G weight *ᵥ q))`.
This is a local finite-sum calculation: unfold `rootedGram`, `treePairing`, `vertexVector`, `Matrix.mulVec`, and `dotProduct`; substitute the coordinate identities for `z`; then normalize casts and finite sums with `ring`. It preserves the original integral pairing rather than assuming positivity on rational vectors.

Apply `h_positive z hz` and cast its strict inequality to `ℚ`. The representation identity and positivity of the nonzero square `(D : ℚ)^2` imply the desired strict positivity of the rational quadratic expression. This completes `Matrix.PosDef` without strengthening `h_positive`.

## Proof Formal

```lean
-- lean-constellation: managed-imports-begin
import PositiveDefiniteTreeLattice.Main.IrreducibleVertex.Prelude
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Ring.Rat
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.PosDef
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `rootedGram_posDef_of_integer_positive`

Let `V` be a finite type with decidable equality, let `G : SimpleGraph V` have decidable adjacency,
and let `weight : V → ℤ`. If `h_positive : ∀ x : V → ℤ, x ≠ 0 → 0 < treePairing G weight x x`, then
the rational matrix `rootedGram G weight` is positive definite: `Matrix.PosDef (rootedGram G
weight)`.

## Sources

- Source `solution.tex`, line 196

## Statement dependencies

- `Matrix.PosDef` from `Mathlib.LinearAlgebra.Matrix.PosDef`
- `Main.LatticeFoundations::treePairingAnchor` → `PositiveDefiniteTreeLattice.treePairing` from
  `PositiveDefiniteTreeLattice.Main.LatticeFoundations.Defs.treePairingAnchor`
- `Main.RootedCapacity::rootedGram` → `rootedGram` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedGram`

## Proof outline

Apply `Matrix.PosDef.of_dotProduct_mulVec_pos`. For Hermitian symmetry, unfold `rootedGram` and
`Matrix.IsHermitian`; the off-diagonal entries are equal after applying the tracked symmetry theorem
`treePairing_symm` to the two vertex vectors (over `ℚ`, conjugation is trivial).

For strict positivity, fix a nonzero rational coordinate vector `q : V → ℚ` (equivalently the
finite-support vector required by `Matrix.PosDef`). Since `V` is finite, clear the finitely many
coordinate denominators: choose a positive natural `D` divisible by every denominator and define an
integer vector `z` by `(z u : ℚ) = D * q u`. The nonzeroness of `q` and `D ≠ 0` give `z ≠ 0`.

Establish the representation identity
`((treePairing G weight z z : ℤ) : ℚ) = (D : ℚ)^2 * (star q ⬝ᵥ (rootedGram G weight *ᵥ q))`.
This is a local finite-sum calculation: unfold `rootedGram`, `treePairing`, `vertexVector`,
`Matrix.mulVec`, and `dotProduct`; substitute the coordinate identities for `z`; then normalize
casts and finite sums with `ring`. It preserves the original integral pairing rather than assuming
positivity on rational vectors.

Apply `h_positive z hz` and cast its strict inequality to `ℚ`. The representation identity and
positivity of the nonzero square `(D : ℚ)^2` imply the desired strict positivity of the rational
quadratic expression. This completes `Matrix.PosDef` without strengthening `h_positive`.

## Proof sources

- Source `solution.tex`, line 196

## Proof dependencies

- `Finset.mul_prod_erase` from `Mathlib.Algebra.BigOperators.Group.Finset.Basic`
- `Rat.mul_den_eq_num` from `Mathlib.Algebra.Ring.Rat`
- `SimpleGraph.neighborFinset_eq_filter` from `Mathlib.Combinatorics.SimpleGraph.Finite`
- `Matrix.isHermitian_iff_isSymm` from `Mathlib.LinearAlgebra.Matrix.Hermitian`
- `Matrix.PosDef.of_dotProduct_mulVec_pos` from `Mathlib.LinearAlgebra.Matrix.PosDef`
- `Main.LatticeFoundations::treePairing_symm` → `PositiveDefiniteTreeLattice.treePairing_symm` from
  `PositiveDefiniteTreeLattice.Main.LatticeFoundations.Theorems.treePairing_symm`
-/
theorem PositiveDefiniteTreeLattice.rootedGram_posDef_of_integer_positive {V : Type*} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (weight : V → ℤ)
    (h_positive : ∀ x : V → ℤ, x ≠ 0 → 0 < PositiveDefiniteTreeLattice.treePairing G weight x x) :
    Matrix.PosDef (rootedGram G weight) := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_
  · apply Matrix.isHermitian_iff_isSymm.mpr
    ext u v
    simp only [Matrix.transpose_apply, rootedGram]
    exact_mod_cast (PositiveDefiniteTreeLattice.treePairing_symm G weight
      (PositiveDefiniteTreeLattice.vertexVector u)
      (PositiveDefiniteTreeLattice.vertexVector v)).symm
  · intro q hq
    let D : ℕ := ∏ u, (q u).den
    let z : V → ℤ := fun u => (q u).num * ∏ w ∈ Finset.univ.erase u, (q w).den
    have hz_scale (u : V) : (z u : ℚ) = D * q u := by
      simp only [z, D]
      push_cast
      rw [← Rat.mul_den_eq_num (q u)]
      have hprod : (q u).den * ∏ w ∈ Finset.univ.erase u, (q w).den =
          ∏ w, (q w).den :=
        Finset.mul_prod_erase Finset.univ (fun w => (q w).den) (Finset.mem_univ u)
      have hprodQ : (↑(q u).den : ℚ) * ∏ w ∈ Finset.univ.erase u, ↑(q w).den =
          ∏ w, ↑(q w).den := by
        exact_mod_cast hprod
      rw [← hprodQ]
      ring
    have hD_pos : 0 < D := by
      dsimp [D]
      positivity
    have hz_ne : z ≠ 0 := by
      intro hz
      apply hq
      ext u
      have hu := hz_scale u
      rw [hz] at hu
      exact (mul_eq_zero.mp hu.symm).resolve_left (by exact_mod_cast (ne_of_gt hD_pos))
    have hquad : ((PositiveDefiniteTreeLattice.treePairing G weight z z : ℤ) : ℚ) =
        (D : ℚ) ^ 2 * dotProduct (star (q : V → ℚ))
          (Matrix.mulVec (rootedGram G weight) (q : V → ℚ)) := by
      simp only [rootedGram, Matrix.mulVec, dotProduct, star_trivial]
      simp only [PositiveDefiniteTreeLattice.treePairing]
      simp only [Int.cast_sum, Int.cast_mul, Int.cast_sub, PositiveDefiniteTreeLattice.vertexVector,
        mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', SimpleGraph.mem_neighborFinset, ite_mul,
        one_mul, zero_mul, Finset.mem_univ, reduceIte, Int.cast_ite, Int.cast_zero, Int.cast_one]
      simp_rw [hz_scale]
      simp_rw [SimpleGraph.neighborFinset_eq_filter]
      simp only [Finset.sum_filter]
      ring_nf
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      have hscale_inner : (∑ y, if G.Adj x y then (D : ℚ) * q y else 0) =
          (D : ℚ) * ∑ y, if G.Adj x y then q y else 0 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro y _
        by_cases hxy : G.Adj x y
        · simp [hxy]
        · simp [hxy]
      rw [hscale_inner]
      have hbase : (∑ y, ((if x = y then (weight x : ℚ) else 0) * q y -
          (if G.Adj x y then 1 else 0) * q y)) =
          (weight x : ℚ) * q x - ∑ y, if G.Adj x y then q y else 0 := by
        simp only [ite_mul, zero_mul, one_mul, Finset.sum_sub_distrib, Finset.sum_ite_eq,
          Finset.mem_univ, reduceIte]
      rw [hbase]
      ring
    have hpair_pos : 0 < ((PositiveDefiniteTreeLattice.treePairing G weight z z : ℤ) : ℚ) := by
      exact_mod_cast h_positive z hz_ne
    have hD_pos_Q : 0 < (D : ℚ) := by
      exact_mod_cast hD_pos
    have hD_sq_pos : 0 < (D : ℚ) ^ 2 := sq_pos_of_pos hD_pos_Q
    have hmul : 0 < (D : ℚ) ^ 2 * dotProduct (star (q : V → ℚ))
        (Matrix.mulVec (rootedGram G weight) (q : V → ℚ)) := by
      rw [← hquad]
      exact hpair_pos
    rcases (mul_pos_iff.mp hmul) with hpos | hneg
    · exact hpos.2
    · linarith
```

## Statement dependencies

- `Mathlib:Mathlib.LinearAlgebra.Matrix.PosDef.Matrix.PosDef`
- `current repo:Main.LatticeFoundations.treePairingAnchor`
- `current repo:Main.RootedCapacity.rootedGram`

## Proof dependencies

- `Mathlib:Mathlib.Algebra.BigOperators.Group.Finset.Basic.Finset.mul_prod_erase`
- `Mathlib:Mathlib.Algebra.Ring.Rat.Rat.mul_den_eq_num`
- `Mathlib:Mathlib.Combinatorics.SimpleGraph.Finite.SimpleGraph.neighborFinset_eq_filter`
- `Mathlib:Mathlib.LinearAlgebra.Matrix.Hermitian.Matrix.isHermitian_iff_isSymm`
- `Mathlib:Mathlib.LinearAlgebra.Matrix.PosDef.Matrix.PosDef.of_dotProduct_mulVec_pos`
- `current repo:Main.LatticeFoundations.treePairing_symm`

## Sources

- `solution.tex:196-196`
