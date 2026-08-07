[← Public API](../PUBLIC_API.md) · [Public boundaries](../PUBLIC_BOUNDARIES.md)

# `exists_irreducible_vertex`

A positive-definite integer-weighted finite tree with a unique underweighted vertex has an irreducible vertex vector.

- Kind: `theorem`
- Node: `Main.IrreducibleVertex`
- Module: `PositiveDefiniteTreeLattice.Main.IrreducibleVertex.Theorems.exists_irreducible_vertex`
- State: `proved`
- Revision status: `committed`
- Repository completion: `graph_proved`
- Formal code: final proof projection

## Lean code

```lean
-- lean-constellation: managed-imports-begin
import PositiveDefiniteTreeLattice.Main.IrreducibleVertex.Prelude
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Tactic.IntervalCases
import PositiveDefiniteTreeLattice.Main.IrreducibleVertex.Lemmas.irreducible_vertex_of_weight_eq_one
import PositiveDefiniteTreeLattice.Main.IrreducibleVertex.Lemmas.normalized_pairing_positive_of_unique_underweight
import PositiveDefiniteTreeLattice.Main.IrreducibleVertex.Lemmas.weight_ge_two_of_ne_one
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

namespace PositiveDefiniteTreeLattice

/--
# lean-constellation target: `exists_irreducible_vertex`

Let `V` be a finite type with decidable equality, let `G : SimpleGraph V` have decidable adjacency,
and let `weight : V → ℤ`. Assume that `G` is a tree, that the integral tree pairing is positive
definite on every nonzero integer vector—namely, for every `x : V → ℤ` with `x ≠ 0`, `0 <
treePairing G weight x x`—and that there exists exactly one vertex `v` with `weight v < (G.degree v
: ℤ)`. Then there exists a vertex `v : V` such that the vertex vector `vertexVector v` is
irreducible for `G` and `weight`, i.e. `Irreducible G weight (vertexVector v)`.

## Sources

- Source `formal_target.lean`, lines 24–33
- Source `solution.tex`, lines 182–186

## Statement dependencies

- `SimpleGraph.IsTree` from `Mathlib.Combinatorics.SimpleGraph.Acyclic`
- `SimpleGraph` from `Mathlib.Combinatorics.SimpleGraph.Basic`
- `SimpleGraph.degree` from `Mathlib.Combinatorics.SimpleGraph.Finite`
- `Main.LatticeFoundations::IrreducibleAnchor` → `PositiveDefiniteTreeLattice.Irreducible` from
  `PositiveDefiniteTreeLattice.Main.LatticeFoundations.Defs.IrreducibleAnchor`
- `Main.LatticeFoundations::treePairingAnchor` → `PositiveDefiniteTreeLattice.treePairing` from
  `PositiveDefiniteTreeLattice.Main.LatticeFoundations.Defs.treePairingAnchor`
- `Main.LatticeFoundations::vertexVectorAnchor` → `PositiveDefiniteTreeLattice.vertexVector` from
  `PositiveDefiniteTreeLattice.Main.LatticeFoundations.Defs.vertexVectorAnchor`

## Proof outline

Use the source proof on solution.tex:182–244. First split on `∃ u : V, weight u = 1`. In the
positive case choose u and return `⟨u, irreducible_vertex_of_weight_eq_one G weight u h_positive
hu⟩`. This is the source’s weight-one alternative and needs no relation between u and the unique
underweighted vertex. In the negative case obtain the unique underweighted vertex `v` from
`h_unique_underweight`, retaining both `hv : weight v < (G.degree v : ℤ)` and uniqueness. The
no-weight-one assumption and `weight_ge_two_of_ne_one G weight x h_positive` give `h_two : ∀ x, 2 ≤
weight x`.

It remains to prove `Irreducible G weight (vertexVector v)`. Unfold only the accepted Irreducible
interface and suppose a forbidden decomposition `vertexVector v = a + b` with `ha : a ≠ 0`, `hb : b
≠ 0`, and `hab : 0 ≤ treePairing G weight a b`. Put `z := -b`. Coordinatewise algebra from the
decomposition gives `a = vertexVector v + z`, while hb proves `z ≠ 0` (and ha also gives `z ≠ -
vertexVector v`). Using `treePairing_add_left`, `treePairing_add_right`, `treePairing_add_self`, and
`treePairing_symm` in their accepted orientations, expand
`treePairing G weight z z + treePairing G weight (vertexVector v) z`
after substituting `z=-b` and `vertexVector v=a+b`. The additive/negation normalization yields
exactly `- treePairing G weight a b`, hence the shifted pairing is nonpositive by hab.

Let `q := z v`. If `0 ≤ q`, apply `normalized_pairing_positive_of_unique_underweight G weight v z
h_tree h_positive h_unique_underweight hv h_two` with the established nonzeroness and
root-coefficient inequality. Its strict positivity contradicts the nonpositive shifted pairing.

Otherwise, `Int.le_sub_one_of_not_le` gives `q ≤ -1`. Define `z' := - vertexVector v - z`, which is
coordinatewise `-a` by the decomposition. Thus `z' ≠ 0` follows from ha. Unfolding only the accepted
vertexVector definition at v shows `z' v = -1-q ≥ 0`. Apply the same normalized lemma to z'. A
second expansion using `treePairing_add_left`, `treePairing_add_right`, `treePairing_add_self`, and
`treePairing_symm` shows the exact invariance
`treePairing G weight z' z' + treePairing G weight (vertexVector v) z' =
 treePairing G weight z z + treePairing G weight (vertexVector v) z`.
Therefore z' also gives strict positivity of the already nonpositive shifted pairing, a
contradiction. Both coefficient cases rule out the forbidden decomposition, so v is irreducible and
provides the required existential witness.

## Proof sources

- Source `solution.tex`, lines 182–244

## Proof dependencies

- `Finset.sum_congr` from `Mathlib.Algebra.BigOperators.Group.Finset.Basic`
- `Finset.sum_neg_distrib` from `Mathlib.Algebra.BigOperators.Group.Finset.Defs`
- `Int.le_sub_one_of_not_le` from `Mathlib.Tactic.IntervalCases`
- `Main.IrreducibleVertex::irreducible_vertex_of_weight_eq_one` →
  `PositiveDefiniteTreeLattice.irreducible_vertex_of_weight_eq_one` from
  `PositiveDefiniteTreeLattice.Main.IrreducibleVertex.Lemmas.irreducible_vertex_of_weight_eq_one`
- `Main.IrreducibleVertex::normalized_pairing_positive_of_unique_underweight` →
  `PositiveDefiniteTreeLattice.normalized_pairing_positive_of_unique_underweight` from `PositiveDefi
  niteTreeLattice.Main.IrreducibleVertex.Lemmas.normalized_pairing_positive_of_unique_underweight`
- `Main.IrreducibleVertex::weight_ge_two_of_ne_one` →
  `PositiveDefiniteTreeLattice.weight_ge_two_of_ne_one` from
  `PositiveDefiniteTreeLattice.Main.IrreducibleVertex.Lemmas.weight_ge_two_of_ne_one`
- `Main.LatticeFoundations::IrreducibleAnchor` → `PositiveDefiniteTreeLattice.Irreducible` from
  `PositiveDefiniteTreeLattice.Main.LatticeFoundations.Defs.IrreducibleAnchor`
- `Main.LatticeFoundations::treePairing_add_left` →
  `PositiveDefiniteTreeLattice.treePairing_add_left` from
  `PositiveDefiniteTreeLattice.Main.LatticeFoundations.Theorems.treePairing_add_left`
- `Main.LatticeFoundations::treePairing_add_right` →
  `PositiveDefiniteTreeLattice.treePairing_add_right` from
  `PositiveDefiniteTreeLattice.Main.LatticeFoundations.Theorems.treePairing_add_right`
- `Main.LatticeFoundations::treePairing_add_self` →
  `PositiveDefiniteTreeLattice.treePairing_add_self` from
  `PositiveDefiniteTreeLattice.Main.LatticeFoundations.Theorems.treePairing_add_self`
- `Main.LatticeFoundations::treePairing_symm` → `PositiveDefiniteTreeLattice.treePairing_symm` from
  `PositiveDefiniteTreeLattice.Main.LatticeFoundations.Theorems.treePairing_symm`
- `Main.LatticeFoundations::vertexVectorAnchor` → `PositiveDefiniteTreeLattice.vertexVector` from
  `PositiveDefiniteTreeLattice.Main.LatticeFoundations.Defs.vertexVectorAnchor`
-/
theorem exists_irreducible_vertex
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (weight : V → ℤ) (h_tree : G.IsTree)
    (h_positive : ∀ x : V → ℤ, x ≠ 0 → 0 < treePairing G weight x x)
    (h_unique_underweight : ∃! v : V, weight v < (G.degree v : ℤ)) :
    ∃ v : V, Irreducible G weight (vertexVector v) := by
  classical
  by_cases h_one : ∃ u : V, weight u = 1
  · obtain ⟨u, hu⟩ := h_one
    exact ⟨u, irreducible_vertex_of_weight_eq_one G weight u h_positive hu⟩
  · rcases h_unique_underweight with ⟨v, hv, huniq⟩
    have h_two : ∀ x : V, 2 ≤ weight x := by
      intro x
      apply weight_ge_two_of_ne_one G weight x h_positive
      intro hx
      exact h_one ⟨x, hx⟩
    refine ⟨v, ?_⟩
    unfold Irreducible
    rintro ⟨a, b, ha, hb, hab, hcross⟩
    have pairing_neg_left (x y : V → ℤ) :
        treePairing G weight (-x) y = -treePairing G weight x y := by
      unfold treePairing
      calc
        (∑ u, (-x) u * (weight u * y u -
          ∑ w ∈ G.neighborFinset u, y w)) =
            ∑ u, -(x u * (weight u * y u - ∑ w ∈ G.neighborFinset u, y w)) := by
              apply Finset.sum_congr rfl
              intro u _
              simp only [Pi.neg_apply, neg_mul]
        _ = -(∑ u, x u * (weight u * y u -
          ∑ w ∈ G.neighborFinset u, y w)) := by
            exact Finset.sum_neg_distrib (s := Finset.univ)
              (fun u : V => x u * (weight u * y u -
                ∑ w ∈ G.neighborFinset u, y w))
    have pairing_neg_right (x y : V → ℤ) :
        treePairing G weight x (-y) = -treePairing G weight x y := by
      unfold treePairing
      calc
        (∑ u, x u * (weight u * (-y) u -
          ∑ w ∈ G.neighborFinset u, (-y) w)) =
            ∑ u, -(x u * (weight u * y u - ∑ w ∈ G.neighborFinset u, y w)) := by
              apply Finset.sum_congr rfl
              intro u _
              simp only [Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]
              ring
        _ = -(∑ u, x u * (weight u * y u -
          ∑ w ∈ G.neighborFinset u, y w)) := by
            exact Finset.sum_neg_distrib (s := Finset.univ)
              (fun u : V => x u * (weight u * y u -
                ∑ w ∈ G.neighborFinset u, y w))
    have pairing_neg_neg (x y : V → ℤ) :
        treePairing G weight (-x) (-y) = treePairing G weight x y := by
      rw [pairing_neg_left, pairing_neg_right]
      ring
    have hshift_eq :
        treePairing G weight (-b) (-b) + treePairing G weight (vertexVector v) (-b) =
          -treePairing G weight a b := by
      calc
        treePairing G weight (-b) (-b) + treePairing G weight (vertexVector v) (-b) =
            treePairing G weight b b +
              (treePairing G weight a (-b) + treePairing G weight b (-b)) := by
                rw [hab, pairing_neg_neg, treePairing_add_left]
        _ = -treePairing G weight a b := by
          rw [pairing_neg_right, pairing_neg_right]
          ring
    have hshift_nonpos :
        treePairing G weight (-b) (-b) + treePairing G weight (vertexVector v) (-b) ≤ 0 := by
      rw [hshift_eq]
      omega
    have hzb : (-b : V → ℤ) ≠ 0 := neg_ne_zero.mpr hb
    by_cases hq : 0 ≤ (-b) v
    · have hpos := normalized_pairing_positive_of_unique_underweight G weight v (-b)
        h_tree h_positive ⟨v, hv, huniq⟩ hv h_two hzb hq
      omega
    · have hq_le : (-b) v ≤ -1 := Int.le_sub_one_of_not_le hq
      have hprime_eq : -vertexVector v - (-b) = -a := by
        rw [hab]
        ext x
        simp only [Pi.sub_apply, Pi.neg_apply, Pi.add_apply]
        ring
      have hprime_nonzero : -vertexVector v - (-b) ≠ 0 := by
        rw [hprime_eq]
        exact neg_ne_zero.mpr ha
      have hq_le' : -b v ≤ -1 := by
        simpa only [Pi.neg_apply] using hq_le
      have hprime_root : 0 ≤ (-vertexVector v - (-b)) v := by
        simp only [Pi.sub_apply, Pi.neg_apply, vertexVector, if_pos]
        omega
      have hprime_shift :
          treePairing G weight (-vertexVector v - (-b)) (-vertexVector v - (-b)) +
            treePairing G weight (vertexVector v) (-vertexVector v - (-b)) =
              treePairing G weight (-b) (-b) + treePairing G weight (vertexVector v) (-b) := by
        calc
          treePairing G weight (-vertexVector v - (-b)) (-vertexVector v - (-b)) +
              treePairing G weight (vertexVector v) (-vertexVector v - (-b)) =
                treePairing G weight (-a) (-a) + treePairing G weight (a + b) (-a) := by
                  rw [hprime_eq, hab]
          _ = treePairing G weight a a +
                (treePairing G weight a (-a) + treePairing G weight b (-a)) := by
                  rw [pairing_neg_neg, treePairing_add_left]
          _ = -treePairing G weight a b := by
            rw [pairing_neg_right, pairing_neg_right, treePairing_symm G weight b a]
            ring
          _ = treePairing G weight (-b) (-b) + treePairing G weight (vertexVector v) (-b) :=
            hshift_eq.symm
      have hpos := normalized_pairing_positive_of_unique_underweight G weight v
        (-vertexVector v - (-b)) h_tree h_positive ⟨v, hv, huniq⟩ hv h_two
        hprime_nonzero hprime_root
      rw [hprime_shift] at hpos
      omega

end PositiveDefiniteTreeLattice
```

## Statement dependencies

- `Mathlib:Mathlib.Combinatorics.SimpleGraph.Acyclic.SimpleGraph.IsTree`
- `Mathlib:Mathlib.Combinatorics.SimpleGraph.Basic.SimpleGraph`
- `Mathlib:Mathlib.Combinatorics.SimpleGraph.Finite.SimpleGraph.degree`
- `current repo:Main.LatticeFoundations.IrreducibleAnchor`
- `current repo:Main.LatticeFoundations.treePairingAnchor`
- `current repo:Main.LatticeFoundations.vertexVectorAnchor`

## Proof dependencies

- `Mathlib:Mathlib.Algebra.BigOperators.Group.Finset.Basic.Finset.sum_congr`
- `Mathlib:Mathlib.Algebra.BigOperators.Group.Finset.Defs.Finset.sum_neg_distrib`
- `Mathlib:Mathlib.Tactic.IntervalCases.Int.le_sub_one_of_not_le`
- `current repo:Main.IrreducibleVertex.irreducible_vertex_of_weight_eq_one`
- `current repo:Main.IrreducibleVertex.normalized_pairing_positive_of_unique_underweight`
- `current repo:Main.IrreducibleVertex.weight_ge_two_of_ne_one`
- `current repo:Main.LatticeFoundations.IrreducibleAnchor`
- `current repo:Main.LatticeFoundations.treePairing_add_left`
- `current repo:Main.LatticeFoundations.treePairing_add_right`
- `current repo:Main.LatticeFoundations.treePairing_add_self`
- `current repo:Main.LatticeFoundations.treePairing_symm`
- `current repo:Main.LatticeFoundations.vertexVectorAnchor`

## Sources

- `formal_target.lean:24-33`
- `solution.tex:182-186`
