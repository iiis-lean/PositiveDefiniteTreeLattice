-- lean-constellation: managed-imports-begin
import PositiveDefiniteTreeLattice.Main.IrreducibleVertex.Prelude
import Mathlib.Combinatorics.SimpleGraph.Finite
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `weight_ge_degree_of_ne_unique_underweight`

Let `V` be a finite type with decidable equality, let `G : SimpleGraph V` have decidable adjacency,
let `weight : V → ℤ`, and let `v x : V`. Suppose `h_unique_underweight : ∃! u : V, weight u <
(G.degree u : ℤ)`, `hv : weight v < (G.degree v : ℤ)`, and `x ≠ v`. Then `(G.degree x : ℤ) ≤ weight
x`.

## Sources

- Source `solution.tex`, lines 197–198

## Statement dependencies

- `SimpleGraph.degree` from `Mathlib.Combinatorics.SimpleGraph.Finite`

## Proof outline

Unpack `h_unique_underweight` as a witness `u`, its underweight inequality, and its uniqueness
property.  Apply that uniqueness property both to the chosen vertex `v` using `hv` and,
hypothetically, to `x` if `weight x < (G.degree x : ℤ)` held.  These two equalities would give `x =
v`, contradicting `hxv`.

Therefore `¬ weight x < (G.degree x : ℤ)`.  Convert this negated strict integer inequality to
`(G.degree x : ℤ) ≤ weight x` by the ordinary linear-order/integer step (implemented directly by
`omega`).  This retains the ambient degree and its stated integer coercion exactly.

## Proof sources

- Source `solution.tex`, lines 197–198
-/
theorem PositiveDefiniteTreeLattice.weight_ge_degree_of_ne_unique_underweight {V : Type*}
    [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (weight : V → ℤ)
    (v x : V) (h_unique_underweight : ∃! u : V, weight u < (G.degree u : ℤ))
    (hv : weight v < (G.degree v : ℤ)) (hxv : x ≠ v) :
    (G.degree x : ℤ) ≤ weight x := by
  by_contra h_not
  have hx_underweight : weight x < (G.degree x : ℤ) := by
    omega
  obtain ⟨u, _, hu_unique⟩ := h_unique_underweight
  apply hxv
  exact (hu_unique x hx_underweight).trans (hu_unique v hv).symm
