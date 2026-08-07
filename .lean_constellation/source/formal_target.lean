import Mathlib

open scoped BigOperators

namespace PositiveDefiniteTreeLattice

/-- The integral bilinear form of a weighted simple graph. -/
def treePairing {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (weight : V → ℤ)
    (x y : V → ℤ) : ℤ :=
  ∑ u, x u * (weight u * y u - ∑ v ∈ G.neighborFinset u, y v)

/-- The lattice basis vector associated with a vertex. -/
def vertexVector {V : Type*} [DecidableEq V] (v : V) : V → ℤ :=
  fun u ↦ if u = v then 1 else 0

/-- Irreducibility with respect to decompositions having nonnegative cross-pairing. -/
def Irreducible {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (weight : V → ℤ)
    (x : V → ℤ) : Prop :=
  ¬ ∃ a b : V → ℤ,
      a ≠ 0 ∧ b ≠ 0 ∧ x = a + b ∧ 0 ≤ treePairing G weight a b

/-- A positive-definite integer-weighted finite tree with exactly one vertex
whose weight is below its degree contains an irreducible vertex vector. -/
theorem exists_irreducible_vertex
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (weight : V → ℤ)
    (h_tree : G.IsTree)
    (h_positive : ∀ x : V → ℤ, x ≠ 0 → 0 < treePairing G weight x x)
    (h_unique_underweight : ∃! v : V, weight v < (G.degree v : ℤ)) :
    ∃ v : V, Irreducible G weight (vertexVector v) := by
  sorry

end PositiveDefiniteTreeLattice
