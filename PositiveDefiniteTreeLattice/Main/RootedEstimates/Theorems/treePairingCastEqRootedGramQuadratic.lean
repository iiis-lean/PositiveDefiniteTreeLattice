-- lean-constellation: managed-imports-begin
import PositiveDefiniteTreeLattice.Main.RootedEstimates.Prelude
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Matrix.Mul
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `treePairingCastEqRootedGramQuadratic`

Let `V` be finite with the existing equality and adjacency decidability instances, let `G` be a
simple graph on `V`, let `w : V → ℤ`, and let `x : V → ℤ`.  Then the integral tree-pairing quadratic
value, cast to `ℚ`, is exactly the rational quadratic form of the rooted Gram matrix on the
coordinatewise cast of `x`:

`((PositiveDefiniteTreeLattice.treePairing G w x x : ℤ) : ℚ) = (fun v => (x v : ℚ)) ⬝ᵥ rootedGram G
w *ᵥ (fun v => (x v : ℚ))`.

The graph, weight, and coordinate vector are the same on both sides; only the scalar extension from
integral coordinates to the rational rooted Gram quadratic form is performed.

## Sources

- Source `solution.tex`, lines 165–174

## Statement dependencies

- `Main.LatticeFoundations::treePairingAnchor` → `PositiveDefiniteTreeLattice.treePairing` from
  `PositiveDefiniteTreeLattice.Main.LatticeFoundations.Defs.treePairingAnchor`
- `Main.RootedCapacity::rootedGram` → `rootedGram` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedGram`

## Proof outline

Work classically and unfold `rootedGram`, `PositiveDefiniteTreeLattice.treePairing`, and the
provider vertex-vector definition while keeping the same `G`, `w`, and integral vector `x`
throughout.  Expand the right-hand quadratic form with `dotProduct` and `Matrix.mulVec_eq_sum`.

First evaluate each rooted-Gram entry by expanding the two basis vectors.  The outer finite sum in
the pairing collapses at the first basis coordinate, and the neighbor sum collapses at the second,
using the `Finset.sum_ite_eq'` simplification for the two indicator functions.  Thus, for each `u`,
the expanded matrix action is the rational cast of the same local expression that occurs in the
tree-pairing summand:
`(rootedGram G w *ᵥ (fun v => (x v : ℚ))) u = (w u : ℚ) * (x u : ℚ) - ∑ v ∈ G.neighborFinset u, (x v
: ℚ)`.

Use `Int.cast_sum` on the outer tree-pairing sum and on its neighbor sums.  Simplify integer casts
of products, subtraction, zero, and one; then substitute the entrywise matrix-action identity into
the expanded dot product.  Each rational outer summand is exactly the cast of `x u * (w u * x u - ∑
v ∈ G.neighborFinset u, x v)`, so finite-sum congruence and ring normalization close the equality.

This is a scalar-extension calculation only: it changes neither the graph, weights, nor coordinates.
It supplies the rational Gram quadratic expression used by solution.tex lines 165–174 in the
subsequent root-coordinate Cauchy bound.

## Proof sources

- Source `solution.tex`, lines 165–174

## Proof dependencies

- `Finset.sum_congr` from `Mathlib.Algebra.BigOperators.Group.Finset.Basic`
- `Finset.sum_filter` from `Mathlib.Algebra.BigOperators.Group.Finset.Basic`
- `Finset.sum_sub_distrib` from `Mathlib.Algebra.BigOperators.Group.Finset.Defs`
- `Finset.sum_ite_eq` from `Mathlib.Algebra.BigOperators.Group.Finset.Piecewise`
- `Finset.sum_ite_eq'` from `Mathlib.Algebra.BigOperators.Group.Finset.Piecewise`
- `Int.cast_sum` from `Mathlib.Algebra.BigOperators.Ring.Finset`
- `SimpleGraph.mem_neighborFinset` from `Mathlib.Combinatorics.SimpleGraph.Finite`
- `SimpleGraph.neighborFinset_eq_filter` from `Mathlib.Combinatorics.SimpleGraph.Finite`
- `Matrix.mulVec_eq_sum` from `Mathlib.Data.Matrix.Mul`
- `dotProduct` from `Mathlib.Data.Matrix.Mul`
- `Main.LatticeFoundations::treePairingAnchor` → `PositiveDefiniteTreeLattice.treePairing` from
  `PositiveDefiniteTreeLattice.Main.LatticeFoundations.Defs.treePairingAnchor`
- `Main.LatticeFoundations::vertexVector` →
  `PositiveDefiniteTreeLattice.Internal.historicalVertexVector` from
  `PositiveDefiniteTreeLattice.Main.LatticeFoundations.Defs.vertexVector`
- `Main.RootedCapacity::rootedGram` → `rootedGram` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedGram`
-/
theorem treePairingCastEqRootedGramQuadratic {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (w x : V → ℤ) :
    (↑(PositiveDefiniteTreeLattice.treePairing G w x x) : ℚ) =
      (fun v => (x v : ℚ)) ⬝ᵥ Matrix.mulVec (rootedGram G w) (fun v => (x v : ℚ)) := by
  classical
  unfold rootedGram
  unfold PositiveDefiniteTreeLattice.vertexVector
  rw [Matrix.mulVec_eq_sum]
  simp only [PositiveDefiniteTreeLattice.treePairing, dotProduct]
  simp only [Int.cast_sum, Int.cast_mul, Int.cast_sub, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', SimpleGraph.mem_neighborFinset, ite_mul, one_mul, zero_mul,
    Finset.mem_univ, ↓reduceIte, Int.cast_ite, Int.cast_zero, Int.cast_one]
  apply Finset.sum_congr rfl
  intro u hu
  congr 1
  simp only [MulOpposite.op_intCast, Finset.sum_apply, Pi.smul_apply, Matrix.transpose_apply,
    MulOpposite.smul_eq_mul_unop, MulOpposite.unop_intCast]
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib]
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, one_mul,
    sub_right_inj]
  rw [SimpleGraph.neighborFinset_eq_filter, Finset.sum_filter]
