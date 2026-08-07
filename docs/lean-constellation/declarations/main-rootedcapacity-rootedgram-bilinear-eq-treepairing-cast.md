[← Public API](../PUBLIC_API.md) · [Public boundaries](../PUBLIC_BOUNDARIES.md)

# `rootedGram_bilinear_eq_treePairing_cast`

The rational bilinear coordinate form of rootedGram equals the rational cast of treePairing for arbitrary integral coefficient functions.

- Kind: `theorem`
- Node: `Main.RootedCapacity`
- Module: `PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.rootedGram_bilinear_eq_treePairing_cast`
- State: `proved`
- Revision status: `committed`
- Repository completion: `graph_proved`
- Formal code: final proof projection

## Lean code

```lean
-- lean-constellation: managed-imports-begin
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Prelude
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Int.Cast.Basic
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedGram
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `rootedGram_bilinear_eq_treePairing_cast`

For every type `V` with finite and decidable equality instances, every simple graph `G : SimpleGraph
V` with decidable adjacency, every integer weight function `w : V → ℤ`, and all integer coefficient
functions `x y : V → ℤ`,

```lean
∑ u, ∑ t, (x u : ℚ) * rootedGram G w u t * (y t : ℚ) =
  (PositiveDefiniteTreeLattice.treePairing G w x y : ℚ)
```

The equality preserves the displayed ordered coefficient product and is asserted with no tree, root,
admissibility, capacity, or other structural hypotheses.

## Sources

- Source `solution.tex`, lines 33–45
- Source `solution.tex`, lines 47–82

## Statement dependencies

- `Main.LatticeFoundations::treePairingAnchor` → `PositiveDefiniteTreeLattice.treePairing` from
  `PositiveDefiniteTreeLattice.Main.LatticeFoundations.Defs.treePairingAnchor`
- `Main.RootedCapacity::rootedGram` → `rootedGram` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedGram`

## Proof outline

Unfold `rootedGram`, `PositiveDefiniteTreeLattice.treePairing`, and
`PositiveDefiniteTreeLattice.vertexVector`. The left side then has the ordered finite double sum of
the scalar extension of the pairing of two coordinate delta-vectors, while the right side is the
cast of the defining integral finite sum.

First rewrite the cast on the right through its outer finite sum using `Int.cast_sum`; use the simp
cast rules, in particular `Int.cast_mul` (and the standard casts for subtraction and zero), to put
each summand in `ℚ`. For the coordinate entry at fixed `u, t`, evaluate the finite sum in
`treePairing G w (vertexVector u) (vertexVector t)`: the outer delta-vector sum selects `u`, and the
neighbor finite sum of the inner delta-vector is the adjacency indicator at `u, t`. This is a direct
finite-`Finset` simplification from the definition of `vertexVector`; no graph property is used.

Substitute that evaluated entry into the displayed ordered double sum. Distribute/reassociate the
finite sums only with the existing finite-sum algebra, and normalize the rational casts and ring
expressions. The resulting summand-by-summand finite sum is exactly the cast-expanded definition of
`treePairing G w x y`, with the coefficient order `(x u : ℚ) * rootedGram G w u t * (y t : ℚ)`
retained. The implementation should therefore be a direct `simp`/finite-sum normalization proof
after these unfolds; if simplification leaves the delta-vector selection explicit, split on the
corresponding equality and use the `if` branches before the same normalization. This is a
lightweight local computation, not a missing reusable helper.

## Proof sources

- Source `solution.tex`, lines 33–45
- Source `solution.tex`, lines 47–82

## Proof dependencies

- `Int.cast_sum` from `Mathlib.Algebra.BigOperators.Ring.Finset`
- `Int.cast_mul` from `Mathlib.Algebra.Ring.Int.Defs`
- `SimpleGraph.neighborFinset_eq_filter` from `Mathlib.Combinatorics.SimpleGraph.Finite`
- `Int.cast_add` from `Mathlib.Data.Int.Cast.Basic`
- `Int.cast_sub` from `Mathlib.Data.Int.Cast.Basic`
- `Main.LatticeFoundations::treePairingAnchor` → `PositiveDefiniteTreeLattice.treePairing` from
  `PositiveDefiniteTreeLattice.Main.LatticeFoundations.Defs.treePairingAnchor`
- `Main.LatticeFoundations::vertexVectorAnchor` → `PositiveDefiniteTreeLattice.vertexVector` from
  `PositiveDefiniteTreeLattice.Main.LatticeFoundations.Defs.vertexVectorAnchor`
- `Main.RootedCapacity::rootedGram` → `rootedGram` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedGram`
-/
theorem rootedGram_bilinear_eq_treePairing_cast {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (w : V → ℤ) (x y : V → ℤ) :
    ∑ u, ∑ t, (x u : ℚ) * rootedGram G w u t * (y t : ℚ) =
      (PositiveDefiniteTreeLattice.treePairing G w x y : ℚ) := by
  simp only [rootedGram, PositiveDefiniteTreeLattice.treePairing,
    PositiveDefiniteTreeLattice.vertexVector, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', SimpleGraph.mem_neighborFinset, ite_mul, one_mul,
    zero_mul, Finset.mem_univ, ↓reduceIte, Int.cast_sub, Int.cast_ite,
    Int.cast_zero, Int.cast_one, Int.cast_sum, Int.cast_mul]
  apply Finset.sum_congr rfl
  intro u _
  simp_rw [mul_sub, sub_mul]
  rw [Finset.sum_sub_distrib]
  simp only [mul_ite, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, ↓reduceIte, mul_one]
  rw [mul_assoc, Finset.mul_sum, SimpleGraph.neighborFinset_eq_filter]
  rw [← Finset.sum_filter]
```

## Statement dependencies

- `current repo:Main.LatticeFoundations.treePairingAnchor`
- `current repo:Main.RootedCapacity.rootedGram`

## Proof dependencies

- `Mathlib:Mathlib.Algebra.BigOperators.Ring.Finset.Int.cast_sum`
- `Mathlib:Mathlib.Algebra.Ring.Int.Defs.Int.cast_mul`
- `Mathlib:Mathlib.Combinatorics.SimpleGraph.Finite.SimpleGraph.neighborFinset_eq_filter`
- `Mathlib:Mathlib.Data.Int.Cast.Basic.Int.cast_add`
- `Mathlib:Mathlib.Data.Int.Cast.Basic.Int.cast_sub`
- `current repo:Main.LatticeFoundations.treePairingAnchor`
- `current repo:Main.LatticeFoundations.vertexVectorAnchor`
- `current repo:Main.RootedCapacity.rootedGram`

## Sources

- `solution.tex:33-45`
- `solution.tex:47-82`
