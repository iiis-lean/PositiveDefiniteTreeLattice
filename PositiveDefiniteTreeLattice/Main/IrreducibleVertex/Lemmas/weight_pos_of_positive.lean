-- lean-constellation: managed-imports-begin
import PositiveDefiniteTreeLattice.Main.IrreducibleVertex.Prelude
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `weight_pos_of_positive`

Let `V` be a finite type with decidable equality, let `G : SimpleGraph V` have decidable adjacency,
let `weight : V → ℤ`, and let `v : V`. If `h_positive` states that every nonzero integer-valued
vertex function has strictly positive `treePairing G weight` self-pairing, then `0 < weight v`.

## Sources

- Source `solution.tex`, lines 189–190

## Statement dependencies

- `Main.LatticeFoundations::treePairingAnchor` → `PositiveDefiniteTreeLattice.treePairing` from
  `PositiveDefiniteTreeLattice.Main.LatticeFoundations.Defs.treePairingAnchor`
- `Main.LatticeFoundations::vertexVectorAnchor` → `PositiveDefiniteTreeLattice.vertexVector` from
  `PositiveDefiniteTreeLattice.Main.LatticeFoundations.Defs.vertexVectorAnchor`

## Proof outline

Specialize `h_positive` to `vertexVector v`.  The side condition is discharged by
`vertexVector_ne_zero v`, yielding strict positivity of its self-pairing.

Rewrite that self-pairing with `treePairing_vertexVector_self G weight v`.  The resulting inequality
is exactly `0 < weight v`.

## Proof sources

- Source `solution.tex`, lines 188–191

## Proof dependencies

- `Main.LatticeFoundations::treePairing_vertexVector_self` →
  `PositiveDefiniteTreeLattice.treePairing_vertexVector_self` from
  `PositiveDefiniteTreeLattice.Main.LatticeFoundations.Theorems.treePairing_vertexVector_self`
- `Main.LatticeFoundations::vertexVector_ne_zero` →
  `PositiveDefiniteTreeLattice.vertexVector_ne_zero` from
  `PositiveDefiniteTreeLattice.Main.LatticeFoundations.Theorems.vertexVector_ne_zero`
-/
theorem PositiveDefiniteTreeLattice.weight_pos_of_positive {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (weight : V → ℤ) (v : V)
    (h_positive : ∀ y : V → ℤ, y ≠ 0 → 0 < PositiveDefiniteTreeLattice.treePairing G weight y y) :
    0 < weight v := by
  rw [← PositiveDefiniteTreeLattice.treePairing_vertexVector_self G weight v]
  exact h_positive (PositiveDefiniteTreeLattice.vertexVector v)
    (PositiveDefiniteTreeLattice.vertexVector_ne_zero v)
