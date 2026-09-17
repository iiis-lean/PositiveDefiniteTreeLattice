[← Public API](../PUBLIC_API.md) · [Public boundaries](../PUBLIC_BOUNDARIES.md) · [Complete graph](../DECLARATION_GRAPH.md)

# `irreducible_vertex_of_weight_eq_one`

A vertex vector of self-pairing one is irreducible.

- Kind: `lemma`
- Node: `Main.IrreducibleVertex`
- Module: `PositiveDefiniteTreeLattice.Main.IrreducibleVertex.Lemmas.irreducible_vertex_of_weight_eq_one`
- State: `proved`
- Revision status: `committed`
- Repository completion: `graph_proved`
- Compatibility `formal_code`: final proof projection

## Statement NL

Let `V` be a finite type with decidable equality, let `G : SimpleGraph V` have decidable adjacency, let `weight : V → ℤ`, and let `v : V`. If `h_positive` states that every nonzero integer-valued vertex function has strictly positive `treePairing G weight` self-pairing, and `weight v = 1`, then `Irreducible G weight (vertexVector v)`.

## Statement Formal

```lean
-- lean-constellation: managed-imports-begin
import PositiveDefiniteTreeLattice.Main.IrreducibleVertex.Prelude
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `irreducible_vertex_of_weight_eq_one`

Let `V` be a finite type with decidable equality, let `G : SimpleGraph V` have decidable adjacency,
let `weight : V → ℤ`, and let `v : V`. If `h_positive` states that every nonzero integer-valued
vertex function has strictly positive `treePairing G weight` self-pairing, and `weight v = 1`, then
`Irreducible G weight (vertexVector v)`.

## Sources

- Source `solution.tex`, lines 190–191

## Statement dependencies

- `Main.LatticeFoundations::IrreducibleAnchor` → `PositiveDefiniteTreeLattice.Irreducible` from
  `PositiveDefiniteTreeLattice.Main.LatticeFoundations.Defs.IrreducibleAnchor`
- `Main.LatticeFoundations::treePairingAnchor` → `PositiveDefiniteTreeLattice.treePairing` from
  `PositiveDefiniteTreeLattice.Main.LatticeFoundations.Defs.treePairingAnchor`
- `Main.LatticeFoundations::vertexVectorAnchor` → `PositiveDefiniteTreeLattice.vertexVector` from
  `PositiveDefiniteTreeLattice.Main.LatticeFoundations.Defs.vertexVectorAnchor`
-/
theorem PositiveDefiniteTreeLattice.irreducible_vertex_of_weight_eq_one {V : Type*} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (weight : V → ℤ) (v : V)
    (h_positive : ∀ y : V → ℤ, y ≠ 0 → 0 < PositiveDefiniteTreeLattice.treePairing G weight y y)
    (h_weight : weight v = 1) :
    PositiveDefiniteTreeLattice.Irreducible G weight
      (PositiveDefiniteTreeLattice.vertexVector v) := by
  sorry
```

## Proof NL

Apply `treePairing_vertexVector_self G weight v` to rewrite the self-pairing of `vertexVector v` as `weight v`.  Combining that equality with `h_weight` gives
`treePairing G weight (vertexVector v) (vertexVector v) = 1`.

Invoke `irreducible_of_pairing_self_eq_one` with the supplied `G`, `weight`, `vertexVector v`, and `h_positive`, using this norm-one equality.  Its conclusion is exactly `Irreducible G weight (vertexVector v)`, so no change to the protected irreducibility predicate or any extra hypothesis is needed.

## Proof Formal

```lean
-- lean-constellation: managed-imports-begin
import PositiveDefiniteTreeLattice.Main.IrreducibleVertex.Prelude
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `irreducible_vertex_of_weight_eq_one`

Let `V` be a finite type with decidable equality, let `G : SimpleGraph V` have decidable adjacency,
let `weight : V → ℤ`, and let `v : V`. If `h_positive` states that every nonzero integer-valued
vertex function has strictly positive `treePairing G weight` self-pairing, and `weight v = 1`, then
`Irreducible G weight (vertexVector v)`.

## Sources

- Source `solution.tex`, lines 190–191

## Statement dependencies

- `Main.LatticeFoundations::IrreducibleAnchor` → `PositiveDefiniteTreeLattice.Irreducible` from
  `PositiveDefiniteTreeLattice.Main.LatticeFoundations.Defs.IrreducibleAnchor`
- `Main.LatticeFoundations::treePairingAnchor` → `PositiveDefiniteTreeLattice.treePairing` from
  `PositiveDefiniteTreeLattice.Main.LatticeFoundations.Defs.treePairingAnchor`
- `Main.LatticeFoundations::vertexVectorAnchor` → `PositiveDefiniteTreeLattice.vertexVector` from
  `PositiveDefiniteTreeLattice.Main.LatticeFoundations.Defs.vertexVectorAnchor`

## Proof outline

Apply `treePairing_vertexVector_self G weight v` to rewrite the self-pairing of `vertexVector v` as
`weight v`.  Combining that equality with `h_weight` gives
`treePairing G weight (vertexVector v) (vertexVector v) = 1`.

Invoke `irreducible_of_pairing_self_eq_one` with the supplied `G`, `weight`, `vertexVector v`, and
`h_positive`, using this norm-one equality.  Its conclusion is exactly `Irreducible G weight
(vertexVector v)`, so no change to the protected irreducibility predicate or any extra hypothesis is
needed.

## Proof sources

- Source `solution.tex`, lines 189–192

## Proof dependencies

- `Main.LatticeFoundations::irreducibleOfPairingSelfEqOneAnchor` →
  `PositiveDefiniteTreeLattice.irreducible_of_pairing_self_eq_one` from
  `PositiveDefiniteTreeLattice.Main.LatticeFoundations.Theorems.irreducibleOfPairingSelfEqOneAnchor`
- `Main.LatticeFoundations::treePairing_vertexVector_self` →
  `PositiveDefiniteTreeLattice.treePairing_vertexVector_self` from
  `PositiveDefiniteTreeLattice.Main.LatticeFoundations.Theorems.treePairing_vertexVector_self`
-/
theorem PositiveDefiniteTreeLattice.irreducible_vertex_of_weight_eq_one {V : Type*} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (weight : V → ℤ) (v : V)
    (h_positive : ∀ y : V → ℤ, y ≠ 0 → 0 < PositiveDefiniteTreeLattice.treePairing G weight y y)
    (h_weight : weight v = 1) :
    PositiveDefiniteTreeLattice.Irreducible G weight
      (PositiveDefiniteTreeLattice.vertexVector v) := by
  apply PositiveDefiniteTreeLattice.irreducible_of_pairing_self_eq_one G weight
    (PositiveDefiniteTreeLattice.vertexVector v) h_positive
  rw [PositiveDefiniteTreeLattice.treePairing_vertexVector_self G weight v, h_weight]
```

## Statement dependencies

- `current repo:Main.LatticeFoundations.IrreducibleAnchor`
- `current repo:Main.LatticeFoundations.treePairingAnchor`
- `current repo:Main.LatticeFoundations.vertexVectorAnchor`

## Proof dependencies

- `current repo:Main.LatticeFoundations.irreducibleOfPairingSelfEqOneAnchor`
- `current repo:Main.LatticeFoundations.treePairing_vertexVector_self`

## Sources

- `solution.tex:190-191`
