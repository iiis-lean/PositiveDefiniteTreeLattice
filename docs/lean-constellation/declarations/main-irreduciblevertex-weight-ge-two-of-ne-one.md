[← Public API](../PUBLIC_API.md) · [Public boundaries](../PUBLIC_BOUNDARIES.md) · [Complete graph](../DECLARATION_GRAPH.md)

# `weight_ge_two_of_ne_one`

A positive-definite vertex weight distinct from one is at least two.

- Kind: `lemma`
- Node: `Main.IrreducibleVertex`
- Module: `PositiveDefiniteTreeLattice.Main.IrreducibleVertex.Lemmas.weight_ge_two_of_ne_one`
- State: `proved`
- Revision status: `committed`
- Repository completion: `graph_proved`
- Compatibility `formal_code`: final proof projection

## Statement NL

Let `V` be a finite type with decidable equality, let `G : SimpleGraph V` have decidable adjacency, let `weight : V → ℤ`, and let `v : V`. If `h_positive` states that every nonzero integer-valued vertex function has strictly positive `treePairing G weight` self-pairing, and `weight v ≠ 1`, then `2 ≤ weight v`.

## Statement Formal

```lean
-- lean-constellation: managed-imports-begin
import PositiveDefiniteTreeLattice.Main.IrreducibleVertex.Prelude
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `weight_ge_two_of_ne_one`

Let `V` be a finite type with decidable equality, let `G : SimpleGraph V` have decidable adjacency,
let `weight : V → ℤ`, and let `v : V`. If `h_positive` states that every nonzero integer-valued
vertex function has strictly positive `treePairing G weight` self-pairing, and `weight v ≠ 1`, then
`2 ≤ weight v`.

## Sources

- Source `solution.tex`, lines 189–192

## Statement dependencies

- `Main.LatticeFoundations::treePairingAnchor` → `PositiveDefiniteTreeLattice.treePairing` from
  `PositiveDefiniteTreeLattice.Main.LatticeFoundations.Defs.treePairingAnchor`
-/
theorem PositiveDefiniteTreeLattice.weight_ge_two_of_ne_one {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (weight : V → ℤ) (v : V)
    (h_positive : ∀ y : V → ℤ, y ≠ 0 → 0 < PositiveDefiniteTreeLattice.treePairing G weight y y)
    (h_weight_ne_one : weight v ≠ 1) :
    2 ≤ weight v := by
  sorry
```

## Proof NL

Use the committed helper `weight_pos_of_positive G weight v h_positive` to obtain `0 < weight v`.

For an integer, strict positivity together with `weight v ≠ 1` rules out every value below two: assuming the target inequality fails, ordinary integer discreteness gives `weight v ≤ 1`, and positivity then forces `weight v = 1`, a contradiction.  This final linear integer step is lightweight and can be discharged directly by `omega`, yielding `2 ≤ weight v`.

## Proof Formal

```lean
-- lean-constellation: managed-imports-begin
import PositiveDefiniteTreeLattice.Main.IrreducibleVertex.Prelude
import PositiveDefiniteTreeLattice.Main.IrreducibleVertex.Lemmas.weight_pos_of_positive
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `weight_ge_two_of_ne_one`

Let `V` be a finite type with decidable equality, let `G : SimpleGraph V` have decidable adjacency,
let `weight : V → ℤ`, and let `v : V`. If `h_positive` states that every nonzero integer-valued
vertex function has strictly positive `treePairing G weight` self-pairing, and `weight v ≠ 1`, then
`2 ≤ weight v`.

## Sources

- Source `solution.tex`, lines 189–192

## Statement dependencies

- `Main.LatticeFoundations::treePairingAnchor` → `PositiveDefiniteTreeLattice.treePairing` from
  `PositiveDefiniteTreeLattice.Main.LatticeFoundations.Defs.treePairingAnchor`

## Proof outline

Use the committed helper `weight_pos_of_positive G weight v h_positive` to obtain `0 < weight v`.

For an integer, strict positivity together with `weight v ≠ 1` rules out every value below two:
assuming the target inequality fails, ordinary integer discreteness gives `weight v ≤ 1`, and
positivity then forces `weight v = 1`, a contradiction.  This final linear integer step is
lightweight and can be discharged directly by `omega`, yielding `2 ≤ weight v`.

## Proof sources

- Source `solution.tex`, lines 188–192

## Proof dependencies

- `Main.IrreducibleVertex::weight_pos_of_positive` →
  `PositiveDefiniteTreeLattice.weight_pos_of_positive` from
  `PositiveDefiniteTreeLattice.Main.IrreducibleVertex.Lemmas.weight_pos_of_positive`
-/
theorem PositiveDefiniteTreeLattice.weight_ge_two_of_ne_one {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (weight : V → ℤ) (v : V)
    (h_positive : ∀ y : V → ℤ, y ≠ 0 → 0 < PositiveDefiniteTreeLattice.treePairing G weight y y)
    (h_weight_ne_one : weight v ≠ 1) :
    2 ≤ weight v := by
  have h_weight_pos := PositiveDefiniteTreeLattice.weight_pos_of_positive G weight v h_positive
  omega
```

## Statement dependencies

- `current repo:Main.LatticeFoundations.treePairingAnchor`

## Proof dependencies

- `current repo:Main.IrreducibleVertex.weight_pos_of_positive`

## Sources

- `solution.tex:189-192`
