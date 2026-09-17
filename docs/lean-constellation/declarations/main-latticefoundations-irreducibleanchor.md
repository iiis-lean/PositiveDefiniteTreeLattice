[← Public API](../PUBLIC_API.md) · [Public boundaries](../PUBLIC_BOUNDARIES.md) · [Complete graph](../DECLARATION_GRAPH.md)

# `IrreducibleAnchor`

Fresh compatible declaration anchor for irreducibility by nonnegative-cross-pairing decompositions.

- Kind: `definition`
- Node: `Main.LatticeFoundations`
- Module: `PositiveDefiniteTreeLattice.Main.LatticeFoundations.Defs.IrreducibleAnchor`
- State: `declared`
- Revision status: `committed`
- Repository completion: `graph_proved`
- Compatibility `formal_code`: final statement projection

## Statement NL

Define the public interface `PositiveDefiniteTreeLattice.Irreducible` as follows. For a type `V` with a finite enumeration and decidable equality, a simple graph `G : SimpleGraph V` with decidable adjacency, a weight function `weight : V → ℤ`, and `x : V → ℤ`, the proposition holds exactly when there do not exist functions `a b : V → ℤ` such that `a ≠ 0`, `b ≠ 0`, `x = a + b`, and

`0 ≤ PositiveDefiniteTreeLattice.treePairing G weight a b`.

This is the negated-existence decomposition predicate with the equality oriented exactly as `x = a + b`; it adds no positive-definiteness assumption or alias.

## Statement Formal

```lean
-- lean-constellation: managed-imports-begin
import PositiveDefiniteTreeLattice.Main.LatticeFoundations.Prelude
import PositiveDefiniteTreeLattice.Main.LatticeFoundations.Defs.treePairingAnchor
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `IrreducibleAnchor`

Define the public interface `PositiveDefiniteTreeLattice.Irreducible` as follows. For a type `V`
with a finite enumeration and decidable equality, a simple graph `G : SimpleGraph V` with decidable
adjacency, a weight function `weight : V → ℤ`, and `x : V → ℤ`, the proposition holds exactly when
there do not exist functions `a b : V → ℤ` such that `a ≠ 0`, `b ≠ 0`, `x = a + b`, and

`0 ≤ PositiveDefiniteTreeLattice.treePairing G weight a b`.

This is the negated-existence decomposition predicate with the equality oriented exactly as `x = a +
b`; it adds no positive-definiteness assumption or alias.

## Sources

- Source `formal_target.lean`, lines 17–22

## Statement dependencies

- `Main.LatticeFoundations::treePairingAnchor` → `PositiveDefiniteTreeLattice.treePairing` from
  `PositiveDefiniteTreeLattice.Main.LatticeFoundations.Defs.treePairingAnchor`
-/
def PositiveDefiniteTreeLattice.Irreducible {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (weight : V → ℤ) (x : V → ℤ) : Prop :=
  ¬ ∃ a b : V → ℤ, a ≠ 0 ∧ b ≠ 0 ∧ x = a + b ∧
    0 ≤ PositiveDefiniteTreeLattice.treePairing G weight a b
```

## Proof NL

Not recorded.

## Proof Formal

Not recorded.

## Statement dependencies

- `current repo:Main.LatticeFoundations.treePairingAnchor`

## Sources

- `formal_target.lean:17-22`
