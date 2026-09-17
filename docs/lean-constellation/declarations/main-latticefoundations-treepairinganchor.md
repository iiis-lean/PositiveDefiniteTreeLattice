[← Public API](../PUBLIC_API.md) · [Public boundaries](../PUBLIC_BOUNDARIES.md) · [Complete graph](../DECLARATION_GRAPH.md)

# `treePairingAnchor`

Fresh compatible declaration anchor for the integral finite-graph pairing interface.

- Kind: `definition`
- Node: `Main.LatticeFoundations`
- Module: `PositiveDefiniteTreeLattice.Main.LatticeFoundations.Defs.treePairingAnchor`
- State: `declared`
- Revision status: `committed`
- Repository completion: `graph_proved`
- Compatibility `formal_code`: final statement projection

## Statement NL

Define the public interface `PositiveDefiniteTreeLattice.treePairing` as follows. For a type `V` with a finite enumeration and decidable equality, a simple graph `G : SimpleGraph V` with decidable adjacency, and functions `weight x y : V → ℤ`, its value is the integer

`∑ u, x u * (weight u * y u - ∑ v ∈ G.neighborFinset u, y v)`.

Thus the definition uses exactly the finite sum over all vertices and, for each vertex, the finite sum over its graph neighbors; it introduces no further assumptions or aliases.

## Statement Formal

```lean
-- lean-constellation: managed-imports-begin
import PositiveDefiniteTreeLattice.Main.LatticeFoundations.Prelude
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Combinatorics.SimpleGraph.Finite
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `treePairingAnchor`

Define the public interface `PositiveDefiniteTreeLattice.treePairing` as follows. For a type `V`
with a finite enumeration and decidable equality, a simple graph `G : SimpleGraph V` with decidable
adjacency, and functions `weight x y : V → ℤ`, its value is the integer

`∑ u, x u * (weight u * y u - ∑ v ∈ G.neighborFinset u, y v)`.

Thus the definition uses exactly the finite sum over all vertices and, for each vertex, the finite
sum over its graph neighbors; it introduces no further assumptions or aliases.

## Sources

- Source `formal_target.lean`, lines 7–11

## Statement dependencies

- `Finset.sum` from `Mathlib.Algebra.BigOperators.Group.Finset.Defs`
- `SimpleGraph.neighborFinset` from `Mathlib.Combinatorics.SimpleGraph.Finite`
-/
def PositiveDefiniteTreeLattice.treePairing {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (weight : V → ℤ) (x y : V → ℤ) : ℤ :=
  Finset.univ.sum fun u =>
    x u * (weight u * y u - (G.neighborFinset u).sum fun v => y v)
```

## Proof NL

Not recorded.

## Proof Formal

Not recorded.

## Statement dependencies

- `Mathlib:Mathlib.Algebra.BigOperators.Group.Finset.Defs.Finset.sum`
- `Mathlib:Mathlib.Combinatorics.SimpleGraph.Finite.SimpleGraph.neighborFinset`

## Sources

- `formal_target.lean:7-11`
