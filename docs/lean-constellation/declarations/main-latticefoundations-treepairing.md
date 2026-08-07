[← Public API](../PUBLIC_API.md) · [Public boundaries](../PUBLIC_BOUNDARIES.md)

# `treePairing`

Integral bilinear pairing of a finite integer-weighted simple graph.

- Kind: `definition`
- Node: `Main.LatticeFoundations`
- Module: `PositiveDefiniteTreeLattice.Main.LatticeFoundations.Defs.treePairing`
- State: `declared`
- Revision status: `committed`
- Repository completion: `graph_proved`
- Formal code: final statement projection

## Lean code

```lean
-- lean-constellation: managed-imports-begin
import PositiveDefiniteTreeLattice.Main.LatticeFoundations.Prelude
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Combinatorics.SimpleGraph.Finite
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `treePairing`

For a finite type `V` with decidable equality, a simple graph `G : SimpleGraph V` with decidable
adjacency, an integer-valued weight function `weight : V → ℤ`, and functions `x y : V → ℤ`,
`treePairing G weight x y` is the integer finite sum over all vertices `u : V` of

`x u * (weight u * y u - ∑ v ∈ G.neighborFinset u, y v)`.

Thus the inner sum is taken over the finite neighbors of `u` in `G`.

## Sources

- Source `formal_target.lean`, lines 7–11

## Statement dependencies

- `Finset.sum` from `Mathlib.Algebra.BigOperators.Group.Finset.Defs`
- `SimpleGraph.neighborFinset` from `Mathlib.Combinatorics.SimpleGraph.Finite`
-/
def PositiveDefiniteTreeLattice.Internal.historicalTreePairing {V : Type*} [Fintype V]
    [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (weight : V → ℤ) (x y : V → ℤ) : ℤ :=
  Finset.univ.sum fun u =>
    x u * (weight u * y u - (G.neighborFinset u).sum fun v => y v)
```

## Statement dependencies

- `Mathlib:Mathlib.Algebra.BigOperators.Group.Finset.Defs.Finset.sum`
- `Mathlib:Mathlib.Combinatorics.SimpleGraph.Finite.SimpleGraph.neighborFinset`

## Sources

- `formal_target.lean:7-11`
