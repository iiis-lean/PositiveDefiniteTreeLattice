[← Public API](../PUBLIC_API.md) · [Public boundaries](../PUBLIC_BOUNDARIES.md) · [Complete graph](../DECLARATION_GRAPH.md)

# `vertexVectorAnchor`

Fresh compatible declaration anchor for the unit vertex-vector interface.

- Kind: `definition`
- Node: `Main.LatticeFoundations`
- Module: `PositiveDefiniteTreeLattice.Main.LatticeFoundations.Defs.vertexVectorAnchor`
- State: `declared`
- Revision status: `committed`
- Repository completion: `graph_proved`
- Compatibility `formal_code`: final statement projection

## Statement NL

Define the public interface `PositiveDefiniteTreeLattice.vertexVector` as follows. For a type `V` with decidable equality and a vertex `v : V`, return the integer-valued coordinate function sending each `u : V` to `1` when `u = v` and to `0` otherwise:

`fun u ↦ if u = v then 1 else 0`.

The definition has no graph or finiteness assumptions and introduces no aliases.

## Statement Formal

```lean
-- lean-constellation: managed-imports-begin
import PositiveDefiniteTreeLattice.Main.LatticeFoundations.Prelude
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `vertexVectorAnchor`

Define the public interface `PositiveDefiniteTreeLattice.vertexVector` as follows. For a type `V`
with decidable equality and a vertex `v : V`, return the integer-valued coordinate function sending
each `u : V` to `1` when `u = v` and to `0` otherwise:

`fun u ↦ if u = v then 1 else 0`.

The definition has no graph or finiteness assumptions and introduces no aliases.

## Sources

- Source `formal_target.lean`, lines 13–15
-/
def PositiveDefiniteTreeLattice.vertexVector {V : Type*} [DecidableEq V] (v : V) : V → ℤ :=
  fun u ↦ if u = v then 1 else 0
```

## Proof NL

Not recorded.

## Proof Formal

Not recorded.

## Sources

- `formal_target.lean:13-15`
