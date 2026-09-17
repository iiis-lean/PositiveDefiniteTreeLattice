[← Public API](../PUBLIC_API.md) · [Public boundaries](../PUBLIC_BOUNDARIES.md) · [Complete graph](../DECLARATION_GRAPH.md)

# `vertexVector`

Unit integer coordinate function associated with a vertex.

- Kind: `definition`
- Node: `Main.LatticeFoundations`
- Module: `PositiveDefiniteTreeLattice.Main.LatticeFoundations.Defs.vertexVector`
- State: `declared`
- Revision status: `committed`
- Repository completion: `graph_proved`
- Compatibility `formal_code`: final statement projection

## Statement NL

For a type `V` with decidable equality and a vertex `v : V`, `vertexVector v : V → ℤ` is the coordinate function sending a vertex `u` to `1` when `u = v` and to `0` otherwise.

## Statement Formal

```lean
-- lean-constellation: managed-imports-begin
import PositiveDefiniteTreeLattice.Main.LatticeFoundations.Prelude
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `vertexVector`

For a type `V` with decidable equality and a vertex `v : V`, `vertexVector v : V → ℤ` is the
coordinate function sending a vertex `u` to `1` when `u = v` and to `0` otherwise.

## Sources

- Source `formal_target.lean`, lines 13–15
-/
def PositiveDefiniteTreeLattice.Internal.historicalVertexVector {V : Type*} [DecidableEq V]
    (v : V) : V → ℤ :=
  fun u ↦ if u = v then 1 else 0
```

## Proof NL

Not recorded.

## Proof Formal

Not recorded.

## Sources

- `formal_target.lean:13-15`
