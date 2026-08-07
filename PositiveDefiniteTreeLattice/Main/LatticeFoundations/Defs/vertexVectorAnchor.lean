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
