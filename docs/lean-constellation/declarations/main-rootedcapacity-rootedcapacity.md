[← Public API](../PUBLIC_API.md) · [Public boundaries](../PUBLIC_BOUNDARIES.md)

# `rootedCapacity`

The root diagonal entry of the inverse rational Gram matrix.

- Kind: `definition`
- Node: `Main.RootedCapacity`
- Module: `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedCapacity`
- State: `declared`
- Revision status: `committed`
- Repository completion: `graph_proved`
- Formal code: final statement projection

## Lean code

```lean
-- lean-constellation: managed-imports-begin
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Prelude
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedGram
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `rootedCapacity`

For a finite integer-weighted simple graph `G` with weight function `w` and a chosen root vertex
`ρ`, define `rootedCapacity G w ρ : ℚ` to be the `(ρ, ρ)` entry of the inverse rational Gram matrix:
`(rootedGram G w)⁻¹ ρ ρ`.  This is the capacity `γ(C)` of the rooted weighted tree, retained as a
rational quantity.  The definition imposes no positive-definiteness or admissibility hypothesis;
when `rootedGram G w` is positive definite, its inverse exists as in the source.

## Sources

- Source `solution.tex`, lines 39–45

## Statement dependencies

- `Main.RootedCapacity::rootedGram` → `rootedGram` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedGram`
-/
noncomputable def rootedCapacity {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (w : V → ℤ) (ρ : V) : ℚ :=
  (rootedGram G w)⁻¹ ρ ρ
```

## Statement dependencies

- `current repo:Main.RootedCapacity.rootedGram`

## Sources

- `solution.tex:39-45`
