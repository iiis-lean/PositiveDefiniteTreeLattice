[← Public API](../PUBLIC_API.md) · [Public boundaries](../PUBLIC_BOUNDARIES.md) · [Complete graph](../DECLARATION_GRAPH.md)

# `vertexVector_ne_zero`

A vertex coordinate vector is nonzero.

- Kind: `theorem`
- Node: `Main.LatticeFoundations`
- Module: `PositiveDefiniteTreeLattice.Main.LatticeFoundations.Theorems.vertexVector_ne_zero`
- State: `proved`
- Revision status: `committed`
- Repository completion: `graph_proved`
- Compatibility `formal_code`: final proof projection

## Statement NL

For a type `V` with decidable equality and a vertex `v : V`, the unit coordinate function is nonzero:

`vertexVector v ≠ (0 : V → ℤ)`.

## Statement Formal

```lean
-- lean-constellation: managed-imports-begin
import PositiveDefiniteTreeLattice.Main.LatticeFoundations.Prelude
import PositiveDefiniteTreeLattice.Main.LatticeFoundations.Defs.vertexVectorAnchor
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `vertexVector_ne_zero`

For a type `V` with decidable equality and a vertex `v : V`, the unit coordinate function is
nonzero:

`vertexVector v ≠ (0 : V → ℤ)`.

## Sources

- Source `formal_target.lean`, lines 13–15

## Statement dependencies

- `Main.LatticeFoundations::vertexVectorAnchor` → `PositiveDefiniteTreeLattice.vertexVector` from
  `PositiveDefiniteTreeLattice.Main.LatticeFoundations.Defs.vertexVectorAnchor`
-/
theorem PositiveDefiniteTreeLattice.vertexVector_ne_zero {V : Type*} [DecidableEq V] (v : V) :
    PositiveDefiniteTreeLattice.vertexVector v ≠ (0 : V → ℤ) := by
  sorry
```

## Proof NL

Assume `PositiveDefiniteTreeLattice.vertexVector v = (0 : V → ℤ)`.  Apply equality of functions at the coordinate `v` (via `congrFun`).  Unfold `PositiveDefiniteTreeLattice.vertexVector`; its value at `v` is `1`, whereas the zero function has value `0`.  The resulting contradiction proves the unit coordinate function is nonzero.

## Proof Formal

```lean
-- lean-constellation: managed-imports-begin
import PositiveDefiniteTreeLattice.Main.LatticeFoundations.Prelude
import PositiveDefiniteTreeLattice.Main.LatticeFoundations.Defs.vertexVectorAnchor
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `vertexVector_ne_zero`

For a type `V` with decidable equality and a vertex `v : V`, the unit coordinate function is
nonzero:

`vertexVector v ≠ (0 : V → ℤ)`.

## Sources

- Source `formal_target.lean`, lines 13–15

## Statement dependencies

- `Main.LatticeFoundations::vertexVectorAnchor` → `PositiveDefiniteTreeLattice.vertexVector` from
  `PositiveDefiniteTreeLattice.Main.LatticeFoundations.Defs.vertexVectorAnchor`

## Proof outline

Assume `PositiveDefiniteTreeLattice.vertexVector v = (0 : V → ℤ)`.  Apply equality of functions at
the coordinate `v` (via `congrFun`).  Unfold `PositiveDefiniteTreeLattice.vertexVector`; its value
at `v` is `1`, whereas the zero function has value `0`.  The resulting contradiction proves the unit
coordinate function is nonzero.

## Proof dependencies

- `Main.LatticeFoundations::vertexVectorAnchor` → `PositiveDefiniteTreeLattice.vertexVector` from
  `PositiveDefiniteTreeLattice.Main.LatticeFoundations.Defs.vertexVectorAnchor`
-/
theorem PositiveDefiniteTreeLattice.vertexVector_ne_zero {V : Type*} [DecidableEq V] (v : V) :
    PositiveDefiniteTreeLattice.vertexVector v ≠ (0 : V → ℤ) := by
  intro h
  have h' := congrFun h v
  simp [PositiveDefiniteTreeLattice.vertexVector] at h'
```

## Statement dependencies

- `current repo:Main.LatticeFoundations.vertexVectorAnchor`

## Proof dependencies

- `current repo:Main.LatticeFoundations.vertexVectorAnchor`

## Sources

- `formal_target.lean:13-15`
