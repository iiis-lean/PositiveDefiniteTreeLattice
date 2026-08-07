[← Public API](../PUBLIC_API.md) · [Public boundaries](../PUBLIC_BOUNDARIES.md)

# `IsAdmissibleRootedTree`

Admissibility of a finite rooted integer-weighted tree.

- Kind: `definition`
- Node: `Main.RootedCapacity`
- Module: `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.IsAdmissibleRootedTree`
- State: `declared`
- Revision status: `committed`
- Repository completion: `graph_proved`
- Formal code: final statement projection

## Lean code

```lean
-- lean-constellation: managed-imports-begin
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Prelude
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.LinearAlgebra.Matrix.PosDef
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildCount
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedGram
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `IsAdmissibleRootedTree`

For a finite vertex type `V`, a simple graph `G : SimpleGraph V`, an integer weight function `w : V
→ ℤ`, and a root `ρ : V`, define `IsAdmissibleRootedTree G w ρ` to hold exactly when: `G` is a tree
(and hence, on the finite vertex type, a finite tree); the rational matrix `rootedGram G w` is
`Matrix.PosDef`; for every vertex `y`, `2 ≤ w y`; and for every vertex `y`, `(rootedChildCount G ρ y
: ℤ) + 1 ≤ w y`.  This packages the source admissibility condition for the rooted weighted tree,
without any additional connectivity, weight, or scalar assumptions.

## Sources

- Source `solution.tex`, lines 33–38

## Statement dependencies

- `SimpleGraph.IsTree` from `Mathlib.Combinatorics.SimpleGraph.Acyclic`
- `Matrix.PosDef` from `Mathlib.LinearAlgebra.Matrix.PosDef`
- `Main.RootedCapacity::rootedChildCount` → `rootedChildCount` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildCount`
- `Main.RootedCapacity::rootedGram` → `rootedGram` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedGram`
-/
def IsAdmissibleRootedTree {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (w : V → ℤ) (ρ : V) : Prop :=
  ∃ hG : G.IsTree,
    Matrix.PosDef (rootedGram G w) ∧
      (∀ y, (2 : ℤ) ≤ w y) ∧
        ∀ y, (rootedChildCount G hG ρ y : ℤ) + 1 ≤ w y
```

## Statement dependencies

- `Mathlib:Mathlib.Combinatorics.SimpleGraph.Acyclic.SimpleGraph.IsTree`
- `Mathlib:Mathlib.LinearAlgebra.Matrix.PosDef.Matrix.PosDef`
- `current repo:Main.RootedCapacity.rootedChildCount`
- `current repo:Main.RootedCapacity.rootedGram`

## Sources

- `solution.tex:33-38`
