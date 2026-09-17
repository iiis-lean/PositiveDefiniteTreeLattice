[← Public API](../PUBLIC_API.md) · [Public boundaries](../PUBLIC_BOUNDARIES.md) · [Complete graph](../DECLARATION_GRAPH.md)

# `treePairing_add_self`

Self-pairing of a sum expands with twice the cross-pairing.

- Kind: `theorem`
- Node: `Main.LatticeFoundations`
- Module: `PositiveDefiniteTreeLattice.Main.LatticeFoundations.Theorems.treePairing_add_self`
- State: `proved`
- Revision status: `committed`
- Repository completion: `graph_proved`
- Compatibility `formal_code`: final proof projection

## Statement NL

For a finite type `V` with decidable equality, a simple graph `G : SimpleGraph V` with decidable adjacency, an integer-valued weight function `weight : V → ℤ`, and functions `a b : V → ℤ`, the self-pairing of their pointwise sum satisfies

`treePairing G weight (a + b) (a + b) = treePairing G weight a a + treePairing G weight b b + 2 * treePairing G weight a b`.

The cross term is oriented as `treePairing G weight a b`.

## Statement Formal

```lean
-- lean-constellation: managed-imports-begin
import PositiveDefiniteTreeLattice.Main.LatticeFoundations.Prelude
import PositiveDefiniteTreeLattice.Main.LatticeFoundations.Defs.treePairingAnchor
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `treePairing_add_self`

For a finite type `V` with decidable equality, a simple graph `G : SimpleGraph V` with decidable
adjacency, an integer-valued weight function `weight : V → ℤ`, and functions `a b : V → ℤ`, the
self-pairing of their pointwise sum satisfies

`treePairing G weight (a + b) (a + b) = treePairing G weight a a + treePairing G weight b b + 2 *
treePairing G weight a b`.

The cross term is oriented as `treePairing G weight a b`.

## Sources

- Source `solution.tex`, lines 25–28

## Statement dependencies

- `Main.LatticeFoundations::treePairingAnchor` → `PositiveDefiniteTreeLattice.treePairing` from
  `PositiveDefiniteTreeLattice.Main.LatticeFoundations.Defs.treePairingAnchor`
-/
theorem PositiveDefiniteTreeLattice.treePairing_add_self {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (weight : V → ℤ) (a b : V → ℤ) :
    PositiveDefiniteTreeLattice.treePairing G weight (a + b) (a + b) =
      PositiveDefiniteTreeLattice.treePairing G weight a a +
        PositiveDefiniteTreeLattice.treePairing G weight b b +
          2 * PositiveDefiniteTreeLattice.treePairing G weight a b := by
  sorry
```

## Proof NL

Apply the proved fresh-anchor additivity laws to expand the left-hand side in the source-prescribed order.  First use `PositiveDefiniteTreeLattice.treePairing_add_left` with second argument `a + b` to obtain `treePairing G weight a (a + b) + treePairing G weight b (a + b)`.  Apply `PositiveDefiniteTreeLattice.treePairing_add_right` to each summand, giving `treePairing G weight a a + treePairing G weight a b + (treePairing G weight b a + treePairing G weight b b)`.  Rewrite `treePairing G weight b a` to `treePairing G weight a b` using the proved `PositiveDefiniteTreeLattice.treePairing_symm`.  Finally normalize the integer addition by `ring`; this yields exactly `treePairing G weight a a + treePairing G weight b b + 2 * treePairing G weight a b`, preserving the required equality direction, term order, and cross-term orientation.

## Proof Formal

```lean
-- lean-constellation: managed-imports-begin
import PositiveDefiniteTreeLattice.Main.LatticeFoundations.Prelude
import PositiveDefiniteTreeLattice.Main.LatticeFoundations.Defs.treePairingAnchor
import PositiveDefiniteTreeLattice.Main.LatticeFoundations.Theorems.treePairing_add_left
import PositiveDefiniteTreeLattice.Main.LatticeFoundations.Theorems.treePairing_add_right
import PositiveDefiniteTreeLattice.Main.LatticeFoundations.Theorems.treePairing_symm
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `treePairing_add_self`

For a finite type `V` with decidable equality, a simple graph `G : SimpleGraph V` with decidable
adjacency, an integer-valued weight function `weight : V → ℤ`, and functions `a b : V → ℤ`, the
self-pairing of their pointwise sum satisfies

`treePairing G weight (a + b) (a + b) = treePairing G weight a a + treePairing G weight b b + 2 *
treePairing G weight a b`.

The cross term is oriented as `treePairing G weight a b`.

## Sources

- Source `solution.tex`, lines 25–28

## Statement dependencies

- `Main.LatticeFoundations::treePairingAnchor` → `PositiveDefiniteTreeLattice.treePairing` from
  `PositiveDefiniteTreeLattice.Main.LatticeFoundations.Defs.treePairingAnchor`

## Proof outline

Apply the proved fresh-anchor additivity laws to expand the left-hand side in the source-prescribed
order.  First use `PositiveDefiniteTreeLattice.treePairing_add_left` with second argument `a + b` to
obtain `treePairing G weight a (a + b) + treePairing G weight b (a + b)`.  Apply
`PositiveDefiniteTreeLattice.treePairing_add_right` to each summand, giving `treePairing G weight a
a + treePairing G weight a b + (treePairing G weight b a + treePairing G weight b b)`.  Rewrite
`treePairing G weight b a` to `treePairing G weight a b` using the proved
`PositiveDefiniteTreeLattice.treePairing_symm`.  Finally normalize the integer addition by `ring`;
this yields exactly `treePairing G weight a a + treePairing G weight b b + 2 * treePairing G weight
a b`, preserving the required equality direction, term order, and cross-term orientation.

## Proof sources

- Source `solution.tex`, lines 25–28

## Proof dependencies

- `Main.LatticeFoundations::treePairing_add_left` →
  `PositiveDefiniteTreeLattice.treePairing_add_left` from
  `PositiveDefiniteTreeLattice.Main.LatticeFoundations.Theorems.treePairing_add_left`
- `Main.LatticeFoundations::treePairing_add_right` →
  `PositiveDefiniteTreeLattice.treePairing_add_right` from
  `PositiveDefiniteTreeLattice.Main.LatticeFoundations.Theorems.treePairing_add_right`
- `Main.LatticeFoundations::treePairing_symm` → `PositiveDefiniteTreeLattice.treePairing_symm` from
  `PositiveDefiniteTreeLattice.Main.LatticeFoundations.Theorems.treePairing_symm`
-/
theorem PositiveDefiniteTreeLattice.treePairing_add_self {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (weight : V → ℤ) (a b : V → ℤ) :
    PositiveDefiniteTreeLattice.treePairing G weight (a + b) (a + b) =
      PositiveDefiniteTreeLattice.treePairing G weight a a +
        PositiveDefiniteTreeLattice.treePairing G weight b b +
          2 * PositiveDefiniteTreeLattice.treePairing G weight a b := by
  rw [PositiveDefiniteTreeLattice.treePairing_add_left G weight a b (a + b)]
  rw [PositiveDefiniteTreeLattice.treePairing_add_right G weight a a b]
  rw [PositiveDefiniteTreeLattice.treePairing_add_right G weight b a b]
  rw [PositiveDefiniteTreeLattice.treePairing_symm G weight b a]
  ring
```

## Statement dependencies

- `current repo:Main.LatticeFoundations.treePairingAnchor`

## Proof dependencies

- `current repo:Main.LatticeFoundations.treePairing_add_left`
- `current repo:Main.LatticeFoundations.treePairing_add_right`
- `current repo:Main.LatticeFoundations.treePairing_symm`

## Sources

- `solution.tex:25-28`
