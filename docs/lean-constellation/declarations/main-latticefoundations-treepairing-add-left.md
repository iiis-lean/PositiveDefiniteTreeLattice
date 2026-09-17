[← Public API](../PUBLIC_API.md) · [Public boundaries](../PUBLIC_BOUNDARIES.md) · [Complete graph](../DECLARATION_GRAPH.md)

# `treePairing_add_left`

The graph pairing is additive in its first vector argument.

- Kind: `theorem`
- Node: `Main.LatticeFoundations`
- Module: `PositiveDefiniteTreeLattice.Main.LatticeFoundations.Theorems.treePairing_add_left`
- State: `proved`
- Revision status: `committed`
- Repository completion: `graph_proved`
- Compatibility `formal_code`: final proof projection

## Statement NL

For a finite type `V` with decidable equality, a simple graph `G : SimpleGraph V` with decidable adjacency, an integer-valued weight function `weight : V → ℤ`, and functions `x y z : V → ℤ`, the pairing is additive in its left argument:

`treePairing G weight (x + y) z = treePairing G weight x z + treePairing G weight y z`.

Here `x + y` is pointwise addition of functions `V → ℤ`.

## Statement Formal

```lean
-- lean-constellation: managed-imports-begin
import PositiveDefiniteTreeLattice.Main.LatticeFoundations.Prelude
import PositiveDefiniteTreeLattice.Main.LatticeFoundations.Defs.treePairingAnchor
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `treePairing_add_left`

For a finite type `V` with decidable equality, a simple graph `G : SimpleGraph V` with decidable
adjacency, an integer-valued weight function `weight : V → ℤ`, and functions `x y z : V → ℤ`, the
pairing is additive in its left argument:

`treePairing G weight (x + y) z = treePairing G weight x z + treePairing G weight y z`.

Here `x + y` is pointwise addition of functions `V → ℤ`.

## Statement dependencies

- `Main.LatticeFoundations::treePairingAnchor` → `PositiveDefiniteTreeLattice.treePairing` from
  `PositiveDefiniteTreeLattice.Main.LatticeFoundations.Defs.treePairingAnchor`
-/
theorem PositiveDefiniteTreeLattice.treePairing_add_left {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (weight x y z : V → ℤ) :
    PositiveDefiniteTreeLattice.treePairing G weight (x + y) z =
      PositiveDefiniteTreeLattice.treePairing G weight x z +
        PositiveDefiniteTreeLattice.treePairing G weight y z := by
  sorry
```

## Proof NL

Unfold `PositiveDefiniteTreeLattice.treePairing`.  For each outer vertex `u`, reduce pointwise function addition so that `(x + y) u = x u + y u`; distribute multiplication over this sum and normalize the resulting integer expression into the sum of the `x` and `y` summands.  Apply `Finset.sum_add_distrib` to split the outer finite sum, obtaining exactly the two unfolded pairings.  Close the remaining pointwise arithmetic by `ring` (or the corresponding `simp`/ring normalization).

## Proof Formal

```lean
-- lean-constellation: managed-imports-begin
import PositiveDefiniteTreeLattice.Main.LatticeFoundations.Prelude
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import PositiveDefiniteTreeLattice.Main.LatticeFoundations.Defs.treePairingAnchor
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `treePairing_add_left`

For a finite type `V` with decidable equality, a simple graph `G : SimpleGraph V` with decidable
adjacency, an integer-valued weight function `weight : V → ℤ`, and functions `x y z : V → ℤ`, the
pairing is additive in its left argument:

`treePairing G weight (x + y) z = treePairing G weight x z + treePairing G weight y z`.

Here `x + y` is pointwise addition of functions `V → ℤ`.

## Statement dependencies

- `Main.LatticeFoundations::treePairingAnchor` → `PositiveDefiniteTreeLattice.treePairing` from
  `PositiveDefiniteTreeLattice.Main.LatticeFoundations.Defs.treePairingAnchor`

## Proof outline

Unfold `PositiveDefiniteTreeLattice.treePairing`.  For each outer vertex `u`, reduce pointwise
function addition so that `(x + y) u = x u + y u`; distribute multiplication over this sum and
normalize the resulting integer expression into the sum of the `x` and `y` summands.  Apply
`Finset.sum_add_distrib` to split the outer finite sum, obtaining exactly the two unfolded pairings.
Close the remaining pointwise arithmetic by `ring` (or the corresponding `simp`/ring normalization).

## Proof dependencies

- `Finset.sum_add_distrib` from `Mathlib.Algebra.BigOperators.Group.Finset.Basic`
- `Main.LatticeFoundations::treePairingAnchor` → `PositiveDefiniteTreeLattice.treePairing` from
  `PositiveDefiniteTreeLattice.Main.LatticeFoundations.Defs.treePairingAnchor`
-/
theorem PositiveDefiniteTreeLattice.treePairing_add_left {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (weight x y z : V → ℤ) :
    PositiveDefiniteTreeLattice.treePairing G weight (x + y) z =
      PositiveDefiniteTreeLattice.treePairing G weight x z +
        PositiveDefiniteTreeLattice.treePairing G weight y z := by
  unfold PositiveDefiniteTreeLattice.treePairing
  simp only [Pi.add_apply, add_mul]
  rw [Finset.sum_add_distrib]
```

## Statement dependencies

- `current repo:Main.LatticeFoundations.treePairingAnchor`

## Proof dependencies

- `Mathlib:Mathlib.Algebra.BigOperators.Group.Finset.Basic.Finset.sum_add_distrib`
- `current repo:Main.LatticeFoundations.treePairingAnchor`
