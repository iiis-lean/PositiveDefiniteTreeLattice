[← Public API](../PUBLIC_API.md) · [Public boundaries](../PUBLIC_BOUNDARIES.md) · [Complete graph](../DECLARATION_GRAPH.md)

# `treePairing_add_right`

The graph pairing is additive in its second vector argument.

- Kind: `theorem`
- Node: `Main.LatticeFoundations`
- Module: `PositiveDefiniteTreeLattice.Main.LatticeFoundations.Theorems.treePairing_add_right`
- State: `proved`
- Revision status: `committed`
- Repository completion: `graph_proved`
- Compatibility `formal_code`: final proof projection

## Statement NL

For a finite type `V` with decidable equality, a simple graph `G : SimpleGraph V` with decidable adjacency, an integer-valued weight function `weight : V → ℤ`, and functions `x y z : V → ℤ`, the pairing is additive in its right argument:

`treePairing G weight x (y + z) = treePairing G weight x y + treePairing G weight x z`.

Here `y + z` is pointwise addition of functions `V → ℤ`.

## Statement Formal

```lean
-- lean-constellation: managed-imports-begin
import PositiveDefiniteTreeLattice.Main.LatticeFoundations.Prelude
import PositiveDefiniteTreeLattice.Main.LatticeFoundations.Defs.treePairingAnchor
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `treePairing_add_right`

For a finite type `V` with decidable equality, a simple graph `G : SimpleGraph V` with decidable
adjacency, an integer-valued weight function `weight : V → ℤ`, and functions `x y z : V → ℤ`, the
pairing is additive in its right argument:

`treePairing G weight x (y + z) = treePairing G weight x y + treePairing G weight x z`.

Here `y + z` is pointwise addition of functions `V → ℤ`.

## Statement dependencies

- `Main.LatticeFoundations::treePairingAnchor` → `PositiveDefiniteTreeLattice.treePairing` from
  `PositiveDefiniteTreeLattice.Main.LatticeFoundations.Defs.treePairingAnchor`
-/
theorem PositiveDefiniteTreeLattice.treePairing_add_right {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (weight x y z : V → ℤ) :
    PositiveDefiniteTreeLattice.treePairing G weight x (y + z) =
      PositiveDefiniteTreeLattice.treePairing G weight x y +
        PositiveDefiniteTreeLattice.treePairing G weight x z := by
  sorry
```

## Proof NL

Unfold `PositiveDefiniteTreeLattice.treePairing`.  First reduce `(y + z) v` pointwise inside every neighbor sum and use `Finset.sum_add_distrib` to split that inner sum.  Distribute `weight u * (y u + z u)` and the outer multiplication, then normalize the integer expression at each `u` into the sum of the contributions for `y` and `z`.  A second use of `Finset.sum_add_distrib` splits the outer finite sum; `ring` closes the pointwise algebra and gives the two required pairings.

## Proof Formal

```lean
-- lean-constellation: managed-imports-begin
import PositiveDefiniteTreeLattice.Main.LatticeFoundations.Prelude
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import PositiveDefiniteTreeLattice.Main.LatticeFoundations.Defs.treePairingAnchor
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `treePairing_add_right`

For a finite type `V` with decidable equality, a simple graph `G : SimpleGraph V` with decidable
adjacency, an integer-valued weight function `weight : V → ℤ`, and functions `x y z : V → ℤ`, the
pairing is additive in its right argument:

`treePairing G weight x (y + z) = treePairing G weight x y + treePairing G weight x z`.

Here `y + z` is pointwise addition of functions `V → ℤ`.

## Statement dependencies

- `Main.LatticeFoundations::treePairingAnchor` → `PositiveDefiniteTreeLattice.treePairing` from
  `PositiveDefiniteTreeLattice.Main.LatticeFoundations.Defs.treePairingAnchor`

## Proof outline

Unfold `PositiveDefiniteTreeLattice.treePairing`.  First reduce `(y + z) v` pointwise inside every
neighbor sum and use `Finset.sum_add_distrib` to split that inner sum.  Distribute `weight u * (y u
+ z u)` and the outer multiplication, then normalize the integer expression at each `u` into the sum
of the contributions for `y` and `z`.  A second use of `Finset.sum_add_distrib` splits the outer
finite sum; `ring` closes the pointwise algebra and gives the two required pairings.

## Proof dependencies

- `Finset.sum_add_distrib` from `Mathlib.Algebra.BigOperators.Group.Finset.Basic`
- `Finset.sum_congr` from `Mathlib.Algebra.BigOperators.Group.Finset.Basic`
- `Main.LatticeFoundations::treePairingAnchor` → `PositiveDefiniteTreeLattice.treePairing` from
  `PositiveDefiniteTreeLattice.Main.LatticeFoundations.Defs.treePairingAnchor`
-/
theorem PositiveDefiniteTreeLattice.treePairing_add_right {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (weight x y z : V → ℤ) :
    PositiveDefiniteTreeLattice.treePairing G weight x (y + z) =
      PositiveDefiniteTreeLattice.treePairing G weight x y +
        PositiveDefiniteTreeLattice.treePairing G weight x z := by
  unfold PositiveDefiniteTreeLattice.treePairing
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro u _
  simp only [Pi.add_apply, Finset.sum_add_distrib]
  ring
```

## Statement dependencies

- `current repo:Main.LatticeFoundations.treePairingAnchor`

## Proof dependencies

- `Mathlib:Mathlib.Algebra.BigOperators.Group.Finset.Basic.Finset.sum_add_distrib`
- `Mathlib:Mathlib.Algebra.BigOperators.Group.Finset.Basic.Finset.sum_congr`
- `current repo:Main.LatticeFoundations.treePairingAnchor`
