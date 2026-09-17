[← Public API](../PUBLIC_API.md) · [Public boundaries](../PUBLIC_BOUNDARIES.md) · [Complete graph](../DECLARATION_GRAPH.md)

# `irreducibleOfPairingSelfEqOneAnchor`

Fresh compatible declaration anchor for norm-one irreducibility under integral positive definiteness.

- Kind: `theorem`
- Node: `Main.LatticeFoundations`
- Module: `PositiveDefiniteTreeLattice.Main.LatticeFoundations.Theorems.irreducibleOfPairingSelfEqOneAnchor`
- State: `proved`
- Revision status: `committed`
- Repository completion: `graph_proved`
- Compatibility `formal_code`: final proof projection

## Statement NL

The public theorem `PositiveDefiniteTreeLattice.irreducible_of_pairing_self_eq_one` states the following. Let `V` have a finite enumeration and decidable equality, let `G : SimpleGraph V` have decidable adjacency, and let `weight : V → ℤ` and `x : V → ℤ`. Assume

`h_positive : ∀ y : V → ℤ, y ≠ 0 → 0 < PositiveDefiniteTreeLattice.treePairing G weight y y`

and

`hx : PositiveDefiniteTreeLattice.treePairing G weight x x = 1`.

Then `PositiveDefiniteTreeLattice.Irreducible G weight x` holds. The statement adds no tree, vertex, degree, or stronger positivity hypotheses, and preserves the self-pairing equality direction exactly.

## Statement Formal

```lean
-- lean-constellation: managed-imports-begin
import PositiveDefiniteTreeLattice.Main.LatticeFoundations.Prelude
import PositiveDefiniteTreeLattice.Main.LatticeFoundations.Defs.IrreducibleAnchor
import PositiveDefiniteTreeLattice.Main.LatticeFoundations.Defs.treePairingAnchor
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `irreducibleOfPairingSelfEqOneAnchor`

The public theorem `PositiveDefiniteTreeLattice.irreducible_of_pairing_self_eq_one` states the
following. Let `V` have a finite enumeration and decidable equality, let `G : SimpleGraph V` have
decidable adjacency, and let `weight : V → ℤ` and `x : V → ℤ`. Assume

`h_positive : ∀ y : V → ℤ, y ≠ 0 → 0 < PositiveDefiniteTreeLattice.treePairing G weight y y`

and

`hx : PositiveDefiniteTreeLattice.treePairing G weight x x = 1`.

Then `PositiveDefiniteTreeLattice.Irreducible G weight x` holds. The statement adds no tree, vertex,
degree, or stronger positivity hypotheses, and preserves the self-pairing equality direction
exactly.

## Sources

- Source `solution.tex`, lines 19–21

## Statement dependencies

- `Main.LatticeFoundations::IrreducibleAnchor` → `PositiveDefiniteTreeLattice.Irreducible` from
  `PositiveDefiniteTreeLattice.Main.LatticeFoundations.Defs.IrreducibleAnchor`
- `Main.LatticeFoundations::treePairingAnchor` → `PositiveDefiniteTreeLattice.treePairing` from
  `PositiveDefiniteTreeLattice.Main.LatticeFoundations.Defs.treePairingAnchor`
-/
theorem PositiveDefiniteTreeLattice.irreducible_of_pairing_self_eq_one {V : Type*} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (weight : V → ℤ) (x : V → ℤ)
    (h_positive : ∀ y : V → ℤ, y ≠ 0 → 0 < PositiveDefiniteTreeLattice.treePairing G weight y y)
    (hx : PositiveDefiniteTreeLattice.treePairing G weight x x = 1) :
    PositiveDefiniteTreeLattice.Irreducible G weight x := by
  sorry
```

## Proof NL

Unfold `PositiveDefiniteTreeLattice.Irreducible` and argue by contradiction.  From a hypothetical decomposition obtain functions `a` and `b`, proofs `a ≠ 0` and `b ≠ 0`, an equality `x = a + b`, and the nonnegative cross-pairing `0 ≤ treePairing G weight a b`.  Apply `h_positive` to `a` and `b`; because these pairings are integers, convert the resulting strict inequalities to the lower bounds `1 ≤ treePairing G weight a a` and `1 ≤ treePairing G weight b b`.  Substitute the decomposition into `hx` and rewrite its left-hand side with the proved `PositiveDefiniteTreeLattice.treePairing_add_self`, yielding

`treePairing G weight a a + treePairing G weight b b + 2 * treePairing G weight a b = 1`.

Together with the two integral lower bounds and the nonnegative cross term, this forces `2 ≤ 1`, a contradiction closed by `linarith`.  Thus the prohibited decomposition cannot exist, proving the unchanged irreducibility conclusion without any tree, vertex, degree, or stronger positivity assumption.

## Proof Formal

```lean
-- lean-constellation: managed-imports-begin
import PositiveDefiniteTreeLattice.Main.LatticeFoundations.Prelude
import PositiveDefiniteTreeLattice.Main.LatticeFoundations.Defs.IrreducibleAnchor
import PositiveDefiniteTreeLattice.Main.LatticeFoundations.Defs.treePairingAnchor
import PositiveDefiniteTreeLattice.Main.LatticeFoundations.Theorems.treePairing_add_self
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `irreducibleOfPairingSelfEqOneAnchor`

The public theorem `PositiveDefiniteTreeLattice.irreducible_of_pairing_self_eq_one` states the
following. Let `V` have a finite enumeration and decidable equality, let `G : SimpleGraph V` have
decidable adjacency, and let `weight : V → ℤ` and `x : V → ℤ`. Assume

`h_positive : ∀ y : V → ℤ, y ≠ 0 → 0 < PositiveDefiniteTreeLattice.treePairing G weight y y`

and

`hx : PositiveDefiniteTreeLattice.treePairing G weight x x = 1`.

Then `PositiveDefiniteTreeLattice.Irreducible G weight x` holds. The statement adds no tree, vertex,
degree, or stronger positivity hypotheses, and preserves the self-pairing equality direction
exactly.

## Sources

- Source `solution.tex`, lines 19–21

## Statement dependencies

- `Main.LatticeFoundations::IrreducibleAnchor` → `PositiveDefiniteTreeLattice.Irreducible` from
  `PositiveDefiniteTreeLattice.Main.LatticeFoundations.Defs.IrreducibleAnchor`
- `Main.LatticeFoundations::treePairingAnchor` → `PositiveDefiniteTreeLattice.treePairing` from
  `PositiveDefiniteTreeLattice.Main.LatticeFoundations.Defs.treePairingAnchor`

## Proof outline

Unfold `PositiveDefiniteTreeLattice.Irreducible` and argue by contradiction.  From a hypothetical
decomposition obtain functions `a` and `b`, proofs `a ≠ 0` and `b ≠ 0`, an equality `x = a + b`, and
the nonnegative cross-pairing `0 ≤ treePairing G weight a b`.  Apply `h_positive` to `a` and `b`;
because these pairings are integers, convert the resulting strict inequalities to the lower bounds
`1 ≤ treePairing G weight a a` and `1 ≤ treePairing G weight b b`.  Substitute the decomposition
into `hx` and rewrite its left-hand side with the proved
`PositiveDefiniteTreeLattice.treePairing_add_self`, yielding

`treePairing G weight a a + treePairing G weight b b + 2 * treePairing G weight a b = 1`.

Together with the two integral lower bounds and the nonnegative cross term, this forces `2 ≤ 1`, a
contradiction closed by `linarith`.  Thus the prohibited decomposition cannot exist, proving the
unchanged irreducibility conclusion without any tree, vertex, degree, or stronger positivity
assumption.

## Proof sources

- Source `solution.tex`, lines 19–31

## Proof dependencies

- `Main.LatticeFoundations::treePairing_add_self` →
  `PositiveDefiniteTreeLattice.treePairing_add_self` from
  `PositiveDefiniteTreeLattice.Main.LatticeFoundations.Theorems.treePairing_add_self`
-/
theorem PositiveDefiniteTreeLattice.irreducible_of_pairing_self_eq_one {V : Type*} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (weight : V → ℤ) (x : V → ℤ)
    (h_positive : ∀ y : V → ℤ, y ≠ 0 → 0 < PositiveDefiniteTreeLattice.treePairing G weight y y)
    (hx : PositiveDefiniteTreeLattice.treePairing G weight x x = 1) :
    PositiveDefiniteTreeLattice.Irreducible G weight x := by
  unfold PositiveDefiniteTreeLattice.Irreducible
  intro h
  rcases h with ⟨a, b, ha, hb, hxab, hab⟩
  have haa : 0 < PositiveDefiniteTreeLattice.treePairing G weight a a := h_positive a ha
  have hbb : 0 < PositiveDefiniteTreeLattice.treePairing G weight b b := h_positive b hb
  have haa_one : 1 ≤ PositiveDefiniteTreeLattice.treePairing G weight a a := by
    omega
  have hbb_one : 1 ≤ PositiveDefiniteTreeLattice.treePairing G weight b b := by
    omega
  rw [hxab, PositiveDefiniteTreeLattice.treePairing_add_self] at hx
  linarith
```

## Statement dependencies

- `current repo:Main.LatticeFoundations.IrreducibleAnchor`
- `current repo:Main.LatticeFoundations.treePairingAnchor`

## Proof dependencies

- `current repo:Main.LatticeFoundations.treePairing_add_self`

## Sources

- `solution.tex:19-21`
