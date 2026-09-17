[← Public API](../PUBLIC_API.md) · [Public boundaries](../PUBLIC_BOUNDARIES.md) · [Complete graph](../DECLARATION_GRAPH.md)

# `rootedGram_root_nonroot_linear_eq_sum_childRoots`

The ambient rooted-Gram root row and column weighted sums collapse canonically to the negative sum of child-root coefficients.

- Kind: `theorem`
- Node: `Main.RootedCapacity`
- Module: `PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.rootedGram_root_nonroot_linear_eq_sum_childRoots`
- State: `proved`
- Revision status: `committed`
- Repository completion: `graph_proved`
- Compatibility `formal_code`: final proof projection

## Statement NL

Let `V` be a vertex type equipped with `[Fintype V]` and `[DecidableEq V]`. Let `G : SimpleGraph V` be equipped with `[DecidableRel G.Adj]`, let `hG : G.IsTree`, let `ρ : V`, and let `w : V → ℤ`. Define `R := {x : V // x ≠ ρ}`, `I := {c : V // c ∈ rootedChildren G hG ρ ρ}`, `S := Σ c : I, rootedChildComponent G ρ c.1`, and `e := (rootedChildComponentsEquivNonroot G hG ρ).symm : R ≃ S`. Then, for every coefficient function `a : R → ℚ`, both ambient root/nonroot linear sums collapse to the child-root coefficients:

`∑ x : R, rootedGram G w ρ x.1 * a x = - ∑ c : I, a (e.symm ⟨c, rootedChildRoot G ρ c.1⟩)`,

and

`∑ x : R, a x * rootedGram G w x.1 ρ = - ∑ c : I, a (e.symm ⟨c, rootedChildRoot G ρ c.1⟩)`.

The first identity retains the root-row factor order and the second retains the root-column factor order.

## Statement Formal

```lean
-- lean-constellation: managed-imports-begin
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Prelude
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Data.Fintype.BigOperators
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildComponent
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildComponentsEquivNonroot
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildRoot
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildren
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedGram
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.rootedChildComponentsEquivNonroot_apply
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.rootedGram_root_rootedChildComponent_support
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `rootedGram_root_nonroot_linear_eq_sum_childRoots`

Let `V` be a vertex type equipped with `[Fintype V]` and `[DecidableEq V]`. Let `G : SimpleGraph V`
be equipped with `[DecidableRel G.Adj]`, let `hG : G.IsTree`, let `ρ : V`, and let `w : V → ℤ`.
Define `R := {x : V // x ≠ ρ}`, `I := {c : V // c ∈ rootedChildren G hG ρ ρ}`, `S := Σ c : I,
rootedChildComponent G ρ c.1`, and `e := (rootedChildComponentsEquivNonroot G hG ρ).symm : R ≃ S`.
Then, for every coefficient function `a : R → ℚ`, both ambient root/nonroot linear sums collapse to
the child-root coefficients:

`∑ x : R, rootedGram G w ρ x.1 * a x = - ∑ c : I, a (e.symm ⟨c, rootedChildRoot G ρ c.1⟩)`,

and

`∑ x : R, a x * rootedGram G w x.1 ρ = - ∑ c : I, a (e.symm ⟨c, rootedChildRoot G ρ c.1⟩)`.

The first identity retains the root-row factor order and the second retains the root-column factor
order.

## Sources

- Source `solution.tex`, lines 57–63

## Statement dependencies

- `Equiv.sum_comp` from `Mathlib.Algebra.BigOperators.Group.Finset.Defs`
- `Fintype.sum_sigma` from `Mathlib.Data.Fintype.BigOperators`
- `Main.RootedCapacity::rootedChildComponent` → `rootedChildComponent` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildComponent`
- `Main.RootedCapacity::rootedChildComponentsEquivNonroot` → `rootedChildComponentsEquivNonroot`
  from `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildComponentsEquivNonroot`
- `Main.RootedCapacity::rootedChildComponentsEquivNonroot_apply` →
  `rootedChildComponentsEquivNonroot_apply` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.rootedChildComponentsEquivNonroot_apply`
- `Main.RootedCapacity::rootedChildRoot` → `rootedChildRoot` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildRoot`
- `Main.RootedCapacity::rootedChildren` → `rootedChildren` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildren`
- `Main.RootedCapacity::rootedGram` → `rootedGram` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedGram`
- `Main.RootedCapacity::rootedGram_root_rootedChildComponent_support` →
  `rootedGram_root_rootedChildComponent_support` from `PositiveDefiniteTreeLattice.Main.RootedCapaci
  ty.Theorems.rootedGram_root_rootedChildComponent_support`
-/

theorem rootedGram_root_nonroot_linear_eq_sum_childRoots {V : Type*} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.IsTree)
    (w : V → ℤ) (ρ : V) :
    let R := {x : V // x ≠ ρ}
    let I := {c : V // c ∈ rootedChildren G hG ρ ρ}
    let S := Σ c : I, rootedChildComponent G ρ c.1
    let e : R ≃ S := (rootedChildComponentsEquivNonroot G hG ρ).symm
    ∀ a : R → ℚ,
      (∑ x : R, rootedGram G w ρ x.1 * a x) =
        -∑ c : I, a (e.symm ⟨c, rootedChildRoot G ρ c.1⟩) ∧
      (∑ x : R, a x * rootedGram G w x.1 ρ) =
        -∑ c : I, a (e.symm ⟨c, rootedChildRoot G ρ c.1⟩) := by
  sorry
```

## Proof NL

Work under `classical`, unfold the four `let` binders, and introduce `a : R → ℚ`. Split the conjunction, treating the row identity first and the column identity second.

For either summand `F : R → ℚ`, transport `∑ x : R, F x` to the sigma index `S` with `Equiv.sum_comp` for `e : R ≃ S`, instantiated with the function `s ↦ F (e.symm s)`. Simplify the resulting `e.symm (e x)` on the `R` side, then use `Fintype.sum_sigma` to obtain one inner sum over `rootedChildComponent G ρ c.1` for each `c : I`. Rewrite the occurrence of the forward canonical component equivalence in `e.symm ⟨c,x⟩` by `rootedChildComponentsEquivNonroot_apply`; this identifies its ambient vertex with `(x : V)` while preserving the required inverse orientation in the coefficient.

For the row identity take `F x := rootedGram G w ρ x.1 * a x`. In each child fiber apply the first arbitrary-function collapse clause in `(rootedGram_root_rootedChildComponent_support G hG w ρ c).2`, with `f x := a (e.symm ⟨c,x⟩)`. It gives exactly `- a (e.symm ⟨c, rootedChildRoot G ρ c.1⟩)`. Sum these equalities over `c`, yielding the stated negative child-root sum with no remaining fiber term.

For the column identity repeat the identical reindexing and flattening with `F x := a x * rootedGram G w x.1 ρ`. Apply the second arbitrary-function collapse clause of the same support theorem to the same `f`; this preserves the column factor order and produces the identical negative child-root sum. No auxiliary declaration or additional assumption is needed.

## Proof Formal

```lean
-- lean-constellation: managed-imports-begin
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Prelude
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildComponent
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildComponentsEquivNonroot
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildRoot
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildren
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedGram
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.rootedChildComponentsEquivNonroot_apply
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.rootedGram_root_rootedChildComponent_support
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `rootedGram_root_nonroot_linear_eq_sum_childRoots`

Let `V` be a vertex type equipped with `[Fintype V]` and `[DecidableEq V]`. Let `G : SimpleGraph V`
be equipped with `[DecidableRel G.Adj]`, let `hG : G.IsTree`, let `ρ : V`, and let `w : V → ℤ`.
Define `R := {x : V // x ≠ ρ}`, `I := {c : V // c ∈ rootedChildren G hG ρ ρ}`, `S := Σ c : I,
rootedChildComponent G ρ c.1`, and `e := (rootedChildComponentsEquivNonroot G hG ρ).symm : R ≃ S`.
Then, for every coefficient function `a : R → ℚ`, both ambient root/nonroot linear sums collapse to
the child-root coefficients:

`∑ x : R, rootedGram G w ρ x.1 * a x = - ∑ c : I, a (e.symm ⟨c, rootedChildRoot G ρ c.1⟩)`,

and

`∑ x : R, a x * rootedGram G w x.1 ρ = - ∑ c : I, a (e.symm ⟨c, rootedChildRoot G ρ c.1⟩)`.

The first identity retains the root-row factor order and the second retains the root-column factor
order.

## Sources

- Source `solution.tex`, lines 57–63

## Statement dependencies

- `Equiv.sum_comp` from `Mathlib.Algebra.BigOperators.Group.Finset.Defs`
- `Fintype.sum_sigma` from `Mathlib.Data.Fintype.BigOperators`
- `Main.RootedCapacity::rootedChildComponent` → `rootedChildComponent` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildComponent`
- `Main.RootedCapacity::rootedChildComponentsEquivNonroot` → `rootedChildComponentsEquivNonroot`
  from `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildComponentsEquivNonroot`
- `Main.RootedCapacity::rootedChildComponentsEquivNonroot_apply` →
  `rootedChildComponentsEquivNonroot_apply` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.rootedChildComponentsEquivNonroot_apply`
- `Main.RootedCapacity::rootedChildRoot` → `rootedChildRoot` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildRoot`
- `Main.RootedCapacity::rootedChildren` → `rootedChildren` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildren`
- `Main.RootedCapacity::rootedGram` → `rootedGram` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedGram`
- `Main.RootedCapacity::rootedGram_root_rootedChildComponent_support` →
  `rootedGram_root_rootedChildComponent_support` from `PositiveDefiniteTreeLattice.Main.RootedCapaci
  ty.Theorems.rootedGram_root_rootedChildComponent_support`

## Proof outline

Work under `classical`, unfold the four `let` binders, and introduce `a : R → ℚ`. Split the
conjunction, treating the row identity first and the column identity second.

For either summand `F : R → ℚ`, transport `∑ x : R, F x` to the sigma index `S` with
`Equiv.sum_comp` for `e : R ≃ S`, instantiated with the function `s ↦ F (e.symm s)`. Simplify the
resulting `e.symm (e x)` on the `R` side, then use `Fintype.sum_sigma` to obtain one inner sum over
`rootedChildComponent G ρ c.1` for each `c : I`. Rewrite the occurrence of the forward canonical
component equivalence in `e.symm ⟨c,x⟩` by `rootedChildComponentsEquivNonroot_apply`; this
identifies its ambient vertex with `(x : V)` while preserving the required inverse orientation in
the coefficient.

For the row identity take `F x := rootedGram G w ρ x.1 * a x`. In each child fiber apply the first
arbitrary-function collapse clause in `(rootedGram_root_rootedChildComponent_support G hG w ρ c).2`,
with `f x := a (e.symm ⟨c,x⟩)`. It gives exactly `- a (e.symm ⟨c, rootedChildRoot G ρ c.1⟩)`. Sum
these equalities over `c`, yielding the stated negative child-root sum with no remaining fiber term.

For the column identity repeat the identical reindexing and flattening with `F x := a x * rootedGram
G w x.1 ρ`. Apply the second arbitrary-function collapse clause of the same support theorem to the
same `f`; this preserves the column factor order and produces the identical negative child-root sum.
No auxiliary declaration or additional assumption is needed.

## Proof sources

- Source `solution.tex`, lines 57–63

## Proof dependencies

- `Finset.sum_congr` from `Mathlib.Algebra.BigOperators.Group.Finset.Basic`
- `Equiv.sum_comp` from `Mathlib.Algebra.BigOperators.Group.Finset.Defs`
- `Finset.sum_neg_distrib` from `Mathlib.Algebra.BigOperators.Group.Finset.Defs`
- `Fintype.sum_sigma` from `Mathlib.Data.Fintype.BigOperators`
- `Fintype.ofFinite` from `Mathlib.Data.Fintype.EquivFin`
- `Main.RootedCapacity::rootedChildComponentsEquivNonroot_apply` →
  `rootedChildComponentsEquivNonroot_apply` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.rootedChildComponentsEquivNonroot_apply`
- `Main.RootedCapacity::rootedGram_root_rootedChildComponent_support` →
  `rootedGram_root_rootedChildComponent_support` from `PositiveDefiniteTreeLattice.Main.RootedCapaci
  ty.Theorems.rootedGram_root_rootedChildComponent_support`
-/
theorem rootedGram_root_nonroot_linear_eq_sum_childRoots {V : Type*} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.IsTree)
    (w : V → ℤ) (ρ : V) :
    let R := {x : V // x ≠ ρ}
    let I := {c : V // c ∈ rootedChildren G hG ρ ρ}
    let S := Σ c : I, rootedChildComponent G ρ c.1
    let e : R ≃ S := (rootedChildComponentsEquivNonroot G hG ρ).symm
    ∀ a : R → ℚ,
      (∑ x : R, rootedGram G w ρ x.1 * a x) =
        -∑ c : I, a (e.symm ⟨c, rootedChildRoot G ρ c.1⟩) ∧
      (∑ x : R, a x * rootedGram G w x.1 ρ) =
        -∑ c : I, a (e.symm ⟨c, rootedChildRoot G ρ c.1⟩) := by
  classical
  dsimp only
  intro a
  let e : {x : V // x ≠ ρ} ≃
      (Σ c : {c : V // c ∈ rootedChildren G hG ρ ρ},
        rootedChildComponent G ρ c.1) :=
    (rootedChildComponentsEquivNonroot G hG ρ).symm
  change
    (∑ x : {x : V // x ≠ ρ}, rootedGram G w ρ x.1 * a x) =
        -∑ c : {c : V // c ∈ rootedChildren G hG ρ ρ},
          a (e.symm ⟨c, rootedChildRoot G ρ c.1⟩) ∧
      (∑ x : {x : V // x ≠ ρ}, a x * rootedGram G w x.1 ρ) =
        -∑ c : {c : V // c ∈ rootedChildren G hG ρ ρ},
          a (e.symm ⟨c, rootedChildRoot G ρ c.1⟩)
  constructor
  · calc
      (∑ x : {x : V // x ≠ ρ}, rootedGram G w ρ x.1 * a x) =
          ∑ s : (Σ c : {c : V // c ∈ rootedChildren G hG ρ ρ},
            rootedChildComponent G ρ c.1),
            rootedGram G w ρ (e.symm s).1 * a (e.symm s) := by
        simpa using e.sum_comp
          (fun s => rootedGram G w ρ (e.symm s).1 * a (e.symm s))
      _ = ∑ c : {c : V // c ∈ rootedChildren G hG ρ ρ},
          ∑ x : rootedChildComponent G ρ c.1,
            rootedGram G w ρ (e.symm ⟨c, x⟩).1 * a (e.symm ⟨c, x⟩) := by
        rw [Fintype.sum_sigma]
      _ = ∑ c : {c : V // c ∈ rootedChildren G hG ρ ρ},
          -a (e.symm ⟨c, rootedChildRoot G ρ c.1⟩) := by
        apply Finset.sum_congr rfl
        intro c hc
        have hcollapse := ((rootedGram_root_rootedChildComponent_support G hG w ρ c).2
          (fun x => a (e.symm ⟨c, x⟩))).1
        have hFintype : Fintype.ofFinite (rootedChildComponent G ρ c.1) =
            (inferInstance : Fintype (rootedChildComponent G ρ c.1)) :=
          Subsingleton.elim _ _
        rw [hFintype] at hcollapse
        simpa only [e, Equiv.symm_symm, rootedChildComponentsEquivNonroot_apply] using hcollapse
      _ = -∑ c : {c : V // c ∈ rootedChildren G hG ρ ρ},
          a (e.symm ⟨c, rootedChildRoot G ρ c.1⟩) := by
        rw [Finset.sum_neg_distrib]
  · calc
      (∑ x : {x : V // x ≠ ρ}, a x * rootedGram G w x.1 ρ) =
          ∑ s : (Σ c : {c : V // c ∈ rootedChildren G hG ρ ρ},
            rootedChildComponent G ρ c.1),
            a (e.symm s) * rootedGram G w (e.symm s).1 ρ := by
        simpa using e.sum_comp
          (fun s => a (e.symm s) * rootedGram G w (e.symm s).1 ρ)
      _ = ∑ c : {c : V // c ∈ rootedChildren G hG ρ ρ},
          ∑ x : rootedChildComponent G ρ c.1,
            a (e.symm ⟨c, x⟩) * rootedGram G w (e.symm ⟨c, x⟩).1 ρ := by
        rw [Fintype.sum_sigma]
      _ = ∑ c : {c : V // c ∈ rootedChildren G hG ρ ρ},
          -a (e.symm ⟨c, rootedChildRoot G ρ c.1⟩) := by
        apply Finset.sum_congr rfl
        intro c hc
        have hcollapse := ((rootedGram_root_rootedChildComponent_support G hG w ρ c).2
          (fun x => a (e.symm ⟨c, x⟩))).2
        have hFintype : Fintype.ofFinite (rootedChildComponent G ρ c.1) =
            (inferInstance : Fintype (rootedChildComponent G ρ c.1)) :=
          Subsingleton.elim _ _
        rw [hFintype] at hcollapse
        simpa only [e, Equiv.symm_symm, rootedChildComponentsEquivNonroot_apply] using hcollapse
      _ = -∑ c : {c : V // c ∈ rootedChildren G hG ρ ρ},
          a (e.symm ⟨c, rootedChildRoot G ρ c.1⟩) := by
        rw [Finset.sum_neg_distrib]
```

## Statement dependencies

- `Mathlib:Mathlib.Algebra.BigOperators.Group.Finset.Defs.Equiv.sum_comp`
- `Mathlib:Mathlib.Data.Fintype.BigOperators.Fintype.sum_sigma`
- `current repo:Main.RootedCapacity.rootedChildComponent`
- `current repo:Main.RootedCapacity.rootedChildComponentsEquivNonroot`
- `current repo:Main.RootedCapacity.rootedChildComponentsEquivNonroot_apply`
- `current repo:Main.RootedCapacity.rootedChildRoot`
- `current repo:Main.RootedCapacity.rootedChildren`
- `current repo:Main.RootedCapacity.rootedGram`
- `current repo:Main.RootedCapacity.rootedGram_root_rootedChildComponent_support`

## Proof dependencies

- `Mathlib:Mathlib.Algebra.BigOperators.Group.Finset.Basic.Finset.sum_congr`
- `Mathlib:Mathlib.Algebra.BigOperators.Group.Finset.Defs.Equiv.sum_comp`
- `Mathlib:Mathlib.Algebra.BigOperators.Group.Finset.Defs.Finset.sum_neg_distrib`
- `Mathlib:Mathlib.Data.Fintype.BigOperators.Fintype.sum_sigma`
- `Mathlib:Mathlib.Data.Fintype.EquivFin.Fintype.ofFinite`
- `current repo:Main.RootedCapacity.rootedChildComponentsEquivNonroot_apply`
- `current repo:Main.RootedCapacity.rootedGram_root_rootedChildComponent_support`

## Sources

- `solution.tex:57-63`
