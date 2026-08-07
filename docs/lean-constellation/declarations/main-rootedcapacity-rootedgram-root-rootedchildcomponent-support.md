[← Public API](../PUBLIC_API.md) · [Public boundaries](../PUBLIC_BOUNDARIES.md)

# `rootedGram_root_rootedChildComponent_support`

The rooted Gram root row and column on an attached child component are supported only at that component's child root.

- Kind: `theorem`
- Node: `Main.RootedCapacity`
- Module: `PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.rootedGram_root_rootedChildComponent_support`
- State: `proved`
- Revision status: `committed`
- Repository completion: `graph_proved`
- Formal code: final proof projection

## Lean code

```lean
-- lean-constellation: managed-imports-begin
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Prelude
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Fintype.EquivFin
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildComponent
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildRoot
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildren
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedGram
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.rootedChildComponent_parent_not_mem
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.rootedChildComponent_partition
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.rootedGram_root_nonroot
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.treePairing_vertexVector_vertexVector
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `rootedGram_root_rootedChildComponent_support`

Let `V` be a finite type with decidable equality, let `G` be a simple graph on `V` with decidable
adjacency, let `hG : G.IsTree`, let `w : V → ℤ`, let `ρ : V`, let

`c : {c : V // c ∈ rootedChildren G hG ρ ρ}`,

and write `C := rootedChildComponent G ρ c.1` and `r_c := rootedChildRoot G ρ c.1`. Use the
canonical `Fintype.ofFinite` convention for the finite component type `C`.

The theorem retains both pointwise support formulas, for every `x : C`:

`rootedGram G w ρ (x : V) = if x = r_c then -1 else 0`,

and

`rootedGram G w (x : V) ρ = if x = r_c then -1 else 0`.

It also supplies the following consequences for every opaque rational-valued function `f : C → ℚ`:

`∑ x : C, rootedGram G w ρ (x : V) * f x = - f r_c`,

and

`∑ x : C, f x * rootedGram G w (x : V) ρ = - f r_c`.

Thus both weighted finite sums collapse to the unique canonical child-root coordinate with the
correct `-1` scalar. The statement contains no admissibility, inverse matrix, capacity, or
Sigma-indexed expression.

## Sources

- Source `solution.tex`, line 63

## Statement dependencies

- `Finset.sum` from `Mathlib.Algebra.BigOperators.Group.Finset.Defs`
- `SimpleGraph.IsTree` from `Mathlib.Combinatorics.SimpleGraph.Acyclic`
- `SimpleGraph.ConnectedComponent.instFinite` from
  `Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected`
- `Fintype.ofFinite` from `Mathlib.Data.Fintype.EquivFin`
- `Main.RootedCapacity::rootedChildComponent` → `rootedChildComponent` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildComponent`
- `Main.RootedCapacity::rootedChildRoot` → `rootedChildRoot` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildRoot`
- `Main.RootedCapacity::rootedChildren` → `rootedChildren` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildren`
- `Main.RootedCapacity::rootedGram` → `rootedGram` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedGram`

## Proof outline

Expand the declared component and canonical Fintype lets and work classically.  Extract hcAdj :
G.Adj ρ c.1 from c.property.  For each x : C, obtain hxne : (x : V) ≠ ρ from
rootedChildComponent_parent_not_mem G ρ c.1 hG hcAdj x.

Establish the pointwise support equivalence
  (x : V) ∈ rootedChildren G hG ρ ρ ↔ x = rootedChildRoot G ρ c.1
using rootedChildComponent_partition G hG ρ (x : V) hxne.  Its uniqueness compares x.property with
the canonical membership of x.val in the component rooted at itself, so the unique ambient child
label is both c.1 and x.val; use Subtype.ext to obtain the equality to rootedChildRoot.  The
converse follows after substitution from c.property.

Use rootedGram_root_nonroot and this support equivalence for the row formula.  For the column
formula, unfold rootedGram, apply treePairing_vertexVector_vertexVector to the two entries, and
simplify with hxne and SimpleGraph.adj_comm to obtain equality with the row; reuse the row formula.
Package these two facts as the required pointwise conjunction for every x.

For each arbitrary f : C → ℚ, rewrite every summand in the first finite sum by the row pointwise
formula.  Apply Finset.sum_eq_single (rootedChildRoot G ρ c.1): at the selected coordinate the
product simplifies to -f (rootedChildRoot G ρ c.1), and every other coordinate is zero because its
if-test is false.  Repeat identically for the second finite sum, using the column pointwise formula
and the selected-coordinate simplification f r * (-1) = -f r.  Keep f opaque throughout; do not
introduce inverse, capacity, admissibility, or Sigma terms.

## Proof sources

- Source `solution.tex`, line 63

## Proof dependencies

- `Finset.sum_eq_single` from `Mathlib.Algebra.BigOperators.Group.Finset.Basic`
- `SimpleGraph.adj_comm` from `Mathlib.Combinatorics.SimpleGraph.Basic`
- `SimpleGraph.ConnectedComponent.connectedComponentMk_mem` from
  `Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected`
- `Main.RootedCapacity::rootedChildComponent_parent_not_mem` → `rootedChildComponent_parent_not_mem`
  from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.rootedChildComponent_parent_not_mem`
- `Main.RootedCapacity::rootedChildComponent_partition` → `rootedChildComponent_partition` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.rootedChildComponent_partition`
- `Main.RootedCapacity::rootedChildRoot` → `rootedChildRoot` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildRoot`
- `Main.RootedCapacity::rootedChildren` → `rootedChildren` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildren`
- `Main.RootedCapacity::rootedGram` → `rootedGram` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedGram`
- `Main.RootedCapacity::rootedGram_root_nonroot` → `rootedGram_root_nonroot` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.rootedGram_root_nonroot`
- `Main.RootedCapacity::treePairing_vertexVector_vertexVector` →
  `treePairing_vertexVector_vertexVector` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.treePairing_vertexVector_vertexVector`
-/
theorem rootedGram_root_rootedChildComponent_support {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.IsTree) (w : V → ℤ) (ρ : V)
    (c : {c : V // c ∈ rootedChildren G hG ρ ρ}) :
    let C := rootedChildComponent G ρ c.1
    letI : Fintype C := Fintype.ofFinite C
    (∀ x : C,
      (rootedGram G w ρ (x : V) =
        if x = rootedChildRoot G ρ c.1 then (-1 : ℚ) else 0) ∧
      (rootedGram G w (x : V) ρ =
        if x = rootedChildRoot G ρ c.1 then (-1 : ℚ) else 0)) ∧
    (∀ f : C → ℚ,
      (∑ x : C, rootedGram G w ρ (x : V) * f x = -f (rootedChildRoot G ρ c.1)) ∧
      (∑ x : C, f x * rootedGram G w (x : V) ρ = -f (rootedChildRoot G ρ c.1))) := by
  classical
  dsimp only
  obtain ⟨hcAdj, _, _⟩ := by simpa [rootedChildren] using c.property
  have hpoint (x : rootedChildComponent G ρ c.1) :
      (rootedGram G w ρ (x : V) =
        if x = rootedChildRoot G ρ c.1 then (-1 : ℚ) else 0) ∧
      (rootedGram G w (x : V) ρ =
        if x = rootedChildRoot G ρ c.1 then (-1 : ℚ) else 0) := by
    have hxne : (x : V) ≠ ρ :=
      rootedChildComponent_parent_not_mem G ρ c.1 hG hcAdj x
    have hsupport : (x : V) ∈ rootedChildren G hG ρ ρ ↔
        x = rootedChildRoot G ρ c.1 := by
      constructor
      · intro hx
        obtain ⟨d, hd, hd_unique⟩ :=
          rootedChildComponent_partition G hG ρ (x : V) hxne
        have hxmem : (x : V) ∈ rootedChildComponent G ρ (x : V) := by
          change (x : V) ∈
            (G.deleteEdges {s(ρ, (x : V))}).connectedComponentMk (x : V)
          exact SimpleGraph.ConnectedComponent.connectedComponentMk_mem
        have hxd : (x : V) = d := hd_unique (x : V) ⟨hx, hxmem⟩
        have hcd : c.1 = d := hd_unique c.1 ⟨c.property, x.property⟩
        apply Subtype.ext
        exact hxd.trans hcd.symm
      · intro hx
        subst x
        exact c.property
    have hrow : rootedGram G w ρ (x : V) =
        if x = rootedChildRoot G ρ c.1 then (-1 : ℚ) else 0 := by
      rw [rootedGram_root_nonroot G hG w ρ (x : V) hxne]
      simp only [hsupport]
    constructor
    · exact hrow
    · rw [show rootedGram G w (x : V) ρ = rootedGram G w ρ (x : V) by
        simp only [rootedGram]
        rw [treePairing_vertexVector_vertexVector,
          treePairing_vertexVector_vertexVector]
        · by_cases hx : (x : V) = ρ
          · exact (hxne hx).elim
          · have hx' : ρ ≠ (x : V) := Ne.symm hx
            simp [hx, hx', SimpleGraph.adj_comm]
        · exact hG
        · exact hG]
      exact hrow
  constructor
  · exact hpoint
  · intro f
    constructor
    · rw [Finset.sum_eq_single (rootedChildRoot G ρ c.1)]
      · rw [(hpoint (rootedChildRoot G ρ c.1)).1]
        simp
      · intro x hx hxroot
        rw [(hpoint x).1, if_neg hxroot, zero_mul]
      · simp
    · rw [Finset.sum_eq_single (rootedChildRoot G ρ c.1)]
      · rw [(hpoint (rootedChildRoot G ρ c.1)).2]
        simp
      · intro x hx hxroot
        rw [(hpoint x).2, if_neg hxroot, mul_zero]
      · simp
```

## Statement dependencies

- `Mathlib:Mathlib.Algebra.BigOperators.Group.Finset.Defs.Finset.sum`
- `Mathlib:Mathlib.Combinatorics.SimpleGraph.Acyclic.SimpleGraph.IsTree`
- `Mathlib:Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected.SimpleGraph.ConnectedComponent.instFinite`
- `Mathlib:Mathlib.Data.Fintype.EquivFin.Fintype.ofFinite`
- `current repo:Main.RootedCapacity.rootedChildComponent`
- `current repo:Main.RootedCapacity.rootedChildRoot`
- `current repo:Main.RootedCapacity.rootedChildren`
- `current repo:Main.RootedCapacity.rootedGram`

## Proof dependencies

- `Mathlib:Mathlib.Algebra.BigOperators.Group.Finset.Basic.Finset.sum_eq_single`
- `Mathlib:Mathlib.Combinatorics.SimpleGraph.Basic.SimpleGraph.adj_comm`
- `Mathlib:Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected.SimpleGraph.ConnectedComponent.connectedComponentMk_mem`
- `current repo:Main.RootedCapacity.rootedChildComponent_parent_not_mem`
- `current repo:Main.RootedCapacity.rootedChildComponent_partition`
- `current repo:Main.RootedCapacity.rootedChildRoot`
- `current repo:Main.RootedCapacity.rootedChildren`
- `current repo:Main.RootedCapacity.rootedGram`
- `current repo:Main.RootedCapacity.rootedGram_root_nonroot`
- `current repo:Main.RootedCapacity.treePairing_vertexVector_vertexVector`

## Sources

- `solution.tex:63-63`
