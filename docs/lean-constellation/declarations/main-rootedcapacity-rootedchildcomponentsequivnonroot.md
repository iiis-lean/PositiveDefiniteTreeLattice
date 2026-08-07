[← Public API](../PUBLIC_API.md) · [Public boundaries](../PUBLIC_BOUNDARIES.md)

# `rootedChildComponentsEquivNonroot`

The dependent family of root-child components is equivalent to the subtype of nonroot vertices.

- Kind: `definition`
- Node: `Main.RootedCapacity`
- Module: `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildComponentsEquivNonroot`
- State: `declared`
- Revision status: `committed`
- Repository completion: `graph_proved`
- Formal code: final statement projection

## Lean code

```lean
-- lean-constellation: managed-imports-begin
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Prelude
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Fintype.Defs
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildComponent
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildren
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.rootedChildComponent_parent_not_mem
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.rootedChildComponent_partition
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `rootedChildComponentsEquivNonroot`

For a finite type V with decidable equality, a simple graph G on V with decidable adjacency, a tree
proof hG : G.IsTree, and a root ρ : V, define the noncomputable equivalence

rootedChildComponentsEquivNonroot G hG ρ :
  (Σ c : {c : V // c ∈ rootedChildren G hG ρ ρ},
    rootedChildComponent G ρ c.1)
  ≃ {v : V // v ≠ ρ}.

Its forward map is the exact dependent inclusion

⟨c, x⟩ ↦ ⟨(x : V), (x : V) ≠ ρ⟩,

where the nonroot proof is obtained from rootedChildComponent_parent_not_mem. Its inverse sends a
nonroot vertex v to the unique c ∈ rootedChildren G hG ρ ρ given by rootedChildComponent_partition,
together with v's corresponding membership in rootedChildComponent G ρ c. The two inverse laws are
proved by that uniqueness and subtype/dependent extensionality, so the standard apply_symm_apply and
symm_apply_apply computations expose these exact maps for reindexing.

## Sources

- Source `solution.tex`, lines 57–68

## Statement dependencies

- `SimpleGraph.IsTree` from `Mathlib.Combinatorics.SimpleGraph.Acyclic`
- `Finset.mem_filter` from `Mathlib.Data.Finset.Filter`
- `Finset.mem_univ` from `Mathlib.Data.Fintype.Defs`
- `Main.RootedCapacity::rootedChildComponent` → `rootedChildComponent` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildComponent`
- `Main.RootedCapacity::rootedChildComponent_parent_not_mem` → `rootedChildComponent_parent_not_mem`
  from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.rootedChildComponent_parent_not_mem`
- `Main.RootedCapacity::rootedChildComponent_partition` → `rootedChildComponent_partition` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.rootedChildComponent_partition`
- `Main.RootedCapacity::rootedChildren` → `rootedChildren` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildren`
-/
noncomputable def rootedChildComponentsEquivNonroot {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.IsTree) (ρ : V) :
    (Σ c : {c : V // c ∈ rootedChildren G hG ρ ρ}, rootedChildComponent G ρ c.1) ≃
      {v : V // v ≠ ρ} := by
  classical
  let f : (Σ c : {c : V // c ∈ rootedChildren G hG ρ ρ}, rootedChildComponent G ρ c.1) →
      {v : V // v ≠ ρ} := fun z =>
    ⟨(z.2 : V), rootedChildComponent_parent_not_mem G ρ z.1.1 hG
      (by
        have hc := z.1.2
        simp only [rootedChildren, Finset.mem_filter, Finset.mem_univ, true_and] at hc
        exact hc.1) z.2⟩
  let g : {v : V // v ≠ ρ} →
      (Σ c : {c : V // c ∈ rootedChildren G hG ρ ρ}, rootedChildComponent G ρ c.1) := fun v =>
    let h := rootedChildComponent_partition G hG ρ (v : V) v.2
    ⟨⟨h.choose, h.choose_spec.1.1⟩, ⟨(v : V), h.choose_spec.1.2⟩⟩
  refine { toFun := f, invFun := g, left_inv := ?_, right_inv := ?_ }
  · rintro ⟨c, x⟩
    let h := rootedChildComponent_partition G hG ρ (x : V) (f ⟨c, x⟩).2
    have hchoose : h.choose = c.1 := (ExistsUnique.choose_eq_iff h).2 ⟨c.2, x.2⟩
    dsimp [f, g]
    apply Sigma.ext (Subtype.ext hchoose)
    apply (Subtype.heq_iff_coe_eq ?_).2
    · rfl
    · intro z
      change z ∈ rootedChildComponent G ρ h.choose ↔ z ∈ rootedChildComponent G ρ c.1
      rw [hchoose]
  · intro v
    apply Subtype.ext
    rfl
```

## Statement dependencies

- `Mathlib:Mathlib.Combinatorics.SimpleGraph.Acyclic.SimpleGraph.IsTree`
- `Mathlib:Mathlib.Data.Finset.Filter.Finset.mem_filter`
- `Mathlib:Mathlib.Data.Fintype.Defs.Finset.mem_univ`
- `current repo:Main.RootedCapacity.rootedChildComponent`
- `current repo:Main.RootedCapacity.rootedChildComponent_parent_not_mem`
- `current repo:Main.RootedCapacity.rootedChildComponent_partition`
- `current repo:Main.RootedCapacity.rootedChildren`

## Sources

- `solution.tex:57-68`
