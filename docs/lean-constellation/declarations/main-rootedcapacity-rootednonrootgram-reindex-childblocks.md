[← Public API](../PUBLIC_API.md) · [Public boundaries](../PUBLIC_BOUNDARIES.md)

# `rootedNonrootGram_reindex_childBlocks`

The nonroot Gram block reindexed by root-child components is the dependent block diagonal of the child Gram matrices.

- Kind: `theorem`
- Node: `Main.RootedCapacity`
- Module: `PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.rootedNonrootGram_reindex_childBlocks`
- State: `proved`
- Revision status: `committed`
- Repository completion: `graph_proved`
- Formal code: final proof projection

## Lean code

```lean
-- lean-constellation: managed-imports-begin
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Prelude
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Defs
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildComponent
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildComponentsEquivNonroot
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildren
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedGram
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.rootedChildComponentsEquivNonroot_apply
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.rootedGram_cross_rootedChildComponents
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.rootedGram_rootedChildComponent
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.rootedNonrootGram_reindex_entry
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.rootedNonrootGram_reindex_entry_explicit
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.rootedNonrootGram_submatrix_entry
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `rootedNonrootGram_reindex_childBlocks`

Let V be a finite type with decidable equality, let G be a simple graph on V with decidable
adjacency, let hG : G.IsTree, let w : V → ℤ, and let ρ : V. Put

R := {v : V // v ≠ ρ},
S := Σ c : {c : V // c ∈ rootedChildren G hG ρ ρ}, rootedChildComponent G ρ c.1,
e : R ≃ S := (rootedChildComponentsEquivNonroot G hG ρ).symm,
D : Matrix R R ℚ := (rootedGram G w).submatrix Subtype.val Subtype.val,

and, for c in the root-child subtype, define the dependent child block

B c := rootedGram (rootedChildComponent G ρ c.1).toSimpleGraph
  (fun x : rootedChildComponent G ρ c.1 => w (x : V)),

using the canonical finite and decidable-adjacency instances of the component. Then reindexing D
along e from the nonroot index R to the sigma index S is the dependent block-diagonal matrix
determined by B: at sigma indices ⟨c,x⟩ and ⟨d,y⟩ it is B c x y after the canonical dependent
transport when c = d, and it is 0 when c ≠ d.

Equivalently, this is the exact identity Q₀ = ⨁ᵢ Q_{Cᵢ}, retaining the same e, D, and B objects and
orientation. It includes no admissibility, positivity, invertibility, or inverse conclusion.

## Sources

- Source `solution.tex`, lines 57–68

## Statement dependencies

- `SimpleGraph.IsTree` from `Mathlib.Combinatorics.SimpleGraph.Acyclic`
- `SimpleGraph.ConnectedComponent.toSimpleGraph` from
  `Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected`
- `SimpleGraph.deleteEdges` from `Mathlib.Combinatorics.SimpleGraph.DeleteEdges`
- `Matrix.blockDiagonal'` from `Mathlib.Data.Matrix.Block`
- `Matrix.reindex` from `Mathlib.LinearAlgebra.Matrix.Defs`
- `Matrix.submatrix` from `Mathlib.LinearAlgebra.Matrix.Defs`
- `Main.RootedCapacity::rootedChildComponent` → `rootedChildComponent` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildComponent`
- `Main.RootedCapacity::rootedChildComponentsEquivNonroot` → `rootedChildComponentsEquivNonroot`
  from `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildComponentsEquivNonroot`
- `Main.RootedCapacity::rootedChildren` → `rootedChildren` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildren`
- `Main.RootedCapacity::rootedGram` → `rootedGram` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedGram`

## Proof outline

Work classically and unfold only the statement's lets `R,S,e,D,B`, retaining the accepted
orientation `e : R ≃ S := (rootedChildComponentsEquivNonroot G hG ρ).symm` and the target
`Matrix.reindex e e D = Matrix.blockDiagonal' B`. Apply matrix extensionality and introduce sigma
indices `⟨c,x⟩` and `⟨d,y⟩`. Rewrite the left entry with `Matrix.reindex_apply` and the right one
with `Matrix.blockDiagonal'_apply'`.

The inverse reindex map is definitionally `e.symm = rootedChildComponentsEquivNonroot G hG ρ`.
Unfold this equivalence only at the two sigma indices: it sends `⟨c,x⟩` to the nonroot subtype whose
underlying vertex is `(x : V)`, and analogously for `⟨d,y⟩`. Hence the reindexed-`D` entry
simplifies to `rootedGram G w (x : V) (y : V)`.

Split on `hcd : c = d`. In the equal-label branch, substitute the dependent child label and
normalize the casts appearing in `Matrix.blockDiagonal'_apply'`; the right side becomes `B c x y`.
Extract `G.Adj ρ c.1` from `c.property` by unfolding the rooted-children filter. Apply
`rootedGram_rootedChildComponent G w ρ c.1 hG hρc x y` in the reverse direction to identify that
child Gram entry with the ambient Gram entry, closing the branch.

In the unequal-label branch, the block-diagonal entry is zero by `Matrix.blockDiagonal'_apply'`.
After the same reindex simplification, apply `rootedGram_cross_rootedChildComponents G hG w ρ c.1
d.1 c.property d.property`; derive `c.1 ≠ d.1` from `hcd` by subtype extensionality. This gives the
required zero ambient entry.

No admissibility, positive-definiteness, invertibility, or inverse facts are used. The proof is
solely the finite child-component reindexing and the established equal- and unequal-child Gram-entry
transports, yielding the exact private block-diagonal equality required by the accepted statement.

## Proof sources

- Source `solution.tex`, lines 57–68

## Proof dependencies

- `Matrix.blockDiagonal'_apply'` from `Mathlib.Data.Matrix.Block`
- `Matrix.ext` from `Mathlib.LinearAlgebra.Matrix.Defs`
- `Matrix.reindex_apply` from `Mathlib.LinearAlgebra.Matrix.Defs`
- `Main.RootedCapacity::rootedChildComponentsEquivNonroot` → `rootedChildComponentsEquivNonroot`
  from `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildComponentsEquivNonroot`
- `Main.RootedCapacity::rootedChildComponentsEquivNonroot_apply` →
  `rootedChildComponentsEquivNonroot_apply` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.rootedChildComponentsEquivNonroot_apply`
- `Main.RootedCapacity::rootedChildren` → `rootedChildren` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildren`
- `Main.RootedCapacity::rootedGram` → `rootedGram` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedGram`
- `Main.RootedCapacity::rootedGram_cross_rootedChildComponents` →
  `rootedGram_cross_rootedChildComponents` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.rootedGram_cross_rootedChildComponents`
- `Main.RootedCapacity::rootedGram_rootedChildComponent` → `rootedGram_rootedChildComponent` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.rootedGram_rootedChildComponent`
- `Main.RootedCapacity::rootedNonrootGram_reindex_entry` → `rootedNonrootGram_reindex_entry` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.rootedNonrootGram_reindex_entry`
- `Main.RootedCapacity::rootedNonrootGram_reindex_entry_explicit` →
  `rootedNonrootGram_reindex_entry_explicit` from `PositiveDefiniteTreeLattice.Main.RootedCapacity.T
  heorems.rootedNonrootGram_reindex_entry_explicit`
- `Main.RootedCapacity::rootedNonrootGram_submatrix_entry` → `rootedNonrootGram_submatrix_entry`
  from `PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.rootedNonrootGram_submatrix_entry`
-/
theorem rootedNonrootGram_reindex_childBlocks {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.IsTree) (w : V → ℤ) (ρ : V) :
    let R := {v : V // v ≠ ρ}
    let S := Σ c : {c : V // c ∈ rootedChildren G hG ρ ρ}, rootedChildComponent G ρ c.1
    let e : R ≃ S := (rootedChildComponentsEquivNonroot G hG ρ).symm
    let D : Matrix R R ℚ := (rootedGram G w).submatrix Subtype.val Subtype.val
    let B : ∀ c : {c : V // c ∈ rootedChildren G hG ρ ρ},
        Matrix (rootedChildComponent G ρ c.1) (rootedChildComponent G ρ c.1) ℚ := fun c =>
      let C := rootedChildComponent G ρ c.1
      letI : Fintype C := Fintype.ofFinite C
      letI : DecidableRel C.toSimpleGraph.Adj := by
        intro x y
        change Decidable ((G.deleteEdges {s(ρ, c.1)}).Adj (x : V) (y : V))
        infer_instance
      rootedGram C.toSimpleGraph (fun x : C => w (x : V))
    Matrix.reindex e e D = Matrix.blockDiagonal' B := by
  classical
  dsimp
  apply Matrix.ext
  rintro ⟨c, x⟩ ⟨d, y⟩
  rw [rootedNonrootGram_submatrix_entry G hG w ρ c d x y]
  rw [Matrix.blockDiagonal'_apply']
  by_cases hcd : c = d
  · subst d
    simp only [dif_pos]
    have hc := c.2
    simp only [rootedChildren, Finset.mem_filter, Finset.mem_univ, true_and] at hc
    simpa using (rootedGram_rootedChildComponent G w ρ c.1 hG hc.1 x y).symm
  · rw [dif_neg hcd]
    apply rootedGram_cross_rootedChildComponents G hG w ρ c.1 d.1 c.2 d.2
    intro h
    apply hcd
    exact Subtype.ext h
```

## Statement dependencies

- `Mathlib:Mathlib.Combinatorics.SimpleGraph.Acyclic.SimpleGraph.IsTree`
- `Mathlib:Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected.SimpleGraph.ConnectedComponent.toSimpleGraph`
- `Mathlib:Mathlib.Combinatorics.SimpleGraph.DeleteEdges.SimpleGraph.deleteEdges`
- `Mathlib:Mathlib.Data.Matrix.Block.Matrix.blockDiagonal'`
- `Mathlib:Mathlib.LinearAlgebra.Matrix.Defs.Matrix.reindex`
- `Mathlib:Mathlib.LinearAlgebra.Matrix.Defs.Matrix.submatrix`
- `current repo:Main.RootedCapacity.rootedChildComponent`
- `current repo:Main.RootedCapacity.rootedChildComponentsEquivNonroot`
- `current repo:Main.RootedCapacity.rootedChildren`
- `current repo:Main.RootedCapacity.rootedGram`

## Proof dependencies

- `Mathlib:Mathlib.Data.Matrix.Block.Matrix.blockDiagonal'_apply'`
- `Mathlib:Mathlib.LinearAlgebra.Matrix.Defs.Matrix.ext`
- `Mathlib:Mathlib.LinearAlgebra.Matrix.Defs.Matrix.reindex_apply`
- `current repo:Main.RootedCapacity.rootedChildComponentsEquivNonroot`
- `current repo:Main.RootedCapacity.rootedChildComponentsEquivNonroot_apply`
- `current repo:Main.RootedCapacity.rootedChildren`
- `current repo:Main.RootedCapacity.rootedGram`
- `current repo:Main.RootedCapacity.rootedGram_cross_rootedChildComponents`
- `current repo:Main.RootedCapacity.rootedGram_rootedChildComponent`
- `current repo:Main.RootedCapacity.rootedNonrootGram_reindex_entry`
- `current repo:Main.RootedCapacity.rootedNonrootGram_reindex_entry_explicit`
- `current repo:Main.RootedCapacity.rootedNonrootGram_submatrix_entry`

## Sources

- `solution.tex:57-68`
