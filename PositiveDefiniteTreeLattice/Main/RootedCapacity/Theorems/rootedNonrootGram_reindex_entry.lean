-- lean-constellation: managed-imports-begin
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Prelude
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.LinearAlgebra.Matrix.Defs
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildComponent
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildComponentsEquivNonroot
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildren
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedGram
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.rootedChildComponentsEquivNonroot_apply
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `rootedNonrootGram_reindex_entry`

Let V be a finite type with decidable equality, let G be a simple graph on V with decidable
adjacency, let hG : G.IsTree, let w : V → ℤ, and let ρ : V. Define

R := {v : V // v ≠ ρ},
S := Σ c : {c : V // c ∈ rootedChildren G hG ρ ρ}, rootedChildComponent G ρ c.1,
e : R ≃ S := (rootedChildComponentsEquivNonroot G hG ρ).symm,
D : Matrix R R ℚ := (rootedGram G w).submatrix Subtype.val Subtype.val.

For every root-child index c,d : {c : V // c ∈ rootedChildren G hG ρ ρ}, every x :
rootedChildComponent G ρ c.1, and every y : rootedChildComponent G ρ d.1, the reindexed nonroot Gram
entry is the ambient Gram entry:

(Matrix.reindex e e D) ⟨c, x⟩ ⟨d, y⟩ = rootedGram G w (x : V) (y : V).

The statement retains the full sigma indices and the exact e/D orientation, with no case split on c
= d and no admissibility assumption.

## Sources

- Source `solution.tex`, lines 57–62

## Statement dependencies

- `SimpleGraph.IsTree` from `Mathlib.Combinatorics.SimpleGraph.Acyclic`
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

Work classically and unfold the statement's lets `R,S,e,D` without changing their orientation: `e :
R ≃ S` remains `(rootedChildComponentsEquivNonroot G hG ρ).symm`. Introduce the four arbitrary
inputs `c,d,x,y`.

Rewrite the left-hand side with `Matrix.reindex_apply`. Its two reindexed sigma arguments are then
`e.symm ⟨c,x⟩` and `e.symm ⟨d,y⟩`; definitionally `e.symm` is `rootedChildComponentsEquivNonroot G
hG ρ`. Apply the proved full-subtype bridge `rootedChildComponentsEquivNonroot_apply G hG ρ c x` to
the first index and the same theorem at `d,y` to the second. These rewrites are at the subtype
level, so they avoid any dependent-coercion elaboration or manual proof conversion.

After the two rewrites, unfold the two nested `Matrix.submatrix` entries defining `D`. Each embedded
nonroot index coerces definitionally to `(x : V)`, respectively `(y : V)`; proof irrelevance handles
the nonroot witnesses. The remaining equality is reflexive:
`rootedGram G w (x : V) (y : V) = rootedGram G w (x : V) (y : V)`.

No split on the root-child labels, block-diagonal constructor, component-Gram transport,
admissibility, or inverse fact is used. This is only the exact entrywise reindex normalization
needed by the subsequent block theorem.

## Proof sources

- Source `solution.tex`, lines 57–62

## Proof dependencies

- `Matrix.reindex_apply` from `Mathlib.LinearAlgebra.Matrix.Defs`
- `Main.RootedCapacity::rootedChildComponent` → `rootedChildComponent` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildComponent`
- `Main.RootedCapacity::rootedChildComponentsEquivNonroot` → `rootedChildComponentsEquivNonroot`
  from `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildComponentsEquivNonroot`
- `Main.RootedCapacity::rootedChildComponentsEquivNonroot_apply` →
  `rootedChildComponentsEquivNonroot_apply` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.rootedChildComponentsEquivNonroot_apply`
- `Main.RootedCapacity::rootedChildren` → `rootedChildren` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildren`
- `Main.RootedCapacity::rootedGram` → `rootedGram` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedGram`
-/
theorem rootedNonrootGram_reindex_entry {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.IsTree) (w : V → ℤ) (ρ : V) :
    let R := {v : V // v ≠ ρ}
    let S := Σ c : {c : V // c ∈ rootedChildren G hG ρ ρ}, rootedChildComponent G ρ c.1
    let e : R ≃ S := (rootedChildComponentsEquivNonroot G hG ρ).symm
    let D : Matrix R R ℚ := (rootedGram G w).submatrix Subtype.val Subtype.val
    ∀ (c d : {c : V // c ∈ rootedChildren G hG ρ ρ})
      (x : rootedChildComponent G ρ c.1) (y : rootedChildComponent G ρ d.1),
      (Matrix.reindex e e D) ⟨c, x⟩ ⟨d, y⟩ = rootedGram G w (x : V) (y : V) := by
  classical
  dsimp
  intro c d x y
  rw [rootedChildComponentsEquivNonroot_apply G hG ρ c x,
    rootedChildComponentsEquivNonroot_apply G hG ρ d y]
