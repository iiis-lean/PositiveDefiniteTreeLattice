-- lean-constellation: managed-imports-begin
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Prelude
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.LinearAlgebra.Matrix.Defs
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildComponent
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildComponentsEquivNonroot
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildren
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedGram
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.rootedNonrootGram_reindex_entry
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `rootedNonrootGram_reindex_entry_explicit`

Let V be a finite type with decidable equality, let G be a simple graph on V with decidable
adjacency, let hG : G.IsTree, let w : V → ℤ, let ρ : V, let

c, d : {z : V // z ∈ rootedChildren G hG ρ ρ},
x : rootedChildComponent G ρ c.1,
y : rootedChildComponent G ρ d.1.

Then, with no local abbreviations, the reindexing of the nonroot principal rooted Gram submatrix
along the specified child-component equivalence evaluates as

(Matrix.reindex (rootedChildComponentsEquivNonroot G hG ρ).symm
  (rootedChildComponentsEquivNonroot G hG ρ).symm
  ((rootedGram G w).submatrix Subtype.val Subtype.val)) ⟨c, x⟩ ⟨d, y⟩
= rootedGram G w (x : V) (y : V).

The statement preserves the exact root-child sigma indices and equivalence orientation used by the
child-block decomposition, and assumes neither admissibility nor any block-diagonal case
distinction.

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

Specialize the proved theorem
`rootedNonrootGram_reindex_entry G hG w ρ`
to the given root-child indices `c,d` and component vertices `x,y`. Its local objects reduce
definitionally to the explicit expression in the current statement:
`R = {v : V // v ≠ ρ}`,
`e = (rootedChildComponentsEquivNonroot G hG ρ).symm`, and
`D = (rootedGram G w).submatrix Subtype.val Subtype.val`.

Use a controlled `simpa only`/definitional let reduction on that specialized result to expose
precisely the no-let left-hand side and the same ambient rooted-Gram right-hand side. The sigma
indices remain `⟨c,x⟩` and `⟨d,y⟩` unchanged, and the two reindex equivalences retain the required
`.symm` orientation.

Do not unfold the equivalence, re-prove subtype coercions, invoke `Matrix.reindex_apply`, split on
`c=d`, or use a block-diagonal/component-Gram argument: all such work is deliberately delegated to
`rootedNonrootGram_reindex_entry`. This proves the exact explicit wrapper required for direct
rewriting in the block-identification theorem.

## Proof sources

- Source `solution.tex`, lines 57–62

## Proof dependencies

- `Main.RootedCapacity::rootedNonrootGram_reindex_entry` → `rootedNonrootGram_reindex_entry` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.rootedNonrootGram_reindex_entry`
-/
theorem rootedNonrootGram_reindex_entry_explicit {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.IsTree) (w : V → ℤ) (ρ : V)
    (c d : {z : V // z ∈ rootedChildren G hG ρ ρ})
    (x : rootedChildComponent G ρ c.1) (y : rootedChildComponent G ρ d.1) :
    (Matrix.reindex (rootedChildComponentsEquivNonroot G hG ρ).symm
      (rootedChildComponentsEquivNonroot G hG ρ).symm
      ((rootedGram G w).submatrix Subtype.val Subtype.val)) ⟨c, x⟩ ⟨d, y⟩ =
        rootedGram G w (x : V) (y : V) := by
  simpa only using rootedNonrootGram_reindex_entry G hG w ρ c d x y
