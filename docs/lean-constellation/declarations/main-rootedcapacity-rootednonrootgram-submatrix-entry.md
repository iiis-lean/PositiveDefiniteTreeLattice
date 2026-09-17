[← Public API](../PUBLIC_API.md) · [Public boundaries](../PUBLIC_BOUNDARIES.md) · [Complete graph](../DECLARATION_GRAPH.md)

# `rootedNonrootGram_submatrix_entry`

The nested nonroot-principal-submatrix entry at child-component indices equals the corresponding ambient rooted Gram entry.

- Kind: `theorem`
- Node: `Main.RootedCapacity`
- Module: `PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.rootedNonrootGram_submatrix_entry`
- State: `proved`
- Revision status: `committed`
- Repository completion: `graph_proved`
- Compatibility `formal_code`: final proof projection

## Statement NL

Let V be a finite type with decidable equality, let G be a simple graph on V with decidable adjacency, let hG : G.IsTree, let w : V → ℤ, let ρ : V, let

c, d : {z : V // z ∈ rootedChildren G hG ρ ρ},
x : rootedChildComponent G ρ c.1,
y : rootedChildComponent G ρ d.1.

Then the nonroot principal submatrix of rootedGram G w, further submatrixed along the forward map rootedChildComponentsEquivNonroot G hG ρ from the child-component sigma type to the nonroot subtype, has the ambient entry

((rootedGram G w).submatrix Subtype.val Subtype.val).submatrix
  (rootedChildComponentsEquivNonroot G hG ρ)
  (rootedChildComponentsEquivNonroot G hG ρ)
  ⟨c, x⟩ ⟨d, y⟩
= rootedGram G w (x : V) (y : V).

This is the exact nested-submatrix normal form of the source’s nonroot child-subtree grouping; it uses neither Matrix.reindex nor any child-equality, block-diagonal, or admissibility condition.

## Statement Formal

```lean
-- lean-constellation: managed-imports-begin
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Prelude
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.LinearAlgebra.Matrix.Defs
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildComponent
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildComponentsEquivNonroot
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildren
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedGram
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `rootedNonrootGram_submatrix_entry`

Let V be a finite type with decidable equality, let G be a simple graph on V with decidable
adjacency, let hG : G.IsTree, let w : V → ℤ, let ρ : V, let

c, d : {z : V // z ∈ rootedChildren G hG ρ ρ},
x : rootedChildComponent G ρ c.1,
y : rootedChildComponent G ρ d.1.

Then the nonroot principal submatrix of rootedGram G w, further submatrixed along the forward map
rootedChildComponentsEquivNonroot G hG ρ from the child-component sigma type to the nonroot subtype,
has the ambient entry

((rootedGram G w).submatrix Subtype.val Subtype.val).submatrix
  (rootedChildComponentsEquivNonroot G hG ρ)
  (rootedChildComponentsEquivNonroot G hG ρ)
  ⟨c, x⟩ ⟨d, y⟩
= rootedGram G w (x : V) (y : V).

This is the exact nested-submatrix normal form of the source’s nonroot child-subtree grouping; it
uses neither Matrix.reindex nor any child-equality, block-diagonal, or admissibility condition.

## Sources

- Source `solution.tex`, lines 57–62

## Statement dependencies

- `SimpleGraph.IsTree` from `Mathlib.Combinatorics.SimpleGraph.Acyclic`
- `Matrix.submatrix` from `Mathlib.LinearAlgebra.Matrix.Defs`
- `Main.RootedCapacity::rootedChildComponent` → `rootedChildComponent` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildComponent`
- `Main.RootedCapacity::rootedChildComponentsEquivNonroot` → `rootedChildComponentsEquivNonroot`
  from `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildComponentsEquivNonroot`
- `Main.RootedCapacity::rootedChildren` → `rootedChildren` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildren`
- `Main.RootedCapacity::rootedGram` → `rootedGram` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedGram`
-/

theorem rootedNonrootGram_submatrix_entry {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.IsTree) (w : V → ℤ) (ρ : V)
    (c d : {z : V // z ∈ rootedChildren G hG ρ ρ})
    (x : rootedChildComponent G ρ c.1) (y : rootedChildComponent G ρ d.1) :
    ((rootedGram G w).submatrix Subtype.val Subtype.val).submatrix
      (rootedChildComponentsEquivNonroot G hG ρ)
      (rootedChildComponentsEquivNonroot G hG ρ)
      ⟨c, x⟩ ⟨d, y⟩ = rootedGram G w (x : V) (y : V) := by
  sorry
```

## Proof NL

The explicit bridge rootedNonrootGram_reindex_entry_explicit G hG w ρ c d x y gives the reindexed entry. Matrix.reindex_apply identifies its left side with the nested submatrix because the inverse maps of (rootedChildComponentsEquivNonroot G hG ρ).symm are the forward map rootedChildComponentsEquivNonroot G hG ρ. Hence the left side is exactly
((rootedGram G w).submatrix Subtype.val Subtype.val).submatrix
  (rootedChildComponentsEquivNonroot G hG ρ)
  (rootedChildComponentsEquivNonroot G hG ρ) ⟨c,x⟩ ⟨d,y⟩.

The specialized theorem therefore has precisely the statement's ambient right-hand side rootedGram G w (x : V) (y : V). The argument preserves the exact forward-map indices and no-let representation, introduces no child-label split or block-diagonal fact, and uses no additional admissibility condition; this normalized identity is the rewrite shape required by rootedNonrootGram_reindex_childBlocks.

## Proof Formal

```lean
-- lean-constellation: managed-imports-begin
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Prelude
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.LinearAlgebra.Matrix.Defs
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildComponent
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildComponentsEquivNonroot
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildren
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedGram
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.rootedNonrootGram_reindex_entry_explicit
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `rootedNonrootGram_submatrix_entry`

Let V be a finite type with decidable equality, let G be a simple graph on V with decidable
adjacency, let hG : G.IsTree, let w : V → ℤ, let ρ : V, let

c, d : {z : V // z ∈ rootedChildren G hG ρ ρ},
x : rootedChildComponent G ρ c.1,
y : rootedChildComponent G ρ d.1.

Then the nonroot principal submatrix of rootedGram G w, further submatrixed along the forward map
rootedChildComponentsEquivNonroot G hG ρ from the child-component sigma type to the nonroot subtype,
has the ambient entry

((rootedGram G w).submatrix Subtype.val Subtype.val).submatrix
  (rootedChildComponentsEquivNonroot G hG ρ)
  (rootedChildComponentsEquivNonroot G hG ρ)
  ⟨c, x⟩ ⟨d, y⟩
= rootedGram G w (x : V) (y : V).

This is the exact nested-submatrix normal form of the source’s nonroot child-subtree grouping; it
uses neither Matrix.reindex nor any child-equality, block-diagonal, or admissibility condition.

## Sources

- Source `solution.tex`, lines 57–62

## Statement dependencies

- `SimpleGraph.IsTree` from `Mathlib.Combinatorics.SimpleGraph.Acyclic`
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

Specialize the proved explicit bridge
`rootedNonrootGram_reindex_entry_explicit G hG w ρ c d x y`.
Rewrite only its left-hand reindex matrix using `Matrix.reindex_apply`. Since both reindex
equivalences are
`(rootedChildComponentsEquivNonroot G hG ρ).symm`,
their inverse maps simplify definitionally to the forward map
`rootedChildComponentsEquivNonroot G hG ρ`. The rewritten left-hand side is therefore exactly
`((rootedGram G w).submatrix Subtype.val Subtype.val).submatrix
  (rootedChildComponentsEquivNonroot G hG ρ)
  (rootedChildComponentsEquivNonroot G hG ρ) ⟨c,x⟩ ⟨d,y⟩`.

Finish by controlled `simpa only [Matrix.reindex_apply]` from that specialized theorem. This neither
unfolds the noncomputable equivalence nor repeats any coercion proof; it introduces no child-label
split, block-diagonal reasoning, or additional mathematical fact. The result is precisely the
normalized nested-submatrix entry shape required for direct rewriting in
`rootedNonrootGram_reindex_childBlocks`.

## Proof sources

- Source `solution.tex`, lines 57–62

## Proof dependencies

- `Matrix.reindex_apply` from `Mathlib.LinearAlgebra.Matrix.Defs`
- `Main.RootedCapacity::rootedNonrootGram_reindex_entry_explicit` →
  `rootedNonrootGram_reindex_entry_explicit` from `PositiveDefiniteTreeLattice.Main.RootedCapacity.T
  heorems.rootedNonrootGram_reindex_entry_explicit`
-/
theorem rootedNonrootGram_submatrix_entry {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.IsTree) (w : V → ℤ) (ρ : V)
    (c d : {z : V // z ∈ rootedChildren G hG ρ ρ})
    (x : rootedChildComponent G ρ c.1) (y : rootedChildComponent G ρ d.1) :
    ((rootedGram G w).submatrix Subtype.val Subtype.val).submatrix
      (rootedChildComponentsEquivNonroot G hG ρ)
      (rootedChildComponentsEquivNonroot G hG ρ)
      ⟨c, x⟩ ⟨d, y⟩ = rootedGram G w (x : V) (y : V) := by
  simpa only [Matrix.reindex_apply, Equiv.symm_symm] using
    rootedNonrootGram_reindex_entry_explicit G hG w ρ c d x y
```

## Statement dependencies

- `Mathlib:Mathlib.Combinatorics.SimpleGraph.Acyclic.SimpleGraph.IsTree`
- `Mathlib:Mathlib.LinearAlgebra.Matrix.Defs.Matrix.submatrix`
- `current repo:Main.RootedCapacity.rootedChildComponent`
- `current repo:Main.RootedCapacity.rootedChildComponentsEquivNonroot`
- `current repo:Main.RootedCapacity.rootedChildren`
- `current repo:Main.RootedCapacity.rootedGram`

## Proof dependencies

- `Mathlib:Mathlib.LinearAlgebra.Matrix.Defs.Matrix.reindex_apply`
- `current repo:Main.RootedCapacity.rootedNonrootGram_reindex_entry_explicit`

## Sources

- `solution.tex:57-62`
