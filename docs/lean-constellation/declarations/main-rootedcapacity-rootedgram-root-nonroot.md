[← Public API](../PUBLIC_API.md) · [Public boundaries](../PUBLIC_BOUNDARIES.md) · [Complete graph](../DECLARATION_GRAPH.md)

# `rootedGram_root_nonroot`

The root row of rootedGram is minus one on root children and zero on other nonroot vertices.

- Kind: `theorem`
- Node: `Main.RootedCapacity`
- Module: `PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.rootedGram_root_nonroot`
- State: `proved`
- Revision status: `committed`
- Repository completion: `graph_proved`
- Compatibility `formal_code`: final proof projection

## Statement NL

Let V be a finite type with decidable equality, let G be a simple graph on V with decidable adjacency, let hG : G.IsTree, let w : V → ℤ, let ρ : V, and let x : V with x ≠ ρ. Then the ambient rational rooted Gram entry in the root row is

rootedGram G w ρ x = if x ∈ rootedChildren G hG ρ ρ then (-1 : ℚ) else 0.

Equivalently, it is −1 exactly when x is a rooted child of ρ and is 0 for every nonroot vertex that is not a rooted child. No admissibility or additional weight hypothesis is assumed.

## Statement Formal

```lean
-- lean-constellation: managed-imports-begin
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Prelude
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildren
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedGram
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `rootedGram_root_nonroot`

Let V be a finite type with decidable equality, let G be a simple graph on V with decidable
adjacency, let hG : G.IsTree, let w : V → ℤ, let ρ : V, and let x : V with x ≠ ρ. Then the ambient
rational rooted Gram entry in the root row is

rootedGram G w ρ x = if x ∈ rootedChildren G hG ρ ρ then (-1 : ℚ) else 0.

Equivalently, it is −1 exactly when x is a rooted child of ρ and is 0 for every nonroot vertex that
is not a rooted child. No admissibility or additional weight hypothesis is assumed.

## Sources

- Source `solution.tex`, lines 57–63

## Statement dependencies

- `SimpleGraph.IsTree` from `Mathlib.Combinatorics.SimpleGraph.Acyclic`
- `Main.RootedCapacity::rootedChildren` → `rootedChildren` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildren`
- `Main.RootedCapacity::rootedGram` → `rootedGram` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedGram`
-/
theorem rootedGram_root_nonroot {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.IsTree) (w : V → ℤ) (ρ x : V)
    (hx : x ≠ ρ) :
    rootedGram G w ρ x = if x ∈ rootedChildren G hG ρ ρ then (-1 : ℚ) else 0 := by
  sorry
```

## Proof NL

Establish the key equivalence `x ∈ rootedChildren G hG ρ ρ ↔ G.Adj ρ x`.  In the forward direction, unfold the `Finset.filter` definition of `rootedChildren` and take its adjacency witness.  In the reverse direction, given `hρx : G.Adj ρ x`, use the empty root-prefix walk and the one-edge walk `hρx.toWalk`.  `SimpleGraph.Walk.IsPath.of_adj hρx` makes this a simple path, and uniqueness from `hG.existsUnique_path ρ x` identifies it with the canonical root-to-`x` path.  This exactly fills the rootedChildren predicate, so no extra orientation assumption is needed.

Unfold only `rootedGram` and apply the proved private basis-entry theorem `treePairing_vertexVector_vertexVector G hG`.  The hypothesis `hx : x ≠ ρ` removes the diagonal branch.  Split on `x ∈ rootedChildren G hG ρ ρ`: in the true case use the equivalence to rewrite the adjacency branch to `-1 : ℚ`; in the false case use its contrapositive to rewrite the adjacency branch to `0`.  Reassemble the two cases as the accepted `if` expression.  The argument assumes neither admissibility nor a weight inequality and leaves this as a private root-row helper.

## Proof Formal

```lean
-- lean-constellation: managed-imports-begin
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Prelude
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Paths
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildren
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedGram
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.treePairing_vertexVector_vertexVector
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `rootedGram_root_nonroot`

Let V be a finite type with decidable equality, let G be a simple graph on V with decidable
adjacency, let hG : G.IsTree, let w : V → ℤ, let ρ : V, and let x : V with x ≠ ρ. Then the ambient
rational rooted Gram entry in the root row is

rootedGram G w ρ x = if x ∈ rootedChildren G hG ρ ρ then (-1 : ℚ) else 0.

Equivalently, it is −1 exactly when x is a rooted child of ρ and is 0 for every nonroot vertex that
is not a rooted child. No admissibility or additional weight hypothesis is assumed.

## Sources

- Source `solution.tex`, lines 57–63

## Statement dependencies

- `SimpleGraph.IsTree` from `Mathlib.Combinatorics.SimpleGraph.Acyclic`
- `Main.RootedCapacity::rootedChildren` → `rootedChildren` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildren`
- `Main.RootedCapacity::rootedGram` → `rootedGram` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedGram`

## Proof outline

Establish the key equivalence `x ∈ rootedChildren G hG ρ ρ ↔ G.Adj ρ x`.  In the forward direction,
unfold the `Finset.filter` definition of `rootedChildren` and take its adjacency witness.  In the
reverse direction, given `hρx : G.Adj ρ x`, use the empty root-prefix walk and the one-edge walk
`hρx.toWalk`.  `SimpleGraph.Walk.IsPath.of_adj hρx` makes this a simple path, and uniqueness from
`hG.existsUnique_path ρ x` identifies it with the canonical root-to-`x` path.  This exactly fills
the rootedChildren predicate, so no extra orientation assumption is needed.

Unfold only `rootedGram` and apply the proved private basis-entry theorem
`treePairing_vertexVector_vertexVector G hG`.  The hypothesis `hx : x ≠ ρ` removes the diagonal
branch.  Split on `x ∈ rootedChildren G hG ρ ρ`: in the true case use the equivalence to rewrite the
adjacency branch to `-1 : ℚ`; in the false case use its contrapositive to rewrite the adjacency
branch to `0`.  Reassemble the two cases as the accepted `if` expression.  The argument assumes
neither admissibility nor a weight inequality and leaves this as a private root-row helper.

## Proof sources

- Source `solution.tex`, lines 57–63

## Proof dependencies

- `SimpleGraph.IsTree.existsUnique_path` from `Mathlib.Combinatorics.SimpleGraph.Acyclic`
- `SimpleGraph.Walk.IsPath.of_adj` from `Mathlib.Combinatorics.SimpleGraph.Paths`
- `Main.RootedCapacity::rootedChildren` → `rootedChildren` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildren`
- `Main.RootedCapacity::rootedGram` → `rootedGram` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedGram`
- `Main.RootedCapacity::treePairing_vertexVector_vertexVector` →
  `treePairing_vertexVector_vertexVector` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.treePairing_vertexVector_vertexVector`
-/
theorem rootedGram_root_nonroot {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.IsTree) (w : V → ℤ) (ρ x : V)
    (hx : x ≠ ρ) :
    rootedGram G w ρ x = if x ∈ rootedChildren G hG ρ ρ then (-1 : ℚ) else 0 := by
  classical
  have hchild : x ∈ rootedChildren G hG ρ ρ ↔ G.Adj ρ x := by
    constructor
    · intro h
      simp only [rootedChildren, Finset.mem_filter, Finset.mem_univ, true_and] at h
      exact h.1
    · intro hρx
      simp only [rootedChildren, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨hρx, .nil, SimpleGraph.Walk.IsPath.nil, ?_⟩
      have hsingle : (hG.existsUnique_path ρ x).choose =
          SimpleGraph.Walk.cons hρx .nil := by
        apply (hG.existsUnique_path ρ x).unique
        · exact (hG.existsUnique_path ρ x).choose_spec.1
        · exact SimpleGraph.Walk.IsPath.of_adj hρx
      simpa [SimpleGraph.Walk.concat] using hsingle
  unfold rootedGram
  rw [treePairing_vertexVector_vertexVector G hG]
  simp [hx.symm, hchild]
```

## Statement dependencies

- `Mathlib:Mathlib.Combinatorics.SimpleGraph.Acyclic.SimpleGraph.IsTree`
- `current repo:Main.RootedCapacity.rootedChildren`
- `current repo:Main.RootedCapacity.rootedGram`

## Proof dependencies

- `Mathlib:Mathlib.Combinatorics.SimpleGraph.Acyclic.SimpleGraph.IsTree.existsUnique_path`
- `Mathlib:Mathlib.Combinatorics.SimpleGraph.Paths.SimpleGraph.Walk.IsPath.of_adj`
- `current repo:Main.RootedCapacity.rootedChildren`
- `current repo:Main.RootedCapacity.rootedGram`
- `current repo:Main.RootedCapacity.treePairing_vertexVector_vertexVector`

## Sources

- `solution.tex:57-63`
