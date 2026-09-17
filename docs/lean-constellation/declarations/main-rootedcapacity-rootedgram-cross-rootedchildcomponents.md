[← Public API](../PUBLIC_API.md) · [Public boundaries](../PUBLIC_BOUNDARIES.md) · [Complete graph](../DECLARATION_GRAPH.md)

# `rootedGram_cross_rootedChildComponents`

Gram entries vanish between distinct root-child components.

- Kind: `theorem`
- Node: `Main.RootedCapacity`
- Module: `PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.rootedGram_cross_rootedChildComponents`
- State: `proved`
- Revision status: `committed`
- Repository completion: `graph_proved`
- Compatibility `formal_code`: final proof projection

## Statement NL

Let V be a finite type with decidable equality, let G be a simple graph on V with decidable adjacency, let hG : G.IsTree, let w : V → ℤ, and let ρ, c, d : V. Suppose c ∈ rootedChildren G hG ρ ρ, d ∈ rootedChildren G hG ρ ρ, and c ≠ d. For every x : rootedChildComponent G ρ c and y : rootedChildComponent G ρ d, the ambient rational rooted Gram entry vanishes:

rootedGram G w (x : V) (y : V) = 0.

The statement retains the existing deleted-edge child-component indices and gives precisely the zero off-diagonal child-block entry used in the root/rest decomposition.

## Statement Formal

```lean
-- lean-constellation: managed-imports-begin
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Prelude
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildComponent
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildren
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedGram
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `rootedGram_cross_rootedChildComponents`

Let V be a finite type with decidable equality, let G be a simple graph on V with decidable
adjacency, let hG : G.IsTree, let w : V → ℤ, and let ρ, c, d : V. Suppose c ∈ rootedChildren G hG ρ
ρ, d ∈ rootedChildren G hG ρ ρ, and c ≠ d. For every x : rootedChildComponent G ρ c and y :
rootedChildComponent G ρ d, the ambient rational rooted Gram entry vanishes:

rootedGram G w (x : V) (y : V) = 0.

The statement retains the existing deleted-edge child-component indices and gives precisely the zero
off-diagonal child-block entry used in the root/rest decomposition.

## Sources

- Source `solution.tex`, lines 57–63

## Statement dependencies

- `SimpleGraph.IsTree` from `Mathlib.Combinatorics.SimpleGraph.Acyclic`
- `Main.RootedCapacity::rootedChildComponent` → `rootedChildComponent` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildComponent`
- `Main.RootedCapacity::rootedChildren` → `rootedChildren` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildren`
- `Main.RootedCapacity::rootedGram` → `rootedGram` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedGram`
-/
theorem rootedGram_cross_rootedChildComponents {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.IsTree) (w : V → ℤ) (ρ c d : V)
    (hc : c ∈ rootedChildren G hG ρ ρ) (hd : d ∈ rootedChildren G hG ρ ρ) (hcd : c ≠ d)
    (x : rootedChildComponent G ρ c) (y : rootedChildComponent G ρ d) :
    rootedGram G w (x : V) (y : V) = 0 := by
  sorry
```

## Proof NL

First extract the root adjacencies `G.Adj ρ c` and `G.Adj ρ d` from `hc` and `hd`.  The public cut theorem `rootedChildComponent_parent_not_mem` then gives `(x : V) ≠ ρ` and `(y : V) ≠ ρ` for the two component vertices.

Show that the underlying vertices are distinct.  If `(x : V) = (y : V)`, then that common nonroot vertex lies in both `rootedChildComponent G ρ c` (from `x.property`) and `rootedChildComponent G ρ d` (from `y.property`).  Apply the proved unique partition theorem `rootedChildComponent_partition G hG ρ (y : V)` to its two root-child/component witnesses; uniqueness gives `c = d`, contradicting `hcd`.

Show `¬ G.Adj (x : V) (y : V)`.  Were such an edge present, it cannot be the deleted edge `{ρ,c}`: either orientation of an equality `s((x : V),(y : V)) = s(ρ,c)` would force `x = ρ` or `y = ρ`, excluded above.  Hence `SimpleGraph.deleteEdges_adj` makes it an adjacency in `G.deleteEdges {s(ρ,c)}`.  Since `x.property` puts `x` in the `c` connected component, `SimpleGraph.ConnectedComponent.mem_supp_of_adj_mem_supp` puts `y` in that same component.  Together with `y.property` in the `d` component and the two rooted-child hypotheses, the uniqueness clause of `rootedChildComponent_partition` again gives `c = d`, contradicting `hcd`.

Finally unfold `rootedGram` and apply the proved private bridge `treePairing_vertexVector_vertexVector G hG`.  Its distinct-nonadjacent branch, using the established underlying-vertex inequality and `¬ G.Adj (x : V) (y : V)`, simplifies the ambient rational Gram entry to `0`.  This is a local private block helper only; it preserves the ambient Gram and existing deleted-edge component indices.

## Proof Formal

```lean
-- lean-constellation: managed-imports-begin
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Prelude
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Data.Sym.Sym2
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildComponent
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildren
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedGram
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.rootedChildComponent_parent_not_mem
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.rootedChildComponent_partition
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.treePairing_vertexVector_vertexVector
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `rootedGram_cross_rootedChildComponents`

Let V be a finite type with decidable equality, let G be a simple graph on V with decidable
adjacency, let hG : G.IsTree, let w : V → ℤ, and let ρ, c, d : V. Suppose c ∈ rootedChildren G hG ρ
ρ, d ∈ rootedChildren G hG ρ ρ, and c ≠ d. For every x : rootedChildComponent G ρ c and y :
rootedChildComponent G ρ d, the ambient rational rooted Gram entry vanishes:

rootedGram G w (x : V) (y : V) = 0.

The statement retains the existing deleted-edge child-component indices and gives precisely the zero
off-diagonal child-block entry used in the root/rest decomposition.

## Sources

- Source `solution.tex`, lines 57–63

## Statement dependencies

- `SimpleGraph.IsTree` from `Mathlib.Combinatorics.SimpleGraph.Acyclic`
- `Main.RootedCapacity::rootedChildComponent` → `rootedChildComponent` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildComponent`
- `Main.RootedCapacity::rootedChildren` → `rootedChildren` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildren`
- `Main.RootedCapacity::rootedGram` → `rootedGram` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedGram`

## Proof outline

First extract the root adjacencies `G.Adj ρ c` and `G.Adj ρ d` from `hc` and `hd`.  The public cut
theorem `rootedChildComponent_parent_not_mem` then gives `(x : V) ≠ ρ` and `(y : V) ≠ ρ` for the two
component vertices.

Show that the underlying vertices are distinct.  If `(x : V) = (y : V)`, then that common nonroot
vertex lies in both `rootedChildComponent G ρ c` (from `x.property`) and `rootedChildComponent G ρ
d` (from `y.property`).  Apply the proved unique partition theorem `rootedChildComponent_partition G
hG ρ (y : V)` to its two root-child/component witnesses; uniqueness gives `c = d`, contradicting
`hcd`.

Show `¬ G.Adj (x : V) (y : V)`.  Were such an edge present, it cannot be the deleted edge `{ρ,c}`:
either orientation of an equality `s((x : V),(y : V)) = s(ρ,c)` would force `x = ρ` or `y = ρ`,
excluded above.  Hence `SimpleGraph.deleteEdges_adj` makes it an adjacency in `G.deleteEdges
{s(ρ,c)}`.  Since `x.property` puts `x` in the `c` connected component,
`SimpleGraph.ConnectedComponent.mem_supp_of_adj_mem_supp` puts `y` in that same component.  Together
with `y.property` in the `d` component and the two rooted-child hypotheses, the uniqueness clause of
`rootedChildComponent_partition` again gives `c = d`, contradicting `hcd`.

Finally unfold `rootedGram` and apply the proved private bridge
`treePairing_vertexVector_vertexVector G hG`.  Its distinct-nonadjacent branch, using the
established underlying-vertex inequality and `¬ G.Adj (x : V) (y : V)`, simplifies the ambient
rational Gram entry to `0`.  This is a local private block helper only; it preserves the ambient
Gram and existing deleted-edge component indices.

## Proof sources

- Source `solution.tex`, lines 57–63

## Proof dependencies

- `SimpleGraph.ConnectedComponent.mem_supp_of_adj_mem_supp` from
  `Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected`
- `SimpleGraph.deleteEdges_adj` from `Mathlib.Combinatorics.SimpleGraph.DeleteEdges`
- `Sym2.eq_iff` from `Mathlib.Data.Sym.Sym2`
- `Main.RootedCapacity::rootedChildComponent` → `rootedChildComponent` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildComponent`
- `Main.RootedCapacity::rootedChildComponent_parent_not_mem` → `rootedChildComponent_parent_not_mem`
  from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.rootedChildComponent_parent_not_mem`
- `Main.RootedCapacity::rootedChildComponent_partition` → `rootedChildComponent_partition` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.rootedChildComponent_partition`
- `Main.RootedCapacity::rootedChildren` → `rootedChildren` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildren`
- `Main.RootedCapacity::rootedGram` → `rootedGram` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedGram`
- `Main.RootedCapacity::treePairing_vertexVector_vertexVector` →
  `treePairing_vertexVector_vertexVector` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.treePairing_vertexVector_vertexVector`
-/
theorem rootedGram_cross_rootedChildComponents {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.IsTree) (w : V → ℤ) (ρ c d : V)
    (hc : c ∈ rootedChildren G hG ρ ρ) (hd : d ∈ rootedChildren G hG ρ ρ) (hcd : c ≠ d)
    (x : rootedChildComponent G ρ c) (y : rootedChildComponent G ρ d) :
    rootedGram G w (x : V) (y : V) = 0 := by
  classical
  have hc' := hc
  have hd' := hd
  simp only [rootedChildren, Finset.mem_filter, Finset.mem_univ, true_and] at hc' hd'
  obtain ⟨hρc, -, -, -⟩ := hc'
  obtain ⟨hρd, -, -, -⟩ := hd'
  have hxne : (x : V) ≠ ρ := rootedChildComponent_parent_not_mem G ρ c hG hρc x
  have hyne : (y : V) ≠ ρ := rootedChildComponent_parent_not_mem G ρ d hG hρd y
  have hxy_ne : (x : V) ≠ (y : V) := by
    intro hxy
    have hyC : (y : V) ∈ rootedChildComponent G ρ c := by
      rw [← hxy]
      exact x.property
    obtain ⟨k, -, hunique⟩ := rootedChildComponent_partition G hG ρ (y : V) hyne
    have hck : c = k := hunique c ⟨hc, hyC⟩
    have hdk : d = k := hunique d ⟨hd, y.property⟩
    exact hcd (hck.trans hdk.symm)
  have hnoadj : ¬ G.Adj (x : V) (y : V) := by
    intro hxy
    have hnotcut : s((x : V), (y : V)) ∉ ({s(ρ, c)} : Set (Sym2 V)) := by
      simp only [Set.mem_singleton_iff]
      intro hcut
      rcases Sym2.eq_iff.mp hcut with ⟨hxr, hyc⟩ | ⟨hxc, hyr⟩
      · exact hxne hxr
      · exact hyne hyr
    have hxycut : (G.deleteEdges {s(ρ, c)}).Adj (x : V) (y : V) :=
      SimpleGraph.deleteEdges_adj.mpr ⟨hxy, hnotcut⟩
    have hyC : (y : V) ∈ rootedChildComponent G ρ c :=
      SimpleGraph.ConnectedComponent.mem_supp_of_adj_mem_supp _ x.property hxycut
    obtain ⟨k, -, hunique⟩ := rootedChildComponent_partition G hG ρ (y : V) hyne
    have hck : c = k := hunique c ⟨hc, hyC⟩
    have hdk : d = k := hunique d ⟨hd, y.property⟩
    exact hcd (hck.trans hdk.symm)
  unfold rootedGram
  rw [treePairing_vertexVector_vertexVector G hG]
  simp [hxy_ne, hnoadj]
```

## Statement dependencies

- `Mathlib:Mathlib.Combinatorics.SimpleGraph.Acyclic.SimpleGraph.IsTree`
- `current repo:Main.RootedCapacity.rootedChildComponent`
- `current repo:Main.RootedCapacity.rootedChildren`
- `current repo:Main.RootedCapacity.rootedGram`

## Proof dependencies

- `Mathlib:Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected.SimpleGraph.ConnectedComponent.mem_supp_of_adj_mem_supp`
- `Mathlib:Mathlib.Combinatorics.SimpleGraph.DeleteEdges.SimpleGraph.deleteEdges_adj`
- `Mathlib:Mathlib.Data.Sym.Sym2.Sym2.eq_iff`
- `current repo:Main.RootedCapacity.rootedChildComponent`
- `current repo:Main.RootedCapacity.rootedChildComponent_parent_not_mem`
- `current repo:Main.RootedCapacity.rootedChildComponent_partition`
- `current repo:Main.RootedCapacity.rootedChildren`
- `current repo:Main.RootedCapacity.rootedGram`
- `current repo:Main.RootedCapacity.treePairing_vertexVector_vertexVector`

## Sources

- `solution.tex:57-63`
