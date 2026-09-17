[← Public API](../PUBLIC_API.md) · [Public boundaries](../PUBLIC_BOUNDARIES.md) · [Complete graph](../DECLARATION_GRAPH.md)

# `rootedGram_rootedChildComponent`

The child component Gram matrix is the corresponding principal submatrix of the ambient rooted Gram matrix.

- Kind: `theorem`
- Node: `Main.RootedCapacity`
- Module: `PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.rootedGram_rootedChildComponent`
- State: `proved`
- Revision status: `committed`
- Repository completion: `graph_proved`
- Compatibility `formal_code`: final proof projection

## Statement NL

For a finite vertex type `V` with decidable equality, a simple graph `G : SimpleGraph V`, an integer weight function `w : V → ℤ`, vertices `parent c : V`, a tree hypothesis `hG : G.IsTree`, and an adjacency hypothesis `hpc : G.Adj parent c`, let `C := rootedChildComponent G parent c`.  Then the rational rooted Gram matrix of the induced child-component graph with restricted weight agrees entrywise with the ambient rooted Gram matrix along the subtype inclusion: for all `x y : C`, `rootedGram C.toSimpleGraph (fun z : C => w (z : V)) x y = rootedGram G w (x : V) (y : V)`.  Equivalently, it is the principal submatrix of `rootedGram G w` reindexed by `C → V`.  No positive-definiteness, admissibility, or root-orientation hypothesis is assumed.

## Statement Formal

```lean
-- lean-constellation: managed-imports-begin
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Prelude
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildComponent
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedGram
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `rootedGram_rootedChildComponent`

For a finite vertex type `V` with decidable equality, a simple graph `G : SimpleGraph V`, an integer
weight function `w : V → ℤ`, vertices `parent c : V`, a tree hypothesis `hG : G.IsTree`, and an
adjacency hypothesis `hpc : G.Adj parent c`, let `C := rootedChildComponent G parent c`.  Then the
rational rooted Gram matrix of the induced child-component graph with restricted weight agrees
entrywise with the ambient rooted Gram matrix along the subtype inclusion: for all `x y : C`,
`rootedGram C.toSimpleGraph (fun z : C => w (z : V)) x y = rootedGram G w (x : V) (y : V)`.
Equivalently, it is the principal submatrix of `rootedGram G w` reindexed by `C → V`.  No
positive-definiteness, admissibility, or root-orientation hypothesis is assumed.

## Sources

- Source `solution.tex`, lines 57–62

## Statement dependencies

- `SimpleGraph.IsTree` from `Mathlib.Combinatorics.SimpleGraph.Acyclic`
- `SimpleGraph.ConnectedComponent.toSimpleGraph` from
  `Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected`
- `Main.RootedCapacity::rootedChildComponent` → `rootedChildComponent` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildComponent`
- `Main.RootedCapacity::rootedGram` → `rootedGram` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedGram`
-/
theorem rootedGram_rootedChildComponent {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (w : V → ℤ) (parent c : V)
    (hG : G.IsTree) (hpc : G.Adj parent c) :
    let C := rootedChildComponent G parent c
    letI : Fintype C := Fintype.ofFinite C
    letI : DecidableRel C.toSimpleGraph.Adj := by
      intro x y
      change Decidable ((G.deleteEdges {s(parent, c)}).Adj (x : V) (y : V))
      infer_instance
    ∀ x y : C,
      rootedGram C.toSimpleGraph (fun z : C => w (z : V)) x y =
        rootedGram G w (x : V) (y : V) := by
  sorry
```

## Proof NL

Introduce the component abbreviation and its finite/decidable instances from the formal statement, then fix `x y : C`. First obtain the component-tree hypothesis `hC : C.toSimpleGraph.IsTree` from the accepted public bridge `rootedChildComponent_isTree G parent c hG`.

Prove the key adjacency equivalence
`C.toSimpleGraph.Adj x y ↔ G.Adj (x : V) (y : V)`.
The forward implication is immediate by unfolding the induced component graph and applying the forward direction of `SimpleGraph.deleteEdges_adj`. For the reverse implication, `SimpleGraph.deleteEdges_adj` reduces the goal to showing that the deleted unordered edge is not `s((x : V), (y : V))`. If equality with `s(parent, c)` held, apply `Sym2.mk_eq_mk_iff`: either `x = parent` or `y = parent` (up to swapping). Each case contradicts the accepted public bridge `rootedChildComponent_parent_not_mem G parent c hG hpc`. Hence the ambient adjacency survives inside the component.

Finally unfold `rootedGram` on both sides. Rewrite the component pairing with the accepted private basis-entry theorem `treePairing_vertexVector_vertexVector` using `hC`, and rewrite the ambient pairing with the same theorem using `hG`. The diagonal branches agree by the restricted weight definition; the off-diagonal branches agree by the adjacency equivalence just proved. Simplification of the integer-to-rational casts completes the required entrywise equality.

## Proof Formal

```lean
-- lean-constellation: managed-imports-begin
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Prelude
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Data.Sym.Sym2
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildComponent
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedGram
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.rootedChildComponent_isTree
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.rootedChildComponent_parent_not_mem
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.treePairing_vertexVector_vertexVector
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `rootedGram_rootedChildComponent`

For a finite vertex type `V` with decidable equality, a simple graph `G : SimpleGraph V`, an integer
weight function `w : V → ℤ`, vertices `parent c : V`, a tree hypothesis `hG : G.IsTree`, and an
adjacency hypothesis `hpc : G.Adj parent c`, let `C := rootedChildComponent G parent c`.  Then the
rational rooted Gram matrix of the induced child-component graph with restricted weight agrees
entrywise with the ambient rooted Gram matrix along the subtype inclusion: for all `x y : C`,
`rootedGram C.toSimpleGraph (fun z : C => w (z : V)) x y = rootedGram G w (x : V) (y : V)`.
Equivalently, it is the principal submatrix of `rootedGram G w` reindexed by `C → V`.  No
positive-definiteness, admissibility, or root-orientation hypothesis is assumed.

## Sources

- Source `solution.tex`, lines 57–62

## Statement dependencies

- `SimpleGraph.IsTree` from `Mathlib.Combinatorics.SimpleGraph.Acyclic`
- `SimpleGraph.ConnectedComponent.toSimpleGraph` from
  `Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected`
- `Main.RootedCapacity::rootedChildComponent` → `rootedChildComponent` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildComponent`
- `Main.RootedCapacity::rootedGram` → `rootedGram` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedGram`

## Proof outline

Introduce the component abbreviation and its finite/decidable instances from the formal statement,
then fix `x y : C`. First obtain the component-tree hypothesis `hC : C.toSimpleGraph.IsTree` from
the accepted public bridge `rootedChildComponent_isTree G parent c hG`.

Prove the key adjacency equivalence
`C.toSimpleGraph.Adj x y ↔ G.Adj (x : V) (y : V)`.
The forward implication is immediate by unfolding the induced component graph and applying the
forward direction of `SimpleGraph.deleteEdges_adj`. For the reverse implication,
`SimpleGraph.deleteEdges_adj` reduces the goal to showing that the deleted unordered edge is not
`s((x : V), (y : V))`. If equality with `s(parent, c)` held, apply `Sym2.mk_eq_mk_iff`: either `x =
parent` or `y = parent` (up to swapping). Each case contradicts the accepted public bridge
`rootedChildComponent_parent_not_mem G parent c hG hpc`. Hence the ambient adjacency survives inside
the component.

Finally unfold `rootedGram` on both sides. Rewrite the component pairing with the accepted private
basis-entry theorem `treePairing_vertexVector_vertexVector` using `hC`, and rewrite the ambient
pairing with the same theorem using `hG`. The diagonal branches agree by the restricted weight
definition; the off-diagonal branches agree by the adjacency equivalence just proved. Simplification
of the integer-to-rational casts completes the required entrywise equality.

## Proof sources

- Source `solution.tex`, lines 57–62

## Proof dependencies

- `SimpleGraph.ConnectedComponent.toSimpleGraph` from
  `Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected`
- `SimpleGraph.deleteEdges` from `Mathlib.Combinatorics.SimpleGraph.DeleteEdges`
- `SimpleGraph.deleteEdges_adj` from `Mathlib.Combinatorics.SimpleGraph.DeleteEdges`
- `Sym2.mk_eq_mk_iff` from `Mathlib.Data.Sym.Sym2`
- `Main.RootedCapacity::rootedChildComponent` → `rootedChildComponent` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildComponent`
- `Main.RootedCapacity::rootedChildComponent_isTree` → `rootedChildComponent_isTree` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.rootedChildComponent_isTree`
- `Main.RootedCapacity::rootedChildComponent_parent_not_mem` → `rootedChildComponent_parent_not_mem`
  from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.rootedChildComponent_parent_not_mem`
- `Main.RootedCapacity::rootedGram` → `rootedGram` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedGram`
- `Main.RootedCapacity::treePairing_vertexVector_vertexVector` →
  `treePairing_vertexVector_vertexVector` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.treePairing_vertexVector_vertexVector`
-/
theorem rootedGram_rootedChildComponent {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (w : V → ℤ) (parent c : V)
    (hG : G.IsTree) (hpc : G.Adj parent c) :
    let C := rootedChildComponent G parent c
    letI : Fintype C := Fintype.ofFinite C
    letI : DecidableRel C.toSimpleGraph.Adj := by
      intro x y
      change Decidable ((G.deleteEdges {s(parent, c)}).Adj (x : V) (y : V))
      infer_instance
    ∀ x y : C,
      rootedGram C.toSimpleGraph (fun z : C => w (z : V)) x y =
        rootedGram G w (x : V) (y : V) := by
  dsimp only
  letI : Fintype (rootedChildComponent G parent c) := Fintype.ofFinite _
  letI : DecidableRel (rootedChildComponent G parent c).toSimpleGraph.Adj := by
    intro x y
    change Decidable ((G.deleteEdges {s(parent, c)}).Adj (x : V) (y : V))
    infer_instance
  intro x y
  have hC : (rootedChildComponent G parent c).toSimpleGraph.IsTree :=
    rootedChildComponent_isTree G parent c hG
  have hadj : (rootedChildComponent G parent c).toSimpleGraph.Adj x y ↔
      G.Adj (x : V) (y : V) := by
    change (G.deleteEdges {s(parent, c)}).Adj (x : V) (y : V) ↔ G.Adj (x : V) (y : V)
    constructor
    · intro hxy
      exact (G.deleteEdges_adj.mp hxy).1
    · intro hxy
      apply G.deleteEdges_adj.mpr
      refine ⟨hxy, ?_⟩
      simp only [Set.mem_singleton_iff]
      intro hedge
      let p : V × V := ((x : V), (y : V))
      let q : V × V := (parent, c)
      have hpair_eq : s(p.1, p.2) = s(q.1, q.2) := by
        simpa [p, q] using hedge
      rcases Sym2.mk_eq_mk_iff.mp hpair_eq with hpair | hpair
      · have hxparent : (x : V) = parent := by
          simpa [p, q] using congrArg Prod.fst hpair
        exact (rootedChildComponent_parent_not_mem G parent c hG hpc x) hxparent
      · have hyparent : (y : V) = parent := by
          simpa [p, q] using congrArg Prod.snd hpair
        exact (rootedChildComponent_parent_not_mem G parent c hG hpc y) hyparent
  unfold rootedGram
  rw [treePairing_vertexVector_vertexVector _ hC,
    treePairing_vertexVector_vertexVector _ hG]
  simp [hadj]
```

## Statement dependencies

- `Mathlib:Mathlib.Combinatorics.SimpleGraph.Acyclic.SimpleGraph.IsTree`
- `Mathlib:Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected.SimpleGraph.ConnectedComponent.toSimpleGraph`
- `current repo:Main.RootedCapacity.rootedChildComponent`
- `current repo:Main.RootedCapacity.rootedGram`

## Proof dependencies

- `Mathlib:Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected.SimpleGraph.ConnectedComponent.toSimpleGraph`
- `Mathlib:Mathlib.Combinatorics.SimpleGraph.DeleteEdges.SimpleGraph.deleteEdges`
- `Mathlib:Mathlib.Combinatorics.SimpleGraph.DeleteEdges.SimpleGraph.deleteEdges_adj`
- `Mathlib:Mathlib.Data.Sym.Sym2.Sym2.mk_eq_mk_iff`
- `current repo:Main.RootedCapacity.rootedChildComponent`
- `current repo:Main.RootedCapacity.rootedChildComponent_isTree`
- `current repo:Main.RootedCapacity.rootedChildComponent_parent_not_mem`
- `current repo:Main.RootedCapacity.rootedGram`
- `current repo:Main.RootedCapacity.treePairing_vertexVector_vertexVector`

## Sources

- `solution.tex:57-62`
