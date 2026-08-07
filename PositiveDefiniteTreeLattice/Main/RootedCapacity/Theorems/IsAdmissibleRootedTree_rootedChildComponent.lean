-- lean-constellation: managed-imports-begin
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Prelude
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.PosDef
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.IsAdmissibleRootedTree
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildComponent
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildRoot
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildren
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.rootedChildComponent_isTree
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.rootedChildCount_rootedChildComponent
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.rootedGram_rootedChildComponent
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `IsAdmissibleRootedTree_rootedChildComponent`

Let V be a finite type with decidable equality, let G be a simple graph on V with decidable
adjacency, let w : V → ℤ, and let ρ, parent, c : V. Suppose hG : G.IsTree, hc : c ∈ rootedChildren G
hG ρ parent, and hAdm : IsAdmissibleRootedTree G w ρ. Then the child-side component C :=
rootedChildComponent G parent c is admissible when regarded as the rooted weighted tree with graph
C.toSimpleGraph, restricted weight x ↦ w (x : V), and root rootedChildRoot G parent c:

IsAdmissibleRootedTree C.toSimpleGraph (fun x : C => w (x : V)) (rootedChildRoot G parent c).

Thus positive definiteness and both integer weight bounds of the ambient admissible rooted tree are
inherited by every rooted child component, without changing the deleted-edge component or its
child-root index.

## Sources

- Source `solution.tex`, lines 33–37
- Source `solution.tex`, lines 47–61

## Statement dependencies

- `SimpleGraph.IsTree` from `Mathlib.Combinatorics.SimpleGraph.Acyclic`
- `SimpleGraph.ConnectedComponent.toSimpleGraph` from
  `Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected`
- `SimpleGraph.deleteEdges` from `Mathlib.Combinatorics.SimpleGraph.DeleteEdges`
- `Main.RootedCapacity::IsAdmissibleRootedTree` → `IsAdmissibleRootedTree` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.IsAdmissibleRootedTree`
- `Main.RootedCapacity::rootedChildComponent` → `rootedChildComponent` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildComponent`
- `Main.RootedCapacity::rootedChildRoot` → `rootedChildRoot` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildRoot`
- `Main.RootedCapacity::rootedChildren` → `rootedChildren` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildren`

## Proof outline

After introducing the `let`-bound component `C`, its finite and deleted-edge adjacency instances,
unfold `IsAdmissibleRootedTree` and destruct `hAdm` into the ambient tree witness,
positive-definiteness of `rootedGram G w`, the pointwise bound `2 ≤ w y`, and the ambient
rooted-child-count bound.  Use proof irrelevance if necessary to identify the tree witness carried
by `hAdm` with the explicit `hG` that indexes `hc` and the child-count transport.

Construct the child admissibility witness with the canonical theorem `rootedChildComponent_isTree G
parent c hG`.  Extract `hpc : G.Adj parent c` from the rooted-child membership `hc` by unfolding its
`Finset.filter` predicate (while retaining `hc` for the orientation transport).  Let `e : C → V` be
the subtype coercion and prove it injective with `Subtype.ext`.  Apply `Matrix.PosDef.submatrix` to
the ambient positive-definiteness proof along `e`.  Establish, by `Matrix.ext` and
`rootedGram_rootedChildComponent G w parent c hG hpc`, that this principal submatrix is exactly
`rootedGram C.toSimpleGraph (fun x : C => w (x : V))`; rewrite by this equality to obtain the
required child positive-definiteness.  This keeps the exact rational rootedGram and restricted
integer-valued weight.

For the pointwise lower bound, specialize the ambient `2 ≤ w y` bound at the coerced vertex `(x :
V)`.  For the child-count bound, specialize the ambient count bound at `(x : V)`, rewrite its left
side using the proved theorem `rootedChildCount_rootedChildComponent G hG ρ parent c hc x`, and
conclude.  Thus no admissibility, weight, positivity, or orientation hypotheses beyond `hG`, `hc`,
and `hAdm` are introduced, and the result remains the canonical deleted-edge component rooted at
`rootedChildRoot G parent c`.

## Proof sources

- Source `solution.tex`, lines 33–37
- Source `solution.tex`, lines 47–61

## Proof dependencies

- `Matrix.ext` from `Mathlib.LinearAlgebra.Matrix.Defs`
- `Matrix.PosDef.submatrix` from `Mathlib.LinearAlgebra.Matrix.PosDef`
- `Main.RootedCapacity::IsAdmissibleRootedTree` → `IsAdmissibleRootedTree` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.IsAdmissibleRootedTree`
- `Main.RootedCapacity::rootedChildComponent_isTree` → `rootedChildComponent_isTree` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.rootedChildComponent_isTree`
- `Main.RootedCapacity::rootedChildCount_rootedChildComponent` →
  `rootedChildCount_rootedChildComponent` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.rootedChildCount_rootedChildComponent`
- `Main.RootedCapacity::rootedChildren` → `rootedChildren` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildren`
- `Main.RootedCapacity::rootedGram_rootedChildComponent` → `rootedGram_rootedChildComponent` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.rootedGram_rootedChildComponent`
-/
theorem IsAdmissibleRootedTree_rootedChildComponent {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (w : V → ℤ) (ρ parent c : V)
    (hG : G.IsTree) (hc : c ∈ rootedChildren G hG ρ parent)
    (hAdm : IsAdmissibleRootedTree G w ρ) :
    let C := rootedChildComponent G parent c
    letI : Fintype C := Fintype.ofFinite C
    letI : DecidableRel C.toSimpleGraph.Adj := by
      intro x y
      change Decidable ((G.deleteEdges {s(parent, c)}).Adj (x : V) (y : V))
      infer_instance
    IsAdmissibleRootedTree C.toSimpleGraph (fun x : C => w (x : V))
      (rootedChildRoot G parent c) := by
  classical
  dsimp only
  letI : Fintype (rootedChildComponent G parent c) := Fintype.ofFinite _
  letI : DecidableRel (rootedChildComponent G parent c).toSimpleGraph.Adj := by
    intro x y
    change Decidable ((G.deleteEdges {s(parent, c)}).Adj (x : V) (y : V))
    infer_instance
  obtain ⟨hG', hpos, hweight, hcount⟩ := hAdm
  have hhG : hG' = hG := Subsingleton.elim _ _
  subst hG'
  have hc' := hc
  simp only [rootedChildren, Finset.mem_filter, Finset.mem_univ, true_and] at hc'
  obtain ⟨hpc, -, -, -⟩ := hc'
  refine ⟨rootedChildComponent_isTree G parent c hG, ?_, ?_, ?_⟩
  · let e : rootedChildComponent G parent c → V := fun x => (x : V)
    have he : Function.Injective e := by
      intro x y hxy
      exact Subtype.ext hxy
    have hGram :
        rootedGram (rootedChildComponent G parent c).toSimpleGraph
            (fun x : rootedChildComponent G parent c => w (x : V)) =
          (rootedGram G w).submatrix e e := by
      apply Matrix.ext
      intro x y
      simpa only [Matrix.submatrix_apply, e] using
        (rootedGram_rootedChildComponent G w parent c hG hpc x y)
    rw [hGram]
    exact hpos.submatrix he
  · intro x
    exact hweight (x : V)
  · intro x
    rw [rootedChildCount_rootedChildComponent G hG ρ parent c hc x]
    exact hcount (x : V)
