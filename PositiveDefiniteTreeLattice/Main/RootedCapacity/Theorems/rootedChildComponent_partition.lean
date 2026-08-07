-- lean-constellation: managed-imports-begin
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Prelude
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Walk.Basic
import Mathlib.Combinatorics.SimpleGraph.Walk.Maps
import Mathlib.Combinatorics.SimpleGraph.Walk.Operations
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildComponent
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildren
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.rootedChildComponent_path_decomposition
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `rootedChildComponent_partition`

Let V be a finite type with decidable equality, let G be a simple graph on V with decidable
adjacency, let hG : G.IsTree, and let ρ : V. For every x : V with x ≠ ρ, there exists a unique c : V
such that

c ∈ rootedChildren G hG ρ ρ

and x belongs to the child-side connected component rootedChildComponent G ρ c. Equivalently, the
unique c is a root child for which c and x are reachable in the graph obtained by deleting the edge
{ρ, c}.

Thus the rooted child components indexed by rootedChildren G hG ρ ρ uniquely partition the nonroot
vertices, using the existing deleted-edge component representation.

## Sources

- Source `solution.tex`, lines 47–61

## Statement dependencies

- `SimpleGraph.IsTree` from `Mathlib.Combinatorics.SimpleGraph.Acyclic`
- `Main.RootedCapacity::rootedChildComponent` → `rootedChildComponent` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildComponent`
- `Main.RootedCapacity::rootedChildren` → `rootedChildren` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildren`

## Proof outline

Fix `x ≠ ρ` and let `p := (hG.existsUnique_path ρ x).choose`, with `p.IsPath`.  Use the verified
`SimpleGraph.Walk.exists_eq_cons_of_ne hx p` to write this nontrivial unique path as a first edge
`hρc : G.Adj ρ c` followed by a walk `p' : G.Walk c x`.  The one-edge walk `ρ ─c` is a simple path,
so uniqueness of tree paths identifies it with the canonical path from `ρ` to `c`.  Taking the
root-prefix walk to be `nil`, this gives `c ∈ rootedChildren G hG ρ ρ` by the definition of
`rootedChildren`.

To show `x ∈ rootedChildComponent G ρ c`, prove that the tail `p'` avoids the deleted edge `{ρ,c}`.
If it used that edge, the first edge of `p = hρc :: p'` would repeat, contradicting the nodup
property of the simple path `p`.  Map `p'` with `SimpleGraph.Walk.toDeleteEdges` to obtain
reachability from `c` to `x` in `G.deleteEdges {s(ρ,c)}`, then unfold `rootedChildComponent` and use
`SimpleGraph.ConnectedComponent.sound` to obtain the component-membership witness.

For uniqueness, suppose `c` and `d` are root children and `x` lies in both corresponding
deleted-edge components.  Package each membership as a subtype vertex and apply
`rootedChildComponent_path_decomposition` to obtain the two canonical decompositions of the same
root-to-`x` unique path, respectively through `c` and through `d`.  Each root-child membership
identifies the corresponding root-to-child prefix with its single initial edge.  Comparing the two
decompositions with uniqueness of simple tree paths forces these initial edges—and hence their child
endpoints—to agree.  Equivalently, use
`PositiveDefiniteTreeLattice.uniquePath_support_separated_by_cut` at the `c` cut to rule out a
distinct root child in the child-side tail; a distinct `d` remains on the root side after deleting
`{ρ,c}`, while its own decomposition would place it on the same canonical root-to-`x` path.
Therefore `c = d`.

This uses the existing deleted-edge component model and the proved RootedCapacity/TreePathSeparation
path boundary; it introduces no choice function, generic duplicate theorem, or hypotheses beyond
`hG` and `x ≠ ρ`.

## Proof sources

- Source `solution.tex`, lines 47–61

## Proof dependencies

- `SimpleGraph.IsTree.existsUnique_path` from `Mathlib.Combinatorics.SimpleGraph.Acyclic`
- `SimpleGraph.ConnectedComponent.sound` from
  `Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected`
- `SimpleGraph.Walk.IsPath.cons` from `Mathlib.Combinatorics.SimpleGraph.Paths`
- `SimpleGraph.Walk.IsPath.of_adj` from `Mathlib.Combinatorics.SimpleGraph.Paths`
- `SimpleGraph.Walk.isPath_iff_nil` from `Mathlib.Combinatorics.SimpleGraph.Paths`
- `SimpleGraph.Walk.Nil.eq_nil` from `Mathlib.Combinatorics.SimpleGraph.Walk.Basic`
- `SimpleGraph.Walk.edges_cons` from `Mathlib.Combinatorics.SimpleGraph.Walk.Basic`
- `SimpleGraph.Walk.exists_eq_cons_of_ne` from `Mathlib.Combinatorics.SimpleGraph.Walk.Basic`
- `SimpleGraph.Walk.toDeleteEdges` from `Mathlib.Combinatorics.SimpleGraph.Walk.Maps`
- `SimpleGraph.Walk.edges_nodup_of_support_nodup` from
  `Mathlib.Combinatorics.SimpleGraph.Walk.Operations`
- `Main.RootedCapacity::rootedChildComponent` → `rootedChildComponent` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildComponent`
- `Main.RootedCapacity::rootedChildComponent_path_decomposition` →
  `rootedChildComponent_path_decomposition` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.rootedChildComponent_path_decomposition`
- `Main.RootedCapacity::rootedChildren` → `rootedChildren` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildren`
- `Main.TreePathSeparation::uniquePath_eq_append_through_cut` →
  `PositiveDefiniteTreeLattice.uniquePath_eq_append_through_cut` from
  `PositiveDefiniteTreeLattice.Main.TreePathSeparation.Theorems.uniquePath_eq_append_through_cut`
- `Main.TreePathSeparation::uniquePath_support_separated_by_cut` →
  `PositiveDefiniteTreeLattice.uniquePath_support_separated_by_cut` from
  `PositiveDefiniteTreeLattice.Main.TreePathSeparation.Theorems.uniquePath_support_separated_by_cut`
-/
theorem rootedChildComponent_partition {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.IsTree) (ρ x : V) (hx : x ≠ ρ) :
    ∃! c : V, c ∈ rootedChildren G hG ρ ρ ∧ x ∈ rootedChildComponent G ρ c := by
  classical
  let p := (hG.existsUnique_path ρ x).choose
  have hp : p.IsPath := (hG.existsUnique_path ρ x).choose_spec.1
  obtain ⟨c, hρc, p', hp_eq⟩ := p.exists_eq_cons_of_ne hx.symm
  have hsingle : (hG.existsUnique_path ρ c).choose = SimpleGraph.Walk.cons hρc .nil := by
    apply (hG.existsUnique_path ρ c).unique
    · exact (hG.existsUnique_path ρ c).choose_spec.1
    · exact SimpleGraph.Walk.IsPath.of_adj hρc
  have hc : c ∈ rootedChildren G hG ρ ρ := by
    simp only [rootedChildren, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨hρc, .nil, SimpleGraph.Walk.IsPath.nil, ?_⟩
    simpa [SimpleGraph.Walk.concat] using hsingle
  have havoids : ∀ e, e ∈ p'.edges → e ∉ ({s(ρ, c)} : Set (Sym2 V)) := by
    intro e he hes
    rw [Set.mem_singleton_iff] at hes
    subst e
    have hnodup : (s(ρ, c) :: p'.edges).Nodup := by
      simpa [hp_eq, SimpleGraph.Walk.edges_cons] using
        SimpleGraph.Walk.edges_nodup_of_support_nodup hp.support_nodup
    exact (List.nodup_cons.mp hnodup).1 he
  have hxC : x ∈ rootedChildComponent G ρ c := by
    unfold rootedChildComponent
    change (G.deleteEdges {s(ρ, c)}).connectedComponentMk x =
      (G.deleteEdges {s(ρ, c)}).connectedComponentMk c
    exact SimpleGraph.ConnectedComponent.sound ⟨p'.toDeleteEdges {s(ρ, c)} havoids⟩ |>.symm
  refine ⟨c, ⟨hc, hxC⟩, ?_⟩
  intro d hd
  rcases hd with ⟨hdchild, hxd⟩
  let xD : rootedChildComponent G ρ d := ⟨x, hxd⟩
  have hdchild' := hdchild
  simp only [rootedChildren, Finset.mem_filter, Finset.mem_univ, true_and] at hdchild'
  obtain ⟨hρd, q, hq, hqeq⟩ := hdchild'
  have hqnil : q = .nil := (SimpleGraph.Walk.isPath_iff_nil.mp hq).eq_nil
  have hsingleD : (hG.existsUnique_path ρ d).choose = SimpleGraph.Walk.cons hρd .nil := by
    calc
      (hG.existsUnique_path ρ d).choose = q.concat hρd := hqeq
      _ = SimpleGraph.Walk.cons hρd .nil := by simp [hqnil, SimpleGraph.Walk.concat]
  have hpdec : p = SimpleGraph.Walk.cons hρd (hG.existsUnique_path d x).choose := by
    rw [show p = (hG.existsUnique_path ρ x).choose from rfl]
    rw [rootedChildComponent_path_decomposition G hG ρ ρ d hdchild xD, hsingleD]
    simp [SimpleGraph.Walk.cons_append]
  have hcons : SimpleGraph.Walk.cons hρc p' =
      SimpleGraph.Walk.cons hρd (hG.existsUnique_path d x).choose := by
    rw [← hp_eq]
    exact hpdec
  exact (SimpleGraph.Walk.cons.inj hcons).1.symm
