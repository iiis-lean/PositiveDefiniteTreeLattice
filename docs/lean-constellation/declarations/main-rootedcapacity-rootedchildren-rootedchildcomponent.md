[← Public API](../PUBLIC_API.md) · [Public boundaries](../PUBLIC_BOUNDARIES.md) · [Complete graph](../DECLARATION_GRAPH.md)

# `rootedChildren_rootedChildComponent`

Local rooted children in a child component map exactly to the ambient rooted children.

- Kind: `theorem`
- Node: `Main.RootedCapacity`
- Module: `PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.rootedChildren_rootedChildComponent`
- State: `proved`
- Revision status: `committed`
- Repository completion: `graph_proved`
- Compatibility `formal_code`: final proof projection

## Statement NL

For a finite vertex type `V` with decidable equality, a simple graph `G : SimpleGraph V`, a tree proof `hG : G.IsTree`, an ambient root `ρ : V`, vertices `parent c : V`, and a hypothesis `hc : c ∈ rootedChildren G hG ρ parent`, let `C := rootedChildComponent G parent c` and let `e : C ↪ V` be the explicit subtype inclusion `x ↦ (x : V)`.  Then, for every `x : C`, mapping the component rooted-children finset along `e` gives exactly the ambient rooted-children finset: `(rootedChildren C.toSimpleGraph (rootedChildComponent_isTree G parent c hG) (rootedChildRoot G parent c) x).map e = rootedChildren G hG ρ (x : V)`.  No weight or admissibility hypothesis is assumed, and the conclusion is equality of finsets rather than only equality of cardinalities.

## Statement Formal

```lean
-- lean-constellation: managed-imports-begin
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Prelude
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Finset.Image
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildComponent
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildRoot
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildren
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.rootedChildComponent_isTree
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `rootedChildren_rootedChildComponent`

For a finite vertex type `V` with decidable equality, a simple graph `G : SimpleGraph V`, a tree
proof `hG : G.IsTree`, an ambient root `ρ : V`, vertices `parent c : V`, and a hypothesis `hc : c ∈
rootedChildren G hG ρ parent`, let `C := rootedChildComponent G parent c` and let `e : C ↪ V` be the
explicit subtype inclusion `x ↦ (x : V)`.  Then, for every `x : C`, mapping the component
rooted-children finset along `e` gives exactly the ambient rooted-children finset: `(rootedChildren
C.toSimpleGraph (rootedChildComponent_isTree G parent c hG) (rootedChildRoot G parent c) x).map e =
rootedChildren G hG ρ (x : V)`.  No weight or admissibility hypothesis is assumed, and the
conclusion is equality of finsets rather than only equality of cardinalities.

## Sources

- Source `solution.tex`, lines 48–61

## Statement dependencies

- `SimpleGraph.IsTree` from `Mathlib.Combinatorics.SimpleGraph.Acyclic`
- `SimpleGraph.ConnectedComponent.toSimpleGraph` from
  `Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected`
- `Finset.map` from `Mathlib.Data.Finset.Image`
- `Main.RootedCapacity::rootedChildComponent` → `rootedChildComponent` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildComponent`
- `Main.RootedCapacity::rootedChildComponent_isTree` → `rootedChildComponent_isTree` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.rootedChildComponent_isTree`
- `Main.RootedCapacity::rootedChildRoot` → `rootedChildRoot` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildRoot`
- `Main.RootedCapacity::rootedChildren` → `rootedChildren` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildren`
-/
theorem rootedChildren_rootedChildComponent {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.IsTree) (ρ parent c : V)
    (hc : c ∈ rootedChildren G hG ρ parent) :
    let C := rootedChildComponent G parent c
    letI : Fintype C := Fintype.ofFinite C
    letI : DecidableRel C.toSimpleGraph.Adj := by
      intro u v
      change Decidable ((G.deleteEdges {s(parent, c)}).Adj (u : V) (v : V))
      infer_instance
    let e : C ↪ V :=
      { toFun := fun x => (x : V)
        inj' := by
          intro x y hxy
          exact Subtype.ext hxy }
    ∀ x : C,
      (rootedChildren C.toSimpleGraph (rootedChildComponent_isTree G parent c hG)
          (rootedChildRoot G parent c) x).map e =
        rootedChildren G hG ρ (x : V) := by
  sorry
```

## Proof NL

Introduce the component abbreviation, its instances, and the explicit inclusion embedding `e : C ↪ V`. For each `x : C`, apply `Finset.ext` and unfold `Finset.mem_map` and the definition of `rootedChildren`; membership on the left is an existential local child `z : C` with its coercion equal to the ambient test vertex.

For the forward implication, take a local child `z` of `x`. Its component-path witness from the canonical root `rootedChildRoot G parent c` to `x`, followed by the local edge to `z`, maps through `C.toSimpleGraph_hom` to a walk in the cut graph and hence in `G`. The hypothesis `hc` supplies the ambient rooted orientation of the deleted edge, so concatenate the unique ambient root-to-`c` path with this mapped component path. Use `hG.existsUnique_path` to identify the resulting ambient root-to-`z` path with the chosen one in `rootedChildren`; this gives that `(z : V)` is an ambient child of `(x : V)`.

For the reverse implication, take an ambient child `z` of `(x : V)`. The ambient child path and the cut-component path from `c` to `x` identify, by uniqueness in `hG`, the orientation of the edge `x-z`. In particular `z ≠ parent`: otherwise the ambient root path would return across the parent-child cut after reaching the child-side component, contradicting the simple/unique tree path. Since `x ≠ parent` by `rootedChildComponent_parent_not_mem`, this edge is not the deleted unordered edge. Rewrite with `SimpleGraph.deleteEdges_adj`; the edge therefore belongs to the cut graph. Component closure under cut-graph adjacency puts `z` in `C`, producing the required subtype `zC`.

Finally use the unique component-tree path from `rootedChildRoot` to `zC` and compare its ambient image with the established ambient root path using `hG.existsUnique_path`. This shows `zC` satisfies the local `rootedChildren` predicate at `x`; its image under `e` is `z`. The two membership implications close the Finset extensionality proof exactly.

## Proof Formal

```lean
-- lean-constellation: managed-imports-begin
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Prelude
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Walk.Maps
import Mathlib.Combinatorics.SimpleGraph.Walk.Operations
import Mathlib.Data.Finset.Image
import Mathlib.Data.Sym.Sym2
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildComponent
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildRoot
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildren
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.rootedChildComponent_isTree
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.rootedChildComponent_parent_not_mem
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.rootedChildComponent_path_decomposition
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `rootedChildren_rootedChildComponent`

For a finite vertex type `V` with decidable equality, a simple graph `G : SimpleGraph V`, a tree
proof `hG : G.IsTree`, an ambient root `ρ : V`, vertices `parent c : V`, and a hypothesis `hc : c ∈
rootedChildren G hG ρ parent`, let `C := rootedChildComponent G parent c` and let `e : C ↪ V` be the
explicit subtype inclusion `x ↦ (x : V)`.  Then, for every `x : C`, mapping the component
rooted-children finset along `e` gives exactly the ambient rooted-children finset: `(rootedChildren
C.toSimpleGraph (rootedChildComponent_isTree G parent c hG) (rootedChildRoot G parent c) x).map e =
rootedChildren G hG ρ (x : V)`.  No weight or admissibility hypothesis is assumed, and the
conclusion is equality of finsets rather than only equality of cardinalities.

## Sources

- Source `solution.tex`, lines 48–61

## Statement dependencies

- `SimpleGraph.IsTree` from `Mathlib.Combinatorics.SimpleGraph.Acyclic`
- `SimpleGraph.ConnectedComponent.toSimpleGraph` from
  `Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected`
- `Finset.map` from `Mathlib.Data.Finset.Image`
- `Main.RootedCapacity::rootedChildComponent` → `rootedChildComponent` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildComponent`
- `Main.RootedCapacity::rootedChildComponent_isTree` → `rootedChildComponent_isTree` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.rootedChildComponent_isTree`
- `Main.RootedCapacity::rootedChildRoot` → `rootedChildRoot` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildRoot`
- `Main.RootedCapacity::rootedChildren` → `rootedChildren` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildren`

## Proof outline

Introduce the component abbreviation, its instances, and the explicit inclusion embedding `e : C ↪
V`. For each `x : C`, apply `Finset.ext` and unfold `Finset.mem_map` and the definition of
`rootedChildren`; membership on the left is an existential local child `z : C` with its coercion
equal to the ambient test vertex.

For the forward implication, take a local child `z` of `x`. Its component-path witness from the
canonical root `rootedChildRoot G parent c` to `x`, followed by the local edge to `z`, maps through
`C.toSimpleGraph_hom` to a walk in the cut graph and hence in `G`. The hypothesis `hc` supplies the
ambient rooted orientation of the deleted edge, so concatenate the unique ambient root-to-`c` path
with this mapped component path. Use `hG.existsUnique_path` to identify the resulting ambient
root-to-`z` path with the chosen one in `rootedChildren`; this gives that `(z : V)` is an ambient
child of `(x : V)`.

For the reverse implication, take an ambient child `z` of `(x : V)`. The ambient child path and the
cut-component path from `c` to `x` identify, by uniqueness in `hG`, the orientation of the edge
`x-z`. In particular `z ≠ parent`: otherwise the ambient root path would return across the
parent-child cut after reaching the child-side component, contradicting the simple/unique tree path.
Since `x ≠ parent` by `rootedChildComponent_parent_not_mem`, this edge is not the deleted unordered
edge. Rewrite with `SimpleGraph.deleteEdges_adj`; the edge therefore belongs to the cut graph.
Component closure under cut-graph adjacency puts `z` in `C`, producing the required subtype `zC`.

Finally use the unique component-tree path from `rootedChildRoot` to `zC` and compare its ambient
image with the established ambient root path using `hG.existsUnique_path`. This shows `zC` satisfies
the local `rootedChildren` predicate at `x`; its image under `e` is `z`. The two membership
implications close the Finset extensionality proof exactly.

## Proof sources

- Source `solution.tex`, lines 48–61

## Proof dependencies

- `SimpleGraph.IsTree.existsUnique_path` from `Mathlib.Combinatorics.SimpleGraph.Acyclic`
- `SimpleGraph.isAcyclic_iff_forall_adj_isBridge` from `Mathlib.Combinatorics.SimpleGraph.Acyclic`
- `SimpleGraph.ConnectedComponent.mem_supp_of_adj_mem_supp` from
  `Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected`
- `SimpleGraph.ConnectedComponent.toSimpleGraph_adj` from
  `Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected`
- `SimpleGraph.ConnectedComponent.toSimpleGraph_hom` from
  `Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected`
- `SimpleGraph.deleteEdges_adj` from `Mathlib.Combinatorics.SimpleGraph.DeleteEdges`
- `SimpleGraph.Walk.concat_isPath_iff` from `Mathlib.Combinatorics.SimpleGraph.Paths`
- `SimpleGraph.Walk.support_map` from `Mathlib.Combinatorics.SimpleGraph.Walk.Maps`
- `SimpleGraph.Walk.support_subset_support_append_right` from
  `Mathlib.Combinatorics.SimpleGraph.Walk.Operations`
- `Finset.mem_map` from `Mathlib.Data.Finset.Image`
- `Sym2.mk_eq_mk_iff` from `Mathlib.Data.Sym.Sym2`
- `Main.RootedCapacity::rootedChildComponent` → `rootedChildComponent` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildComponent`
- `Main.RootedCapacity::rootedChildComponent_isTree` → `rootedChildComponent_isTree` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.rootedChildComponent_isTree`
- `Main.RootedCapacity::rootedChildComponent_parent_not_mem` → `rootedChildComponent_parent_not_mem`
  from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.rootedChildComponent_parent_not_mem`
- `Main.RootedCapacity::rootedChildComponent_path_decomposition` →
  `rootedChildComponent_path_decomposition` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.rootedChildComponent_path_decomposition`
- `Main.RootedCapacity::rootedChildRoot` → `rootedChildRoot` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildRoot`
- `Main.RootedCapacity::rootedChildren` → `rootedChildren` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildren`
- `Main.TreePathSeparation::reachable_childSide_of_uniquePath_concat` →
  `PositiveDefiniteTreeLattice.reachable_childSide_of_uniquePath_concat` from `PositiveDefiniteTreeL
  attice.Main.TreePathSeparation.Theorems.reachable_childSide_of_uniquePath_concat`
- `Main.TreePathSeparation::uniquePath` → `uniquePath` from
  `PositiveDefiniteTreeLattice.Main.TreePathSeparation.Defs.uniquePath`
- `Main.TreePathSeparation::uniquePath_support_separated_by_cut` →
  `PositiveDefiniteTreeLattice.uniquePath_support_separated_by_cut` from
  `PositiveDefiniteTreeLattice.Main.TreePathSeparation.Theorems.uniquePath_support_separated_by_cut`
-/
theorem rootedChildren_rootedChildComponent {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.IsTree) (ρ parent c : V)
    (hc : c ∈ rootedChildren G hG ρ parent) :
    let C := rootedChildComponent G parent c
    letI : Fintype C := Fintype.ofFinite C
    letI : DecidableRel C.toSimpleGraph.Adj := by
      intro u v
      change Decidable ((G.deleteEdges {s(parent, c)}).Adj (u : V) (v : V))
      infer_instance
    let e : C ↪ V :=
      { toFun := fun x => (x : V)
        inj' := by
          intro x y hxy
          exact Subtype.ext hxy }
    ∀ x : C,
      (rootedChildren C.toSimpleGraph (rootedChildComponent_isTree G parent c hG)
          (rootedChildRoot G parent c) x).map e =
        rootedChildren G hG ρ (x : V) := by
  classical
  dsimp
  intro x
  apply Finset.ext
  intro z
  constructor
  · intro hz
    rw [Finset.mem_map] at hz
    obtain ⟨zC, hzC, rfl⟩ := hz
    simp only [rootedChildren, Finset.mem_filter, Finset.mem_univ, true_and] at hzC ⊢
    obtain ⟨hxz, q, hq, hqeq⟩ := hzC
    let φ : (rootedChildComponent G parent c).toSimpleGraph →g G :=
      { toFun := fun u => (u : V)
        map_rel' := by
          intro u v huv
          change (G.deleteEdges {s(parent, c)}).Adj (u : V) (v : V) at huv
          exact (SimpleGraph.deleteEdges_le _) huv }
    have hφinj : Function.Injective φ := by
      intro u v huv
      change (u : V) = (v : V) at huv
      exact Subtype.ext huv
    let hxzG : G.Adj (x : V) (zC : V) := by
      simpa [φ] using φ.map_adj hxz
    have hqG : (q.map φ).IsPath := hq.map hφinj
    have hqG_eq : (q.map φ) = (hG.existsUnique_path c (x : V)).choose := by
      simpa [φ, rootedChildRoot] using
        ((hG.existsUnique_path c (x : V)).unique
          (hG.existsUnique_path c (x : V)).choose_spec.1 hqG).symm
    have hqeqG : (hG.existsUnique_path c (zC : V)).choose = (q.map φ).concat hxzG := by
      have hlocal : ((rootedChildComponent_isTree G parent c hG).existsUnique_path
          (rootedChildRoot G parent c) zC).choose = q.concat hxz := hqeq
      have hlocalG :
          ((rootedChildComponent_isTree G parent c hG).existsUnique_path
            (rootedChildRoot G parent c) zC).choose.map φ = (q.map φ).concat hxzG := by
        rw [hlocal]
        simp only [SimpleGraph.Walk.concat, SimpleGraph.Walk.map_append,
          SimpleGraph.Walk.map_cons, SimpleGraph.Walk.map_nil]
      have hpG :
          (((rootedChildComponent_isTree G parent c hG).existsUnique_path
            (rootedChildRoot G parent c) zC).choose.map φ).IsPath :=
        ((rootedChildComponent_isTree G parent c hG).existsUnique_path
          (rootedChildRoot G parent c) zC).choose_spec.1.map hφinj
      have hp_eq :
          ((rootedChildComponent_isTree G parent c hG).existsUnique_path
            (rootedChildRoot G parent c) zC).choose.map φ =
              (hG.existsUnique_path c (zC : V)).choose := by
        simpa [φ, rootedChildRoot] using
          ((hG.existsUnique_path c (zC : V)).unique
            (hG.existsUnique_path c (zC : V)).choose_spec.1 hpG).symm
      exact hp_eq.symm.trans hlocalG
    refine ⟨hxzG, (hG.existsUnique_path ρ (x : V)).choose, ?_, ?_⟩
    · exact (hG.existsUnique_path ρ (x : V)).choose_spec.1
    · rw [rootedChildComponent_path_decomposition G hG ρ parent c hc zC, hqeqG,
        rootedChildComponent_path_decomposition G hG ρ parent c hc x, ← hqG_eq,
        ← SimpleGraph.Walk.append_concat]
      congr
  · intro hz
    simp only [rootedChildren, Finset.mem_filter, Finset.mem_univ, true_and] at hz
    obtain ⟨hxz, q, hq, hqeq⟩ := hz
    obtain ⟨hpc, qparent, hqparent, hqparenteq⟩ := by
      simpa only [rootedChildren, Finset.mem_filter, Finset.mem_univ, true_and] using hc
    have hpath : (qparent.concat hpc).IsPath := by
      rw [← hqparenteq]
      exact (hG.existsUnique_path ρ c).choose_spec.1
    have havoids : ∀ e, e ∈ qparent.edges → e ∉ ({s(parent, c)} : Set (Sym2 V)) := by
      intro e he hes
      rw [Set.mem_singleton_iff] at hes
      subst e
      have hnodup : (qparent.edges.concat s(parent, c)).Nodup := by
        simpa only [SimpleGraph.Walk.edges_concat] using hpath.edges_nodup
      exact (List.nodup_concat qparent.edges s(parent, c)).mp hnodup |>.1 he
    have hroot : (G.deleteEdges {s(parent, c)}).Reachable ρ parent :=
      ⟨qparent.toDeleteEdges {s(parent, c)} havoids⟩
    have hx : (G.deleteEdges {s(parent, c)}).Reachable c (x : V) := by
      apply SimpleGraph.ConnectedComponent.reachable_of_mem_supp
      · exact SimpleGraph.ConnectedComponent.connectedComponentMk_mem
      · exact x.property
    have hconcat :
        uniquePath G hG ρ z = (uniquePath G hG ρ (x : V)).concat hxz := by
      have hq_eq : q = uniquePath G hG ρ (x : V) := by
        apply (hG.existsUnique_path ρ (x : V)).unique hq
        simpa [uniquePath] using (hG.existsUnique_path ρ (x : V)).choose_spec.1
      change (hG.existsUnique_path ρ z).choose =
        (uniquePath G hG ρ (x : V)).concat hxz
      rw [hqeq, hq_eq]
    have hcz : (G.deleteEdges {s(parent, c)}).Reachable c z :=
      PositiveDefiniteTreeLattice.reachable_childSide_of_uniquePath_concat G hG ρ parent c
        (x : V) z hpc hroot hx hxz hconcat
    let zC : rootedChildComponent G parent c := ⟨z, by
      change (G.deleteEdges {s(parent, c)}).connectedComponentMk z =
        (G.deleteEdges {s(parent, c)}).connectedComponentMk c
      exact SimpleGraph.ConnectedComponent.sound hcz |>.symm⟩
    have hbridge : ¬ (G.deleteEdges {s(parent, c)}).Reachable parent c := by
      simpa [SimpleGraph.IsBridge] using
        (SimpleGraph.isAcyclic_iff_forall_adj_isBridge.mp hG.isAcyclic hpc)
    have hnot : s((x : V), z) ∉ ({s(parent, c)} : Set (Sym2 V)) := by
      simp only [Set.mem_singleton_iff]
      intro hcut
      rcases Sym2.eq_iff.mp hcut with ⟨hxp, hzc⟩ | ⟨hxc, hzp⟩
      · exact hbridge (by simpa [hxp, hzc] using hx.symm)
      · exact hbridge (by simpa [hxc, hzp] using hcz.symm)
    have hxzC : (rootedChildComponent G parent c).toSimpleGraph.Adj x zC := by
      apply SimpleGraph.ConnectedComponent.toSimpleGraph_adj _ x.property zC.property |>.2
      exact SimpleGraph.deleteEdges_adj.mpr ⟨hxz, hnot⟩
    rw [Finset.mem_map]
    simp only [rootedChildren, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨zC, ?_, by rfl⟩
    refine ⟨hxzC, (rootedChildComponent_isTree G parent c hG).existsUnique_path
      (rootedChildRoot G parent c) x |>.choose, ?_, ?_⟩
    · exact (rootedChildComponent_isTree G parent c hG).existsUnique_path
        (rootedChildRoot G parent c) x |>.choose_spec.1
    · let φ : (rootedChildComponent G parent c).toSimpleGraph →g G :=
        { toFun := fun u => (u : V)
          map_rel' := by
            intro u v huv
            change (G.deleteEdges {s(parent, c)}).Adj (u : V) (v : V) at huv
            exact (SimpleGraph.deleteEdges_le _) huv }
      have hφinj : Function.Injective φ := by
        intro u v huv
        change (u : V) = (v : V) at huv
        exact Subtype.ext huv
      let p := (rootedChildComponent_isTree G parent c hG).existsUnique_path
        (rootedChildRoot G parent c) x |>.choose
      have hp : p.IsPath :=
        (rootedChildComponent_isTree G parent c hG).existsUnique_path
          (rootedChildRoot G parent c) x |>.choose_spec.1
      have hpG : (p.map φ).IsPath := hp.map hφinj
      have hpG_eq : p.map φ = (hG.existsUnique_path c (x : V)).choose := by
        simpa [p, φ, rootedChildRoot] using
          ((hG.existsUnique_path c (x : V)).unique
            (hG.existsUnique_path c (x : V)).choose_spec.1 hpG).symm
      have hq_eq : q = (hG.existsUnique_path ρ (x : V)).choose := by
        exact (hG.existsUnique_path ρ (x : V)).unique hq
          (hG.existsUnique_path ρ (x : V)).choose_spec.1
      have hznotq : z ∉ q.support := by
        have hzpath : (q.concat hxz).IsPath := by
          rw [← hqeq]
          exact (hG.existsUnique_path ρ z).choose_spec.1
        exact (SimpleGraph.Walk.concat_isPath_iff hxz).mp hzpath |>.2
      have hznotambient : z ∉ (hG.existsUnique_path ρ (x : V)).choose.support := by
        simpa [← hq_eq] using hznotq
      have hznotpG : z ∉ (p.map φ).support := by
        intro hzmem
        apply hznotambient
        rw [rootedChildComponent_path_decomposition G hG ρ parent c hc x]
        apply SimpleGraph.Walk.support_subset_support_append_right
        rw [← hpG_eq]
        exact hzmem
      have hznotp : zC ∉ p.support := by
        intro hzmem
        apply hznotpG
        rw [SimpleGraph.Walk.support_map]
        exact List.mem_map.mpr ⟨zC, hzmem, by simp [φ, zC]⟩
      exact (rootedChildComponent_isTree G parent c hG).existsUnique_path
        (rootedChildRoot G parent c) zC |>.unique
          ((rootedChildComponent_isTree G parent c hG).existsUnique_path
            (rootedChildRoot G parent c) zC).choose_spec.1
          (hp.concat hznotp hxzC)
```

## Statement dependencies

- `Mathlib:Mathlib.Combinatorics.SimpleGraph.Acyclic.SimpleGraph.IsTree`
- `Mathlib:Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected.SimpleGraph.ConnectedComponent.toSimpleGraph`
- `Mathlib:Mathlib.Data.Finset.Image.Finset.map`
- `current repo:Main.RootedCapacity.rootedChildComponent`
- `current repo:Main.RootedCapacity.rootedChildComponent_isTree`
- `current repo:Main.RootedCapacity.rootedChildRoot`
- `current repo:Main.RootedCapacity.rootedChildren`

## Proof dependencies

- `Mathlib:Mathlib.Combinatorics.SimpleGraph.Acyclic.SimpleGraph.IsTree.existsUnique_path`
- `Mathlib:Mathlib.Combinatorics.SimpleGraph.Acyclic.SimpleGraph.isAcyclic_iff_forall_adj_isBridge`
- `Mathlib:Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected.SimpleGraph.ConnectedComponent.mem_supp_of_adj_mem_supp`
- `Mathlib:Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected.SimpleGraph.ConnectedComponent.toSimpleGraph_adj`
- `Mathlib:Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected.SimpleGraph.ConnectedComponent.toSimpleGraph_hom`
- `Mathlib:Mathlib.Combinatorics.SimpleGraph.DeleteEdges.SimpleGraph.deleteEdges_adj`
- `Mathlib:Mathlib.Combinatorics.SimpleGraph.Paths.SimpleGraph.Walk.concat_isPath_iff`
- `Mathlib:Mathlib.Combinatorics.SimpleGraph.Walk.Maps.SimpleGraph.Walk.support_map`
- `Mathlib:Mathlib.Combinatorics.SimpleGraph.Walk.Operations.SimpleGraph.Walk.support_subset_support_append_right`
- `Mathlib:Mathlib.Data.Finset.Image.Finset.mem_map`
- `Mathlib:Mathlib.Data.Sym.Sym2.Sym2.mk_eq_mk_iff`
- `current repo:Main.RootedCapacity.rootedChildComponent`
- `current repo:Main.RootedCapacity.rootedChildComponent_isTree`
- `current repo:Main.RootedCapacity.rootedChildComponent_parent_not_mem`
- `current repo:Main.RootedCapacity.rootedChildComponent_path_decomposition`
- `current repo:Main.RootedCapacity.rootedChildRoot`
- `current repo:Main.RootedCapacity.rootedChildren`
- `current repo:Main.TreePathSeparation.reachable_childSide_of_uniquePath_concat`
- `current repo:Main.TreePathSeparation.uniquePath`
- `current repo:Main.TreePathSeparation.uniquePath_support_separated_by_cut`

## Sources

- `solution.tex:48-61`
