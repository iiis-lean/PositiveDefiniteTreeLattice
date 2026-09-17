[← Public API](../PUBLIC_API.md) · [Public boundaries](../PUBLIC_BOUNDARIES.md) · [Complete graph](../DECLARATION_GRAPH.md)

# `sumNeighborContributionRootedChildComponent`

An ordered ambient neighbor sum on a rooted child component splits into its root boundary and local neighbor sums.

- Kind: `theorem`
- Node: `Main.RootedEstimates`
- Module: `PositiveDefiniteTreeLattice.Main.RootedEstimates.Theorems.sumNeighborContributionRootedChildComponent`
- State: `proved`
- Revision status: `committed`
- Repository completion: `graph_proved`
- Compatibility `formal_code`: final proof projection

## Statement NL

Let `G` be a finite tree with root `rho`, let `c` belong to `rootedChildren G hG rho rho`, and let `uC : rootedChildComponent G rho c`.  For every commutative additive target `A` and every ambient ordered-neighbor contribution `Phi : V → V → A`, the ambient neighbor sum at the ambient vertex represented by `uC` is

`∑ v ∈ G.neighborFinset (↑uC), Phi (↑uC) v = (if (↑uC : V) = c then Phi (↑uC) rho else 0) + ∑ vC ∈ (rootedChildComponent G rho c).toSimpleGraph.neighborFinset uC, Phi (↑uC) (↑vC)`.

Thus the only ambient neighbor of a component vertex that is not a component-graph neighbor is the boundary root `rho`, and it occurs exactly when that vertex is the child root `c`.  Both sums retain the ordered endpoint representation: subtype vertices on the right are coerced to their ambient endpoints before applying `Phi`.

## Statement Formal

```lean
-- lean-constellation: managed-imports-begin
import PositiveDefiniteTreeLattice.Main.RootedEstimates.Prelude
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Finite
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `sumNeighborContributionRootedChildComponent`

Let `G` be a finite tree with root `rho`, let `c` belong to `rootedChildren G hG rho rho`, and let
`uC : rootedChildComponent G rho c`.  For every commutative additive target `A` and every ambient
ordered-neighbor contribution `Phi : V → V → A`, the ambient neighbor sum at the ambient vertex
represented by `uC` is

`∑ v ∈ G.neighborFinset (↑uC), Phi (↑uC) v = (if (↑uC : V) = c then Phi (↑uC) rho else 0) + ∑ vC ∈
(rootedChildComponent G rho c).toSimpleGraph.neighborFinset uC, Phi (↑uC) (↑vC)`.

Thus the only ambient neighbor of a component vertex that is not a component-graph neighbor is the
boundary root `rho`, and it occurs exactly when that vertex is the child root `c`.  Both sums retain
the ordered endpoint representation: subtype vertices on the right are coerced to their ambient
endpoints before applying `Phi`.

## Sources

- Source `solution.tex`, lines 102–110

## Statement dependencies

- `SimpleGraph.ConnectedComponent.toSimpleGraph` from
  `Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected`
- `SimpleGraph.neighborFinset` from `Mathlib.Combinatorics.SimpleGraph.Finite`
- `Main.RootedCapacity::rootedChildComponent` → `rootedChildComponent` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildComponent`
- `Main.RootedCapacity::rootedChildren` → `rootedChildren` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildren`
-/
theorem sumNeighborContributionRootedChildComponent {V A : Type*} [Fintype V] [DecidableEq V]
    [AddCommMonoid A] (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.IsTree) (rho c : V)
    (hc : c ∈ rootedChildren G hG rho rho) (uC : rootedChildComponent G rho c)
    (Phi : V → V → A) :
    let C := rootedChildComponent G rho c
    letI : Fintype C := Fintype.ofFinite C
    letI : DecidableEq C := Classical.decEq C
    letI : DecidableRel C.toSimpleGraph.Adj := by
      intro u v
      change Decidable ((G.deleteEdges {s(rho, c)}).Adj (u : V) (v : V))
      infer_instance
    ∑ v ∈ G.neighborFinset (uC : V), Phi (uC : V) v =
      (if (uC : V) = c then Phi (uC : V) rho else 0) +
        ∑ vC ∈ C.toSimpleGraph.neighborFinset uC, Phi (uC : V) (vC : V) := by
  sorry
```

## Proof NL

Work classically and introduce the local abbreviation C := rootedChildComponent G rho c together with the Fintype/decidable instances already present in the statement. From hc, obtain the root-child adjacency G.Adj rho c; rootedChildComponent_parent_not_mem then gives (uC : V) ≠ rho.

Rewrite both neighbor finsets with SimpleGraph.neighborFinset_eq_filter. Reindex the ambient filtered sum with Finset.sum_bij, using PositiveDefiniteTreeLattice.rootedEdgeClassification G hG rho (uC : V) v for every ambient neighbor v. The impossible first root alternative is excluded by uC ≠ rho. In the second root alternative, v = rho; compare the child supplied by that alternative with c via the uniqueness in rootedChildComponent_partition (the two component memberships are the membership of uC and the canonical child-root membership), obtaining exactly (uC : V) = c. This is the if boundary summand.

For the internal alternative, use its unique component index and again apply partition uniqueness to identify that index with c. Its subtype endpoints then identify the ambient neighbor with a local neighbor of uC. The converse local-to-ambient direction is obtained from SimpleGraph.ConnectedComponent.toSimpleGraph_adj for the deleted-edge graph, followed by monotonicity from deleted adjacency to G.Adj. Thus the reindexed terms are precisely the local ordered-neighbor sum, and additive finite-sum algebra yields the displayed conditional boundary term plus that local sum. This preserves the ordered, hence double-counted, neighbor representation of b_0010 lines 102–110.

## Proof Formal

```lean
-- lean-constellation: managed-imports-begin
import PositiveDefiniteTreeLattice.Main.RootedEstimates.Prelude
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Combinatorics.SimpleGraph.Finite
import PositiveDefiniteTreeLattice.Main.RootedEstimates.Theorems.sumComponentNeighborEqSumAmbientFiltered
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `sumNeighborContributionRootedChildComponent`

Let `G` be a finite tree with root `rho`, let `c` belong to `rootedChildren G hG rho rho`, and let
`uC : rootedChildComponent G rho c`.  For every commutative additive target `A` and every ambient
ordered-neighbor contribution `Phi : V → V → A`, the ambient neighbor sum at the ambient vertex
represented by `uC` is

`∑ v ∈ G.neighborFinset (↑uC), Phi (↑uC) v = (if (↑uC : V) = c then Phi (↑uC) rho else 0) + ∑ vC ∈
(rootedChildComponent G rho c).toSimpleGraph.neighborFinset uC, Phi (↑uC) (↑vC)`.

Thus the only ambient neighbor of a component vertex that is not a component-graph neighbor is the
boundary root `rho`, and it occurs exactly when that vertex is the child root `c`.  Both sums retain
the ordered endpoint representation: subtype vertices on the right are coerced to their ambient
endpoints before applying `Phi`.

## Sources

- Source `solution.tex`, lines 102–110

## Statement dependencies

- `SimpleGraph.ConnectedComponent.toSimpleGraph` from
  `Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected`
- `SimpleGraph.neighborFinset` from `Mathlib.Combinatorics.SimpleGraph.Finite`
- `Main.RootedCapacity::rootedChildComponent` → `rootedChildComponent` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildComponent`
- `Main.RootedCapacity::rootedChildren` → `rootedChildren` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildren`

## Proof outline

Work classically and introduce the local abbreviation C := rootedChildComponent G rho c together
with the Fintype/decidable instances already present in the statement. From hc, obtain the
root-child adjacency G.Adj rho c; rootedChildComponent_parent_not_mem then gives (uC : V) ≠ rho.

Rewrite both neighbor finsets with SimpleGraph.neighborFinset_eq_filter. Reindex the ambient
filtered sum with Finset.sum_bij, using PositiveDefiniteTreeLattice.rootedEdgeClassification G hG
rho (uC : V) v for every ambient neighbor v. The impossible first root alternative is excluded by uC
≠ rho. In the second root alternative, v = rho; compare the child supplied by that alternative with
c via the uniqueness in rootedChildComponent_partition (the two component memberships are the
membership of uC and the canonical child-root membership), obtaining exactly (uC : V) = c. This is
the if boundary summand.

For the internal alternative, use its unique component index and again apply partition uniqueness to
identify that index with c. Its subtype endpoints then identify the ambient neighbor with a local
neighbor of uC. The converse local-to-ambient direction is obtained from
SimpleGraph.ConnectedComponent.toSimpleGraph_adj for the deleted-edge graph, followed by
monotonicity from deleted adjacency to G.Adj. Thus the reindexed terms are precisely the local
ordered-neighbor sum, and additive finite-sum algebra yields the displayed conditional boundary term
plus that local sum. This preserves the ordered, hence double-counted, neighbor representation of
b_0010 lines 102–110.

## Proof sources

- Source `solution.tex`, lines 102–110

## Proof dependencies

- `Finset.add_sum_erase` from `Mathlib.Algebra.BigOperators.Group.Finset.Basic`
- `Finset.sum_bij` from `Mathlib.Algebra.BigOperators.Group.Finset.Defs`
- `SimpleGraph.ConnectedComponent.toSimpleGraph_adj` from
  `Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected`
- `SimpleGraph.deleteEdges_adj` from `Mathlib.Combinatorics.SimpleGraph.DeleteEdges`
- `SimpleGraph.neighborFinset_eq_filter` from `Mathlib.Combinatorics.SimpleGraph.Finite`
- `Main.RootedCapacity::rootedChildComponent_parent_not_mem` → `rootedChildComponent_parent_not_mem`
  from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.rootedChildComponent_parent_not_mem`
- `Main.RootedCapacity::rootedChildComponent_partition` → `rootedChildComponent_partition` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.rootedChildComponent_partition`
- `Main.RootedCapacity::rootedEdgeClassification` →
  `PositiveDefiniteTreeLattice.rootedEdgeClassification` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.rootedEdgeClassification`
- `Main.RootedEstimates::sumComponentNeighborEqSumAmbientFiltered` →
  `sumComponentNeighborEqSumAmbientFiltered` from `PositiveDefiniteTreeLattice.Main.RootedEstimates.
  Theorems.sumComponentNeighborEqSumAmbientFiltered`
-/
theorem sumNeighborContributionRootedChildComponent {V A : Type*} [Fintype V] [DecidableEq V]
    [AddCommMonoid A] (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.IsTree) (rho c : V)
    (hc : c ∈ rootedChildren G hG rho rho) (uC : rootedChildComponent G rho c)
    (Phi : V → V → A) :
    let C := rootedChildComponent G rho c
    letI : Fintype C := Fintype.ofFinite C
    letI : DecidableEq C := Classical.decEq C
    letI : DecidableRel C.toSimpleGraph.Adj := by
      intro u v
      change Decidable ((G.deleteEdges {s(rho, c)}).Adj (u : V) (v : V))
      infer_instance
    ∑ v ∈ G.neighborFinset (uC : V), Phi (uC : V) v =
      (if (uC : V) = c then Phi (uC : V) rho else 0) +
        ∑ vC ∈ C.toSimpleGraph.neighborFinset uC, Phi (uC : V) (vC : V) := by
  classical
  letI : Fintype (rootedChildComponent G rho c) := Fintype.ofFinite _
  letI : DecidableEq (rootedChildComponent G rho c) := Classical.decEq _
  letI : DecidableRel (rootedChildComponent G rho c).toSimpleGraph.Adj := by
    intro u v
    change Decidable ((G.deleteEdges {s(rho, c)}).Adj (u : V) (v : V))
    infer_instance
  have hrc : G.Adj rho c := by
    rw [rootedChildren] at hc
    exact (Finset.mem_filter.mp hc).2.1
  have hu_ne : (uC : V) ≠ rho :=
    rootedChildComponent_parent_not_mem G rho c hG hrc uC
  have hfilter :
      (G.neighborFinset (uC : V)).erase rho =
        (G.neighborFinset (uC : V)).filter
          (fun v => v ∈ rootedChildComponent G rho c) := by
    rw [SimpleGraph.neighborFinset_eq_filter]
    ext v
    simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hv_ne, huv⟩
      rcases (PositiveDefiniteTreeLattice.rootedEdgeClassification G hG rho
        (uC : V) v).mp huv with hroot | hroot | hcomponent
      · exact (hu_ne hroot.1).elim
      · exact (hv_ne hroot.1).elim
      · rcases hcomponent with ⟨d, ⟨hd, uD, vD, huD, hvD, hlocal⟩, _⟩
        have huD_mem : (uC : V) ∈ rootedChildComponent G rho d := by
          rw [← huD]
          exact uD.property
        have hdc : d = c :=
          (rootedChildComponent_partition G hG rho (uC : V) hu_ne).unique
            ⟨hd, huD_mem⟩ ⟨hc, uC.property⟩
        have hvC : v ∈ rootedChildComponent G rho c := by
          rw [← hdc, ← hvD]
          exact vD.property
        exact ⟨huv, hvC⟩
    · rintro ⟨huv, hvC⟩
      refine ⟨?_, huv⟩
      intro hvrho
      subst v
      exact (rootedChildComponent_parent_not_mem G rho c hG hrc ⟨rho, hvC⟩) rfl
  have hrho_mem : rho ∈ G.neighborFinset (uC : V) ↔ (uC : V) = c := by
    rw [SimpleGraph.neighborFinset_eq_filter]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hurho
      rcases (PositiveDefiniteTreeLattice.rootedEdgeClassification G hG rho
        (uC : V) rho).mp hurho with hroot | hroot | hcomponent
      · exact (hu_ne hroot.1).elim
      · have huu : (uC : V) ∈ rootedChildComponent G rho (uC : V) := by
          unfold rootedChildComponent
          exact SimpleGraph.ConnectedComponent.connectedComponentMk_mem
        exact (rootedChildComponent_partition G hG rho (uC : V) hu_ne).unique
          ⟨hroot.2, huu⟩ ⟨hc, uC.property⟩
      · rcases hcomponent with ⟨d, ⟨hd, uD, vD, huD, hvD, hlocal⟩, _⟩
        have hrd : G.Adj rho d := by
          rw [rootedChildren] at hd
          exact (Finset.mem_filter.mp hd).2.1
        exact False.elim ((rootedChildComponent_parent_not_mem G rho d hG hrd vD) hvD)
    · intro huc
      rw [huc]
      exact hrc.symm
  have hdeleted_filter :
      (G.neighborFinset (uC : V)).filter
          (fun v => v ∈ rootedChildComponent G rho c) =
        ((G.deleteEdges {s(rho, c)}).neighborFinset (uC : V)).filter
          (fun v => v ∈ rootedChildComponent G rho c) := by
    rw [SimpleGraph.neighborFinset_eq_filter,
      SimpleGraph.neighborFinset_eq_filter]
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨huv, hvC⟩
      rw [SimpleGraph.deleteEdges_adj]
      refine ⟨⟨huv, ?_⟩, hvC⟩
      intro h
      rw [Set.mem_singleton_iff] at h
      rcases Sym2.eq_iff.mp h with h | h
      · exact hu_ne h.1
      · exact (rootedChildComponent_parent_not_mem G rho c hG hrc ⟨v, hvC⟩) h.2
    · rintro ⟨huv, hvC⟩
      exact ⟨(SimpleGraph.deleteEdges_adj.mp huv).1, hvC⟩
  have hlocal := sumComponentNeighborEqSumAmbientFiltered
    (G.deleteEdges {s(rho, c)}) (rootedChildComponent G rho c) uC (Phi (uC : V))
  have hlocal' :
      ∑ vC ∈ (rootedChildComponent G rho c).toSimpleGraph.neighborFinset uC,
        Phi (uC : V) (vC : V) =
        ∑ v ∈ (G.neighborFinset (uC : V)).filter
          (fun v => v ∈ rootedChildComponent G rho c), Phi (uC : V) v := by
    calc
      ∑ vC ∈ (rootedChildComponent G rho c).toSimpleGraph.neighborFinset uC,
          Phi (uC : V) (vC : V) =
          ∑ v ∈ ((G.deleteEdges {s(rho, c)}).neighborFinset (uC : V)).filter
            (fun v => v ∈ rootedChildComponent G rho c), Phi (uC : V) v := hlocal
      _ = ∑ v ∈ (G.neighborFinset (uC : V)).filter
            (fun v => v ∈ rootedChildComponent G rho c), Phi (uC : V) v := by
        rw [hdeleted_filter]
  by_cases huc : (uC : V) = c
  · have hrho : rho ∈ G.neighborFinset (uC : V) := hrho_mem.mpr huc
    calc
      ∑ v ∈ G.neighborFinset (uC : V), Phi (uC : V) v =
          Phi (uC : V) rho +
            ∑ v ∈ (G.neighborFinset (uC : V)).erase rho, Phi (uC : V) v :=
        (Finset.add_sum_erase (G.neighborFinset (uC : V)) (Phi (uC : V)) hrho).symm
      _ = Phi (uC : V) rho +
            ∑ v ∈ (G.neighborFinset (uC : V)).filter
              (fun v => v ∈ rootedChildComponent G rho c), Phi (uC : V) v := by
        rw [hfilter]
      _ = (if (uC : V) = c then Phi (uC : V) rho else 0) +
            ∑ vC ∈ (rootedChildComponent G rho c).toSimpleGraph.neighborFinset uC,
              Phi (uC : V) (vC : V) := by
        rw [← hlocal']
        simp [huc]
  · have hrho : rho ∉ G.neighborFinset (uC : V) := by
      intro hrho
      exact huc (hrho_mem.mp hrho)
    have hneigh : G.neighborFinset (uC : V) =
        (G.neighborFinset (uC : V)).filter
          (fun v => v ∈ rootedChildComponent G rho c) := by
      calc
        G.neighborFinset (uC : V) = (G.neighborFinset (uC : V)).erase rho :=
          (Finset.erase_eq_of_notMem hrho).symm
        _ = (G.neighborFinset (uC : V)).filter
              (fun v => v ∈ rootedChildComponent G rho c) := hfilter
    calc
      ∑ v ∈ G.neighborFinset (uC : V), Phi (uC : V) v =
          ∑ v ∈ (G.neighborFinset (uC : V)).filter
            (fun v => v ∈ rootedChildComponent G rho c), Phi (uC : V) v := by
        exact congrArg (fun s : Finset V => ∑ v ∈ s, Phi (uC : V) v) hneigh
      _ = ∑ vC ∈ (rootedChildComponent G rho c).toSimpleGraph.neighborFinset uC,
            Phi (uC : V) (vC : V) := by
        rw [← hlocal']
      _ = (if (uC : V) = c then Phi (uC : V) rho else 0) +
            ∑ vC ∈ (rootedChildComponent G rho c).toSimpleGraph.neighborFinset uC,
              Phi (uC : V) (vC : V) := by
        simp [huc]
```

## Statement dependencies

- `Mathlib:Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected.SimpleGraph.ConnectedComponent.toSimpleGraph`
- `Mathlib:Mathlib.Combinatorics.SimpleGraph.Finite.SimpleGraph.neighborFinset`
- `current repo:Main.RootedCapacity.rootedChildComponent`
- `current repo:Main.RootedCapacity.rootedChildren`

## Proof dependencies

- `Mathlib:Mathlib.Algebra.BigOperators.Group.Finset.Basic.Finset.add_sum_erase`
- `Mathlib:Mathlib.Algebra.BigOperators.Group.Finset.Defs.Finset.sum_bij`
- `Mathlib:Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected.SimpleGraph.ConnectedComponent.toSimpleGraph_adj`
- `Mathlib:Mathlib.Combinatorics.SimpleGraph.DeleteEdges.SimpleGraph.deleteEdges_adj`
- `Mathlib:Mathlib.Combinatorics.SimpleGraph.Finite.SimpleGraph.neighborFinset_eq_filter`
- `current repo:Main.RootedCapacity.rootedChildComponent_parent_not_mem`
- `current repo:Main.RootedCapacity.rootedChildComponent_partition`
- `current repo:Main.RootedCapacity.rootedEdgeClassification`
- `current repo:Main.RootedEstimates.sumComponentNeighborEqSumAmbientFiltered`

## Sources

- `solution.tex:102-110`
