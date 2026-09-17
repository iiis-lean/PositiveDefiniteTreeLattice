[← Public API](../PUBLIC_API.md) · [Public boundaries](../PUBLIC_BOUNDARIES.md) · [Complete graph](../DECLARATION_GRAPH.md)

# `treePairingRootedChildDecomposition`

The integral tree pairing decomposes into the root term and rooted-child component pairings.

- Kind: `theorem`
- Node: `Main.RootedEstimates`
- Module: `PositiveDefiniteTreeLattice.Main.RootedEstimates.Theorems.treePairingRootedChildDecomposition`
- State: `proved`
- Revision status: `committed`
- Repository completion: `graph_proved`
- Compatibility `formal_code`: final proof projection

## Statement NL

Let `V` be a finite vertex type, let `G : SimpleGraph V` have decidable adjacency and a tree witness `hG : G.IsTree`, let `w : V → ℤ`, let `rho : V`, and let `x : V → ℤ`. For each `c ∈ rootedChildren G hG rho rho`, define

`C_c := rootedChildComponent G rho c`,

which is the connected-component subtype of `G.deleteEdges {s(rho, c)}` containing `c`. Let its induced child graph be

`G_c := C_c.toSimpleGraph`,

and define the restrictions `w_c : C_c → ℤ` and `x_c : C_c → ℤ` by `w_c(u) := w (u : V)` and `x_c(u) := x (u : V)`. Set

`s_c := x_c (rootedChildRoot G rho c)`.

Writing `a := x rho`, the integral pairing satisfies

`treePairing G w x x = w rho * a^2 - 2 * a * ∑ c ∈ rootedChildren G hG rho rho, s_c + ∑ c ∈ rootedChildren G hG rho rho, treePairing G_c w_c x_c x_c`.

Thus every child self-pairing is formed on the induced graph `C_c.toSimpleGraph` with the induced integer weights and the coordinate restriction, while the root coefficient is exactly `x rho`.

## Statement Formal

```lean
-- lean-constellation: managed-imports-begin
import PositiveDefiniteTreeLattice.Main.RootedEstimates.Prelude
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `treePairingRootedChildDecomposition`

Let `V` be a finite vertex type, let `G : SimpleGraph V` have decidable adjacency and a tree witness
`hG : G.IsTree`, let `w : V → ℤ`, let `rho : V`, and let `x : V → ℤ`. For each `c ∈ rootedChildren G
hG rho rho`, define

`C_c := rootedChildComponent G rho c`,

which is the connected-component subtype of `G.deleteEdges {s(rho, c)}` containing `c`. Let its
induced child graph be

`G_c := C_c.toSimpleGraph`,

and define the restrictions `w_c : C_c → ℤ` and `x_c : C_c → ℤ` by `w_c(u) := w (u : V)` and `x_c(u)
:= x (u : V)`. Set

`s_c := x_c (rootedChildRoot G rho c)`.

Writing `a := x rho`, the integral pairing satisfies

`treePairing G w x x = w rho * a^2 - 2 * a * ∑ c ∈ rootedChildren G hG rho rho, s_c + ∑ c ∈
rootedChildren G hG rho rho, treePairing G_c w_c x_c x_c`.

Thus every child self-pairing is formed on the induced graph `C_c.toSimpleGraph` with the induced
integer weights and the coordinate restriction, while the root coefficient is exactly `x rho`.

## Sources

- Source `solution.tex`, lines 102–110

## Statement dependencies

- `SimpleGraph.IsTree` from `Mathlib.Combinatorics.SimpleGraph.Acyclic`
- `SimpleGraph.ConnectedComponent.toSimpleGraph` from
  `Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected`
- `Main.LatticeFoundations::treePairingAnchor` → `PositiveDefiniteTreeLattice.treePairing` from
  `PositiveDefiniteTreeLattice.Main.LatticeFoundations.Defs.treePairingAnchor`
- `Main.RootedCapacity::rootedChildComponent` → `rootedChildComponent` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildComponent`
- `Main.RootedCapacity::rootedChildRoot` → `rootedChildRoot` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildRoot`
- `Main.RootedCapacity::rootedChildren` → `rootedChildren` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildren`
-/
theorem treePairingRootedChildDecomposition {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.IsTree) (w x : V → ℤ) (rho : V) :
    PositiveDefiniteTreeLattice.treePairing G w x x =
      w rho * (x rho) ^ 2 -
        2 * x rho * (∑ c ∈ rootedChildren G hG rho rho,
          x (rootedChildRoot G rho c)) +
        ∑ c ∈ rootedChildren G hG rho rho,
          let C := rootedChildComponent G rho c
          letI : Fintype C := Fintype.ofFinite C
          letI : DecidableEq C := Classical.decEq C
          letI : DecidableRel C.toSimpleGraph.Adj := by
            intro u v
            change Decidable ((G.deleteEdges {s(rho, c)}).Adj (u : V) (v : V))
            infer_instance
          PositiveDefiniteTreeLattice.treePairing C.toSimpleGraph (fun u => w (u : V))
            (fun u => x (u : V)) (fun u => x (u : V)) := by
  sorry
```

## Proof NL

Unfold `PositiveDefiniteTreeLattice.treePairing` through `treePairingAnchor`, and separate the summand at `rho` from the finite sum over non-root vertices. For each non-root vertex `u`, apply `rootedChildComponent_partition G hG rho u` to obtain its unique child `c`; use this uniqueness to reindex the remaining finite sum by the family of subtypes `rootedChildComponent G rho c`.

Apply both directions of `PositiveDefiniteTreeLattice.rootedEdgeClassification G hG rho u v` to every adjacency contribution. Its two root-child alternatives give exactly the boundary terms, while its unique internal-component alternative identifies every remaining edge with the induced graph on the corresponding child component. Thus the reindexed internal sums are the child `treePairing` terms. Combine the disjoint finite sums with `Finset.sum_disjiUnion`; each root-child edge contributes once from the root and once from its child root. Finish by ring normalization, yielding `w rho * (x rho)^2`, the boundary contribution `- 2 * x rho * ∑ c, x (rootedChildRoot G rho c)`, and the indicated sum of child self-pairings. This follows b_0010 lines 102–110; the edge classification is the formal partition of the source's adjacency cases.

## Proof Formal

```lean
-- lean-constellation: managed-imports-begin
import PositiveDefiniteTreeLattice.Main.RootedEstimates.Prelude
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Disjoint
import Mathlib.Data.Finset.Union
import PositiveDefiniteTreeLattice.Main.RootedEstimates.Theorems.sumNeighborContributionRootedChildComponent
import PositiveDefiniteTreeLattice.Main.RootedEstimates.Theorems.sumNonrootEqSumRootedChildComponents
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `treePairingRootedChildDecomposition`

Let `V` be a finite vertex type, let `G : SimpleGraph V` have decidable adjacency and a tree witness
`hG : G.IsTree`, let `w : V → ℤ`, let `rho : V`, and let `x : V → ℤ`. For each `c ∈ rootedChildren G
hG rho rho`, define

`C_c := rootedChildComponent G rho c`,

which is the connected-component subtype of `G.deleteEdges {s(rho, c)}` containing `c`. Let its
induced child graph be

`G_c := C_c.toSimpleGraph`,

and define the restrictions `w_c : C_c → ℤ` and `x_c : C_c → ℤ` by `w_c(u) := w (u : V)` and `x_c(u)
:= x (u : V)`. Set

`s_c := x_c (rootedChildRoot G rho c)`.

Writing `a := x rho`, the integral pairing satisfies

`treePairing G w x x = w rho * a^2 - 2 * a * ∑ c ∈ rootedChildren G hG rho rho, s_c + ∑ c ∈
rootedChildren G hG rho rho, treePairing G_c w_c x_c x_c`.

Thus every child self-pairing is formed on the induced graph `C_c.toSimpleGraph` with the induced
integer weights and the coordinate restriction, while the root coefficient is exactly `x rho`.

## Sources

- Source `solution.tex`, lines 102–110

## Statement dependencies

- `SimpleGraph.IsTree` from `Mathlib.Combinatorics.SimpleGraph.Acyclic`
- `SimpleGraph.ConnectedComponent.toSimpleGraph` from
  `Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected`
- `Main.LatticeFoundations::treePairingAnchor` → `PositiveDefiniteTreeLattice.treePairing` from
  `PositiveDefiniteTreeLattice.Main.LatticeFoundations.Defs.treePairingAnchor`
- `Main.RootedCapacity::rootedChildComponent` → `rootedChildComponent` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildComponent`
- `Main.RootedCapacity::rootedChildRoot` → `rootedChildRoot` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildRoot`
- `Main.RootedCapacity::rootedChildren` → `rootedChildren` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildren`

## Proof outline

Unfold `PositiveDefiniteTreeLattice.treePairing` through `treePairingAnchor`, and separate the
summand at `rho` from the finite sum over non-root vertices. For each non-root vertex `u`, apply
`rootedChildComponent_partition G hG rho u` to obtain its unique child `c`; use this uniqueness to
reindex the remaining finite sum by the family of subtypes `rootedChildComponent G rho c`.

Apply both directions of `PositiveDefiniteTreeLattice.rootedEdgeClassification G hG rho u v` to
every adjacency contribution. Its two root-child alternatives give exactly the boundary terms, while
its unique internal-component alternative identifies every remaining edge with the induced graph on
the corresponding child component. Thus the reindexed internal sums are the child `treePairing`
terms. Combine the disjoint finite sums with `Finset.sum_disjiUnion`; each root-child edge
contributes once from the root and once from its child root. Finish by ring normalization, yielding
`w rho * (x rho)^2`, the boundary contribution `- 2 * x rho * ∑ c, x (rootedChildRoot G rho c)`, and
the indicated sum of child self-pairings. This follows b_0010 lines 102–110; the edge classification
is the formal partition of the source's adjacency cases.

## Proof sources

- Source `solution.tex`, lines 102–110

## Proof dependencies

- `Finset.sum_congr` from `Mathlib.Algebra.BigOperators.Group.Finset.Basic`
- `Finset.sum_disjiUnion` from `Mathlib.Algebra.BigOperators.Group.Finset.Basic`
- `Finset.sum_sub_distrib` from `Mathlib.Algebra.BigOperators.Group.Finset.Defs`
- `Finset.sum_ite_eq'` from `Mathlib.Algebra.BigOperators.Group.Finset.Piecewise`
- `Finset.mul_sum` from `Mathlib.Algebra.BigOperators.Ring.Finset`
- `SimpleGraph.neighborFinset_eq_filter` from `Mathlib.Combinatorics.SimpleGraph.Finite`
- `Finset.disjoint_left` from `Mathlib.Data.Finset.Disjoint`
- `Finset.disjiUnion` from `Mathlib.Data.Finset.Union`
- `Main.LatticeFoundations::treePairingAnchor` → `PositiveDefiniteTreeLattice.treePairing` from
  `PositiveDefiniteTreeLattice.Main.LatticeFoundations.Defs.treePairingAnchor`
- `Main.RootedCapacity::rootedChildComponent_parent_not_mem` → `rootedChildComponent_parent_not_mem`
  from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.rootedChildComponent_parent_not_mem`
- `Main.RootedCapacity::rootedChildComponent_partition` → `rootedChildComponent_partition` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.rootedChildComponent_partition`
- `Main.RootedCapacity::rootedChildRoot` → `rootedChildRoot` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildRoot`
- `Main.RootedCapacity::rootedChildren` → `rootedChildren` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildren`
- `Main.RootedCapacity::rootedEdgeClassification` →
  `PositiveDefiniteTreeLattice.rootedEdgeClassification` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.rootedEdgeClassification`
- `Main.RootedEstimates::sumNeighborContributionRootedChildComponent` →
  `sumNeighborContributionRootedChildComponent` from `PositiveDefiniteTreeLattice.Main.RootedEstimat
  es.Theorems.sumNeighborContributionRootedChildComponent`
- `Main.RootedEstimates::sumNonrootEqSumRootedChildComponents` →
  `sumNonrootEqSumRootedChildComponents` from
  `PositiveDefiniteTreeLattice.Main.RootedEstimates.Theorems.sumNonrootEqSumRootedChildComponents`
-/
theorem treePairingRootedChildDecomposition {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.IsTree) (w x : V → ℤ) (rho : V) :
    PositiveDefiniteTreeLattice.treePairing G w x x =
      w rho * (x rho) ^ 2 -
        2 * x rho * (∑ c ∈ rootedChildren G hG rho rho,
          x (rootedChildRoot G rho c)) +
        ∑ c ∈ rootedChildren G hG rho rho,
          let C := rootedChildComponent G rho c
          letI : Fintype C := Fintype.ofFinite C
          letI : DecidableEq C := Classical.decEq C
          letI : DecidableRel C.toSimpleGraph.Adj := by
            intro u v
            change Decidable ((G.deleteEdges {s(rho, c)}).Adj (u : V) (v : V))
            infer_instance
          PositiveDefiniteTreeLattice.treePairing C.toSimpleGraph (fun u => w (u : V))
            (fun u => x (u : V)) (fun u => x (u : V)) := by
  classical
  let q : V → ℤ := fun u =>
    x u * (w u * x u - ∑ v ∈ G.neighborFinset u, x v)
  have hroot_child : ∀ {v : V}, v ∈ rootedChildren G hG rho rho → G.Adj rho v := by
    intro v hv
    rw [rootedChildren] at hv
    exact (Finset.mem_filter.mp hv).2.1
  have hadj_child : ∀ {v : V}, G.Adj rho v → v ∈ rootedChildren G hG rho rho := by
    intro v hv
    rcases (PositiveDefiniteTreeLattice.rootedEdgeClassification G hG rho rho v).mp hv with
      hroot | hroot | hcomponent
    · exact hroot.2
    · simpa [hroot.1] using hroot.2
    · rcases hcomponent with ⟨c, ⟨hc, uC, vC, huC, hvC, hlocal⟩, _⟩
      have hrc : G.Adj rho c := hroot_child hc
      exact False.elim ((rootedChildComponent_parent_not_mem G rho c hG hrc uC) huC)
  have hroot_fin : G.neighborFinset rho = rootedChildren G hG rho rho := by
    rw [SimpleGraph.neighborFinset_eq_filter]
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hadj_child, hroot_child⟩
  let split : Bool → Finset V := fun b =>
    if b then Finset.univ.filter (fun u => u ≠ rho) else {rho}
  have hsplit_disjoint :
      ((↑(Finset.univ : Finset Bool) : Set Bool)).PairwiseDisjoint split := by
    intro a ha b hb hab
    cases a <;> cases b <;> simp_all [split, Function.onFun, Finset.disjoint_left]
  have hsplit_cover :
      (Finset.univ : Finset Bool).disjiUnion split hsplit_disjoint = Finset.univ := by
    ext u
    by_cases hu : u = rho <;> simp [split, hu]
  have hroot_nonroot :
      (∑ u : V, q u) = q rho + ∑ u ∈ Finset.univ.filter (fun u : V => u ≠ rho), q u := by
    calc
      (∑ u : V, q u) =
          ∑ u ∈ (Finset.univ : Finset Bool).disjiUnion split hsplit_disjoint, q u := by
        rw [hsplit_cover]
      _ = ∑ b ∈ (Finset.univ : Finset Bool), ∑ u ∈ split b, q u :=
        Finset.sum_disjiUnion _ _ _
      _ = _ := by simp [split, add_comm]
  have hroot_sum :
      (∑ v ∈ rootedChildren G hG rho rho, x v) =
        ∑ c ∈ rootedChildren G hG rho rho, x (rootedChildRoot G rho c) := by
    apply Finset.sum_congr rfl
    intro c _
    simp [rootedChildRoot]
  have hroot_mul :
      x rho * (∑ c ∈ rootedChildren G hG rho rho, x (rootedChildRoot G rho c)) =
        ∑ c ∈ rootedChildren G hG rho rho, x rho * x (rootedChildRoot G rho c) :=
    Finset.mul_sum _ _ _
  have hcomponent : ∀ (c : V) (hc : c ∈ rootedChildren G hG rho rho),
      let C := rootedChildComponent G rho c
      letI : Fintype C := Fintype.ofFinite C
      letI : DecidableEq C := Classical.decEq C
      letI : DecidableRel C.toSimpleGraph.Adj := by
        intro u v
        change Decidable ((G.deleteEdges {s(rho, c)}).Adj (u : V) (v : V))
        infer_instance
      (∑ uC : C, q (uC : V)) =
        PositiveDefiniteTreeLattice.treePairing
          C.toSimpleGraph (fun u => w (u : V))
          (fun u => x (u : V)) (fun u => x (u : V)) -
          x rho * x (rootedChildRoot G rho c) := by
    intro c hc
    let C := rootedChildComponent G rho c
    letI : Fintype C := Fintype.ofFinite C
    letI : DecidableEq C := Classical.decEq C
    letI : DecidableRel C.toSimpleGraph.Adj := by
      intro u v
      change Decidable ((G.deleteEdges {s(rho, c)}).Adj (u : V) (v : V))
      infer_instance
    have hneigh : ∀ uC : C,
        (∑ v ∈ G.neighborFinset (uC : V), x v) =
          (if (uC : V) = c then x rho else 0) +
            ∑ vC ∈ C.toSimpleGraph.neighborFinset uC,
              x (vC : V) := by
      intro uC
      exact sumNeighborContributionRootedChildComponent G hG rho c hc uC (fun _ v => x v)
    have hboundary :
        (∑ uC : C,
          x (uC : V) * (if (uC : V) = c then x rho else 0)) =
          x rho * x (rootedChildRoot G rho c) := by
      rw [show (fun uC : C =>
          x (uC : V) * (if (uC : V) = c then x rho else 0)) =
          (fun uC : C =>
            if uC = rootedChildRoot G rho c then
              x rho * x (rootedChildRoot G rho c) else 0) by
          funext uC
          by_cases huc : uC = rootedChildRoot G rho c
          · subst uC
            simpa [rootedChildRoot] using (mul_comm (x c) (x rho))
          · have hval : (uC : V) ≠ c := by
              intro hval
              apply huc
              apply Subtype.ext
              exact hval.trans rfl.symm
            simp [huc, hval]]
      rw [Finset.sum_ite_eq']
      simp
    unfold q
    unfold PositiveDefiniteTreeLattice.treePairing
    calc
      ∑ uC : C,
          x (uC : V) *
            (w (uC : V) * x (uC : V) -
              ∑ v ∈ G.neighborFinset (uC : V), x v) =
          ∑ uC : C,
            x (uC : V) *
              (w (uC : V) * x (uC : V) -
                ((if (uC : V) = c then x rho else 0) +
                  ∑ vC ∈ C.toSimpleGraph.neighborFinset uC,
                    x (vC : V))) := by
        apply Finset.sum_congr rfl
        intro uC _
        rw [hneigh uC]
      _ =
          ∑ uC : C,
            (x (uC : V) *
              (w (uC : V) * x (uC : V) -
                ∑ vC ∈ C.toSimpleGraph.neighborFinset uC,
                  x (vC : V)) -
              x (uC : V) * (if (uC : V) = c then x rho else 0)) := by
        apply Finset.sum_congr rfl
        intro uC _
        ring
      _ = (∑ uC : C,
            x (uC : V) *
              (w (uC : V) * x (uC : V) -
                ∑ vC ∈ C.toSimpleGraph.neighborFinset uC,
                  x (vC : V))) -
            ∑ uC : C,
              x (uC : V) * (if (uC : V) = c then x rho else 0) :=
        by rw [Finset.sum_sub_distrib]
      _ = _ := by rw [hboundary]
  unfold PositiveDefiniteTreeLattice.treePairing
  rw [hroot_nonroot, sumNonrootEqSumRootedChildComponents G hG rho q]
  simp only [q]
  rw [hroot_fin]
  rw [Finset.sum_congr rfl (fun c hc => hcomponent c hc)]
  simp only [PositiveDefiniteTreeLattice.treePairing, Finset.sum_sub_distrib]
  rw [hroot_sum]
  ring_nf
  rw [hroot_mul]
  ring
```

## Statement dependencies

- `Mathlib:Mathlib.Combinatorics.SimpleGraph.Acyclic.SimpleGraph.IsTree`
- `Mathlib:Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected.SimpleGraph.ConnectedComponent.toSimpleGraph`
- `current repo:Main.LatticeFoundations.treePairingAnchor`
- `current repo:Main.RootedCapacity.rootedChildComponent`
- `current repo:Main.RootedCapacity.rootedChildRoot`
- `current repo:Main.RootedCapacity.rootedChildren`

## Proof dependencies

- `Mathlib:Mathlib.Algebra.BigOperators.Group.Finset.Basic.Finset.sum_congr`
- `Mathlib:Mathlib.Algebra.BigOperators.Group.Finset.Basic.Finset.sum_disjiUnion`
- `Mathlib:Mathlib.Algebra.BigOperators.Group.Finset.Defs.Finset.sum_sub_distrib`
- `Mathlib:Mathlib.Algebra.BigOperators.Group.Finset.Piecewise.Finset.sum_ite_eq'`
- `Mathlib:Mathlib.Algebra.BigOperators.Ring.Finset.Finset.mul_sum`
- `Mathlib:Mathlib.Combinatorics.SimpleGraph.Finite.SimpleGraph.neighborFinset_eq_filter`
- `Mathlib:Mathlib.Data.Finset.Disjoint.Finset.disjoint_left`
- `Mathlib:Mathlib.Data.Finset.Union.Finset.disjiUnion`
- `current repo:Main.LatticeFoundations.treePairingAnchor`
- `current repo:Main.RootedCapacity.rootedChildComponent_parent_not_mem`
- `current repo:Main.RootedCapacity.rootedChildComponent_partition`
- `current repo:Main.RootedCapacity.rootedChildRoot`
- `current repo:Main.RootedCapacity.rootedChildren`
- `current repo:Main.RootedCapacity.rootedEdgeClassification`
- `current repo:Main.RootedEstimates.sumNeighborContributionRootedChildComponent`
- `current repo:Main.RootedEstimates.sumNonrootEqSumRootedChildComponents`

## Sources

- `solution.tex:102-110`
