-- lean-constellation: managed-imports-begin
import PositiveDefiniteTreeLattice.Main.TreePathSeparation.Prelude
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Walk.Basic
import Mathlib.Combinatorics.SimpleGraph.Walk.Maps
import Mathlib.Combinatorics.SimpleGraph.Walk.Operations
import PositiveDefiniteTreeLattice.Main.TreePathSeparation.Defs.uniquePath
import PositiveDefiniteTreeLattice.Main.TreePathSeparation.Theorems.eq_uniquePath_of_isPath
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `uniquePath_support_separated_by_cut`

The public theorem `PositiveDefiniteTreeLattice.uniquePath_support_separated_by_cut` has the
following statement. Let `V` be finite, `G` a simple graph on `V`, `hG : G.IsTree`, and let `root
parent c x z : V`. Assume `G.Adj parent c`, `(G.deleteEdges {s(parent, c)}).Reachable root parent`,
and `(G.deleteEdges {s(parent, c)}).Reachable c x`. Then

`z ∈ (uniquePath G hG root c).support ∧ z ∈ (uniquePath G hG c x).support ↔ z = c`.

The two deleted-edge reachability hypotheses express that `parent—c` is the terminal oriented edge
of the chosen root-to-`c` path and that `x` lies on the `c`-side of that cut. The conclusion is
exact support separation for those two chosen path objects; it introduces no RootedCapacity,
weighted, matrix, or assumed-separation hypothesis.

## Statement dependencies

- `SimpleGraph.Reachable` from `Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected`
- `SimpleGraph.deleteEdges` from `Mathlib.Combinatorics.SimpleGraph.DeleteEdges`
- `SimpleGraph.Walk.support` from `Mathlib.Combinatorics.SimpleGraph.Walk.Basic`
- `Main.TreePathSeparation::uniquePath` → `uniquePath` from
  `PositiveDefiniteTreeLattice.Main.TreePathSeparation.Defs.uniquePath`

## Proof outline

Put `D := G.deleteEdges {s(parent, c)}`. From the tree certificate and `hpc`, derive that
`s(parent,c)` is a bridge using `SimpleGraph.isAcyclic_iff_forall_adj_isBridge`; after unfolding
`SimpleGraph.IsBridge`, obtain `hbridge : ¬ D.Reachable parent c`.

First normalize the root-side witness `hroot`: choose its `D`-walk and replace it by `Walk.toPath`,
obtaining a simple deleted-edge path `a : D.Walk root parent`. Its support cannot contain `c`:
otherwise `a.IsPath.mem_support_iff_exists_append` splits it at `c`, and the suffix yields
`D.Reachable c parent`, contradicting `hbridge`. Transfer `a` back to `G` with `Walk.transfer`;
`IsPath.transfer` preserves simplicity and `support_transfer` preserves its support. Append the
one-edge walk for `hpc`. The preceding exclusion of `c` proves this append is an `IsPath`. Apply
`eq_uniquePath_of_isPath` to identify that append with `uniquePath G hG root c`. By
`support_append`, every vertex of this canonical root-to-`c` support other than `c` lies in the
support of the transferred root-side path `a`.

Similarly, normalize `hx` to a simple `D`-path `b : D.Walk c x`, transfer it to `G`, and use
`eq_uniquePath_of_isPath` to identify it with `uniquePath G hG c x`. Its support is unchanged by
transfer.

For the forward implication, take `z` in both canonical supports and suppose `z ≠ c`. The first
identification and the support formula place `z` in `a.support`; the second places it in
`b.support`. Apply `IsPath.mem_support_iff_exists_append` to both deleted-edge paths at `z`. The
prefix of `b` gives a deleted-edge walk from `c` to `z`; reverse the suffix of `a` to obtain a
deleted-edge walk from `z` to `parent`. Append them (or use `Reachable.trans`) to get `D.Reachable c
parent`, contradicting the bridge condition. Thus `z = c`.

For the reverse implication, substitute `z = c`; `c` is the terminal vertex of `uniquePath G hG root
c` and the initial vertex of `uniquePath G hG c x`, hence belongs to both supports. All nontrivial
mathematical steps are applications of the verified bridge, path-decomposition, transfer, support,
reverse, and reachability APIs; the remaining work is local witness extraction and simplification.

## Proof sources

- Source `solution.tex`, lines 33–64

## Proof dependencies

- `SimpleGraph.isAcyclic_iff_forall_adj_isBridge` from `Mathlib.Combinatorics.SimpleGraph.Acyclic`
- `SimpleGraph.edgeSet_mono` from `Mathlib.Combinatorics.SimpleGraph.Basic`
- `SimpleGraph.IsBridge` from `Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected`
- `SimpleGraph.Reachable.exists_isPath` from
  `Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected`
- `SimpleGraph.deleteEdges_le` from `Mathlib.Combinatorics.SimpleGraph.DeleteEdges`
- `SimpleGraph.Walk.IsPath.cons` from `Mathlib.Combinatorics.SimpleGraph.Paths`
- `SimpleGraph.Walk.IsPath.mem_support_iff_exists_append` from
  `Mathlib.Combinatorics.SimpleGraph.Paths`
- `SimpleGraph.Walk.IsPath.reverse` from `Mathlib.Combinatorics.SimpleGraph.Paths`
- `SimpleGraph.Walk.IsPath.transfer` from `Mathlib.Combinatorics.SimpleGraph.Paths`
- `SimpleGraph.Walk.edges_subset_edgeSet` from `Mathlib.Combinatorics.SimpleGraph.Walk.Basic`
- `SimpleGraph.Walk.end_mem_support` from `Mathlib.Combinatorics.SimpleGraph.Walk.Basic`
- `SimpleGraph.Walk.start_mem_support` from `Mathlib.Combinatorics.SimpleGraph.Walk.Basic`
- `SimpleGraph.Walk.support_transfer` from `Mathlib.Combinatorics.SimpleGraph.Walk.Maps`
- `SimpleGraph.Walk.transfer` from `Mathlib.Combinatorics.SimpleGraph.Walk.Maps`
- `SimpleGraph.Walk.append` from `Mathlib.Combinatorics.SimpleGraph.Walk.Operations`
- `SimpleGraph.Walk.reverse` from `Mathlib.Combinatorics.SimpleGraph.Walk.Operations`
- `Main.TreePathSeparation::eq_uniquePath_of_isPath` → `eq_uniquePath_of_isPath` from
  `PositiveDefiniteTreeLattice.Main.TreePathSeparation.Theorems.eq_uniquePath_of_isPath`
-/
theorem PositiveDefiniteTreeLattice.uniquePath_support_separated_by_cut
    {V : Type*} [Fintype V] (G : SimpleGraph V) (hG : G.IsTree)
    (root parent c x z : V) (hpc : G.Adj parent c)
    (hroot : (G.deleteEdges {s(parent, c)}).Reachable root parent)
    (hx : (G.deleteEdges {s(parent, c)}).Reachable c x) :
    z ∈ (uniquePath G hG root c).support ∧ z ∈ (uniquePath G hG c x).support ↔ z = c := by
  classical
  have hbridge : ¬ (G.deleteEdges {s(parent, c)}).Reachable parent c := by
    simpa [SimpleGraph.IsBridge] using
      (SimpleGraph.isAcyclic_iff_forall_adj_isBridge.mp hG.isAcyclic hpc)
  obtain ⟨a, ha⟩ := hroot.exists_isPath
  have hca : c ∉ a.support := by
    intro hca
    obtain ⟨q, r, hq, hr, har⟩ := (ha.mem_support_iff_exists_append.mp hca)
    apply hbridge
    exact ⟨r.reverse⟩
  have ha_to_G : ∀ e, e ∈ a.edges → e ∈ G.edgeSet := by
    intro e he
    exact (SimpleGraph.edgeSet_mono (G.deleteEdges_le _)) (a.edges_subset_edgeSet he)
  let aG : G.Walk root parent := a.transfer G ha_to_G
  have haG : aG.IsPath := by
    dsimp [aG]
    exact ha.transfer ha_to_G
  have hcaG : c ∉ aG.support := by
    simpa [aG] using hca
  let p : G.Walk root c := (SimpleGraph.Walk.cons hpc.symm aG.reverse).reverse
  have hp : p.IsPath := by
    dsimp [p]
    exact (haG.reverse.cons (by simpa using hcaG)).reverse
  have hp_eq : p = uniquePath G hG root c :=
    eq_uniquePath_of_isPath G hG root c p hp
  obtain ⟨b, hb⟩ := hx.exists_isPath
  have hb_to_G : ∀ e, e ∈ b.edges → e ∈ G.edgeSet := by
    intro e he
    exact (SimpleGraph.edgeSet_mono (G.deleteEdges_le _)) (b.edges_subset_edgeSet he)
  let bG : G.Walk c x := b.transfer G hb_to_G
  have hbG : bG.IsPath := by
    dsimp [bG]
    exact hb.transfer hb_to_G
  have hb_eq : bG = uniquePath G hG c x :=
    eq_uniquePath_of_isPath G hG c x bG hbG
  constructor
  · rintro ⟨hzp, hzb⟩
    by_contra hzc
    have hzp' : z ∈ p.support := by simpa [hp_eq] using hzp
    have hzb' : z ∈ bG.support := by simpa [hb_eq] using hzb
    have hza_or : z ∈ a.support ∨ z = parent := by
      simpa [p, aG, hzc] using hzp'
    have hza : z ∈ a.support := hza_or.elim id fun hz => hz ▸ a.end_mem_support
    have hzb : z ∈ b.support := by simpa [bG] using hzb'
    obtain ⟨q, r, hq, hr, har⟩ := ha.mem_support_iff_exists_append.mp hza
    obtain ⟨s, t, hs, ht, hbt⟩ := hb.mem_support_iff_exists_append.mp hzb
    apply hbridge
    exact ⟨(s.append r).reverse⟩
  · intro hzc
    subst z
    constructor
    · rw [← hp_eq]
      exact p.end_mem_support
    · rw [← hb_eq]
      exact bG.start_mem_support
