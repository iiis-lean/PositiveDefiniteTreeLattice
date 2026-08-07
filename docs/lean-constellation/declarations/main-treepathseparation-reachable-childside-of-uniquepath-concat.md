[← Public API](../PUBLIC_API.md) · [Public boundaries](../PUBLIC_BOUNDARIES.md)

# `reachable_childSide_of_uniquePath_concat`

A one-edge canonical root-path extension from the child side remains on that side of an oriented tree cut.

- Kind: `theorem`
- Node: `Main.TreePathSeparation`
- Module: `PositiveDefiniteTreeLattice.Main.TreePathSeparation.Theorems.reachable_childSide_of_uniquePath_concat`
- State: `proved`
- Revision status: `committed`
- Repository completion: `graph_proved`
- Formal code: final proof projection

## Lean code

```lean
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
import Mathlib.Data.Sym.Sym2
import PositiveDefiniteTreeLattice.Main.TreePathSeparation.Defs.uniquePath
import PositiveDefiniteTreeLattice.Main.TreePathSeparation.Theorems.eq_uniquePath_of_isPath
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `reachable_childSide_of_uniquePath_concat`

For any `{V : Type*} [Fintype V]`, let `G : SimpleGraph V` and `hG : G.IsTree`, and let `root parent
c x z : V`.  Assume `hpc : G.Adj parent c`, `hroot : (G.deleteEdges {s(parent,c)}).Reachable root
parent`, and `hx : (G.deleteEdges {s(parent,c)}).Reachable c x`.  If `hxz : G.Adj x z` and the
equality/witness is oriented as
`uniquePath G hG root z =` the walk obtained by concatenating `uniquePath G hG root x` with the
single ambient edge-walk from `x` to `z`, then
`(G.deleteEdges {s(parent,c)}).Reachable c z`.

Here `s(parent,c)` denotes the deleted undirected cut edge.  The extension is in the ambient graph
`G`; no hypothesis assumes that the edge `x-z` survives deletion.

## Sources

- Source `solution.tex`, lines 33–64

## Statement dependencies

- `SimpleGraph.Reachable` from `Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected`
- `SimpleGraph.deleteEdges` from `Mathlib.Combinatorics.SimpleGraph.DeleteEdges`
- `SimpleGraph.Walk.concat` from `Mathlib.Combinatorics.SimpleGraph.Walk.Operations`
- `Main.TreePathSeparation::uniquePath` → `uniquePath` from
  `PositiveDefiniteTreeLattice.Main.TreePathSeparation.Defs.uniquePath`

## Proof outline

Work classically and write (e = s(parent,c)).

1. Use `uniquePath_isPath G hG root z` and rewrite it by `hconcat`.  Thus the ambient walk
`(uniquePath G hG root x).concat hxz` is simple.  This records that the supplied extension is a
genuine canonical-path extension, not merely an arbitrary ambient walk.

2. Prove `s(x,z) ∉ ({e} : Set (Sym2 V))`.  First obtain
`hbridge : ¬ (G.deleteEdges {e}).Reachable parent c`
from `hG.isAcyclic`, `SimpleGraph.isAcyclic_iff_forall_adj_isBridge`, `hpc`, and the definition of
`SimpleGraph.IsBridge`.  If the equality of the unordered edges identifies `x = parent, z = c`, then
`hx` is exactly deleted-edge reachability from `c` to `parent), contradicting `hbridge` after
reversing its orientation.  In the other possible orientation, `x = c, z = parent), choose a simple
deleted-edge walk supplied by `hroot.exists_isPath`.  Transfer it to an ambient simple walk and use
`eq_uniquePath_of_isPath` to identify it with `uniquePath G hG root parent`.  After substituting
this identification into `hconcat`, `SimpleGraph.Walk.edges_concat` puts the cut edge (e) in that
transferred walk’s edge list (the final edge is `hpc.symm`).  But every edge of the original walk
lies in the deleted graph, so `SimpleGraph.deleteEdges_adj` / edge-set membership says it avoids
(e), a contradiction.  Handle the unordered-edge equality with the compiler-appropriate `Sym2` case
split.  These orientation, transfer, and edge-list manipulations are lightweight local Lean steps;
they introduce no reusable mathematical helper.

3. Apply `SimpleGraph.deleteEdges_adj` to `hxz` and the nonmembership from step 2, obtaining
`(G.deleteEdges {e}).Adj x z`.  The one-edge deleted-graph walk gives reachability from `x` to `z`;
compose it with `hx` using `SimpleGraph.Reachable.trans`.  The result is exactly `(G.deleteEdges
{s(parent,c)}).Reachable c z`.

## Proof sources

- Source `solution.tex`, lines 33–64

## Proof dependencies

- `SimpleGraph.isAcyclic_iff_forall_adj_isBridge` from `Mathlib.Combinatorics.SimpleGraph.Acyclic`
- `SimpleGraph.edgeSet_mono` from `Mathlib.Combinatorics.SimpleGraph.Basic`
- `SimpleGraph.Adj.reachable` from `Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected`
- `SimpleGraph.IsBridge` from `Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected`
- `SimpleGraph.Reachable.exists_isPath` from
  `Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected`
- `SimpleGraph.Reachable.symm` from `Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected`
- `SimpleGraph.Reachable.trans` from `Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected`
- `SimpleGraph.deleteEdges_adj` from `Mathlib.Combinatorics.SimpleGraph.DeleteEdges`
- `SimpleGraph.deleteEdges_le` from `Mathlib.Combinatorics.SimpleGraph.DeleteEdges`
- `SimpleGraph.Walk.IsPath.mem_support_iff_exists_append` from
  `Mathlib.Combinatorics.SimpleGraph.Paths`
- `SimpleGraph.Walk.IsPath.transfer` from `Mathlib.Combinatorics.SimpleGraph.Paths`
- `SimpleGraph.Walk.edges_subset_edgeSet` from `Mathlib.Combinatorics.SimpleGraph.Walk.Basic`
- `SimpleGraph.Walk.end_mem_support` from `Mathlib.Combinatorics.SimpleGraph.Walk.Basic`
- `SimpleGraph.Walk.transfer` from `Mathlib.Combinatorics.SimpleGraph.Walk.Maps`
- `SimpleGraph.Walk.reverse` from `Mathlib.Combinatorics.SimpleGraph.Walk.Operations`
- `SimpleGraph.Walk.support_subset_support_concat` from
  `Mathlib.Combinatorics.SimpleGraph.Walk.Operations`
- `Sym2.eq_iff` from `Mathlib.Data.Sym.Sym2`
- `Main.TreePathSeparation::eq_uniquePath_of_isPath` → `eq_uniquePath_of_isPath` from
  `PositiveDefiniteTreeLattice.Main.TreePathSeparation.Theorems.eq_uniquePath_of_isPath`
-/
theorem PositiveDefiniteTreeLattice.reachable_childSide_of_uniquePath_concat
    {V : Type*} [Fintype V] (G : SimpleGraph V) (hG : G.IsTree)
    (root parent c x z : V) (hpc : G.Adj parent c)
    (hroot : (G.deleteEdges {s(parent, c)}).Reachable root parent)
    (hx : (G.deleteEdges {s(parent, c)}).Reachable c x) (hxz : G.Adj x z)
    (hconcat : uniquePath G hG root z = (uniquePath G hG root x).concat hxz) :
    (G.deleteEdges {s(parent, c)}).Reachable c z := by
  classical
  have hbridge : ¬ (G.deleteEdges {s(parent, c)}).Reachable parent c := by
    simpa [SimpleGraph.IsBridge] using
      (SimpleGraph.isAcyclic_iff_forall_adj_isBridge.mp hG.isAcyclic hpc)
  have hnot : s(x, z) ∉ ({s(parent, c)} : Set (Sym2 V)) := by
    simp only [Set.mem_singleton_iff]
    intro hcut
    rcases Sym2.eq_iff.mp hcut with ⟨hxp, hzc⟩ | ⟨hxc, hzp⟩
    · subst x
      subst z
      exact hbridge hx.symm
    · subst x
      subst z
      obtain ⟨a, ha⟩ := hroot.exists_isPath
      have hca : c ∉ a.support := by
        intro hca
        obtain ⟨q, r, hq, hr, har⟩ :=
          ha.mem_support_iff_exists_append.mp hca
        exact hbridge ⟨r.reverse⟩
      have ha_to_G : ∀ e, e ∈ a.edges → e ∈ G.edgeSet := by
        intro e he
        exact (SimpleGraph.edgeSet_mono (G.deleteEdges_le _))
          (a.edges_subset_edgeSet he)
      let aG : G.Walk root parent := a.transfer G ha_to_G
      have haG : aG.IsPath := by
        dsimp [aG]
        exact ha.transfer ha_to_G
      have ha_eq : aG = uniquePath G hG root parent :=
        eq_uniquePath_of_isPath G hG root parent aG haG
      have hc_parent : c ∈ (uniquePath G hG root parent).support := by
        rw [hconcat]
        exact SimpleGraph.Walk.support_subset_support_concat _ hpc.symm
          (uniquePath G hG root c).end_mem_support
      have hcaG : c ∉ aG.support := by
        simpa [aG] using hca
      apply hcaG
      simpa [ha_eq] using hc_parent
  have hxz' : (G.deleteEdges {s(parent, c)}).Adj x z :=
    SimpleGraph.deleteEdges_adj.mpr ⟨hxz, hnot⟩
  exact hx.trans hxz'.reachable
```

## Statement dependencies

- `Mathlib:Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected.SimpleGraph.Reachable`
- `Mathlib:Mathlib.Combinatorics.SimpleGraph.DeleteEdges.SimpleGraph.deleteEdges`
- `Mathlib:Mathlib.Combinatorics.SimpleGraph.Walk.Operations.SimpleGraph.Walk.concat`
- `current repo:Main.TreePathSeparation.uniquePath`

## Proof dependencies

- `Mathlib:Mathlib.Combinatorics.SimpleGraph.Acyclic.SimpleGraph.isAcyclic_iff_forall_adj_isBridge`
- `Mathlib:Mathlib.Combinatorics.SimpleGraph.Basic.SimpleGraph.edgeSet_mono`
- `Mathlib:Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected.SimpleGraph.Adj.reachable`
- `Mathlib:Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected.SimpleGraph.IsBridge`
- `Mathlib:Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected.SimpleGraph.Reachable.exists_isPath`
- `Mathlib:Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected.SimpleGraph.Reachable.symm`
- `Mathlib:Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected.SimpleGraph.Reachable.trans`
- `Mathlib:Mathlib.Combinatorics.SimpleGraph.DeleteEdges.SimpleGraph.deleteEdges_adj`
- `Mathlib:Mathlib.Combinatorics.SimpleGraph.DeleteEdges.SimpleGraph.deleteEdges_le`
- `Mathlib:Mathlib.Combinatorics.SimpleGraph.Paths.SimpleGraph.Walk.IsPath.mem_support_iff_exists_append`
- `Mathlib:Mathlib.Combinatorics.SimpleGraph.Paths.SimpleGraph.Walk.IsPath.transfer`
- `Mathlib:Mathlib.Combinatorics.SimpleGraph.Walk.Basic.SimpleGraph.Walk.edges_subset_edgeSet`
- `Mathlib:Mathlib.Combinatorics.SimpleGraph.Walk.Basic.SimpleGraph.Walk.end_mem_support`
- `Mathlib:Mathlib.Combinatorics.SimpleGraph.Walk.Maps.SimpleGraph.Walk.transfer`
- `Mathlib:Mathlib.Combinatorics.SimpleGraph.Walk.Operations.SimpleGraph.Walk.reverse`
- `Mathlib:Mathlib.Combinatorics.SimpleGraph.Walk.Operations.SimpleGraph.Walk.support_subset_support_concat`
- `Mathlib:Mathlib.Data.Sym.Sym2.Sym2.eq_iff`
- `current repo:Main.TreePathSeparation.eq_uniquePath_of_isPath`

## Sources

- `solution.tex:33-64`
