[← Public API](../PUBLIC_API.md) · [Public boundaries](../PUBLIC_BOUNDARIES.md) · [Complete graph](../DECLARATION_GRAPH.md)

# `sumComponentNeighborEqSumAmbientFiltered`

A connected component's local neighbor sum equals the filtered ambient neighbor sum after coercion.

- Kind: `theorem`
- Node: `Main.RootedEstimates`
- Module: `PositiveDefiniteTreeLattice.Main.RootedEstimates.Theorems.sumComponentNeighborEqSumAmbientFiltered`
- State: `proved`
- Revision status: `committed`
- Repository completion: `graph_proved`
- Compatibility `formal_code`: final proof projection

## Statement NL

Let `G` be a finite simple graph on ambient vertices `V`, let `C : G.ConnectedComponent`, and let `uC : C`.  For every commutative additive target `A` and every summand `Phi : V → A`, the neighbor sum in the component graph equals the ambient neighbor sum filtered to the vertices of that component:

`∑ vC ∈ C.toSimpleGraph.neighborFinset uC, Phi (↑vC) = ∑ v ∈ (G.neighborFinset (↑uC)).filter (fun v => v ∈ C), Phi v`.

The equality uses the subtype-to-ambient coercion on the left.  Thus the local neighbor index is exactly the filtered ambient ordered-neighbor index, with each compatible ambient neighbor represented once by its component subtype.

## Statement Formal

```lean
-- lean-constellation: managed-imports-begin
import PositiveDefiniteTreeLattice.Main.RootedEstimates.Prelude
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Finite
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `sumComponentNeighborEqSumAmbientFiltered`

Let `G` be a finite simple graph on ambient vertices `V`, let `C : G.ConnectedComponent`, and let
`uC : C`.  For every commutative additive target `A` and every summand `Phi : V → A`, the neighbor
sum in the component graph equals the ambient neighbor sum filtered to the vertices of that
component:

`∑ vC ∈ C.toSimpleGraph.neighborFinset uC, Phi (↑vC) = ∑ v ∈ (G.neighborFinset (↑uC)).filter (fun v
=> v ∈ C), Phi v`.

The equality uses the subtype-to-ambient coercion on the left.  Thus the local neighbor index is
exactly the filtered ambient ordered-neighbor index, with each compatible ambient neighbor
represented once by its component subtype.

## Sources

- Source `solution.tex`, lines 102–110

## Statement dependencies

- `SimpleGraph.ConnectedComponent.toSimpleGraph` from
  `Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected`
- `SimpleGraph.neighborFinset` from `Mathlib.Combinatorics.SimpleGraph.Finite`
-/
theorem sumComponentNeighborEqSumAmbientFiltered {V A : Type*} [Fintype V] [AddCommMonoid A]
    (G : SimpleGraph V) [DecidableRel G.Adj] (C : G.ConnectedComponent)
    (uC : C) (Phi : V → A) :
    letI : Fintype C := Fintype.ofFinite C
    letI : DecidableEq C := Classical.decEq C
    letI : DecidableRel C.toSimpleGraph.Adj := by
      intro u v
      change Decidable (G.Adj (u : V) (v : V))
      infer_instance
    letI : DecidablePred (fun v : V => v ∈ C) := Classical.decPred _
    ∑ vC ∈ C.toSimpleGraph.neighborFinset uC, Phi (vC : V) =
      ∑ v ∈ (G.neighborFinset (uC : V)).filter (fun v => v ∈ C), Phi v := by
  sorry
```

## Proof NL

Work classically and use the Fintype, decidable-equality, local-adjacency, and membership-decision instances already introduced by the formal statement. Rewrite the local and ambient neighbor finsets with SimpleGraph.neighborFinset_eq_filter. Apply Finset.sum_bij to the coercion map sending a local neighbor vC : C to its ambient value (vC : V).

For membership, a local neighbor satisfies C.toSimpleGraph.Adj uC vC; SimpleGraph.ConnectedComponent.toSimpleGraph_adj converts this to G.Adj (uC : V) (vC : V), and vC.property supplies the required component-filter membership. Injectivity is Subtype.ext applied to equality of ambient values. For surjectivity, an ambient vertex v in the filtered neighbor finset has both G.Adj (uC : V) v and hv : v ∈ C. Form the subtype vC := ⟨v, hv⟩; the reverse direction of toSimpleGraph_adj proves it is a local neighbor, and its coercion is v. Finally each transported summand is definitionally Phi (vC : V), so the summand-equality premise of sum_bij is reflexive.

The resulting equality is exactly the ordered local-neighbor sum and the ambient neighborFinset filtered by membership in C. It supplies the representation bridge used when expanding the child-subtree contribution in b_0010 lines 102–110, without changing the source mathematics or the ordered/double-counted convention.

## Proof Formal

```lean
-- lean-constellation: managed-imports-begin
import PositiveDefiniteTreeLattice.Main.RootedEstimates.Prelude
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Finite
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `sumComponentNeighborEqSumAmbientFiltered`

Let `G` be a finite simple graph on ambient vertices `V`, let `C : G.ConnectedComponent`, and let
`uC : C`.  For every commutative additive target `A` and every summand `Phi : V → A`, the neighbor
sum in the component graph equals the ambient neighbor sum filtered to the vertices of that
component:

`∑ vC ∈ C.toSimpleGraph.neighborFinset uC, Phi (↑vC) = ∑ v ∈ (G.neighborFinset (↑uC)).filter (fun v
=> v ∈ C), Phi v`.

The equality uses the subtype-to-ambient coercion on the left.  Thus the local neighbor index is
exactly the filtered ambient ordered-neighbor index, with each compatible ambient neighbor
represented once by its component subtype.

## Sources

- Source `solution.tex`, lines 102–110

## Statement dependencies

- `SimpleGraph.ConnectedComponent.toSimpleGraph` from
  `Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected`
- `SimpleGraph.neighborFinset` from `Mathlib.Combinatorics.SimpleGraph.Finite`

## Proof outline

Work classically and use the Fintype, decidable-equality, local-adjacency, and membership-decision
instances already introduced by the formal statement. Rewrite the local and ambient neighbor finsets
with SimpleGraph.neighborFinset_eq_filter. Apply Finset.sum_bij to the coercion map sending a local
neighbor vC : C to its ambient value (vC : V).

For membership, a local neighbor satisfies C.toSimpleGraph.Adj uC vC;
SimpleGraph.ConnectedComponent.toSimpleGraph_adj converts this to G.Adj (uC : V) (vC : V), and
vC.property supplies the required component-filter membership. Injectivity is Subtype.ext applied to
equality of ambient values. For surjectivity, an ambient vertex v in the filtered neighbor finset
has both G.Adj (uC : V) v and hv : v ∈ C. Form the subtype vC := ⟨v, hv⟩; the reverse direction of
toSimpleGraph_adj proves it is a local neighbor, and its coercion is v. Finally each transported
summand is definitionally Phi (vC : V), so the summand-equality premise of sum_bij is reflexive.

The resulting equality is exactly the ordered local-neighbor sum and the ambient neighborFinset
filtered by membership in C. It supplies the representation bridge used when expanding the
child-subtree contribution in b_0010 lines 102–110, without changing the source mathematics or the
ordered/double-counted convention.

## Proof sources

- Source `solution.tex`, lines 102–110

## Proof dependencies

- `Finset.sum_bij` from `Mathlib.Algebra.BigOperators.Group.Finset.Defs`
- `SimpleGraph.ConnectedComponent.toSimpleGraph_adj` from
  `Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected`
- `SimpleGraph.neighborFinset_eq_filter` from `Mathlib.Combinatorics.SimpleGraph.Finite`
-/
theorem sumComponentNeighborEqSumAmbientFiltered {V A : Type*} [Fintype V] [AddCommMonoid A]
    (G : SimpleGraph V) [DecidableRel G.Adj] (C : G.ConnectedComponent)
    (uC : C) (Phi : V → A) :
    letI : Fintype C := Fintype.ofFinite C
    letI : DecidableEq C := Classical.decEq C
    letI : DecidableRel C.toSimpleGraph.Adj := by
      intro u v
      change Decidable (G.Adj (u : V) (v : V))
      infer_instance
    letI : DecidablePred (fun v : V => v ∈ C) := Classical.decPred _
    ∑ vC ∈ C.toSimpleGraph.neighborFinset uC, Phi (vC : V) =
      ∑ v ∈ (G.neighborFinset (uC : V)).filter (fun v => v ∈ C), Phi v := by
  classical
  rw [SimpleGraph.neighborFinset_eq_filter,
    SimpleGraph.neighborFinset_eq_filter]
  refine Finset.sum_bij (fun vC _ => (vC : V)) ?_ ?_ ?_ ?_
  · intro vC hvC
    have hlocal : C.toSimpleGraph.Adj uC vC := by
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hvC
    refine Finset.mem_filter.mpr ⟨?_, vC.property⟩
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using
      (SimpleGraph.ConnectedComponent.toSimpleGraph_adj C uC.property vC.property).mp hlocal
  · intro vC₁ hvC₁ vC₂ hvC₂ hEq
    exact Subtype.ext hEq
  · intro v hv
    have hvAdj : G.Adj (uC : V) v := by
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using
        (Finset.mem_filter.mp hv).1
    have hvC : v ∈ C := (Finset.mem_filter.mp hv).2
    refine ⟨⟨v, hvC⟩, ?_, rfl⟩
    have hlocal : C.toSimpleGraph.Adj uC ⟨v, hvC⟩ :=
      (SimpleGraph.ConnectedComponent.toSimpleGraph_adj C uC.property hvC).mpr hvAdj
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hlocal
  · intro vC hvC
    rfl
```

## Statement dependencies

- `Mathlib:Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected.SimpleGraph.ConnectedComponent.toSimpleGraph`
- `Mathlib:Mathlib.Combinatorics.SimpleGraph.Finite.SimpleGraph.neighborFinset`

## Proof dependencies

- `Mathlib:Mathlib.Algebra.BigOperators.Group.Finset.Defs.Finset.sum_bij`
- `Mathlib:Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected.SimpleGraph.ConnectedComponent.toSimpleGraph_adj`
- `Mathlib:Mathlib.Combinatorics.SimpleGraph.Finite.SimpleGraph.neighborFinset_eq_filter`

## Sources

- `solution.tex:102-110`
