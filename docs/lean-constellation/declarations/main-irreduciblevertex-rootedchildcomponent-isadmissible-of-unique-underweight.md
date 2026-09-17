[← Public API](../PUBLIC_API.md) · [Public boundaries](../PUBLIC_BOUNDARIES.md) · [Complete graph](../DECLARATION_GRAPH.md)

# `rootedChildComponent_isAdmissible_of_unique_underweight`

Each rooted component attached to the unique underweighted vertex is admissible.

- Kind: `lemma`
- Node: `Main.IrreducibleVertex`
- Module: `PositiveDefiniteTreeLattice.Main.IrreducibleVertex.Lemmas.rootedChildComponent_isAdmissible_of_unique_underweight`
- State: `proved`
- Revision status: `committed`
- Repository completion: `graph_proved`
- Compatibility `formal_code`: final proof projection

## Statement NL

Let `V` be a finite type with decidable equality, let `G : SimpleGraph V` have decidable adjacency, let `weight : V → ℤ`, and let `v c : V`. Suppose `h_tree : G.IsTree`, `h_positive : ∀ x : V → ℤ, x ≠ 0 → 0 < treePairing G weight x x`, `h_unique_underweight : ∃! u : V, weight u < (G.degree u : ℤ)`, `hv : weight v < (G.degree v : ℤ)`, `h_two : ∀ x : V, 2 ≤ weight x`, and `hvc : G.Adj v c`. Then `IsAdmissibleRootedTree (rootedChildComponent G v c).toSimpleGraph (fun z => weight (z : V)) (rootedChildRoot G v c)`.

## Statement Formal

```lean
-- lean-constellation: managed-imports-begin
import PositiveDefiniteTreeLattice.Main.IrreducibleVertex.Prelude
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Finite
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

noncomputable local instance rootedChildComponentFintype {V : Type*} [Fintype V]
    (G : SimpleGraph V) (v c : V) : Fintype (rootedChildComponent G v c) :=
  Fintype.ofFinite _

noncomputable local instance rootedChildComponentDecidableAdj {V : Type*} (G : SimpleGraph V)
    (v c : V) : DecidableRel (rootedChildComponent G v c).toSimpleGraph.Adj :=
  Classical.decRel _

/--
# lean-constellation target: `rootedChildComponent_isAdmissible_of_unique_underweight`

Let `V` be a finite type with decidable equality, let `G : SimpleGraph V` have decidable adjacency,
let `weight : V → ℤ`, and let `v c : V`. Suppose `h_tree : G.IsTree`, `h_positive : ∀ x : V → ℤ, x ≠
0 → 0 < treePairing G weight x x`, `h_unique_underweight : ∃! u : V, weight u < (G.degree u : ℤ)`,
`hv : weight v < (G.degree v : ℤ)`, `h_two : ∀ x : V, 2 ≤ weight x`, and `hvc : G.Adj v c`. Then
`IsAdmissibleRootedTree (rootedChildComponent G v c).toSimpleGraph (fun z => weight (z : V))
(rootedChildRoot G v c)`.

## Sources

- Source `solution.tex`, lines 194–204

## Statement dependencies

- `SimpleGraph.IsTree` from `Mathlib.Combinatorics.SimpleGraph.Acyclic`
- `SimpleGraph.degree` from `Mathlib.Combinatorics.SimpleGraph.Finite`
- `Main.LatticeFoundations::treePairingAnchor` → `PositiveDefiniteTreeLattice.treePairing` from
  `PositiveDefiniteTreeLattice.Main.LatticeFoundations.Defs.treePairingAnchor`
- `Main.RootedCapacity::IsAdmissibleRootedTree` → `IsAdmissibleRootedTree` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.IsAdmissibleRootedTree`
- `Main.RootedCapacity::rootedChildComponent` → `rootedChildComponent` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildComponent`
- `Main.RootedCapacity::rootedChildRoot` → `rootedChildRoot` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildRoot`
-/
theorem PositiveDefiniteTreeLattice.rootedChildComponent_isAdmissible_of_unique_underweight
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (weight : V → ℤ) (v c : V) (h_tree : G.IsTree)
    (h_positive : ∀ x : V → ℤ, x ≠ 0 → 0 < PositiveDefiniteTreeLattice.treePairing G weight x x)
    (h_unique_underweight : ∃! u : V, weight u < (G.degree u : ℤ))
    (hv : weight v < (G.degree v : ℤ)) (h_two : ∀ x : V, 2 ≤ weight x) (hvc : G.Adj v c) :
    IsAdmissibleRootedTree (rootedChildComponent G v c).toSimpleGraph (fun z => weight (z : V))
      (rootedChildRoot G v c) := by
  sorry
```

## Proof NL

Let C := rootedChildComponent G v c, with the local Fintype and decidable-adjacency instances already present in the accepted statement file. Unfold IsAdmissibleRootedTree and provide its four required pieces in order, using hC := rootedChildComponent_isTree G v c h_tree as the tree witness.

1. Tree field: use hC.

2. Positive-definite field: apply rootedGram_posDef_of_integer_positive G weight h_positive to obtain Matrix.PosDef (rootedGram G weight). Restrict this form along the injective coercion C → V with Matrix.PosDef.submatrix. Then use rootedGram_rootedChildComponent G weight v c h_tree hvc entrywise to rewrite the restriction as rootedGram C.toSimpleGraph (fun z : C => weight (z : V)).

3. Global weight-two field: prove ∀ y : C, (2 : ℤ) ≤ weight (y : V) by intro y; exact h_two (y : V). This is a separate conjunct of IsAdmissibleRootedTree and uses the original global hypothesis without alteration.

4. Rooted child-count field: first construct the precise witness
   hc : c ∈ rootedChildren G h_tree v v.
   After unfolding rootedChildren and Finset.mem_filter, supply:
   (a) c ∈ Finset.univ;
   (b) the edge witness hvc : G.Adj v c;
   (c) q := SimpleGraph.Walk.nil : G.Walk v v;
   (d) q.IsPath, by the nil-walk path fact; and
   (e) (h_tree.existsUnique_path v c).choose = q.concat hvc.
   For (e), the chosen path has IsPath by its choose_spec. The one-edge walk q.concat hvc is also a path: simplify q.concat hvc to the edge walk, use irreflexivity of G (hvc gives c ≠ v), and apply the nil/one-edge path constructors. The uniqueness clause of h_tree.existsUnique_path v c then gives the displayed equality. Thus every filter and unique-path condition in rootedChildren is explicitly discharged.

   Now fix z : C. The parent-exclusion lemma rootedChildComponent_parent_not_mem G v c h_tree hvc z gives (z : V) ≠ v. Hence weight_ge_degree_of_ne_unique_underweight G weight v h_unique_underweight hv (z : V) gives
   (G.degree (z : V) : ℤ) ≤ weight (z : V).
   Apply rootedChildComponent_childCount_add_one_eq_degree G h_tree v c hc z and rewrite its natural-number equality, explicitly after coercion to ℤ. The target becomes exactly
   (rootedChildCount C.toSimpleGraph hC (rootedChildRoot G v c) z : ℤ) + 1 ≤ weight (z : V),
   and follows from the preceding ambient-degree bound.

This follows solution.tex:194–204: components are trees, their Gram matrices are principal restrictions, every component vertex is nonexceptional and has global weight at least two, and ambient degree is component child count plus one.

## Proof Formal

```lean
-- lean-constellation: managed-imports-begin
import PositiveDefiniteTreeLattice.Main.IrreducibleVertex.Prelude
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Data.Sym.Sym2
import Mathlib.LinearAlgebra.Matrix.PosDef
import PositiveDefiniteTreeLattice.Main.IrreducibleVertex.Lemmas.rootedChildComponent_childCount_add_one_eq_degree
import PositiveDefiniteTreeLattice.Main.IrreducibleVertex.Lemmas.rootedGram_posDef_of_integer_positive
import PositiveDefiniteTreeLattice.Main.IrreducibleVertex.Lemmas.weight_ge_degree_of_ne_unique_underweight
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

noncomputable local instance rootedChildComponentFintype_admissible {V : Type*} [Fintype V]
    (G : SimpleGraph V) (v c : V) : Fintype (rootedChildComponent G v c) :=
  Fintype.ofFinite _

noncomputable local instance
    rootedChildComponentDecidableAdj_admissible {V : Type*} (G : SimpleGraph V)
    (v c : V) : DecidableRel (rootedChildComponent G v c).toSimpleGraph.Adj :=
  Classical.decRel _

/--
# lean-constellation target: `rootedChildComponent_isAdmissible_of_unique_underweight`

Let `V` be a finite type with decidable equality, let `G : SimpleGraph V` have decidable adjacency,
let `weight : V → ℤ`, and let `v c : V`. Suppose `h_tree : G.IsTree`, `h_positive : ∀ x : V → ℤ, x ≠
0 → 0 < treePairing G weight x x`, `h_unique_underweight : ∃! u : V, weight u < (G.degree u : ℤ)`,
`hv : weight v < (G.degree v : ℤ)`, `h_two : ∀ x : V, 2 ≤ weight x`, and `hvc : G.Adj v c`. Then
`IsAdmissibleRootedTree (rootedChildComponent G v c).toSimpleGraph (fun z => weight (z : V))
(rootedChildRoot G v c)`.

## Sources

- Source `solution.tex`, lines 194–204

## Statement dependencies

- `SimpleGraph.IsTree` from `Mathlib.Combinatorics.SimpleGraph.Acyclic`
- `SimpleGraph.degree` from `Mathlib.Combinatorics.SimpleGraph.Finite`
- `Main.LatticeFoundations::treePairingAnchor` → `PositiveDefiniteTreeLattice.treePairing` from
  `PositiveDefiniteTreeLattice.Main.LatticeFoundations.Defs.treePairingAnchor`
- `Main.RootedCapacity::IsAdmissibleRootedTree` → `IsAdmissibleRootedTree` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.IsAdmissibleRootedTree`
- `Main.RootedCapacity::rootedChildComponent` → `rootedChildComponent` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildComponent`
- `Main.RootedCapacity::rootedChildRoot` → `rootedChildRoot` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildRoot`

## Proof outline

Let C := rootedChildComponent G v c, with the local Fintype and decidable-adjacency instances
already present in the accepted statement file. Unfold IsAdmissibleRootedTree and provide its four
required pieces in order, using hC := rootedChildComponent_isTree G v c h_tree as the tree witness.

1. Tree field: use hC.

2. Positive-definite field: apply rootedGram_posDef_of_integer_positive G weight h_positive to
obtain Matrix.PosDef (rootedGram G weight). Restrict this form along the injective coercion C → V
with Matrix.PosDef.submatrix. Then use rootedGram_rootedChildComponent G weight v c h_tree hvc
entrywise to rewrite the restriction as rootedGram C.toSimpleGraph (fun z : C => weight (z : V)).

3. Global weight-two field: prove ∀ y : C, (2 : ℤ) ≤ weight (y : V) by intro y; exact h_two (y : V).
This is a separate conjunct of IsAdmissibleRootedTree and uses the original global hypothesis
without alteration.

4. Rooted child-count field: first construct the precise witness
   hc : c ∈ rootedChildren G h_tree v v.
   After unfolding rootedChildren and Finset.mem_filter, supply:
   (a) c ∈ Finset.univ;
   (b) the edge witness hvc : G.Adj v c;
   (c) q := SimpleGraph.Walk.nil : G.Walk v v;
   (d) q.IsPath, by the nil-walk path fact; and
   (e) (h_tree.existsUnique_path v c).choose = q.concat hvc.
   For (e), the chosen path has IsPath by its choose_spec. The one-edge walk q.concat hvc is also a
path: simplify q.concat hvc to the edge walk, use irreflexivity of G (hvc gives c ≠ v), and apply
the nil/one-edge path constructors. The uniqueness clause of h_tree.existsUnique_path v c then gives
the displayed equality. Thus every filter and unique-path condition in rootedChildren is explicitly
discharged.

   Now fix z : C. The parent-exclusion lemma rootedChildComponent_parent_not_mem G v c h_tree hvc z
gives (z : V) ≠ v. Hence weight_ge_degree_of_ne_unique_underweight G weight v h_unique_underweight
hv (z : V) gives
   (G.degree (z : V) : ℤ) ≤ weight (z : V).
   Apply rootedChildComponent_childCount_add_one_eq_degree G h_tree v c hc z and rewrite its
natural-number equality, explicitly after coercion to ℤ. The target becomes exactly
   (rootedChildCount C.toSimpleGraph hC (rootedChildRoot G v c) z : ℤ) + 1 ≤ weight (z : V),
   and follows from the preceding ambient-degree bound.

This follows solution.tex:194–204: components are trees, their Gram matrices are principal
restrictions, every component vertex is nonexceptional and has global weight at least two, and
ambient degree is component child count plus one.

## Proof sources

- Source `solution.tex`, lines 194–204

## Proof dependencies

- `SimpleGraph.IsTree.existsUnique_path` from `Mathlib.Combinatorics.SimpleGraph.Acyclic`
- `SimpleGraph.ConnectedComponent.toSimpleGraph` from
  `Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected`
- `SimpleGraph.deleteEdges` from `Mathlib.Combinatorics.SimpleGraph.DeleteEdges`
- `SimpleGraph.deleteEdges_adj` from `Mathlib.Combinatorics.SimpleGraph.DeleteEdges`
- `SimpleGraph.Walk.IsPath.concat` from `Mathlib.Combinatorics.SimpleGraph.Paths`
- `Sym2.instDecidableEq` from `Mathlib.Data.Sym.Sym2`
- `Sym2.mk_eq_mk_iff` from `Mathlib.Data.Sym.Sym2`
- `Matrix.PosDef.submatrix` from `Mathlib.LinearAlgebra.Matrix.PosDef`
- `Main.IrreducibleVertex::rootedChildComponent_childCount_add_one_eq_degree` →
  `PositiveDefiniteTreeLattice.rootedChildComponent_childCount_add_one_eq_degree` from `PositiveDefi
  niteTreeLattice.Main.IrreducibleVertex.Lemmas.rootedChildComponent_childCount_add_one_eq_degree`
- `Main.IrreducibleVertex::rootedGram_posDef_of_integer_positive` →
  `PositiveDefiniteTreeLattice.rootedGram_posDef_of_integer_positive` from
  `PositiveDefiniteTreeLattice.Main.IrreducibleVertex.Lemmas.rootedGram_posDef_of_integer_positive`
- `Main.IrreducibleVertex::weight_ge_degree_of_ne_unique_underweight` →
  `PositiveDefiniteTreeLattice.weight_ge_degree_of_ne_unique_underweight` from `PositiveDefiniteTree
  Lattice.Main.IrreducibleVertex.Lemmas.weight_ge_degree_of_ne_unique_underweight`
- `Main.RootedCapacity::rootedChildComponent_isTree` → `rootedChildComponent_isTree` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.rootedChildComponent_isTree`
- `Main.RootedCapacity::rootedChildComponent_parent_not_mem` → `rootedChildComponent_parent_not_mem`
  from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.rootedChildComponent_parent_not_mem`
- `Main.RootedCapacity::rootedChildren` → `rootedChildren` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildren`
- `Main.RootedCapacity::treePairing_vertexVector_vertexVector` →
  `treePairing_vertexVector_vertexVector` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.treePairing_vertexVector_vertexVector`
-/
theorem PositiveDefiniteTreeLattice.rootedChildComponent_isAdmissible_of_unique_underweight
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (weight : V → ℤ) (v c : V) (h_tree : G.IsTree)
    (h_positive : ∀ x : V → ℤ, x ≠ 0 → 0 < PositiveDefiniteTreeLattice.treePairing G weight x x)
    (h_unique_underweight : ∃! u : V, weight u < (G.degree u : ℤ))
    (hv : weight v < (G.degree v : ℤ)) (h_two : ∀ x : V, 2 ≤ weight x) (hvc : G.Adj v c) :
    IsAdmissibleRootedTree (rootedChildComponent G v c).toSimpleGraph (fun z => weight (z : V))
      (rootedChildRoot G v c) := by
  classical
  have hC : (rootedChildComponent G v c).toSimpleGraph.IsTree :=
    rootedChildComponent_isTree G v c h_tree
  refine ⟨hC, ?_, ?_, ?_⟩
  · have hpd : Matrix.PosDef (rootedGram G weight) :=
      rootedGram_posDef_of_integer_positive G weight h_positive
    have hGram :
        rootedGram (rootedChildComponent G v c).toSimpleGraph (fun z => weight (z : V)) =
          (rootedGram G weight).submatrix
            (fun z : rootedChildComponent G v c => (z : V))
            (fun z : rootedChildComponent G v c => (z : V)) := by
      ext x y
      have hadj : (rootedChildComponent G v c).toSimpleGraph.Adj x y ↔
          G.Adj (x : V) (y : V) := by
        change (G.deleteEdges {s(v, c)}).Adj (x : V) (y : V) ↔ G.Adj (x : V) (y : V)
        constructor
        · intro hxy
          exact (G.deleteEdges_adj.mp hxy).1
        · intro hxy
          apply G.deleteEdges_adj.mpr
          refine ⟨hxy, ?_⟩
          simp only [Set.mem_singleton_iff]
          intro hedge
          let p : V × V := ((x : V), (y : V))
          let q : V × V := (v, c)
          have hpair_eq : s(p.1, p.2) = s(q.1, q.2) := by
            simpa [p, q] using hedge
          rcases Sym2.mk_eq_mk_iff.mp hpair_eq with hpair | hpair
          · have hxv : (x : V) = v := by
              simpa [p, q] using congrArg Prod.fst hpair
            exact (rootedChildComponent_parent_not_mem G v c h_tree hvc x) hxv
          · have hyv : (y : V) = v := by
              simpa [p, q] using congrArg Prod.snd hpair
            exact (rootedChildComponent_parent_not_mem G v c h_tree hvc y) hyv
      change
        (PositiveDefiniteTreeLattice.treePairing (rootedChildComponent G v c).toSimpleGraph
          (fun z => weight (z : V))
          (PositiveDefiniteTreeLattice.vertexVector x)
          (PositiveDefiniteTreeLattice.vertexVector y) : ℚ) =
          PositiveDefiniteTreeLattice.treePairing G weight
            (PositiveDefiniteTreeLattice.vertexVector (x : V))
            (PositiveDefiniteTreeLattice.vertexVector (y : V))
      rw [treePairing_vertexVector_vertexVector _ hC,
        treePairing_vertexVector_vertexVector _ h_tree]
      simp [hadj]
    rw [hGram]
    exact hpd.submatrix Subtype.val_injective
  · intro y
    exact h_two (y : V)
  · have hc : c ∈ rootedChildren G h_tree v v := by
      rw [rootedChildren]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨hvc, SimpleGraph.Walk.nil, ?_, ?_⟩
      · simp
      · apply (h_tree.existsUnique_path v c).unique
        · exact (h_tree.existsUnique_path v c).choose_spec.1
        · have hcv : c ≠ v := by
            intro hcv
            subst c
            exact G.irrefl hvc
          exact SimpleGraph.Walk.IsPath.concat SimpleGraph.Walk.IsPath.nil (by simpa using hcv) hvc
    intro z
    have hzv : (z : V) ≠ v :=
      rootedChildComponent_parent_not_mem G v c h_tree hvc z
    have hdegree : (G.degree (z : V) : ℤ) ≤ weight (z : V) :=
      weight_ge_degree_of_ne_unique_underweight G weight v (z : V) h_unique_underweight hv hzv
    have hcount := rootedChildComponent_childCount_add_one_eq_degree G h_tree v c hc z
    have hcount_int :
        (rootedChildCount (rootedChildComponent G v c).toSimpleGraph hC
          (rootedChildRoot G v c) z : ℤ) + 1 = (G.degree (z : V) : ℤ) := by
      norm_cast
    rw [hcount_int]
    exact hdegree
```

## Statement dependencies

- `Mathlib:Mathlib.Combinatorics.SimpleGraph.Acyclic.SimpleGraph.IsTree`
- `Mathlib:Mathlib.Combinatorics.SimpleGraph.Finite.SimpleGraph.degree`
- `current repo:Main.LatticeFoundations.treePairingAnchor`
- `current repo:Main.RootedCapacity.IsAdmissibleRootedTree`
- `current repo:Main.RootedCapacity.rootedChildComponent`
- `current repo:Main.RootedCapacity.rootedChildRoot`

## Proof dependencies

- `Mathlib:Mathlib.Combinatorics.SimpleGraph.Acyclic.SimpleGraph.IsTree.existsUnique_path`
- `Mathlib:Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected.SimpleGraph.ConnectedComponent.toSimpleGraph`
- `Mathlib:Mathlib.Combinatorics.SimpleGraph.DeleteEdges.SimpleGraph.deleteEdges`
- `Mathlib:Mathlib.Combinatorics.SimpleGraph.DeleteEdges.SimpleGraph.deleteEdges_adj`
- `Mathlib:Mathlib.Combinatorics.SimpleGraph.Paths.SimpleGraph.Walk.IsPath.concat`
- `Mathlib:Mathlib.Data.Sym.Sym2.Sym2.instDecidableEq`
- `Mathlib:Mathlib.Data.Sym.Sym2.Sym2.mk_eq_mk_iff`
- `Mathlib:Mathlib.LinearAlgebra.Matrix.PosDef.Matrix.PosDef.submatrix`
- `current repo:Main.IrreducibleVertex.rootedChildComponent_childCount_add_one_eq_degree`
- `current repo:Main.IrreducibleVertex.rootedGram_posDef_of_integer_positive`
- `current repo:Main.IrreducibleVertex.weight_ge_degree_of_ne_unique_underweight`
- `current repo:Main.RootedCapacity.rootedChildComponent_isTree`
- `current repo:Main.RootedCapacity.rootedChildComponent_parent_not_mem`
- `current repo:Main.RootedCapacity.rootedChildren`
- `current repo:Main.RootedCapacity.treePairing_vertexVector_vertexVector`

## Sources

- `solution.tex:194-204`
