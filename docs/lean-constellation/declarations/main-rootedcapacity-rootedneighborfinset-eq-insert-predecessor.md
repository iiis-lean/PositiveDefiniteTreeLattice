[← Public API](../PUBLIC_API.md) · [Public boundaries](../PUBLIC_BOUNDARIES.md) · [Complete graph](../DECLARATION_GRAPH.md)

# `rootedNeighborFinset_eq_insert_predecessor`

The neighbors of a nonroot vertex are its unique predecessor together with its rooted children.

- Kind: `theorem`
- Node: `Main.RootedCapacity`
- Module: `PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.rootedNeighborFinset_eq_insert_predecessor`
- State: `proved`
- Revision status: `committed`
- Repository completion: `graph_proved`
- Compatibility `formal_code`: final proof projection

## Statement NL

Let `V` be a finite type with decidable equality, let `G : SimpleGraph V` have decidable adjacency, let `hG : G.IsTree`, and fix a root `ρ : V`. For every vertex `x : V` with `x ≠ ρ`, there exists a vertex `p : V` such that `p ∉ rootedChildren G hG ρ x` and

`G.neighborFinset x = insert p (rootedChildren G hG ρ x)`.

Here `p` is the unique predecessor of `x` on the root-to-`x` path; all remaining neighbors of `x` are exactly its rooted children.

## Statement Formal

```lean
-- lean-constellation: managed-imports-begin
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Prelude
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Finite
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildren
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `rootedNeighborFinset_eq_insert_predecessor`

Let `V` be a finite type with decidable equality, let `G : SimpleGraph V` have decidable adjacency,
let `hG : G.IsTree`, and fix a root `ρ : V`. For every vertex `x : V` with `x ≠ ρ`, there exists a
vertex `p : V` such that `p ∉ rootedChildren G hG ρ x` and

`G.neighborFinset x = insert p (rootedChildren G hG ρ x)`.

Here `p` is the unique predecessor of `x` on the root-to-`x` path; all remaining neighbors of `x`
are exactly its rooted children.

## Sources

- Source `solution.tex`, lines 194–204

## Statement dependencies

- `SimpleGraph.IsTree` from `Mathlib.Combinatorics.SimpleGraph.Acyclic`
- `SimpleGraph.neighborFinset` from `Mathlib.Combinatorics.SimpleGraph.Finite`
- `Main.RootedCapacity::rootedChildren` → `rootedChildren` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildren`
-/
theorem rootedNeighborFinset_eq_insert_predecessor {V : Type*} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.IsTree)
    (ρ x : V) (hx : x ≠ ρ) :
    ∃ p : V, p ∉ rootedChildren G hG ρ x ∧
      G.neighborFinset x = insert p (rootedChildren G hG ρ x) := by
  sorry
```

## Proof NL

Let `P := (hG.existsUnique_path ρ x).choose`.  Since `hx : x ≠ ρ`, `P` is nonempty.  Set `p := P.penultimate`, and let `hpx : G.Adj p x` be its final edge.  The local walk facts `P.dropLast : G.Walk ρ p`, `P.IsPath.dropLast`, and the reconstruction of `P` from `P.dropLast` and `hpx` show, by unfolding `rootedChildren`, that `x ∈ rootedChildren G hG ρ p`.

For the first conjunct, suppose `p ∈ rootedChildren G hG ρ x`.  Its defining equality says that the unique root-to-`p` path is `P.concat hxp`.  On the other hand, the dropped-last path is the unique root-to-`p` path.  Rewriting by uniqueness makes `P.concat hxp` a path; `SimpleGraph.Walk.concat_isPath_iff` then says that `p ∉ P.support`, contradicting that the penultimate vertex lies on `P`.  Hence `p ∉ rootedChildren G hG ρ x`.

Prove the finset equality by extensionality.  Membership in `G.neighborFinset x` is ambient adjacency.  The forward inclusion splits on whether a neighbor `y` equals `p`.  In the other case, use `rootedChildRoot G p x` as the vertex `x` of the deleted-edge component `rootedChildComponent G p x`; then `rootedChildComponent_adj_mem G hG ρ p x hchild (rootedChildRoot G p x) y hxy hy` places `y` in that component.  Package it as `yC`.

Apply `rootedChildComponent_path_decomposition G hG ρ p x hchild yC`.  The unique root-to-`y` path is thereby the unique root-to-`x` path followed by the unique `x`-to-`y` component path.  The one-edge walk supplied by `hxy` is a path, so uniqueness in the child component identifies that factor with the edge `x-y`.  Rewriting gives exactly the `rootedChildren` membership witness for `y` at parent `x`.  Thus every ambient neighbor is either `p` or a rooted child.  Conversely, unfold `rootedChildren`: its first witness is precisely ambient adjacency from `x`, hence every inserted child belongs to `G.neighborFinset x`.  Simplify the two membership characterizations to conclude `G.neighborFinset x = insert p (rootedChildren G hG ρ x)`.

The only nontrivial library ingredients are the verified tree unique-path API and standard `Walk.dropLast`/path-concatenation facts; finset extensionality and insert membership are lightweight local simplifications.

## Proof Formal

```lean
-- lean-constellation: managed-imports-begin
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Prelude
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Walk.Operations
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildRoot
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildren
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.rootedChildComponent_adj_mem
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.rootedChildComponent_path_decomposition
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `rootedNeighborFinset_eq_insert_predecessor`

Let `V` be a finite type with decidable equality, let `G : SimpleGraph V` have decidable adjacency,
let `hG : G.IsTree`, and fix a root `ρ : V`. For every vertex `x : V` with `x ≠ ρ`, there exists a
vertex `p : V` such that `p ∉ rootedChildren G hG ρ x` and

`G.neighborFinset x = insert p (rootedChildren G hG ρ x)`.

Here `p` is the unique predecessor of `x` on the root-to-`x` path; all remaining neighbors of `x`
are exactly its rooted children.

## Sources

- Source `solution.tex`, lines 194–204

## Statement dependencies

- `SimpleGraph.IsTree` from `Mathlib.Combinatorics.SimpleGraph.Acyclic`
- `SimpleGraph.neighborFinset` from `Mathlib.Combinatorics.SimpleGraph.Finite`
- `Main.RootedCapacity::rootedChildren` → `rootedChildren` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildren`

## Proof outline

Let `P := (hG.existsUnique_path ρ x).choose`.  Since `hx : x ≠ ρ`, `P` is nonempty.  Set `p :=
P.penultimate`, and let `hpx : G.Adj p x` be its final edge.  The local walk facts `P.dropLast :
G.Walk ρ p`, `P.IsPath.dropLast`, and the reconstruction of `P` from `P.dropLast` and `hpx` show, by
unfolding `rootedChildren`, that `x ∈ rootedChildren G hG ρ p`.

For the first conjunct, suppose `p ∈ rootedChildren G hG ρ x`.  Its defining equality says that the
unique root-to-`p` path is `P.concat hxp`.  On the other hand, the dropped-last path is the unique
root-to-`p` path.  Rewriting by uniqueness makes `P.concat hxp` a path;
`SimpleGraph.Walk.concat_isPath_iff` then says that `p ∉ P.support`, contradicting that the
penultimate vertex lies on `P`.  Hence `p ∉ rootedChildren G hG ρ x`.

Prove the finset equality by extensionality.  Membership in `G.neighborFinset x` is ambient
adjacency.  The forward inclusion splits on whether a neighbor `y` equals `p`.  In the other case,
use `rootedChildRoot G p x` as the vertex `x` of the deleted-edge component `rootedChildComponent G
p x`; then `rootedChildComponent_adj_mem G hG ρ p x hchild (rootedChildRoot G p x) y hxy hy` places
`y` in that component.  Package it as `yC`.

Apply `rootedChildComponent_path_decomposition G hG ρ p x hchild yC`.  The unique root-to-`y` path
is thereby the unique root-to-`x` path followed by the unique `x`-to-`y` component path.  The
one-edge walk supplied by `hxy` is a path, so uniqueness in the child component identifies that
factor with the edge `x-y`.  Rewriting gives exactly the `rootedChildren` membership witness for `y`
at parent `x`.  Thus every ambient neighbor is either `p` or a rooted child.  Conversely, unfold
`rootedChildren`: its first witness is precisely ambient adjacency from `x`, hence every inserted
child belongs to `G.neighborFinset x`.  Simplify the two membership characterizations to conclude
`G.neighborFinset x = insert p (rootedChildren G hG ρ x)`.

The only nontrivial library ingredients are the verified tree unique-path API and standard
`Walk.dropLast`/path-concatenation facts; finset extensionality and insert membership are
lightweight local simplifications.

## Proof sources

- Source `solution.tex`, lines 194–204

## Proof dependencies

- `SimpleGraph.IsTree.existsUnique_path` from `Mathlib.Combinatorics.SimpleGraph.Acyclic`
- `SimpleGraph.Walk.IsPath.of_adj` from `Mathlib.Combinatorics.SimpleGraph.Paths`
- `SimpleGraph.Walk.concat_isPath_iff` from `Mathlib.Combinatorics.SimpleGraph.Paths`
- `SimpleGraph.Walk.concat_eq_append` from `Mathlib.Combinatorics.SimpleGraph.Walk.Operations`
- `SimpleGraph.Walk.reverse_cons` from `Mathlib.Combinatorics.SimpleGraph.Walk.Operations`
- `Main.RootedCapacity::rootedChildComponent_adj_mem` → `rootedChildComponent_adj_mem` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.rootedChildComponent_adj_mem`
- `Main.RootedCapacity::rootedChildComponent_path_decomposition` →
  `rootedChildComponent_path_decomposition` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.rootedChildComponent_path_decomposition`
- `Main.RootedCapacity::rootedChildRoot` → `rootedChildRoot` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildRoot`
-/
theorem rootedNeighborFinset_eq_insert_predecessor {V : Type*} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.IsTree)
    (ρ x : V) (hx : x ≠ ρ) :
    ∃ p : V, p ∉ rootedChildren G hG ρ x ∧
      G.neighborFinset x = insert p (rootedChildren G hG ρ x) := by
  classical
  let P := (hG.existsUnique_path ρ x).choose
  have hP : P.IsPath := by
    exact (hG.existsUnique_path ρ x).choose_spec.1
  generalize hrev : P.reverse = W
  cases W with
  | nil =>
      exact (hx rfl).elim
  | cons h R =>
      rename_i _ _ _ p
      have hPdecomp : P = R.reverse.concat h.symm := by
        calc
          P = P.reverse.reverse := by simp
          _ = (SimpleGraph.Walk.cons h R).reverse := by rw [hrev]
          _ = R.reverse.concat h.symm := by
            simpa only [SimpleGraph.Walk.reverse_cons] using
              (R.reverse.concat_eq_append h.symm).symm
      have hcatPath : (R.reverse.concat h.symm).IsPath := by
        rw [← hPdecomp]
        exact hP
      have hRpath : R.reverse.IsPath :=
        (SimpleGraph.Walk.concat_isPath_iff h.symm).mp hcatPath |>.1
      have hchild : x ∈ rootedChildren G hG ρ p := by
        simp only [rootedChildren, Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨h.symm, R.reverse, hRpath, ?_⟩
        simpa [P] using hPdecomp
      have hnotchild : p ∉ rootedChildren G hG ρ x := by
        intro hm
        simp only [rootedChildren, Finset.mem_filter, Finset.mem_univ, true_and] at hm
        obtain ⟨hxm, q, hq, hqeq⟩ := hm
        have hqP : q = P := by
          simpa [P] using (hG.existsUnique_path ρ x).unique hq
            (hG.existsUnique_path ρ x).choose_spec.1
        have hqcat : (q.concat hxm).IsPath := by
          rw [← hqeq]
          exact (hG.existsUnique_path ρ p).choose_spec.1
        have hnotmem : p ∉ q.support :=
          (SimpleGraph.Walk.concat_isPath_iff hxm).mp hqcat |>.2
        apply hnotmem
        rw [hqP, hPdecomp]
        simp
      refine ⟨p, hnotchild, ?_⟩
      ext y
      simp only [SimpleGraph.mem_neighborFinset, Finset.mem_insert]
      constructor
      · intro hxy
        by_cases hy : y = p
        · exact Or.inl hy
        · right
          simp only [rootedChildren, Finset.mem_filter, Finset.mem_univ, true_and]
          have hyC : y ∈ rootedChildComponent G p x := by
            exact rootedChildComponent_adj_mem G hG ρ p x hchild
              (rootedChildRoot G p x) y hxy hy
          have hdecomp := rootedChildComponent_path_decomposition G hG ρ p x hchild
            ⟨y, hyC⟩
          have hxyunique : (hG.existsUnique_path x y).choose = hxy.toWalk := by
            symm
            exact (hG.existsUnique_path x y).unique (SimpleGraph.Walk.IsPath.of_adj hxy)
              (hG.existsUnique_path x y).choose_spec.1
          refine ⟨hxy, P, hP, ?_⟩
          calc
            (hG.existsUnique_path ρ y).choose =
                (hG.existsUnique_path ρ x).choose.append
                  (hG.existsUnique_path x y).choose := hdecomp
            _ = P.append hxy.toWalk := by simp [P, hxyunique]
            _ = P.concat hxy := (P.concat_eq_append hxy).symm
      · intro hy
        rcases hy with rfl | hy
        · exact h
        · simp only [rootedChildren, Finset.mem_filter, Finset.mem_univ, true_and] at hy
          exact hy.1
```

## Statement dependencies

- `Mathlib:Mathlib.Combinatorics.SimpleGraph.Acyclic.SimpleGraph.IsTree`
- `Mathlib:Mathlib.Combinatorics.SimpleGraph.Finite.SimpleGraph.neighborFinset`
- `current repo:Main.RootedCapacity.rootedChildren`

## Proof dependencies

- `Mathlib:Mathlib.Combinatorics.SimpleGraph.Acyclic.SimpleGraph.IsTree.existsUnique_path`
- `Mathlib:Mathlib.Combinatorics.SimpleGraph.Paths.SimpleGraph.Walk.IsPath.of_adj`
- `Mathlib:Mathlib.Combinatorics.SimpleGraph.Paths.SimpleGraph.Walk.concat_isPath_iff`
- `Mathlib:Mathlib.Combinatorics.SimpleGraph.Walk.Operations.SimpleGraph.Walk.concat_eq_append`
- `Mathlib:Mathlib.Combinatorics.SimpleGraph.Walk.Operations.SimpleGraph.Walk.reverse_cons`
- `current repo:Main.RootedCapacity.rootedChildComponent_adj_mem`
- `current repo:Main.RootedCapacity.rootedChildComponent_path_decomposition`
- `current repo:Main.RootedCapacity.rootedChildRoot`

## Sources

- `solution.tex:194-204`
