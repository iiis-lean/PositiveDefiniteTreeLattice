-- lean-constellation: managed-imports-begin
import PositiveDefiniteTreeLattice.Main.RootedEstimates.Prelude
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `sumNonrootEqSumRootedChildComponents`

Let `G` be a finite tree with root `rho`, let `A` be a commutative additive target, and let `f : V →
A` be a function on the ambient vertices.  The finite sum of `f` over all ambient vertices different
from `rho` equals the nested finite sum over the root children and their child-side components:

`∑ v ∈ Finset.univ with v ≠ rho, f v = ∑ c ∈ rootedChildren G hG rho rho, ∑ uC :
rootedChildComponent G rho c, f (↑uC)`.

The right-hand side uses exactly the `rootedChildren G hG rho rho` index and the subtype
`rootedChildComponent G rho c`; each non-root ambient vertex occurs in one and only one inner
component sum.

## Sources

- Source `solution.tex`, lines 102–110

## Statement dependencies

- `Main.RootedCapacity::rootedChildComponent` → `rootedChildComponent` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildComponent`
- `Main.RootedCapacity::rootedChildren` → `rootedChildren` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildren`

## Proof outline

Work classically. Let S := Finset.univ.filter (fun v => v ≠ rho) and let T be the finite sigma index
(rootedChildren G hG rho rho).sigma (fun c => Finset.univ : Finset (rootedChildComponent G rho c)).
For every v ∈ S, use rootedChildComponent_partition G hG rho v to choose its unique child c and its
membership proof, and map v to the sigma element whose second coordinate is ⟨v, hvC⟩.

Apply Finset.sum_bij to this map. It lands in T by the chosen child membership. If two images agree,
equality of their ambient second coordinates gives equality of the original vertices; the uniqueness
clause of rootedChildComponent_partition identifies their child indices. Conversely, every sigma
element ⟨c,uC⟩ maps back to its ambient coercion. The component-root exclusion from
rootedChildComponent_parent_not_mem proves this ambient vertex lies in S, while the partition
theorem and subtype extensionality prove it maps back to the same sigma element. The summands agree
definitionally as f (uC : V).

Finally use Finset.sum_sigma to rewrite the sum over T as the displayed outer finite sum over
rootedChildren G hG rho rho and inner Fintype sum over each exact subtype rootedChildComponent G rho
c. This is the finite implementation of the root/child-subtree decomposition in b_0010 lines
102–110.

## Proof sources

- Source `solution.tex`, lines 102–110

## Proof dependencies

- `Finset.sum_bij` from `Mathlib.Algebra.BigOperators.Group.Finset.Defs`
- `Finset.sum_sigma` from `Mathlib.Algebra.BigOperators.Group.Finset.Sigma`
- `Finset.sum_sigma'` from `Mathlib.Algebra.BigOperators.Group.Finset.Sigma`
- `Main.RootedCapacity::rootedChildComponent_parent_not_mem` → `rootedChildComponent_parent_not_mem`
  from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.rootedChildComponent_parent_not_mem`
- `Main.RootedCapacity::rootedChildComponent_partition` → `rootedChildComponent_partition` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.rootedChildComponent_partition`
-/
theorem sumNonrootEqSumRootedChildComponents {V A : Type*} [Fintype V] [DecidableEq V]
    [AddCommMonoid A] (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.IsTree) (rho : V)
    (f : V → A) :
    ∑ v ∈ Finset.univ.filter (fun v => v ≠ rho), f v =
      ∑ c ∈ rootedChildren G hG rho rho,
        let C := rootedChildComponent G rho c
        letI : Fintype C := Fintype.ofFinite C
        ∑ uC : C, f (uC : V) := by
  classical
  let child : ∀ v : V, v ≠ rho → V := fun v hv =>
    (rootedChildComponent_partition G hG rho v hv).choose
  have hchild : ∀ (v : V) (hv : v ≠ rho),
      child v hv ∈ rootedChildren G hG rho rho ∧
        v ∈ rootedChildComponent G rho (child v hv) := by
    intro v hv
    exact (rootedChildComponent_partition G hG rho v hv).choose_spec.1
  dsimp
  rw [Finset.sum_sigma']
  refine Finset.sum_bij
    (fun v hv => ⟨child v (Finset.mem_filter.mp hv).2,
      ⟨v, (hchild v (Finset.mem_filter.mp hv).2).2⟩⟩) ?_ ?_ ?_ ?_
  · intro v hv
    show ⟨child v (Finset.mem_filter.mp hv).2,
      ⟨v, (hchild v (Finset.mem_filter.mp hv).2).2⟩⟩ ∈
        (rootedChildren G hG rho rho).sigma
          (fun c => @Finset.univ (rootedChildComponent G rho c) (Fintype.ofFinite _))
    exact Finset.mem_sigma.mpr ⟨(hchild v (Finset.mem_filter.mp hv).2).1,
      @Finset.mem_univ _ (Fintype.ofFinite _) _⟩
  · intro v₁ hv₁ v₂ hv₂ heq
    exact congrArg (fun z => (z.2 : V)) heq
  · rintro ⟨c, uC⟩ hmem
    rcases Finset.mem_sigma.mp hmem with ⟨hc, _⟩
    have hrc : G.Adj rho c := by
      rw [rootedChildren] at hc
      exact (Finset.mem_filter.mp hc).2.1
    refine ⟨(uC : V), Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      rootedChildComponent_parent_not_mem G rho c hG hrc uC⟩, ?_⟩
    have hcc : child (uC : V)
        (rootedChildComponent_parent_not_mem G rho c hG hrc uC) = c :=
      (rootedChildComponent_partition G hG rho (uC : V)
        (rootedChildComponent_parent_not_mem G rho c hG hrc uC)).unique
        (hchild (uC : V)
          (rootedChildComponent_parent_not_mem G rho c hG hrc uC))
        ⟨hc, uC.property⟩
    apply Sigma.ext hcc
    apply (Subtype.heq_iff_coe_eq (by
      intro x
      change x ∈ rootedChildComponent G rho
        (child (uC : V)
          (rootedChildComponent_parent_not_mem G rho c hG hrc uC)) ↔
        x ∈ rootedChildComponent G rho c
      rw [hcc])).mpr
    rfl
  · intro v hv
    rfl
