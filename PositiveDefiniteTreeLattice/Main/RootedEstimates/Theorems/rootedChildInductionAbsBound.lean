-- lean-constellation: managed-imports-begin
import PositiveDefiniteTreeLattice.Main.RootedEstimates.Prelude
import PositiveDefiniteTreeLattice.Main.RootedEstimates.Theorems.twoBoundsGiveAbsLowerBound
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

universe u

/--
# lean-constellation target: `rootedChildInductionAbsBound`

Let `G` be a finite rooted integer-weighted tree with root `rho`, weight `w`, and admissibility
hypothesis `hT : IsAdmissibleRootedTree G w rho`.  Let `x : V → ℤ`, let `c ∈ rootedChildren G hT rho
rho`, and write `C := rootedChildComponent G rho c` with its provider-generated finite and decidable
structure and local root `rootedChildRoot G rho ⟨c, hc⟩`.  Set `a := x rho`, `s_c := x c`, and
`gamma_c := rootedChildCapacitySummand G hT w rho ⟨c, hc⟩`.

Assume the generalized strong-induction hypothesis for the rooted integer estimate: it supplies that
estimate, for every finite rooted admissible integer-weighted tree with strictly smaller
vertex-cardinality than `V`, every integral coordinate vector, and every integer parameter.  Applied
to `C` at the two integers `a` and `a - 1`, with the restricted weight and restricted coordinate
vector, it yields

`(↑childPairing : ℚ) - 2 * (a : ℚ) * (s_c : ℚ) ≥ -gamma_c * (a : ℚ)^2 + |(s_c : ℚ) - gamma_c * (a :
ℚ)|`,

where `childPairing` is the tree pairing of the child component graph on the restricted coordinate
vector.  The component’s rooted capacity is identified with `gamma_c`, and the child index remains
exactly `c ∈ rootedChildren G hT rho rho`.

## Sources

- Source `solution.tex`, lines 112–121

## Statement dependencies

- `Main.LatticeFoundations::treePairingAnchor` → `PositiveDefiniteTreeLattice.treePairing` from
  `PositiveDefiniteTreeLattice.Main.LatticeFoundations.Defs.treePairingAnchor`
- `Main.RootedCapacity::IsAdmissibleRootedTree` → `IsAdmissibleRootedTree` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.IsAdmissibleRootedTree`
- `Main.RootedCapacity::rootedCapacity` → `rootedCapacity` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedCapacity`
- `Main.RootedCapacity::rootedChildCapacitySummand` → `rootedChildCapacitySummand` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildCapacitySummand`
- `Main.RootedCapacity::rootedChildComponent` → `rootedChildComponent` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildComponent`
- `Main.RootedCapacity::rootedChildren` → `rootedChildren` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildren`

## Proof outline

Work classically and unfold the statement's lets only far enough to name C := rootedChildComponent G
rho c and install its displayed Fintype, DecidableEq, and local DecidableRel instances. Put a := x
rho, sC := x c, and gammaC := rootedChildCapacitySummand G hT w rho ⟨c,hc⟩. The repaired shared
universe is essential here: C is Type u, so it now directly instantiates the generalized hIH binder
W : Type u without any universe lift or strengthened induction premise.

Obtain hAdmC from IsAdmissibleRootedTree_rootedChildComponent G w rho rho c hT hc hAdm and hcard
from rootedChildComponent_card_lt G hT rho rho c hc. Apply hIH to the induced child graph
C.toSimpleGraph, the restricted weight fun u => w (u : V), child root rootedChildRoot G rho c,
hcard, and hAdmC. Use the restricted coordinate vector fun u => x (u : V), first with a and then
with a - 1. Unfold rootedChildCapacitySummand at both resulting conclusions; its definition
identifies their child rooted-capacity term with gammaC and their root coordinate with sC.

Cast and normalize the first induction conclusion over the rationals to obtain childPairing - 2*a*sC
>= sC - gammaC*a*(a+1). Normalize the second conclusion, at a-1, to obtain childPairing - 2*a*sC >=
-sC - gammaC*a*(a-1). The casts of the restricted pairing and child-root coordinate agree with the
formal conclusion by rfl/simp; the remaining rearrangements are ring normalization and linear
rational arithmetic.

Apply twoBoundsGiveAbsLowerBound gammaC a sC childPairing to these two inequalities. Its conclusion
is exactly childPairing - 2*a*sC >= -gammaC*a^2 + |sC-gammaC*a| with the unchanged
integer-to-rational casts. This reruns the source argument at b_0010 lines 112-121, retaining
exactly the same rootedChildren G hT rho rho index and admissibility assumptions.

## Proof sources

- Source `solution.tex`, lines 112–121

## Proof dependencies

- `Main.RootedCapacity::IsAdmissibleRootedTree_rootedChildComponent` →
  `IsAdmissibleRootedTree_rootedChildComponent` from `PositiveDefiniteTreeLattice.Main.RootedCapacit
  y.Theorems.IsAdmissibleRootedTree_rootedChildComponent`
- `Main.RootedCapacity::rootedChildCapacitySummand` → `rootedChildCapacitySummand` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildCapacitySummand`
- `Main.RootedCapacity::rootedChildComponent_card_lt` → `rootedChildComponent_card_lt` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.rootedChildComponent_card_lt`
- `Main.RootedCapacity::rootedChildRoot` → `rootedChildRoot` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildRoot`
- `Main.RootedEstimates::twoBoundsGiveAbsLowerBound` → `twoBoundsGiveAbsLowerBound` from
  `PositiveDefiniteTreeLattice.Main.RootedEstimates.Theorems.twoBoundsGiveAbsLowerBound`
-/
theorem rootedChildInductionAbsBound {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (w : V → ℤ) (rho : V) (hT : G.IsTree)
    (hAdm : IsAdmissibleRootedTree G w rho) (x : V → ℤ) (c : V)
    (hc : c ∈ rootedChildren G hT rho rho)
    (hIH : ∀ {W : Type u} [Fintype W] [DecidableEq W] (H : SimpleGraph W)
      [DecidableRel H.Adj] (weight : W → ℤ) (r : W), Fintype.card W < Fintype.card V →
        IsAdmissibleRootedTree H weight r → ∀ (y : W → ℤ) (k : ℤ),
          0 ≤ (↑(PositiveDefiniteTreeLattice.treePairing H weight y y) : ℚ) -
            (2 * (k : ℚ) + 1) * (y r : ℚ) + rootedCapacity H weight r * (k : ℚ) *
              ((k : ℚ) + 1)) :
    let C := rootedChildComponent G rho c
    letI : Fintype C := Fintype.ofFinite C
    letI : DecidableEq C := Classical.decEq C
    letI : DecidableRel C.toSimpleGraph.Adj := by
      intro u v
      change Decidable ((G.deleteEdges {s(rho, c)}).Adj (u : V) (v : V))
      infer_instance
    let a : ℤ := x rho
    let sC : ℤ := x c
    let gammaC : ℚ := rootedChildCapacitySummand G hT w rho ⟨c, hc⟩
    (↑(PositiveDefiniteTreeLattice.treePairing C.toSimpleGraph (fun u => w (u : V))
      (fun u => x (u : V)) (fun u => x (u : V))) : ℚ) -
        2 * (a : ℚ) * (sC : ℚ) ≥ -gammaC * (a : ℚ) ^ 2 +
          |(sC : ℚ) - gammaC * (a : ℚ)| := by
  classical
  dsimp only
  let C := rootedChildComponent G rho c
  letI : Fintype C := Fintype.ofFinite C
  letI : DecidableEq C := fun u v => u.instDecidableEq v
  letI : DecidableRel C.toSimpleGraph.Adj := by
    intro u v
    change Decidable ((G.deleteEdges {s(rho, c)}).Adj (u : V) (v : V))
    infer_instance
  let a : ℤ := x rho
  let sC : ℤ := x c
  let gammaC : ℚ := rootedChildCapacitySummand G hT w rho ⟨c, hc⟩
  have hAdmC :=
    IsAdmissibleRootedTree_rootedChildComponent G w rho rho c hT hc hAdm
  have hcard : Fintype.card C < Fintype.card V :=
    rootedChildComponent_card_lt G hT rho rho c hc
  have hfirst := hIH C.toSimpleGraph (fun u : C => w (u : V))
    (rootedChildRoot G rho c) hcard hAdmC (fun u : C => x (u : V)) a
  have hsecond := hIH C.toSimpleGraph (fun u : C => w (u : V))
    (rootedChildRoot G rho c) hcard hAdmC (fun u : C => x (u : V)) (a - 1)
  have hfirst' :
      (↑(PositiveDefiniteTreeLattice.treePairing C.toSimpleGraph (fun u => w (u : V))
        (fun u => x (u : V)) (fun u => x (u : V))) : ℚ) -
          2 * (a : ℚ) * (sC : ℚ) ≥
        (sC : ℚ) - gammaC * (a : ℚ) * ((a : ℚ) + 1) := by
    dsimp [gammaC, rootedChildCapacitySummand, a, sC] at hfirst ⊢
    simp only [rootedChildRoot] at hfirst ⊢
    norm_num at hfirst ⊢
    nlinarith
  have hsecond' :
      (↑(PositiveDefiniteTreeLattice.treePairing C.toSimpleGraph (fun u => w (u : V))
        (fun u => x (u : V)) (fun u => x (u : V))) : ℚ) -
          2 * (a : ℚ) * (sC : ℚ) ≥
        -(sC : ℚ) - gammaC * (a : ℚ) * ((a : ℚ) - 1) := by
    dsimp [gammaC, rootedChildCapacitySummand, a, sC] at hsecond ⊢
    simp only [rootedChildRoot] at hsecond ⊢
    norm_num at hsecond ⊢
    nlinarith
  exact twoBoundsGiveAbsLowerBound gammaC (a : ℚ) (sC : ℚ) _ hfirst' hsecond'
