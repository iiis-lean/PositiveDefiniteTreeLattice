-- lean-constellation: managed-imports-begin
import PositiveDefiniteTreeLattice.Main.RootedEstimates.Prelude
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Defs
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `treePairingInstanceIndependent`

Let `V` be one fixed type, let `G` be a simple graph on `V`, let `weight : V → ℤ`, and let `x y : V
→ ℤ`.  Let `(f₁, e₁, d₁)` and `(f₂, e₂, d₂)` be two explicit instance stacks consisting respectively
of a `Fintype V`, a `DecidableEq V`, and a `DecidableRel G.Adj`.

Evaluate `PositiveDefiniteTreeLattice.treePairing G weight x y` once with all three explicit
instances from the first stack and once with all three explicit instances from the second stack.
These two values are equal.

The equality changes only the finite/enumeration and adjacency-decision choices.  The type, graph,
endpoints, weight, vectors, and tree-pairing definition are identical on both sides, so the theorem
applies in particular when `V` is a rooted child-component subtype.

## Statement dependencies

- `Main.LatticeFoundations::treePairingAnchor` → `PositiveDefiniteTreeLattice.treePairing` from
  `PositiveDefiniteTreeLattice.Main.LatticeFoundations.Defs.treePairingAnchor`

## Proof outline

Introduce the two explicit instance stacks exactly as bound in the formal statement and unfold the
nested `letI` bindings, keeping the graph `G`, `weight`, `x`, and `y` fixed.  Unfold
`PositiveDefiniteTreeLattice.treePairing` on both sides; no graph-theoretic hypothesis or
source-derived lemma is needed.

Prove that the two explicit `Finset.univ : Finset V` values are equal using `Finset.ext`: membership
in either is `True`, independently of the supplied `Fintype V`.  For every fixed ambient vertex `u`,
prove that its two explicit `G.neighborFinset u` values are equal, again by `Finset.ext`; after
rewriting membership by `SimpleGraph.mem_neighborFinset`, both sides are the same proposition `G.Adj
u v`, independently of the supplied `DecidableEq V` and `DecidableRel G.Adj`.

Rewrite the outer sum with the `univ` equality.  Apply `Finset.sum_congr` and, at each fixed `u`,
rewrite its neighbor sum with the corresponding neighbor-finset equality.  The remaining summands
are definitionally the identical integer expression `x u * (weight u * y u - ∑ v, y v)`, so
reflexivity closes them.  This compares only the two instance choices and therefore applies
unchanged when `V` is a rooted child-component subtype.  It is a Lean-specific transport bridge, not
a mathematical premise from the source.

## Proof dependencies

- `Finset.sum_congr` from `Mathlib.Algebra.BigOperators.Group.Finset.Basic`
- `SimpleGraph.mem_neighborFinset` from `Mathlib.Combinatorics.SimpleGraph.Finite`
- `Finset.ext` from `Mathlib.Data.Finset.Defs`
- `Main.LatticeFoundations::treePairingAnchor` → `PositiveDefiniteTreeLattice.treePairing` from
  `PositiveDefiniteTreeLattice.Main.LatticeFoundations.Defs.treePairingAnchor`
-/
theorem treePairingInstanceIndependent {V : Type*} (G : SimpleGraph V) (weight x y : V → ℤ)
    (fintype₁ fintype₂ : Fintype V) (decEq₁ decEq₂ : DecidableEq V)
    (decAdj₁ decAdj₂ : DecidableRel G.Adj) :
    letI : Fintype V := fintype₁
    letI : DecidableEq V := decEq₁
    letI : DecidableRel G.Adj := decAdj₁
    let leftPairing := PositiveDefiniteTreeLattice.treePairing G weight x y
    letI : Fintype V := fintype₂
    letI : DecidableEq V := decEq₂
    letI : DecidableRel G.Adj := decAdj₂
    leftPairing = PositiveDefiniteTreeLattice.treePairing G weight x y := by
  classical
  dsimp only
  unfold PositiveDefiniteTreeLattice.treePairing
  apply Finset.sum_congr
  · ext u
    simp
  · intro u hu
    congr 1
    congr 1
    apply Finset.sum_congr
    · ext v
      simp [SimpleGraph.mem_neighborFinset]
    · intro v hv
      rfl
