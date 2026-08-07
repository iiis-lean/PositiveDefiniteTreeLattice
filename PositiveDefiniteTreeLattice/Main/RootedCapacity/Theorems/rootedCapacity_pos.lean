-- lean-constellation: managed-imports-begin
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Prelude
import Mathlib.LinearAlgebra.Matrix.PosDef
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.IsAdmissibleRootedTree
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedCapacity
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `rootedCapacity_pos`

Let V be a finite type with decidable equality, let G be a simple graph on V with decidable
adjacency, let w : V → ℤ, and let ρ : V. If hAdm : IsAdmissibleRootedTree G w ρ, then the rational
rooted capacity is strictly positive:

0 < rootedCapacity G w ρ.

Here rootedCapacity remains the ρ,ρ entry of the inverse rational rooted Gram matrix; no separate
tree proof or weight assumption beyond admissibility is required.

## Sources

- Source `solution.tex`, lines 39–45
- Source `solution.tex`, lines 70–72

## Statement dependencies

- `Main.RootedCapacity::IsAdmissibleRootedTree` → `IsAdmissibleRootedTree` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.IsAdmissibleRootedTree`
- `Main.RootedCapacity::rootedCapacity` → `rootedCapacity` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedCapacity`

## Proof outline

Unfold `IsAdmissibleRootedTree` only far enough to destruct `hAdm`; retain its positive-definiteness
field `hPos : Matrix.PosDef (rootedGram G w)` and ignore the tree witness and integer weight bounds,
which are not needed for this lower bound.  Apply the verified Mathlib theorem `Matrix.PosDef.inv`
to obtain `hPos.inv : Matrix.PosDef ((rootedGram G w)⁻¹)`.  Then specialize `Matrix.PosDef.diag_pos`
at the existing root index `ρ`, yielding `0 < (rootedGram G w)⁻¹ ρ ρ` over `ℚ`.

Finally unfold only `rootedCapacity`, whose definition is exactly that inverse diagonal entry, and
close by the diagonal-positivity result.  No separate tree witness, new weight bound,
Schur-complement hypothesis, or scalar extension is introduced; the proof uses exactly the
positive-definite rational rootedGram already packaged by admissibility.

## Proof sources

- Source `solution.tex`, lines 39–45
- Source `solution.tex`, lines 70–72

## Proof dependencies

- `Matrix.PosDef.diag_pos` from `Mathlib.LinearAlgebra.Matrix.PosDef`
- `Matrix.PosDef.inv` from `Mathlib.LinearAlgebra.Matrix.PosDef`
- `Main.RootedCapacity::IsAdmissibleRootedTree` → `IsAdmissibleRootedTree` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.IsAdmissibleRootedTree`
- `Main.RootedCapacity::rootedCapacity` → `rootedCapacity` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedCapacity`
-/
theorem rootedCapacity_pos {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (w : V → ℤ) (ρ : V)
    (hAdm : IsAdmissibleRootedTree G w ρ) : 0 < rootedCapacity G w ρ := by
  obtain ⟨-, hpos, -, -⟩ := hAdm
  unfold rootedCapacity
  exact hpos.inv.diag_pos
