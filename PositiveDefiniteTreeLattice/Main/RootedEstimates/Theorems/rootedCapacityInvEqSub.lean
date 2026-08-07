-- lean-constellation: managed-imports-begin
import PositiveDefiniteTreeLattice.Main.RootedEstimates.Prelude
import Mathlib.Algebra.Group.Basic
import Mathlib.Combinatorics.SimpleGraph.Acyclic
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `rootedCapacityInvEqSub`

Let `V` be a finite vertex type, let `G : SimpleGraph V` have decidable adjacency, let `w : V → ℤ`,
and let `rho : V`. Assume separately a tree witness `hG : G.IsTree` and an admissibility hypothesis
`hAdm : IsAdmissibleRootedTree G w rho`. Then

`(rootedCapacity G w rho)⁻¹ = (w rho : ℚ) - rootedChildCapacitySum G hG w rho`.

Thus the child-capacity sum is formed using the tree witness `hG`, while admissibility is the
distinct hypothesis `hAdm`.

## Sources

- Source `solution.tex`, lines 122–126

## Statement dependencies

- `SimpleGraph.IsTree` from `Mathlib.Combinatorics.SimpleGraph.Acyclic`
- `Main.RootedCapacity::IsAdmissibleRootedTree` → `IsAdmissibleRootedTree` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.IsAdmissibleRootedTree`
- `Main.RootedCapacity::rootedCapacity` → `rootedCapacity` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedCapacity`
- `Main.RootedCapacity::rootedChildCapacitySum` → `rootedChildCapacitySum` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildCapacitySum`

## Proof outline

Put `d := (w rho : ℚ) - rootedChildCapacitySum G hG w rho`. Apply `rootedCapacity_recursion G hG w
rho hAdm` to rewrite the left side as `(1 / d)⁻¹`. The first component of
`PositiveDefiniteTreeLattice.capacity_pos_lt_one G w rho hAdm` supplies `0 < rootedCapacity G w
rho`, hence any nonzero side condition required by the field normalization. Use `inv_div` and the
simplifier's unit inverse/division identities to normalize `(1 / d)⁻¹ = d`. Substitution of the
definition of `d` is exactly the claimed equality. This implements the reciprocal substitution in
b_0010 lines 122–126.

## Proof sources

- Source `solution.tex`, lines 122–126

## Proof dependencies

- `inv_div` from `Mathlib.Algebra.Group.Basic`
- `Main.RootedCapacity::capacity_pos_lt_one` → `PositiveDefiniteTreeLattice.capacity_pos_lt_one`
  from `PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.capacity_pos_lt_one`
- `Main.RootedCapacity::rootedCapacity_recursion` → `rootedCapacity_recursion` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.rootedCapacity_recursion`
-/
theorem rootedCapacityInvEqSub {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.IsTree) (w : V → ℤ) (rho : V)
    (hAdm : IsAdmissibleRootedTree G w rho) :
    (rootedCapacity G w rho)⁻¹ = (w rho : ℚ) - rootedChildCapacitySum G hG w rho := by
  rw [rootedCapacity_recursion G hG w rho hAdm]
  simp
