-- lean-constellation: managed-imports-begin
import PositiveDefiniteTreeLattice.Main.RootedEstimates.Prelude
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.Ring.Unbundled.Basic
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `consecutiveIntegerProductNonneg`

For every integer `n`, the product of the consecutive integers `n` and `n - 1` is nonnegative:

`0 ≤ n * (n - 1)`.

## Sources

- Source `solution.tex`, lines 93–100

## Proof outline

Use the source's consecutive-integers argument (solution.tex, lines 93–100). Split on whether `n ≤
0`. In that branch, linear integer arithmetic gives `n - 1 ≤ 0`, so `mul_nonneg_of_nonpos_of_nonpos`
proves the product is nonnegative. In the complementary branch, integer discreteness gives `1 ≤ n`;
hence `0 ≤ n - 1`, and `mul_nonneg` proves the result. The linear order facts are lightweight and
can be discharged by `omega`. No project declaration is used.

## Proof sources

- Source `solution.tex`, lines 93–100

## Proof dependencies

- `mul_nonneg` from `Mathlib.Algebra.Order.GroupWithZero.Basic`
- `mul_nonneg_of_nonpos_of_nonpos` from `Mathlib.Algebra.Order.Ring.Unbundled.Basic`
-/
theorem consecutiveIntegerProductNonneg (n : ℤ) : 0 ≤ n * (n - 1) := by
  by_cases hn : n ≤ 0
  · exact mul_nonneg_of_nonpos_of_nonpos hn (by omega)
  · exact mul_nonneg (by omega) (by omega)
