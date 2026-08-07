-- lean-constellation: managed-imports-begin
import PositiveDefiniteTreeLattice.Main.RootedEstimates.Prelude
import Mathlib.Algebra.Order.Group.Unbundled.Abs
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `twoBoundsGiveAbsLowerBound`

For rational numbers `gamma`, `a`, `s`, and `z`, suppose

`z ≥ s - gamma * a * (a + 1)`

and

`z ≥ -s - gamma * a * (a - 1)`.

Then

`z ≥ -gamma * a^2 + |s - gamma * a|`.

## Sources

- Source `solution.tex`, lines 112–120

## Proof outline

Follow solution.tex, lines 112–121, by combining the two inequalities as the two signs of one
deviation. Put `b = s - gamma * a`. Ring normalization rewrites the first lower bound as `z ≥ -gamma
* a^2 + b` and the second as `z ≥ -gamma * a^2 - b`. Case-split with `abs_cases b`: in the
nonnegative case replace `|b|` by `b` and use the first bound; in the negative case replace `|b|` by
`-b` and use the second. Each final rearrangement is a lightweight ordered-ring
normalization/`linarith` step. No project declaration is used.

## Proof sources

- Source `solution.tex`, lines 112–121

## Proof dependencies

- `abs_of_nonneg` from `Mathlib.Algebra.Order.Group.Unbundled.Abs`
- `abs_of_nonpos` from `Mathlib.Algebra.Order.Group.Unbundled.Abs`
-/
theorem twoBoundsGiveAbsLowerBound (gamma a s z : ℚ)
    (h₁ : z ≥ s - gamma * a * (a + 1))
    (h₂ : z ≥ -s - gamma * a * (a - 1)) :
    z ≥ -gamma * a ^ 2 + |s - gamma * a| := by
  by_cases h : 0 ≤ s - gamma * a
  · rw [abs_of_nonneg h]
    nlinarith [h₁]
  · rw [abs_of_nonpos (le_of_not_ge h)]
    nlinarith [h₂]
