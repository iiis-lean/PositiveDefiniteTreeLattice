-- lean-constellation: managed-imports-begin
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Prelude
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildren
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `rootedChildCount`

For a finite simple graph `G` that is a tree, a chosen root `ρ`, and a vertex `y`, define
`rootedChildCount G ρ y : ℕ` to be the cardinality of the finite set `rootedChildren G ρ y`.  Thus
`rootedChildCount G ρ y` is exactly `ch_C(y)`, the number of children of `y` in the orientation of
the rooted tree away from `ρ`.

## Sources

- Source `solution.tex`, lines 33–34

## Statement dependencies

- `Main.RootedCapacity::rootedChildren` → `rootedChildren` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildren`
-/
noncomputable def rootedChildCount {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hG : G.IsTree) (ρ y : V) : ℕ :=
  (rootedChildren G hG ρ y).card
