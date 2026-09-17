-- lean-constellation: managed-imports-begin
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Prelude
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Data.Fintype.EquivFin
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.IsAdmissibleRootedTree
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildCapacitySum
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildComponent
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildRoot
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildren
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedGram
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `rootedGram_rootNonroot_contraction_eq_childCapacitySum_of_child_admissible`

Let `V` be finite with decidable equality. Let `G` be a tree on `V`, with a fixed tree witness `hG`
and decidable adjacency; let `w : V → ℤ` and `ρ : V`. Set `P := {x : V // x = ρ}` and `R := {x : V
// x ≠ ρ}`. Let `B₀`, `C₀`, and `D` be, respectively, the root-to-nonroot, nonroot-to-root, and
nonroot principal submatrices of `rootedGram G w` occurring in the exact root/nonroot block
decomposition of `rootedGram_reindex_rootNonroot_blocks`.

Assume only that every canonical root child `a : rootedChildren G hG ρ` has an attached rooted child
component `rootedChildComponent G hG ρ a` which is `IsAdmissibleRootedTree` at its canonical local
root `rootedChildRoot G hG ρ a`, with the fixed canonical attached-child-family instances used for
the child-block inverse decomposition.

Then, for every `r : P`,
`(B₀ * D⁻¹ * C₀) r r = rootedChildCapacitySum G hG w ρ`.
This uses the displayed multiplication order and the existing canonical sum over attached root-child
components.

## Sources

- Source `solution.tex`, lines 57–68

## Statement dependencies

- `SimpleGraph.IsTree` from `Mathlib.Combinatorics.SimpleGraph.Acyclic`
- `SimpleGraph.ConnectedComponent.toSimpleGraph` from
  `Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected`
- `SimpleGraph.deleteEdges` from `Mathlib.Combinatorics.SimpleGraph.DeleteEdges`
- `Fintype.ofFinite` from `Mathlib.Data.Fintype.EquivFin`
- `Matrix.submatrix` from `Mathlib.LinearAlgebra.Matrix.Defs`
- `Matrix.inv` from `Mathlib.LinearAlgebra.Matrix.NonsingularInverse`
- `Main.RootedCapacity::IsAdmissibleRootedTree` → `IsAdmissibleRootedTree` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.IsAdmissibleRootedTree`
- `Main.RootedCapacity::rootedChildCapacitySum` → `rootedChildCapacitySum` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildCapacitySum`
- `Main.RootedCapacity::rootedChildComponent` → `rootedChildComponent` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildComponent`
- `Main.RootedCapacity::rootedChildRoot` → `rootedChildRoot` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildRoot`
- `Main.RootedCapacity::rootedChildren` → `rootedChildren` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildren`
- `Main.RootedCapacity::rootedGram` → `rootedGram` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedGram`
-/

theorem rootedGram_rootNonroot_contraction_eq_childCapacitySum_of_child_admissible
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.IsTree) (w : V → ℤ) (ρ : V) :
    let P := {v : V // v = ρ}
    let R := {v : V // v ≠ ρ}
    let B₀ : Matrix P R ℚ := (rootedGram G w).submatrix Subtype.val Subtype.val
    let C₀ : Matrix R P ℚ := (rootedGram G w).submatrix Subtype.val Subtype.val
    let D : Matrix R R ℚ := (rootedGram G w).submatrix Subtype.val Subtype.val
    let I := {c : V // c ∈ rootedChildren G hG ρ ρ}
    letI : Fintype I := Fintype.ofFinite I
    letI : ∀ c : I, Fintype (rootedChildComponent G ρ c.1) :=
      fun c => Fintype.ofFinite (rootedChildComponent G ρ c.1)
    letI : ∀ c : I, DecidableEq (rootedChildComponent G ρ c.1) :=
      fun c => Classical.decEq (rootedChildComponent G ρ c.1)
    letI : ∀ c : I, DecidableRel (G.deleteEdges {s(ρ, c.1)}).Adj :=
      fun c => Classical.decRel (G.deleteEdges {s(ρ, c.1)}).Adj
    letI : ∀ c : I, DecidableRel (rootedChildComponent G ρ c.1).toSimpleGraph.Adj :=
      fun c => Classical.decRel (rootedChildComponent G ρ c.1).toSimpleGraph.Adj
    (∀ c : I, IsAdmissibleRootedTree (rootedChildComponent G ρ c.1).toSimpleGraph
      (fun x => w (x : V)) (rootedChildRoot G ρ c.1)) →
      ∀ r : P, (B₀ * D⁻¹ * C₀) r r = rootedChildCapacitySum G hG w ρ := by
  sorry
