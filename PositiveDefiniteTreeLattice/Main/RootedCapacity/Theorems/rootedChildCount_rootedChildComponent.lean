-- lean-constellation: managed-imports-begin
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Prelude
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Finset.Card
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildComponent
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildCount
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildRoot
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildren
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.rootedChildComponent_isTree
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.rootedChildren_rootedChildComponent
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `rootedChildCount_rootedChildComponent`

For a finite vertex type `V` with decidable equality, a simple graph `G : SimpleGraph V`, a tree
proof `hG : G.IsTree`, an ambient root `ρ : V`, vertices `parent c : V`, and a hypothesis `hc : c ∈
rootedChildren G hG ρ parent`, let `C := rootedChildComponent G parent c`.  Then, for every `x : C`,
the child count in the induced component rooted at its canonical child root equals the ambient child
count: `rootedChildCount C.toSimpleGraph (rootedChildComponent_isTree G parent c hG)
(rootedChildRoot G parent c) x = rootedChildCount G hG ρ (x : V)`.  This is an equality of natural
numbers, with no weight, positive-definiteness, or admissibility hypothesis.

## Sources

- Source `solution.tex`, lines 48–61

## Statement dependencies

- `SimpleGraph.IsTree` from `Mathlib.Combinatorics.SimpleGraph.Acyclic`
- `SimpleGraph.ConnectedComponent.toSimpleGraph` from
  `Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected`
- `Main.RootedCapacity::rootedChildComponent` → `rootedChildComponent` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildComponent`
- `Main.RootedCapacity::rootedChildComponent_isTree` → `rootedChildComponent_isTree` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.rootedChildComponent_isTree`
- `Main.RootedCapacity::rootedChildCount` → `rootedChildCount` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildCount`
- `Main.RootedCapacity::rootedChildRoot` → `rootedChildRoot` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildRoot`
- `Main.RootedCapacity::rootedChildren` → `rootedChildren` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildren`

## Proof outline

Work under the existing `let`-bound child component, its finite and adjacency instances, and an
arbitrary `x : rootedChildComponent G parent c`; introduce `x` after discharging those local
binders.  Use the canonical subtype embedding
`e : rootedChildComponent G parent c ↪ V`, `e x = (x : V)`, whose injectivity is `Subtype.ext`.

Unfold `rootedChildCount` on both sides.  Apply `congrArg Finset.card` to the already proved public
transport theorem `rootedChildren_rootedChildComponent G hG ρ parent c hc x`.  Its conclusion is
exactly the equality between the ambient child finset and the `Finset.map e` of the component child
finset.  Rewrite the cardinality of that mapped finset with `Finset.card_map e`; this theorem
applies precisely because `e` is an embedding (hence injective), and leaves the component child
finset's cardinality.  The resulting equality is the required equality of the two unfolded child
counts.

This proof uses only the stated tree and rooted-child hypotheses.  In particular, it introduces no
admissibility, weight, positivity, or nonemptiness assumptions; all orientation transport is
delegated to the proved `rootedChildren_rootedChildComponent` equality.

## Proof sources

- Source `solution.tex`, lines 47–63

## Proof dependencies

- `Finset.card_map` from `Mathlib.Data.Finset.Card`
- `Main.RootedCapacity::rootedChildCount` → `rootedChildCount` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedChildCount`
- `Main.RootedCapacity::rootedChildren_rootedChildComponent` → `rootedChildren_rootedChildComponent`
  from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.rootedChildren_rootedChildComponent`
-/
theorem rootedChildCount_rootedChildComponent {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.IsTree) (ρ parent c : V)
    (hc : c ∈ rootedChildren G hG ρ parent) :
    let C := rootedChildComponent G parent c
    letI : Fintype C := Fintype.ofFinite C
    letI : DecidableRel C.toSimpleGraph.Adj := by
      intro x y
      change Decidable ((G.deleteEdges {s(parent, c)}).Adj (x : V) (y : V))
      infer_instance
    ∀ x : C,
      rootedChildCount C.toSimpleGraph (rootedChildComponent_isTree G parent c hG)
          (rootedChildRoot G parent c) x =
        rootedChildCount G hG ρ (x : V) := by
  classical
  dsimp
  intro x
  unfold rootedChildCount
  have h := congrArg Finset.card
    (rootedChildren_rootedChildComponent G hG ρ parent c hc x)
  simpa only [Finset.card_map] using h
