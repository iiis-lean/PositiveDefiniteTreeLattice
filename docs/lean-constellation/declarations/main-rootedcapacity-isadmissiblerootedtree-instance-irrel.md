[← Public API](../PUBLIC_API.md) · [Public boundaries](../PUBLIC_BOUNDARIES.md) · [Complete graph](../DECLARATION_GRAPH.md)

# `isAdmissibleRootedTree_instance_irrel`

Admissibility of a fixed rooted weighted graph is independent of the chosen finite and decidability instances.

- Kind: `theorem`
- Node: `Main.RootedCapacity`
- Module: `PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.isAdmissibleRootedTree_instance_irrel`
- State: `proved`
- Revision status: `committed`
- Repository completion: `graph_proved`
- Compatibility `formal_code`: final proof projection

## Statement NL

For any type `V`, simple graph `G : SimpleGraph V`, integer weight `w : V → ℤ`, and root `ρ : V`, let `(fintype₁, decEq₁, decAdj₁)` and `(fintype₂, decEq₂, decAdj₂)` be two explicit instance conventions consisting respectively of a `Fintype V`, a `DecidableEq V`, and a `DecidableRel G.Adj`. Then the two explicitly instantiated propositions `@IsAdmissibleRootedTree` obtained from these conventions are logically equivalent. Thus admissibility for the fixed `(G, w, ρ)` transports in either direction between any two locally installed finite-type, equality-decidability, and adjacency-decidability instances.

## Statement Formal

```lean
-- lean-constellation: managed-imports-begin
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Prelude
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.IsAdmissibleRootedTree
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `isAdmissibleRootedTree_instance_irrel`

For any type `V`, simple graph `G : SimpleGraph V`, integer weight `w : V → ℤ`, and root `ρ : V`,
let `(fintype₁, decEq₁, decAdj₁)` and `(fintype₂, decEq₂, decAdj₂)` be two explicit instance
conventions consisting respectively of a `Fintype V`, a `DecidableEq V`, and a `DecidableRel G.Adj`.
Then the two explicitly instantiated propositions `@IsAdmissibleRootedTree` obtained from these
conventions are logically equivalent. Thus admissibility for the fixed `(G, w, ρ)` transports in
either direction between any two locally installed finite-type, equality-decidability, and
adjacency-decidability instances.

## Sources

- Source `solution.tex`, lines 33–38

## Statement dependencies

- `Main.RootedCapacity::IsAdmissibleRootedTree` → `IsAdmissibleRootedTree` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.IsAdmissibleRootedTree`
-/
theorem isAdmissibleRootedTree_instance_irrel {V : Type*} (G : SimpleGraph V)
    (w : V → ℤ) (ρ : V) (fintype₁ fintype₂ : Fintype V)
    (decEq₁ decEq₂ : DecidableEq V) (decAdj₁ decAdj₂ : DecidableRel G.Adj) :
    @IsAdmissibleRootedTree V fintype₁ decEq₁ G decAdj₁ w ρ ↔
      @IsAdmissibleRootedTree V fintype₂ decEq₂ G decAdj₂ w ρ := by
  have hFintype : fintype₁ = fintype₂ := Subsingleton.elim _ _
  subst fintype₂
  have hDecEq : decEq₁ = decEq₂ := Subsingleton.elim _ _
  subst decEq₂
  have hDecAdj : decAdj₁ = decAdj₂ := Subsingleton.elim _ _
  subst decAdj₂
  rfl
```

## Proof NL

Use instance irrelevance only. First obtain `fintype₁ = fintype₂` from the `Subsingleton (Fintype V)` instance supplied by `Fintype.subsingleton`, and eliminate that equality so both explicitly instantiated admissibility propositions use the same finite-type witness. Next obtain and eliminate `decEq₁ = decEq₂` and `decAdj₁ = decAdj₂` by ordinary subsingleton elimination for the decidability witnesses. After these three substitutions the two propositions are definitionally identical, so conclude the biconditional by `rfl`. The argument neither unfolds `IsAdmissibleRootedTree` nor uses graph, tree, or weight hypotheses.

## Proof Formal

```lean
-- lean-constellation: managed-imports-begin
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Prelude
import Mathlib.Data.Fintype.Defs
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.IsAdmissibleRootedTree
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `isAdmissibleRootedTree_instance_irrel`

For any type `V`, simple graph `G : SimpleGraph V`, integer weight `w : V → ℤ`, and root `ρ : V`,
let `(fintype₁, decEq₁, decAdj₁)` and `(fintype₂, decEq₂, decAdj₂)` be two explicit instance
conventions consisting respectively of a `Fintype V`, a `DecidableEq V`, and a `DecidableRel G.Adj`.
Then the two explicitly instantiated propositions `@IsAdmissibleRootedTree` obtained from these
conventions are logically equivalent. Thus admissibility for the fixed `(G, w, ρ)` transports in
either direction between any two locally installed finite-type, equality-decidability, and
adjacency-decidability instances.

## Sources

- Source `solution.tex`, lines 33–38

## Statement dependencies

- `Main.RootedCapacity::IsAdmissibleRootedTree` → `IsAdmissibleRootedTree` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.IsAdmissibleRootedTree`

## Proof outline

Use instance irrelevance only. First obtain `fintype₁ = fintype₂` from the `Subsingleton (Fintype
V)` instance supplied by `Fintype.subsingleton`, and eliminate that equality so both explicitly
instantiated admissibility propositions use the same finite-type witness. Next obtain and eliminate
`decEq₁ = decEq₂` and `decAdj₁ = decAdj₂` by ordinary subsingleton elimination for the decidability
witnesses. After these three substitutions the two propositions are definitionally identical, so
conclude the biconditional by `rfl`. The argument neither unfolds `IsAdmissibleRootedTree` nor uses
graph, tree, or weight hypotheses.

## Proof dependencies

- `Fintype.subsingleton` from `Mathlib.Data.Fintype.Defs`
-/
theorem isAdmissibleRootedTree_instance_irrel {V : Type*} (G : SimpleGraph V)
    (w : V → ℤ) (ρ : V) (fintype₁ fintype₂ : Fintype V)
    (decEq₁ decEq₂ : DecidableEq V) (decAdj₁ decAdj₂ : DecidableRel G.Adj) :
    @IsAdmissibleRootedTree V fintype₁ decEq₁ G decAdj₁ w ρ ↔
      @IsAdmissibleRootedTree V fintype₂ decEq₂ G decAdj₂ w ρ := by
  have hFintype : fintype₁ = fintype₂ := Subsingleton.elim _ _
  subst fintype₂
  have hDecEq : decEq₁ = decEq₂ := Subsingleton.elim _ _
  subst decEq₂
  have hDecAdj : decAdj₁ = decAdj₂ := Subsingleton.elim _ _
  subst decAdj₂
  rfl
```

## Statement dependencies

- `current repo:Main.RootedCapacity.IsAdmissibleRootedTree`

## Proof dependencies

- `Mathlib:Mathlib.Data.Fintype.Defs.Fintype.subsingleton`

## Sources

- `solution.tex:33-38`
