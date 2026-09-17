[← Public API](../PUBLIC_API.md) · [Public boundaries](../PUBLIC_BOUNDARIES.md) · [Complete graph](../DECLARATION_GRAPH.md)

# `rootedCapacity_instance_irrel`

The rooted capacity value is independent of the chosen finite and decidability instance conventions.

- Kind: `theorem`
- Node: `Main.RootedCapacity`
- Module: `PositiveDefiniteTreeLattice.Main.RootedCapacity.Theorems.rootedCapacity_instance_irrel`
- State: `proved`
- Revision status: `committed`
- Repository completion: `graph_proved`
- Compatibility `formal_code`: final proof projection

## Statement NL

For every type `V`, simple graph `G : SimpleGraph V`, weight function `w : V → ℤ`, root `ρ : V`, two explicit finite-type conventions `fintype₁ fintype₂ : Fintype V`, two explicit equality-decision conventions `decEq₁ decEq₂ : DecidableEq V`, and two explicit adjacency-decision conventions `decAdj₁ decAdj₂ : DecidableRel G.Adj`, the two explicitly instantiated rooted capacities are equal:

`@rootedCapacity V fintype₁ decEq₁ G decAdj₁ w ρ = @rootedCapacity V fintype₂ decEq₂ G decAdj₂ w ρ`.

Thus the root diagonal entry of the inverse rooted Gram matrix for fixed `G`, `w`, and `ρ` is independent of the chosen finite and decidability instances.

## Statement Formal

```lean
-- lean-constellation: managed-imports-begin
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Prelude
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedCapacity
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `rootedCapacity_instance_irrel`

For every type `V`, simple graph `G : SimpleGraph V`, weight function `w : V → ℤ`, root `ρ : V`, two
explicit finite-type conventions `fintype₁ fintype₂ : Fintype V`, two explicit equality-decision
conventions `decEq₁ decEq₂ : DecidableEq V`, and two explicit adjacency-decision conventions
`decAdj₁ decAdj₂ : DecidableRel G.Adj`, the two explicitly instantiated rooted capacities are equal:

`@rootedCapacity V fintype₁ decEq₁ G decAdj₁ w ρ = @rootedCapacity V fintype₂ decEq₂ G decAdj₂ w ρ`.

Thus the root diagonal entry of the inverse rooted Gram matrix for fixed `G`, `w`, and `ρ` is
independent of the chosen finite and decidability instances.

## Sources

- Source `solution.tex`, lines 39–45

## Statement dependencies

- `Main.RootedCapacity::rootedCapacity` → `rootedCapacity` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedCapacity`
-/
theorem rootedCapacity_instance_irrel {V : Type*} (G : SimpleGraph V)
    (w : V → ℤ) (ρ : V) (fintype₁ fintype₂ : Fintype V)
    (decEq₁ decEq₂ : DecidableEq V) (decAdj₁ decAdj₂ : DecidableRel G.Adj) :
    @rootedCapacity V fintype₁ decEq₁ G decAdj₁ w ρ =
      @rootedCapacity V fintype₂ decEq₂ G decAdj₂ w ρ := by
  sorry
```

## Proof NL

For the fixed data `V`, `G`, `w`, and `ρ`, first use subsingleton elimination to identify `fintype₁` with `fintype₂`.  Next identify `decEq₁` with `decEq₂`, and identify `decAdj₁` with `decAdj₂`; equality-decision and relation-decision conventions are proposition-valued decidability data and hence subsingletons.  The needed finite-type step is supplied by the verified instance `Fintype.subsingleton`.

Eliminate these three equalities in sequence (for example, by `obtain rfl := Subsingleton.elim ...`).  Both sides are then the same explicit `@rootedCapacity` application, with every data argument and every instance argument syntactically identical.  Close by controlled reflexivity; if elaboration exposes the definition, unfold `rootedCapacity` once and use `rfl` for its fixed rooted-Gram inverse diagonal.  This route uses no tree, admissibility, or child-specific hypothesis and introduces no casts, `HEq`, canonical instance, or representation change.

## Proof Formal

```lean
-- lean-constellation: managed-imports-begin
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Prelude
import Mathlib.Data.Fintype.Defs
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedCapacity
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `rootedCapacity_instance_irrel`

For every type `V`, simple graph `G : SimpleGraph V`, weight function `w : V → ℤ`, root `ρ : V`, two
explicit finite-type conventions `fintype₁ fintype₂ : Fintype V`, two explicit equality-decision
conventions `decEq₁ decEq₂ : DecidableEq V`, and two explicit adjacency-decision conventions
`decAdj₁ decAdj₂ : DecidableRel G.Adj`, the two explicitly instantiated rooted capacities are equal:

`@rootedCapacity V fintype₁ decEq₁ G decAdj₁ w ρ = @rootedCapacity V fintype₂ decEq₂ G decAdj₂ w ρ`.

Thus the root diagonal entry of the inverse rooted Gram matrix for fixed `G`, `w`, and `ρ` is
independent of the chosen finite and decidability instances.

## Sources

- Source `solution.tex`, lines 39–45

## Statement dependencies

- `Main.RootedCapacity::rootedCapacity` → `rootedCapacity` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedCapacity`

## Proof outline

For the fixed data `V`, `G`, `w`, and `ρ`, first use subsingleton elimination to identify `fintype₁`
with `fintype₂`.  Next identify `decEq₁` with `decEq₂`, and identify `decAdj₁` with `decAdj₂`;
equality-decision and relation-decision conventions are proposition-valued decidability data and
hence subsingletons.  The needed finite-type step is supplied by the verified instance
`Fintype.subsingleton`.

Eliminate these three equalities in sequence (for example, by `obtain rfl := Subsingleton.elim
...`).  Both sides are then the same explicit `@rootedCapacity` application, with every data
argument and every instance argument syntactically identical.  Close by controlled reflexivity; if
elaboration exposes the definition, unfold `rootedCapacity` once and use `rfl` for its fixed
rooted-Gram inverse diagonal.  This route uses no tree, admissibility, or child-specific hypothesis
and introduces no casts, `HEq`, canonical instance, or representation change.

## Proof sources

- Source `solution.tex`, lines 39–45

## Proof dependencies

- `Fintype.subsingleton` from `Mathlib.Data.Fintype.Defs`
- `Main.RootedCapacity::rootedCapacity` → `rootedCapacity` from
  `PositiveDefiniteTreeLattice.Main.RootedCapacity.Defs.rootedCapacity`
-/
theorem rootedCapacity_instance_irrel {V : Type*} (G : SimpleGraph V)
    (w : V → ℤ) (ρ : V) (fintype₁ fintype₂ : Fintype V)
    (decEq₁ decEq₂ : DecidableEq V) (decAdj₁ decAdj₂ : DecidableRel G.Adj) :
    @rootedCapacity V fintype₁ decEq₁ G decAdj₁ w ρ =
      @rootedCapacity V fintype₂ decEq₂ G decAdj₂ w ρ := by
  obtain rfl := Subsingleton.elim fintype₁ fintype₂
  obtain rfl := Subsingleton.elim decEq₁ decEq₂
  obtain rfl := Subsingleton.elim decAdj₁ decAdj₂
  rfl
```

## Statement dependencies

- `current repo:Main.RootedCapacity.rootedCapacity`

## Proof dependencies

- `Mathlib:Mathlib.Data.Fintype.Defs.Fintype.subsingleton`
- `current repo:Main.RootedCapacity.rootedCapacity`

## Sources

- `solution.tex:39-45`
