-- lean-constellation: managed-imports-begin
import PositiveDefiniteTreeLattice.Main.RootedCapacity.Prelude
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `rootedGram`

For a finite integer-weighted simple graph `G` with weight function `w`, define `rootedGram G w` as
the rational matrix indexed by the vertices of `G` whose `(u, v)` entry is the integer value
`treePairing G w (vertexVector u) (vertexVector v)` coerced to `ℚ`.  It is therefore the exact
rational scalar extension of the repository tree pairing in the vertex-vector basis.

## Sources

- Source `solution.tex`, lines 39–45

## Statement dependencies

- `Main.LatticeFoundations::treePairingAnchor` → `PositiveDefiniteTreeLattice.treePairing` from
  `PositiveDefiniteTreeLattice.Main.LatticeFoundations.Defs.treePairingAnchor`
- `Main.LatticeFoundations::vertexVectorAnchor` → `PositiveDefiniteTreeLattice.vertexVector` from
  `PositiveDefiniteTreeLattice.Main.LatticeFoundations.Defs.vertexVectorAnchor`
-/
def rootedGram {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (w : V → ℤ) : Matrix V V ℚ :=
  fun u v =>
    (PositiveDefiniteTreeLattice.treePairing G w
      (PositiveDefiniteTreeLattice.vertexVector u)
      (PositiveDefiniteTreeLattice.vertexVector v) : ℚ)
