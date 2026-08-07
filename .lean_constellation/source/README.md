# Positive-definite Tree Lattices

This corpus gives a self-contained statement and proof of an irreducible-vertex
theorem for finite integer-weighted trees.

Source provenance: the material was derived from a canonical mathematical
problem statement and a complete natural-language solution, with the argument
cross-checked against an independent proof.

Reading order: read `problem.tex` first for the definitions and target theorem, then
`solution.tex` for the complete rooted-capacity proof.  The file
`formal_target.lean` is the single formalization target; its definitions encode
the same weighted-tree lattice, positive-definiteness hypothesis, unique
underweighted vertex, and irreducibility conclusion.

The solution develops all problem-specific ingredients used by the proof:
capacities of rooted components, their Schur-complement recursion, the rooted
integer estimate, and the final decomposition argument.  Standard finite
linear algebra facts about positive-definite matrices, inverse matrices,
Schur complements, and Cauchy--Schwarz are stated where they are used.

Extraction limits: there are no known gaps in the selected proof. Contextual
motivation, wider conjectures, an alternative cut-and-flow proof, and an
illustrative example are omitted because they are not needed for the stated
theorem or for the closure of the supplied solution.
