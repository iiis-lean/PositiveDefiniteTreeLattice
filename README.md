<!-- BEGIN Lean Constellation: project-summary -->
<h1><img src="docs/lean-constellation/assets/lean-constellation-mark.svg" alt="Lean Constellation mark" width="42" align="absmiddle"> Positive-Definite Tree Lattices in Lean</h1>

![status: proved](https://img.shields.io/static/v1?label=status&message=proved&color=0f8f88&style=flat-square) ![Lean: 4.32.0](https://img.shields.io/static/v1?label=Lean&message=4.32.0&color=6b4fbb&style=flat-square) [![source: arXiv 2606.18119](https://img.shields.io/static/v1?label=source&message=arXiv+2606.18119&color=b31b1b&style=flat-square)](https://arxiv.org/abs/2606.18119) [![LC: Lean Constellation](https://img.shields.io/static/v1?label=LC&message=Lean+Constellation&color=092745&style=flat-square)](https://github.com/iiis-lean/lean-constellation) [![MCP: Lean Toolkit](https://img.shields.io/static/v1?label=MCP&message=Lean+Toolkit&color=e45132&style=flat-square)](https://github.com/iiis-lean/lean-mcp-toolkit)

A Lean 4 formalization of First Proof Second Batch Problem 6: an irreducible vertex in a positive-definite integer-weighted tree lattice.

## Project status

| Property | Value |
| --- | --- |
| Completion | `graph_proved` |
| Proof availability | `proved` |

## Build

```sh
lake build
```

## Public API

This repository exports **4 public declarations** across **2 nodes**.

Browse the [Public API index](docs/lean-constellation/PUBLIC_API.md) for the dependency graph, declaration index, final Lean code, dependencies, and sources. The [public boundary catalog](docs/lean-constellation/PUBLIC_BOUNDARIES.md) documents internal Content-public declarations and Scope propagation.

## About this formalization

This repository contains an independent Lean 4 formalization of First Proof Second Batch Problem 6:

> Joshua Evan Greene and Duncan McCoy, Problem 6 in Mohammed Abouzaid, Nikhil Srivastava, Rachel Ward, and Lauren Williams,
> *First Proof Second Batch*, arXiv:2606.18119v1 [cs.AI], 2026.
> <https://arxiv.org/abs/2606.18119>

The original theorem and author solution are due to Joshua Evan Greene and Duncan McCoy. The Lean formalization was produced by IIIS Lean using Lean Constellation. It is not presented as work by, or endorsed by, the original authors or the First Proof Project unless explicitly stated otherwise. The fixed supplementary material is available in the [official Second Batch repository](https://github.com/1stproof/batch-2/tree/77b4e4b466e958759882302179e7e94d7392a8e7), including the [authors' solution](https://github.com/1stproof/batch-2/blob/77b4e4b466e958759882302179e7e94d7392a8e7/batch-2-human-solution/problem-06/human-solution.tex) and the [expert-reviewed rooted-capacity submission used as the formalization route](https://github.com/1stproof/batch-2/blob/77b4e4b466e958759882302179e7e94d7392a8e7/batch-2-AI-solutions/problem-06/submission-C.tex).

For a finite tree `G` with integer vertex weights `w`, the associated integral lattice pairing is

```text
<x, y> = sum_u x_u * (w(u) * y_u - sum_{v adjacent to u} y_v).
```

The main theorem assumes that this pairing is positive on every nonzero integer vector and that exactly one vertex `v` is underweighted, meaning `w(v) < degree(v)`. It proves that some vertex basis vector is irreducible: it cannot be written as `a + b` for nonzero integer vectors `a` and `b` with `<a, b> >= 0`. See [`exists_irreducible_vertex`](docs/lean-constellation/declarations/main-irreduciblevertex-exists-irreducible-vertex.md) for the exact Lean statement and proof.

The proof deletes the unique underweighted vertex, organizes the remaining components as rooted trees, controls the root diagonal of the inverse Gram matrix by a capacity recursion, proves the rooted integer estimate, and uses it in the final decomposition argument. The broader Neumann--Zagier conjecture and the alternative cut-and-flow proof are outside this repository's scope. The focused SourceCorpus under `.lean_constellation/source/` is a rewritten and reorganized formalization resource; it preserves attribution to the original mathematical sources and does not reproduce the complete external supplementary TeX files verbatim.

To the best of our knowledge, this is the first public Lean 4 formalization of this exact Second Batch theorem. This is a bounded literature and code-search claim and does not rule out private or unindexed work. It should not be confused with public formalizations of First Proof *First Batch* Problem 6, which is a different graph-theoretic problem.

## Citation

If you use the mathematical result, cite the First Proof Second Batch report and identify Problem 6 as contributed by Joshua Evan Greene and Duncan McCoy:

```bibtex
@article{AbouzaidEtAl2026FirstProofSecondBatch,
  author        = {Mohammed Abouzaid and Nikhil Srivastava and Rachel Ward and Lauren Williams},
  title         = {First Proof Second Batch},
  journal       = {arXiv preprint},
  year          = {2026},
  eprint        = {2606.18119},
  archivePrefix = {arXiv},
  primaryClass  = {cs.AI},
  doi           = {10.48550/arXiv.2606.18119},
  url           = {https://arxiv.org/abs/2606.18119},
  note          = {Problem 6 contributed by Joshua Evan Greene and Duncan McCoy}
}
```

If you use the Lean implementation, cite this repository in addition to the report. Machine-readable citation metadata is available in [`CITATION.cff`](CITATION.cff).

## Licensing

Lean source code, the rewritten SourceCorpus, generated Lean Constellation metadata, and repository documentation are licensed under the Apache License 2.0; see [`LICENSE`](LICENSE).

The original theorem and author proof remain attributed to Joshua Evan Greene and Duncan McCoy. The First Proof report is distributed under [Creative Commons Attribution 4.0](https://creativecommons.org/licenses/by/4.0/); the fixed supplementary GitHub repository does not declare a repository-wide license. This repository does not relicense the linked external TeX files. See [`NOTICE`](NOTICE) for the scope and attribution record.

<p align="center">
  <img src="docs/lean-constellation/assets/lean-constellation-mark.svg" alt="Lean Constellation" width="72">
  <br>
  <sub>Generated with <strong>Lean Constellation</strong></sub>
</p>
<!-- END Lean Constellation: project-summary -->
