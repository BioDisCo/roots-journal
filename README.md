# Asymptotic Subspace Consensus in Dynamic Networks

This repository accompanies the paper *Asymptotic Subspace Consensus in Dynamic
Networks* by Matthias Függer and Thomas Nowak. It contains the manuscript,
supplementary animations and interactive figures, and a Lean formalization of
the mathematical results.

An earlier version of this paper appeared in the proceedings of
[SAND 2026](https://doi.org/10.4230/LIPIcs.SAND.2026.10).

- [Manuscript](manuscript/main.tex)
- [Supplementary material](manuscript/supplementary_material)
- [Lean formalization and correspondence with the paper](lean/README.md)

## Checking the formalization

The formalization can be checked from the repository's root directory with:

```sh
make check
```

This downloads the compiled Mathlib dependencies, builds the project, and checks
that every project theorem uses only Lean's standard foundational axioms
(`propext`, `Classical.choice`, and `Quot.sound`). It also checks the main proof
dependencies and the source-file and line targets of the manuscript's Lean badges.
The [correspondence table](lean/README.md#results) provides a starting point for
comparing individual statements and proofs with the paper.

The command requires Git, Make, Python 3, and
[elan](https://github.com/leanprover/elan), Lean's toolchain manager, with `lake`
available on the command search path. Elan selects the pinned Lean version
automatically. Lean and Mathlib are pinned to **v4.35.0**; the dependency revisions
are recorded in [lake-manifest.json](lean/lake-manifest.json).

## Building the manuscript

With `latexmk` and a TeX installation available, `make paper` builds
`manuscript/main.pdf`. The figure and badge PDFs are included in the repository.

`make check-all` runs both the formalization checks and the manuscript build.
