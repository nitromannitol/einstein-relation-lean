# Paper

This directory contains the paper formalized by this repository,

> Ahmed Bou-Rabee and Ruizhe Xu,
> *Quantitative Einstein relation for reversible diffusions in a random environment*
> (preprint),

with its bibliography and figure, and the compiled PDF.

- [`main.tex`](main.tex) is the source. It uses [`Ref.bib`](Ref.bib) and the figure
  [`einstein_paths.pdf`](einstein_paths.pdf).
- [`main.pdf`](main.pdf) is the compiled paper.

**Labels.** The paper is an evolving project, and this directory holds its current version.
[`CORRESPONDENCE.md`](../CORRESPONDENCE.md) maps its numbered results, by their LaTeX `\label`, to
Lean declarations. Comments in the Lean files cite `main.tex` by line range, in the form
`paper/main.tex:777–782`.

**Building.** With a TeX Live installation, run this in the present directory:

```bash
pdflatex -no-shell-escape main.tex
bibtex main
pdflatex -no-shell-escape main.tex
pdflatex -no-shell-escape main.tex
pdflatex -no-shell-escape main.tex
```

The last run reports no warning and no undefined reference.

**Rights.** The paper is by Ahmed Bou-Rabee and Ruizhe Xu. Its publication licence is not
set by the repository's Apache-2.0 licence ([`LICENSE`](../../LICENSE)), which is the licence of
the Lean development.
