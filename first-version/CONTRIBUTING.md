# Contributing and building

This repository is mainly a finished artifact, the formalization of one paper, but issues and
pull requests are welcome.

## Building locally

```bash
lake exe cache get   # prebuilt mathlib oleans
lake build           # compile DeGiorgi and the library
```

The toolchain is pinned in `lean-toolchain` and managed by
[elan](https://github.com/leanprover/elan). The first build compiles the DeGiorgi dependency
from source; the README records a measured build time. The library builds without errors; it
inherits some linter warnings (unused variables and similar) from the development, and new code
should not add any. The only Lean files that contain a `sorry` are the two comparator challenges
`EinsteinRelationAudit/*/Challenge.lean`, each with exactly one, in its final theorem.

`lake build EinsteinRelation` builds the library alone, and `lake build EinsteinRelationAudit`
builds the comparator files.

## The main results and the audits

The eleven numbered results of the paper are in `EinsteinRelation/MainTheorems.lean`. Each
takes the literature inputs that its proof uses as explicit hypotheses, followed by the
statement of the result. Their axiom reports must consist of exactly `propext`,
`Classical.choice` and `Quot.sound`:

```bash
python3 scripts/check_axioms.py
```

The script writes the report request to a temporary file outside the repository, so that no
`#print` command is part of the library. It fails on `sorryAx`, on any other axiom, on a warning
and on a missing, unexpected or duplicate report.

```bash
python3 scripts/check_sources.py
```

checks that no library file contains `sorry`, `admit`, `native_decide`, `implemented_by`, an
`axiom` declaration or a `#print`/`#eval` command outside comments, that each comparator challenge
and its vocabulary import only Mathlib and each other, and that each `Challenge.lean` has exactly
one `sorry` and its vocabulary none.

## Conventions for Lean files

- No `sorry`, `admit`, `native_decide`, `implemented_by`, new `axiom` or debugging command
  anywhere in the library.
- Keep statements faithful to the paper. The statements of the eleven theorems must not be
  changed; a literature input must not be weakened or strengthened without checking it against
  its source. Refer to a result of the paper by its LaTeX label, as
  [`CORRESPONDENCE.md`](CORRESPONDENCE.md) does. Comments that cite `paper/main.tex` by line
  range refer to the file in [`paper/`](paper/).
- The pinned dependencies under `.lake/packages/` are read-only; extend them from this project
  rather than editing them.
- `lake clean` deletes the compiled dependencies and forces a rebuild of DeGiorgi. To rebuild
  only this project, delete its own build output under `.lake/build/lib/lean/EinsteinRelation`
  and run `lake build` again.

## Comparators

Each pair under `EinsteinRelationAudit/` has a `Challenge.lean` with its `Vocabulary/` files, which
import only Mathlib and each other; a `Solution.lean` that proves the same statement from the
library; and a `comparator.json` that permits exactly `propext`, `Classical.choice` and
`Quot.sound`. The vocabulary restates, under their library names, the definitions that the
statement uses, one file per library module, each importing exactly the Mathlib modules that the
library module sees (see [`EinsteinRelationAudit/README.md`](EinsteinRelationAudit/README.md)).
A change to one of these definitions in the library must be mirrored in the vocabulary; do not
change a challenge without checking it against the library and the paper. Run the pairs with
`scripts/run_comparators.sh`, as described in the README. A missing pair, a missing tool or a
failed kernel check is a failure. Logs are kept under `.lake/comparator-logs/`.

## Continuous integration

`.github/workflows/build.yml` runs the source audit, builds the library, fails on an incomplete
proof and runs the axiom audit. `.github/workflows/comparator.yml` builds the pinned comparator
tools and runs both comparator pairs.
