# Independent statement comparisons

Theorem 1.2 and Proposition 7.1 of the paper are restated here using nothing but Mathlib.
Each restatement is then proved from the library, and
[leanprover/comparator](https://github.com/leanprover/comparator) checks that the statement proved
from the library is the restated one. A reader who wants to know what these two theorems say,
and what they assume, therefore needs only the corresponding challenge, not the library.

## How a pair is built and checked

Each subdirectory is one comparator pair:

| File | Role |
| --- | --- |
| `Challenge.lean` | The statement, with exactly one `sorry`, the proof of the final theorem. Its module docstring states the theorem in words. **This is the file to read**, together with the vocabulary it imports. |
| `Vocabulary/` | The definitions that the statement uses, restated: one file per library module that contains such a definition. These files import only Mathlib and each other, and contain no `sorry`. |
| `Solution.lean` | The proof. It imports the library, states the same theorem and proves it with the library theorem. |
| `comparator.json` | The comparator configuration: the challenge and solution modules, the theorem name, and the permitted axioms. |

**What the challenge restates.** The statement of each theorem has two parts: the literature
inputs, which are Prop-valued hypotheses, and the statement of the result. The challenge restates
both, with all the definitions they depend on: the environment laws of Assumption 1.1, the
diffusion of Gantert, Mathieu and Piatnitski (2012, Section 7), velocities and diffusivities,
and the vocabulary of the literature inputs (correctors, heat kernels, coefficient laws in the
normalization of Armstrong, Kuusi and Mourrat, and the regeneration construction). The
definitions are restated **under their library names** (namespace `EinsteinRelation`), copied from
the library source, in the context (`namespace`, `open`, `variable`) in which they are declared
there. The instances declared next to them, and the lemmas that some definitions need (for
example that a set is a submodule), are restated with their proofs.

**Why one vocabulary file per library module.** Lean resolves type-class instances from the
modules that a file imports, and it shares an auxiliary proof between declarations of one file
when they prove the same proposition. A single file restating everything would import more of
Mathlib than some library modules do, and would share auxiliary proofs across what are separate
library modules, so some restated definitions would differ from the library's as terms. Each
vocabulary file therefore restates one library module and imports exactly the Mathlib modules
that this library module sees, together with the vocabulary files of the restated library modules
that it imports. `Challenge.lean` imports the vocabulary and the Mathlib modules seen by
`EinsteinRelation/MainTheorems.lean`.

**What the comparator checks.** Because the names agree, the solution needs no translation layer:
it states the theorem of the challenge in the library's environment and proves it by applying the
library theorem. The comparator checks, independently of how the solution was produced, that the
theorem of the solution has exactly the type of the theorem of the challenge, and that every
definition that this type depends on is the same declaration in the challenge and in the solution
environment. So the restated definitions are exactly the library's definitions, and the library
theorem proves exactly the challenge statement.

`comparator.json` permits exactly `propext`, `Classical.choice` and `Quot.sound`. The key
`enable_nanoda` is set, so the comparator also replays the solution with NanoDa. See the
[README](../README.md#running-the-comparators) for how to run the pairs.

## The pairs

| Pair | Paper statement | Library declaration |
| --- | --- | --- |
| [`MobilityRate`](MobilityRate/) | Theorem 1.2, label `t.main` | `EinsteinRelation.mobility_rate` |
| [`SharpExample`](SharpExample/) | Proposition 7.1, label `sharp.example` | `EinsteinRelation.mobility_rate_sharp` |

The other numbered results of the paper have no separate pair; their statements are in
[`EinsteinRelation/MainTheorems.lean`](../EinsteinRelation/MainTheorems.lean) and their axiom
reports are checked by the build.

## Conventions shared by the challenges

- The theorem is stated for every `d ≥ 2` and every environment law satisfying Assumption 1.1
  (`EinsteinRelation.EnvironmentLaw`).
- Its hypotheses are the literature inputs used by the proof, in the order of the table in the
  [README](../README.md#assumed-literature-inputs), each a Prop-valued definition whose
  docstring records its source.
- Norms are Euclidean (Frobenius for matrices). Real-valued definitions are total, so analytic
  statements carry the integrability and measurability conditions that they need.
