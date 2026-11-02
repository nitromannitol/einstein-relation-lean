# Independent statement comparisons

Theorems 1.1 and 1.2 and Proposition 7.1 of the paper are restated here using nothing but Mathlib.
Each restatement is proved from the library, and
[leanprover/comparator](https://github.com/leanprover/comparator) checks that the statement proved from
the library is the restated one. A reader who wants to know what these results say, and what they
assume, therefore needs only the corresponding challenge and the vocabulary, not the library.

## How a pair is built and checked

| File | Role |
| --- | --- |
| `<Pair>/Challenge.lean` | The statement, with exactly one `sorry`, the proof of the final theorem. Its module docstring states the result in words and lists the literature inputs that its proof uses. **This is the file to read**, together with the vocabulary it imports. |
| `Vocabulary/` | The definitions that the statements use, and the literature inputs with their statements, restated: one file per library module that declares one of them. These files import only Mathlib and each other. |
| `<Pair>/Solution.lean` | The proof. It imports the library, states the same theorem and proves it with the library theorem. |
| `<Pair>/comparator.json` | The comparator configuration: the challenge and solution modules, the theorem name and the permitted axioms, namely `propext`, `Classical.choice`, `Quot.sound` and the literature inputs of the result. |
| `Axioms.lean` | The axiom report of all twenty-one numbered results, checked by `scripts/check_axioms.py`. |

**What the vocabulary restates.** The definitions are restated under their library names, copied from the
library source in the context (`namespace`, `open`, `variable`, local attributes) in which they are
declared there, together with the instances declared next to them and the lemmas that some definitions
need. The literature inputs are restated as the same named axioms, with their statements. The
comparator compares each of them with the library's declaration of the same name, so a definition or an
input that differs from the library's, even in an instance or an auxiliary proof, is rejected.

**Why one vocabulary file per library module.** Lean resolves type-class instances from the modules that
a file imports, and it shares an auxiliary proof between declarations of one file when they prove the
same proposition. Each vocabulary file therefore restates one library module and imports exactly the
Mathlib modules that this library module sees, together with the vocabulary files of the library
modules below it. Each challenge imports the vocabulary and the Mathlib modules seen by the library
module that states its result.

## Running the check

```bash
./scripts/run_comparators.sh --palomar
```

builds the library and the audit modules and runs the three pairs with the comparator, which replays
each solution with Lean's kernel and with NanoDa, both bundled with the pinned toolchain; it needs
`bubblewrap`. The con-ron kernel, in its verified mode, declines every proof that uses an axiom beyond
the standard three, so it cannot check results that use the literature inputs and is not configured. The
[comparator workflow](../.github/workflows/comparator.yml) runs the same check on every push to `main`.
