# Quantitative Einstein relation for reversible diffusions in a random environment

A machine-checked **Lean 4** formalization of the paper

> Ahmed Bou-Rabee and Ruizhe Xu,
> *Quantitative Einstein relation for reversible diffusions in a random environment*
> (arXiv:2605.26082).

The paper's source, bibliography, figure and compiled PDF are included under
[`paper/`](paper/). Every numbered result of the paper, twenty-one in all, is proved **for every
random environment that satisfies the paper's Assumptions 1.1 and 1.2**, from thirteen results of the
literature. These literature inputs are stated in Lean as named axioms, each with its source; they
are listed in [Assumed literature inputs](#assumed-literature-inputs). The axiom report of every numbered
result lists `propext`, `Classical.choice`, `Quot.sound` and inputs from that list, and nothing else; the
library contains no `sorry`.

The development is built on [mathlib](https://github.com/leanprover-community/mathlib4) and on the
public libraries [MarkovProcess](https://github.com/scottnarmstrong/MarkovProcess),
[CoarseGraining](https://github.com/scottnarmstrong/CoarseGraining),
[EllipticRegularityLean](https://github.com/scottnarmstrong/EllipticRegularityLean),
[SuperdiffusionCLT](https://github.com/scottnarmstrong/SuperdiffusionCLT) and
[subdiffusive-process](https://github.com/nitromannitol/subdiffusive-process).

[![CI](https://github.com/nitromannitol/einstein-relation-lean/actions/workflows/build.yml/badge.svg?branch=main)](https://github.com/nitromannitol/einstein-relation-lean/actions/workflows/build.yml)
[![Comparator audit](https://github.com/nitromannitol/einstein-relation-lean/actions/workflows/comparator.yml/badge.svg?branch=main)](https://github.com/nitromannitol/einstein-relation-lean/actions/workflows/comparator.yml)

## What is proved

The paper studies a reversible diffusion `X` in a random environment `(a₀, V)` on `ℝᵈ`, `d ≥ 2`,
pushed by a signed force `λ ∈ ℝ` in the direction `e₁`. Its generator is

> `𝓛^λ f = ½ e^{2V} ∇·(e^{−2V} a₀ ∇f) + λ a₀ e₁·∇f`.

For `λ ≠ 0` the diffusion has a deterministic velocity `ℓ_X(λ) = lim X(t)/t`; without force it
satisfies an invariance principle with a deterministic diffusivity matrix `Σ_X`. The main result is a
uniform expansion of the velocity in the force, up to and including the critical order `d + 1`:

**Theorem 1.1 (`t:expansion`).** For every `d ≥ 2` and every structural data set `𝒟` there are
`C < ∞` and `λ_* ∈ (0, e⁻¹]` such that every law satisfying Assumptions 1.1 and 1.2 has
deterministic vectors `b₁, …, b_{d+1}, c` with `b₁ = Σ_X e₁`, `Σⱼ |bⱼ| + |c| ≤ C` and, for
`0 < |λ| ≤ λ_*`,

> `|ℓ_X(λ) − Σ_{j=1}^{d+1} bⱼ λʲ − c S_d(λ)| ≤ C |λ|^{d+1} ω(|λ|)`,

where `S_d(λ) = λ^{d+1} log(1/|λ|)` for even `d`, `S_d(λ) = λ|λ|ᵈ` for odd `d`, and
`ω(s) = exp(−√(log(1/s)))`.

Its first-order consequence is the quantitative Einstein relation
`|ℓ_X(λ)/λ − Σ_X e₁| ≤ Cλ` (Theorem 1.2), and Proposition 7.1 shows that the order is optimal.
The model is stated precisely in [Standing assumptions and scope](#standing-assumptions-and-scope).

Each numbered result is stated, with its paper label and number, in its own file under
[`EinsteinFull/Frozen/`](EinsteinFull/Frozen/), and is proved there from the provider in
[`EinsteinFull/Proofs/`](EinsteinFull/Proofs/).
[`EinsteinFull/MainTheorems.lean`](EinsteinFull/MainTheorems.lean) imports all of them.

| Paper | Lean declaration | Content |
| --- | --- | --- |
| Theorem 1.1 (`t:expansion`) | `EinsteinFull.Frozen.uniform_small_force_expansion` | The uniform expansion of the velocity through order `d + 1`, with the critical term `c S_d(λ)` and error `C\|λ\|^{d+1} ω(\|λ\|)`. |
| Theorem 1.2 (`t.main`) | `EinsteinFull.Frozen.mobility_rate` | The quantitative Einstein relation `\|ℓ_X(λ)/λ − Σ_X e₁\| ≤ Cλ`. |
| Proposition 2.1 (`p:response`) | `EinsteinFull.Frozen.response` | Exact response: the resolvent averages `ν_{λ,s}` and the velocity through time correlations of local fields. |
| Lemma 3.1 (`rt:factorization`) | `EinsteinFull.Frozen.environmental_factorization` | Environmental factorization at the first regeneration time. |
| Lemma 3.2 (`rt:renewal`) | `EinsteinFull.Frozen.uniform_lattice_renewal` | The uniform lattice renewal estimate and exponential moments of the regeneration times. |
| Proposition 3.3 (`rt:local-mixing`) | `EinsteinFull.Frozen.local_mixing` | Growing-support covariance mixing: `\|𝔼[F P_t^λ G]\| ≤ C e^{CA − cλ²t} ‖F‖_p ‖G‖_p` for fields measurable in `B_{A/\|λ\|}`. |
| Proposition 3.4 (`p:tail`) | `EinsteinFull.Frozen.correlation_tail` | Exponential tail of the time correlations of the commutator and the clock. |
| Proposition 4.1 (`p:gauge`) | `EinsteinFull.Frozen.gauge` | The unitary gauge `U_λ f = e^{λx₁} f` and the conjugated forced generator. |
| Proposition 4.2 (`p:scalar`) | `EinsteinFull.Frozen.forced_scalar_decay` | Forced scalar decay in `Lᵖ`, `2 ≤ p < ∞`. |
| Lemma 4.3 (`l:forced-local`) | `EinsteinFull.Frozen.forced_local_estimates` | Local estimates with force for the evolved endpoints. |
| Lemma 4.4 (`l:forced-flux`) | `EinsteinFull.Frozen.forced_weak_flux` | The centered weak flux of the forced solution. |
| Proposition 5.1 (`p:covariance`) | `EinsteinFull.Frozen.covariance_scaling` | The joint covariance of the commutator and the clock: white-noise limit with a power rate. |
| Proposition 6.1 (`h:forced`) | `EinsteinFull.Frozen.forced_comparison` | Forced comparison with the homogeneous drift–diffusion. |
| Proposition 6.2 (`p:late`) | `EinsteinFull.Frozen.late_force_replacement` | Late force replacement. |
| Lemma 6.3 (`l:finite-xi`) | `EinsteinFull.Frozen.finite_time_unforced_commutator` | The finite-time unforced commutator. |
| Lemma 6.4 (`l:late-propagation`) | `EinsteinFull.Frozen.late_homogeneous_propagation` | Late homogeneous propagation. |
| Proposition 6.5 (`p:endpoint-comparison`) | `EinsteinFull.Frozen.endpoint_comparison` | Endpoint comparison at the late intermediate time. |
| Proposition 6.6 (`p:profile`) | `EinsteinFull.Frozen.correlation_profile` | The Gaussian profile `t^{−1−d/2}(u₀ + u₂z²)e^{−γz²}` of the correlations, `z = λ√t`. |
| Proposition 6.7 (`p:integration`) | `EinsteinFull.Frozen.kernel_integration` | Integration of the correlation kernel: the ordinary coefficients and the critical term. |
| Proposition 7.1 (`sharp.example`) | `EinsteinFull.Frozen.sharp_example` | Smooth environments for which `((ℓ_X(λ)/λ − Σ_X e₁)·e₁)/λ → c₀ > 0`. |
| Lemma A.1 (`app:factorization`) | `EinsteinFull.Frozen.regeneration_factorization` | Regeneration factorization for supports growing on the scale `\|λ\|⁻¹`. |

## Standing assumptions and scope

1. **Every theorem is about every law.** An environment law is a structure
   `EinsteinRelation.EnvironmentLaw d Λ₀ r₀`: a probability measure on pairs `(a₀, V)` of
   continuous fields satisfying (S1)–(S5) of Assumption 1.1, namely symmetric uniform ellipticity
   with constant `Λ₀`, `|V| ≤ Λ₀`, `Λ₀`-Lipschitz regularity, stationarity, and finite range of
   dependence `r₀`. Assumption 1.2 is `EinsteinFull.HasSmoothBounds D Q`: almost surely, `a₀` and
   `V` are smooth with `‖∇ᵏa₀‖_∞ + ‖∇ᵏV‖_∞ ≤ Λ_k` for every `k ≥ 1`. The structural data `𝒟` of
   the paper are `EinsteinFull.StructuralData d`. The results of Sections 3–6 are stated, as in
   the paper, under both assumptions.
2. **Axioms and incomplete proofs.** The library contains no `sorry`, no `admit` and no
   `native_decide`. Beyond `propext`, `Classical.choice` and `Quot.sound`, the axiom reports of the
   numbered results contain only the thirteen literature inputs below. Each one states a result of the
   cited literature in Lean and was checked against its source in an independent model review; the
   axiom report of each numbered result lists exactly the inputs that its proof uses.
3. **The formal diffusion.** The diffusion is specified by its martingale problem: a family of
   quenched path laws `P` is admissible (`IsSignedPhysicalFamily`) when, for every force `λ` and
   almost every environment, the law started at the origin solves the martingale problem of
   `𝓛^λ`. The velocity and the diffusivity are defined by their limit properties
   (`HasQuenchedVelocity`, `HasDiffusivity`). The theorems hold for every admissible family, every
   velocity and every diffusivity with these properties; the existence of the velocity and of the
   diffusivity, which the paper cites from the literature, is not asserted by the statements. No
   stochastic differential equation appears.
4. **Order of quantifiers.** The constants of Theorems 1.1 and 1.2 are chosen from the structural
   data before the law; in Theorem 1.1 the coefficients `bⱼ` and `c` are chosen from the law
   before the diffusion and the force.
5. **Norms and conventions.** Vectors and matrices are measured in the Euclidean norm and the
   Euclidean operator norm. Lean's real-valued definitions are total (division by zero,
   `Real.log 0` and non-integrable integrals have conventional values), so analytic statements
   carry their positivity, integrability and measurability hypotheses explicitly.

## Assumed literature inputs

| Lean name | Statement | Source | Results that use it |
| --- | --- | --- | --- |
| `akm_averaged_corrector` | Gaussian averages of the corrector gradient, flux and energy density | AKM, Theorem 4.1 | 5 |
| `akm_block_boundary` | boundary estimate of the localized block energies | AKM, Lemma 5.29 | 5 |
| `akm_block_change` | change of the localized block energies | AKM, Lemma 5.29 | 5 |
| `akm_block_clt` | central limit estimate of the localized block energies | AKM, Lemma 5.29 | 5 |
| `akm_coarsened_coefficient_estimates` | coarsened coefficient estimates | AKM, Definition 5.23 and Lemma 5.24 | 7 |
| `akm_localized_energy` | localized energy minimizers and their measurability | AKM, Section 4.4 and Theorem 4.6(iv) | 5 |
| `akm_negative_sobolev` | negative Sobolev bound for the corrector gradient and flux | AKM, Theorem 4.24 | 7 |
| `akm_sublinear_correctors` | sublinearity of the scalar and flux correctors above a minimal radius | AKM, Lemma 3.17, Lemma 6.1 and Proposition 6.2 | 13 |
| `akm_white_noise_exists` | existence of scalar white noise | AKM, Proposition 5.14 | 1 |
| `bass_continuous_elliptic_well_posed` | well-posedness of the martingale problem with continuous elliptic diffusion and bounded drift | Bass, Chapter VI, Theorem 4.3 | 18 |
| `dfgw_invariance` | the invariance principle for reversible Markov processes | DFGW, Theorem 2.2 | 4 |
| `gantert_regeneration_tail` | the no-return bound and exponential tail of the first regeneration time | GMP, Lemma 5.8 | 8 |
| `gmp_velocity` | the quenched law of large numbers with positive longitudinal velocity | GMP, Section 2.3 and Proposition 5.9 | 4 |

AKM: S. Armstrong, T. Kuusi and J.-C. Mourrat, *Quantitative Stochastic Homogenization and Large-Scale
Regularity*, Grundlehren 352, Springer, 2019. GMP: N. Gantert, P. Mathieu and A. Piatnitski, *Einstein
relation for reversible diffusions in a random environment*, Comm. Pure Appl. Math. 65 (2012), 187–228.
DFGW: A. De Masi, P. A. Ferrari, S. Goldstein and W. D. Wick, *An invariance principle for reversible Markov
processes*, J. Stat. Phys. 55 (1989), 787–855. Bass: R. F. Bass, *Diffusions and Elliptic Operators*,
Springer, 1997. The library also declares `gmp_dirichlet_lower` (GMP, Lemma 5.3), which no numbered
result uses.

The precise Lean statement of each input is in `EinsteinFull/External/` (and, for the regeneration
tail, `EinsteinFull/Frozen/GantertRegenerationTail.lean`), with the pinpoint references in its
docstring.

## Guarantees

- **No `sorry`.** The library has none. The three comparator challenges under
  [`EinsteinFullAudit/`](EinsteinFullAudit/) each contain one intentional statement-level `sorry`,
  which the corresponding solution proves.
- **Axioms.** The axiom report of each of the twenty-one numbered results lists `propext`,
  `Classical.choice`, `Quot.sound` and literature inputs from the table above, and nothing else.
  [`EinsteinFullAudit/Axioms.lean`](EinsteinFullAudit/Axioms.lean) prints the reports and
  `scripts/check_axioms.py` fails on any other axiom, on `sorryAx`, or on a missing report.
- **Builds from a clean checkout.** `lake build` of this tree in a fresh build directory compiled
  14,471 jobs with no errors.
- **Independent check of the statements.** Theorems 1.1 and 1.2 and Proposition 7.1 are restated in
  [`EinsteinFullAudit/`](EinsteinFullAudit/) using mathlib alone, one challenge per result. A shared
  vocabulary restates, under their library names, every definition that the statements use and the
  literature inputs that their proofs use, with their full statements. Each solution proves its
  restatement from the library, and [leanprover/comparator](https://github.com/leanprover/comparator)
  checks that the statement is proved with only the permitted axioms (the three standard ones and those
  literature inputs), that every definition and every literature input agrees with the library's, and
  replays the proof through independent implementations of the Lean kernel. See
  [`EinsteinFullAudit/README.md`](EinsteinFullAudit/README.md).
- **Pinned toolchain and dependencies.** Lean and mathlib `v4.35.0-rc2`; the libraries above at the
  exact revisions recorded in [`lake-manifest.json`](lake-manifest.json).
- **The paper is part of the repository**, in [`paper/`](paper/).

## Size

The library contains 2,327 Lean files with 684,549 physical lines, on top of mathlib and the
libraries above. The comparator sources are counted separately.

## Building

Install [elan](https://github.com/leanprover/elan). The toolchain is pinned in
[`lean-toolchain`](lean-toolchain), and Lake fetches the dependencies.

```bash
lake exe cache get   # prebuilt mathlib
lake build
```

The source dependencies have no prebuilt cache, so the first build compiles them as well as the
library. With the dependencies already built, a fresh build of the library took about 23
minutes on an Intel Core Ultra 9 285 machine (24 threads).

To reproduce the axiom reports:

```bash
lake env lean EinsteinFullAudit/Axioms.lean 2>&1 | tee .lake/axioms-audit.log
python3 scripts/check_axioms.py .lake/axioms-audit.log
```

To build the paper, run `latexmk -pdf main.tex` in [`paper/`](paper/).

## Running the comparators

Each comparator pair has a configuration `EinsteinFullAudit/<Pair>/comparator.json`. To run the
three pairs locally with the tools bundled with the pinned Lean toolchain:

```bash
./scripts/run_comparators.sh --palomar
```

This needs `bubblewrap` and, on Linux, a memory-mapping limit of at least 131072
(`sudo sysctl -w vm.max_map_count=262144`). Logs are kept under `.lake/comparator-logs/`.

There are two continuous-integration workflows: **CI** builds the library and checks the axiom
reports; **Comparator audit** checks the three challenge/solution pairs.

## Repository layout

```text
EinsteinFull.lean               the root module
EinsteinFull/
  MainTheorems.lean             imports the twenty-one numbered results
  Frozen/                       the statements of the numbered results, the definitions they use,
                                and the regeneration-tail input
  Proofs/                       the proof of each numbered result, composed from the steps below
  Closures/                     the composition of the proof steps, in dependency order
  Blueprint/                    one Lean proposition per step of the proofs in the paper, and its proof
  Calculus/, Work/              supporting theory: semigroups, heat kernels, correctors, couplings
  Regeneration/                 the regeneration construction and its renewal structure
  External/                     the literature inputs
vendor/EinsteinRelation/        the blueprint library: environments, diffusions, generators
vendor/DeGiorgi/                De Giorgi–Nash–Moser theory
EinsteinFullAudit/              the axiom report and the mathlib-only comparator pairs, with their
                                vocabulary
paper/                          the paper: source, bibliography, figure, PDF
scripts/                        axiom check and comparator runner
.github/workflows/              build and comparator workflows
```

## How this was built

The Lean code was written with AI assistance, using models from Anthropic (Claude) and OpenAI (GPT)
and, for some auxiliary lemmas, Mistral (Leanstral), under the direction of the authors. Every proof
is checked by the Lean kernel. The models, tooling and review process are disclosed in
[`formalization.yaml`](formalization.yaml), following the
[mathlib-initiative](https://github.com/mathlib-initiative/formalization.yaml) standard.

## Authors and citation

The paper and the Lean development are by **Ahmed Bou-Rabee** and **Ruizhe Xu**. To cite them, use
[`CITATION.cff`](CITATION.cff).

## License

The Lean development is licensed under the Apache License 2.0; see [`LICENSE`](LICENSE). The paper in
[`paper/`](paper/) is included with its authors' permission; its publication licence is not set by
this software licence.
