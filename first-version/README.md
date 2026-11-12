# Quantitative Einstein relation for reversible diffusions in a random environment

A machine-checked **Lean 4** formalization of the paper

> Ahmed Bou-Rabee and Ruizhe Xu,
> *Quantitative Einstein relation for reversible diffusions in a random environment*
> (preprint).

The paper's source, bibliography, figure and compiled PDF are included under
[`paper/`](paper/). Every numbered result of the paper except Conjecture 1.3 is stated and
proved **for every random environment that satisfies the paper's Assumption 1.1**,
**conditionally on thirty results from the literature**: twenty-nine results that the paper
cites, and the Fukushima decomposition of Dirichlet-form theory, which the paper uses through
the cited work of Gantert, Mathieu and Piatnitski (2012). These literature inputs are explicit
hypotheses of the Lean theorems: they are neither axioms nor `sorry`, and nothing in this
repository asserts them. They are listed, with their sources, in
[Assumed literature inputs](#assumed-literature-inputs).

The development is built on [mathlib](https://github.com/leanprover-community/mathlib4) and on
[DeGiorgi](https://github.com/nitromannitol/DeGiorgi), a Lean library of De Giorgi–Nash–Moser
theory, which proves two results that would otherwise be literature inputs.

[![CI](https://github.com/nitromannitol/einstein-relation-lean/actions/workflows/build.yml/badge.svg?branch=main)](https://github.com/nitromannitol/einstein-relation-lean/actions/workflows/build.yml)
[![Comparator audit](https://github.com/nitromannitol/einstein-relation-lean/actions/workflows/comparator.yml/badge.svg?branch=main)](https://github.com/nitromannitol/einstein-relation-lean/actions/workflows/comparator.yml)

## What is proved

The paper studies a reversible diffusion `X` in a random environment `(a₀, V)` on `ℝᵈ`, `d ≥ 2`,
pushed by a constant force of magnitude `λ > 0` in the direction `e₁`. Its generator is

> `𝓛^λ f = ½ e^{2V} ∇·(e^{−2V} a₀ ∇f) + λ a₀ e₁·∇f`.

At force `λ` the diffusion has a deterministic velocity `ℓ_X(λ) = lim X(t)/t`; without force it
satisfies an invariance principle with a deterministic diffusivity matrix `Σ_X`. The Einstein
relation `ℓ_X(λ)/λ → Σ_X e₁` as `λ ↓ 0` was proved by Gantert, Mathieu and Piatnitski (2012). The
paper proves the optimal rate `|ℓ_X(λ)/λ − Σ_X e₁| ≤ Cλ` (Theorem 1.2) and shows that the rate is
attained (Proposition 7.1). The model is stated precisely in
[Standing assumptions and scope](#standing-assumptions-and-scope).

All results are stated and proved in
[`EinsteinRelation/MainTheorems.lean`](EinsteinRelation/MainTheorems.lean).

| Paper | Lean declaration | Content |
| --- | --- | --- |
| Theorem 1.2 (`t.main`) | `EinsteinRelation.mobility_rate` | The quantitative Einstein relation `\|ℓ_X(λ)/λ − Σ_X e₁\| ≤ Cλ`. |
| Lemma 3.1 (`regen.renewal`) | `EinsteinRelation.regeneration_renewal` | The regeneration cycles after the first are distributed as the first, conditioned on no backtracking. |
| Proposition 3.2 (`regen.occupation`) | `EinsteinRelation.regeneration_occupation` | Occupation-time and resolvent bounds for local functions of the environment seen from the particle. |
| Lemma 4.1 (`entropy.fisher`) | `EinsteinRelation.entropy_fisher_bound` | The Fisher information of the resolvent density `ρ_s` is at most `4Λλ²`. |
| Lemma 4.2 (`entropy.divergence`) | `EinsteinRelation.entropy_divergence_bound` | `\|𝔼[Dρ_s·F]\| ≤ Cλ‖F‖_{L^{2p}}` for local fields `F`, and integration by parts. |
| Lemma 4.3 (`entropy.resolvent`) | `EinsteinRelation.entropy_resolvent_bound` | The resolvent identity and the bound `\|𝔼[ρ_s h]\| ≤ Cs‖f‖ + Cλ‖G‖` when `𝓛^λ f = h + D·G`. |
| Lemma 5.1 (`corrector.moments`) | `EinsteinRelation.corrector_moments` | Moments of the oscillations of the scalar and flux correctors and of the corrector gradient. |
| Lemma 5.2 (`corrector.conditional`) | `EinsteinRelation.corrector_conditional` | Conditional localization of the corrector gradient (`R^{−d/2}`) and, in `d = 2`, of the centred corrector values. |
| Proposition 5.3 (`corrector.local`) | `EinsteinRelation.corrector_local` | Local correctors on `B_{33R}` with flux error and gradient error `O(R⁻¹)`. |
| Proposition 6.1 (`scalar.decomposition`) | `EinsteinRelation.scalar_decomposition` | Dyadic decomposition of local scalar fields and the response bound `C(sR + λ + λ²R + R⁻¹)`. |
| Proposition 7.1 (`sharp.example`) | `EinsteinRelation.mobility_rate_sharp` | Smooth environments for which `((ℓ_X(λ)/λ − Σ_X e₁)·e₁)/λ → c > 0`. |

Assumption 1.1 (`a.environment`) is the structure `EinsteinRelation.EnvironmentLaw`.
Conjecture 1.3 is not formalized. [`CORRESPONDENCE.md`](CORRESPONDENCE.md) maps every numbered
result and every object of the statements to its Lean declaration and file.

**Theorem 1.2 (`t.main`).** Assume the 27 literature inputs marked 1.2 in the table below. Let
`d ≥ 2` and `Λ₀, r₀ ∈ ℝ`. There are `C < ∞` and `λ_* > 0`, depending only on `d`, `Λ₀` and `r₀`,
such that the following holds for every probability law `Q` of environments satisfying
Assumption 1.1 with the constants `Λ₀` and `r₀`. Let `P` be a family of quenched path laws such
that, for every `λ ∈ [0, 1]` and `Q`-almost every environment, `P λ` started at the origin is the
law of the diffusion of Gantert, Mathieu and Piatnitski (2012, Section 7) in that environment. Let
`Σ_X` be a matrix such that the rescaled unforced path `ε X⁰(ε⁻² ·)`, under the annealed law,
converges in law as `ε ↓ 0` to a centred Brownian motion with covariance `Σ_X`. Let
`0 < λ ≤ λ_*`, and let `ℓ` be a vector such that, for `Q`-almost every environment, almost every
path of `P λ` from the origin satisfies `X(t)/t → ℓ`. Then

> `|ℓ/λ − Σ_X e₁| ≤ Cλ`  (Euclidean norm).

**Proposition 7.1 (`sharp.example`).** Assume the 29 literature inputs marked 7.1 in the table
below. For every `d ≥ 2` there are constants `Λ₀, r₀`, a law `Q` of environments satisfying
Assumption 1.1 with these constants whose fields `a₀` and `V` are almost surely `C^∞`, and
`c > 0`, such that the following holds. For every family `P` of quenched path laws that is, as
above, the diffusion of Gantert, Mathieu and Piatnitski for `Q`, every diffusivity `Σ_X` of the
unforced diffusion as above, and every function `λ ↦ ℓ(λ)` such that `ℓ(λ)` is the quenched
velocity of `P λ` for every `λ ∈ (0, 1]`,

> `((ℓ(λ)/λ − Σ_X e₁) · e₁) / λ → c`  as `λ ↓ 0`.

## Standing assumptions and scope

1. **Every theorem is about every environment.** Assumption 1.1 is the structure
   `EinsteinRelation.EnvironmentLaw d Λ₀ r₀`: a probability measure on pairs `(a₀, V)` of
   continuous fields on `ℝᵈ` (a matrix field and a scalar field) with `Λ₀ ≥ 1` and `r₀ ≥ 1`,
   such that almost surely (S1) `a₀(x)` is symmetric with
   `Λ₀⁻¹|ξ|² ≤ ξ·a₀(x)ξ ≤ Λ₀|ξ|²`, (S2) `|V| ≤ Λ₀`, (S3) `a₀` and `V` are `Λ₀`-Lipschitz (`a₀` in
   the Euclidean operator norm); and the law is (S4) invariant under every translation of `ℝᵈ`
   and (S5) of finite range: the restrictions to two Borel sets at distance greater than `r₀`
   are independent. Every result holds for every such law; Proposition 7.1 constructs one.
2. **Conditional on the literature inputs, and on nothing else.** Each theorem takes as
   hypotheses exactly the literature inputs that its proof uses (table below). They are
   Prop-valued definitions, stated in Lean as close to the cited statements as the
   formalization allows; the docstring of each definition records the source. The library
   contains no `sorry`, no `admit`, no `native_decide`, no `implemented_by` and no `axiom`, and
   the axiom report of each of the eleven theorems is exactly `propext`, `Classical.choice`,
   `Quot.sound`. A reader who does not accept an input can see from the table which results
   depend on it.
3. **The diffusion.** Following the paper (line 66 of `paper/main.tex`), the diffusion with
   Lipschitz coefficients is the process of Gantert, Mathieu and Piatnitski (2012, Section 7):
   the conservative Hunt process with continuous paths whose semigroup is that of the operator
   in the weak sense. In Lean, `IsGMPPhysicalFamily` requires that, for each force
   `λ ∈ [0, 1]` and almost every environment, the path law from the origin is that of a
   `GantertFixedEnvironmentRealization`: a continuous-path law whose one-time marginals and
   ordered finite-dimensional distributions are given by a Markov semigroup with a heat-kernel
   density, reversible for `physicalReversibleMeasure`, whose closed form has the weighted `H¹`
   domain and the energy of Gantert, Mathieu and Piatnitski (2012, (7.1)). No stochastic
   differential equation, Brownian motion or Itô integral appears in the statements. The
   time-changed diffusion `Y^λ` of Section 2 of the paper is described in the same way
   (`IsGMPReducedFamily`).
4. **Velocity and diffusivity.** `HasQuenchedVelocity` is the almost sure limit of `X(t)/t`
   for almost every environment. `HasDiffusivity` is the annealed invariance principle: weak
   convergence of `ε X⁰(ε⁻² ·)` on continuous paths (with the topology of locally uniform
   convergence) to a centred Brownian law, specified by its Gaussian finite-dimensional
   characteristic functions, with a symmetric positive semidefinite covariance.
5. **Universal statements.** Theorem 1.2 and Proposition 7.1 quantify over every diffusion
   family, every diffusivity and every velocity with these properties; they do not assert that
   such objects exist. Their existence is part of the cited work of Gantert, Mathieu and
   Piatnitski, and inputs 28 and 29 below (existence of the family and of the velocity) are used
   in the proof of Proposition 7.1. Velocities are unique when they exist
   (`HasPathVelocity.unique`).
6. **Lemma 5.2.** Lemma 5.2 assumes that the scalar and flux correctors are almost surely
   continuous, as the paper states. Without that hypothesis the point values in its
   two-dimensional conclusion are not determined by the corrector classes.
7. **Quantifier forms.** The intermediate results are stated in the form fixed for the
   formalization. Where the paper writes "there exist `p > 1` and `C`", the Lean statements
   give a threshold `p₀ > 1` and a constant `C` for every `p ≥ p₀`, and they make explicit the
   scale `l₀` of the regeneration construction and its measurability conditions. Lemmas 4.1–4.3
   and Proposition 6.1 take the stationarity of the reduced reference law as an argument
   (`hQ : IsStationary (reducedReferenceLaw Q)`), because their weak derivatives are defined
   with respect to it; it holds for every environment law (`Clock.isStationary_reducedReferenceLaw`).
8. **Conventions.** Vectors are `Fin d → ℝ`; norms of vectors and matrices in estimates are the
   Euclidean norm and the Frobenius norm; balls are Euclidean; `e₁` is
   `unitVector ⟨0, _⟩`. Lean's real-valued definitions are total (division by zero,
   non-integrable integrals and `ENNReal.toReal ∞` have conventional values), so analytic
   conclusions carry the integrability and measurability statements that they need.
9. **Fixed statements.** The statements of the eleven results were fixed before their proofs
   were written. The definitions they use are under
   [`EinsteinRelation/Frozen/`](EinsteinRelation/Frozen/) and in the modules these import. The
   statements in `MainTheorems.lean` are copied byte for byte from the fixed statements and are
   preceded by the literature inputs that the proofs use.

## Assumed literature inputs

AKM: S. Armstrong, T. Kuusi and J.-C. Mourrat, *Quantitative Stochastic Homogenization and
Large-Scale Regularity*, Grundlehren 352, Springer, 2019. GT: D. Gilbarg and N. S. Trudinger,
*Elliptic Partial Differential Equations of Second Order*, Classics in Mathematics, Springer,
2001 (reprint of the 1998 edition). FOT: M. Fukushima, Y. Oshima and M. Takeda, *Dirichlet Forms
and Symmetric Markov Processes*, 2nd edition, de Gruyter, 2011. GMP: N. Gantert, P. Mathieu and
A. Piatnitski, *Einstein relation for reversible diffusions in a random environment*, Comm. Pure
Appl. Math. 65 (2012), 187–228. DFGW: A. De Masi, P. A. Ferrari, S. Goldstein and W. D. Wick,
J. Stat. Phys. 55 (1989), 787–855. Shen (2003): L. Shen, *On ballistic diffusions in random
environment*, Ann. Inst. H. Poincaré Probab. Statist. 39 (2003). Page numbers are printed page
numbers. All predicates are in the namespace `EinsteinRelation`; the column *Hypothesis* gives
the name of the hypothesis in the theorems, and *Used by* lists the results that take it.

| # | Source | Content | Lean predicate | Hypothesis | Used by |
| --- | --- | --- | --- | --- | --- |
| 1 | AKM Theorem 4.1, (4.5), p. 124 | stationary oscillation bound of the scalar corrector | `External.AKM.ScalarStationaryEstimate` | `h45` | 5.1, 5.2, 5.3, 6.1, 1.2, 7.1 |
| 2 | AKM Theorem 4.1, (4.6), p. 124 (dimension two) | normalized `L²` oscillation of the scalar corrector in the plane | `External.AKM.ScalarPlanarL2Estimate` | `h46` | 5.1, 5.2, 5.3, 6.1, 1.2, 7.1 |
| 3 | AKM Theorem 4.1, (4.7), p. 124 | difference of heat averages of the scalar corrector | `External.AKM.ScalarHeatDifferenceEstimate` | `h47` | 5.1, 5.2, 5.3, 6.1, 1.2, 7.1 |
| 4 | AKM Lemma 6.1, (6.8), p. 246 | gradient bound for the flux corrector | `External.AKM.FluxGradientEstimate` | `h68` | 5.1, 5.2, 5.3, 6.1, 1.2, 7.1 |
| 5 | AKM Proposition 6.2, (6.14), pp. 249–250 | stationary oscillation bound of the flux corrector | `External.AKM.FluxStationaryEstimate` | `h614` | 5.1, 5.2, 5.3, 6.1, 1.2, 7.1 |
| 6 | AKM Proposition 6.2, (6.15), p. 250, for radii `r ≥ 2` | normalized `L²` oscillation of the flux corrector in the plane | `External.AKM.FluxPlanarL2Estimate` | `h615` | 5.1, 5.2, 5.3, 6.1, 1.2, 7.1 |
| 7 | AKM Proposition 6.2, (6.16), p. 250 | difference of heat averages of the flux corrector | `External.AKM.FluxHeatDifferenceEstimate` | `h616` | 5.1, 5.2, 5.3, 6.1, 1.2, 7.1 |
| 8 | GT Theorem 8.32, (8.86), p. 210 (homogeneous case) | interior gradient estimate for weak solutions | `External.GilbargTrudinger.InteriorGradientEstimate` | `h832` | 5.1, 5.2, 5.3, 6.1, 1.2, 7.1 |
| 9 | GT Corollary 8.36, (8.91), p. 212, with the hypotheses of Theorem 8.32 | interior `C^{1,α}` regularity of weak solutions | `External.GilbargTrudinger.InteriorRegularRepresentative` | `h836` | 5.1, 5.2, 5.3, 6.1, 1.2, 7.1 |
| 10 | AKM Theorem 9.1, (9.7), p. 349, for the flow (9.2), p. 347 | decay of the parabolic flow defined by the heat kernel | `External.AKM.ParabolicSemigroupKernelDecay` | `hdecay` | 5.2, 5.3, 6.1, 1.2, 7.1 |
| 11 | AKM Remark 8.8, (8.25), p. 315 | large-scale gradient estimate for the parabolic flow | `External.AKM.ParabolicLargeScale` | `hreg` | 5.2, 5.3, 6.1, 1.2, 7.1 |
| 12 | AKM Theorem 3.3, (3.15)–(3.19), p. 75 | large-scale regularity above a random minimal scale | `External.AKM.EllipticLargeScale` | `hEll` | 5.2, 5.3, 6.1, 1.2, 7.1 |
| 13 | AKM Proposition E.1, (E.1)–(E.4) and (E.7)–(E.11), pp. 499–501 | existence and Gaussian bounds of the parabolic Green function | `External.AKM.ParabolicHeatKernel` | `hE1` | 5.2, 5.3, 6.1, 1.2, 7.1 |
| 14 | AKM (4.126), p. 173 (case `d = 2`), accompanying Theorem 4.24 | `H⁻²(B₁)` bound `O_s(Cε)` for the rescaled corrector gradient and centred flux, `d = 2` | `External.AKM.CorrectorWeakH2` | `hH2` | 5.3, 6.1, 1.2, 7.1 |
| 15 | AKM Theorem 4.1, (4.3), p. 124, at heat times `t ≥ 1` | decay `C (1 + t)^{-1/2}` of heat averages of the centred flux | `AKMFluxDecayLargeTime` | `hAKM` | 1.2 |
| 16 | FOT Theorem 5.5.5, p. 275, with (5.5.8)–(5.5.11), under (4.2.9), p. 165; for the GMP Section 7 processes (GMP p. 32 and Lemma 7.1, p. 33) | Fukushima decomposition of a `C¹` function of the diffusion | `FukushimaDecompositionInput` | `hFOT` | 4.1, 4.2, 4.3, 6.1, 1.2, 7.1 |
| 17 | GMP Proposition 7.2 and (7.4), pp. 33–34, with Hölder's inequality | Girsanov bound comparing forced and unforced endpoint laws | `GirsanovEndpointStep` | `hGir` | 3.2, 4.1, 4.2, 4.3, 6.1, 1.2, 7.1 |
| 18 | GMP pp. 8, 10 and 32; DFGW Section 6, (6.9)–(6.13) | invariance of the environment law for the unforced environment process | `UnforcedEnvironmentInvarianceStep` | `hInv` | 3.2, 4.1, 4.2, 4.3, 6.1, 1.2, 7.1 |
| 19 | GMP Section 7, p. 32, and (3.8)–(3.9), p. 10 | existence of the reduced (time-changed) diffusion family | `External.GMPReducedFamilyExistence` | `hRF` | 3.2, 4.1, 4.2, 4.3, 6.1, 1.2, 7.1 |
| 20 | GMP Proposition 5.4, p. 23, extended to measurable coefficients in Section 7, p. 32; kernel form of Shen (2003), Theorem 2.1, (2.8)–(2.9) | existence of the regeneration coupling | `GMPCouplingExistsV2Input` | `hE` | 3.2, 4.2, 4.3, 6.1, 1.2, 7.1 |
| 21 | GMP Lemmas 5.7 (p. 25) and 5.8 (p. 26) and (5.20), p. 25, with Section 7, p. 32 | no-backtracking probability and regeneration-time tails | `GMPCouplingTailsV2Input` | `hTail` | 3.1, 3.2, 4.2, 4.3, 6.1, 1.2, 7.1 |
| 22 | GMP proof of Proposition 7.2, pp. 34–35 | locality of the diffusion up to the exit time from an open set | `External.GMPKernelLocality` | `hLoc` | 3.1, 3.2, 4.2, 4.3, 6.1, 1.2, 7.1 |
| 23 | GMP pp. 5 and 10 | law of large numbers for the reduced diffusion, positive first component | `External.GMPReducedVelocityExistence` | `hRV` | 1.2, 7.1 |
| 24 | GMP Section 3, p. 10, and Section 7, p. 32 | time change between the physical and the reduced diffusion | `External.GMPTimeChangeLaw` | `hTC` | 1.2, 7.1 |
| 25 | GMP Section 2.3, p. 5 | positive first component of the physical velocity | `External.GMPPhysicalVelocityPositive` | `hPos` | 1.2, 7.1 |
| 26 | GMP p. 8 and p. 10 | ergodic limit of the clock of the unforced reduced diffusion | `External.GMPEnvironmentProcessErgodic` | `hErg` | 1.2, 7.1 |
| 27 | GMP Section 2.2, pp. 4 and 10 | invariance principle for the unforced reduced diffusion with covariance `ā` | `External.GMPReducedInvarianceAbar` | `hIP` | 1.2, 7.1 |
| 28 | GMP Section 7, p. 32, with the annealed law (2.5), p. 4 | existence of the physical diffusion family | `External.GMPPhysicalFamilyExistence` | `hPF` | 7.1 |
| 29 | GMP Section 2.3, p. 5 (citing Shen), and Section 7, p. 32 | law of large numbers for the physical diffusion | `External.GMPVelocityExistence` | `hVX` | 7.1 |
| 30 | AKM Definition 5.1, Proposition 5.14 and Remark 5.15, pp. 192 and 201–202 | existence of unit scalar white noise (used for every `d ≥ 2`) | `External.WhiteNoiseExistence` | `hW` | 7.1 |

Inputs 1–7 and 10–14 are stated, as in the book, for coefficient fields in its normalization
(AKM (0.6)–(0.11): ellipticity normalized below by one, `ℤᵈ`-stationarity, unit range of
dependence), with constants chosen before the coefficient field or its law; the library
transfers them to the reduced coefficient of the paper. Input 15 is stated directly for the
paper's reduced environment; its docstring records the rescaling from the book's setting, which
is part of the input. The white-noise input is stated for every `d ≥ 2`
(`∀ d, 2 ≤ d → WhiteNoiseExistence d`). FOT is not cited in the paper; it supplies the
decomposition of a function of the diffusion into a martingale and a drift integral, which the
paper uses through Gantert, Mathieu and Piatnitski (2012, Section 7).

**Former inputs that are proved.** Two results of Gilbarg and Trudinger used in Lemma 5.1 are
proved in this repository from the [DeGiorgi](https://github.com/nitromannitol/DeGiorgi)
library, and are therefore not hypotheses: the Poincaré inequality on balls, GT (7.45), p. 164
(`External.GilbargTrudinger.BallPoincareEstimate`, proved by
`Correctors.ballPoincareEstimate_of_deGiorgi`), and local boundedness of weak solutions, GT
Theorem 8.17, (8.46), p. 194 (`External.GilbargTrudinger.LocalBoundednessEstimate`, proved by
`Correctors.localBoundednessEstimate_of_deGiorgi`).

The library defines a few further Prop-valued statements of results from the literature (for
example `External.AKM.EnergyDensityEstimate`) that are hypotheses of intermediate lemmas only;
none of them is a hypothesis of the eleven theorems.

## Guarantees

- **No `sorry`.** The library has none. The two comparator challenges under
  [`EinsteinRelationAudit/`](EinsteinRelationAudit/) each contain one intentional
  statement-level `sorry`, which the corresponding solution proves.
- **Standard axioms only.** The axiom report of each of the eleven theorems of
  `MainTheorems.lean` lists exactly `propext`, `Classical.choice` and `Quot.sound`.
  [`scripts/check_axioms.py`](scripts/check_axioms.py) generates the report and fails on any
  other axiom, on `sorryAx`, and on a missing or an unexpected report.
- **Builds from a clean checkout.** In a fresh clone of this repository, with an empty build
  directory and Mathlib and DeGiorgi already compiled, `lake build` completed 9,396 jobs without
  errors and without any `sorry`; it reports 109 linter warnings in 52 files, inherited from the
  development (unused variables, unused `simp` arguments, tactics that do nothing). `lake build
  EinsteinRelationAudit` then compiled the comparator files, whose only warnings are the two
  intentional `sorry`s.
- **Independent check of the statements.** Theorem 1.2 and Proposition 7.1 are restated in
  [`EinsteinRelationAudit/`](EinsteinRelationAudit/) using mathlib alone: one challenge per
  theorem, made of `Challenge.lean` and the vocabulary files it imports, which restate every
  definition the statement uses, including the literature inputs. The solution proves each
  restatement from the library, and [leanprover/comparator](https://github.com/leanprover/comparator)
  checks that the statement is proved, with only the three standard axioms, and that the
  definitions it depends on are the same in the challenge and in the library. See
  [`EinsteinRelationAudit/README.md`](EinsteinRelationAudit/README.md) and
  [Running the comparators](#running-the-comparators) for what has been run.
- **Pinned toolchain and dependencies.** Lean and mathlib `v4.26.0`; DeGiorgi at the revision
  recorded in [`lake-manifest.json`](lake-manifest.json) (see [Building](#building)).
- **The paper is part of the repository.** Its source and PDF are in [`paper/`](paper/); the
  correspondence refers to [`paper/main.tex`](paper/main.tex).

## Size

The library contains 1,557 Lean files with 166,068 physical lines, on top of mathlib and
DeGiorgi. The comparator sources (114 files with 7,754 lines, most of them definitions restated
from the library) are counted separately.

## Building

Install [elan](https://github.com/leanprover/elan). The toolchain is pinned in
[`lean-toolchain`](lean-toolchain), and Lake fetches the dependencies.

```bash
lake exe cache get   # prebuilt mathlib
lake build
```

DeGiorgi has no prebuilt cache, so the first build compiles the modules of it that the library
uses, as well as the library. With Mathlib and DeGiorgi already compiled, a fresh build of
the library took 77 minutes on a 20-core Linux machine running two Lean processes at a time; the
compile times of the individual modules add up to 2.5 hours. On a 4-core GitHub-hosted runner we
expect the library to take one to two hours and DeGiorgi less than one hour, within the six-hour
limit of a job; these are estimates, not measurements.

`import EinsteinRelation` loads the eleven theorems and everything they use, and
`lake build EinsteinRelationAudit` builds the comparator files.

The dependencies are public repositories, pinned to exact commits in
[`lake-manifest.json`](lake-manifest.json):

- mathlib: `https://github.com/leanprover-community/mathlib4` at tag `v4.26.0`
  (`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`).
- DeGiorgi: `https://github.com/nitromannitol/DeGiorgi` at
  `31fc3240a6af8a506c2c6e9b540b091525d5c451` (branch `v426-backport`).

To reproduce the axiom reports:

```bash
python3 scripts/check_axioms.py
```

To build the paper, see [`paper/README.md`](paper/README.md).

## Running the comparators

Each comparator pair has a configuration `EinsteinRelationAudit/<Pair>/comparator.json` that
permits exactly `propext`, `Classical.choice` and `Quot.sound`. The comparator checks that the
solution proves the challenge statement, compares the definitions that the statement depends
on, and replays the proof with the Lean kernel and, if enabled, with NanoDa.

```bash
./scripts/run_comparators.sh
```

The script expects the paths of the tools in the environment variables `COMPARATOR_BIN`,
`COMPARATOR_LANDRUN`, `COMPARATOR_LEAN4EXPORT` and `COMPARATOR_NANODA`. The Lean v4.26.0
toolchain does not bundle these tools; the
[comparator workflow](.github/workflows/comparator.yml) builds them from pinned sources
(lean4export at the tag `v4.26.0` that matches [`lean-toolchain`](lean-toolchain), the comparator,
NanoDa and landrun) and runs the same checks on GitHub-hosted runners. The badge at the top of
this file shows the result of its latest run.

There are two continuous-integration workflows: **CI** builds the library and checks the axiom
reports; **Comparator audit** checks both challenge/solution pairs. CI runs on pushes to `main`
that change code or build configuration. Both workflows can be started manually from the
[Actions page](https://github.com/nitromannitol/einstein-relation-lean/actions). See
[`CONTRIBUTING.md`](CONTRIBUTING.md) for build conventions.

## Repository layout

```text
EinsteinRelation.lean           the root module, importing the main theorems
EinsteinRelation/
  MainTheorems.lean             the eleven numbered results, with their literature inputs
  Frozen/                       definitions used in the statements, fixed before the proofs
  External/                     the literature inputs (Prop-valued) and their vocabulary
  Environment/ Diffusion/       environments (Assumption 1.1), path laws, velocity, diffusivity
  Regeneration/ Density/        Section 3: regeneration and occupation bounds
  Entropy/                      Section 4: entropy and Fisher information
  Correctors/                   Section 5: correctors and their localization
  Mobility/ Clock/ Closure/     Section 6 and the proof of Theorem 1.2
  Sharpness/                    Section 7: the example attaining the rate
  ...                           supporting calculus, probability and measurability
EinsteinRelationAudit/          the mathlib-only restatements (challenge and vocabulary) and solutions
paper/                          the paper: source, bibliography, figure, PDF
scripts/                        axiom check and comparator runner
.github/workflows/              build and comparator workflows
```

## How this was built

The Lean development was written by AI agents between 18 and 21 October 2026, under the direction of the authors. Every
proof is checked by the Lean kernel. The checks on the statements and on the literature inputs, which the kernel does not
perform, are described below. Models, tools and review records are also listed in [`formalization.yaml`](formalization.yaml).

**Timeline** (2026, UTC).

| Date | Milestone |
| --- | --- |
| 18 Oct, 15:00 | Development started. |
| 18–19 Oct | Statements first. Every numbered result in scope and every literature input was stated in Lean and frozen before any proof work; the eleven results were frozen by 19 Oct, 14:25. |
| 19 Oct, 15:45 | First frozen result proved. |
| 20 Oct | Lemmas 3.1, 4.1, 4.2 and 4.3 and Proposition 3.2 proved. |
| 21 Oct, 04:26 | Lemma 5.1 proved. |
| 21 Oct, 08:46 | Lemma 5.2, Propositions 5.3, 6.1 and 7.1, and Theorem 1.2 proved. |
| 21 Oct | Public release. |

**Models and their roles.**

- OpenAI GPT-6.1 Sol (Codex CLI): orchestration on 18–19 October, and the main proof campaigns, among them Lemma 3.1 and
  Proposition 3.2, Lemma 5.1, the continuity form of Lemma 5.2, and the assembly of Proposition 5.3 and of the final chain.
- OpenAI GPT-6 Luna (Codex CLI): Lean statements of the results and of the literature inputs, and refute-first reviews of
  the frozen statements.
- OpenAI GPT-6 Astra (maximum reasoning effort, run separately from the development agents): independent audits of the
  literature inputs against the cited sources and of suspected errors in the paper.
- Anthropic Claude Opus 5.5 (Claude Code): orchestration from 19 October, integration, statement reviews, the final seal
  checks, and parts of the proofs, including the closed-graph argument that gives the measurable choice of heat kernel
  used in Proposition 5.3.
- Anthropic Claude Haiku 5.5: routine lemmas with fixed statements, dispatched in batches.
- Mistral Leanstral: small auxiliary lemmas with fixed statements.

**What was checked, and how.**

- *Proofs.* The published theorems depend only on the axioms `propext`, `Classical.choice` and `Quot.sound`. The repository
  contains no `sorry` and no `axiom`.
- *Statements.* Each statement was frozen before its proof was attempted. A frozen statement was accepted once it
  elaborated and a model that had not written it compared it with the manuscript, trying to find a mismatch (refute-first
  review); the development repository holds about 300 such review records. The authors fixed the scope and the policy
  for literature inputs; they did not review every Lean statement themselves. The
  statements of Theorem 1.2 and Proposition 7.1 are also checked against self-contained challenge files by the comparator
  (see [Running the comparators](#running-the-comparators)).
- *Literature inputs.* Each input was checked against the cited theorem or equation in the source by a model that had not
  written it. The inputs remain assumptions; they are listed in [Assumed literature inputs](#assumed-literature-inputs).

The full development history (about 2,700 commits), the review records and the audit reports are kept in a separate
private repository.

## Authors and citation

The paper and the Lean development are by **Ahmed Bou-Rabee** and **Ruizhe Xu**. To cite the
formalization, use [`CITATION.cff`](CITATION.cff).

## License

The Lean development is licensed under the Apache License 2.0; see [`LICENSE`](LICENSE).
The paper in [`paper/`](paper/) is included with its authors' permission; its publication
licence is not set by this software licence.
