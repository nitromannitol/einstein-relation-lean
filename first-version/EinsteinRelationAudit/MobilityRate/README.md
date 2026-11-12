# Theorem 1.2: the quantitative Einstein relation

This pair checks Theorem 1.2 of the introduction, label `t.main`, exposed as
`EinsteinRelation.mobility_rate` in
[`EinsteinRelation/MainTheorems.lean`](../../EinsteinRelation/MainTheorems.lean).

**What `Challenge.lean` states** (with the definitions restated in `Vocabulary/`). Assume the
27 literature inputs that the proof uses (the hypotheses `h45`, …, `hIP`; see the table in the
[README](../../README.md#assumed-literature-inputs)).
For `d ≥ 2` and constants `Λ₀`, `r₀` there are `C` and `λ_* > 0` such that, for every
environment law `Q` satisfying Assumption 1.1 with these constants, every family of quenched path
laws that is the diffusion of Gantert, Mathieu and Piatnitski (2012, Section 7) for `Q`, every
diffusivity `Σ_X` of the unforced diffusion, every `λ ∈ (0, λ_*]` and every quenched velocity
`ℓ` of the diffusion with force `λ`, `|λ⁻¹ ℓ − Σ_X e₁| ≤ C λ`.

**How to read the encoding.**

- *The environment.* `EnvironmentLaw d Λ₀ r₀` is a probability law on pairs `(a₀, V)` of
  continuous fields with (S1)–(S5) of Assumption 1.1 and `Λ₀ ≥ 1`, `r₀ ≥ 1`. The theorem quantifies
  over every such law; the constants `C` and `λ_*` are chosen before it.
- *The diffusion.* `IsGMPPhysicalFamily` says that, for each force `λ ∈ [0, 1]` and almost every
  environment, the path law from the origin is that of a `GantertFixedEnvironmentRealization`:
  the continuous-path law of a Markov semigroup with a heat-kernel density, reversible for
  `physicalReversibleMeasure`, whose closed form has the weighted `H¹` domain and energy of
  Gantert, Mathieu and Piatnitski (2012, (7.1)).
- *Velocity and diffusivity.* `HasQuenchedVelocity` is the almost sure limit of `X(t)/t` for
  almost every environment. `HasDiffusivity` is weak convergence of the annealed law of
  `ε X⁰(ε⁻² ·)` on continuous paths to a centred Brownian law with covariance `Σ_X`.
- *Universal statement.* The theorem holds for every diffusion family, diffusivity and velocity
  with these properties; it does not assert that they exist.
- *The literature inputs.* Each hypothesis is a Prop-valued definition restated in the challenge
  with the docstring that records its source. They are not axioms and are not proved.

The solution applies the library theorem without adding a hypothesis or dropping a conclusion.
The permitted axioms are `propext`, `Classical.choice` and `Quot.sound`.
