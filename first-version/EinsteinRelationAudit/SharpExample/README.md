# Proposition 7.1: the rate is attained

This pair checks Proposition 7.1, label `sharp.example`, exposed as
`EinsteinRelation.mobility_rate_sharp` in
[`EinsteinRelation/MainTheorems.lean`](../../EinsteinRelation/MainTheorems.lean).

**What `Challenge.lean` states** (with the definitions restated in `Vocabulary/`). Assume the
29 literature inputs that the proof uses (the hypotheses `h45`, …, `hW`; see the table in the
[README](../../README.md#assumed-literature-inputs)).
For every `d ≥ 2` there are constants `Λ₀`, `r₀`, an environment law `Q` satisfying
Assumption 1.1 with these constants whose fields `a₀` and `V` are almost surely `C^∞`, and
`c > 0`, such that, for every family of quenched path laws that is the diffusion of Gantert,
Mathieu and Piatnitski (2012, Section 7) for `Q`, every diffusivity `Σ_X` of the unforced
diffusion and every function `λ ↦ ℓ(λ)` that gives the quenched velocity for each
`λ ∈ (0, 1]`, `((λ⁻¹ ℓ(λ) − Σ_X e₁) · e₁) / λ → c` as `λ ↓ 0`.

**How to read the encoding.**

- *The example.* The environment law is constructed in the library; the challenge states only
  that it exists, satisfies Assumption 1.1 (`EnvironmentLaw d Λ₀ r₀`) and is supported on smooth
  fields (`IsSmoothFieldPair`: every entry of `a₀` and the potential `V` are `C^∞`).
- *The diffusion, velocity and diffusivity* are encoded as for Theorem 1.2: see
  [`../MobilityRate/README.md`](../MobilityRate/README.md).
- *The limit* is one-sided, through `λ > 0`, as in the paper (`eq.sharp-expansion`).
- *Universal statement.* The conclusion holds for every diffusion family, diffusivity and
  velocity function with the stated properties; it does not assert that they exist.
- *The white-noise input* `hW` is stated for every `d ≥ 2`:
  `∀ d, 2 ≤ d → WhiteNoiseExistence d`.

The solution applies the library theorem without adding a hypothesis or dropping a conclusion.
The permitted axioms are `propext`, `Classical.choice` and `Quot.sound`.
