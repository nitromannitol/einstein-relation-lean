import EinsteinRelation.Regeneration.OccupationFromRenewal

/-! # The Girsanov step of Proposition 3.2: its two inputs

Source: `paper/main.tex` 457-480 (Step 1 of the proof of Proposition 3.2) and Gantert, Mathieu and
Piatnitski (2012), Section 7, Proposition 7.2 and estimate (7.4), pp. 33-34. Step 1 bounds the
occupation of the first regeneration interval by three facts:

* `GirsanovEndpointStep`: for almost every environment, the law of the reduced diffusion at force
  `λ` and time `t` is controlled by its law at force `0` through the Girsanov density `Z_t`, with
  `E⁰[Z_t^q] ≤ exp(½ q (q - 1) K λ² t)`; Hölder's inequality turns this into the displayed bound.
  GMP prove the Girsanov formula (Proposition 7.2) and the exponential moment (7.4) for every
  environment and almost every starting point, and note the transfer to the origin for almost every
  environment (p. 33). The reduced diffusion is their model with potential zero and coefficient
  `a = e^{-2V} a₀` (p. 10, (3.8)-(3.9)); `K = sourceReducedBound Λ₀` bounds the bracket
  `⟨B̄⟩_t = ∫₀ᵗ e₁·a(Y_s) e₁ ds ≤ K t` ((7.3)).
* `UnforcedEnvironmentInvarianceStep`: at force `0` the environment seen from the reduced diffusion
  is stationary under the reduced reference law (`paper/main.tex` 257 and 455).
* the first regeneration tail `HasFirstRegenerationTail`, a GMP literature input.

Cauchy-Schwarz against the tail, Hölder in the environment, and the time integral with
`q - 1 ≤ c / K` then give `FirstRewardStep` with `p = 2q / (q - 1)`.
-/

open MeasureTheory
open scoped NNReal ENNReal

open EinsteinRelation.External.GantertSection7Support (GantertFixedEnvironmentRealization)

noncomputable section

namespace EinsteinRelation

/-- Step `GirsanovEndpointStep` (GMP 2012, Proposition 7.2 and (7.4), pp. 33-34, with Hölder): for
almost every environment `ω`, any realization `r` at force `λ` and any realization `r₀` at force
`0` of the zero-potential reduced pair satisfy, for every time `t`, every exponent `q > 1` and every
measurable `φ ≥ 0` on space,
`E^λ_0[φ(Y_t)] ≤ (E⁰_0[φ(Y_t)^{q/(q-1)}])^{(q-1)/q} exp(½ (q - 1) K λ² t)`
with `K = sourceReducedBound Λ₀`. -/
def GirsanovEndpointStep : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ) (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h0 : 0 ≤ lam)
    (h1 : lam ≤ 1),
    ∀ᵐ ω ∂Q.measure, ∀ (hω' : IsRegular (sourceReducedBound Λ₀) (zeroPotentialReducedPair ω))
      (r : GantertFixedEnvironmentRealization hd (sourceReducedBound Λ₀)
        (one_le_sourceReducedBound Q.ellipticity_parameter) (zeroPotentialReducedPair ω) hω'
        lam h0 h1)
      (r0 : GantertFixedEnvironmentRealization hd (sourceReducedBound Λ₀)
        (one_le_sourceReducedBound Q.ellipticity_parameter) (zeroPotentialReducedPair ω) hω'
        0 le_rfl zero_le_one)
      (t : ℝ≥0) (q : ℝ), 1 < q → ∀ φ : Vec d → ℝ≥0∞, Measurable φ →
        ∫⁻ γ, φ (γ t) ∂r.pathLaw 0 ≤
          (∫⁻ γ, φ (γ t) ^ (q / (q - 1)) ∂r0.pathLaw 0) ^ ((q - 1) / q) *
            ENNReal.ofReal (Real.exp ((1 / 2) * (q - 1) * sourceReducedBound Λ₀ * lam ^ 2 * t))

/-- Step `UnforcedEnvironmentInvarianceStep` (`paper/main.tex` 257 and 455): for a reduced GMP
family at force `0`, the reduced environment observed at any time `t` has, under the annealed law
from the origin, the reduced reference law. Source: GMP 2012, p. 8 (the environment law is
invariant for the environment seen from the particle when `V = 0`), applied to the reduced process
by p. 10 and to measurable coefficients by Section 7, p. 32; the proof by detailed balance,
stationarity and translation covariance is De Masi, Ferrari, Goldstein and Wick 1989, Section 6,
(6.9)-(6.13). The observation is `reduce (translate (Y_t) ω)`, so its law is the image of the
invariant law under `reduce`. -/
def UnforcedEnvironmentInvarianceStep : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ) (Q : EnvironmentLaw d Λ₀ r₀) (P' : DiffusionFamily d),
    IsGMPReducedFamily hd Q.ellipticity_parameter Q P' →
    ∀ (hP0 : ∀ᵐ ω ∂Q.measure, IsProbabilityMeasure (originLaw (P' 0) ω)) (t : ℝ≥0)
      (ψ : FieldPair d → ℝ≥0∞), Measurable ψ →
        ∫⁻ z, ψ (Carriers.reducedObservationAt t z)
            ∂(Carriers.annealedCoordinateJoint Q.measure (P' 0) hP0) =
          ∫⁻ w, ψ w ∂(Carriers.reducedReferenceLaw Q)

end EinsteinRelation
