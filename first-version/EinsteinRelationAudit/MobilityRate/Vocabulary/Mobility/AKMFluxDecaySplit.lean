import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.SpecificCodomains.WithLp
import EinsteinRelationAudit.MobilityRate.Vocabulary.Calculus.Generator
import EinsteinRelationAudit.MobilityRate.Vocabulary.Calculus.HorizontalSobolev
import EinsteinRelationAudit.MobilityRate.Vocabulary.Calculus.HorizontalTranslationLp
import EinsteinRelationAudit.MobilityRate.Vocabulary.Carriers.DensityAnnealedTwins
import EinsteinRelationAudit.MobilityRate.Vocabulary.Correctors.CanonicalVariationalGradientSupport
import EinsteinRelationAudit.MobilityRate.Vocabulary.Correctors.EllipticOperatorBound
import EinsteinRelationAudit.MobilityRate.Vocabulary.Correctors.HeatSmoothing
import EinsteinRelationAudit.MobilityRate.Vocabulary.Correctors.HorizontalH1EuclideanGradient
import EinsteinRelationAudit.MobilityRate.Vocabulary.Correctors.StationaryGradientDomainSupport
import EinsteinRelationAudit.MobilityRate.Vocabulary.Correctors.StationarySpatialRealizationSupport
import EinsteinRelationAudit.MobilityRate.Vocabulary.Diffusion.GMPFamily
import EinsteinRelationAudit.MobilityRate.Vocabulary.Environment.Basic
import EinsteinRelationAudit.MobilityRate.Vocabulary.Environment.CoefficientRestriction
import EinsteinRelationAudit.MobilityRate.Vocabulary.Environment.Reduction
import EinsteinRelationAudit.MobilityRate.Vocabulary.Environment.SourceReducedBoundSupport
import EinsteinRelationAudit.MobilityRate.Vocabulary.Mobility.VelocityRateFromSteps
import EinsteinRelationAudit.MobilityRate.Vocabulary.Probability.LocalSigma
import EinsteinRelationAudit.MobilityRate.Vocabulary.Probability.ReductionLocality

/-! Restated from the library module `EinsteinRelation.Mobility.AKMFluxDecaySplit`:
the declarations of that module that the statement of
`EinsteinRelationAudit.MobilityRate.mobility_rate` depends on, in their module context. -/

open MeasureTheory
open scoped ENNReal
namespace EinsteinRelation
open Correctors
/-- The first coordinate of the centred flux `g_i = a(e_i + ∇φ_i) - ā e_i` on the reduced space
(`paper/main.tex` 705-708), as in `AKMFluxDecay`. -/
noncomputable def centredFluxFirst {d : ℕ} {Λ₀ r₀ : ℝ} (hd : 2 ≤ d) (Q : EnvironmentLaw d Λ₀ r₀)
    (i : Fin d) (ω : FieldPair d) : ℝ :=
  (StationarySpatialRealization.spatialRealization (canonicalCorrectorFlux Q i) ((0 : Vec d), ω)).ofLp (firstIdx hd) -
    (expectedCorrectorFlux Q i).ofLp (firstIdx hd)
/-- Step `AKMFluxDecayLargeTime`, the estimate (4.3) of AKM Theorem 4.1 (p. 124) at heat times
`t ≥ 1`: `‖H_t (g_i)_1‖_{L^m(Q)} ≤ C_m (1 + t)^{-1/2}`, with `C` depending on `d`, `Λ₀`, `r₀`, `m`.

Hypotheses. AKM's standing assumptions (pp. xvii-xviii) are (0.6) `|ξ|² ≤ ξ·a(x)ξ ≤ Λ|ξ|²`,
(0.10) `ℤ^d`-stationarity and (0.11) unit range of dependence, with `d ≥ 2`. The reduced coefficient
law is `ℝ^d`-stationary, has range of dependence `r₀`, and is elliptic with constants in
`[Λ₀⁻¹ e^{-2Λ₀}, Λ₀ e^{2Λ₀}]`. AKM applies after the rescalings `x ↦ x / r₀` and `a ↦ c a`: the
correctors are unchanged, the flux and `ā` scale by `c`, and heat times scale by `r₀²`. The
constant therefore depends only on `d`, `Λ₀`, `r₀` and `m`, as in the quantifier order here.

Objects. AKM's first-order corrector `φ_e` (Sect. 3.4) has a stationary, mean-zero,
square-integrable gradient solving `-∇·a(e + ∇φ_e) = 0`, and `ā e = E[a(e + ∇φ_e)]`. Here the
flux is `canonicalCorrectorFlux Q i` and its mean `expectedCorrectorFlux Q i`, built from
`canonicalCorrectorGradient Q i`. The two agree by the uniqueness of the variational solution in the
potential domain (`existsUnique_canonicalCorrectorGradient_horizontalH1`), applied to `∇φ_{e_i}`
once it is placed in `correctorPotentialDomain`, the `L²` closure of horizontal gradients.

The range `t < 1`, which (4.3) does not cover, is proved from the flux moments in
`akmFluxDecay_of_largeTime`. -/
def AKMFluxDecayLargeTime : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ) (m : ℝ), 2 ≤ m →
    ∃ C : ℝ, ∀ (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (t : ℝ), 1 ≤ t →
      eLpNorm (heatSmoothed t (centredFluxFirst hd Q i)) (ENNReal.ofReal m)
        (Carriers.reducedReferenceLaw Q) ≤ ENNReal.ofReal (C * (Real.sqrt (1 + t))⁻¹)
end EinsteinRelation
