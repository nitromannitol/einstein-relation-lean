import EinsteinRelation.Correctors.CorrectorLocalFromSelectedScalar
import EinsteinRelation.Correctors.CanonicalSourceTailsFromConditional
import EinsteinRelation.Correctors.ConditionalCopyFrobeniusJensen
import EinsteinRelation.Correctors.CorrectorConditionalContinuousStatement

/-! # Proposition 5.3 for a fixed continuous normalized source family

Source: `paper/main.tex:774–786,895–977`. The planar copy estimate is used
only for the jointly measurable selected scalar and skew sources at the
origin. No estimate for arbitrary spatial representatives is required.
-/

open MeasureTheory ProbabilityTheory
namespace EinsteinRelation
open Correctors External.AKM External.GilbargTrudinger HeatSelectedSkewMeaning
open Correctors.NormalizedSpatialRepresentativeSupport
open Correctors.NormalizedScalarPhysicalLawTransportSupport
local instance : Fact (2 ≤ (2 : ℕ)) := ⟨le_rfl⟩
attribute [local instance] ReductionImageV3.fieldPair_standardBorel
local instance continuousNormalizedCopyRestrictionMeasurableSpace {d : ℕ} (U : Set (Vec d)) :
    MeasurableSpace C(U, Mat d) := borel C(U, Mat d)

variable
    (hP : BallPoincareEstimate)
    (U : ∀ {d : ℕ} [Fact (2 ≤ d)] {L r₀ : ℝ}, EnvironmentLaw d L r₀ → ℝ → Fin d →
      FieldPair d → Vec d → ℝ)
    (S : ∀ {d : ℕ} [Fact (2 ≤ d)] {L r₀ : ℝ}, EnvironmentLaw d L r₀ → ℝ → Fin d →
      FieldPair d → Vec d → Mat d)
    (hu : ∀ {d : ℕ} [Fact (2 ≤ d)] {L r₀ : ℝ}
      (Q : EnvironmentLaw d L r₀) (R : ℝ) (hR : 1 ≤ R) (i : Fin d),
      IsNormalizedCanonicalScalarCorrector Q i (canonicalSourceMollifier d) R hR 0
        (fun ω x => U Q R i ω x.ofLp))
    (hS : ∀ {d : ℕ} [Fact (2 ≤ d)] {L r₀ : ℝ}
      (Q : EnvironmentLaw d L r₀) (R : ℝ), 1 ≤ R → ∀ i : Fin d,
      HasHeatSelectedSkewCorrectorColumn (Fact.out : 2 ≤ d) Q i (S Q R i))
    (hSm : ∀ {d : ℕ} [Fact (2 ≤ d)] {L r₀ : ℝ}
      (Q : EnvironmentLaw d L r₀) (R : ℝ), 1 ≤ R → ∀ i j k : Fin d,
      StronglyMeasurable (fun z : FieldPair d × Vec d => S Q R i z.1 z.2 j k))
    (hSsk : ∀ {d : ℕ} [Fact (2 ≤ d)] {L r₀ : ℝ}
      (Q : EnvironmentLaw d L r₀) (R : ℝ), 1 ≤ R → ∀ (i : Fin d) (ω : FieldPair d)
        (x : Vec d), (S Q R i ω x).transpose = -(S Q R i ω x))
    (hSn : ∀ {d : ℕ} [Fact (2 ≤ d)] {L r₀ : ℝ}
      (Q : EnvironmentLaw d L r₀) (R : ℝ), 1 ≤ R → ∀ i j k : Fin d,
      ∀ᵐ ω ∂reducedEnvironmentLaw Q,
        (∫ z, S Q R i ω (-z) j k ∂mollifierCenterMeasure d R) = 0)
    (huc : ∀ {L r₀ : ℝ} (Q : EnvironmentLaw 2 L r₀) (R : ℝ),
      1 ≤ R → ∀ i : Fin 2, ∀ᵐ ω ∂reducedEnvironmentLaw Q, Continuous (U Q R i ω))
    (hSc : ∀ {L r₀ : ℝ} (Q : EnvironmentLaw 2 L r₀) (R : ℝ),
      1 ≤ R → ∀ i : Fin 2, ∀ᵐ ω ∂reducedEnvironmentLaw Q, Continuous (S Q R i ω))


include hP hu hS hSm hSsk hSn huc hSc

/-- The selected-family form of Proposition 5.3. All remaining internal
source and paired-bound obligations are explicit. The scalar source is fixed
before the moment exponent and can be a proved continuous selection.
Source: `paper/main.tex:861–894,948–973`. -/
theorem correctorLocalConstruction_of_continuous_normalized_sources_and_separate_copy_bounds
    (hgradient : ∀ (d : ℕ) [Fact (2 ≤ d)] (Λ₀ r₀ m : ℝ),
      2 ≤ m → ∃ C : ℝ, ∀ (Q : EnvironmentLaw d Λ₀ r₀) (R : ℝ), 1 ≤ R →
        ∀ (y : Point d) (i : Fin d),
        eLpNorm (fun z : C(conditionalCorrectorBall R y, Mat d) ×
          (FieldPair d × FieldPair d) =>
          euclideanNorm (conditionalCorrectorGradient Q i y z.2.1 -
            conditionalCorrectorGradient Q i y z.2.2)) (ENNReal.ofReal m)
          (reducedConditionalCopyLaw (reducedEnvironmentLaw Q) (conditionalCorrectorBall R y)) ≤
            ENNReal.ofReal (C * R ^ (-(d : ℝ) / 2)))
    (hplanar : ∀ (L r₀ m : ℝ), 2 ≤ m → ∃ C : ℝ,
      ∀ (Q : EnvironmentLaw 2 L r₀) (R : ℝ) (_hR : 1 ≤ R) (i : Fin 2),
        let φ := fun ω x => U Q R i ω x.ofLp
        let σ := S Q R i
        Measurable (conditionalCenteredScalar (canonicalSourceMollifier 2) R 0 φ) ∧
        Integrable (conditionalCenteredScalar (canonicalSourceMollifier 2) R 0 φ)
          (reducedEnvironmentLaw Q) ∧
        Measurable (conditionalCenteredSkew (canonicalSourceMollifier 2) R 0 σ) ∧
        (∀ a b, Integrable (fun ω =>
          conditionalCenteredSkew (canonicalSourceMollifier 2) R 0 σ ω a b)
          (reducedEnvironmentLaw Q)) ∧
        eLpNorm (fun z : C(conditionalCorrectorBall R (0 : Point 2), Mat 2) ×
          (FieldPair 2 × FieldPair 2) =>
          conditionalCenteredScalar (canonicalSourceMollifier 2) R 0 φ z.2.1 -
            conditionalCenteredScalar (canonicalSourceMollifier 2) R 0 φ z.2.2)
          (ENNReal.ofReal m)
          (reducedConditionalCopyLaw (reducedEnvironmentLaw Q) (conditionalCorrectorBall R 0)) +
        eLpNorm (fun z : C(conditionalCorrectorBall R (0 : Point 2), Mat 2) ×
          (FieldPair 2 × FieldPair 2) =>
          frobeniusNorm (conditionalCenteredSkew (canonicalSourceMollifier 2) R 0 σ z.2.1 -
            conditionalCenteredSkew (canonicalSourceMollifier 2) R 0 σ z.2.2))
          (ENNReal.ofReal m)
          (reducedConditionalCopyLaw (reducedEnvironmentLaw Q) (conditionalCorrectorBall R 0)) ≤
            ENNReal.ofReal C)
    (h45 : ScalarStationaryEstimate) (h46 : ScalarPlanarL2Estimate)
    (h47 : ScalarHeatDifferenceEstimate) (h68 : FluxGradientEstimate)
    (h614 : FluxStationaryEstimate) (h615 : FluxPlanarL2Estimate)
    (h616 : FluxHeatDifferenceEstimate)
    (h817 : LocalBoundednessEstimate) (h832 : InteriorGradientEstimate)
    (h836 : InteriorRegularRepresentative) (hH2 : CorrectorWeakH2) :
    CorrectorLocalConstruction := by
  apply correctorLocalConstruction_of_dimensionwise_sources_and_tails
    U S hu hS hSm hSsk hSn huc hSc ?_ ?_
    h45 h46 h47 h68 h614 h615 h616 hP h817 h832 h836 hH2
  · intro d _ L r₀ p hp
    obtain ⟨C, hC⟩ := hgradient d L r₀ p hp
    refine ⟨max C 0, le_max_right _ _, ?_⟩
    intro Q R hR i
    have h := (eLpNorm_canonicalGradient_euclidean_conditional_error_le_copy_difference Q i
      (WithLp.ofLp (0 : Point d)) (conditionalCorrectorBall R 0)
      (isOpen_conditionalCorrectorBall R 0)
      (ENNReal.one_le_ofReal.mpr (one_le_two.trans hp)) ENNReal.ofReal_ne_top).trans
        (hC Q R hR 0 i)
    change eLpNorm (fun ω => euclideanNorm (conditionalCorrectorGradient Q i 0 ω -
      (reducedEnvironmentLaw Q)[conditionalCorrectorGradient Q i 0 |
        Carriers.reducedCoefficientObservationSigma (conditionalCorrectorBall R 0)] ω))
      (ENNReal.ofReal p) (reducedEnvironmentLaw Q) ≤ _ at h
    rw [conditionalCorrectorGradient_zero, conditionalCorrectorBall_zero] at h
    exact h.trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg
        (zero_le_one.trans hR) _)))
  · intro L r₀ p hp
    obtain ⟨C, hC⟩ := hplanar L r₀ p hp
    refine ⟨max C 0, le_max_right _ _, ?_⟩
    intro Q R hR i
    let u := U Q R i
    let σ := S Q R i
    obtain ⟨hsm, hsi, htm, hti, hb⟩ := hC Q R hR i
    have h := (add_le_add
      (eLpNorm_reduced_conditional_error_le_copy_difference (reducedEnvironmentLaw Q)
        (conditionalCorrectorBall R 0) (isOpen_conditionalCorrectorBall R 0)
        (ENNReal.one_le_ofReal.mpr (one_le_two.trans hp)) ENNReal.ofReal_ne_top hsm hsi)
      (eLpNorm_reduced_conditional_frobenius_le_copy_difference (reducedEnvironmentLaw Q)
        (conditionalCorrectorBall R 0) (isOpen_conditionalCorrectorBall R 0)
        (ENNReal.one_le_ofReal.mpr (one_le_two.trans hp)) ENNReal.ofReal_ne_top htm hti)).trans hb
    let μ := reducedEnvironmentLaw Q
    let obs := Carriers.reducedCoefficientObservationSigma (conditionalCorrectorBall (d := 2) R 0)
    let cφ := conditionalCenteredScalar (canonicalSourceMollifier 2) R 0
      (fun ω x => u ω x.ofLp)
    let cσ := conditionalCenteredSkew (canonicalSourceMollifier 2) R 0 σ
    have hφ : cφ =ᵐ[μ] (fun ω => u ω 0) := by
      filter_upwards [normalizedCanonicalScalar_mollifierCenterMean_eq_zero Q i hR u (hu Q R hR i)]
        with ω hω
      simp only [cφ, conditionalCenteredScalar, WithLp.ofLp_zero,
        integral_canonicalSourceKernel_eq_centerMean (zero_lt_one.trans_le hR), hω, sub_zero]
    have hσ (j k : Fin 2) : (fun ω => cσ ω j k) =ᵐ[μ] (fun ω => σ ω 0 j k) := by
      filter_upwards [hSn Q R hR i j k] with ω hω
      change σ ω 0 j k - (∫ z : Point 2,
        sourceScaledMollifierKernel (canonicalSourceMollifier 2) R 0 z * σ ω z.ofLp j k) = _
      rw [integral_canonicalSourceKernel_eq_centerMean (zero_lt_one.trans_le hR)
        (fun x => σ ω x j k), hω, sub_zero]
    have hs := condExp_congr_ae (m := obs) hφ
    have ht := ae_all_iff.mpr fun j => ae_all_iff.mpr fun k =>
      (hσ j k).and (condExp_congr_ae (m := obs) (hσ j k))
    have heqφ : eLpNorm (fun ω => cφ ω - condExp obs μ cφ ω) (ENNReal.ofReal p) μ =
        eLpNorm ((fun ω => u ω 0) - condExp obs μ (fun ω => u ω 0))
          (ENNReal.ofReal p) μ := by
      apply eLpNorm_congr_ae
      filter_upwards [hφ, hs] with ω hω hc
      exact congrArg₂ (· - ·) hω hc
    have heqσ : eLpNorm (fun ω => frobeniusNorm (Matrix.of (fun j k => cσ ω j k -
        condExp obs μ (fun a => cσ a j k) ω))) (ENNReal.ofReal p) μ =
        eLpNorm (fun ω => frobeniusNorm (fun j k => σ ω 0 j k -
          condExp obs μ (fun a => σ a 0 j k) ω)) (ENNReal.ofReal p) μ := by
      apply eLpNorm_congr_ae
      filter_upwards [ht] with ω hω
      congr 1
      funext j k
      exact congrArg₂ (· - ·) (hω j k).1 (hω j k).2
    change eLpNorm (fun ω => cφ ω - condExp obs μ cφ ω) _ μ +
      eLpNorm (fun ω => frobeniusNorm (Matrix.of (fun j k => cσ ω j k -
        condExp obs μ (fun a => cσ a j k) ω))) _ μ ≤ _ at h
    rw [heqφ, heqσ] at h
    dsimp only [obs, μ] at h
    rw [conditionalCorrectorBall_zero] at h
    exact ⟨(le_add_right le_rfl |>.trans h).trans
        (ENNReal.ofReal_le_ofReal (le_max_left _ _)),
      (le_add_left le_rfl |>.trans h).trans
        (ENNReal.ofReal_le_ofReal (le_max_left _ _))⟩

end EinsteinRelation
