import EinsteinRelation.Correctors.CorrectorLocalFromRegularSources
import EinsteinRelation.Correctors.ContinuousNormalizedSkewSource
import EinsteinRelation.Correctors.PlanarCenteredIntegrability
import EinsteinRelation.Correctors.ConditionalCopyPlanarMoments
import EinsteinRelation.Correctors.PlanarEnergyFromGradientCopies
import EinsteinRelation.Correctors.CorrectorGradientMomentsFromLiterature

/-! # Proposition 5.3 with both continuous source selections discharged

Source: `paper/main.tex:762–766,872–890,948–973`. Only quantitative
point-gradient conditional-copy decay remains an internal obligation. Source existence,
normalization, continuity, measurability and marginal integrability are
proved from the existing cited inputs.
-/

open MeasureTheory
namespace EinsteinRelation
open Correctors External.AKM External.GilbargTrudinger HeatSelectedSkewMeaning
open Correctors.NormalizedSpatialRepresentativeSupport
open Correctors.NormalizedScalarPhysicalLawTransportSupport
local instance : Fact (2 ≤ (2 : ℕ)) := ⟨le_rfl⟩
attribute [local instance] ReductionImageV3.fieldPair_standardBorel
local instance selectedEnergyRestrictionMeasurableSpace {d : ℕ} (U : Set (Vec d)) :
    MeasurableSpace C(U, Mat d) := borel C(U, Mat d)

/-- Proposition 5.3 reduced to the actual point-gradient copy decay.
Planar spatial RMS decay follows by nested conditioning and averaging,
with Lemma 5.1 handling small radii. The same fixed continuous sources
serve every exponent. Source: `paper/main.tex:872–890,948–973`. -/
theorem correctorLocalConstruction_of_continuous_sources_and_gradient_copy_bounds
    (hP : BallPoincareEstimate) (h836 : InteriorRegularRepresentative)
    (hgradient : ∀ (d : ℕ) [Fact (2 ≤ d)] (Λ₀ r₀ m : ℝ),
      2 ≤ m → ∃ C : ℝ, ∀ (Q : EnvironmentLaw d Λ₀ r₀) (R : ℝ), 1 ≤ R →
        ∀ (y : Point d) (i : Fin d),
        eLpNorm (fun z : C(conditionalCorrectorBall R y, Mat d) ×
          (FieldPair d × FieldPair d) =>
          euclideanNorm (conditionalCorrectorGradient Q i y z.2.1 -
            conditionalCorrectorGradient Q i y z.2.2)) (ENNReal.ofReal m)
          (reducedConditionalCopyLaw (reducedEnvironmentLaw Q) (conditionalCorrectorBall R y)) ≤
            ENNReal.ofReal (C * R ^ (-(d : ℝ) / 2)))
    (h45 : ScalarStationaryEstimate) (h46 : ScalarPlanarL2Estimate)
    (h47 : ScalarHeatDifferenceEstimate) (h68 : FluxGradientEstimate)
    (h614 : FluxStationaryEstimate) (h615 : FluxPlanarL2Estimate)
    (h616 : FluxHeatDifferenceEstimate)
    (h817 : LocalBoundednessEstimate) (h832 : InteriorGradientEstimate)
    (hH2 : CorrectorWeakH2) :
    CorrectorLocalConstruction := by
  let S : ∀ {d : ℕ} [Fact (2 ≤ d)] {L r₀ : ℝ}, EnvironmentLaw d L r₀ → ℝ → Fin d →
      FieldPair d → Vec d → Mat d :=
    fun Q R i => selectedContinuousNormalizedSkewSource h68 hP h836 Q R i
  have hspec {d : ℕ} [Fact (2 ≤ d)] {L r₀ : ℝ}
      (Q : EnvironmentLaw d L r₀) (R : ℝ) (hR : 1 ≤ R) (i : Fin d) :=
    selectedContinuousNormalizedSkewSource_spec h68 hP h836 Q R hR i
  apply correctorLocalConstruction_of_selected_regular_sources_and_separate_copy_bounds
    hP h836 S
    (fun Q R hR i => (hspec Q R hR i).1)
    (fun Q R hR i => (hspec Q R hR i).2.1)
    (fun Q R hR i => (hspec Q R hR i).2.2.1)
    (fun Q R hR i => (hspec Q R hR i).2.2.2.1)
    (fun Q R hR i => (hspec Q R hR i).2.2.2.2)
    hgradient _ h45 h46 h47 h68 h614 h615 h616 h817 h832 hH2
  intro L r₀ m hm
  have H51 := correctorGradientMoments_of_literature
    h45 h46 h68 h614 h615 hP h817 h832 h836
  have hg : ∃ C : ℝ, ∀ (Q : EnvironmentLaw 2 L r₀) (R : ℝ), 1 ≤ R →
      ∀ (y : Point 2) (i : Fin 2),
      eLpNorm (fun z : C(conditionalCorrectorBall R y, Mat 2) ×
        (FieldPair 2 × FieldPair 2) =>
        euclideanNorm (conditionalCorrectorGradient Q i y z.2.1 -
          conditionalCorrectorGradient Q i y z.2.2)) (ENNReal.ofReal m)
        (reducedConditionalCopyLaw (reducedEnvironmentLaw Q) (conditionalCorrectorBall R y)) ≤
          ENNReal.ofReal (C/R) := by
    obtain ⟨C, hC⟩ := hgradient 2 L r₀ m hm
    refine ⟨C, fun Q R hR y i => ?_⟩
    simpa only [Nat.cast_ofNat, show -(2 : ℝ)/2 = -1 by norm_num,
      Real.rpow_neg_one, div_eq_mul_inv] using hC Q R hR y i
  obtain ⟨B, hB, hEb⟩ := exists_planar_copy_energy_bound_of_gradient_copy_bounds H51 L r₀ m hm hg
  obtain ⟨C, _, hb⟩ := paired_planar_centered_moments_of_energy h817 hP L
  refine ⟨C*B, ?_⟩
  intro Q R hR i
  let φ : FieldPair 2 → Point 2 → ℝ := fun ω x =>
    selectedContinuousCanonicalScalarSource hP h836 Q R i ω x.ofLp
  let σ := S Q R i
  have hφ := selectedContinuousCanonicalScalarSource_normalized hP h836 Q R hR i
  have hσ := hspec Q R hR i
  have hc : ∀ᵐ ω ∂reducedEnvironmentLaw Q, Continuous (φ ω) ∧ Continuous (σ ω) := by
    filter_upwards [ae_continuous_selectedContinuousCanonicalScalarSource hP h836 Q R i,
      hσ.2.2.2.2] with ω hφc hσc
    exact ⟨hφc.comp (PiLp.continuous_ofLp 2 (fun _ : Fin 2 => ℝ)), hσc⟩
  have hσm (a b : Fin 2) : Measurable (fun z : FieldPair 2 × Vec 2 => σ z.1 z.2 a b) :=
    (hσ.2.1 a b).measurable
  obtain ⟨hEi, hEn⟩ := hEb Q R hR 0 i
  obtain ⟨hφm, hSm, _, _, hn⟩ := hb Q (canonicalSourceMollifier 2) R hR 0 i
    φ σ hφ hσ.1 hc hσm (ENNReal.ofReal m) B hB.le hEi hEn
  obtain ⟨hφi, hSi⟩ := integrable_planar_centered_correctors h817 hP Q
    (canonicalSourceMollifier 2) R hR 0 i φ σ hφ hσ.1 hc hσm
  exact ⟨hφm, hφi, hSm, hSi, hn⟩

end EinsteinRelation
