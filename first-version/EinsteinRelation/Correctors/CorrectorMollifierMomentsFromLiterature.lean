import EinsteinRelation.Correctors.CorrectorMomentsFromLiterature
import EinsteinRelation.Correctors.CenteredEuclideanTransport
import EinsteinRelation.Correctors.MollifierSpatialMomentComparison

/-! # Actual source moments for the conditional mollifier construction

Source: `paper/main.tex:715–722,942–947`. The proved Lemma 5.1 estimate
controls the mollifier-weighted centered scalar and heat-selected skew
sources, with the constant fixed before the law and radius.
-/

open MeasureTheory
open scoped ENNReal

namespace EinsteinRelation.Correctors
open External.AKM External.GilbargTrudinger HeatSelectedSkewMeaning
open NormalizedSpatialRepresentativeSupport NormalizedScalarPhysicalLawTransportSupport

/-- The actual normalized scalar and heat-selected skew pair has uniform
mollifier-weighted centered source moments, conditional only on the
existing frozen literature estimates. Source: `paper/main.tex:715–722,942–947`. -/
theorem corrector_mollifier_centered_moments_of_literature
    (h45 : ScalarStationaryEstimate) (h46 : ScalarPlanarL2Estimate)
    (h47 : ScalarHeatDifferenceEstimate) (h68 : FluxGradientEstimate)
    (h614 : FluxStationaryEstimate) (h615 : FluxPlanarL2Estimate)
    (h616 : FluxHeatDifferenceEstimate) (hP : BallPoincareEstimate)
    (h817 : LocalBoundednessEstimate) (h832 : InteriorGradientEstimate)
    (h836 : InteriorRegularRepresentative)
    (d : ℕ) [Fact (2 ≤ d)] (L r₀ p : ℝ) (hp : 2 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Q : EnvironmentLaw d L r₀) (ζ : SourceMollifier d)
      (R : ℝ) (hR : 1 ≤ R) (i : Fin d)
      (u : FieldPair d → Vec d → ℝ) (S : FieldPair d → Vec d → Mat d),
      IsNormalizedCanonicalScalarCorrector Q i ζ R hR 0
        (fun ω x => u ω x.ofLp) →
      HasHeatSelectedSkewCorrectorColumn (Fact.out : 2 ≤ d) Q i S →
      (∫⁻ ω, ∫⁻ y,
        ENNReal.ofReal (|u ω (-y) - ⨍ z in ball (0 : Vec d) (2 * R), u ω z ∂volume| ^ p) +
        ENNReal.ofReal (frobeniusNorm (S ω (-y) - Matrix.of (fun j k =>
          ⨍ z in ball (0 : Vec d) (2 * R), S ω z j k ∂volume)) ^ p)
        ∂mollifierCenterMeasure d R ∂reducedEnvironmentLaw Q) ≤
          ENNReal.ofReal (C * correctorAmplitude d R ^ p) := by
  obtain ⟨A, hA⟩ := correctorMoments_of_literature
    h45 h46 h47 h68 h614 h615 h616 hP h817 h832 h836 d L r₀ p hp
  obtain ⟨D, hD, hcompare⟩ := exists_lintegral_mollifierCenterMeasure_le_ball_average d
  refine ⟨D * (|A| + 1), by positivity, ?_⟩
  intro Q ζ R hR i u S hu hS
  have hb := (hA Q ζ).2 R hR 0 i (fun ω x => u ω x.ofLp) S hu hS
  simp only [centered_scalar_flux_average_toLp, WithLp.ofLp_zero] at hb
  let F : FieldPair d → Vec d → ℝ≥0∞ := fun ω x =>
    ENNReal.ofReal (|u ω x - ⨍ z in ball (0 : Vec d) (2 * R), u ω z ∂volume| ^ p) +
      ENNReal.ofReal (frobeniusNorm (S ω x - Matrix.of (fun j k =>
        ⨍ z in ball (0 : Vec d) (2 * R), S ω z j k ∂volume)) ^ p)
  change (∫⁻ ω, ∫⁻ y, F ω (-y) ∂mollifierCenterMeasure d R
    ∂reducedEnvironmentLaw Q) ≤ _
  calc
    _ ≤ ∫⁻ ω, ENNReal.ofReal D * (⨍⁻ x in ball (0 : Vec d) (2 * R), F ω x ∂volume)
        ∂reducedEnvironmentLaw Q :=
      lintegral_mono fun ω => hcompare R (zero_lt_one.trans_le hR) (F ω)
    _ = ENNReal.ofReal D * (∫⁻ ω, ⨍⁻ x in ball (0 : Vec d) (2 * R), F ω x ∂volume
        ∂reducedEnvironmentLaw Q) := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ENNReal.ofReal D * ENNReal.ofReal (A * correctorAmplitude d R ^ p) :=
      mul_le_mul_right hb _
    _ ≤ ENNReal.ofReal ((D * (|A| + 1)) * correctorAmplitude d R ^ p) := by
      rw [← ENNReal.ofReal_mul hD.le]
      apply ENNReal.ofReal_le_ofReal
      calc
        _ ≤ D * ((|A| + 1) * correctorAmplitude d R ^ p) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
            (by linarith [le_abs_self A]) (Real.rpow_nonneg (by
              unfold correctorAmplitude; split <;> positivity) p)) hD.le
        _ = _ := mul_assoc _ _ _ |>.symm

end EinsteinRelation.Correctors
