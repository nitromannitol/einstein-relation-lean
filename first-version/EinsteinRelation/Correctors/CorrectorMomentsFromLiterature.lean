import EinsteinRelation.Correctors.CorrectorLargeRadiusMomentsFromLiterature
import EinsteinRelation.Correctors.CorrectorGradientMomentsFromLiterature
open MeasureTheory
open EinsteinRelation.Correctors.NormalizedScalarPhysicalLawTransportSupport
open EinsteinRelation.Correctors.NormalizedSpatialRepresentativeSupport
open EinsteinRelation.Correctors.StationarySpatialRealization
namespace EinsteinRelation.Correctors
open External.AKM External.GilbargTrudinger HeatSelectedSkewMeaning
/-- Lemma 5.1, `paper/main.tex:709-716,718-745`, with the exact frozen
statement and only the eleven frozen literature estimates as hypotheses. -/
theorem correctorMoments_of_literature
    (h45 : ScalarStationaryEstimate) (h46 : ScalarPlanarL2Estimate)
    (h47 : ScalarHeatDifferenceEstimate) (h68 : FluxGradientEstimate)
    (h614 : FluxStationaryEstimate) (h615 : FluxPlanarL2Estimate)
    (h616 : FluxHeatDifferenceEstimate) (hP : BallPoincareEstimate)
    (h817 : LocalBoundednessEstimate) (h832 : InteriorGradientEstimate)
    (h836 : InteriorRegularRepresentative) :
  ∀ (d : ℕ) [Fact (2 ≤ d)] (Λ₀ r₀ : ℝ) (m : ℝ), 2 ≤ m → ∃ C : ℝ,
    ∀ (Q : EnvironmentLaw d Λ₀ r₀) (ζ : SourceMollifier d),
      (∀ i : Fin d,
        ∫⁻ ω, ENNReal.ofReal
            (euclideanNorm
              ((spatialRealization (canonicalCorrectorGradient Q i :
                  Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
                ((0 : Vec d), ω)).ofLp) ^ m)
          ∂(reducedEnvironmentLaw Q) ≤ ENNReal.ofReal C) ∧
      ∀ (R : ℝ) (hR : 1 ≤ R) (y : Point d) (i : Fin d)
        (φ : FieldPair d → Point d → ℝ) (σ : FieldPair d → Vec d → Mat d),
        IsNormalizedCanonicalScalarCorrector Q i ζ R hR y φ →
        HasHeatSelectedSkewCorrectorColumn (Fact.out : 2 ≤ d) Q i σ →
        ∫⁻ ω, (⨍⁻ x in Metric.ball y (2 * R),
            (ENNReal.ofReal (|φ ω x - (⨍ z in Metric.ball y (2 * R), φ ω z ∂volume)| ^ m) +
              ENNReal.ofReal
                (frobeniusNorm
                  (σ ω (WithLp.ofLp x) -
                    Matrix.of (fun (a b : Fin d) =>
                      ⨍ z in Metric.ball y (2 * R), σ ω (WithLp.ofLp z) a b ∂volume)) ^ m))
            ∂volume)
          ∂(reducedEnvironmentLaw Q)
          ≤ ENNReal.ofReal (C * EinsteinRelation.Correctors.correctorAmplitude d R ^ m) := by
  intro d hd L r₀ p hp
  by_cases hL : 1 ≤ L
  · by_cases hr₀ : 1 ≤ r₀
    · obtain ⟨G, hG⟩ := correctorGradientMoments_of_literature
        h45 h46 h68 h614 h615 hP h817 h832 h836 d (Fact.out : 2 ≤ d) L r₀ p hp
      obtain ⟨M, hM, hlarge⟩ := exists_largeRadius_corrector_moment_bound_of_literature
        h45 h46 h47 h68 h614 h615 h616 hP h817 h832 h836 d L r₀ p hL hr₀ hp
      refine ⟨|G| + M + 1, ?_⟩
      intro Q ζ
      constructor
      · intro i
        exact (hG Q i).trans (ENNReal.ofReal_le_ofReal (by linarith [le_abs_self G]))
      · intro R hR y i φ σ hφ hσ
        apply (hlarge Q ζ R hR y i φ σ hφ hσ).trans
        apply ENNReal.ofReal_le_ofReal
        exact mul_le_mul_of_nonneg_right (by linarith [abs_nonneg G])
          (Real.rpow_nonneg (by unfold correctorAmplitude; split_ifs <;> positivity) p)
    · exact ⟨0, fun Q _ => (hr₀ Q.range_parameter).elim⟩
  · exact ⟨0, fun Q _ => (hL Q.ellipticity_parameter).elim⟩
end EinsteinRelation.Correctors
