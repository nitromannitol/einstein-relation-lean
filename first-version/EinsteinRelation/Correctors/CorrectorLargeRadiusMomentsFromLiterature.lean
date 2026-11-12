import EinsteinRelation.Correctors.AKMPhysicalMajorantCenteredBound
import EinsteinRelation.Correctors.AKMPhysicalPlanarLargeGaugeData
import EinsteinRelation.Correctors.AKMPhysicalJointStationaryData
import EinsteinRelation.Correctors.AKMJointPlanarOscillationMoments
import EinsteinRelation.Correctors.LocalMomentMeasurability
import EinsteinRelation.Correctors.CorrectorAmplitudeLowerBound
open MeasureTheory
namespace EinsteinRelation.Correctors
open External.AKM External.GilbargTrudinger HeatSelectedSkewMeaning
open Environment.AKMTestIntegralSupport ReductionImageV3
open NormalizedSpatialRepresentativeSupport NormalizedScalarPhysicalLawTransportSupport
/-- Source: `paper/main.tex:709-716,718-745`. The large-radius assertion
of Lemma 5.1, with its constant uniform before the law and spatial centers. -/
theorem exists_largeRadius_corrector_moment_bound_of_literature
    (h45 : ScalarStationaryEstimate) (h46 : ScalarPlanarL2Estimate)
    (h47 : ScalarHeatDifferenceEstimate) (h68 : FluxGradientEstimate)
    (h614 : FluxStationaryEstimate) (h615 : FluxPlanarL2Estimate)
    (h616 : FluxHeatDifferenceEstimate) (hP : BallPoincareEstimate)
    (h817 : LocalBoundednessEstimate) (h832 : InteriorGradientEstimate)
    (h836 : InteriorRegularRepresentative)
    (d : ℕ) [Fact (2 ≤ d)] (L r₀ p : ℝ)
    (hL : 1 ≤ L) (hr₀ : 1 ≤ r₀) (hp : 2 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Q : EnvironmentLaw d L r₀) (ζ : SourceMollifier d)
      (R : ℝ) (hR : 1 ≤ R) (y : Point d) (i : Fin d)
      (φ : FieldPair d → Point d → ℝ) (σ : FieldPair d → Vec d → Mat d),
      IsNormalizedCanonicalScalarCorrector Q i ζ R hR y φ →
      HasHeatSelectedSkewCorrectorColumn (Fact.out : 2 ≤ d) Q i σ →
      (∫⁻ ω, ⨍⁻ x in Metric.ball y (2 * R),
        ENNReal.ofReal (|φ ω x - ⨍ z in Metric.ball y (2 * R), φ ω z ∂volume| ^ p) +
        ENNReal.ofReal (frobeniusNorm (σ ω x.ofLp - Matrix.of (fun j k =>
          ⨍ z in Metric.ball y (2 * R), σ ω z.ofLp j k ∂volume)) ^ p) ∂volume
        ∂reducedEnvironmentLaw Q) ≤ ENNReal.ofReal (C * correctorAmplitude d R ^ p) := by
  obtain ⟨A, hA, hcenter⟩ := exists_centeredMoment_bound_of_physical_majorants
    h817 h68 hP h832 h836 d L p hL hp
  by_cases hd : d = 2
  · subst d
    obtain ⟨B, hB, hmajorants⟩ := exists_physical_planar_largeGauge_local_majorants
      h46 h47 h615 h616 L r₀ p hL hr₀ hp
    obtain ⟨_, _, hdata⟩ := exists_joint_planar_akm_oscillation_moments
      h46 h68 h615 hP L r₀ p hL (by linarith)
    refine ⟨A * (B + 1), by positivity, ?_⟩
    intro Q ζ R hR y i φ σ hφ hσ
    obtain ⟨ψ, S, hid, _⟩ := hdata Q i
    let c : PhysicalField 2 L → ℝ := fun ω => (2 * r₀) *
      scalarHeatAverage (ψ.potential (project (r₀ := r₀) Q.ellipticity_parameter ω))
        (r₀⁻¹ • y.ofLp) (8 * R)
    let b : PhysicalField 2 L → Mat 2 := fun ω => (r₀ / ellipticityScale L) •
      fluxHeatAverage (S.potential (project (r₀ := r₀) Q.ellipticity_parameter ω))
        (r₀⁻¹ • y.ofLp) (8 * R)
    have hbm : Measurable b := by
      exact ((measurable_fluxHeatAverage S.potential S.measurable_potential
        (r₀⁻¹ • y.ofLp) (8 * R)).comp (measurePreserving_akmProject Q).measurable).const_smul
          (r₀ / ellipticityScale L)
    have h := hcenter Q i ψ hid S σ hσ ζ R hR y φ hφ c b hbm
      (B * (Real.sqrt (Real.log (2 + R))) ^ p) (fun z hz =>
        hmajorants Q i ψ hid S R hR y.ofLp z (by
          change euclideanNorm (z - y.ofLp) < 2 * R at hz
          linarith))
    apply h.trans
    rw [max_eq_left (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have hT : 1 ≤ (Real.sqrt (Real.log (2 + R))) ^ p := by
      simpa [correctorAmplitude] using Real.rpow_le_rpow zero_le_one
        (one_le_correctorAmplitude 2 hR) (by linarith : 0 ≤ p)
    change A * (B * (Real.sqrt (Real.log (2 + R))) ^ p + 1) ≤
      A * (B + 1) * (Real.sqrt (Real.log (2 + R))) ^ p
    calc
      A * (B * (Real.sqrt (Real.log (2 + R))) ^ p + 1) ≤
          A * ((B + 1) * (Real.sqrt (Real.log (2 + R))) ^ p) :=
        mul_le_mul_of_nonneg_left (by nlinarith) hA.le
      _ = _ := by ring
  · have hd' : 2 < d := by have := (Fact.out : 2 ≤ d); omega
    obtain ⟨B, hB, hdata⟩ := exists_physical_joint_stationary_local_L2_data
      h45 h68 h614 hP d hd' L r₀ p hL hr₀ hp
    refine ⟨A * (B + 1), by positivity, ?_⟩
    intro Q ζ R hR y i φ σ hφ hσ
    letI := physicalReferenceLaw_probability Q
    obtain ⟨ψ, S, hψm, hid, _, hlocal⟩ := hdata Q i
    let u := physicalAKMScalarPotential Q ψ
    let T := physicalAKMFluxPotential Q ψ S
    have hum : Measurable (Function.uncurry u) :=
      measurable_const.mul (hψm.comp
        (((measurePreserving_akmProject Q).measurable.comp measurable_fst).prodMk
          (measurable_const.smul measurable_snd)))
    have hTm : Measurable (Function.uncurry T) := measurable_physicalAKMFlux_potential Q i ψ S
    have h := hcenter Q i ψ hid S σ hσ ζ R hR y φ hφ (fun _ => 0) (fun _ => 0)
      measurable_const B (fun z _ => by
        let U := fun ω => Real.sqrt (∫ x in ball z 4, |u ω x| ^ 2 ∂volume)
        let V := fun ω => Real.sqrt (∫ x in ball z 4, frobeniusNorm (T ω x) ^ 2 ∂volume)
        refine ⟨U, V, ?_, ?_, (fun _ => Real.sqrt_nonneg _), (fun _ => Real.sqrt_nonneg _),
          ?_, (hlocal z).1, (hlocal z).2⟩
        · simpa only [sub_zero] using
            (measurable_scalar_local_root u (fun _ => 0) hum measurable_const z 4).aemeasurable
        · simpa only [sub_zero] using
            (measurable_tensor_local_root T (fun _ => 0) hTm measurable_const z 4).aemeasurable
        · exact ae_of_all _ fun _ => by simp [U, V, u, T])
    simpa [max_eq_left hB.le, correctorAmplitude, show 3 ≤ d by omega] using h
end EinsteinRelation.Correctors
