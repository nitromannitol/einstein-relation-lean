import EinsteinRelation.Correctors.JointLocalMajorantCentering
import EinsteinRelation.Correctors.AKMPhysicalJointLocalBounds
import EinsteinRelation.Correctors.AKMPhysicalPotentials
import EinsteinRelation.Correctors.AKMScalarGaugeProductionTransfer
import EinsteinRelation.Correctors.AKMPhysicalFluxGaugeIdentification
import EinsteinRelation.Correctors.AKMUnitFluxConstruction
import EinsteinRelation.Correctors.CenteredPhysicalTransfer
import EinsteinRelation.Correctors.CenteredEuclideanTransport
import EinsteinRelation.Correctors.CenteredMomentAddition
open MeasureTheory
namespace EinsteinRelation.Correctors
open External.AKM External.GilbargTrudinger HeatSelectedSkewMeaning
open Environment.AKMTestIntegralSupport ReductionImageV3
open NormalizedSpatialRepresentativeSupport NormalizedScalarPhysicalLawTransportSupport
/-- Source: `paper/main.tex:727-745`. Uniform physical L² majorants
control exactly the centered scalar-plus-tensor expression of Lemma 5.1. -/
theorem exists_centeredMoment_bound_of_physical_majorants
    (h817 : LocalBoundednessEstimate) (h68 : FluxGradientEstimate)
    (hP : BallPoincareEstimate) (h832 : InteriorGradientEstimate)
    (h836 : InteriorRegularRepresentative)
    (d : ℕ) [Fact (2 ≤ d)] (L p : ℝ) (hL : 1 ≤ L) (hp : 2 ≤ p) :
    ∃ A : ℝ, 0 < A ∧ ∀ {r₀ : ℝ} (Q : EnvironmentLaw d L r₀) (i : Fin d)
      (ψ : Corrector (actualCoefficientLaw Q) (halfDirection i)),
      CanonicalAKMGradientIdentification Q i ψ →
      ∀ (S : FluxCorrector (scaledAKMCorrector ψ 2))
      (σ : FieldPair d → Vec d → Mat d),
      HasHeatSelectedSkewCorrectorColumn (Fact.out : 2 ≤ d) Q i σ →
      ∀ (ζ : SourceMollifier d) (R : ℝ) (hR : 1 ≤ R) (y : Point d)
      (φ : FieldPair d → Point d → ℝ),
      IsNormalizedCanonicalScalarCorrector Q i ζ R hR y φ →
      ∀ (c : PhysicalField d L → ℝ) (b : PhysicalField d L → Mat d),
      Measurable b → ∀ B : ℝ,
      (∀ z ∈ ball y.ofLp (2 * R), ∃ U V : PhysicalField d L → ℝ,
        AEMeasurable U (physicalReferenceLaw Q) ∧ AEMeasurable V (physicalReferenceLaw Q) ∧
        (∀ ω, 0 ≤ U ω) ∧ (∀ ω, 0 ≤ V ω) ∧
        (∀ᵐ ω ∂physicalReferenceLaw Q,
          Real.sqrt (∫ x in ball z 4, |physicalAKMScalarPotential Q ψ ω x - c ω| ^ 2 ∂volume) ≤ U ω ∧
          Real.sqrt (∫ x in ball z 4,
            frobeniusNorm (physicalAKMFluxPotential Q ψ S ω x - b ω) ^ 2 ∂volume) ≤ V ω) ∧
        (∫⁻ ω, ENNReal.ofReal (U ω ^ p) ∂physicalReferenceLaw Q) ≤ ENNReal.ofReal B ∧
        (∫⁻ ω, ENNReal.ofReal (V ω ^ p) ∂physicalReferenceLaw Q) ≤ ENNReal.ofReal B) →
      (∫⁻ ω, ⨍⁻ x in Metric.ball y (2 * R),
        ENNReal.ofReal (|φ ω x - ⨍ z in Metric.ball y (2 * R), φ ω z ∂volume| ^ p) +
        ENNReal.ofReal (frobeniusNorm (σ ω x.ofLp - Matrix.of (fun j k =>
          ⨍ z in Metric.ball y (2 * R), σ ω z.ofLp j k ∂volume)) ^ p) ∂volume
        ∂reducedEnvironmentLaw Q) ≤ ENNReal.ofReal (A * (max B 0 + 1)) := by
  have hd : 0 < d := by have := (Fact.out : 2 ≤ d); omega
  obtain ⟨C, hC, hvalue⟩ := ae_physicalAKM_joint_local_bounds h817 h68 hP h832 h836 d L hL
  obtain ⟨A, hA, hcenter⟩ := joint_centered_moments_of_local_L2_majorants d hd p C hp hC
  refine ⟨2 * A, by positivity, ?_⟩
  intro r₀ Q i ψ hid S σ hσ ζ R hR y φ hφ c b hbm B hlocal
  classical
  letI := physicalReferenceLaw_probability Q
  let μ := volume.restrict (ball y.ofLp (2 * R))
  have hR0 : 0 < 2 * R := by linarith
  letI : IsFiniteMeasure μ := isFiniteMeasure_restrict_euclideanBall y.ofLp (2 * R) hR0
  letI : NeZero μ := ⟨by
    intro h
    have hh : μ Set.univ = 0 := by rw [h]; simp
    have hp := (ENNReal.toReal_pos_iff.mp (ball_volume_pos_finite d (2 * R) hR0)).1
    exact hp.ne' (by simpa [μ, volume_euclideanBall_center] using hh)⟩
  let f : PhysicalField d L → Vec d → ℝ := fun ω x => φ (reduce ω.1) (WithLp.toLp 2 x)
  let u := physicalAKMScalarPotential Q ψ
  let T := physicalAKMFluxPotential Q ψ S
  have hg := akmPotential_gauge_identification_production Q i ψ hid ζ R hR y φ hφ
  let a : PhysicalField d L → ℝ := fun ω => Classical.epsilon (fun c : ℝ =>
    f ω =ᵐ[volume] (fun x => u ω x + c))
  have ha : ∀ᵐ ω ∂physicalReferenceLaw Q,
      f ω =ᵐ[volume] (fun x => u ω x + a ω) :=
    hg.mono fun ω hω => Classical.epsilon_spec hω
  have hfm : Measurable (Function.uncurry f) := hφ.1.comp
    (measurable_snd.prodMk ((measurePreserving_physicalReduction Q).measurable.comp measurable_fst))
  have hTm : Measurable (Function.uncurry T) := measurable_physicalAKMFlux_potential Q i ψ S
  have hu := ae_physicalAKMPotential_affine_weakSolution Q i ψ hid
  have hT := ae_physicalAKMFlux_memLp_on_balls Q i ψ S
  have hi : ∀ᵐ ω ∂physicalReferenceLaw Q, Integrable (f ω) μ ∧
      ∀ j k, Integrable (fun x => T ω x j k) μ := by
    filter_upwards [hu, hT, ha] with ω hω hωT hg
    have huint : Integrable (u ω) μ := by
      simpa only [sub_zero] using ((hω y.ofLp (2 * R) hR0 0).1.integrable (by norm_num))
    exact ⟨(huint.add (integrable_const (a ω))).congr (ae_restrict_of_ae (Filter.EventuallyEq.symm hg)),
      fun j k => (hωT y.ofLp (2 * R) hR0 j k).integrable (by norm_num)⟩
  have hsource := ae_unitAKMCenteredFlux_eq_scaled_canonicalCenteredFlux Q i ψ hid
  have hv : ∀ᵐ ω ∂physicalReferenceLaw Q, ∀ x : Vec d,
      ∀ᵐ t ∂volume.restrict (ball x (1 / 4)),
        |u ω t - c ω| ≤ C * (1 +
          Real.sqrt (∫ s in ball x 4, |u ω s - c ω| ^ 2 ∂volume) +
          Real.sqrt (∫ s in ball x 4, frobeniusNorm (T ω s - b ω) ^ 2 ∂volume)) ∧
        frobeniusNorm (T ω t - b ω) ≤ C * (1 +
          Real.sqrt (∫ s in ball x 4, |u ω s - c ω| ^ 2 ∂volume) +
          Real.sqrt (∫ s in ball x 4, frobeniusNorm (T ω s - b ω) ^ 2 ∂volume)) := by
    filter_upwards [hvalue Q i ψ S hid hsource σ hσ] with ω hω
    exact fun x => hω x (c ω) (b ω)
  obtain ⟨hs, ht⟩ := hcenter (physicalReferenceLaw Q) f u T c a b hfm hTm hbm
    y.ofLp (2 * R) B hR0 hi ha hv hlocal
  have hs' : (∫⁻ ρ, ⨍⁻ x, ENNReal.ofReal
      (|φ ρ (WithLp.toLp 2 x) - ⨍ z, φ ρ (WithLp.toLp 2 z) ∂μ| ^ p) ∂μ
        ∂reducedEnvironmentLaw Q) ≤ ENNReal.ofReal (A * (max B 0 + 1)) := by
    apply le_trans _ hs
    rw [← (measurePreserving_physicalReduction Q).map_eq]
    exact lintegral_map_le _ _
  have ht' : (∫⁻ ρ, ⨍⁻ x, ENNReal.ofReal (frobeniusNorm (σ ρ x -
      Matrix.of (fun j k => ⨍ z, σ ρ z j k ∂μ)) ^ p) ∂μ ∂reducedEnvironmentLaw Q) ≤
      ENNReal.ofReal (A * (max B 0 + 1)) := by
    apply le_trans _ ht
    apply lintegral_centered_flux_le_of_physical_gauge
      (measurePreserving_physicalReduction Q) μ σ T p (hi.mono fun _ h => h.2)
    filter_upwards [ae_physicalAKMFlux_potential_gauge Q i ψ S hsource σ hσ] with ω hω
    intro j k
    obtain ⟨c, hc⟩ := hω j k
    refine ⟨-c, ?_⟩
    filter_upwards [ae_restrict_of_ae hc] with x hx
    change σ (reduce ω.1) x j k =
      r₀ / ellipticityScale L * S.potential
        (project (r₀ := r₀) Q.ellipticity_parameter ω) (r₀⁻¹ • x) j k + -c
    linarith
  calc
    _ = ∫⁻ ρ, ⨍⁻ x, ENNReal.ofReal
        (|φ ρ (WithLp.toLp 2 x) - ⨍ z, φ ρ (WithLp.toLp 2 z) ∂μ| ^ p) +
        ENNReal.ofReal (frobeniusNorm (σ ρ x - Matrix.of (fun j k => ⨍ z, σ ρ z j k ∂μ)) ^ p) ∂μ
        ∂reducedEnvironmentLaw Q := by
      apply lintegral_congr
      intro ρ
      exact centered_scalar_flux_average_toLp (φ ρ) (σ ρ) y (2 * R) p
    _ = _ := lintegral_laverage_centered_scalar_flux_add (reducedEnvironmentLaw Q) μ
      (fun ρ x => φ ρ (WithLp.toLp 2 x)) σ p (hφ.1.comp measurable_swap)
    _ ≤ ENNReal.ofReal (A * (max B 0 + 1)) + ENNReal.ofReal (A * (max B 0 + 1)) :=
      add_le_add hs' ht'
    _ = _ := by rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; congr 1; ring
end EinsteinRelation.Correctors
