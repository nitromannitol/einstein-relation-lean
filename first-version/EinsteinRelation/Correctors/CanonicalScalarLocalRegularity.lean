import EinsteinRelation.Correctors.GTBallRegularRepresentative
import EinsteinRelation.Correctors.CanonicalGlobalWeakPotential
import EinsteinRelation.Correctors.CanonicalHarmonicFromPoincare
import EinsteinRelation.Correctors.ScalarGaugeReconstruction

/-! Source: `paper/main.tex:694-704,735-737,762-766`. Every scalar
representative with the canonical weak gradient has continuous local
versions. Poincaré constructs the locally square integrable comparison
potential; equality of weak gradients supplies the constant gauge. -/

open MeasureTheory

namespace EinsteinRelation.Correctors
open External.AKM External.GilbargTrudinger
open NormalizedScalarPhysicalLawTransportSupport NormalizedSpatialRepresentativeSupport
open StationarySpatialRealization

/-- The existing scalar predicate supplies continuous local versions on
one common event, without any regularity premise on the supplied values. -/
theorem ae_normalizedScalarCorrector_continuousOn_representatives
    (hP : BallPoincareEstimate) (h836 : InteriorRegularRepresentative)
    {d : ℕ} [Fact (2 ≤ d)] {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) (i : Fin d)
    (ζ : SourceMollifier d) (R : ℝ) (hR : 1 ≤ R) (y : Point d)
    (φ : FieldPair d → Point d → ℝ)
    (hφ : IsNormalizedCanonicalScalarCorrector Q i ζ R hR y φ) :
    ∀ᵐ ω ∂reducedEnvironmentLaw Q, ∀ n : ℕ, ∃ v : Vec d → ℝ,
      ContinuousOn v (Metric.ball 0 ((n : ℝ) + 1)) ∧
      (fun x : Vec d => φ ω (WithLp.toLp 2 x)) =ᵐ[
        volume.restrict (Metric.ball 0 ((n : ℝ) + 1))] v := by
  let G : Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q) :=
    canonicalCorrectorGradient Q i
  have hd : 0 < d := by have := (Fact.out : 2 ≤ d); omega
  have hL : 0 ≤ L := zero_le_one.trans Q.ellipticity_parameter
  filter_upwards [hφ.2, ae_exists_canonical_global_weakPotential hP Q i,
    ae_spatialRealization_memLp_on_all_compacts (reducedEnvironmentLaw_stationary Q) G,
    ae_canonicalCorrectorFlux_hasWeakDivergence Q i,
    ae_spatial_canonicalCorrectorFlux Q i measurable_id,
    ActualImageLpStateTransport.ae_reducedEnvironmentLaw_mem_image Q]
    with ω hφω hu hG hdiv hflux himg
  obtain ⟨u, hw, hu, _⟩ := hu
  obtain ⟨_, hφw, _⟩ := hφω
  have hφw' : HasWeakGradient Set.univ
      (fun x : Vec d => φ ω (WithLp.toLp 2 x))
      (fun x => (G (translate x ω)).ofLp) := hφw
  obtain ⟨c, hc⟩ := weakPotentials_differ_by_constant hd hφw' hw
  have hdiv' : HasWeakDivergence Set.univ
      (fun x => (ω.1 x).mulVec (unitVector i + (G (translate x ω)).ofLp))
      (fun _ => 0) := by
    exact hdiv.congr_ae (by simpa only [Measure.restrict_univ] using hflux)
      (ae_eq_refl _)
  obtain ⟨η, hη, hηeq⟩ := himg
  have hb := sourceReducedBound_support Q.ellipticity_parameter hη
  have hB : 0 < sourceReducedBound L := zero_lt_one.trans_le hb.1
  have hell : IsElliptic (sourceReducedBound L) ω.1 := by
    simpa only [← hηeq] using hb.2.1
  have hlip : IsOperatorLipschitz (Real.exp (2 * L) * (L + 2 * L ^ 2)) ω.1 := by
    simpa only [← hηeq] using hb.2.2.2.1
  intro n
  let S : ℝ := ((d : ℝ) + 1) * ((n : ℝ) + 1)
  have hS : 0 < S := by dsimp [S]; positivity
  have hsub : Metric.ball (0 : Vec d) ((n : ℝ) + 1) ⊆ ball 0 S := by
    intro x hx
    change euclideanNorm (x - 0) < S
    rw [sub_zero]
    exact (euclideanNorm_le_dimension_mul_norm x).trans_lt
      (mul_lt_mul_of_pos_left (by simpa only [Metric.mem_ball, dist_zero_right] using hx)
        (by positivity))
  have hg : MemLp (fun x => (G (translate x ω)).ofLp) 2
      (volume.restrict (ball (0 : Vec d) (2 * S))) := by
    apply memLp_pi_iff.mpr
    intro j
    exact ((hG (Metric.closedBall 0 (2 * S)) (isCompact_closedBall _ _)).mono_measure
      (Measure.restrict_mono_set volume
        (euclideanBall_subset_coordinateClosedBall (2 * S) (by positivity)))).eval_piLp j
  obtain ⟨v, hv, hveq⟩ := exists_continuousOn_scalar_corrector_ball_of_gt h836
    (Fact.out : 2 ≤ d) ω.1 (sourceReducedBound L)
    (Real.exp (2 * L) * (L + 2 * L ^ 2)) S hB (by positivity) hS hell hlip
    i u _ (hu _ (by positivity)) hg
    (fun j => HasWeakPartialDerivative.restrict_subset (Set.subset_univ _) MeasurableSet.univ (hw j))
    (HasWeakDivergence.restrict_subset (Set.subset_univ _) MeasurableSet.univ hdiv')
  refine ⟨fun x => v x + c, (hv.mono hsub).add continuousOn_const, ?_⟩
  filter_upwards [ae_restrict_of_ae hc,
    hveq.filter_mono (ae_mono (Measure.restrict_mono_set volume hsub))] with x hx hvx
  exact hx.trans (congrArg (· + c) hvx)

end EinsteinRelation.Correctors
