import EinsteinRelation.Correctors.AKMPhysicalFluxGaugeIdentification
import EinsteinRelation.Correctors.AKMUnitFluxConstruction
import EinsteinRelation.Correctors.StationarySpatialWeakPotentials

/-! Source: `paper/main.tex:733-745`. Local Sobolev data for the actual
canonical heat-selected flux potential, obtained from the frozen AKM
construction and its proved physical gauge identification. -/
open MeasureTheory
namespace EinsteinRelation.Correctors
open External.AKM HeatSelectedSkewMeaning Environment.AKMTestIntegralSupport ReductionImageV3

/-- The literal selected heat gradient has local L² coordinates on every
Euclidean ball. The heat-selection definition uses coordinate balls;
only a proved inclusion is used to restrict them. -/
theorem memLp_heatSelectedGradient_on_euclidean_balls
    {d : ℕ} {G : Vec d → Vec d} {ρ : FieldPair d}
    {F : FieldPair d → Fin d → Fin d → Fin d → ℝ}
    (hF : IsIteratedAKMHeatGradientAt G ρ F) (j k : Fin d) :
    ∀ R : ℝ, 0 < R → MemLp
      (fun x : Vec d => fun l : Fin d => F (translate x ρ) j k l) 2
      (volume.restrict (ball 0 R)) := by
  intro R hR
  obtain ⟨N, hN⟩ := exists_nat_gt R
  have hs : ball (0 : Vec d) R ⊆ Metric.ball 0 ((N + 1 : ℕ) : ℝ) := by
    intro x hx
    have hx' := euclideanBall_subset_coordinateClosedBall R hR.le hx
    have hR' : R < ((N + 1 : ℕ) : ℝ) := by exact_mod_cast (hN.trans_le (by simp))
    exact (Metric.closedBall_subset_ball hR') hx'
  apply memLp_pi_iff.mpr
  intro l
  exact ((hF j k l N).2.2.1).mono_measure (Measure.restrict_mono_set volume hs)

/-- Every canonical heat-selected skew potential has the genuine local
L² data required by the local Poisson estimate. No regularity or local
integrability premise is added to the source-facing corrector predicate. -/
theorem ae_canonicalFlux_local_memLp
    (h68 : FluxGradientEstimate)
    (hP : External.GilbargTrudinger.BallPoincareEstimate)
    {d : ℕ} [Fact (2 ≤ d)] {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀)
    (i : Fin d) (σ : FieldPair d → Vec d → Mat d)
    (hσ : HasHeatSelectedSkewCorrectorColumn (Fact.out : 2 ≤ d) Q i σ) :
    ∃ F : FieldPair d → Fin d → Fin d → Fin d → ℝ,
      (∀ᵐ ρ ∂reducedEnvironmentLaw Q,
        HasSourceSkewCorrectorColumnAt (Fact.out : 2 ≤ d) Q i σ ρ ∧
        HasSelectedHeatGradientRepresentative (σ ρ) F ρ) ∧
      ∀ᵐ ω ∂physicalReferenceLaw Q, ∀ j k : Fin d, ∀ R : ℝ, 0 < R →
        MemLp (fun x => σ (reduce ω.1) x j k) 2 (volume.restrict (ball 0 R)) ∧
        MemLp (fun x : Vec d => fun l : Fin d => F (translate x (reduce ω.1)) j k l) 2
          (volume.restrict (ball 0 R)) := by
  obtain ⟨F, hFm, hF⟩ := hσ
  obtain ⟨_, _, hex⟩ := exists_unitAKMFluxCorrector_with_canonical_source
    h68 hP d L r₀ 2 Q.ellipticity_parameter (by norm_num)
  obtain ⟨φ, S, hsrc, _⟩ := hex Q i
  have hgauge := ae_physicalAKMFlux_potential_gauge Q i φ S hsrc σ ⟨F, hFm, hF⟩
  have hlocal := (measurePreserving_akmProject Q).quasiMeasurePreserving.ae
    S.locally_square_integrable
  have hFphysical := (measurePreserving_physicalReduction Q).quasiMeasurePreserving.ae hF
  refine ⟨F, hF.mono (fun ρ hρ => ⟨hρ.1, hρ.2.2⟩), ?_⟩
  filter_upwards [hgauge, hlocal, hFphysical] with ω hg hl hf
  intro j k
  obtain ⟨c, hc⟩ := hg j k
  have hr : 0 < r₀ := zero_lt_one.trans_le Q.range_parameter
  have hu := memLp_two_on_euclidean_balls_dilation
    (fun x => S.potential (project (r₀ := r₀) Q.ellipticity_parameter ω) x j k)
    (fun R hR => (hl R hR j k).1) r₀⁻¹ (r₀ / ellipticityScale L) (inv_pos.mpr hr)
  intro R hR
  have hvol := ENNReal.toReal_pos_iff.mp (ball_volume_pos_finite d R hR)
  letI : IsFiniteMeasure (volume.restrict (ball (0 : Vec d) R)) :=
    isFiniteMeasure_restrict.mpr hvol.2.ne
  constructor
  · apply (memLp_congr_ae (ae_restrict_of_ae (hc.mono (fun x hx =>
      show σ (reduce ω.1) x j k =
        (r₀ / ellipticityScale L) * S.potential
          (project (r₀ := r₀) Q.ellipticity_parameter ω) (r₀⁻¹ • x) j k - c by
        linarith)))).mpr
    exact (hu R hR).sub (memLp_const c)
  · exact memLp_heatSelectedGradient_on_euclidean_balls hf.2.1 j k R hR

end EinsteinRelation.Correctors
