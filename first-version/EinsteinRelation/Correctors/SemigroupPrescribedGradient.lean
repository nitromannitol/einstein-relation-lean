import EinsteinRelation.Correctors.ParabolicPrescribedEnergy
import EinsteinRelation.Correctors.SemigroupLocalL2Continuity
import EinsteinRelation.Correctors.WeakGradientBallGluing
import EinsteinRelation.Correctors.MeasurableWeakGradient
import EinsteinRelation.Correctors.PairedPDEAmplitude

open MeasureTheory
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

/-- Euclidean coordinate balls are relatively compact.
Source: `paper/main.tex:798–806`. -/
theorem isCompact_closure_originBall (d : ℕ) (R : ℝ) :
    IsCompact (closure (originBall d R)) := by
  let F : EuclideanSpace ℝ (Fin d) → Vec d := WithLp.ofLp
  have hc : IsCompact (F '' Metric.closedBall 0 R) :=
    (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin d)) R).image
      (PiLp.continuous_ofLp 2 _)
  apply hc.of_isClosed_subset isClosed_closure
  apply closure_minimal _ hc.isClosed
  intro x hx
  refine ⟨WithLp.toLp 2 x, ?_, rfl⟩
  change ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin d)) - 0‖ ≤ R
  rw [sub_zero, ← TimeChange.euclideanNorm_eq_norm_toLp]
  exact le_of_lt hx

/-- The unchanged scalar semigroup has a spatial weak gradient at each
positive time; cutoff existence is the elementary geometric input.
Source: `paper/main.tex:798–806`. -/
theorem semigroupSolution_exists_prescribed_gradient {d : ℕ} {K : ℝ}
    (hK : 0 < K)
    (hcut : ∀ r : ℝ, 0 < r → ∃ (χ : Vec d → ℝ) (L : ℝ), 0 ≤ L ∧
      IsSpatialTest (originBall d (2*r)) χ ∧ (∀ x, |χ x| ≤ 1) ∧
      (∀ x ∈ originBall d r, χ x = 1) ∧
      ∀ x, euclideanNorm (gradient χ x) ≤ L)
    {A : Coefficient d K} {v : Vec d → Vec d}
    {u : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    (hsol : IsSemigroupSolution A v u G) {t : ℝ} (ht : 0 < t) :
    ∃ H : Vec d → Vec d, HasWeakGradient Set.univ (fun x => u (t,x)) H := by
  apply exists_global_weakGradient_of_ball_gradients
  intro r hr
  obtain ⟨χ,L,hL,hχ,hχb,hχr,hχD⟩ := hcut r hr
  have hU := isCompact_closure_originBall d (2*r)
  have hV := isCompact_closure_originBall d r
  letI : IsFiniteMeasure (volume.restrict (originBall d (2*r))) :=
    isFiniteMeasure_restrict.mpr (ne_top_of_le_ne_top
      (hU.measure_ne_top (μ := volume)) (measure_mono subset_closure))
  letI : IsFiniteMeasure (volume.restrict (originBall d r)) :=
    isFiniteMeasure_restrict.mpr (ne_top_of_le_ne_top
      (hV.measure_ne_top (μ := volume)) (measure_mono subset_closure))
  have hopen (s : ℝ) : IsOpen (originBall d s) := by
    unfold originBall euclideanNorm euclideanSq dot
    exact isOpen_lt (by fun_prop) continuous_const
  obtain ⟨H,hw,_,_⟩ := parabolicSolution_prescribed_gradient_energy hK (half_pos ht)
    (by linarith : t/2 < t) (hopen (2*r))
    (show originBall d r ⊆ originBall d (2*r) from fun x hx =>
      lt_of_lt_of_le (show euclideanNorm x < r from hx)
        (show r ≤ 2*r by linarith only [hr])) (hopen r).measurableSet hsol.1
    (hsol.2.1 (t/2) t (2*r) (half_pos ht) (by linarith) (by positivity))
    (semigroupSolution_scalar_memLp_on_precompact hsol hV ht) hχ hχb hχr hL hχD
  exact ⟨H,hw⟩

/-- Recovery from the actual scalar field provides one jointly measurable
version of all prescribed-time whole-space gradients simultaneously.
Source: `paper/main.tex:798–806`. -/
theorem exists_measurable_prescribed_gradient_recovery {Ω : Type*} [MeasurableSpace Ω]
    {d : ℕ} (u : Ω → ℝ × Vec d → ℝ)
    (hum : Measurable (fun z : Ω × (ℝ × Vec d) => u z.1 z.2)) :
    ∃ H : Ω → ℝ × Vec d → Vec d,
      Measurable (fun z : Ω × (ℝ × Vec d) => H z.1 z.2) ∧
      ∀ ω t (G : Vec d → Vec d),
        HasWeakGradient Set.univ (fun x => u ω (t,x)) G →
          (fun x => H ω (t,x)) =ᵐ[volume] G := by
  let f : (Ω × ℝ) → Vec d → ℝ := fun z x => u z.1 (z.2,x)
  have hfm : Measurable (fun z : (Ω × ℝ) × Vec d => f z.1 z.2) :=
    hum.comp ((measurable_fst.fst).prodMk
      (measurable_fst.snd.prodMk measurable_snd))
  obtain ⟨H,hHm,hrec⟩ := exists_measurable_spatialGradient_recovery f hfm
  refine ⟨fun ω z => H (ω,z.1) z.2,?_,?_⟩
  · exact hHm.comp ((measurable_fst.prodMk measurable_snd.fst).prodMk measurable_snd.snd)
  · intro ω t G hG
    exact hrec (ω,t) G hG

/-- All positive-time weak gradients of a measurable actual semigroup
family admit one joint measurable version. Source: `paper/main.tex:798–806`. -/
theorem measurable_prescribed_gradient_of_semigroupSolutions {Ω : Type*}
    [MeasurableSpace Ω] {d : ℕ} {K : ℝ} (hK : 0 < K)
    (hcut : ∀ r : ℝ, 0 < r → ∃ (χ : Vec d → ℝ) (L : ℝ), 0 ≤ L ∧
      IsSpatialTest (originBall d (2*r)) χ ∧ (∀ x, |χ x| ≤ 1) ∧
      (∀ x ∈ originBall d r, χ x = 1) ∧
      ∀ x, euclideanNorm (gradient χ x) ≤ L)
    (P : Measure Ω) (A : Ω → Coefficient d K) (v : Ω → Vec d → Vec d)
    (u : Ω → ℝ × Vec d → ℝ) (G : Ω → ℝ × Vec d → Vec d)
    (hum : Measurable (fun z : Ω × (ℝ × Vec d) => u z.1 z.2))
    (hsol : ∀ᵐ ω ∂P, IsSemigroupSolution (A ω) (v ω) (u ω) (G ω)) :
    ∃ H : Ω → ℝ × Vec d → Vec d,
      Measurable (fun z : Ω × (ℝ × Vec d) => H z.1 z.2) ∧
      ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t →
        HasWeakGradient Set.univ (fun x => u ω (t,x)) (fun x => H ω (t,x)) := by
  obtain ⟨H,hHm,hrec⟩ := exists_measurable_prescribed_gradient_recovery u hum
  refine ⟨H,hHm,?_⟩
  filter_upwards [hsol] with ω hω
  intro t ht
  obtain ⟨J,hJ⟩ := semigroupSolution_exists_prescribed_gradient hK hcut hω ht
  apply hasWeakGradient_congr_ae isOpen_univ hJ Filter.EventuallyEq.rfl
  simpa only [Measure.restrict_univ] using (hrec ω t J hJ).symm

end EinsteinRelation.Correctors
