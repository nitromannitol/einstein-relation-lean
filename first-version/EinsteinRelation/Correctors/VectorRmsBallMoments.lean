import EinsteinRelation.Correctors.ScalarMomentAverage
import EinsteinRelation.Correctors.PlanarContinuousBallSupport
import Mathlib.Probability.ConditionalProbability
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace EinsteinRelation.Correctors
open External.AKM

/-- Euclidean spatial RMS inherits uniform slice moments; source
`paper/main.tex:864–886`. This uses the existing scalar averaging theorem. -/
theorem vectorRms_ball_moment_of_uniform_slices
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {d : ℕ} (s : ℝ) (hs : 0 < s) {p C : ℝ} (hp : 2 ≤ p) (hC : 0 ≤ C)
    (F : Ω × Vec d → Vec d) (hF : Measurable F)
    (hslices : ∀ x ∈ ball (0 : Vec d) s,
      MemLp (fun ω => euclideanNorm (F (ω,x))) (ENNReal.ofReal p) μ ∧
      eLpNorm (fun ω => euclideanNorm (F (ω,x))) (ENNReal.ofReal p) μ ≤ ENNReal.ofReal C) :
    MemLp (fun ω => vectorRms volume (ball 0 s) (fun x => F (ω,x)))
      (ENNReal.ofReal p) μ ∧
    eLpNorm (fun ω => vectorRms volume (ball 0 s) (fun x => F (ω,x)))
      (ENNReal.ofReal p) μ ≤ ENNReal.ofReal C := by
  have hball_meas : MeasurableSet (ball (0 : Vec d) s) :=
    (paired_isOpen_ball (0 : Vec d) s).measurableSet
  have hball := ball_volume_pos_finite d s hs
  have hball_pos : volume (ball (0 : Vec d) s) ≠ 0 :=
    (ENNReal.toReal_pos_iff.mp hball).1.ne'
  have hball_fin : volume (ball (0 : Vec d) s) ≠ ∞ :=
    (ENNReal.toReal_pos_iff.mp hball).2.ne
  have h_euclideanNorm_cont : Continuous (fun v : Vec d => euclideanNorm v) := by
    have hsum : Continuous (fun v : Vec d => ∑ j, v j * v j) := by
      apply continuous_finset_sum
      intro j _
      exact (continuous_apply j).mul (continuous_apply j)
    unfold euclideanNorm euclideanSq dot
    exact Real.continuous_sqrt.comp hsum
  have h_euclideanNorm_meas : Measurable (fun (z : Ω × Vec d) => euclideanNorm (F z)) :=
    h_euclideanNorm_cont.measurable.comp hF
  have h_sq_eq (v : Vec d) : euclideanSq v = (euclideanNorm v) ^ 2 := by
    rw [euclideanNorm]
    have h_nonneg : 0 ≤ euclideanSq v := by
      unfold euclideanSq dot
      exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
    rw [Real.sq_sqrt h_nonneg]
  -- Normalize the restriction of volume to the ball, making it a probability measure
  let ν := (volume (ball (0 : Vec d) s))⁻¹ • volume.restrict (ball (0 : Vec d) s)
  letI : IsProbabilityMeasure ν := ⟨by
    simp only [ν, Measure.smul_apply, smul_eq_mul, Measure.restrict_apply_univ]
    exact ENNReal.inv_mul_cancel hball_pos hball_fin⟩
  -- Extend f by zero outside the ball; the average over the ball equals the integral against ν
  let f : Ω × Vec d → ℝ := (Prod.snd ⁻¹' ball (0 : Vec d) s).indicator
    (fun z => euclideanNorm (F z))
  have hf_meas : Measurable f :=
    h_euclideanNorm_meas.indicator (hball_meas.preimage measurable_snd)
  have hf_mom (x : Vec d) : MemLp (fun ω => f (ω, x)) (ENNReal.ofReal p) μ ∧
      eLpNorm (fun ω => f (ω, x)) (ENNReal.ofReal p) μ ≤ ENNReal.ofReal C := by
    by_cases hx : x ∈ ball (0 : Vec d) s
    · simpa only [f, Set.indicator_of_mem, Set.mem_preimage, hx] using hslices x hx
    · simp only [f, Set.indicator_of_notMem, Set.mem_preimage, hx, not_false_eq_true]
      exact ⟨MemLp.zero, by simp⟩
  have h_scalar := (scalarL2_average_moment_le μ ν hp hC f hf_meas hf_mom).2
  -- Relate the integral against ν to the set average over the ball
  have h_integral_eq (ω : Ω) : (∫ x, f (ω, x) ^ 2 ∂ν) =
      ⨍ x in ball (0 : Vec d) s, (euclideanNorm (F (ω, x))) ^ 2 ∂volume := by
    rw [setAverage_eq']
    apply integral_congr_ae
    refine (Measure.ae_smul_measure (ae_restrict_mem hball_meas) _).mono fun x hx => ?_
    have hx_mem : x ∈ ball (0 : Vec d) s := hx
    simp only [f, Set.indicator_of_mem (show (ω, x) ∈ Prod.snd ⁻¹' ball (0 : Vec d) s from hx_mem),
      euclideanNorm]
  -- Combine with the identity euclideanSq = (euclideanNorm)^2
  have h_vectorRms_eq (ω : Ω) : vectorRms volume (ball 0 s) (fun x => F (ω, x)) =
      Real.sqrt (⨍ x in ball (0 : Vec d) s, (euclideanNorm (F (ω, x))) ^ 2 ∂volume) := by
    dsimp [vectorRms]
    congr 1
    exact setAverage_congr_fun hball_meas (Filter.Eventually.of_forall fun x _ => h_sq_eq (F (ω,x)))
  have h_eq_fun : (fun ω => vectorRms volume (ball 0 s) (fun x => F (ω, x))) =
      (fun ω => Real.sqrt (∫ x, f (ω, x) ^ 2 ∂ν)) := by
    ext ω
    rw [h_vectorRms_eq ω, h_integral_eq ω]
  rcases h_scalar with ⟨hmem, hnorm⟩
  refine ⟨?_, ?_⟩
  · rw [h_eq_fun]; exact hmem
  · rw [h_eq_fun]; exact hnorm
end EinsteinRelation.Correctors
