import EinsteinRelation.Correctors.CoefficientLpEnergy
import EinsteinRelation.Correctors.EuclideanRmsNorm

open MeasureTheory
namespace EinsteinRelation.Correctors

/-- A cutoff equal to one controls the actual gradient norm on the smaller
region. Source: `paper/main.tex:798–806`; local endpoint estimates. -/
theorem cutoff_energy_restricted_L2_le {d : ℕ} {U V : Set (Vec d)}
    (hVU : V ⊆ U) (hV : MeasurableSet V)
    {χ : Vec d → ℝ} (hχ : IsSpatialTest U χ) (hχb : ∀ x, |χ x| ≤ 1)
    (hχV : ∀ x ∈ V, χ x = 1)
    (g : Lp (EuclideanSpace ℝ (Fin d)) 2 (volume.restrict U))
    {B : ℝ} (hB : 0 ≤ B)
    (he : (∫ x in U, χ x^2 * euclideanSq (g x).ofLp) ≤ B^2) :
    MemLp (fun x => euclideanNorm (g x).ofLp) 2 (volume.restrict V) ∧
      (eLpNorm (fun x => euclideanNorm (g x).ofLp) 2 (volume.restrict V)).toReal ≤ B := by
  have hn (x : Vec d) : euclideanNorm (g x).ofLp = ‖g x‖ := by
    simpa using TimeChange.euclideanNorm_eq_norm_toLp (g x).ofLp
  have hmU : MemLp (fun x => euclideanNorm (g x).ofLp) 2 (volume.restrict U) := by
    simpa only [hn] using (Lp.memLp g).norm
  have hm := hmU.mono_measure (Measure.restrict_mono_set volume hVU)
  have hpos x : 0 ≤ euclideanSq (g x).ofLp := by
    unfold euclideanSq dot
    exact Finset.sum_nonneg fun j _ => mul_self_nonneg _
  have hsq : Integrable (fun x => euclideanSq (g x).ofLp) (volume.restrict U) := by
    have heq x : euclideanNorm (g x).ofLp ^ 2 = euclideanSq (g x).ofLp :=
      Real.sq_sqrt (hpos x)
    simpa only [heq] using hmU.integrable_sq
  have hχm : MemLp (fun x => χ x^2) ⊤ (volume.restrict U) :=
    memLp_top_of_bound (hχ.1.continuous.aestronglyMeasurable.pow 2) 1
      (Filter.Eventually.of_forall fun x => by
        simpa only [Real.norm_eq_abs,abs_sq,sq_abs,one_pow] using
          pow_le_pow_left₀ (abs_nonneg _) (hχb x) 2)
  have hi : Integrable (fun x => χ x^2 * euclideanSq (g x).ofLp) (volume.restrict U) := by
    simpa only [mul_comm] using hsq.mul_of_top_right hχm
  have hsmall : (∫ x in V, euclideanSq (g x).ofLp) ≤ B^2 := by
    calc
      _ = ∫ x in V, χ x^2 * euclideanSq (g x).ofLp := by
        apply setIntegral_congr_fun hV
        intro x hx
        simp only [hχV x hx,one_pow,one_mul]
      _ ≤ ∫ x in U, χ x^2 * euclideanSq (g x).ofLp :=
        setIntegral_mono_set hi (Filter.Eventually.of_forall fun x => mul_nonneg (sq_nonneg _) (hpos x))
          (Filter.Eventually.of_forall hVU)
      _ ≤ _ := he
  refine ⟨hm,?_⟩
  have hnorm : (eLpNorm (fun x => euclideanNorm (g x).ofLp) 2
      (volume.restrict V)).toReal = Real.sqrt (∫ x in V, euclideanSq (g x).ofLp) := by
    rw [hm.eLpNorm_eq_integral_rpow_norm (by norm_num : (2 : ENNReal) ≠ 0)
      (by norm_num : (2 : ENNReal) ≠ ⊤),ENNReal.toReal_ofReal (by positivity),
      Real.sqrt_eq_rpow]
    congr 1
    · apply integral_congr_ae
      filter_upwards with x
      simp only [ENNReal.toReal_ofNat,Real.rpow_two,Real.norm_eq_abs,sq_abs,
        euclideanNorm,Real.sq_sqrt (hpos x)]
    · norm_num
  rw [hnorm]
  exact (Real.sqrt_le_sqrt hsmall).trans_eq (Real.sqrt_sq hB)

end EinsteinRelation.Correctors
