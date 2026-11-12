import EinsteinRelation.Correctors.SpatialLocalL2Dilation
import EinsteinRelation.Correctors.SpatialBallLocalL2Support

/-! Source: `paper/main.tex:722,756`. Actual local L² convergence
transports with the Haar Jacobian under physical space dilation. -/
open MeasureTheory Filter Topology
open scoped ENNReal
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

/-- The restricted L² norm has exactly the square root of the spatial
Haar Jacobian. No global integrability is required. -/
theorem eLpNorm_two_dilation_ball {d : ℕ} (f : Vec d → ℝ)
    (r R : ℝ) (hr : 0 < r)
    (hf : MemLp f 2 (volume.restrict (ball 0 (r * R)))) :
    eLpNorm (fun x => f (r • x)) 2 (volume.restrict (ball 0 R)) =
      (ENNReal.ofReal |(r ^ d)⁻¹|) ^ (1 / (2 : ℝ≥0∞)).toReal *
        eLpNorm f 2 (volume.restrict (ball 0 (r * R))) := by
  have hm (S : ℝ) : MeasurableSet (ball (0 : Vec d) S) := by
    unfold ball euclideanNorm euclideanSq dot
    exact (isOpen_lt (by fun_prop) continuous_const).measurableSet
  let g := (ball (0 : Vec d) (r * R)).indicator f
  have hI : MemLp g 2 volume := (memLp_indicator_iff_restrict (hm _)).mpr hf
  have hJ : MemLp g 2 (Measure.map (fun x : Vec d => r • x) volume) := by
    rw [Measure.map_addHaar_smul volume hr.ne']
    exact hI.smul_measure ENNReal.ofReal_ne_top
  have hind : (fun x : Vec d => g (r • x)) =
      (ball (0 : Vec d) R).indicator (fun x => f (r • x)) := by
    funext x
    have hx : r • x ∈ ball (0 : Vec d) (r * R) ↔ x ∈ ball (0 : Vec d) R := by
      simp only [ball, Set.mem_setOf_eq, sub_zero, euclideanNorm_smul r hr.le]
      exact mul_lt_mul_iff_right₀ hr
    by_cases hxR : x ∈ ball (0 : Vec d) R
    · simp only [g, Set.indicator_of_mem hxR, Set.indicator_of_mem (hx.mpr hxR)]
    · simp only [g, Set.indicator_of_notMem hxR, Set.indicator_of_notMem (mt hx.mp hxR)]
  have he := eLpNorm_map_measure (p := (2 : ℝ≥0∞)) hJ.aestronglyMeasurable
    ((continuous_const.smul continuous_id).measurable.aemeasurable)
  change eLpNorm g 2 (Measure.map (fun x : Vec d => r • x) volume) =
    eLpNorm (fun x : Vec d => g (r • x)) 2 volume at he
  rw [hind, eLpNorm_indicator_eq_eLpNorm_restrict (hm R)] at he
  rw [← he, Measure.map_addHaar_smul volume hr.ne',
    eLpNorm_smul_measure_of_ne_top (by norm_num)]
  simp only [Module.finrank_fin_fun, smul_eq_mul, g,
    eLpNorm_indicator_eq_eLpNorm_restrict (hm _)]

/-- Local L² convergence on every integer origin ball survives fixed
space and amplitude dilations, with the two indices still independent. -/
theorem local_L2_zero_dilation {d : ℕ}
    (f : ℕ × ℕ → Vec d → ℝ)
    (hf : ∀ R : ℕ, ∀ n, MemLp (f n) 2
      (volume.restrict (ball 0 ((R : ℝ) + 1))))
    (hlim : ∀ R : ℕ, Tendsto (fun n => eLpNorm (f n) 2
      (volume.restrict (ball 0 ((R : ℝ) + 1)))) atTop (𝓝 0))
    (r b : ℝ) (hr : 0 < r) :
    ∀ R : ℕ,
      (∀ n, MemLp (fun x => b * f n (r • x)) 2
        (volume.restrict (ball 0 ((R : ℝ) + 1)))) ∧
      Tendsto (fun n => eLpNorm (fun x => b * f n (r • x)) 2
        (volume.restrict (ball 0 ((R : ℝ) + 1)))) atTop (𝓝 0) := by
  intro R
  have hmem (n : ℕ × ℕ) (S : ℝ) (hS : 0 < S) :
      MemLp (f n) 2 (volume.restrict (ball 0 S)) := by
    obtain ⟨N, hN⟩ := exists_nat_gt S
    exact (hf N n).mono_measure (Measure.restrict_mono_set volume (by
      intro x hx
      change euclideanNorm (x - 0) < S at hx
      change euclideanNorm (x - 0) < (N : ℝ) + 1
      linarith))
  refine ⟨fun n => by
    simpa only [smul_eq_mul] using
      memLp_two_on_euclidean_balls_dilation (f n) (hmem n) r b hr
        ((R : ℝ) + 1) (by positivity), ?_⟩
  obtain ⟨N, hN⟩ := exists_nat_gt (r * ((R : ℝ) + 1))
  have hsub : ball (0 : Vec d) (r * ((R : ℝ) + 1)) ⊆ ball 0 ((N : ℝ) + 1) := by
    intro x hx
    change euclideanNorm (x - 0) < r * ((R : ℝ) + 1) at hx
    change euclideanNorm (x - 0) < (N : ℝ) + 1
    linarith
  let J : ℝ≥0∞ := (ENNReal.ofReal |(r ^ d)⁻¹|) ^ (1 / (2 : ℝ≥0∞)).toReal
  have hJ : J ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top
  have hupper : Tendsto (fun n => ‖b‖ₑ * (J * eLpNorm (f n) 2
      (volume.restrict (ball 0 ((N : ℝ) + 1))))) atTop (𝓝 0) := by
    have h1 := ENNReal.Tendsto.const_mul (hlim N) (Or.inr hJ)
    have h2 := ENNReal.Tendsto.const_mul h1 (Or.inr (enorm_ne_top (x := b)))
    simpa only [mul_zero] using h2
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
    (fun _ => zero_le _) ?_
  intro n
  dsimp only
  rw [show (fun x => b * f n (r • x)) = b • (fun x => f n (r • x)) by rfl,
    eLpNorm_const_smul, eLpNorm_two_dilation_ball (f n) r ((R : ℝ) + 1) hr
      (hmem n _ (by positivity))]
  exact mul_le_mul (le_refl _) (mul_le_mul (le_refl _)
    (eLpNorm_mono_measure (f n) (Measure.restrict_mono_set volume hsub))
      (zero_le _) (zero_le _)) (zero_le _) (zero_le _)

end EinsteinRelation.Correctors
