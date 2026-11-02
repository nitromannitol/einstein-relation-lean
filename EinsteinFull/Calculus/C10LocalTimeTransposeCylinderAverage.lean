import EinsteinFull.Calculus.C10LocalTimeTransposeAllDataTrace
import PDEFoundation.Measure.BallVolume
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators
noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation EinsteinFull

/-- The actual terminal transpose mass is controlled by its cylinder average. -/
theorem local_time_transpose_terminal_cylinder_average
    (d : ℕ) [Fact (2 ≤ d)] (Λ₀ : ℝ) (hΛ : 1 ≤ Λ₀) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (r₀ : ℝ) (Q : EnvironmentLaw d Λ₀ r₀)
      (i : Fin d) (ζ : ℂ)
      (P T : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)),
      IsComplexEnvironmentSemigroup Q i ζ P →
      IsComplexTransposeSemigroup Q P T →
    ∀ (f : Lp ℂ 2 (reducedLaw Q)),
    ∃ W : ℝ × FieldPair d → ℂ,
      Measurable W ∧
      (∀ s, (fun ω => W (s, ω)) =ᵐ[reducedLaw Q] T s.toNNReal f) ∧
      ∀ (t : ℝ≥0), 0 < (t : ℝ) →
        ∀ (ρ : ℝ) (z : Vec d), Real.sqrt (t : ℝ) ≤ ρ →
          ∀ᵐ ω ∂reducedLaw Q,
            (⨍ x in {x | euclideanNorm (x - z) ≤ ρ},
              ‖(T t f) (translate x ω)‖ ^ 2) ≤
            C * (1 + ‖ζ‖ * Real.sqrt (t : ℝ)) ^ 2 *
              (⨍ s in Icc ((t : ℝ) / 2) (t : ℝ),
                ⨍ x in {x | euclideanNorm (x - z) ≤ 2 * ρ},
                  ‖W (s, translate x ω)‖ ^ 2)
 := by
  obtain ⟨B, hB, htrace⟩ := local_time_transpose_all_data_ae_terminal_ball_L2 d
  let K := 10 * (Real.exp (2 * Λ₀) * Λ₀) ^ 3
  let D := (d : ℝ) * B ^ 2
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  refine ⟨(2 : ℝ) ^ d * (2 + K * (1 + D)), by positivity, ?_⟩
  intro r₀ Q i ζ P T hP hT f
  obtain ⟨W, hW, heW, hbound⟩ := htrace Λ₀ r₀ Q i ζ P T hP hT f
  refine ⟨W, hW, heW, ?_⟩
  intro t ht ρ z hρ
  have hsqrt : 0 < Real.sqrt (t : ℝ) := Real.sqrt_pos.2 ht
  have hr : 0 < ρ := hsqrt.trans_le hρ
  have hsq : Real.sqrt (t : ℝ) ^ (2 : ℕ) = (t : ℝ) := Real.sq_sqrt (by positivity)
  have htρ : (t : ℝ) ≤ ρ ^ 2 := by
    have hh := (sq_le_sq₀ hsqrt.le hr.le).2 hρ
    rwa [hsq] at hh
  have hball (r : ℝ) (hr : 0 < r) :
      {x : Vec d | euclideanNorm (x - z) ≤ r} = PDE.euclideanClosedBall z r := by
    ext x
    change Real.sqrt (euclideanSq (x - z)) ≤ r ↔ PDE.vecNormSq (x - z) ≤ r ^ 2
    rw [Real.sqrt_le_iff]
    exact and_iff_right hr.le
  have hvol (r : ℝ) (hr : 0 < r) :
      volume.real {x : Vec d | euclideanNorm (x - z) ≤ r} =
        r ^ d * (volume (PDE.euclideanClosedBall (0 : Vec d) 1)).toReal := by
    rw [hball r hr, PDE.euclideanClosedBall_eq_translateSet_smul_unit_of_pos z hr,
      MeasureTheory.measureReal_def, PDE.volume_translateSet_eq,
      PDE.volume_smul_set_toReal_of_pos hr]
  let v := volume.real {x : Vec d | euclideanNorm (x - z) ≤ ρ}
  have hv : 0 < v := by
    apply ENNReal.toReal_pos _ (isCompact_physical_euclidean_closedBall z ρ).measure_ne_top
    apply ne_of_gt
    exact (PDE.volume_euclideanBall_pos z hr).trans_le
      (measure_mono (by rw [hball ρ hr]; exact PDE.euclideanBall_subset_euclideanClosedBall z ρ))
  have hv2 : volume.real {x : Vec d | euclideanNorm (x - z) ≤ 2 * ρ} =
      (2 : ℝ) ^ d * v := by
    rw [hvol (2 * ρ) (by positivity)]
    dsimp [v]
    rw [hvol ρ hr, mul_pow]
    ring
  let F := (1 + ‖ζ‖ * Real.sqrt (t : ℝ)) ^ 2
  have hF : 1 ≤ F := by
    dsimp [F]
    nlinarith [mul_nonneg (norm_nonneg ζ) hsqrt.le]
  have hforce : (t : ℝ) * ‖ζ‖ ^ 2 ≤ F := by
    dsimp [F]
    have he : (t : ℝ) * ‖ζ‖ ^ 2 = (‖ζ‖ * Real.sqrt (t : ℝ)) ^ 2 := by
      rw [mul_pow, hsq]
      ring
    rw [he]
    nlinarith [mul_nonneg (norm_nonneg ζ) hsqrt.le]
  have hratio : (t : ℝ) / ρ ^ 2 ≤ 1 := (div_le_one (sq_pos_of_pos hr)).2 htρ
  have hcoef : 2 + K * ((t : ℝ) * ‖ζ‖ ^ 2 + D * ((t : ℝ) / ρ ^ 2)) ≤
      (2 + K * (1 + D)) * F := by
    have h1 := mul_le_mul_of_nonneg_left hratio hD
    have h2 := mul_le_mul_of_nonneg_left hF hD
    have h3 := mul_le_mul_of_nonneg_left (add_le_add hforce (h1.trans h2)) hK
    nlinarith only [h3, hF]
  filter_upwards [hbound ((t : ℝ) / 2) t (by positivity) (by linarith) z ρ hr] with ω hω
  simp only [Real.toNNReal_coe] at hω
  let M := ∫ s in Icc ((t : ℝ) / 2) (t : ℝ),
    ∫ x in {x | euclideanNorm (x - z) ≤ 2 * ρ}, ‖W (s, translate x ω)‖ ^ 2
  have hM : 0 ≤ M := integral_nonneg fun _ => integral_nonneg fun _ => sq_nonneg _
  have htime : volume.real (Icc ((t : ℝ) / 2) (t : ℝ)) = (t : ℝ) / 2 := by
    rw [Real.volume_real_Icc]
    rw [max_eq_left (by linarith)]
    ring
  have hnorm :
      v⁻¹ * (2 * (((t : ℝ) - (t : ℝ) / 2)⁻¹ +
        K * (‖ζ‖ ^ 2 + D / ρ ^ 2))) =
      ((2 : ℝ) ^ d * (2 + K * ((t : ℝ) * ‖ζ‖ ^ 2 + D * ((t : ℝ) / ρ ^ 2)))) *
        (((t : ℝ) / 2)⁻¹ * (((2 : ℝ) ^ d * v)⁻¹)) := by
    field_simp
    ring
  simp only [average_eq, measureReal_restrict_apply_univ, smul_eq_mul,
    integral_const_mul, htime, hv2]
  change v⁻¹ * _ ≤ ((2 : ℝ) ^ d * (2 + K * (1 + D))) * F *
    (((t : ℝ) / 2)⁻¹ * (((2 : ℝ) ^ d * v)⁻¹ * M))
  calc
    _ ≤ v⁻¹ * (2 * (((t : ℝ) - (t : ℝ) / 2)⁻¹ +
        K * (‖ζ‖ ^ 2 + D / ρ ^ 2)) * M) :=
      mul_le_mul_of_nonneg_left hω (inv_nonneg.2 hv.le)
    _ = ((2 : ℝ) ^ d * (2 + K * ((t : ℝ) * ‖ζ‖ ^ 2 + D * ((t : ℝ) / ρ ^ 2)))) *
        (((t : ℝ) / 2)⁻¹ * (((2 : ℝ) ^ d * v)⁻¹)) * M := by
      rw [← mul_assoc, hnorm]
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left hcoef (by positivity : 0 ≤ (2 : ℝ) ^ d)
      have hh' := mul_le_mul_of_nonneg_right hh
        (by positivity : 0 ≤ ((t : ℝ) / 2)⁻¹ * (((2 : ℝ) ^ d * v)⁻¹))
      have hh'' := mul_le_mul_of_nonneg_right hh' hM
      convert hh'' using 1
      dsimp [F]
      ring
end EinsteinFull.Blueprint
