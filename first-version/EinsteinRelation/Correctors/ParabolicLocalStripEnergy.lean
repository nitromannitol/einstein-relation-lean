import EinsteinRelation.Correctors.PrescribedBallCutoff
import EinsteinRelation.Correctors.PositiveTimeCutoff
import EinsteinRelation.Correctors.ParabolicTensorCutoff

open MeasureTheory
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

/-- Local strip gradient energy follows from scalar energy on a larger
cylinder, with constants independent of the solution. Source:
`paper/main.tex:787–792,844–855`. -/
theorem parabolicSolution_local_strip_gradient_energy {d : ℕ} {K : ℝ}
    (hK : 0 < K) {a b R : ℝ} (ha : 0 < a) (hab : a < b) (hR : 0 < R) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ (A : Coefficient d K)
      (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d),
      IsParabolicSolution A (Set.Ioo (a/2) (b+a/2)) (originBall d (2*R)) u G →
      (∫ z in Set.Ioo a b ×ˢ originBall d R, euclideanNorm (G z)^2) ≤
        E * ∫ z in Set.Ioo (a/2) (b+a/2) ×ˢ originBall d (2*R), (u z)^2 := by
  obtain ⟨η,M,hη,hηc,hηs,hηb,hηone,hM,hηD⟩ := exists_positive_time_plateau ha hab
  obtain ⟨χ,L,hL,hχ,hχb,hχone,_hχD⟩ := exists_prescribed_spatial_ball_cutoff d R hR
  obtain ⟨N,hN⟩ := (hχ.2.1.fderiv ℝ).exists_bound_of_continuous
    (hχ.1.continuous_fderiv (by simp))
  have hN0 : 0 ≤ N := (norm_nonneg _).trans (hN 0)
  have hχD (x : Vec d) : ‖gradient χ x‖ ≤ N := by
    apply (pi_norm_le_iff_of_nonneg hN0).mpr
    intro j
    have hv : ‖unitVector j‖ ≤ 1 :=
      (pi_norm_le_iff_of_nonneg zero_le_one).mpr (fun k => by
        simp only [unitVector,Pi.single_apply,Real.norm_eq_abs]
        split_ifs <;> norm_num)
    exact ((fderiv ℝ χ x).le_opNorm (unitVector j)).trans
      ((mul_le_mul (hN x) hv (norm_nonneg _) hN0).trans_eq (mul_one N))
  let ζ : ℝ × Vec d → ℝ := fun z => η z.1 * χ z.2
  have hζ : ContDiff ℝ (⊤ : ℕ∞) ζ :=
    (hη.comp contDiff_fst).mul (hχ.1.comp contDiff_snd)
  have hζc : HasCompactSupport ζ := by
    simpa only [pow_one,mul_one] using
      hasCompactSupport_tensor_cutoff hηc hχ.2.1 1 (by decide) (fun _ => (1 : ℝ))
  have hζs : tsupport ζ ⊆ interior (Set.Ioo (a/2) (b+a/2)) ×ˢ originBall d (2*R) := by
    rw [interior_Ioo]
    apply Set.Subset.trans ?_ (Set.prod_mono hηs hχ.2.2)
    apply closure_minimal ?_ ((isClosed_tsupport η).prod (isClosed_tsupport χ))
    intro z hz
    exact ⟨subset_tsupport η (fun he => hz (by simp only [ζ,he,zero_mul])),
      subset_tsupport χ (fun he => hz (by simp only [ζ,he,mul_zero]))⟩
  let E := 2*M+4*K^2*(d : ℝ)*N^2
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hB := parabolic_tensor_cutoff_error_bound K hη hχ.1 hM hN0
    (fun t => by rw [abs_of_nonneg (hηb t).1]; exact (hηb t).2) hηD hχb hχD
  refine ⟨E,hE,?_⟩
  intro A u G hsol
  have hU : IsOpen (originBall d (2*R)) := by
    unfold originBall euclideanNorm euclideanSq dot
    exact isOpen_lt (by fun_prop) continuous_const
  have hlocal := parabolicSolution_cutoff_energy hK measurableSet_Ioo hU hsol hζ hζc hζs
  have hsub : Set.Ioo a b ×ˢ originBall d R ⊆
      Set.Ioo (a/2) (b+a/2) ×ˢ originBall d (2*R) := by
    intro z hz
    exact ⟨⟨by linarith [hz.1.1],by linarith [hz.1.2]⟩,
      (show euclideanNorm z.2 < 2*R from lt_trans hz.2 (by linarith))⟩
  have hV : MeasurableSet (Set.Ioo a b ×ˢ originBall d R) := by
    apply measurableSet_Ioo.prod
    unfold originBall euclideanNorm euclideanSq dot
    exact measurableSet_lt (by fun_prop) measurable_const
  calc
    _ = ∫ z in Set.Ioo a b ×ˢ originBall d R, ζ z^2*euclideanSq (G z) := by
      apply setIntegral_congr_fun hV
      intro z hz
      have he : ζ z = 1 := by
        dsimp [ζ]
        rw [hηone z.1 ⟨hz.1.1.le,hz.1.2.le⟩,hχone z.2 hz.2,one_mul]
      dsimp only
      rw [he,one_pow,one_mul,euclideanNorm,Real.sq_sqrt (euclideanSq_nonneg_fisher _)]
    _ ≤ ∫ z in Set.Ioo (a/2) (b+a/2) ×ˢ originBall d (2*R), ζ z^2*euclideanSq (G z) :=
      setIntegral_mono_set hlocal.1
        (Filter.Eventually.of_forall fun z => mul_nonneg (sq_nonneg _) (euclideanSq_nonneg_fisher _))
        hsub.eventuallyLE
    _ ≤ _ := parabolicSolution_cutoff_energy_le_scalar hK measurableSet_Ioo hU hsol
      hζ hζc hζs (fun z _ => hB z)

end EinsteinRelation.Correctors
