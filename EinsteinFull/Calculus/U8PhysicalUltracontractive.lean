import EinsteinFull.Calculus.U8PhysicalNashDuality
import EinsteinFull.Calculus.U8FourierFirstMoment

open MeasureTheory
open EinsteinRelation EinsteinRelation.SpatialDirichlet EinsteinRelation.External.GantertSection7Support
open scoped ENNReal NNReal

noncomputable section
namespace EinsteinFull

/-- Lebesgue L¹ control transfers to the unforced physical measure. -/
theorem u8_unforced_lebesgue_integral_abs_comparison {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (Λ : ℝ) (hω : IsRegular Λ ω)
    (f : Vec d → ℝ) (hf : Integrable f volume) :
    Integrable f (physicalReversibleMeasure ω hd 0) ∧
      (∫ x, |f x| ∂physicalReversibleMeasure ω hd 0) ≤ Real.exp (2 * Λ) *
        (∫ x, |f x|) := by
  have hp : Integrable f (physicalReversibleMeasure ω hd 0) := memLp_one_iff_integrable.mp <|
    (memLp_one_iff_integrable.mpr hf).of_measure_le_smul
      (c := ENNReal.ofReal (Real.exp (2 * Λ))) ENNReal.ofReal_ne_top
      (u4_unforced_physical_measure_comparable hd ω Λ hω).1
  refine ⟨hp, ?_⟩
  apply integral_le_const_mul_of_measure_le (physicalReversibleMeasure ω hd 0) volume
    (Real.exp (2 * Λ)) (Real.exp_pos _).le
    (u4_unforced_physical_measure_comparable hd ω Λ hω).1
    (fun x => |f x|) (Filter.Eventually.of_forall fun x => abs_nonneg _)
  simpa only [Real.norm_eq_abs] using hf.norm


/-- The physical evolution factors through two equal half-time steps. -/
theorem u8_physical_half_time {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (t : ℝ≥0)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd 0)) :
    Blueprint.gmpPhysicalSemigroup hd ω 0 Λ hΛ hω t f =
      Blueprint.gmpPhysicalSemigroup hd ω 0 Λ hΛ hω (t / 2)
        (Blueprint.gmpPhysicalSemigroup hd ω 0 Λ hΛ hω (t / 2) f) := by
  simpa only [add_halves] using
    (Blueprint.gmpPhysicalSemigroup hd ω 0 Λ hΛ hω).add_apply (t / 2) (t / 2) f

/-- Positive-time L¹(volume)-to-L∞ smoothing for the unforced physical semigroup. -/
theorem u8_unforced_physical_L1_to_Linfty
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (t : ℝ≥0) (ht : 0 < t) :
    ∃ M : ℝ, 0 < M ∧
      ∀ (g : Vec d → ℝ) (hg1 : Integrable g volume)
        (hg2 : MemLp g 2 (physicalReversibleMeasure ω hd 0)),
        ∀ᵐ x ∂(physicalReversibleMeasure ω hd 0),
          |Blueprint.gmpPhysicalSemigroup hd ω 0 Λ hΛ hω t (hg2.toLp g) x| ≤
            M * ∫ y, |g y| := by
  have hh : 0 < t / 2 := by positivity
  obtain ⟨C, hC, hInf⟩ := u8_unforced_physical_L2_to_Linfty hd ω Λ hΛ hω (t / 2) hh
  obtain ⟨D, hD, h₂⟩ := u7_unforced_physical_L1_to_L2 hd ω Λ hΛ hω
  let B : ℝ := D * ((t / 2 : ℝ≥0) : ℝ) ^ (-(d : ℝ) / 4)
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨C * B, mul_pos hC hB, ?_⟩
  intro g hg1 hg2
  have hbound := h₂ (t / 2) hh g hg1 hg2
  filter_upwards [hInf (Blueprint.gmpPhysicalSemigroup hd ω 0 Λ hΛ hω (t / 2)
    (hg2.toLp g))] with x hx
  calc
    _ = |Blueprint.gmpPhysicalSemigroup hd ω 0 Λ hΛ hω (t / 2)
        (Blueprint.gmpPhysicalSemigroup hd ω 0 Λ hΛ hω (t / 2) (hg2.toLp g)) x| := by
      rw [u8_physical_half_time]
    _ ≤ C * ‖Blueprint.gmpPhysicalSemigroup hd ω 0 Λ hΛ hω (t / 2) (hg2.toLp g)‖ := hx
    _ ≤ C * (B * ∫ y, |g y|) := mul_le_mul_of_nonneg_left hbound hC.le
    _ = _ := by ring




open scoped RealInnerProductSpace

/-- An identified first-moment Fourier representative gives C¹ regularity for
an actual unforced physical semigroup action. -/
theorem u8_unforced_physical_action_C1_of_fourier_first_moment
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (t : ℝ≥0)
    (g : Lp ℝ 2 (physicalReversibleMeasure ω hd 0))
    (F : EuclideanSpace ℝ (Fin d) → ℂ)
    (hF : Integrable F) (hF1 : Integrable (fun ξ => ‖ξ‖ * ‖F ξ‖))
    (hrep : (fun x : Vec d => ∫ ξ,
      Complex.exp (2 * Real.pi * Complex.I *
        (inner ℝ ξ (WithLp.toLp 2 x) : ℂ)) * F ξ) =ᵐ[volume]
          fun x => (Blueprint.gmpPhysicalSemigroup hd ω 0 Λ hΛ hω t g x : ℂ)) :
    ∃ f : Vec d → ℂ, ContDiff ℝ 1 f ∧
      f =ᵐ[volume] (fun x => (Blueprint.gmpPhysicalSemigroup hd ω 0 Λ hΛ hω t g x : ℂ)) ∧
      ∀ x, ‖fderiv ℝ f x‖ ≤
        (2 * Real.pi * ∫ ξ, ‖ξ‖ * ‖F ξ‖) *
          ‖((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm).toContinuousLinearMap‖ := by
  let E := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm
  let v := fun x : EuclideanSpace ℝ (Fin d) => ∫ ξ,
    Complex.exp (2 * Real.pi * Complex.I * (inner ℝ ξ x : ℂ)) * F ξ
  have hv : ContDiff ℝ 1 v := u8_fourier_first_moment_C1_consumer F hF hF1
  refine ⟨v ∘ E, hv.comp E.contDiff, ?_, ?_⟩
  · simpa [v, E, PiLp.coe_symm_continuousLinearEquiv, Function.comp_def] using hrep
  · intro x
    rw [fderiv_comp x (hv.differentiable (by norm_num) _) E.differentiableAt]
    change ‖fderiv ℝ v (E x) ∘SL fderiv ℝ (fun z => E.toContinuousLinearMap z) x‖ ≤ _
    rw [E.toContinuousLinearMap.fderiv]
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul_of_nonneg_right
        (u8_fourier_first_moment_derivative_bound F hF hF1 (E x)) (norm_nonneg _))

end EinsteinFull
