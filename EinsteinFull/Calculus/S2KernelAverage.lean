import EinsteinFull.Calculus.SpatialPairingSupport
import EinsteinFull.Frozen.ComplexTranslation

/-!
# Kernel averages on the stationary `L²` space

For a scalar kernel `k` on `Vec d` the kernel average `∫ k x • T_x F` is the common shape of
the frozen Gaussian, homogeneous and derivative averages. Its operator norm is bounded by the
`L¹` norm of the kernel, and the average of a convolution is the composition of averages.
-/

open MeasureTheory

namespace EinsteinFull

open EinsteinRelation

variable {d : ℕ} (Q : Measure (FieldPair d)) (hQ : IsStationary Q)

/-- The stationary average of a scalar kernel against the translation action. -/
noncomputable def kernelAvg (k : Vec d → ℂ) (F : Lp ℂ 2 Q) : Lp ℂ 2 Q :=
  ∫ x : Vec d, k x • complexTranslation Q hQ x F

/-- Scalar convolution `(k₁ ⋆ k₂)(x) = ∫ k₁(x - y) k₂(y) dy`. -/
noncomputable def kernelConv (k₁ k₂ : Vec d → ℂ) (x : Vec d) : ℂ :=
  ∫ y : Vec d, k₁ (x - y) * k₂ y

theorem norm_kernelAvg_le (k : Vec d → ℂ) (F : Lp ℂ 2 Q) :
    ‖kernelAvg Q hQ k F‖ ≤ (∫ x : Vec d, ‖k x‖) * ‖F‖ := by
  unfold kernelAvg
  calc _ ≤ ∫ x : Vec d, ‖k x • complexTranslation Q hQ x F‖ := norm_integral_le_integral_norm _
    _ = (∫ x : Vec d, ‖k x‖) * ‖F‖ := by
      simp_rw [norm_smul, norm_complexTranslation]
      rw [integral_mul_const]

theorem complexTranslation_kernelAvg [IsProbabilityMeasure Q] (k : Vec d → ℂ)
    (hk : Integrable k) (hc : Continuous k) (x : Vec d) (F : Lp ℂ 2 Q) :
    complexTranslation Q hQ x (kernelAvg Q hQ k F) =
      ∫ y : Vec d, k y • complexTranslation Q hQ (x + y) F := by
  change (complexTranslation Q hQ x).toContinuousLinearMap
    (∫ y : Vec d, k y • complexTranslation Q hQ y F) = _
  rw [← (complexTranslation Q hQ x).toContinuousLinearMap.integral_comp_comm
    (integrable_kernel_complexTranslation Q hQ k hk hc F)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun y => by
    simp only [LinearIsometry.coe_toContinuousLinearMap, map_smul, complexTranslation_add]

theorem kernelAvg_conv [IsProbabilityMeasure Q] (k₁ k₂ : Vec d → ℂ)
    (h₁ : Integrable k₁) (h₂ : Integrable k₂) (c₁ : Continuous k₁) (c₂ : Continuous k₂)
    (F : Lp ℂ 2 Q) :
    kernelAvg Q hQ k₁ (kernelAvg Q hQ k₂ F) = kernelAvg Q hQ (kernelConv k₁ k₂) F := by
  let T := fun x => complexTranslation Q hQ x F
  have hprod : Integrable (fun p : Vec d × Vec d => (k₁ p.1 * k₂ p.2) • T (p.1 + p.2))
      (volume.prod volume) := by
    have hT : Continuous (fun p : Vec d × Vec d => complexTranslation Q hQ (p.1 + p.2) F) :=
      (continuous_complexTranslation Q hQ).comp
        ((continuous_fst.add continuous_snd).prodMk continuous_const)
    refine ((h₁.norm.mul_prod h₂.norm).mul_const ‖F‖).mono'
      (((c₁.comp continuous_fst).mul (c₂.comp continuous_snd)).smul hT
        |>.aestronglyMeasurable) ?_
    exact Filter.Eventually.of_forall fun p => by
      simp only [T, norm_smul, norm_mul, norm_complexTranslation, le_refl]
  have hconv : Integrable (fun p : Vec d × Vec d => (k₁ (p.1 - p.2) * k₂ p.2) • T p.1)
      (volume.prod volume) := by
    have hT : Continuous (fun p : Vec d × Vec d => complexTranslation Q hQ p.1 F) :=
      (continuous_complexTranslation Q hQ).comp (continuous_fst.prodMk continuous_const)
    have hb := (h₂.norm.convolution_integrand (ContinuousLinearMap.mul ℝ ℝ) h₁.norm).mul_const
      ‖F‖
    apply hb.mono'
      (((c₁.comp (continuous_fst.sub continuous_snd)).fun_mul
        (c₂.comp continuous_snd) |>.fun_smul hT |>.aestronglyMeasurable))
    exact Filter.Eventually.of_forall fun p => by
      simp only [Pi.smul_apply, Pi.mul_apply, Pi.sub_apply, Function.comp_apply, norm_smul,
        norm_mul, norm_complexTranslation, ContinuousLinearMap.mul_apply']
      exact le_of_eq (congrArg (fun a : ℝ => a * ‖F‖) (mul_comm _ _))
  calc kernelAvg Q hQ k₁ (kernelAvg Q hQ k₂ F)
      = ∫ x : Vec d, ∫ y : Vec d, (k₁ x * k₂ y) • T (x + y) := by
        change (∫ x : Vec d, k₁ x • complexTranslation Q hQ x (kernelAvg Q hQ k₂ F)) = _
        apply integral_congr_ae
        refine Filter.Eventually.of_forall fun x => ?_
        dsimp only
        rw [complexTranslation_kernelAvg Q hQ k₂ h₂ c₂, ← integral_smul]
        simp only [smul_smul, T]
    _ = ∫ y : Vec d, ∫ x : Vec d, (k₁ x * k₂ y) • T (x + y) := integral_integral_swap hprod
    _ = ∫ y : Vec d, ∫ x : Vec d, (k₁ (x - y) * k₂ y) • T x := by
        apply integral_congr_ae
        refine Filter.Eventually.of_forall fun y => ?_
        simpa only [sub_add_cancel] using
          (integral_sub_right_eq_self (fun x => (k₁ x * k₂ y) • T (x + y)) y).symm
    _ = ∫ x : Vec d, ∫ y : Vec d, (k₁ (x - y) * k₂ y) • T x :=
        (integral_integral_swap hconv).symm
    _ = kernelAvg Q hQ (kernelConv k₁ k₂) F := by
        unfold kernelAvg
        apply integral_congr_ae
        refine Filter.Eventually.of_forall fun x => ?_
        dsimp only [T]
        rw [integral_smul_const]
        rfl

end EinsteinFull
