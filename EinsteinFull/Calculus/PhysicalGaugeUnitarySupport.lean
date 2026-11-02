import EinsteinFull.Calculus.PhysicalMeasureSupport
import EinsteinFull.Frozen.PhysicalGaugeMultiplier
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas

/-! Exact exponential gauge transport between the public physical L2 spaces.

The inverse is constructed from the negative-force multiplier. All identities
use the frozen physical density and multiplier, with their actual null sets.
-/

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace EinsteinFull

open EinsteinRelation

@[simp]
theorem physicalGaugeMultiplier_neg_cancel {d : ℕ} (i : Fin d) (lam : ℝ)
    (f : Vec d → ℂ) :
    physicalGaugeMultiplier i lam (physicalGaugeMultiplier i (-lam) f) = f := by
  funext x
  simp only [physicalGaugeMultiplier, neg_mul, ← mul_assoc, ← Complex.ofReal_mul,
    ← Real.exp_add, add_neg_cancel, Real.exp_zero, Complex.ofReal_one, one_mul]

private theorem aestronglyMeasurable_physicalGaugeMultiplier {d : ℕ} (i : Fin d) (lam : ℝ)
    {μ : Measure (Vec d)} {f : Vec d → ℂ} (hf : AEStronglyMeasurable f μ) :
    AEStronglyMeasurable (physicalGaugeMultiplier i lam f) μ :=
  ((Complex.continuous_ofReal.comp (Real.continuous_exp.comp
    (continuous_const.mul (continuous_apply i)))).aestronglyMeasurable).mul hf

/-- The exponential gauge cancels exactly the weighted L2 density. -/
theorem eLpNorm_physicalGaugeMultiplier {d : ℕ} (i : Fin d) (lam : ℝ)
    (f : Vec d → ℂ) :
    eLpNorm (physicalGaugeMultiplier i lam f) 2 volume =
      eLpNorm f 2 (physicalForceMeasure i lam) := by
  by_cases hf : AEStronglyMeasurable f (physicalForceMeasure i lam)
  · have hg : AEStronglyMeasurable (physicalGaugeMultiplier i lam f) volume :=
      aestronglyMeasurable_physicalGaugeMultiplier i lam
        (hf.mono_ac (volume_absolutelyContinuous_physicalForceMeasure i lam))
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num : (2 : ℝ≥0∞) ≠ 0)
        (by norm_num : (2 : ℝ≥0∞) ≠ ∞) hg,
      eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num : (2 : ℝ≥0∞) ≠ 0)
        (by norm_num : (2 : ℝ≥0∞) ≠ ∞) hf]
    congr 1
    unfold physicalForceMeasure
    rw [lintegral_withDensity_eq_lintegral_mul_non_measurable volume
      (show Measurable (fun x : Vec d => ENNReal.ofReal (Real.exp (2 * lam * x i))) from
        (ENNReal.continuous_ofReal.comp (Real.continuous_exp.comp
          (continuous_const.mul (continuous_apply i)))).measurable)
      (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
    apply lintegral_congr
    intro x
    simp only [physicalGaugeMultiplier, enorm_mul, ENNReal.toReal_ofNat]
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
    congr 1
    rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _), ENNReal.rpow_two, ← ENNReal.ofReal_pow (Real.exp_pos _).le]
    congr 1
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  · have hg : ¬ AEStronglyMeasurable (physicalGaugeMultiplier i lam f) volume := by
      intro hg
      apply hf
      have h2 := aestronglyMeasurable_physicalGaugeMultiplier i (-lam)
        (hg.mono_ac (physicalForceMeasure_absolutelyContinuous i lam))
      have e := physicalGaugeMultiplier_neg_cancel i (-lam) f
      rw [neg_neg] at e
      rw [e] at h2
      exact h2
    rw [eLpNorm_of_not_aestronglyMeasurable hg, eLpNorm_of_not_aestronglyMeasurable hf]

theorem memLp_physicalGaugeMultiplier {d : ℕ} (i : Fin d) (lam : ℝ)
    {f : Vec d → ℂ} (hf : MemLp f 2 (physicalForceMeasure i lam)) :
    MemLp (physicalGaugeMultiplier i lam f) 2 volume := by
  rw [memLp_iff, eLpNorm_physicalGaugeMultiplier]
  exact hf

theorem memLp_physicalGaugeMultiplier_neg {d : ℕ} (i : Fin d) (lam : ℝ)
    {f : Vec d → ℂ} (hf : MemLp f 2 volume) :
    MemLp (physicalGaugeMultiplier i (-lam) f) 2 (physicalForceMeasure i lam) := by
  rw [memLp_iff, ← eLpNorm_physicalGaugeMultiplier, physicalGaugeMultiplier_neg_cancel]
  exact hf

private def gaugeLp {d : ℕ} (i : Fin d) (lam : ℝ)
    (f : Lp ℂ 2 (physicalForceMeasure i lam)) : Lp ℂ 2 (volume : Measure (Vec d)) :=
  (memLp_physicalGaugeMultiplier i lam (Lp.memLp f)).toLp _

private theorem gaugeLp_coe {d : ℕ} (i : Fin d) (lam : ℝ)
    (f : Lp ℂ 2 (physicalForceMeasure i lam)) :
    (gaugeLp i lam f : Vec d → ℂ) =ᵐ[volume] physicalGaugeMultiplier i lam f :=
  MemLp.coeFn_toLp _

private def gaugeLinearIsometry {d : ℕ} (i : Fin d) (lam : ℝ) :
    Lp ℂ 2 (physicalForceMeasure i lam) →ₗᵢ[ℂ] Lp ℂ 2 (volume : Measure (Vec d)) where
  toFun := gaugeLp i lam
  map_add' f g := by
    apply Lp.ext
    filter_upwards [gaugeLp_coe i lam (f + g), gaugeLp_coe i lam f,
      gaugeLp_coe i lam g, Lp.coeFn_add (gaugeLp i lam f) (gaugeLp i lam g),
      (volume_absolutelyContinuous_physicalForceMeasure i lam).ae_eq (Lp.coeFn_add f g)]
      with x hsum hf hg hout hin
    rw [hsum, hout]
    simp only [Pi.add_apply]
    rw [hf, hg]
    simp only [physicalGaugeMultiplier, hin, Pi.add_apply, mul_add]
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [gaugeLp_coe i lam (c • f), gaugeLp_coe i lam f,
      Lp.coeFn_smul c (gaugeLp i lam f),
      (volume_absolutelyContinuous_physicalForceMeasure i lam).ae_eq (Lp.coeFn_smul c f)]
      with x hcf hf hout hin
    simp only [RingHom.id_apply]
    rw [hcf, hout]
    simp only [Pi.smul_apply]
    rw [hf]
    simp only [physicalGaugeMultiplier, hin, Pi.smul_apply, smul_eq_mul]
    ring
  norm_map' f := by
    change ‖(memLp_physicalGaugeMultiplier i lam (Lp.memLp f)).toLp _‖ = _
    rw [Lp.norm_toLp, eLpNorm_physicalGaugeMultiplier, Lp.norm_def]

private theorem gaugeLinearIsometry_surjective {d : ℕ} (i : Fin d) (lam : ℝ) :
    Function.Surjective (gaugeLinearIsometry i lam) := by
  intro f
  let hf := memLp_physicalGaugeMultiplier_neg i lam (Lp.memLp f)
  refine ⟨hf.toLp _, Lp.ext ?_⟩
  have hrep := (volume_absolutelyContinuous_physicalForceMeasure i lam).ae_eq
    hf.coeFn_toLp
  filter_upwards [gaugeLp_coe i lam (hf.toLp _), hrep] with x hout hin
  change gaugeLp i lam (hf.toLp _) x = f x
  rw [hout]
  simp only [physicalGaugeMultiplier, hin, neg_mul, ← mul_assoc, ← Complex.ofReal_mul,
    ← Real.exp_add, add_neg_cancel, Real.exp_zero, Complex.ofReal_one, one_mul]

/-- Multiplication by exp(lambda x_i), as an actual complex L2 unitary. -/
def physicalGaugeUnitary {d : ℕ} (i : Fin d) (lam : ℝ) :
    Lp ℂ 2 (physicalForceMeasure i lam) ≃ₗᵢ[ℂ] Lp ℂ 2 (volume : Measure (Vec d)) :=
  LinearIsometryEquiv.ofSurjective (gaugeLinearIsometry i lam)
    (gaugeLinearIsometry_surjective i lam)

theorem physicalGaugeUnitary_coe {d : ℕ} (i : Fin d) (lam : ℝ)
    (f : Lp ℂ 2 (physicalForceMeasure i lam)) :
    (physicalGaugeUnitary i lam f : Vec d → ℂ) =ᵐ[volume]
      physicalGaugeMultiplier i lam f :=
  gaugeLp_coe i lam f

/-- The inverse unitary is multiplication by exp(-lambda x_i). -/
theorem physicalGaugeUnitary_symm_coe {d : ℕ} (i : Fin d) (lam : ℝ)
    (f : Lp ℂ 2 (volume : Measure (Vec d))) :
    ((physicalGaugeUnitary i lam).symm f : Vec d → ℂ) =ᵐ[physicalForceMeasure i lam]
      physicalGaugeMultiplier i (-lam) f := by
  apply (physicalForceMeasure_absolutelyContinuous i lam).ae_eq
  filter_upwards [physicalGaugeUnitary_coe i lam ((physicalGaugeUnitary i lam).symm f)]
    with x hx
  simp only [LinearIsometryEquiv.apply_symm_apply] at hx
  change _ = (Real.exp (-lam * x i) : ℂ) * f x
  rw [hx]
  simp only [physicalGaugeMultiplier, neg_mul, ← mul_assoc, ← Complex.ofReal_mul,
    ← Real.exp_add, neg_add_cancel, Real.exp_zero, Complex.ofReal_one, one_mul]

/-- The literal unitary and representative assertion required by the gauge proposition. -/
theorem exists_physicalGaugeUnitary {d : ℕ} (i : Fin d) (lam : ℝ) :
    ∃ U : Lp ℂ 2 (physicalForceMeasure i lam) ≃ₗᵢ[ℂ]
        Lp ℂ 2 (volume : Measure (Vec d)),
      ∀ f : Lp ℂ 2 (physicalForceMeasure i lam),
        (U f : Vec d → ℂ) =ᵐ[volume] physicalGaugeMultiplier i lam f :=
  ⟨physicalGaugeUnitary i lam, physicalGaugeUnitary_coe i lam⟩

end EinsteinFull
