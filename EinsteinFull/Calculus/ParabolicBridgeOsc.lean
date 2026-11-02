import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Average

/-!
# Mean oscillation from sup bounds and `L²` approximation

Elementary facts on averages over a finite measure used in the bridge to the Hölder decay.
-/

open scoped ENNReal

noncomputable section
namespace EinsteinFull.ParabolicBridge

open MeasureTheory Set Filter Topology

variable {α : Type*} [MeasurableSpace α]

theorem sqrt_integral_sq_eq (ν : Measure α) {f : α → ℝ} (hf : MemLp f 2 ν) :
    Real.sqrt (∫ z, f z ^ 2 ∂ν) = (eLpNorm f 2 ν).toReal := by
  rw [hf.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num),
    ENNReal.toReal_ofReal (Real.rpow_nonneg (integral_nonneg fun z => by positivity) _)]
  rw [Real.sqrt_eq_rpow]
  simp only [ENNReal.toReal_ofNat]
  congr 1
  · refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp [Real.rpow_two, sq_abs]
  · norm_num

theorem sqrt_integral_sq_add_le (ν : Measure α) {f g : α → ℝ} (hf : MemLp f 2 ν)
    (hg : MemLp g 2 ν) :
    Real.sqrt (∫ z, (f z + g z) ^ 2 ∂ν) ≤
      Real.sqrt (∫ z, f z ^ 2 ∂ν) + Real.sqrt (∫ z, g z ^ 2 ∂ν) := by
  have hfg : MemLp (f + g) 2 ν := hf.add hg
  have h1 : Real.sqrt (∫ z, (f z + g z) ^ 2 ∂ν) = (eLpNorm (f + g) 2 ν).toReal :=
    sqrt_integral_sq_eq ν hfg
  rw [h1, sqrt_integral_sq_eq ν hf, sqrt_integral_sq_eq ν hg]
  have h2 : eLpNorm (f + g) 2 ν ≤ eLpNorm f 2 ν + eLpNorm g 2 ν := eLpNorm_add_le (by norm_num)
  have h3 : (eLpNorm (f + g) 2 ν).toReal ≤ (eLpNorm f 2 ν + eLpNorm g 2 ν).toReal :=
    ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hf.ne, hg.ne⟩) h2
  rwa [ENNReal.toReal_add hf.ne hg.ne] at h3

/-- The average minimizes the mean square deviation. -/
theorem integral_sq_sub_average_le (ν : Measure α) [IsFiniteMeasure ν] {V : α → ℝ}
    (hV : MemLp V 2 ν) (c : ℝ) :
    ∫ z, (V z - ⨍ w, V w ∂ν) ^ 2 ∂ν ≤ ∫ z, (V z - c) ^ 2 ∂ν := by
  set a : ℝ := ⨍ w, V w ∂ν with ha
  have hint : Integrable V ν := hV.integrable one_le_two
  have h0 : ∫ z, (V z - a) ∂ν = 0 := integral_sub_average ν V
  have hsq1 : Integrable (fun z => (V z - a) ^ 2) ν :=
    (hV.sub (memLp_const a)).integrable_sq
  have hlin : Integrable (fun z => 2 * (a - c) * (V z - a)) ν :=
    (hint.sub (integrable_const a)).const_mul _
  have key : (fun z => (V z - c) ^ 2) =
      fun z => ((V z - a) ^ 2 + 2 * (a - c) * (V z - a)) + (a - c) ^ 2 := by
    funext z
    ring
  have hadd : Integrable (fun z => (V z - a) ^ 2 + 2 * (a - c) * (V z - a)) ν := hsq1.add hlin
  rw [key, integral_add hadd (integrable_const _), integral_add hsq1 hlin,
    integral_const_mul, h0, integral_const]
  simp only [mul_zero, add_zero, smul_eq_mul]
  nlinarith [sq_nonneg (a - c), measureReal_nonneg (μ := ν) (s := Set.univ)]

/-- Mean oscillation of `V` from a sup-bounded `L²` approximant. -/
theorem sqrt_avg_osc_le (ν : Measure α) [IsFiniteMeasure ν] (hpos : 0 < ν.real Set.univ)
    {V u : α → ℝ} (hV : MemLp V 2 ν) (hu : MemLp u 2 ν) {m M : ℝ}
    (hmM : ∀ᵐ z ∂ν, m ≤ u z ∧ u z ≤ M) :
    Real.sqrt (⨍ z, |V z - ⨍ w, V w ∂ν| ^ 2 ∂ν) ≤
      (ν.real Set.univ) ^ (-(1 / 2 : ℝ)) * (eLpNorm (V - u) 2 ν).toReal + (M - m) / 2 := by
  set mE : ℝ := ν.real Set.univ with hmE
  set c : ℝ := (m + M) / 2 with hc
  have hsqrt : 0 < Real.sqrt mE := Real.sqrt_pos.mpr hpos
  have hν : ν ≠ 0 := by
    intro h
    simp [hmE, h] at hpos
  haveI : (ae ν).NeBot := ae_neBot.mpr hν
  obtain ⟨z0, hz0⟩ := hmM.exists
  have hMm : 0 ≤ (M - m) / 2 := by linarith [hz0.1, hz0.2]
  have s1 := integral_sq_sub_average_le ν hV c
  have hVu : MemLp (fun z => V z - u z) 2 ν := hV.sub hu
  have huc : MemLp (fun z => u z - c) 2 ν := hu.sub (memLp_const c)
  have s2 := sqrt_integral_sq_add_le ν hVu huc
  have e : ∀ z, (V z - u z) + (u z - c) = V z - c := fun z => by ring
  simp only [e] at s2
  have s3 : ∫ z, (u z - c) ^ 2 ∂ν ≤ ∫ z, ((M - m) / 2) ^ 2 ∂ν := by
    refine integral_mono_ae huc.integrable_sq (integrable_const _) ?_
    filter_upwards [hmM] with z hz
    have h1 : |u z - c| ≤ (M - m) / 2 := by
      rw [abs_le]
      constructor <;> linarith [hz.1, hz.2]
    exact sq_le_sq' (abs_le.mp h1).1 (abs_le.mp h1).2
  have s3' : Real.sqrt (∫ z, (u z - c) ^ 2 ∂ν) ≤ Real.sqrt mE * ((M - m) / 2) := by
    refine (Real.sqrt_le_sqrt s3).trans ?_
    rw [integral_const, smul_eq_mul, Real.sqrt_mul (measureReal_nonneg), Real.sqrt_sq hMm]
  have s4 : Real.sqrt (∫ z, (V z - ⨍ w, V w ∂ν) ^ 2 ∂ν) ≤
      Real.sqrt (∫ z, (V z - u z) ^ 2 ∂ν) + Real.sqrt mE * ((M - m) / 2) :=
    (Real.sqrt_le_sqrt s1).trans (s2.trans (add_le_add le_rfl s3'))
  have e2 : ⨍ z, |V z - ⨍ w, V w ∂ν| ^ 2 ∂ν = mE⁻¹ * ∫ z, (V z - ⨍ w, V w ∂ν) ^ 2 ∂ν := by
    rw [average_eq, smul_eq_mul]
    congr 1
    exact integral_congr_ae (Filter.Eventually.of_forall fun z => sq_abs _)
  have e3 : mE ^ (-(1 / 2 : ℝ)) = (Real.sqrt mE)⁻¹ := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg_one, ← Real.rpow_mul hpos.le]
    norm_num
  have e4 : Real.sqrt (∫ z, (V z - u z) ^ 2 ∂ν) = (eLpNorm (V - u) 2 ν).toReal :=
    sqrt_integral_sq_eq ν hVu
  rw [e2, Real.sqrt_mul (inv_nonneg.mpr hpos.le), Real.sqrt_inv, e3, ← e4]
  have h5 : (Real.sqrt mE)⁻¹ * Real.sqrt (∫ z, (V z - ⨍ w, V w ∂ν) ^ 2 ∂ν) ≤
      (Real.sqrt mE)⁻¹ * (Real.sqrt (∫ z, (V z - u z) ^ 2 ∂ν) +
        Real.sqrt mE * ((M - m) / 2)) :=
    mul_le_mul_of_nonneg_left s4 (inv_nonneg.mpr hsqrt.le)
  refine h5.trans (le_of_eq ?_)
  field_simp

end EinsteinFull.ParabolicBridge
