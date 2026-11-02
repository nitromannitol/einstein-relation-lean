import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open MeasureTheory
open scoped NNReal

noncomputable section
namespace EinsteinFull

/-- A discounted orbit of a strongly continuous contraction family is integrable
on every right half-line. -/
theorem u2_discounted_C0_orbit_integrableOn_Ioi
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T : ℝ≥0 → E →L[ℝ] E) (hbound : ∀ t, ‖T t‖ ≤ 1)
    (hcont : ∀ f, Continuous (fun t : ℝ≥0 => T t f))
    (f : E) (a c : ℝ) (hc : 0 < c) :
    IntegrableOn (fun s : ℝ => Real.exp (-c*s) • T s.toNNReal f) (Set.Ioi a) := by
  have he : IntegrableOn (fun s : ℝ => ‖f‖ * Real.exp (-c*s)) (Set.Ioi a) :=
    (integrableOn_exp_mul_Ioi (neg_neg_of_pos hc) a).const_mul ‖f‖
  apply he.mono'
  · exact ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).smul
      ((hcont f).comp continuous_real_toNNReal)).aestronglyMeasurable
  · filter_upwards with s
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have hb : ‖T s.toNNReal f‖ ≤ ‖f‖ := by
      simpa using ((T s.toNNReal).le_opNorm f).trans
        (mul_le_mul_of_nonneg_right (hbound s.toNNReal) (norm_nonneg f))
    nlinarith [mul_le_mul_of_nonneg_left hb (Real.exp_pos (-c*s)).le]

/-- Translating the Laplace integral of a strongly continuous contraction
semigroup gives its discounted tail. -/
theorem u2_C0_discounted_resolvent_tail
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (T : ℝ≥0 → E →L[ℝ] E) (hbound : ∀ t, ‖T t‖ ≤ 1)
    (hadd : ∀ s t f, T (s + t) f = T s (T t f))
    (hcont : ∀ f, Continuous (fun t : ℝ≥0 => T t f))
    (c : ℝ) (hc : 0 < c) (f : E) (t : ℝ≥0) :
    T t (∫ s : ℝ in Set.Ioi 0, Real.exp (-c*s) • T s.toNNReal f) =
      Real.exp (c*(t:ℝ)) •
        (∫ s : ℝ in Set.Ioi (t:ℝ), Real.exp (-c*s) • T s.toNNReal f) := by
  let g : ℝ → E := fun s => Real.exp (-c*s) • T s.toNNReal f
  have hi : IntegrableOn g (Set.Ioi 0) :=
    u2_discounted_C0_orbit_integrableOn_Ioi T hbound hcont f 0 c hc
  have hp : (fun s : ℝ => (t : ℝ) + s) ⁻¹' Set.Ioi (t : ℝ) = Set.Ioi 0 := by
    ext s
    simp only [Set.mem_preimage, Set.mem_Ioi]
    constructor <;> intro h <;> linarith
  have ht := (measurePreserving_add_left volume (t : ℝ)).setIntegral_preimage_emb
    (MeasurableEquiv.addLeft (t : ℝ)).measurableEmbedding g (Set.Ioi (t : ℝ))
  rw [hp] at ht
  have hfactor : (∫ s : ℝ in Set.Ioi 0, g ((t : ℝ) + s)) =
      Real.exp (-c*(t:ℝ)) • T t (∫ s : ℝ in Set.Ioi 0, g s) := by
    rw [← (T t).integral_comp_comm hi, ← integral_smul]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    simp only [Set.mem_Ioi] at hs
    dsimp only [g]
    rw [show -c * ((t : ℝ) + s) = -c*(t:ℝ) + -c*s by ring, Real.exp_add,
      Real.toNNReal_add (NNReal.coe_nonneg t) hs.le, Real.toNNReal_coe,
      hadd, map_smul, smul_smul]
  rw [← ht, hfactor, smul_smul, ← Real.exp_add]
  simp [g, neg_mul]

/-- The discounted tail of a contraction orbit has an exponential norm bound. -/
theorem u2_C0_discounted_resolvent_tail_norm_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T : ℝ≥0 → E →L[ℝ] E) (hbound : ∀ t, ‖T t‖ ≤ 1)
    (hcont : ∀ f, Continuous (fun t : ℝ≥0 => T t f))
    (f : E) (s R : ℝ) (hs : 0 < s) :
    ‖∫ t : ℝ in Set.Ioi R, Real.exp (-s*t) • T t.toNNReal f‖ ≤
      ‖f‖ / s * Real.exp (-s*R) := by
  have hi := u2_discounted_C0_orbit_integrableOn_Ioi T hbound hcont f R s hs
  have he : IntegrableOn (fun t : ℝ => ‖f‖ * Real.exp (-s*t)) (Set.Ioi R) :=
    (integrableOn_exp_mul_Ioi (neg_neg_of_pos hs) R).const_mul ‖f‖
  calc
    ‖∫ t : ℝ in Set.Ioi R, Real.exp (-s*t) • T t.toNNReal f‖ ≤
        ∫ t : ℝ in Set.Ioi R, ‖Real.exp (-s*t) • T t.toNNReal f‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ t : ℝ in Set.Ioi R, ‖f‖ * Real.exp (-s*t) := by
      apply integral_mono_ae hi.norm he
      filter_upwards with t
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      have hb : ‖T t.toNNReal f‖ ≤ ‖f‖ := by
        simpa using ((T t.toNNReal).le_opNorm f).trans
          (mul_le_mul_of_nonneg_right (hbound t.toNNReal) (norm_nonneg f))
      nlinarith [mul_le_mul_of_nonneg_left hb (Real.exp_pos (-s*t)).le]
    _ = ‖f‖ / s * Real.exp (-s*R) := by
      rw [integral_const_mul, integral_exp_mul_Ioi (neg_neg_of_pos hs) R]
      simp [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]

end EinsteinFull
