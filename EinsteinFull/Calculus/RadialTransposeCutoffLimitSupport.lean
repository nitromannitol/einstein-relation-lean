import EinsteinFull.Calculus.RadialCutoffLimitSupport
import EinsteinFull.Calculus.RadialTransposeEnergySupport
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Removing the bounded radial tests for the actual transpose evolution

The primitive has its exact power limit, including the factor `1/p`. A single
positive sequence removes the saturation and regularization together.
-/

open MeasureTheory Filter Set
open scoped Topology NNReal Interval

noncomputable section
namespace EinsteinFull
open EinsteinRelation

-- The nonnegative Fatou argument is shared mathematically with the forward
-- cutoff proof; its private implementation is repeated to keep that audited
-- public interface and its import hashes unchanged.
private theorem integrable_integral_le_of_nonneg_limit
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {F : ℕ → α → ℝ} {f : α → ℝ} {C : ℕ → ℝ} {c : ℝ}
    (hF : ∀ n, Integrable (F n) μ) (hF0 : ∀ n, ∀ᵐ ω ∂μ, 0 ≤ F n ω)
    (hf0 : ∀ᵐ ω ∂μ, 0 ≤ f ω)
    (hlim : ∀ᵐ ω ∂μ, Tendsto (fun n => F n ω) atTop (𝓝 (f ω)))
    (hbound : ∀ n, (∫ ω, F n ω ∂μ) ≤ C n) (hC : Tendsto C atTop (𝓝 c)) :
    Integrable f μ ∧ (∫ ω, f ω ∂μ) ≤ c := by
  have hc : 0 ≤ c := ge_of_tendsto hC (Eventually.of_forall fun n =>
    (integral_nonneg_of_ae (hF0 n)).trans (hbound n))
  have hmeas := aestronglyMeasurable_of_tendsto_ae _
    (fun n => (hF n).aestronglyMeasurable) hlim
  have hfatou : (∫⁻ ω, ENNReal.ofReal (f ω) ∂μ) ≤
      liminf (fun n => ∫⁻ ω, ENNReal.ofReal (F n ω) ∂μ) atTop := by
    calc
      _ = ∫⁻ ω, liminf (fun n => ENNReal.ofReal (F n ω)) atTop ∂μ := by
        apply lintegral_congr_ae
        filter_upwards [hlim] with ω hω
        exact (ENNReal.tendsto_ofReal hω).liminf_eq.symm
      _ ≤ _ := lintegral_liminf_le' fun n => (hF n).aestronglyMeasurable.aemeasurable.ennreal_ofReal
  have hupper : (∫⁻ ω, ENNReal.ofReal (f ω) ∂μ) ≤ ENNReal.ofReal c := by
    apply hfatou.trans
    calc
      _ ≤ liminf (fun n => ENNReal.ofReal (C n)) atTop := by
        refine liminf_le_liminf (Eventually.of_forall ?_)
        intro n
        rw [← ofReal_integral_eq_lintegral_ofReal (hF n) (hF0 n)]
        exact ENNReal.ofReal_le_ofReal (hbound n)
      _ = _ := (ENNReal.tendsto_ofReal hC).liminf_eq
  have hfi : Integrable f μ := by
    refine ⟨hmeas, ?_⟩
    rw [hasFiniteIntegral_iff_norm]
    have he : (fun ω => ENNReal.ofReal ‖f ω‖) =ᵐ[μ]
        (fun ω => ENNReal.ofReal (f ω)) := by
      filter_upwards [hf0] with ω hω
      rw [Real.norm_eq_abs, abs_of_nonneg hω]
    rw [lintegral_congr_ae he]
    exact hupper.trans_lt ENNReal.ofReal_lt_top
  refine ⟨hfi, ?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal hfi hf0] at hupper
  exact (ENNReal.ofReal_le_ofReal_iff hc).mp hupper

/-- The untruncated transpose p-moment estimate on all actual L2 data that also
belong to Lp, for every real p = 2(1+a) ≥ 2. In particular the output Lp
membership is proved rather than assumed. -/
theorem IsComplexTransposeSemigroup.power_moment_growth
    {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
    {P T : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (hT : IsComplexTransposeSemigroup Q P T)
    {a : ℝ} (ha : 0 ≤ a) (f : Lp ℂ 2 (reducedLaw Q))
    (hf : MemLp f (ENNReal.ofReal (2 * (1 + a))) (reducedLaw Q)) (t : ℝ≥0) :
    MemLp (T t f) (ENNReal.ofReal (2 * (1 + a))) (reducedLaw Q) ∧
      (∫ ω, ‖T t f ω‖ ^ (2 * (1 + a)) ∂reducedLaw Q) ≤
        (∫ ω, ‖f ω‖ ^ (2 * (1 + a)) ∂reducedLaw Q) *
          Real.exp (((2 * (1 + a)) * ((d : ℝ) * (Real.exp (2 * Λ₀) * Λ₀) *
            (‖ζ‖ * (Real.exp (2 * Λ₀) * Λ₀) * (1 + 2 * a)) ^ 2)) * (t : ℝ)) := by
  letI := reducedLaw_probability Q
  let r (n : ℕ) : ℝ := (n : ℝ) + 1
  let e (n : ℕ) : ℝ := (r n)⁻¹
  have hr (n : ℕ) : 0 < r n := by dsimp only [r]; positivity
  have he (n : ℕ) : 0 < e n := inv_pos.mpr (hr n)
  have he1 (n : ℕ) : e n ≤ 1 := by
    apply (inv_le_one₀ (hr n)).mpr
    dsimp only [r]
    linarith only [Nat.cast_nonneg (α := ℝ) n]
  have hrlim : Tendsto r atTop atTop :=
    tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  have helim : Tendsto e atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hrlim
  let p : ℝ := 2 * (1 + a)
  let A : ℝ := Real.exp ((p * ((d : ℝ) * (Real.exp (2 * Λ₀) * Λ₀) *
    (‖ζ‖ * (Real.exp (2 * Λ₀) * Λ₀) * (1 + 2 * a)) ^ 2)) * (t : ℝ))
  have hp : 0 < p := by dsimp only [p]; linarith
  have hlimit := MemLp.tendsto_integral_radialTruncationPrimitive ha hf he he1 hr helim hrlim
  have hbounded := integrable_integral_le_of_nonneg_limit
    (F := fun n ω => radialTruncationPrimitive (e n) (r n) a (T t f ω))
    (f := fun ω => ‖T t f ω‖ ^ p / p)
    (C := fun n => (∫ ω, radialTruncationPrimitive (e n) (r n) a (f ω)
      ∂reducedLaw Q) * A)
    (c := (∫ ω, ‖f ω‖ ^ p / p ∂reducedLaw Q) * A)
    (fun n => integrable_radialTruncationPrimitive (reducedLaw Q) (T t f) (he n) (hr n) ha)
    (fun n => Eventually.of_forall fun ω =>
      radialTruncationPrimitive_nonneg (he n) (hr n) (T t f ω))
    (Eventually.of_forall fun ω => div_nonneg (Real.rpow_nonneg (norm_nonneg _) _) hp.le)
    (Eventually.of_forall fun ω =>
      tendsto_radialTruncationPrimitive he he1 hr ha helim hrlim (T t f ω))
    (fun n => hT.radialTruncation_energy_growth_all hP f (he n) (hr n) ha t)
    (hlimit.mul_const A)
  have hout : Integrable (fun ω => ‖T t f ω‖ ^ p) (reducedLaw Q) := by
    convert hbounded.1.const_mul p using 1
    ext ω
    exact (mul_div_cancel₀ _ hp.ne').symm
  have hmem : MemLp (T t f) (ENNReal.ofReal p) (reducedLaw Q) := by
    apply (integrable_norm_rpow_iff (Lp.aestronglyMeasurable (T t f))
      (ENNReal.ofReal_pos.mpr hp).ne' ENNReal.ofReal_ne_top).mp
    simpa only [ENNReal.toReal_ofReal hp.le] using hout
  refine ⟨hmem, ?_⟩
  have hb := hbounded.2
  simp only [div_eq_mul_inv, integral_mul_const] at hb
  have hh : (∫ ω, ‖T t f ω‖ ^ p ∂reducedLaw Q) ≤
      (∫ ω, ‖f ω‖ ^ p ∂reducedLaw Q) * A := by
    have heq : ((∫ ω, ‖f ω‖ ^ p ∂reducedLaw Q) * p⁻¹ * A) * p =
        (∫ ω, ‖f ω‖ ^ p ∂reducedLaw Q) * A := by
      calc
        _ = (∫ ω, ‖f ω‖ ^ p ∂reducedLaw Q) * A * (p⁻¹ * p) := by ring
        _ = _ := by rw [inv_mul_cancel₀ hp.ne', mul_one]
    have hmul := mul_le_mul_of_nonneg_right hb hp.le
    rw [heq, mul_assoc, inv_mul_cancel₀ hp.ne', mul_one] at hmul
    exact hmul
  exact hh

/-- Taking the exact pth root gives leading constant one and a quadratic force
rate on the actual transpose family. -/
theorem IsComplexTransposeSemigroup.eLpNorm_growth
    {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
    {P T : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (hT : IsComplexTransposeSemigroup Q P T)
    {a : ℝ} (ha : 0 ≤ a) (f : Lp ℂ 2 (reducedLaw Q))
    (hf : MemLp f (ENNReal.ofReal (2 * (1 + a))) (reducedLaw Q)) (t : ℝ≥0) :
    eLpNorm (T t f) (ENNReal.ofReal (2 * (1 + a))) (reducedLaw Q) ≤
      eLpNorm f (ENNReal.ofReal (2 * (1 + a))) (reducedLaw Q) *
        ENNReal.ofReal (Real.exp (((d : ℝ) * (Real.exp (2 * Λ₀) * Λ₀) *
          (‖ζ‖ * (Real.exp (2 * Λ₀) * Λ₀) * (1 + 2 * a)) ^ 2) * (t : ℝ))) := by
  let p := 2 * (1 + a)
  let c := ((d : ℝ) * (Real.exp (2 * Λ₀) * Λ₀) *
    (‖ζ‖ * (Real.exp (2 * Λ₀) * Λ₀) * (1 + 2 * a)) ^ 2) * (t : ℝ)
  have hp : 0 < p := by dsimp only [p]; linarith
  obtain ⟨hout, hb⟩ := hT.power_moment_growth hP ha f hf t
  rw [hout.eLpNorm_eq_integral_rpow_norm (ENNReal.ofReal_pos.mpr hp).ne'
    ENNReal.ofReal_ne_top,
    hf.eLpNorm_eq_integral_rpow_norm (ENNReal.ofReal_pos.mpr hp).ne'
      ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hp.le,
    ← ENNReal.ofReal_mul (Real.rpow_nonneg (integral_nonneg fun ω =>
      Real.rpow_nonneg (norm_nonneg (f ω)) _) _)]
  apply ENNReal.ofReal_le_ofReal
  have hm := Real.rpow_le_rpow (integral_nonneg fun ω =>
    Real.rpow_nonneg (norm_nonneg (T t f ω)) p) hb (inv_nonneg.mpr hp.le)
  apply hm.trans_eq
  rw [Real.mul_rpow (integral_nonneg fun ω => Real.rpow_nonneg (norm_nonneg (f ω)) p)
    (Real.exp_pos _).le, ← Real.exp_mul]
  congr 2
  change (p * _ * (t : ℝ)) * p⁻¹ = c
  dsimp only [c]
  field_simp

/-- Every datum of the genuine finite Lp space, p ≥ 2, embeds in actual L2
and satisfies the transpose bound; no density or output-membership premise is
needed. -/
theorem IsComplexTransposeSemigroup.eLpNorm_growth_Lp
    {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
    {P T : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (hT : IsComplexTransposeSemigroup Q P T)
    {a : ℝ} (ha : 0 ≤ a)
    (f : Lp ℂ (ENNReal.ofReal (2 * (1 + a))) (reducedLaw Q)) (t : ℝ≥0) :
    letI := reducedLaw_probability Q
    let h₂ : MemLp f 2 (reducedLaw Q) := (Lp.memLp f).mono_exponent
      ((ENNReal.natCast_le_ofReal (by decide : (2 : ℕ) ≠ 0)).mpr
        (by norm_num only [Nat.cast_ofNat]; linarith))
    MemLp (T t (h₂.toLp f)) (ENNReal.ofReal (2 * (1 + a))) (reducedLaw Q) ∧
      eLpNorm (T t (h₂.toLp f)) (ENNReal.ofReal (2 * (1 + a))) (reducedLaw Q) ≤
        eLpNorm f (ENNReal.ofReal (2 * (1 + a))) (reducedLaw Q) *
          ENNReal.ofReal (Real.exp (((d : ℝ) * (Real.exp (2 * Λ₀) * Λ₀) *
            (‖ζ‖ * (Real.exp (2 * Λ₀) * Λ₀) * (1 + 2 * a)) ^ 2) * (t : ℝ))) := by
  dsimp only
  letI := reducedLaw_probability Q
  let h₂ : MemLp f 2 (reducedLaw Q) := (Lp.memLp f).mono_exponent
    ((ENNReal.natCast_le_ofReal (by decide : (2 : ℕ) ≠ 0)).mpr
        (by norm_num only [Nat.cast_ofNat]; linarith))
  have hf : MemLp (h₂.toLp f) (ENNReal.ofReal (2 * (1 + a))) (reducedLaw Q) :=
    (Lp.memLp f).ae_eq h₂.coeFn_toLp.symm
  refine ⟨(hT.power_moment_growth hP ha (h₂.toLp f) hf t).1, ?_⟩
  have h := hT.eLpNorm_growth hP ha (h₂.toLp f) hf t
  rw [eLpNorm_congr_ae h₂.coeFn_toLp] at h
  exact h

end EinsteinFull
