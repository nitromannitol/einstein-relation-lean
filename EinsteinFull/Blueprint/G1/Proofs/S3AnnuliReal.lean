import EinsteinFull.Blueprint.G1.Proofs.S3RealSemigroup
import EinsteinFull.Frozen.CenteredComplexLp
import EinsteinFull.Frozen.RealLocalObservation
import EinsteinFull.Frozen.ComplexLocalObservation

/-!
# Realness and real local approximants of `L²` endpoints

Support for `p:tail#annuli`: a.e. real classes, the centering `Π`, real parts of complex local
observations, and the numerical bound turning the forced-local error into the annulus error.
-/

open MeasureTheory
open scoped NNReal

namespace EinsteinFull

open EinsteinRelation

section AeReal

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- An `L²` class that is a.e. real-valued. -/
def AeReal (X : Lp ℂ 2 μ) : Prop := ∀ᵐ x ∂μ, (X x).im = 0

theorem aeReal_of_star_eq {X : Lp ℂ 2 μ} (h : star X = X) : AeReal X := by
  filter_upwards [lpStar_apply_ae X] with x hx
  have : starRingEnd ℂ (X x) = X x := by rw [← hx, h]
  exact Complex.conj_eq_iff_im.1 this

theorem star_eq_of_aeReal {X : Lp ℂ 2 μ} (h : AeReal X) : star X = X := by
  apply Lp.ext
  filter_upwards [lpStar_apply_ae X, h] with x h1 h2
  rw [h1]
  exact Complex.conj_eq_iff_im.2 h2

theorem AeReal.add {X Y : Lp ℂ 2 μ} (hX : AeReal X) (hY : AeReal Y) : AeReal (X + Y) :=
  aeReal_of_star_eq (by rw [lpStar_add, star_eq_of_aeReal hX, star_eq_of_aeReal hY])

theorem AeReal.smul_real (r : ℝ) {X : Lp ℂ 2 μ} (hX : AeReal X) : AeReal ((r : ℂ) • X) :=
  aeReal_of_star_eq (by rw [lpStar_smul, Complex.conj_ofReal, star_eq_of_aeReal hX])

theorem AeReal.of_ae_eq_ofReal {X : Lp ℂ 2 μ} (f : α → ℝ)
    (h : (X : α → ℂ) =ᵐ[μ] fun x => (f x : ℂ)) : AeReal X := by
  filter_upwards [h] with x hx
  rw [hx]
  exact Complex.ofReal_im _

theorem integral_im_eq_zero {X : Lp ℂ 2 μ} (hX : AeReal X) : (∫ x, X x ∂μ).im = 0 := by
  rw [← Complex.conj_eq_iff_im, ← integral_conj]
  exact integral_congr_ae (hX.mono fun x hx => Complex.conj_eq_iff_im.2 hx)

end AeReal

section Centered

variable {d : ℕ} {Λ₀ r₀ : ℝ}

theorem centeredComplexLp_ae (Q : EnvironmentLaw d Λ₀ r₀) (f : Lp ℂ 2 (reducedLaw Q)) :
    (centeredComplexLp Q f : FieldPair d → ℂ) =ᵐ[reducedLaw Q]
      fun ω => f ω - ∫ ω', f ω' ∂reducedLaw Q := by
  haveI := reducedLaw_probability Q
  have h2 := Lp.coeFn_const (p := 2) (μ := reducedLaw Q) (c := ∫ ω', f ω' ∂reducedLaw Q)
  filter_upwards [Lp.coeFn_sub f (Lp.const 2 (reducedLaw Q) (∫ ω', f ω' ∂reducedLaw Q)), h2]
    with ω h1 h3
  refine h1.trans ?_
  simp only [Pi.sub_apply, h3, Function.const_apply]

theorem aeReal_centered (Q : EnvironmentLaw d Λ₀ r₀) {X : Lp ℂ 2 (reducedLaw Q)}
    (hX : AeReal X) : AeReal (centeredComplexLp Q X) := by
  filter_upwards [centeredComplexLp_ae Q X, hX] with ω h1 h2
  rw [h1]
  simp only [Complex.sub_im, h2, integral_im_eq_zero hX, sub_zero]

theorem isComplexLocal_centered (Q : EnvironmentLaw d Λ₀ r₀) {R : ℝ}
    {X : Lp ℂ 2 (reducedLaw Q)} (hX : IsComplexLocalObservation Q R X) :
    IsComplexLocalObservation Q R (centeredComplexLp Q X) := by
  obtain ⟨f, hf, hfe⟩ := hX
  refine ⟨fun ω => f ω - ∫ ω', X ω' ∂reducedLaw Q, by exact hf.sub measurable_const, ?_⟩
  filter_upwards [hfe, centeredComplexLp_ae Q X] with ω h1 h2
  rw [h2, h1]

theorem smul_centered_ae_eq (Q : EnvironmentLaw d Λ₀ r₀) (z : ℂ) (f : Lp ℂ 2 (reducedLaw Q)) :
    (z • centeredComplexLp Q f : Lp ℂ 2 (reducedLaw Q)) =ᵐ[reducedLaw Q]
      (centeredComplexLp Q (z • f) : Lp ℂ 2 (reducedLaw Q)) := by
  have hint : ∫ ω', (z • f : Lp ℂ 2 (reducedLaw Q)) ω' ∂reducedLaw Q =
      z * ∫ ω', f ω' ∂reducedLaw Q := by
    rw [integral_congr_ae (Lp.coeFn_smul z f)]
    simp only [Pi.smul_apply, smul_eq_mul]
    exact integral_const_mul z _
  filter_upwards [Lp.coeFn_smul z (centeredComplexLp Q f), centeredComplexLp_ae Q f,
    centeredComplexLp_ae Q (z • f), Lp.coeFn_smul z f] with ω h1 h2 h3 h4
  rw [h1, Pi.smul_apply, h2, h3, h4, hint, Pi.smul_apply]
  simp only [smul_eq_mul]
  ring

end Centered

section Approx

variable {d : ℕ} {Λ₀ r₀ : ℝ}

theorem exists_realPart (Q : EnvironmentLaw d Λ₀ r₀) {R : ℝ} (X : Lp ℂ 2 (reducedLaw Q))
    (hX : IsComplexLocalObservation Q R X) :
    ∃ V : Lp ℂ 2 (reducedLaw Q), IsRealLocalObservation Q R V ∧
      ∀ᵐ ω ∂reducedLaw Q, V ω = ((X ω).re : ℂ) := by
  have hV : ∀ᵐ ω ∂reducedLaw Q,
      ((2⁻¹ : ℂ) • (X + star X) : Lp ℂ 2 (reducedLaw Q)) ω = ((X ω).re : ℂ) := by
    filter_upwards [Lp.coeFn_smul (2⁻¹ : ℂ) (X + star X), Lp.coeFn_add X (star X),
      lpStar_apply_ae X] with ω h1 h2 h3
    rw [h1, Pi.smul_apply, h2, Pi.add_apply, h3, smul_eq_mul, Complex.re_eq_add_conj]
    ring
  obtain ⟨fU, hfU, hfe⟩ := hX
  refine ⟨(2⁻¹ : ℂ) • (X + star X), ⟨fun ω => (fU ω).re, by exact Complex.measurable_re.comp hfU,
    ?_⟩, hV⟩
  filter_upwards [hfe, hV] with ω h1 h2
  rw [h2, h1]

theorem norm_sub_re_le {u x : ℂ} (hu : u.im = 0) : ‖u - ((x.re : ℝ) : ℂ)‖ ≤ ‖u - x‖ := by
  have : u - ((x.re : ℝ) : ℂ) = (((u - x).re : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [hu]
  rw [this, Complex.norm_real, Real.norm_eq_abs]
  exact Complex.abs_re_le_norm _

theorem exists_real_approx (Q : EnvironmentLaw d Λ₀ r₀) {R : ℝ} (U X : Lp ℂ 2 (reducedLaw Q))
    {ε : ℝ} (hU : AeReal U) (hX : IsComplexLocalObservation Q R X)
    (h : ∀ᵐ ω ∂reducedLaw Q, ‖U ω - X ω‖ ≤ ε) :
    ∃ V : Lp ℂ 2 (reducedLaw Q), IsRealLocalObservation Q R V ∧
      ∀ᵐ ω ∂reducedLaw Q, ‖U ω - V ω‖ ≤ ε := by
  obtain ⟨V, hV, hVe⟩ := exists_realPart Q X hX
  refine ⟨V, hV, ?_⟩
  filter_upwards [hU, h, hVe] with ω h1 h2 h3
  rw [h3]
  exact (norm_sub_re_le h1).trans h2

end Approx

section Numerics

/-- The forced-local error at `t = s⁻²`, `ρ = n l / (2 s)` and `‖ζ‖ = s` is an annulus error. -/
theorem eps_bound (Cdet cF l l₀ s t z : ℝ) (NF n : ℕ) (hCdet : 0 < Cdet) (hcF : 0 < cF)
    (hl₀ : 0 < l₀) (hl : l₀ ≤ l) (hs : 0 < s) (hs1 : s ≤ 1) (ht : t = (s ^ 2)⁻¹) (hz : z = s) :
    2 * Cdet * (2 + t) ^ NF * Real.exp (Cdet * z ^ 2 * t - cF * ((n : ℝ) * l / (2 * s)) ^ 2 / t) ≤
      2 * Cdet * 3 ^ NF * Real.exp Cdet * s ^ (-((2 * NF : ℕ) : ℝ)) *
        Real.exp (-(cF * l₀ ^ 2 / 4) * (n : ℝ) ^ 2) := by
  rw [ht, hz]
  have hs2 : 0 < s ^ 2 := by positivity
  have hT1 : 1 ≤ (s ^ 2)⁻¹ := (one_le_inv₀ hs2).2 (pow_le_one₀ hs.le hs1)
  have e1 : Cdet * s ^ 2 * (s ^ 2)⁻¹ = Cdet := by field_simp
  have e2 : cF * ((n : ℝ) * l / (2 * s)) ^ 2 / (s ^ 2)⁻¹ = cF * (n : ℝ) ^ 2 * l ^ 2 / 4 := by
    field_simp
    ring
  have hll : l₀ ^ 2 ≤ l ^ 2 := pow_le_pow_left₀ hl₀.le hl 2
  have hn2 : 0 ≤ (n : ℝ) ^ 2 := sq_nonneg _
  have hexp : Cdet * s ^ 2 * (s ^ 2)⁻¹ - cF * ((n : ℝ) * l / (2 * s)) ^ 2 / (s ^ 2)⁻¹ ≤
      Cdet + -(cF * l₀ ^ 2 / 4) * (n : ℝ) ^ 2 := by
    rw [e1, e2]
    nlinarith [mul_nonneg hcF.le hn2, mul_nonneg (mul_nonneg hcF.le hn2) (sub_nonneg.2 hll)]
  have hpow : ((s ^ 2)⁻¹) ^ NF = s ^ (-((2 * NF : ℕ) : ℝ)) := by
    rw [Real.rpow_neg hs.le, Real.rpow_natCast, pow_mul, inv_pow]
  have h23 : (2 + (s ^ 2)⁻¹) ^ NF ≤ 3 ^ NF * ((s ^ 2)⁻¹) ^ NF := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (by linarith) NF
  have hE : Real.exp (Cdet * s ^ 2 * (s ^ 2)⁻¹ - cF * ((n : ℝ) * l / (2 * s)) ^ 2 / (s ^ 2)⁻¹) ≤
      Real.exp Cdet * Real.exp (-(cF * l₀ ^ 2 / 4) * (n : ℝ) ^ 2) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.2 hexp
  calc 2 * Cdet * (2 + (s ^ 2)⁻¹) ^ NF * Real.exp (Cdet * s ^ 2 * (s ^ 2)⁻¹ -
        cF * ((n : ℝ) * l / (2 * s)) ^ 2 / (s ^ 2)⁻¹)
      ≤ 2 * Cdet * (3 ^ NF * ((s ^ 2)⁻¹) ^ NF) *
          (Real.exp Cdet * Real.exp (-(cF * l₀ ^ 2 / 4) * (n : ℝ) ^ 2)) := by
        apply mul_le_mul _ hE (Real.exp_pos _).le (by positivity)
        exact mul_le_mul_of_nonneg_left h23 (by positivity)
    _ = 2 * Cdet * 3 ^ NF * Real.exp Cdet * s ^ (-((2 * NF : ℕ) : ℝ)) *
          Real.exp (-(cF * l₀ ^ 2 / 4) * (n : ℝ) ^ 2) := by
        rw [hpow]; ring

end Numerics

end EinsteinFull
