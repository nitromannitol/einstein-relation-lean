import EinsteinFull.Calculus.ComplexForceDriftSupport

/-!
# Shifted coercivity of the actual forced stationary generator

Subtracting the actual column drift puts every forced graph pair in the
unforced graph. Its proved coercivity and a scalar Young inequality retain
half the gradient control with an explicit structural quadratic force shift.
-/

open MeasureTheory
open scoped BigOperators

noncomputable section
namespace EinsteinFull
open EinsteinRelation

/-- An explicit structural quadratic shift for the complex force. -/
def complexForceShift (d : ℕ) (Λ₀ : ℝ) (ζ : ℂ) : ℝ :=
  (Real.exp (2 * Λ₀) * Λ₀) * (‖ζ‖ * ((d : ℝ) * (Real.exp (2 * Λ₀) * Λ₀))) ^ 2

/-- The force shift is nonnegative for an actual environment law. -/
theorem complexForceShift_nonneg {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (ζ : ℂ) : 0 ≤ complexForceShift d Λ₀ ζ :=
  mul_nonneg (mul_nonneg (Real.exp_pos _).le
    (zero_le_one.trans Q.ellipticity_parameter)) (sq_nonneg _)

private theorem force_young (K b x y : ℝ) (hK : 0 < K) :
    b * y * x ≤ (K⁻¹ / 4) * x ^ 2 + K * b ^ 2 * y ^ 2 := by
  have h : 0 ≤ K⁻¹ * (x - 2 * K * b * y) ^ 2 / 4 :=
    div_nonneg (mul_nonneg (inv_pos.mpr hK).le (sq_nonneg _)) (by norm_num)
  have he : K⁻¹ * (x - 2 * K * b * y) ^ 2 / 4 =
      (K⁻¹ / 4) * x ^ 2 + K * b ^ 2 * y ^ 2 - b * y * x := by
    field_simp
    ring
  rw [he] at h
  linarith only [h]

/-- Young control of the actual drift pairing, retaining Euclidean gradient energy. -/
theorem re_complexForceDrift_pair_le {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (ζ : ℂ)
    (f : Lp ℂ 2 (reducedLaw Q))
    (G : PiLp 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q))) :
    (ζ * inner ℂ f (complexForceDrift Q i G)).re ≤
      ((Real.exp (2 * Λ₀) * Λ₀)⁻¹ / 4) * (∑ j, ‖G j‖ ^ 2) +
        complexForceShift d Λ₀ ζ * ‖f‖ ^ 2 := by
  let K := Real.exp (2 * Λ₀) * Λ₀
  let C := (d : ℝ) * K
  have hK : 0 < K := mul_pos (Real.exp_pos _)
    (lt_of_lt_of_le zero_lt_one Q.ellipticity_parameter)
  have hd : ‖complexForceDrift Q i G‖ ≤ C * ‖G‖ :=
    norm_complexForceDrift_apply_le Q i G
  have hp : (ζ * inner ℂ f (complexForceDrift Q i G)).re ≤
      (‖ζ‖ * C) * ‖f‖ * ‖G‖ := by
    calc
      _ ≤ ‖ζ * inner ℂ f (complexForceDrift Q i G)‖ := Complex.re_le_norm _
      _ = ‖ζ‖ * ‖inner ℂ f (complexForceDrift Q i G)‖ := norm_mul _ _
      _ ≤ ‖ζ‖ * (‖f‖ * ‖complexForceDrift Q i G‖) :=
        mul_le_mul_of_nonneg_left (norm_inner_le_norm _ _) (norm_nonneg _)
      _ ≤ ‖ζ‖ * (‖f‖ * (C * ‖G‖)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hd (norm_nonneg _))
          (norm_nonneg _)
      _ = _ := by ring
  have hy := force_young K (‖ζ‖ * C) ‖G‖ ‖f‖ hK
  rw [PiLp.norm_sq_eq_of_L2] at hy
  exact hp.trans hy

/-- Every full forced graph pair retains H1 coercivity after a quadratic shift. -/
theorem IsComplexGeneratorPair.forced_coercive {d : ℕ} {Λ₀ r₀ : ℝ}
    {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
    {f g : Lp ℂ 2 (reducedLaw Q)} (hfg : IsComplexGeneratorPair Q i ζ f g) :
    ∃ G : Fin d → Lp ℂ 2 (reducedLaw Q),
      HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) f G ∧
      ((Real.exp (2 * Λ₀) * Λ₀)⁻¹ / 4) * (∑ j, ‖G j‖ ^ 2) ≤
        -(inner ℂ f g).re + complexForceShift d Λ₀ ζ * ‖f‖ ^ 2 := by
  have hfg_copy := hfg
  obtain ⟨G, hG, _⟩ := hfg_copy
  let U : PiLp 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q)) := WithLp.toLp 2 G
  let D := complexForceDrift Q i U
  have hzero := hfg.change_force 0 hG
  obtain ⟨H, hH, hb⟩ := hzero.unforced_coercive
  have he : H = G := hH.unique hG
  subst H
  refine ⟨G, hG, ?_⟩
  have hb' : ((Real.exp (2 * Λ₀) * Λ₀)⁻¹ / 2) * (∑ j, ‖G j‖ ^ 2) ≤
      -(inner ℂ f g).re + (ζ * inner ℂ f D).re := by
    simpa only [zero_sub, inner_add_right, inner_smul_right, neg_mul,
      Complex.add_re, Complex.neg_re, neg_add_rev, neg_neg, add_comm] using hb
  have hy := re_complexForceDrift_pair_le Q i ζ f U
  linarith only [hb', hy]

/-- The quadratic structural shift makes the entire forced graph dissipative. -/
theorem IsComplexGeneratorPair.forced_re_inner_le {d : ℕ} {Λ₀ r₀ : ℝ}
    {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
    {f g : Lp ℂ 2 (reducedLaw Q)} (hfg : IsComplexGeneratorPair Q i ζ f g) :
    (inner ℂ f g).re ≤ complexForceShift d Λ₀ ζ * ‖f‖ ^ 2 := by
  obtain ⟨G, _, hb⟩ := hfg.forced_coercive
  have ha : 0 ≤ (Real.exp (2 * Λ₀) * Λ₀)⁻¹ / 4 :=
    div_nonneg (inv_nonneg.mpr (mul_nonneg (Real.exp_pos _).le
      (zero_le_one.trans Q.ellipticity_parameter))) (by norm_num)
  have hG : 0 ≤ ∑ j, ‖G j‖ ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
  linarith only [hb, mul_nonneg ha hG]

/-- The full forced generator has the shifted real resolvent norm bound. -/
theorem IsComplexGeneratorPair.forced_resolvent_bound {d : ℕ} {Λ₀ r₀ : ℝ}
    {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
    {f g : Lp ℂ 2 (reducedLaw Q)} (hfg : IsComplexGeneratorPair Q i ζ f g)
    (s : ℝ) :
    (s - complexForceShift d Λ₀ ζ) * ‖f‖ ≤ ‖(s : ℂ) • f - g‖ := by
  have hd := hfg.forced_re_inner_le
  have hi : (s - complexForceShift d Λ₀ ζ) * ‖f‖ ^ 2 ≤
      (inner ℂ f ((s : ℂ) • f - g)).re := by
    rw [inner_sub_right, inner_smul_right]
    simp only [Complex.sub_re, Complex.re_ofReal_mul]
    have hself : (inner ℂ f f).re = ‖f‖ ^ 2 := (norm_sq_eq_re_inner (𝕜 := ℂ) f).symm
    rw [hself]
    nlinarith only [hd]
  have hc : (inner ℂ f ((s : ℂ) • f - g)).re ≤ ‖f‖ * ‖(s : ℂ) • f - g‖ :=
    (Complex.re_le_norm _).trans (norm_inner_le_norm _ _)
  by_cases hf : f = 0
  · simp only [hf, norm_zero, mul_zero, smul_zero, zero_sub, norm_neg]
    exact norm_nonneg _
  · have hn : 0 < ‖f‖ := norm_pos_iff.mpr hf
    have hb : ‖f‖ * ((s - complexForceShift d Λ₀ ζ) * ‖f‖) ≤
        ‖f‖ * ‖(s : ℂ) • f - g‖ := by
      nlinarith only [hi, hc]
    exact (mul_le_mul_iff_right₀ hn).mp hb

/-- Every shift above the quadratic force shift has at most one full graph solution. -/
theorem IsComplexGeneratorPair.forced_resolvent_unique {d : ℕ} {Λ₀ r₀ : ℝ}
    {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ} {s : ℝ}
    (hs : complexForceShift d Λ₀ ζ < s) {rhs f h : Lp ℂ 2 (reducedLaw Q)}
    (hf : IsComplexGeneratorPair Q i ζ f ((s : ℂ) • f - rhs))
    (hh : IsComplexGeneratorPair Q i ζ h ((s : ℂ) • h - rhs)) : f = h := by
  have hd := hf.add (hh.smul (-1))
  have he : ((s : ℂ) • f - rhs) + (-1 : ℂ) • ((s : ℂ) • h - rhs) =
      (s : ℂ) • (f - h) := by module
  rw [he] at hd
  simp only [neg_one_smul, ← sub_eq_add_neg] at hd
  have hb := hd.forced_resolvent_bound s
  rw [sub_self, norm_zero] at hb
  have hz : ‖f - h‖ = 0 := le_antisymm
    (nonpos_of_mul_nonpos_right hb (sub_pos.mpr hs)) (norm_nonneg _)
  exact sub_eq_zero.mp (norm_eq_zero.mp hz)

end EinsteinFull
