import EinsteinFull.Calculus.S5EnergySupport

/-!
# Davies growth bound for bounded smooth weights

The forward and transpose physical semigroups satisfy
`‖φ P_t f‖ ≤ exp (κ t) ‖φ f‖`, `κ = 5 Λ³ (q² + |ζ|²)`, for every smooth bounded weight with
`|∇φ| ≤ q |φ|`.
-/

open MeasureTheory
open scoped NNReal ENNReal

noncomputable section
namespace EinsteinFull
open EinsteinRelation

section S5Davies

variable {d : ℕ}

theorem s5_forward_energy {a : Vec d → Mat d} {Λ B q : ℝ} {φ : Vec d → ℝ}
    (hell : ∀ x, S5Elliptic (fun j k => a x j k) Λ)
    (hmeas : ∀ j k, Measurable fun x => a x j k)
    (hφ : S5Weight φ B q) (i : Fin d) (ζ : ℂ)
    {f g : Lp ℂ 2 (volume : Measure (Vec d))}
    (hfg : IsPhysicalComplexGeneratorPair a i ζ f g) :
    (inner ℂ (s5Mul volume hφ.measurable hφ.B_nonneg hφ.bound f)
        (s5Mul volume hφ.measurable hφ.B_nonneg hφ.bound g)).re ≤
      (5 * Λ ^ 3 * (q ^ 2 + ‖ζ‖ ^ 2)) *
        ‖s5Mul volume hφ.measurable hφ.B_nonneg hφ.bound f‖ ^ 2 := by
  obtain ⟨Gf, hGf, hweak⟩ := hfg
  obtain ⟨w, J, hw, hwr, hJr⟩ := physicalH1Graph_mul_smooth (fun x => φ x * φ x)
    hφ.sq_smooth hφ.memLp_sq hφ.memLp_sq_deriv (star f) (fun j => star (Gf j))
    (s5_isPhysicalH1Graph_star f Gf hGf)
  have hid := hweak w J hw
  have hwr' : (w : Vec d → ℂ) =ᵐ[volume] fun x =>
      ((φ x * φ x : ℝ) : ℂ) * (starRingEnd ℂ) (f x) := by
    filter_upwards [hwr, Lp.coeFn_star f] with x h1 h2
    rw [h1, h2]
    try rfl
  have hin := s5_inner_eq hφ f g w hwr'
  have hbound : ∀ j k x, ‖((a x j k : ℝ) : ℂ)‖ ≤ Λ := fun j k x => by
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact (hell x).entry_abs_le j k
  have hcm : ∀ j k, Measurable fun x => ((a x j k : ℝ) : ℂ) := fun j k =>
    Complex.measurable_ofReal.comp (hmeas j k)
  have hS1 : Integrable (fun x => ∑ j, ∑ k, ((a x j k : ℝ) : ℂ) * Gf k x * J j x) volume :=
    integrable_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ =>
      s5_integrable_coef (hcm j k) (hbound j k) (Gf k) (J j)
  have hS2 : Integrable (fun x => (∑ j, ((a x j i : ℝ) : ℂ) * Gf j x) * w x) volume := by
    have e : (fun x => (∑ j, ((a x j i : ℝ) : ℂ) * Gf j x) * w x) =
        fun x => ∑ j, ((a x j i : ℝ) : ℂ) * Gf j x * w x := by
      funext x
      rw [Finset.sum_mul]
    rw [e]
    exact integrable_finsetSum _ fun j _ =>
      s5_integrable_coef (hcm j i) (hbound j i) (Gf j) w
  have hTint : Integrable (fun x => -(1 / 2 : ℂ) *
      (∑ j, ∑ k, ((a x j k : ℝ) : ℂ) * Gf k x * J j x) +
      ζ * ((∑ j, ((a x j i : ℝ) : ℂ) * Gf j x) * w x)) volume :=
    (hS1.const_mul _).add (hS2.const_mul _)
  have hint : ∫ x, g x * w x = ∫ x, (-(1 / 2 : ℂ) *
      (∑ j, ∑ k, ((a x j k : ℝ) : ℂ) * Gf k x * J j x) +
      ζ * ((∑ j, ((a x j i : ℝ) : ℂ) * Gf j x) * w x)) := by
    rw [hid, integral_add (hS1.const_mul _) (hS2.const_mul _), integral_const_mul,
      integral_const_mul]
  rw [hin, hint]
  refine s5_re_integral_le hφ f _ (5 * Λ ^ 3 * (q ^ 2 + ‖ζ‖ ^ 2)) hTint ?_
  have hJa : ∀ᵐ x ∂(volume : Measure (Vec d)), ∀ j, (J j : Vec d → ℂ) x =
      ((φ x * φ x : ℝ) : ℂ) * (starRingEnd ℂ) (Gf j x) +
        (starRingEnd ℂ) (f x) * (coordinateDerivative j (fun y => φ y * φ y) x : ℂ) := by
    rw [ae_all_iff]
    intro j
    filter_upwards [hJr j, Lp.coeFn_star (Gf j), Lp.coeFn_star f] with x h1 h2 h3
    rw [h1, h2, h3]
    try rfl
  filter_upwards [hJa, hwr', s5_norm_sq_pt hφ f] with x hJx hwx hnorm
  rw [hnorm]
  have key := s5_pt_forward (hell x) (fun k => Gf k x) (f x)
    (fun j => coordinateDerivative j (fun y => φ y * φ y) x) (φ x * φ x) q i ζ
    (mul_self_nonneg _) (hφ.sq_grad x)
  simp only [hJx, hwx]
  exact key

theorem s5_transpose_energy {a : Vec d → Mat d} {Λ B q : ℝ} {φ : Vec d → ℝ}
    (hell : ∀ x, S5Elliptic (fun j k => a x j k) Λ)
    (hmeas : ∀ j k, Measurable fun x => a x j k)
    (hφ : S5Weight φ B q) (i : Fin d) (ζ : ℂ)
    {f g : Lp ℂ 2 (volume : Measure (Vec d))}
    (hfg : IsPhysicalComplexTransposeGeneratorPair a i ζ f g) :
    (inner ℂ (s5Mul volume hφ.measurable hφ.B_nonneg hφ.bound f)
        (s5Mul volume hφ.measurable hφ.B_nonneg hφ.bound g)).re ≤
      (5 * Λ ^ 3 * (q ^ 2 + ‖ζ‖ ^ 2)) *
        ‖s5Mul volume hφ.measurable hφ.B_nonneg hφ.bound f‖ ^ 2 := by
  obtain ⟨Gf, hGf, hweak⟩ := hfg
  obtain ⟨w, J, hw, hwr, hJr⟩ := physicalH1Graph_mul_smooth (fun x => φ x * φ x)
    hφ.sq_smooth hφ.memLp_sq hφ.memLp_sq_deriv (star f) (fun j => star (Gf j))
    (s5_isPhysicalH1Graph_star f Gf hGf)
  have hid := hweak w J hw
  have hwr' : (w : Vec d → ℂ) =ᵐ[volume] fun x =>
      ((φ x * φ x : ℝ) : ℂ) * (starRingEnd ℂ) (f x) := by
    filter_upwards [hwr, Lp.coeFn_star f] with x h1 h2
    rw [h1, h2]
    try rfl
  have hin := s5_inner_eq hφ f g w hwr'
  have hbound : ∀ j k x, ‖((a x j k : ℝ) : ℂ)‖ ≤ Λ := fun j k x => by
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact (hell x).entry_abs_le j k
  have hcm : ∀ j k, Measurable fun x => ((a x j k : ℝ) : ℂ) := fun j k =>
    Complex.measurable_ofReal.comp (hmeas j k)
  have hS1 : Integrable (fun x => ∑ j, ∑ k, ((a x k j : ℝ) : ℂ) * Gf k x * J j x) volume :=
    integrable_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ =>
      s5_integrable_coef (hcm k j) (hbound k j) (Gf k) (J j)
  have hS2 : Integrable (fun x => f x * (∑ j, ((a x j i : ℝ) : ℂ) * J j x)) volume := by
    have e : (fun x => f x * (∑ j, ((a x j i : ℝ) : ℂ) * J j x)) =
        fun x => ∑ j, ((a x j i : ℝ) : ℂ) * J j x * f x := by
      funext x
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [e]
    exact integrable_finsetSum _ fun j _ =>
      s5_integrable_coef (hcm j i) (hbound j i) (J j) f
  have hTint : Integrable (fun x => -(1 / 2 : ℂ) *
      (∑ j, ∑ k, ((a x k j : ℝ) : ℂ) * Gf k x * J j x) +
      ζ * (f x * (∑ j, ((a x j i : ℝ) : ℂ) * J j x))) volume :=
    (hS1.const_mul _).add (hS2.const_mul _)
  have hint : ∫ x, g x * w x = ∫ x, (-(1 / 2 : ℂ) *
      (∑ j, ∑ k, ((a x k j : ℝ) : ℂ) * Gf k x * J j x) +
      ζ * (f x * (∑ j, ((a x j i : ℝ) : ℂ) * J j x))) := by
    rw [hid, integral_add (hS1.const_mul _) (hS2.const_mul _), integral_const_mul,
      integral_const_mul]
  rw [hin, hint]
  refine s5_re_integral_le hφ f _ (5 * Λ ^ 3 * (q ^ 2 + ‖ζ‖ ^ 2)) hTint ?_
  have hJa : ∀ᵐ x ∂(volume : Measure (Vec d)), ∀ j, (J j : Vec d → ℂ) x =
      ((φ x * φ x : ℝ) : ℂ) * (starRingEnd ℂ) (Gf j x) +
        (starRingEnd ℂ) (f x) * (coordinateDerivative j (fun y => φ y * φ y) x : ℂ) := by
    rw [ae_all_iff]
    intro j
    filter_upwards [hJr j, Lp.coeFn_star (Gf j), Lp.coeFn_star f] with x h1 h2 h3
    rw [h1, h2, h3]
    try rfl
  filter_upwards [hJa, s5_norm_sq_pt hφ f] with x hJx hnorm
  rw [hnorm]
  have key := s5_pt_transpose (hell x) (fun k => Gf k x) (f x)
    (fun j => coordinateDerivative j (fun y => φ y * φ y) x) (φ x * φ x) q i ζ
    (mul_self_nonneg _) (hφ.sq_grad x)
  simp only [hJx]
  exact key

theorem s5_forward_growth {a : Vec d → Mat d} {Λ B q : ℝ} {φ : Vec d → ℝ}
    (hell : ∀ x, S5Elliptic (fun j k => a x j k) Λ)
    (hmeas : ∀ j k, Measurable fun x => a x j k)
    (hφ : S5Weight φ B q) (i : Fin d) (ζ : ℂ)
    {P : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ] Lp ℂ 2 (volume : Measure (Vec d))}
    (hP : IsPhysicalComplexSemigroup a i ζ P)
    (f : Lp ℂ 2 (volume : Measure (Vec d))) (t : ℝ≥0) :
    (eLpNorm (fun x => (φ x : ℂ) * (P t f) x) 2 volume).toReal ≤
      Real.exp ((5 * Λ ^ 3 * (q ^ 2 + ‖ζ‖ ^ 2)) * (t : ℝ)) *
        (eLpNorm (fun x => (φ x : ℂ) * f x) 2 volume).toReal := by
  have hS : S5Semigroup P (IsPhysicalComplexGeneratorPair a i ζ) :=
    ⟨hP.1, hP.2.1, hP.2.2.1, hP.2.2.2⟩
  have h := hS.weighted_growth (s5Mul volume hφ.measurable hφ.B_nonneg hφ.bound)
    (5 * Λ ^ 3 * (q ^ 2 + ‖ζ‖ ^ 2))
    (fun f g hfg => s5_forward_energy hell hmeas hφ i ζ hfg) f t
  rwa [s5Mul_norm, s5Mul_norm] at h

theorem s5_transpose_growth {a : Vec d → Mat d} {Λ B q : ℝ} {φ : Vec d → ℝ}
    (hell : ∀ x, S5Elliptic (fun j k => a x j k) Λ)
    (hmeas : ∀ j k, Measurable fun x => a x j k)
    (hφ : S5Weight φ B q) (i : Fin d) (ζ : ℂ)
    {P Pdag : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d))}
    (hP : IsPhysicalComplexTransposeSemigroup a i ζ P Pdag)
    (f : Lp ℂ 2 (volume : Measure (Vec d))) (t : ℝ≥0) :
    (eLpNorm (fun x => (φ x : ℂ) * (Pdag t f) x) 2 volume).toReal ≤
      Real.exp ((5 * Λ ^ 3 * (q ^ 2 + ‖ζ‖ ^ 2)) * (t : ℝ)) *
        (eLpNorm (fun x => (φ x : ℂ) * f x) 2 volume).toReal := by
  have hS : S5Semigroup Pdag (IsPhysicalComplexTransposeGeneratorPair a i ζ) :=
    ⟨hP.1, hP.2.1, hP.2.2.1, hP.2.2.2.1⟩
  have h := hS.weighted_growth (s5Mul volume hφ.measurable hφ.B_nonneg hφ.bound)
    (5 * Λ ^ 3 * (q ^ 2 + ‖ζ‖ ^ 2))
    (fun f g hfg => s5_transpose_energy hell hmeas hφ i ζ hfg) f t
  rwa [s5Mul_norm, s5Mul_norm] at h

end S5Davies

end EinsteinFull
