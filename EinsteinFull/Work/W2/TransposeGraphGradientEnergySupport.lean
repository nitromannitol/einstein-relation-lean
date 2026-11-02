import EinsteinFull.Calculus.ComplexTransposeResolventSupport

/-!
# Full transpose graph gradient energy

Conjugate testing retains the actual anisotropic principal form and places the
column drift on the test gradient. The resulting structural estimate applies
to every full graph pair and to the actual transpose resolvent on all L2 data.
-/

open MeasureTheory
open scoped BigOperators

noncomputable section
namespace EinsteinFull
open EinsteinRelation

/-- The transpose column pairing has the same structural Young bound as the
forward pairing, by conjugation of the scalar force and Hilbert pairing. -/
theorem re_complexTransposeForceDrift_pair_le {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (ζ : ℂ)
    (f : Lp ℂ 2 (reducedLaw Q))
    (G : PiLp 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q))) :
    (ζ * inner ℂ (complexForceDrift Q i G) f).re ≤
      ((Real.exp (2 * Λ₀) * Λ₀)⁻¹ / 4) * (∑ j, ‖G j‖ ^ 2) +
        complexForceShift d Λ₀ ζ * ‖f‖ ^ 2 := by
  have h := re_complexForceDrift_pair_le Q i (star ζ) f G
  have he : (star ζ * inner ℂ f (complexForceDrift Q i G)).re =
      (ζ * inner ℂ (complexForceDrift Q i G) f).re := by
    rw [← inner_conj_symm f (complexForceDrift Q i G)]
    change (star ζ * star (inner ℂ (complexForceDrift Q i G) f)).re = _
    rw [← star_mul]
    simp only [Complex.star_def, Complex.conj_re, mul_comm]
  simpa only [he, complexForceShift, norm_star] using h

/-- Full transpose graph coercivity for its unique actual H1 gradient.
The coefficient and force shift depend only on dimension and ellipticity. -/
theorem IsComplexTransposeGeneratorPair.gradient_coercive
    {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
    {f g : Lp ℂ 2 (reducedLaw Q)} (hfg : IsComplexTransposeGeneratorPair Q i ζ f g)
    {G : Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hG : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) f G) :
    ((Real.exp (2 * Λ₀) * Λ₀)⁻¹ / 4) * (∑ j, ‖G j‖ ^ 2) ≤
      -(inner ℂ f g).re + complexForceShift d Λ₀ ζ * ‖f‖ ^ 2 := by
  have ht := hfg.conjugate_test hG f G hG
  have hb := reduced_complex_energy_lowerBound Q G
  have hy := re_complexTransposeForceDrift_pair_le Q i ζ f (WithLp.toLp 2 G)
  have hr : (inner ℂ f g).re = -(1 / 2 : ℝ) *
      (∫ ω, ∑ j, ∑ k, star (G j ω) * (ω.1 0 j k : ℂ) * G k ω
        ∂reducedLaw Q).re +
      (ζ * inner ℂ (complexForceDrift Q i (WithLp.toLp 2 G)) f).re := by
    rw [ht, Complex.add_re, Complex.mul_re]
    norm_num
  linarith only [hb, hy, hr]

/-- Explicit quadratic Euclidean gradient bound on the entire transpose graph. -/
theorem IsComplexTransposeGeneratorPair.gradient_energy_le
    {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
    {f g : Lp ℂ 2 (reducedLaw Q)} (hfg : IsComplexTransposeGeneratorPair Q i ζ f g)
    {G : Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hG : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) f G) :
    ‖WithLp.toLp 2 G‖ ^ 2 ≤ 4 * (Real.exp (2 * Λ₀) * Λ₀) *
      (‖f‖ * ‖g‖ + complexForceShift d Λ₀ ζ * ‖f‖ ^ 2) := by
  have hK : 0 < Real.exp (2 * Λ₀) * Λ₀ := mul_pos (Real.exp_pos _)
    (lt_of_lt_of_le zero_lt_one Q.ellipticity_parameter)
  have hc := hfg.gradient_coercive hG
  have hi : -(inner ℂ f g).re ≤ ‖f‖ * ‖g‖ := by
    calc
      _ = (-inner ℂ f g).re := (Complex.neg_re _).symm
      _ ≤ ‖-inner ℂ f g‖ := Complex.re_le_norm _
      _ = ‖inner ℂ f g‖ := norm_neg _
      _ ≤ _ := norm_inner_le_norm _ _
  have hh := mul_le_mul_of_nonneg_left
    (hc.trans (add_le_add hi le_rfl)) (show 0 ≤ 4 * (Real.exp (2 * Λ₀) * Λ₀) by positivity)
  have he : 4 * (Real.exp (2 * Λ₀) * Λ₀) *
      (((Real.exp (2 * Λ₀) * Λ₀)⁻¹ / 4) * (∑ j, ‖G j‖ ^ 2)) =
      ∑ j, ‖G j‖ ^ 2 := by
    calc
      _ = ((Real.exp (2 * Λ₀) * Λ₀) * (Real.exp (2 * Λ₀) * Λ₀)⁻¹) *
          (∑ j, ‖G j‖ ^ 2) := by ring
      _ = _ := by rw [mul_inv_cancel₀ (ne_of_gt hK), one_mul]
  rw [he] at hh
  simpa only [PiLp.norm_sq_eq_of_L2] using hh

/-- Every full transpose pair supplies a unique gradient, with no additional
domain premise, and the structural quadratic energy estimate. -/
theorem IsComplexTransposeGeneratorPair.existsUnique_gradient_energy_le
    {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
    {f g : Lp ℂ 2 (reducedLaw Q)} (hfg : IsComplexTransposeGeneratorPair Q i ζ f g) :
    ∃! G : Fin d → Lp ℂ 2 (reducedLaw Q),
      HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) f G ∧
      ‖WithLp.toLp 2 G‖ ^ 2 ≤ 4 * (Real.exp (2 * Λ₀) * Λ₀) *
        (‖f‖ * ‖g‖ + complexForceShift d Λ₀ ζ * ‖f‖ ^ 2) := by
  have hfg_copy := hfg
  obtain ⟨G, hG, _⟩ := hfg_copy
  refine ⟨G, ⟨hG, ?_⟩, fun H hH => hH.1.unique hG⟩
  exact hfg.gradient_energy_le hG

/-- The actual positive-shift transpose resolvent has a unique Euclidean H1
gradient for arbitrary L2 data, with an explicit shifted quadratic energy bound.
No regularity or generator-domain hypothesis is imposed on the datum. -/
theorem existsUnique_gradient_complexL2Transpose_forcedComplexResolvent_energy_le
    {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (ζ : ℂ)
    (s : ℝ) (hs : complexForceShift d Λ₀ ζ < s) (rhs : Lp ℂ 2 (reducedLaw Q)) :
    ∃! G : Fin d → Lp ℂ 2 (reducedLaw Q),
      HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
        (complexL2Transpose (reducedLaw Q) (forcedComplexResolvent Q i ζ s hs) rhs) G ∧
      ‖WithLp.toLp 2 G‖ ^ 2 ≤
        (4 * (Real.exp (2 * Λ₀) * Λ₀) / (s - complexForceShift d Λ₀ ζ)) * ‖rhs‖ ^ 2 := by
  let f := complexL2Transpose (reducedLaw Q) (forcedComplexResolvent Q i ζ s hs) rhs
  have hfg := complexL2Transpose_forcedComplexResolvent_spec Q i ζ s hs rhs
  have hfg_copy := hfg
  obtain ⟨G, hG, _⟩ := hfg_copy
  refine ⟨G, ⟨hG, ?_⟩, fun H hH => hH.1.unique hG⟩
  have hc := hfg.gradient_coercive hG
  have hn : ‖f‖ ≤ (s - complexForceShift d Λ₀ ζ)⁻¹ * ‖rhs‖ :=
    norm_complexL2Transpose_forcedComplexResolvent_apply_le Q i ζ s hs rhs
  have hi : (inner ℂ f rhs).re ≤ ‖f‖ * ‖rhs‖ :=
    (Complex.re_le_norm _).trans (norm_inner_le_norm _ _)
  have he : (inner ℂ f ((s : ℂ) • f - rhs)).re =
      s * ‖f‖ ^ 2 - (inner ℂ f rhs).re := by
    rw [inner_sub_right, inner_smul_right, Complex.sub_re, Complex.mul_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    rw [show (inner ℂ f f).re = ‖f‖ ^ 2 from (norm_sq_eq_re_inner (𝕜 := ℂ) f).symm]
  change ((Real.exp (2 * Λ₀) * Λ₀)⁻¹ / 4) * (∑ j, ‖G j‖ ^ 2) ≤
    -(inner ℂ f ((s : ℂ) • f - rhs)).re + complexForceShift d Λ₀ ζ * ‖f‖ ^ 2 at hc
  rw [he] at hc
  have hdrop : 0 ≤ (s - complexForceShift d Λ₀ ζ) * ‖f‖ ^ 2 :=
    mul_nonneg (sub_pos.mpr hs).le (sq_nonneg _)
  have hb : ((Real.exp (2 * Λ₀) * Λ₀)⁻¹ / 4) * (∑ j, ‖G j‖ ^ 2) ≤
      (s - complexForceShift d Λ₀ ζ)⁻¹ * ‖rhs‖ ^ 2 := by
    have hm := mul_le_mul_of_nonneg_right hn (norm_nonneg rhs)
    nlinarith only [hc, hdrop, hi, hm]
  have hK : 0 < Real.exp (2 * Λ₀) * Λ₀ := mul_pos (Real.exp_pos _)
    (lt_of_lt_of_le zero_lt_one Q.ellipticity_parameter)
  have hm := mul_le_mul_of_nonneg_left hb
    (show 0 ≤ 4 * (Real.exp (2 * Λ₀) * Λ₀) by positivity)
  have hcancel : 4 * (Real.exp (2 * Λ₀) * Λ₀) *
      (((Real.exp (2 * Λ₀) * Λ₀)⁻¹ / 4) * (∑ j, ‖G j‖ ^ 2)) =
      ∑ j, ‖G j‖ ^ 2 := by
    calc
      _ = ((Real.exp (2 * Λ₀) * Λ₀) * (Real.exp (2 * Λ₀) * Λ₀)⁻¹) *
          (∑ j, ‖G j‖ ^ 2) := by ring
      _ = _ := by rw [mul_inv_cancel₀ (ne_of_gt hK), one_mul]
  rw [hcancel] at hm
  simpa only [PiLp.norm_sq_eq_of_L2, div_eq_mul_inv, mul_assoc] using hm

end EinsteinFull
