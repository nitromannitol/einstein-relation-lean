import EinsteinFull.Calculus.ComplexHorizontalIntegrationSupport
import EinsteinFull.Calculus.PhysicalGaugeCoercivitySupport
import EinsteinFull.Frozen.ComplexGeneratorGraph
import EinsteinRelation.Correctors.StationaryGradientDomainSupport
import EinsteinRelation.Mobility.DriftBoundPointwise

/-!
# Energy control of the actual stationary complex generator

The actual reduced law inherits origin ellipticity from the pinned blueprint.
Complex quadratic energies retain the full anisotropic matrix. Testing the
frozen unforced weak generator graph with the conjugate H1 function gives
coercivity and dissipativity, without assuming a semigroup or a core.
-/

open MeasureTheory
open scoped BigOperators ENNReal

namespace EinsteinFull

open EinsteinRelation

/-- Actual reduced coefficient entries at the origin are essentially bounded. -/
theorem memLp_reduced_coefficient_complex {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (j k : Fin d) :
    MemLp (fun ω : FieldPair d => (ω.1 0 j k : ℂ)) ∞ (reducedLaw Q) := by
  have hK : 0 ≤ Real.exp (2 * Λ₀) * Λ₀ :=
    mul_nonneg (Real.exp_pos _).le (zero_le_one.trans Q.ellipticity_parameter)
  have he : ∀ᵐ ω ∂reducedLaw Q,
      IsElliptic (Real.exp (2 * Λ₀) * Λ₀) (fun _ => ω.1 (0 : Vec d)) :=
    Correctors.ae_reducedEnvironmentLaw_origin_elliptic Q
  have hm : Continuous (fun ω : FieldPair d => (ω.1 0 j k : ℂ)) :=
    Complex.continuous_ofReal.comp
      (((continuous_eval_const (0 : Vec d)).comp continuous_fst).matrix_elem j k)
  apply memLp_top_of_bound hm.aestronglyMeasurable (Real.exp (2 * Λ₀) * Λ₀)
  filter_upwards [he] with ω hω
  rw [Complex.norm_real, Real.norm_eq_abs]
  apply abs_entry_le_of_quadratic_bounds hK (ω.1 0) (hω 0).1
  · intro ξ
    exact (mul_nonneg (inv_nonneg.mpr hK) (euclideanSq_nonneg_coords ξ)).trans
      ((hω 0).2 ξ).1
  · exact fun ξ => ((hω 0).2 ξ).2

/-- The actual reduced anisotropic bilinear energy of any two L2 gradients is integrable. -/
theorem integrable_reduced_complex_energy {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (G H : Fin d → Lp ℂ 2 (reducedLaw Q)) :
    Integrable (fun ω => ∑ j, ∑ k,
      star (G j ω) * (ω.1 0 j k : ℂ) * H k ω) (reducedLaw Q) := by
  apply integrable_finset_sum
  intro j _
  apply integrable_finset_sum
  intro k _
  have hp := ((Lp.memLp (G j)).star.integrable_mul (Lp.memLp (H k))).mul_of_top_right
    (memLp_reduced_coefficient_complex Q j k)
  convert hp using 1
  ext ω
  simp only [Pi.mul_apply, Pi.star_apply]
  ring

private theorem complexL2_norm_sq {d : ℕ} (Q : Measure (FieldPair d)) (u : Lp ℂ 2 Q) :
    ‖u‖ ^ 2 = ∫ ω, ‖u ω‖ ^ 2 ∂Q := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp only [real_inner_self_eq_norm_sq]

/-- Ellipticity controls the Euclidean sum of squared actual gradient L2 norms. -/
theorem reduced_complex_energy_lowerBound {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (G : Fin d → Lp ℂ 2 (reducedLaw Q)) :
    (Real.exp (2 * Λ₀) * Λ₀)⁻¹ * (∑ j, ‖G j‖ ^ 2) ≤
      (∫ ω, ∑ j, ∑ k, star (G j ω) * (ω.1 0 j k : ℂ) * G k ω ∂reducedLaw Q).re := by
  have hN : Integrable (fun ω => ∑ j, ‖G j ω‖ ^ 2) (reducedLaw Q) :=
    integrable_finset_sum Finset.univ fun j _ => (Lp.memLp (G j)).norm.integrable_sq
  have hE := integrable_reduced_complex_energy Q G G
  have he : ∀ᵐ ω ∂reducedLaw Q,
      IsElliptic (Real.exp (2 * Λ₀) * Λ₀) (fun _ => ω.1 (0 : Vec d)) :=
    Correctors.ae_reducedEnvironmentLaw_origin_elliptic Q
  have hb : (Real.exp (2 * Λ₀) * Λ₀)⁻¹ *
      (∫ ω, ∑ j, ‖G j ω‖ ^ 2 ∂reducedLaw Q) ≤
      ∫ ω, (∑ j, ∑ k, star (G j ω) * (ω.1 0 j k : ℂ) * G k ω).re ∂reducedLaw Q := by
    rw [← integral_const_mul]
    apply integral_mono_ae (hN.const_mul _) hE.re
    filter_upwards [he] with ω hω
    exact complex_quadratic_lowerBound (ω.1 0) (Real.exp (2 * Λ₀) * Λ₀)⁻¹
      (fun ξ => ((hω 0).2 ξ).1) (fun j => G j ω)
  have hEr : (∫ ω, (∑ j, ∑ k, star (G j ω) * (ω.1 0 j k : ℂ) *
      G k ω).re ∂reducedLaw Q) =
      (∫ ω, ∑ j, ∑ k, star (G j ω) * (ω.1 0 j k : ℂ) * G k ω ∂reducedLaw Q).re :=
    integral_re hE
  rw [hEr] at hb
  rw [integral_finset_sum _ (fun j _ => (Lp.memLp (G j)).norm.integrable_sq)] at hb
  simpa only [← complexL2_norm_sq] using hb

/-- The actual unforced generator satisfies the full stationary H1 coercivity bound. -/
theorem IsComplexGeneratorPair.unforced_coercive {d : ℕ} {Λ₀ r₀ : ℝ}
    {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d}
    {f g : Lp ℂ 2 (reducedLaw Q)} (hfg : IsComplexGeneratorPair Q i 0 f g) :
    ∃ G : Fin d → Lp ℂ 2 (reducedLaw Q),
      HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) f G ∧
      ((Real.exp (2 * Λ₀) * Λ₀)⁻¹ / 2) * (∑ j, ‖G j‖ ^ 2) ≤ -(inner ℂ f g).re := by
  obtain ⟨G, hG, hw⟩ := hfg
  refine ⟨G, hG, ?_⟩
  have hv : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
      (star f) (fun j => star (G j)) := fun j => (hG j).star
  have ht := hw (star f) (fun j => star (G j)) hv
  have hm : (∫ ω, g ω * (star f : Lp ℂ 2 (reducedLaw Q)) ω ∂reducedLaw Q) =
      inner ℂ f g := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_star f] with ω hω
    change (star f : Lp ℂ 2 (reducedLaw Q)) ω = star (f ω) at hω
    simp only [hω, RCLike.inner_apply, Complex.star_def]
  have hE : (∫ ω, ∑ j, ∑ k, (ω.1 0 j k : ℂ) * G k ω *
      (star (G j) : Lp ℂ 2 (reducedLaw Q)) ω ∂reducedLaw Q) =
      ∫ ω, ∑ j, ∑ k, star (G j ω) * (ω.1 0 j k : ℂ) * G k ω ∂reducedLaw Q := by
    apply integral_congr_ae
    have ha : ∀ᵐ ω ∂reducedLaw Q, ∀ j, (star (G j) : Lp ℂ 2 (reducedLaw Q)) ω =
        star (G j ω) := ae_all_iff.mpr fun j => Lp.coeFn_star (G j)
    filter_upwards [ha] with ω hω
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    rw [hω j]
    ring
  simp only [hm, hE, zero_mul, add_zero] at ht
  let E : ℂ := ∫ ω, ∑ j, ∑ k, star (G j ω) * (ω.1 0 j k : ℂ) * G k ω ∂reducedLaw Q
  have hr : (inner ℂ f g).re = -(1 / 2 : ℝ) * E.re := by
    change inner ℂ f g = -(1 / 2 : ℂ) * E at ht
    rw [ht, Complex.mul_re]
    norm_num
  have hb : (Real.exp (2 * Λ₀) * Λ₀)⁻¹ * (∑ j, ‖G j‖ ^ 2) ≤ E.re :=
    reduced_complex_energy_lowerBound Q G
  linarith only [hb, hr]

/-- Dissipativity follows on the full actual unforced generator domain. -/
theorem IsComplexGeneratorPair.unforced_re_inner_nonpos {d : ℕ} {Λ₀ r₀ : ℝ}
    {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d}
    {f g : Lp ℂ 2 (reducedLaw Q)} (hfg : IsComplexGeneratorPair Q i 0 f g) :
    (inner ℂ f g).re ≤ 0 := by
  obtain ⟨G, _, hbound⟩ := hfg.unforced_coercive
  have hK : 0 ≤ (Real.exp (2 * Λ₀) * Λ₀)⁻¹ / 2 :=
    div_nonneg (inv_nonneg.mpr (mul_nonneg (Real.exp_pos _).le
      (zero_le_one.trans Q.ellipticity_parameter))) (by norm_num)
  have hG : 0 ≤ ∑ j, ‖G j‖ ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
  linarith only [hbound, mul_nonneg hK hG]

/-- A function in the actual unforced generator kernel has zero horizontal gradient. -/
theorem IsComplexGeneratorPair.unforced_kernel_gradient_zero {d : ℕ} {Λ₀ r₀ : ℝ}
    {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d}
    {f : Lp ℂ 2 (reducedLaw Q)} (hf : IsComplexGeneratorPair Q i 0 f 0) :
    HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) f (fun _ => 0) := by
  obtain ⟨G, hG, hb⟩ := hf.unforced_coercive
  have hK : 0 < (Real.exp (2 * Λ₀) * Λ₀)⁻¹ / 2 :=
    div_pos (inv_pos.mpr (mul_pos (Real.exp_pos _)
      (lt_of_lt_of_le zero_lt_one Q.ellipticity_parameter))) (by norm_num)
  have hs : (∑ j, ‖G j‖ ^ 2) ≤ 0 := by
    apply nonpos_of_mul_nonpos_right (a := (Real.exp (2 * Λ₀) * Λ₀)⁻¹ / 2) _ hK
    simpa only [inner_zero_right, Complex.zero_re, neg_zero] using hb
  have hz (j : Fin d) : G j = 0 := by
    have hj : ‖G j‖ ^ 2 ≤ 0 :=
      (Finset.single_le_sum (fun k _ => sq_nonneg ‖G k‖) (Finset.mem_univ j)).trans hs
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp (le_antisymm hj (sq_nonneg _)))
  have he : G = fun _ => 0 := funext hz
  simpa only [he] using hG

/-- The actual unforced graph has the real-shift bound used for positive resolvents. -/
theorem IsComplexGeneratorPair.unforced_resolvent_bound {d : ℕ} {Λ₀ r₀ : ℝ}
    {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d}
    {f g : Lp ℂ 2 (reducedLaw Q)} (hfg : IsComplexGeneratorPair Q i 0 f g)
    (s : ℝ) :
    s * ‖f‖ ≤ ‖(s : ℂ) • f - g‖ := by
  have hd := hfg.unforced_re_inner_nonpos
  have hi : s * ‖f‖ ^ 2 ≤ (inner ℂ f ((s : ℂ) • f - g)).re := by
    rw [inner_sub_right, inner_smul_right]
    simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero]
    have hself : (inner ℂ f f).re = ‖f‖ ^ 2 := (norm_sq_eq_re_inner (𝕜 := ℂ) f).symm
    rw [hself]
    linarith only [hd]
  have hc : (inner ℂ f ((s : ℂ) • f - g)).re ≤ ‖f‖ * ‖(s : ℂ) • f - g‖ :=
    (Complex.re_le_norm _).trans (norm_inner_le_norm _ _)
  by_cases hf : f = 0
  · simp only [hf, norm_zero, mul_zero, smul_zero, zero_sub, norm_neg]
    exact norm_nonneg _
  · have hn : 0 < ‖f‖ := norm_pos_iff.mpr hf
    have hb : ‖f‖ * (s * ‖f‖) ≤ ‖f‖ * ‖(s : ℂ) • f - g‖ := by
      nlinarith only [hi, hc]
    exact (mul_le_mul_iff_right₀ hn).mp hb

end EinsteinFull
