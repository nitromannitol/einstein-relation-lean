import EinsteinFull.Calculus.ComplexRadialGeneratorSupport
import EinsteinFull.Frozen.StructuralData
import EinsteinFull.Frozen.SmoothEnvironment
import EinsteinFull.Calculus.C4CoefficientRowWeakProduct
import EinsteinFull.Calculus.S4ReducedCoefficientSupport
import EinsteinFull.Calculus.C5ResponseThresholdHorizontalGradient

open MeasureTheory
open scoped NNReal ENNReal Topology BigOperators
namespace EinsteinFull.Blueprint
open EinsteinRelation
/- SUPERVISOR EXACT CONTRACT (not a declaration/proof):
theorem response_real_force_threshold_energy
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
        (hQ : HasSmoothBounds D Q) (lam : ℝ)
        (f g : Lp ℂ 2 (reducedLaw Q)),
        IsComplexGeneratorPair Q (⟨0, by omega⟩ : Fin d) (lam : ℂ) f g →
        ∀ K : ℝ, 0 ≤ K →
          (∫ ω, (star (((max (‖f ω‖ - K) 0 / ‖f ω‖ : ℝ) : ℂ) * f ω) *
            g ω).re ∂reducedLaw Q) ≤
            C * |lam| * (∫ ω, (max (‖f ω‖ - K) 0) ^ 2 ∂reducedLaw Q)
-/

/-- The literal threshold test has exactly the excess norm, including at zero. -/
theorem response_threshold_test_norm (z : ℂ) (K : ℝ) (hK : 0 ≤ K) :
    ‖((max (‖z‖ - K) 0 / ‖z‖ : ℝ) : ℂ) * z‖ = max (‖z‖ - K) 0 := by
  by_cases hz : z = 0
  · subst z
    simp only [norm_zero, zero_sub, max_eq_right (neg_nonpos.mpr hK),
      div_zero, Complex.ofReal_zero, mul_zero]
  · have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg (le_max_right _ _) (norm_nonneg _)),
      div_mul_cancel₀ _ hn]

/-- The radial differential preserves the real threshold flux. This identity
allows stationary integration by parts on two H1 threshold factors. -/
theorem response_threshold_flux_identity (z w : ℂ) (K : ℝ) (hK : 0 ≤ K) :
    let v := ((max (‖z‖ - K) 0 / ‖z‖ : ℝ) : ℂ) * z
    let H := if K < ‖z‖ then
      (((1 - K / ‖z‖ : ℝ) : ℂ) * w +
        ((K / ‖z‖ ^ 3 * (star z * w).re : ℝ) : ℂ) * z) else 0
    (star v * H).re = (star v * w).re := by
  dsimp only
  by_cases hz : K < ‖z‖
  · rw [ite_eq_left hz, max_eq_left (sub_nonneg.mpr hz.le)]
    have hn : ‖z‖ ≠ 0 := ne_of_gt (lt_of_le_of_lt hK hz)
    have hsq : z.re ^ 2 + z.im ^ 2 = ‖z‖ ^ 2 := by
      simpa only [Complex.normSq_apply, ← sq] using Complex.normSq_eq_norm_sq z
    simp only [Complex.star_def, map_mul, Complex.conj_ofReal,
      Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im]
    field_simp
    linear_combination K * (‖z‖ - K) * (z.re * w.re + z.im * w.im) * hsq
  · rw [ite_eq_right hz, max_eq_right (sub_nonpos.mpr (le_of_not_gt hz))]
    simp only [zero_div, Complex.ofReal_zero, zero_mul, star_zero, mul_zero]

/-- Anisotropic diffusion tested against the literal threshold differential
has nonnegative real energy; no isotropic replacement is used. -/
theorem response_threshold_diffusion_nonneg {d : ℕ} (A : Mat d)
    (hA : ∀ ξ : Vec d, 0 ≤ dot ξ (A.mulVec ξ))
    (z : ℂ) (G : Fin d → ℂ) (K : ℝ) (hK : 0 ≤ K) :
    0 ≤ (∑ j : Fin d, ∑ k : Fin d,
      star (if K < ‖z‖ then
        (((1 - K / ‖z‖ : ℝ) : ℂ) * G j +
          ((K / ‖z‖ ^ 3 * (star z * G j).re : ℝ) : ℂ) * z) else 0) *
        (A j k : ℂ) * G k).re := by
  by_cases hz : K < ‖z‖
  · have hn : 0 < ‖z‖ := lt_of_le_of_lt hK hz
    have hb : 0 ≤ 1 - K / ‖z‖ := sub_nonneg.mpr
      ((div_le_one hn).mpr hz.le)
    have hc : 0 ≤ K / (2 * ‖z‖ ^ 3) := div_nonneg hK (by positivity)
    have he (j : Fin d) :
        complexRadialDifferential (1 - K / ‖z‖) (K / (2 * ‖z‖ ^ 3)) z (G j) =
          (((1 - K / ‖z‖ : ℝ) : ℂ) * G j +
            ((K / ‖z‖ ^ 3 * (star z * G j).re : ℝ) : ℂ) * z) := by
      rw [complexRadialDifferential_apply]
      have ht : 2 * (K / (2 * ‖z‖ ^ 3)) = K / ‖z‖ ^ 3 := by ring
      rw [ht]
      simp only [real_inner_eq_re_inner ℂ, RCLike.inner_apply,
        Complex.real_smul, Complex.star_def, mul_comm (G j), RCLike.re_to_complex]
    have hp := complexRadialDifferential_energy_lowerBound A 0
      (1 - K / ‖z‖) (K / (2 * ‖z‖ ^ 3)) (le_refl 0) hb hc
      (fun ξ => by simpa only [zero_mul] using hA ξ) z G
    simpa only [mul_zero, zero_mul, he, ite_eq_left hz] using hp
  · simp only [ite_eq_right hz, star_zero, zero_mul, Finset.sum_const_zero, Complex.zero_re,
      le_refl]

/-- The real drift pairing of one actual H1 function is its coefficient
column-divergence pairing. The two H1 factors avoid any L2 assumption on
its squared modulus. -/
theorem response_real_drift_energy_identity
    {d : ℕ} (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q)
    (β : Fin d → Lp ℂ 2 (reducedLaw Q)) (hβ : IsReducedDriftObservation Q hQ β)
    (v : Lp ℂ 2 (reducedLaw Q)) (H : Fin d → Lp ℂ 2 (reducedLaw Q))
    (hv : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) v H)
    (i : Fin d) :
    (inner ℂ v (complexForceDrift Q i (WithLp.toLp 2 H))).re =
      -(∫ ω, β i ω * v ω * star (v ω) ∂reducedLaw Q).re := by
  have hw := coefficient_row_weak_product D Q hQ β hβ v (star v) H
    (fun j => star (H j)) hv (fun j => (hv j).star) i
  let I : ℂ := ∫ ω, (∑ j, (ω.1 0 i j : ℂ) * H j ω) * star (v ω) ∂reducedLaw Q
  have hL : (∫ ω, (∑ j, (ω.1 0 i j : ℂ) * H j ω) *
      (star v : Lp ℂ 2 (reducedLaw Q)) ω ∂reducedLaw Q) = I := by
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_star v] with ω hω
    change (star v : Lp ℂ 2 (reducedLaw Q)) ω = star (v ω) at hω
    rw [hω]
  have hR : (∫ ω, v ω * (∑ j, (ω.1 0 i j : ℂ) *
      (star (H j) : Lp ℂ 2 (reducedLaw Q)) ω) ∂reducedLaw Q) = star I := by
    change _ = (starRingEnd ℂ) I
    rw [← integral_conj]
    apply integral_congr_ae
    filter_upwards [ae_all_iff.mpr fun j => Lp.coeFn_star (H j)] with ω hω
    change ∀ j, (star (H j) : Lp ℂ 2 (reducedLaw Q)) ω = star (H j ω) at hω
    simp only [hω, map_mul, map_sum, Complex.star_def, Complex.conj_ofReal,
      Complex.conj_conj]
    ring
  have hB : (∫ ω, β i ω * v ω * (star v : Lp ℂ 2 (reducedLaw Q)) ω
      ∂reducedLaw Q) = ∫ ω, β i ω * v ω * star (v ω) ∂reducedLaw Q := by
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_star v] with ω hω
    change (star v : Lp ℂ 2 (reducedLaw Q)) ω = star (v ω) at hω
    rw [hω]
  rw [hL, hR, hB] at hw
  have he := congrArg Complex.re hw
  norm_num [Complex.sub_re, Complex.neg_re, Complex.mul_re,
    Complex.star_def, Complex.conj_re] at he
  have hI : I = inner ℂ v (complexForceDrift Q i (WithLp.toLp 2 H)) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [complexForceDrift_coe Q i (WithLp.toLp 2 H),
      Correctors.ae_reducedEnvironmentLaw_origin_elliptic Q] with ω hω hsym
    change (complexForceDrift Q i (WithLp.toLp 2 H)) ω =
      ∑ j, (ω.1 0 j i : ℂ) * H j ω at hω
    have hs (j : Fin d) : ω.1 0 i j = ω.1 0 j i :=
      congrArg (fun A : Mat d => A j i) (hsym 0).1
    simp only [RCLike.inner_apply, hω, hs, Complex.star_def, mul_comm]
  rw [← hI]
  simp only [Complex.star_def]
  linarith only [he]

/-- The actual smooth reduced drift has L2 representatives with one bound
chosen before the environment law. -/
theorem response_reduced_drift_exists_uniform_bound (d : ℕ) (D : StructuralData d) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q),
        ∃ β : Fin d → Lp ℂ 2 (reducedLaw Q),
          IsReducedDriftObservation Q hQ β ∧
            ∀ i, ∀ᵐ ω ∂reducedLaw Q, ‖β i ω‖ ≤ C := by
  let L : ℝ≥0 := Real.toNNReal
    (Real.exp (2 * D.ellipticity) * (2 * D.ellipticity ^ 2 + D.ellipticity) *
      Real.sqrt d)
  let B : ℝ := (1 / 2 : ℝ) * (d * (L : ℝ))
  have hB : 0 ≤ B := by positivity
  refine ⟨1 + B, by linarith, ?_⟩
  intro Q hQ
  letI : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  let b (i : Fin d) (ω : FieldPair d) : ℂ :=
    (((1 / 2 : ℝ) * ∑ j, coordinateDerivative j (fun x => ω.1 x j i) 0 : ℝ) : ℂ)
  have hb (i : Fin d) : MemLp (b i) ∞ (reducedLaw Q) := by
    have hj (j : Fin d) : MemLp (fun ω : FieldPair d =>
        (coordinateDerivative j (fun x => ω.1 x j i) 0 : ℂ)) ∞ (reducedLaw Q) := by
      have hm := Complex.ofRealCLM.comp_memLp'
        (timeFlux_coefficient_jets_memLp_top hQ j i [j])
      have ho (ω : FieldPair d) : orbit (fun η : FieldPair d => η.1 0 j i) ω =
          fun x => ω.1 x j i := by
        funext x
        simp only [orbit, translate_matrix, add_zero]
      simp only [iteratedHorizontalDerivative] at hm
      change MemLp (fun ω => (horizontalDerivative j (fun η : FieldPair d => η.1 0 j i) ω : ℂ))
        ∞ (reducedLaw Q) at hm
      simpa only [horizontalDerivative, ho] using hm
    convert (memLp_finsetSum Finset.univ (fun j _ => hj j)).const_mul (1 / 2 : ℂ) using 1 <;>
      simp only [b, Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_one,
        Complex.ofReal_ofNat, Complex.ofReal_sum]
  let β (i : Fin d) : Lp ℂ 2 (reducedLaw Q) := ((hb i).mono_exponent le_top).toLp (b i)
  have hβ : IsReducedDriftObservation Q hQ β := fun i =>
    ((hb i).mono_exponent le_top).coeFn_toLp
  refine ⟨β, hβ, ?_⟩
  intro i
  apply (ae_map_iff Probability.measurable_reduce.aemeasurable
    (measurableSet_le (Lp.stronglyMeasurable (β i)).measurable.norm measurable_const)).mpr
  have he := ae_of_ae_map Probability.measurable_reduce.aemeasurable (hβ i)
  filter_upwards [Q.regular, he] with ω hω heq
  rw [heq, Complex.norm_real, Real.norm_eq_abs]
  have hΛ : 0 < D.ellipticity := lt_of_lt_of_le zero_lt_one D.one_le_ellipticity
  have hbound : |matrixDivDrift (reducedCoefficient ω) 0 i| ≤ B :=
    abs_matrixDivDrift_le (reducedCoefficient ω) (reducedCoefficient_lipschitz hΛ hω) 0 i
  exact hbound.trans (by linarith)

/-- The real H1 column-drift pairing has a uniform structural upper bound
by its exact squared L2 mass, without an L4 assumption. -/
theorem response_real_drift_energy_abs_bound (d : ℕ) (D : StructuralData d) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q)
        (v : Lp ℂ 2 (reducedLaw Q)) (H : Fin d → Lp ℂ 2 (reducedLaw Q)),
        HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) v H →
        ∀ i : Fin d,
          |(inner ℂ v (complexForceDrift Q i (WithLp.toLp 2 H))).re| ≤
            C * (∫ ω, ‖v ω‖ ^ 2 ∂reducedLaw Q) := by
  obtain ⟨C, hC, hβexists⟩ := response_reduced_drift_exists_uniform_bound d D
  refine ⟨C, hC, ?_⟩
  intro Q hQ v H hv i
  obtain ⟨β, hβ, hβbound⟩ := hβexists Q hQ
  have hm : MemLp (fun ω => β i ω) ∞ (reducedLaw Q) :=
    memLp_top_of_bound (Lp.aestronglyMeasurable (β i)) C (hβbound i)
  have hprod : MemLp (fun ω => β i ω * v ω) 2 (reducedLaw Q) :=
    hm.fun_mul (Lp.memLp v)
  have hi : Integrable (fun ω => β i ω * v ω * star (v ω)) (reducedLaw Q) :=
    hprod.integrable_mul (Lp.memLp v).star
  have hv2 := (Lp.memLp v).norm.integrable_sq
  rw [response_real_drift_energy_identity D Q hQ β hβ v H hv i, abs_neg]
  calc
    |(∫ ω, β i ω * v ω * star (v ω) ∂reducedLaw Q).re| ≤
        ‖∫ ω, β i ω * v ω * star (v ω) ∂reducedLaw Q‖ := Complex.abs_re_le_norm _
    _ ≤ ∫ ω, ‖β i ω * v ω * star (v ω)‖ ∂reducedLaw Q :=
      norm_integral_le_integral_norm _
    _ ≤ C * (∫ ω, ‖v ω‖ ^ 2 ∂reducedLaw Q) := by
      rw [← integral_const_mul]
      apply integral_mono_ae hi.norm (hv2.const_mul C)
      filter_upwards [hβbound i] with ω hω
      calc
        ‖β i ω * v ω * star (v ω)‖ = ‖β i ω‖ * ‖v ω‖ ^ 2 := by
          rw [norm_mul, norm_mul, norm_star]
          ring
        _ ≤ C * ‖v ω‖ ^ 2 := mul_le_mul_of_nonneg_right hω (sq_nonneg _)

/-- Integrated anisotropic positivity for the exact threshold differential. -/
theorem response_threshold_diffusion_integral_nonneg {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (f : Lp ℂ 2 (reducedLaw Q))
    (G H : Fin d → Lp ℂ 2 (reducedLaw Q)) (K : ℝ) (hK : 0 ≤ K)
    (hH : ∀ j, H j =ᵐ[reducedLaw Q] fun ω =>
      if K < ‖f ω‖ then
        (((1 - K / ‖f ω‖ : ℝ) : ℂ) * G j ω +
          ((K / ‖f ω‖ ^ 3 * (star (f ω) * G j ω).re : ℝ) : ℂ) * f ω)
      else 0) :
    0 ≤ (∫ ω, ∑ j, ∑ k, star (H j ω) * (ω.1 0 j k : ℂ) * G k ω
      ∂reducedLaw Q).re := by
  have hr : (∫ ω, (∑ j, ∑ k, star (H j ω) * (ω.1 0 j k : ℂ) * G k ω).re
      ∂reducedLaw Q) = (∫ ω, ∑ j, ∑ k,
      star (H j ω) * (ω.1 0 j k : ℂ) * G k ω ∂reducedLaw Q).re :=
    integral_re (integrable_reduced_complex_energy Q H G)
  rw [← hr]
  apply integral_nonneg_of_ae
  filter_upwards [Correctors.ae_reducedEnvironmentLaw_origin_elliptic Q,
    ae_all_iff.mpr hH] with ω hω hrep
  simp only [hrep]
  apply response_threshold_diffusion_nonneg (ω.1 0) _ (f ω) (fun j => G j ω) K hK
  intro ξ
  exact (mul_nonneg (inv_nonneg.mpr (mul_nonneg (Real.exp_pos _).le
    (zero_le_one.trans Q.ellipticity_parameter))) (euclideanSq_nonneg_coords ξ)).trans
      ((hω 0).2 ξ).1

/-- Threshold testing preserves the real coefficient-column flux after integration.
Both integrands are L1 products of actual L2 vectors. -/
theorem response_threshold_drift_flux_identity {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d)
    (f v : Lp ℂ 2 (reducedLaw Q))
    (G H : Fin d → Lp ℂ 2 (reducedLaw Q)) (K : ℝ) (hK : 0 ≤ K)
    (hv : v =ᵐ[reducedLaw Q] fun ω =>
      ((max (‖f ω‖ - K) 0 / ‖f ω‖ : ℝ) : ℂ) * f ω)
    (hH : ∀ j, H j =ᵐ[reducedLaw Q] fun ω =>
      if K < ‖f ω‖ then
        (((1 - K / ‖f ω‖ : ℝ) : ℂ) * G j ω +
          ((K / ‖f ω‖ ^ 3 * (star (f ω) * G j ω).re : ℝ) : ℂ) * f ω)
      else 0) :
    (inner ℂ v (complexForceDrift Q i (WithLp.toLp 2 G))).re =
      (inner ℂ v (complexForceDrift Q i (WithLp.toLp 2 H))).re := by
  have hi (F : Fin d → Lp ℂ 2 (reducedLaw Q)) :
      (inner ℂ v (complexForceDrift Q i (WithLp.toLp 2 F))).re =
        ∫ ω, (star (v ω) * (complexForceDrift Q i (WithLp.toLp 2 F)) ω).re
          ∂reducedLaw Q := by
    rw [L2.inner_def]
    simp only [RCLike.inner_apply, Complex.star_def, mul_comm]
    exact (integral_re ((Lp.memLp v).star.integrable_mul
      (Lp.memLp (complexForceDrift Q i (WithLp.toLp 2 F))))).symm
  rw [hi G, hi H]
  apply integral_congr_ae
  filter_upwards [hv, ae_all_iff.mpr hH,
    complexForceDrift_coe Q i (WithLp.toLp 2 G),
    complexForceDrift_coe Q i (WithLp.toLp 2 H)] with ω hvω hHω hGω hDω
  change (complexForceDrift Q i (WithLp.toLp 2 G)) ω =
    ∑ j, (ω.1 0 j i : ℂ) * G j ω at hGω
  change (complexForceDrift Q i (WithLp.toLp 2 H)) ω =
    ∑ j, (ω.1 0 j i : ℂ) * H j ω at hDω
  rw [hGω, hDω]
  simp only [Finset.mul_sum, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro j _
  have he := response_threshold_flux_identity (f ω) (G j ω) K hK
  dsimp only at he
  rw [← hvω, ← hHω j] at he
  simpa only [← mul_assoc, mul_comm (star (v ω)), mul_assoc,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
    zero_mul, sub_zero] using congrArg (fun x : ℝ => (ω.1 0 j i) * x) he.symm

/-- Once the literal threshold and its differential belong to horizontal H1,
the actual generator graph yields the signed real-force energy inequality.
The constant is chosen before the law, force, function and threshold. -/
theorem response_real_force_threshold_energy_of_gradient (d : ℕ) (D : StructuralData d) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
        (hQ : HasSmoothBounds D Q) (i : Fin d) (lam : ℝ)
        (f g v : Lp ℂ 2 (reducedLaw Q))
        (G H : Fin d → Lp ℂ 2 (reducedLaw Q)) (K : ℝ),
        0 ≤ K → IsComplexGeneratorPair Q i (lam : ℂ) f g →
        HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) f G →
        HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) v H →
        (v =ᵐ[reducedLaw Q] fun ω =>
          ((max (‖f ω‖ - K) 0 / ‖f ω‖ : ℝ) : ℂ) * f ω) →
        (∀ j, H j =ᵐ[reducedLaw Q] fun ω =>
          if K < ‖f ω‖ then
            (((1 - K / ‖f ω‖ : ℝ) : ℂ) * G j ω +
              ((K / ‖f ω‖ ^ 3 * (star (f ω) * G j ω).re : ℝ) : ℂ) * f ω)
          else 0) →
        (∫ ω, (star (((max (‖f ω‖ - K) 0 / ‖f ω‖ : ℝ) : ℂ) * f ω) *
          g ω).re ∂reducedLaw Q) ≤
          C * |lam| * (∫ ω, (max (‖f ω‖ - K) 0) ^ 2 ∂reducedLaw Q) := by
  obtain ⟨C, hC, hbound⟩ := response_real_drift_energy_abs_bound d D
  refine ⟨C, hC, ?_⟩
  intro Q hQ i lam f g v G H K hK hfg hG hv hvrep hHrep
  have htest := hfg.conjugate_test hG v H hv
  have hdiff := response_threshold_diffusion_integral_nonneg Q f G H K hK hHrep
  have hflux := response_threshold_drift_flux_identity Q i f v G H K hK hvrep hHrep
  have he : (inner ℂ v g).re =
      -(1 / 2 : ℝ) * (∫ ω, ∑ j, ∑ k,
        star (H j ω) * (ω.1 0 j k : ℂ) * G k ω ∂reducedLaw Q).re +
        lam * (inner ℂ v (complexForceDrift Q i (WithLp.toLp 2 H))).re := by
    rw [htest]
    simp only [Complex.add_re, Complex.mul_re, Complex.neg_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    norm_num [hflux]
  have hmass : (∫ ω, ‖v ω‖ ^ 2 ∂reducedLaw Q) =
      ∫ ω, (max (‖f ω‖ - K) 0) ^ 2 ∂reducedLaw Q := by
    apply integral_congr_ae
    filter_upwards [hvrep] with ω hω
    rw [hω, response_threshold_test_norm (f ω) K hK]
  have hleft : (∫ ω, (star (((max (‖f ω‖ - K) 0 / ‖f ω‖ : ℝ) : ℂ) * f ω) *
      g ω).re ∂reducedLaw Q) = (inner ℂ v g).re := by
    have hi := (Lp.memLp v).star.integrable_mul (Lp.memLp g)
    have hr : (∫ ω, (star (v ω) * g ω).re ∂reducedLaw Q) =
        (∫ ω, star (v ω) * g ω ∂reducedLaw Q).re := integral_re hi
    have hm : inner ℂ v g = ∫ ω, star (v ω) * g ω ∂reducedLaw Q := by
      rw [L2.inner_def]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun ω => by
        simp only [RCLike.inner_apply, Complex.star_def]
        ring
    rw [hm, ← hr]
    apply integral_congr_ae
    filter_upwards [hvrep] with ω hω
    rw [hω]
  rw [hleft]
  calc
    (inner ℂ v g).re ≤
        lam * (inner ℂ v (complexForceDrift Q i (WithLp.toLp 2 H))).re := by
      linarith only [he, hdiff]
    _ ≤ |lam| * |(inner ℂ v (complexForceDrift Q i (WithLp.toLp 2 H))).re| := by
      rw [← abs_mul]
      exact le_abs_self _
    _ ≤ |lam| * (C * (∫ ω, ‖v ω‖ ^ 2 ∂reducedLaw Q)) :=
      mul_le_mul_of_nonneg_left (hbound Q hQ v H hv i) (abs_nonneg lam)
    _ = C * |lam| * (∫ ω, (max (‖f ω‖ - K) 0) ^ 2 ∂reducedLaw Q) := by
      rw [hmass]
      ring

/-- The actual generator tested against radial soft thresholding satisfies a
uniform energy bound for every signed real force. -/
theorem response_real_force_threshold_energy
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
        (hQ : HasSmoothBounds D Q) (lam : ℝ)
        (f g : Lp ℂ 2 (reducedLaw Q)),
        IsComplexGeneratorPair Q (⟨0, by omega⟩ : Fin d) (lam : ℂ) f g →
        ∀ K : ℝ, 0 ≤ K →
          (∫ ω, (star (((max (‖f ω‖ - K) 0 / ‖f ω‖ : ℝ) : ℂ) * f ω) *
            g ω).re ∂reducedLaw Q) ≤
            C * |lam| * (∫ ω, (max (‖f ω‖ - K) 0) ^ 2 ∂reducedLaw Q) := by
  obtain ⟨C, hC, henergy⟩ := response_real_force_threshold_energy_of_gradient d D
  refine ⟨C, hC, ?_⟩
  intro Q hQ lam f g hfg K hK
  obtain ⟨G, hG, htest⟩ := hfg
  obtain ⟨v, H, hvrep, hv, hHrep⟩ := response_threshold_horizontal_gradient
    (reducedLaw Q) (reducedLaw_stationary Q) f G hG K hK
  exact henergy Q hQ ⟨0, by omega⟩ lam f g v G H K hK
    ⟨G, hG, htest⟩ hG hv hvrep hHrep

end EinsteinFull.Blueprint
