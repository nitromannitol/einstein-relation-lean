import EinsteinFull.Work.W4.ActualHomogeneousGaussianSemigroupProof
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
Positive-time differentiation of the literal anisotropic Gaussian. The complex
force is fixed, with both signs retained. The scalar kernel has the adjoint
spatial drift; convolution against positive stationary translations reverses it.
-/

open MeasureTheory Filter Set
open scoped Topology BigOperators
noncomputable section
namespace EinsteinFull
open EinsteinRelation

variable {d : ℕ} {Λ r : ℝ}

/-- Time derivative of the real Gaussian with covariance `t A`. -/
theorem hasDerivAt_anisotropicGaussian_time (A : Mat d) (x : Vec d)
    (s : ℝ) (hs : 0 < s) :
    HasDerivAt (fun t => anisotropicGaussian A t x)
      ((-(d : ℝ) / (2 * s) +
        (∑ j, ∑ k, x j * (A⁻¹) j k * x k) / (2 * s ^ 2)) *
        anisotropicGaussian A s x) s := by
  let p : ℝ := -(d : ℝ) / 2
  let q : ℝ := ∑ j, ∑ k, x j * (A⁻¹) j k * x k
  have hb : 0 < 2 * Real.pi * s := by positivity
  have hp := (((hasDerivAt_id s).const_mul (2 * Real.pi)).rpow_const
    (p := p) (Or.inl hb.ne')).div_const (Real.sqrt A.det)
  have he := (((hasDerivAt_const s (-q)).div
    ((hasDerivAt_id s).const_mul 2) (by positivity : 2 * s ≠ 0)).exp)
  have h := hp.mul he
  change HasDerivAt (fun t => anisotropicGaussian A t x) _ s at h
  convert h using 1
  dsimp only [id_eq]
  rw [Real.rpow_sub hb]
  simp only [Real.rpow_one]
  dsimp [anisotropicGaussian, p, q]
  field_simp
  ring

/-- The exact time-derivative kernel, without any generator-domain premise. -/
def homogenizedGaussianKernelTimeDerivative (Q : EnvironmentLaw d Λ r) (i : Fin d)
    (s : ℝ) (hs : 0 < s) (ζ : ℂ) (x : Vec d) : ℂ :=
  (((-(d : ℝ) / (2 * s) +
      (∑ j, ∑ k, x j * ((homogenizedCoefficient Q)⁻¹) j k * x k) /
        (2 * s ^ 2) : ℝ) : ℂ) -
      ζ ^ 2 * (homogenizedCoefficient Q i i : ℂ) / 2) *
    homogenizedGaussianKernel Q i s hs ζ x

/-- Differentiation in time of the literal kernel on its positive-time domain.
The value zero outside that domain is irrelevant to this local derivative. -/
theorem hasDerivAt_homogenizedGaussianKernel_time (Q : EnvironmentLaw d Λ r)
    (i : Fin d) (ζ : ℂ) (x : Vec d) (s : ℝ) (hs : 0 < s) :
    HasDerivAt (fun t => if ht : 0 < t then homogenizedGaussianKernel Q i t ht ζ x else 0)
      (homogenizedGaussianKernelTimeDerivative Q i s hs ζ x) s := by
  have hg := (hasDerivAt_anisotropicGaussian_time (homogenizedCoefficient Q) x s hs).ofReal_comp
  have ht := (((hasDerivAt_const s (ζ * (x i : ℂ))).sub
    (((((hasDerivAt_id s).ofReal_comp).const_mul (ζ ^ 2)).mul_const
      (homogenizedCoefficient Q i i : ℂ)).div_const 2)).cexp)
  have h := ht.mul hg
  apply HasDerivAt.congr_of_eventuallyEq (f := fun t : ℝ =>
    Complex.exp (ζ * (x i : ℂ) - ζ ^ 2 * (t : ℂ) *
      (homogenizedCoefficient Q i i : ℂ) / 2) *
        (anisotropicGaussian (homogenizedCoefficient Q) t x : ℂ)) ?_ ?_
  · convert h using 1 <;> try rfl
    dsimp [homogenizedGaussianKernelTimeDerivative]
    rw [homogenizedGaussianKernel_eq_exp_tilt]
    simp only [Complex.ofReal_mul]
    ring
  · filter_upwards [eventually_gt_nhds hs] with t ht
    rw [dif_pos ht, homogenizedGaussianKernel_eq_exp_tilt]

private lemma gaussian_matrix_time_identities (A : Mat d) (hA : A.transpose = A)
    (hdet : IsUnit A.det) (x : Vec d) (i : Fin d) :
    (∀ j, ∑ k, A j k * (A⁻¹).mulVec x k = x j) ∧
    (∀ j, ∑ k, A j k * (A⁻¹) j k = 1) ∧
    (∑ j, A j i * (A⁻¹).mulVec x j) = x i := by
  have hAB := Matrix.mul_nonsing_inv A hdet
  have hB : (A⁻¹).transpose = A⁻¹ := by
    rw [Matrix.transpose_nonsing_inv, hA]
  have hrow (j : Fin d) : ∑ k, A j k * (A⁻¹).mulVec x k = x j := by
    change (A.mulVec ((A⁻¹).mulVec x)) j = _
    rw [Matrix.mulVec_mulVec, hAB, Matrix.one_mulVec]
  refine ⟨hrow, ?_, ?_⟩
  · intro j
    have h := congrFun (congrFun hAB j) j
    simp only [Matrix.mul_apply, Matrix.one_apply_eq] at h
    simpa only [show ∀ k, (A⁻¹) k j = (A⁻¹) j k from
      fun k => congrFun (congrFun hB j) k] using h
  · convert hrow i using 1
    apply Finset.sum_congr rfl
    intro j _
    rw [show A j i = A i j from congrFun (congrFun hA i) j]

/-- The spatial expression of the density is the adjoint drift expression:
`∂t K = (1/2) A:D² K - ζ (A e_i)·D K`. -/
theorem homogenizedGaussianKernelTimeDerivative_eq_spatial
    (Q : EnvironmentLaw d Λ r) (i : Fin d) (s : ℝ) (hs : 0 < s)
    (ζ : ℂ) (x : Vec d) :
    homogenizedGaussianKernelTimeDerivative Q i s hs ζ x =
      (1 / 2 : ℂ) * (∑ j, ∑ k, (homogenizedCoefficient Q j k : ℂ) *
        fderiv ℝ (fun y => fderiv ℝ (homogenizedGaussianKernel Q i s hs ζ) y
          (unitVector j)) x (unitVector k)) -
      ζ * ∑ j, ((homogenizedCoefficient Q).mulVec (unitVector i) j : ℂ) *
        fderiv ℝ (homogenizedGaussianKernel Q i s hs ζ) x (unitVector j) := by
  let A := homogenizedCoefficient Q
  let b := (A⁻¹).mulVec x
  have hA : A.transpose = A := homogenizedMatrix_transpose Q
  obtain ⟨hrow, htrace, hcol⟩ := gaussian_matrix_time_identities A hA
    (isUnit_iff_ne_zero.mpr (det_homogenizedCoefficient_pos Q).ne') x i
  have hrowC (j : Fin d) : ∑ k, (A j k : ℂ) * (b k : ℂ) = (x j : ℂ) := by
    exact_mod_cast hrow j
  have htraceC : (∑ j, ∑ k, (A j k : ℂ) * ((A⁻¹) j k : ℂ)) = (d : ℂ) := by
    simp_rw [← Complex.ofReal_mul, ← Complex.ofReal_sum, htrace]
    simp
  have hcolC : (∑ j, (A j i : ℂ) * (b j : ℂ)) = (x i : ℂ) := by
    exact_mod_cast hcol
  have hq : (∑ j, (x j : ℂ) * (b j : ℂ)) =
      ((∑ j, ∑ k, x j * (A⁻¹) j k * x k : ℝ) : ℂ) := by
    simp only [b, Matrix.mulVec, dotProduct, Complex.ofReal_sum, Complex.ofReal_mul,
      Finset.mul_sum, mul_assoc]
  have hu (j : Fin d) : (∑ k, (A j k : ℂ) * (unitVector i k : ℂ)) = (A j i : ℂ) := by
    simp [unitVector, Pi.single_apply, apply_ite Complex.ofReal, mul_ite]
  have hv (j : Fin d) : (A.mulVec (unitVector i) j : ℂ) = (A j i : ℂ) := by
    simp [Matrix.mulVec, dotProduct, unitVector, Pi.single_apply, mul_ite]
  have hdiag : (∑ j, (A j i : ℂ) * (unitVector i j : ℂ)) = (A i i : ℂ) := by
    simp [unitVector, Pi.single_apply, apply_ite Complex.ofReal, mul_ite]
  have hcross : (∑ j, (unitVector i j : ℂ) * (x j : ℂ)) = (x i : ℂ) := by
    simp [unitVector, Pi.single_apply, apply_ite Complex.ofReal, ite_mul]
  have hcontract :
      (∑ j, ∑ k, (A j k : ℂ) *
        (((ζ * (unitVector i j : ℂ) - (b j : ℂ) / (s : ℂ)) *
          (ζ * (unitVector i k : ℂ) - (b k : ℂ) / (s : ℂ))) -
          ((A⁻¹) j k : ℂ) / (s : ℂ))) =
        ζ ^ 2 * (A i i : ℂ) - 2 * ζ * (x i : ℂ) / (s : ℂ) +
          ((∑ j, ∑ k, x j * (A⁻¹) j k * x k : ℝ) : ℂ) / (s : ℂ) ^ 2 -
            (d : ℂ) / (s : ℂ) := by
    have hinner (j : Fin d) :
        (∑ k, (A j k : ℂ) * ((ζ * (unitVector i j : ℂ) - (b j : ℂ) / (s : ℂ)) *
          (ζ * (unitVector i k : ℂ) - (b k : ℂ) / (s : ℂ)) -
          ((A⁻¹) j k : ℂ) / (s : ℂ))) =
        (ζ * (unitVector i j : ℂ) - (b j : ℂ) / (s : ℂ)) *
          (ζ * (A j i : ℂ) - (x j : ℂ) / (s : ℂ)) -
            (∑ k, (A j k : ℂ) * ((A⁻¹) j k : ℂ)) / (s : ℂ) := by
      calc
        _ = (ζ * (unitVector i j : ℂ) - (b j : ℂ) / (s : ℂ)) *
            (∑ k, (A j k : ℂ) * (ζ * (unitVector i k : ℂ) - (b k : ℂ) / (s : ℂ))) -
              (∑ k, (A j k : ℂ) * ((A⁻¹) j k : ℂ)) / (s : ℂ) := by
          rw [Finset.mul_sum, Finset.sum_div, ← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro k _
          ring
        _ = _ := by
          congr 1
          congr 1
          calc
            _ = ζ * (∑ k, (A j k : ℂ) * (unitVector i k : ℂ)) -
                (∑ k, (A j k : ℂ) * (b k : ℂ)) / (s : ℂ) := by
              rw [Finset.mul_sum, Finset.sum_div, ← Finset.sum_sub_distrib]
              apply Finset.sum_congr rfl
              intro k _
              ring
            _ = _ := by rw [hu, hrowC]
    simp_rw [hinner]
    rw [Finset.sum_sub_distrib, ← Finset.sum_div, htraceC]
    congr 1
    calc
      _ = ζ ^ 2 * (∑ j, (A j i : ℂ) * (unitVector i j : ℂ)) -
          ζ * (∑ j, (unitVector i j : ℂ) * (x j : ℂ)) / (s : ℂ) -
          ζ * (∑ j, (A j i : ℂ) * (b j : ℂ)) / (s : ℂ) +
          (∑ j, (x j : ℂ) * (b j : ℂ)) / (s : ℂ) ^ 2 := by
        simp only [Finset.mul_sum, Finset.sum_div]
        rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = _ := by rw [hdiag, hcross, hcolC, hq]; ring
  have hdrift : (∑ j, (A j i : ℂ) *
      (ζ * (unitVector i j : ℂ) - (b j : ℂ) / (s : ℂ))) =
        ζ * (A i i : ℂ) - (x i : ℂ) / (s : ℂ) := by
    calc
      _ = ζ * (∑ j, (A j i : ℂ) * (unitVector i j : ℂ)) -
          (∑ j, (A j i : ℂ) * (b j : ℂ)) / (s : ℂ) := by
        simp only [Finset.mul_sum, Finset.sum_div]
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = _ := by rw [hdiag, hcolC]
  simp_rw [fderiv_fderiv_homogenizedGaussianKernel_complexForce_coordinate,
    fderiv_homogenizedGaussianKernel_complexForce_coordinate]
  change _ = (1 / 2 : ℂ) * (∑ j, ∑ k, (A j k : ℂ) *
    ((_ * _ - ((A⁻¹) j k : ℂ) / (s : ℂ)) * _)) -
      ζ * ∑ j, (A.mulVec (unitVector i) j : ℂ) * ((_ - (b j : ℂ) / (s : ℂ)) * _)
  simp_rw [← mul_assoc, ← Finset.sum_mul, hv]
  rw [hcontract, hdrift]
  unfold homogenizedGaussianKernelTimeDerivative
  simp only [Complex.ofReal_add, Complex.ofReal_div, Complex.ofReal_neg,
    Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_natCast, Complex.ofReal_ofNat]
  dsimp only [A]
  field_simp [Complex.ofReal_ne_zero.mpr hs.ne']
  ring

private lemma timeReducedBound_pos (Q : EnvironmentLaw d Λ r) :
    0 < sourceReducedBound Λ := by
  unfold sourceReducedBound
  exact mul_pos (Real.exp_pos _) (by nlinarith [Q.ellipticity_parameter, sq_nonneg Λ])

private lemma timeEuclideanNorm_sq (x : Vec d) : euclideanNorm x ^ 2 = euclideanSq x := by
  apply Real.sq_sqrt
  unfold euclideanSq dot
  exact Finset.sum_nonneg fun j _ => mul_self_nonneg (x j)

private lemma timeCoord_le (x : Vec d) (j : Fin d) : |x j| ≤ euclideanNorm x := by
  apply le_of_sq_le_sq _ (Real.sqrt_nonneg _)
  change |x j| ^ 2 ≤ euclideanNorm x ^ 2
  rw [sq_abs, timeEuclideanNorm_sq]
  simpa only [euclideanSq, dot, pow_two] using!
    Finset.single_le_sum (fun k _ => mul_self_nonneg (x k)) (Finset.mem_univ j)

private lemma timeEntry_le (Q : EnvironmentLaw d Λ r) (i : Fin d) :
    |homogenizedCoefficient Q i i| ≤ sourceReducedBound Λ := by
  have h := (timeCoord_le ((homogenizedCoefficient Q).mulVec (unitVector i)) i).trans
    (homogenizedMatrix_euclideanNorm_mulVec_unitVector_le Q i)
  simpa [Matrix.mulVec, dotProduct, unitVector, Pi.single_apply, mul_ite,
    euclideanNorm, euclideanSq, dot] using h

private lemma timeGaussian_exponent {K b R z q s : ℝ} (hK : 0 < K) (hb : 0 < b)
    (_hR : 0 ≤ R) (_hz : 0 ≤ z) (hs : 0 < s) (hsb : s ≤ b)
    (hq : K⁻¹ * R ^ 2 ≤ q) :
    z * R + z ^ 2 * b * K / 2 - q / (2 * s) ≤
      2 * K * b * z ^ 2 - R ^ 2 / (4 * K * b) := by
  have hq0 : 0 ≤ q := (mul_nonneg (inv_nonneg.mpr hK.le) (sq_nonneg R)).trans hq
  have hdiv : R ^ 2 / (2 * K * b) ≤ q / (2 * s) := by
    calc
      _ = (K⁻¹ * R ^ 2) / (2 * b) := by ring
      _ ≤ q / (2 * b) := div_le_div_of_nonneg_right hq (by positivity)
      _ ≤ q / (2 * s) := div_le_div_of_nonneg_left hq0 (by positivity) (by linarith)
  have hy : z * R - R ^ 2 / (4 * K * b) ≤ K * b * z ^ 2 := by
    apply (mul_le_mul_iff_right₀ (by positivity : 0 < 4 * K * b)).mp
    field_simp
    nlinarith only [sq_nonneg (R - 2 * K * b * z)]
  have hpos : 0 ≤ K * b * z ^ 2 := by positivity
  have hd : R ^ 2 / (2 * K * b) = 2 * (R ^ 2 / (4 * K * b)) := by ring
  rw [hd] at hdiv
  nlinarith only [hdiv, hy, hpos]

/-- A common Gaussian bound for the literal kernels on any positive compact
window. All constants depend only on structural data, window and fixed force. -/
theorem norm_homogenizedGaussianKernel_le_timeWindow (Q : EnvironmentLaw d Λ r)
    (i : Fin d) (a b : ℝ) (ha : 0 < a) (s : ℝ) (hs : 0 < s)
    (has : a ≤ s) (hsb : s ≤ b) (ζ : ℂ) (x : Vec d) :
    ‖homogenizedGaussianKernel Q i s hs ζ x‖ ≤
      ((2 * Real.pi * a) ^ (-(d : ℝ) / 2) *
        Real.sqrt ((Fintype.card (Equiv.Perm (Fin d)) : ℝ) * (sourceReducedBound Λ) ^ d)) *
      Real.exp (2 * sourceReducedBound Λ * b * ‖ζ‖ ^ 2) *
      Real.exp (-euclideanSq x / (4 * sourceReducedBound Λ * b)) := by
  let K := sourceReducedBound Λ
  let P := Real.sqrt ((Fintype.card (Equiv.Perm (Fin d)) : ℝ) * K ^ d)
  let q := dot x ((homogenizedCoefficient Q)⁻¹.mulVec x)
  let pref := (2 * Real.pi * s) ^ (-(d : ℝ) / 2) / Real.sqrt (homogenizedCoefficient Q).det
  have hK : 0 < K := timeReducedBound_pos Q
  have hb : 0 < b := hs.trans_le hsb
  have hp0 : 0 ≤ pref := by dsimp [pref]; positivity
  have hP : pref ≤ (2 * Real.pi * a) ^ (-(d : ℝ) / 2) * P := by
    calc
      _ ≤ (2 * Real.pi * a) ^ (-(d : ℝ) / 2) /
          Real.sqrt (homogenizedCoefficient Q).det := by
        apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
        exact Real.rpow_le_rpow_of_nonpos (by positivity)
          (by gcongr) (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg d)) (by norm_num))
      _ ≤ _ := by
        rw [div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_left (inv_sqrt_det_homogenizedCoefficient_le Q)
          (Real.rpow_nonneg (by positivity) _)
  have htilt :
      (ζ * (x i : ℂ) - ζ ^ 2 * (s : ℂ) * (homogenizedCoefficient Q i i : ℂ) / 2).re ≤
        ‖ζ‖ * euclideanNorm x + ‖ζ‖ ^ 2 * b * K / 2 := by
    calc
      _ ≤ ‖ζ * (x i : ℂ) - ζ ^ 2 * (s : ℂ) * (homogenizedCoefficient Q i i : ℂ) / 2‖ :=
        Complex.re_le_norm _
      _ ≤ ‖ζ * (x i : ℂ)‖ + ‖ζ ^ 2 * (s : ℂ) *
          (homogenizedCoefficient Q i i : ℂ) / 2‖ := norm_sub_le _ _
      _ = ‖ζ‖ * |x i| + ‖ζ‖ ^ 2 * s * |homogenizedCoefficient Q i i| / 2 := by
        simp only [norm_mul, norm_pow, norm_div, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos hs]
        norm_num
      _ ≤ _ := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left (timeCoord_le x i) (norm_nonneg _)
        · gcongr
          exact timeEntry_le Q i
  have hq := (homogenizedCoefficient_inv_quadratic_bounds Q x).1
  rw [← timeEuclideanNorm_sq] at hq
  have he := (sub_le_sub_right htilt (q / (2 * s))).trans
    (timeGaussian_exponent hK hb (Real.sqrt_nonneg _) (norm_nonneg _) hs hsb hq)
  have hreal : anisotropicGaussian (homogenizedCoefficient Q) s x =
      pref * Real.exp (-q / (2 * s)) := by
    dsimp [anisotropicGaussian, pref, q, dot, Matrix.mulVec, dotProduct]
    simp only [Finset.mul_sum, mul_assoc]
  rw [homogenizedGaussianKernel_eq_exp_tilt, norm_mul, Complex.norm_exp,
    Complex.norm_real, Real.norm_eq_abs, hreal,
    abs_of_nonneg (mul_nonneg hp0 (Real.exp_pos _).le)]
  calc
    _ = pref * Real.exp ((ζ * (x i : ℂ) - ζ ^ 2 * (s : ℂ) *
        (homogenizedCoefficient Q i i : ℂ) / 2).re - q / (2 * s)) := by
      rw [Real.exp_sub, neg_div, Real.exp_neg]
      ring
    _ ≤ ((2 * Real.pi * a) ^ (-(d : ℝ) / 2) * P) *
        Real.exp (2 * K * b * ‖ζ‖ ^ 2 - euclideanNorm x ^ 2 / (4 * K * b)) :=
      mul_le_mul hP (Real.exp_le_exp.mpr he) (Real.exp_pos _).le (by positivity)
    _ = _ := by
      dsimp only [K, P]
      rw [timeEuclideanNorm_sq, Real.exp_sub]
      simp only [neg_div, Real.exp_neg]
      ring

/-- Quadratic-polynomial Gaussian domination of the time derivative, uniform
on each positive compact time window, for fixed signed complex force. -/
theorem norm_homogenizedGaussianKernelTimeDerivative_le_timeWindow
    (Q : EnvironmentLaw d Λ r) (i : Fin d) (a b : ℝ) (ha : 0 < a)
    (s : ℝ) (hs : 0 < s) (has : a ≤ s) (hsb : s ≤ b) (ζ : ℂ) (x : Vec d) :
    ‖homogenizedGaussianKernelTimeDerivative Q i s hs ζ x‖ ≤
      ((d : ℝ) / (2 * a) + sourceReducedBound Λ / (2 * a ^ 2) +
        ‖ζ‖ ^ 2 * sourceReducedBound Λ / 2) * (1 + euclideanSq x) *
      ((2 * Real.pi * a) ^ (-(d : ℝ) / 2) *
        Real.sqrt ((Fintype.card (Equiv.Perm (Fin d)) : ℝ) * (sourceReducedBound Λ) ^ d)) *
      Real.exp (2 * sourceReducedBound Λ * b * ‖ζ‖ ^ 2) *
      Real.exp (-euclideanSq x / (4 * sourceReducedBound Λ * b)) := by
  let K := sourceReducedBound Λ
  let q := dot x ((homogenizedCoefficient Q)⁻¹.mulVec x)
  have hK : 0 < K := timeReducedBound_pos Q
  have hx : 0 ≤ euclideanSq x := by rw [← timeEuclideanNorm_sq]; positivity
  have hq0 : 0 ≤ q :=
    (mul_nonneg (inv_nonneg.mpr hK.le) hx).trans
      (homogenizedCoefficient_inv_quadratic_bounds Q x).1
  have hq : q ≤ K * euclideanSq x := (homogenizedCoefficient_inv_quadratic_bounds Q x).2
  have heq : (∑ j, ∑ k, x j * ((homogenizedCoefficient Q)⁻¹) j k * x k) = q := by
    dsimp [q, dot, Matrix.mulVec, dotProduct]
    simp only [Finset.mul_sum, mul_assoc]
  have hm :
      ‖((-(d : ℝ) / (2 * s) + q / (2 * s ^ 2) : ℝ) : ℂ) -
          ζ ^ 2 * (homogenizedCoefficient Q i i : ℂ) / 2‖ ≤
        (d : ℝ) / (2 * a) + K * euclideanSq x / (2 * a ^ 2) + ‖ζ‖ ^ 2 * K / 2 := by
    calc
      _ ≤ ‖((-(d : ℝ) / (2 * s) + q / (2 * s ^ 2) : ℝ) : ℂ)‖ +
          ‖ζ ^ 2 * (homogenizedCoefficient Q i i : ℂ) / 2‖ := norm_sub_le _ _
      _ ≤ (d : ℝ) / (2 * s) + q / (2 * s ^ 2) +
          ‖ζ‖ ^ 2 * |homogenizedCoefficient Q i i| / 2 := by
        simp only [Complex.norm_real, Real.norm_eq_abs, norm_div, norm_mul, norm_pow]
        norm_num only [Complex.norm_ofNat]
        apply add_le_add _ le_rfl
        exact (abs_add_le _ _).trans (by
          rw [abs_div, abs_neg, abs_of_nonneg (Nat.cast_nonneg d),
            abs_of_pos (by positivity : 0 < 2 * s),
            abs_of_nonneg (div_nonneg hq0 (by positivity))])
      _ ≤ _ := by
        apply add_le_add
        · apply add_le_add
          · exact div_le_div_of_nonneg_left (Nat.cast_nonneg d) (by positivity) (by linarith)
          · exact (div_le_div_of_nonneg_right hq (by positivity)).trans
              (div_le_div_of_nonneg_left (mul_nonneg hK.le hx) (by positivity)
                (by nlinarith [sq_nonneg (s - a)]))
        · exact div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left (timeEntry_le Q i) (sq_nonneg _)) (by norm_num)
  have hpoly :
      (d : ℝ) / (2 * a) + K * euclideanSq x / (2 * a ^ 2) + ‖ζ‖ ^ 2 * K / 2 ≤
        ((d : ℝ) / (2 * a) + K / (2 * a ^ 2) + ‖ζ‖ ^ 2 * K / 2) *
          (1 + euclideanSq x) := by
    have h0 : 0 ≤ (d : ℝ) / (2 * a) := by positivity
    have h1 : 0 ≤ K / (2 * a ^ 2) := by positivity
    have h2 : 0 ≤ ‖ζ‖ ^ 2 * K / 2 := by positivity
    rw [show K * euclideanSq x / (2 * a ^ 2) =
      (K / (2 * a ^ 2)) * euclideanSq x by ring]
    nlinarith only [mul_nonneg h0 hx, mul_nonneg h2 hx, h1]
  unfold homogenizedGaussianKernelTimeDerivative
  rw [norm_mul, heq]
  calc
    _ ≤ (((d : ℝ) / (2 * a) + K / (2 * a ^ 2) + ‖ζ‖ ^ 2 * K / 2) *
        (1 + euclideanSq x)) *
        (((2 * Real.pi * a) ^ (-(d : ℝ) / 2) *
          Real.sqrt ((Fintype.card (Equiv.Perm (Fin d)) : ℝ) * K ^ d)) *
          Real.exp (2 * K * b * ‖ζ‖ ^ 2) *
          Real.exp (-euclideanSq x / (4 * K * b))) :=
      mul_le_mul (hm.trans hpoly)
        (norm_homogenizedGaussianKernel_le_timeWindow Q i a b ha s hs has hsb ζ x)
        (norm_nonneg _) (by positivity)
    _ = _ := by ring

private lemma integrable_timeGaussianEnvelope (c : ℝ) (hc : 0 < c) :
    Integrable (fun x : Vec d => Real.exp (-euclideanSq x / c)) := by
  have hg : Integrable (fun a : ℝ => Real.exp (-(a * a) / c)) := by
    convert integrable_exp_neg_mul_sq (b := 1 / c) (by positivity) using 1
    ext a
    congr 1
    ring
  have hp : Integrable (fun x : Vec d => ∏ j, Real.exp (-(x j * x j) / c)) := by
    rw [volume_pi]
    exact Integrable.fintype_prod fun _ => hg
  convert hp using 1
  ext x
  rw [← Real.exp_sum]
  congr 1
  simp only [euclideanSq, dot, Finset.sum_div, Finset.sum_neg_distrib, neg_div]

private lemma integrable_polynomial_timeGaussianEnvelope (c : ℝ) (hc : 0 < c) :
    Integrable (fun x : Vec d => (1 + euclideanSq x) * Real.exp (-euclideanSq x / c)) := by
  apply Integrable.mono' ((integrable_timeGaussianEnvelope (2 * c) (by positivity)).const_mul
    (1 + 2 * c)) (by unfold euclideanSq dot; fun_prop)
  refine Eventually.of_forall fun x => ?_
  have hx : 0 ≤ euclideanSq x := by rw [← timeEuclideanNorm_sq]; positivity
  rw [Real.norm_of_nonneg (by positivity)]
  have hu : 0 ≤ euclideanSq x / (2 * c) := by positivity
  have h1 : 1 ≤ Real.exp (euclideanSq x / (2 * c)) := Real.one_le_exp hu
  have h2 : euclideanSq x ≤ 2 * c * Real.exp (euclideanSq x / (2 * c)) := by
    have h := Real.add_one_le_exp (euclideanSq x / (2 * c))
    rw [mul_comm (2 * c)]
    apply (div_le_iff₀ (by positivity : 0 < 2 * c)).mp
    linarith only [h]
  calc
    _ ≤ ((1 + 2 * c) * Real.exp (euclideanSq x / (2 * c))) *
        Real.exp (-euclideanSq x / c) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      nlinarith only [h1, h2]
    _ = _ := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring

/-- A structural integrable envelope is chosen before the environment law,
coordinate and time on a prescribed positive compact time window. -/
theorem exists_integrable_homogenizedGaussianKernelTimeDerivative_bound
    (d : ℕ) (Λ a b : ℝ) (ha : 0 < a) (hb : 0 < b) (ζ : ℂ)
    (hΛ : 1 ≤ Λ) :
    ∃ B : Vec d → ℝ, Integrable B ∧ (∀ x, 0 ≤ B x) ∧
      ∀ (r : ℝ) (Q : EnvironmentLaw d Λ r) (i : Fin d) (s : ℝ) (hs : 0 < s),
        a ≤ s → s ≤ b → ∀ x,
          ‖homogenizedGaussianKernelTimeDerivative Q i s hs ζ x‖ ≤ B x := by
  let K := sourceReducedBound Λ
  let C := ((d : ℝ) / (2 * a) + K / (2 * a ^ 2) + ‖ζ‖ ^ 2 * K / 2) *
    ((2 * Real.pi * a) ^ (-(d : ℝ) / 2) *
      Real.sqrt ((Fintype.card (Equiv.Perm (Fin d)) : ℝ) * K ^ d)) *
      Real.exp (2 * K * b * ‖ζ‖ ^ 2)
  have hK : 0 < K := by
    dsimp [K, sourceReducedBound]
    exact mul_pos (Real.exp_pos _) (by nlinarith [sq_nonneg Λ])
  refine ⟨fun x => C * ((1 + euclideanSq x) * Real.exp (-euclideanSq x / (4 * K * b))),
    (integrable_polynomial_timeGaussianEnvelope (4 * K * b) (by positivity)).const_mul C,
    ?_, ?_⟩
  · intro x
    have hx : 0 ≤ euclideanSq x := by rw [← timeEuclideanNorm_sq]; positivity
    dsimp [C]
    positivity
  · intro r Q i s hs has hsb x
    convert norm_homogenizedGaussianKernelTimeDerivative_le_timeWindow Q i a b ha
      s hs has hsb ζ x using 1
    dsimp [C, K]
    ring

/-- Spatial Lebesgue integrability of the exact time-derivative kernel. -/
theorem integrable_homogenizedGaussianKernelTimeDerivative (Q : EnvironmentLaw d Λ r)
    (i : Fin d) (s : ℝ) (hs : 0 < s) (ζ : ℂ) :
    Integrable (homogenizedGaussianKernelTimeDerivative Q i s hs ζ) := by
  obtain ⟨B, hB, _, hbound⟩ :=
    exists_integrable_homogenizedGaussianKernelTimeDerivative_bound d Λ s s hs hs ζ
      Q.ellipticity_parameter
  apply Integrable.mono' hB ?_ (Eventually.of_forall (hbound r Q i s hs le_rfl le_rfl))
  apply Continuous.aestronglyMeasurable
  unfold homogenizedGaussianKernelTimeDerivative homogenizedGaussianKernel
  fun_prop

/-- The time derivative defines a genuine Bochner integral for arbitrary L2 data. -/
theorem integrable_homogeneousAverageTimeDerivative_integrand
    (Q : EnvironmentLaw d Λ r) (i : Fin d) (s : ℝ) (hs : 0 < s)
    (ζ : ℂ) (f : Lp ℂ 2 (reducedLaw Q)) :
    Integrable (fun x : Vec d => homogenizedGaussianKernelTimeDerivative Q i s hs ζ x •
      complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x f) := by
  letI := reducedLaw_probability Q
  apply integrable_kernel_complexTranslation _ _ _
    (integrable_homogenizedGaussianKernelTimeDerivative Q i s hs ζ)
  unfold homogenizedGaussianKernelTimeDerivative homogenizedGaussianKernel
  fun_prop

/-- Positive-time L2 derivative of the actual stationary Gaussian average,
obtained by dominated differentiation of its literal Bochner integral. -/
theorem hasDerivAt_homogeneousAverage_time (Q : EnvironmentLaw d Λ r) (i : Fin d)
    (ζ : ℂ) (f : Lp ℂ 2 (reducedLaw Q)) (s : ℝ) (hs : 0 < s) :
    HasDerivAt
      (fun t => if ht : 0 < t then homogeneousAverage Q i t ht ζ f else 0)
      (∫ x : Vec d, homogenizedGaussianKernelTimeDerivative Q i s hs ζ x •
        complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x f) s := by
  let F : ℝ → Vec d → Lp ℂ 2 (reducedLaw Q) := fun t x =>
    (if ht : 0 < t then homogenizedGaussianKernel Q i t ht ζ x else 0) •
      complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x f
  let F' : ℝ → Vec d → Lp ℂ 2 (reducedLaw Q) := fun t x =>
    (if ht : 0 < t then homogenizedGaussianKernelTimeDerivative Q i t ht ζ x else 0) •
      complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x f
  obtain ⟨B, hB, _, hbound⟩ :=
    exists_integrable_homogenizedGaussianKernelTimeDerivative_bound d Λ (s / 2) (2 * s)
      (by positivity) (by positivity) ζ Q.ellipticity_parameter
  have hball (t : ℝ) (ht : t ∈ Metric.ball s (s / 2)) :
      0 < t ∧ s / 2 ≤ t ∧ t ≤ 2 * s := by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at ht
    constructor
    · linarith [ht.1]
    · constructor <;> linarith [ht.1, ht.2]
  have hmeas : ∀ᶠ t in 𝓝 s, AEStronglyMeasurable (F t) := by
    filter_upwards [eventually_gt_nhds hs] with t ht
    simpa only [F, dif_pos ht] using!
      (integrable_homogeneousAverage_integrand Q i t ht ζ f).aestronglyMeasurable
  have hint : Integrable (F s) := by
    simpa only [F, dif_pos hs] using! integrable_homogeneousAverage_integrand Q i s hs ζ f
  have hmeas' : AEStronglyMeasurable (F' s) := by
    simpa only [F', dif_pos hs] using!
      (integrable_homogeneousAverageTimeDerivative_integrand Q i s hs ζ f).aestronglyMeasurable
  have hdom : ∀ᵐ x : Vec d, ∀ t ∈ Metric.ball s (s / 2), ‖F' t x‖ ≤ B x * ‖f‖ := by
    refine Eventually.of_forall fun x t ht => ?_
    obtain ⟨ht0, htlo, hthi⟩ := hball t ht
    dsimp only [F']
    rw [dif_pos ht0, norm_smul, norm_complexTranslation]
    exact mul_le_mul_of_nonneg_right (hbound r Q i t ht0 htlo hthi x) (norm_nonneg _)
  have hdiff : ∀ᵐ x : Vec d, ∀ t ∈ Metric.ball s (s / 2), HasDerivAt (F · x) (F' t x) t := by
    refine Eventually.of_forall fun x t ht => ?_
    have ht0 := (hball t ht).1
    simpa only [F, F', dif_pos ht0] using!
      (hasDerivAt_homogenizedGaussianKernel_time Q i ζ x t ht0).smul_const
        (complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x f)
  have h := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.ball_mem_nhds s (by positivity : 0 < s / 2))
    hmeas hint hmeas' hdom (hB.mul_const ‖f‖) hdiff).2
  have heq : (fun t => ∫ x, F t x) =
      (fun t => if ht : 0 < t then homogeneousAverage Q i t ht ζ f else 0) := by
    funext t
    by_cases ht : 0 < t
    · simp only [F, dif_pos ht, homogeneousAverage]
    · simp only [F, dif_neg ht, zero_smul, integral_zero]
  rw [heq] at h
  simpa only [F', dif_pos hs] using! h

/-- The constructed all-time stationary Gaussian evolution has the same
positive-time strong L2 derivative. The real time extension uses `max t 0`. -/
theorem hasDerivAt_homogeneousGaussianEvolution_time (Q : EnvironmentLaw d Λ r)
    (i : Fin d) (ζ : ℂ) (f : Lp ℂ 2 (reducedLaw Q)) (s : ℝ) (hs : 0 < s) :
    HasDerivAt (fun t : ℝ => homogeneousGaussianEvolution Q i ζ ⟨max t 0, le_max_right _ _⟩ f)
      (∫ x : Vec d, homogenizedGaussianKernelTimeDerivative Q i s hs ζ x •
        complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x f) s := by
  apply (hasDerivAt_homogeneousAverage_time Q i ζ f s hs).congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds hs] with t ht
  erw [dif_pos ht, homogeneousGaussianEvolution_pos Q i ζ _ (by simpa only [max_eq_left ht.le] using! ht)]
  simp only [max_eq_left ht.le]
  rfl

private lemma fderiv_gaussian_reflection (g : Vec d → ℂ) (x y v : Vec d)
    (hg : DifferentiableAt ℝ g (x - y)) :
    fderiv ℝ (fun z => g (x - z)) y v = -fderiv ℝ g (x - y) v := by
  have hh := hg.hasFDerivAt.comp y ((hasFDerivAt_id y).const_sub x)
  change (fderiv ℝ (g ∘ (fun z => x - z)) y) v = _
  rw [hh.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.id_apply, map_neg]

/-- In the translated kernel used by positive stationary translations, the
horizontal drift sign is positive. Both derivatives are literal Euclidean
Fréchet derivatives; the density PDE above has the opposite spatial sign. -/
theorem homogenizedGaussianKernelTimeDerivative_eq_translated_spatial
    (Q : EnvironmentLaw d Λ r) (i : Fin d) (s : ℝ) (hs : 0 < s)
    (ζ : ℂ) (x : Vec d) :
    homogenizedGaussianKernelTimeDerivative Q i s hs ζ x =
      (1 / 2 : ℂ) * (∑ j, ∑ k, (homogenizedCoefficient Q j k : ℂ) *
        fderiv ℝ (fun y => fderiv ℝ (fun z => homogenizedGaussianKernel Q i s hs ζ (x - z))
          y (unitVector j)) 0 (unitVector k)) +
      ζ * ∑ j, ((homogenizedCoefficient Q).mulVec (unitVector i) j : ℂ) *
        fderiv ℝ (fun y => homogenizedGaussianKernel Q i s hs ζ (x - y)) 0 (unitVector j) := by
  let K := homogenizedGaussianKernel Q i s hs ζ
  have hK (y : Vec d) : DifferentiableAt ℝ K y := by
    dsimp [K]
    exact ((contDiff_homogenizedGaussianKernel_complexForce Q i s hs ζ).differentiable
      (by simp)).differentiableAt
  have h1 (y : Vec d) (j : Fin d) :
      fderiv ℝ (fun z => K (x - z)) y (unitVector j) =
        -fderiv ℝ K (x - y) (unitVector j) :=
    fderiv_gaussian_reflection K x y (unitVector j) (hK _)
  have h2 (j k : Fin d) :
      fderiv ℝ (fun y => fderiv ℝ (fun z => K (x - z)) y (unitVector j))
        0 (unitVector k) =
      fderiv ℝ (fun y => fderiv ℝ K y (unitVector j)) x (unitVector k) := by
    simp_rw [h1]
    rw [fderiv_fun_neg]
    simp only [ContinuousLinearMap.neg_apply]
    rw [fderiv_gaussian_reflection (fun z => fderiv ℝ K z (unitVector j))
      x 0 (unitVector k)]
    · simp only [sub_zero, neg_neg]
    · dsimp [K]
      simp_rw [fderiv_homogenizedGaussianKernel_complexForce_coordinate]
      unfold Matrix.mulVec dotProduct homogenizedGaussianKernel
      fun_prop
  change _ = (1 / 2 : ℂ) * (∑ j, ∑ k, (homogenizedCoefficient Q j k : ℂ) *
    fderiv ℝ (fun y => fderiv ℝ (fun z => K (x - z)) y (unitVector j)) 0 (unitVector k)) +
    ζ * ∑ j, ((homogenizedCoefficient Q).mulVec (unitVector i) j : ℂ) *
      fderiv ℝ (fun y => K (x - y)) 0 (unitVector j)
  simp_rw [h2, h1, sub_zero, mul_neg, Finset.sum_neg_distrib]
  simpa only [sub_eq_add_neg, mul_neg] using!
    homogenizedGaussianKernelTimeDerivative_eq_spatial Q i s hs ζ x

end EinsteinFull
