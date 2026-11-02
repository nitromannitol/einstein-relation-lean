import EinsteinFull.Calculus.C6GaussianLocalH1Realization
import EinsteinFull.Calculus.PhysicalH1IntegrationSupport
import EinsteinRelation.Correctors.SpatialWeakProduct
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation EinsteinRelation.External.AKM
theorem physical_gaussian_local_divergence_testing
    {d : ℕ} (r : ℝ) (hr : 0 < r)
    (P : Fin d → Vec d → ℂ) (q : Vec d → ℂ)
    (hdivre : HasWeakDivergence Set.univ (fun x j => (P j x).re) (fun x => (q x).re))
    (hdivim : HasWeakDivergence Set.univ (fun x j => (P j x).im) (fun x => (q x).im))
    (hP : ∀ j, MemLp (fun x => (Real.exp (-euclideanSq x/(2*r)) : ℂ) * P j x) 2 volume)
    (hq : MemLp (fun x => (Real.exp (-euclideanSq x/(2*r)) : ℂ) * q x) 2 volume)
    (v : Lp ℂ 2 (volume : Measure (Vec d)))
    (H : Fin d → Lp ℂ 2 (volume : Measure (Vec d)))
    (hv : IsPhysicalH1Graph volume (Or.inl rfl) v H) :
    (∫ x : Vec d, (Real.exp (-euclideanSq x/r) : ℂ) * q x * v x) =
      -(∫ x : Vec d, ∑ j,
        P j x * ((Real.exp (-euclideanSq x/r) : ℂ) * H j x +
          ((-2*x j/r*Real.exp (-euclideanSq x/r) : ℝ) : ℂ) * v x)) := by
  classical
  have spatial_derivative {d : ℕ} (x : Vec d)
      (j : Fin d) (L r : ℝ) :
      HasDerivAt (fun s : ℝ =>
        Real.exp (-euclideanSq (x + s • Pi.single j 1) / (L * r)))
        (-2 * x j / (L * r) * Real.exp (-euclideanSq x / (L * r))) 0 := by
    have hcoord (k : Fin d) : HasDerivAt
        (fun s : ℝ => (x k + s * (Pi.single j 1 : Vec d) k) ^ 2)
        (2 * x k * (Pi.single j 1 : Vec d) k) 0 := by
      convert (((hasDerivAt_id (0 : ℝ)).mul_const ((Pi.single j 1 : Vec d) k)).const_add
        (x k)).pow 2 using 1
      · funext s
        dsimp
      · dsimp
        ring
    have hsum := HasDerivAt.fun_sum (u := Finset.univ) (fun k _ => hcoord k)
    have hsq : HasDerivAt (fun s : ℝ => euclideanSq (x + s • Pi.single j 1))
        (2 * x j) 0 := by
      simpa [euclideanSq, dot, sq, Pi.single_apply, Pi.add_apply, Pi.smul_apply,
        smul_eq_mul] using hsum
    have hg := (hsq.neg.div_const (L * r)).exp
    convert hg using 1
    dsimp
    simp only [zero_smul, add_zero]
    ring

  have admissible {d : ℕ} {L r : ℝ}
      (hL : 0 < L) (hr : 0 < r) :
      let η : Vec d → ℝ := fun x => Real.exp (-euclideanSq x / (L * r))
      ContDiff ℝ (⊤ : ℕ∞) η ∧
        MemLp (fun x => (η x : ℂ)) ∞ volume ∧
        (∀ j x, coordinateDerivative j η x = -2 * x j / (L * r) * η x) ∧
        (∀ j, MemLp (fun x => (coordinateDerivative j η x : ℂ)) ∞ volume) := by
    intro η
    have ha : 0 < L * r := mul_pos hL hr
    have hsmooth : ContDiff ℝ (⊤ : ℕ∞) η := by
      dsimp only [η, euclideanSq, dot]
      fun_prop
    have hnonneg (x : Vec d) : 0 ≤ euclideanSq x := by
      change 0 ≤ ∑ j : Fin d, x j * x j
      exact Finset.sum_nonneg fun j _ => mul_self_nonneg _
    have hη (x : Vec d) : η x ≤ 1 :=
      Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg
        (neg_nonpos.mpr (hnonneg x)) ha.le)
    have hb : MemLp (fun x => (η x : ℂ)) ∞ volume := by
      apply memLp_top_of_bound (Complex.continuous_ofReal.comp hsmooth.continuous).aestronglyMeasurable 1
      exact ae_of_all _ fun x => by
        change ‖(η x : ℂ)‖ ≤ 1
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        exact hη x
    have hder (j : Fin d) (x : Vec d) :
        coordinateDerivative j η x = -2 * x j / (L * r) * η x := by
      have hline := (((hasDerivAt_id (0 : ℝ)).smul_const (unitVector j)).const_add x)
      have hcomp := (hsmooth.differentiable (by simp)
        (x + (0 : ℝ) • unitVector j)).hasFDerivAt.comp_hasDerivAt 0 hline
      have hcomp' : HasDerivAt (fun s : ℝ => η (x + s • unitVector j))
          (coordinateDerivative j η x) 0 := by
        simpa only [Function.comp_def, zero_smul, add_zero, one_smul,
          coordinateDerivative, id_eq] using! hcomp
      exact hcomp'.unique (spatial_derivative x j L r)
    refine ⟨hsmooth, hb, hder, fun j => ?_⟩
    have hc : Continuous (fun x => coordinateDerivative j η x) := by
      simp_rw [hder]
      exact ((continuous_const.mul (continuous_apply j)).div_const _).mul hsmooth.continuous
    apply memLp_top_of_bound (Complex.continuous_ofReal.comp hc).aestronglyMeasurable
      (2 / (L * r) * (1 + L * r))
    refine ae_of_all _ fun x => ?_
    have hqexp : euclideanSq x * η x ≤ L * r := by
      have h := (Real.mul_exp_neg_le_exp_neg_one (euclideanSq x / (L * r))).trans
        (Real.exp_le_one_iff.mpr (by norm_num))
      have hm := mul_le_mul_of_nonneg_left h ha.le
      have he : L * r * (euclideanSq x / (L * r) *
          Real.exp (-(euclideanSq x / (L * r)))) = euclideanSq x * η x := by
        dsimp only [η]
        rw [neg_div]
        field_simp
      simpa only [he, mul_one] using hm
    have hj : x j ^ 2 ≤ euclideanSq x := by
      change x j ^ 2 ≤ ∑ k : Fin d, x k * x k
      simpa only [sq] using Finset.single_le_sum (fun k _ => mul_self_nonneg (x k))
        (Finset.mem_univ j)
    have hx : |x j| ≤ 1 + euclideanSq x := by
      nlinarith [sq_abs (x j), sq_nonneg (|x j| - 1)]
    have hprod : |x j| * η x ≤ 1 + L * r := by
      have hm := mul_le_mul_of_nonneg_right hx (show 0 ≤ η x from Real.exp_nonneg _)
      nlinarith only [hm, hqexp, hη x]
    change ‖(coordinateDerivative j η x : ℂ)‖ ≤ 2 / (L * r) * (1 + L * r)
    rw [hder, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_div, abs_mul,
      abs_of_pos ha, abs_of_pos (Real.exp_pos _)]
    norm_num only [abs_neg, show |(2 : ℝ)| = 2 by norm_num]
    calc
      2 * |x j| / (L * r) * η x = 2 / (L * r) * (|x j| * η x) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hprod (by positivity)

  obtain ⟨hs, hb, hd, hdb⟩ := admissible (d := d) (L := 2) (r := r) (by norm_num) hr
  obtain ⟨hsfull, _, hdfull, _⟩ := admissible (d := d) (L := 1) (r := r) (by norm_num) hr
  have hexp (x : Vec d) :
      Real.exp (-euclideanSq x / r) =
        Real.exp (-euclideanSq x / (2*r)) * Real.exp (-euclideanSq x / (2*r)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  let w (x : Vec d) : ℝ := Real.exp (-euclideanSq x/r)
  let dw (j : Fin d) (x : Vec d) : ℝ := -2*x j/r*w x
  let A (j : Fin d) (x : Vec d) : ℂ := (w x : ℂ) * P j x
  let D (j : Fin d) (x : Vec d) : ℂ := (dw j x : ℂ) * P j x
  let Q (x : Vec d) : ℂ := (w x : ℂ) * q x
  let B (x : Vec d) : ℂ := Q x + ∑ j, D j x
  have hA (j : Fin d) : MemLp (A j) 2 volume := by
    convert hb.fun_mul (r := 2) (hP j) using 1
    funext x
    dsimp only [A, w]
    rw [hexp, Complex.ofReal_mul]
    ring
  have hD (j : Fin d) : MemLp (D j) 2 volume := by
    convert ((hdb j).const_mul (2 : ℂ)).fun_mul (r := 2) (hP j) using 1
    funext x
    dsimp only [D, dw, w]
    rw [hd, hexp]
    push_cast
    field_simp
  have hQ : MemLp Q 2 volume := by
    convert hb.fun_mul (r := 2) hq using 1
    funext x
    dsimp only [Q, w]
    rw [hexp, Complex.ofReal_mul]
    ring
  have hB : MemLp B 2 volume := hQ.add (memLp_finsetSum _ (fun j _ => hD j))
  have hbr : HasWeakDivergence Set.univ (fun x j => (A j x).re) (fun x => (B x).re) := by
    have h := Correctors.hasWeakDivergence_mul_smooth isOpen_univ hdivre hsfull
    simp only [one_mul] at hdfull h
    simpa only [A, B, Q, D, dw, w, Complex.add_re, Complex.re_sum,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, sub_zero, one_mul,
      dot, gradient, hdfull, mul_comm] using h
  have hbi : HasWeakDivergence Set.univ (fun x j => (A j x).im) (fun x => (B x).im) := by
    have h := Correctors.hasWeakDivergence_mul_smooth isOpen_univ hdivim hsfull
    simp only [one_mul] at hdfull h
    simpa only [A, B, Q, D, dw, w, Complex.add_im, Complex.im_sum,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, add_zero, zero_add, one_mul,
      dot, gradient, hdfull, mul_comm] using h
  have hrr := Correctors.sol04_weakDivergence_test_H1 hbr hv.1
    (Lp.memLp v).re (fun j => (Lp.memLp (H j)).re) (fun j => (hA j).re) hB.re
  have hii := Correctors.sol04_weakDivergence_test_H1 hbi hv.2
    (Lp.memLp v).im (fun j => (Lp.memLp (H j)).im) (fun j => (hA j).im) hB.im
  have hri := Correctors.sol04_weakDivergence_test_H1 hbr hv.2
    (Lp.memLp v).im (fun j => (Lp.memLp (H j)).im) (fun j => (hA j).re) hB.re
  have hir := Correctors.sol04_weakDivergence_test_H1 hbi hv.1
    (Lp.memLp v).re (fun j => (Lp.memLp (H j)).re) (fun j => (hA j).im) hB.im
  have hAH : Integrable (fun x => ∑ j, A j x * H j x) volume :=
    integrable_finsetSum _ (fun j _ => (hA j).integrable_mul (Lp.memLp (H j)))
  have hBv : Integrable (fun x => B x * v x) volume := hB.integrable_mul (Lp.memLp v)
  have htest : (∫ x, ∑ j, A j x * H j x) = -(∫ x, B x * v x) := by
    apply Complex.ext
    · simp only [Complex.neg_re]
      change RCLike.re (∫ x, ∑ j, A j x * H j x) = -RCLike.re (∫ x, B x * v x)
      rw [← integral_re hAH, ← integral_re hBv]
      simp only [RCLike.re_eq_complex_re, Complex.re_sum, Complex.mul_re,
        Finset.sum_sub_distrib]
      rw [integral_sub
        (f := fun x => ∑ j, (A j x).re * (H j x).re)
        (g := fun x => ∑ j, (A j x).im * (H j x).im)
        (integrable_finsetSum Finset.univ (fun j _ => (hA j).re.integrable_mul (Lp.memLp (H j)).re))
        (integrable_finsetSum _ (fun j _ => (hA j).im.integrable_mul (Lp.memLp (H j)).im)),
        integral_sub (f := fun x => (B x).re * (v x).re)
          (g := fun x => (B x).im * (v x).im) (hB.re.integrable_mul (Lp.memLp v).re)
          (hB.im.integrable_mul (Lp.memLp v).im)]
      change (∫ x, dot (fun j => (A j x).re) (fun j => (H j x).re)) -
        (∫ x, dot (fun j => (A j x).im) (fun j => (H j x).im)) = _
      rw [hrr, hii]
      ring
    · simp only [Complex.neg_im]
      change RCLike.im (∫ x, ∑ j, A j x * H j x) = -RCLike.im (∫ x, B x * v x)
      rw [← integral_im hAH, ← integral_im hBv]
      simp only [RCLike.im_eq_complex_im, Complex.im_sum, Complex.mul_im,
        Finset.sum_add_distrib]
      rw [integral_add
        (f := fun x => ∑ j, (A j x).re * (H j x).im)
        (g := fun x => ∑ j, (A j x).im * (H j x).re)
        (integrable_finsetSum Finset.univ (fun j _ => (hA j).re.integrable_mul (Lp.memLp (H j)).im))
        (integrable_finsetSum _ (fun j _ => (hA j).im.integrable_mul (Lp.memLp (H j)).re)),
        integral_add (f := fun x => (B x).re * (v x).im)
          (g := fun x => (B x).im * (v x).re) (hB.re.integrable_mul (Lp.memLp v).im)
          (hB.im.integrable_mul (Lp.memLp v).re)]
      change (∫ x, dot (fun j => (A j x).re) (fun j => (H j x).im)) +
        (∫ x, dot (fun j => (A j x).im) (fun j => (H j x).re)) = _
      rw [hri, hir]
      ring
  have hDv : Integrable (fun x => ∑ j, D j x * v x) volume :=
    integrable_finsetSum _ (fun j _ => (hD j).integrable_mul (Lp.memLp v))
  have hsplit : (∫ x, B x * v x) = (∫ x, Q x * v x) + (∫ x, ∑ j, D j x * v x) := by
    simp only [B, add_mul, Finset.sum_mul]
    exact integral_add (hQ.integrable_mul (Lp.memLp v)) hDv
  have hrhs : (∫ x : Vec d, ∑ j,
        P j x * ((Real.exp (-euclideanSq x/r) : ℂ) * H j x +
          ((-2*x j/r*Real.exp (-euclideanSq x/r) : ℝ) : ℂ) * v x)) =
      (∫ x, ∑ j, A j x * H j x) + (∫ x, ∑ j, D j x * v x) := by
    rw [← integral_add hAH hDv]
    apply integral_congr_ae
    exact ae_of_all _ fun x => by
      change (∑ j, P j x * _) = (∑ j, A j x * H j x) + ∑ j, D j x * v x
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      dsimp only [A, D, dw, w]
      ring
  rw [hrhs]
  change (∫ x, Q x * v x) = _
  rw [hsplit] at htest
  linear_combination htest

end EinsteinFull.Blueprint
