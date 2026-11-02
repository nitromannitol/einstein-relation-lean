import EinsteinFull.Work.W6.PhysicalLocalTestingSupport
import EinsteinFull.Calculus.C6RetainedGaussianDefectEnergy
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation EinsteinRelation.External.AKM
theorem physical_gaussian_local_h1_realization
    {d : ℕ} (r : ℝ) (hr : 0 < r)
    (f : Vec d → ℂ) (G : Fin d → Vec d → ℂ)
    (hre : ∀ j, HasWeakPartialDerivative Set.univ j (fun x => (f x).re)
      (fun x => (G j x).re))
    (him : ∀ j, HasWeakPartialDerivative Set.univ j (fun x => (f x).im)
      (fun x => (G j x).im))
    (hf : MemLp (fun x => (Real.exp (-euclideanSq x / (2*r)) : ℂ) * f x) 2 volume)
    (hG : ∀ j, MemLp (fun x => (Real.exp (-euclideanSq x / (2*r)) : ℂ) * G j x) 2 volume) :
    ∃ (u : Lp ℂ 2 (volume : Measure (Vec d)))
      (H : Fin d → Lp ℂ 2 (volume : Measure (Vec d))),
      IsPhysicalH1Graph volume (Or.inl rfl) u H ∧
      (u : Vec d → ℂ) =ᵐ[volume]
        (fun x => (Real.exp (-euclideanSq x/r) : ℂ) * f x) ∧
      ∀ j, (H j : Vec d → ℂ) =ᵐ[volume]
        (fun x => (Real.exp (-euclideanSq x/r) : ℂ) * G j x +
          ((-2*x j/r*Real.exp (-euclideanSq x/r) : ℝ) : ℂ) * f x) := by
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
  have huf : MemLp (fun x => (Real.exp (-euclideanSq x/r) : ℂ) * f x) 2 volume := by
    convert hb.fun_mul (r := 2) hf using 1
    funext x
    rw [hexp, Complex.ofReal_mul]
    ring
  have hgrad (j : Fin d) : MemLp (fun x =>
      (Real.exp (-euclideanSq x/r) : ℂ) * G j x +
      ((-2*x j/r*Real.exp (-euclideanSq x/r) : ℝ) : ℂ) * f x) 2 volume := by
    have hfirst : MemLp (fun x => (Real.exp (-euclideanSq x/r) : ℂ) * G j x) 2 volume := by
      convert hb.fun_mul (r := 2) (hG j) using 1
      funext x
      rw [hexp, Complex.ofReal_mul]
      ring
    apply hfirst.add
    convert ((hdb j).const_mul (2 : ℂ)).fun_mul (r := 2) hf using 1
    funext x
    rw [hd, hexp]
    push_cast
    field_simp
  let u := huf.toLp _
  let H (j : Fin d) := (hgrad j).toLp _
  refine ⟨u, H, ?_, huf.coeFn_toLp, fun j => (hgrad j).coeFn_toLp⟩
  rw [isPhysicalH1Graph_iff_representatives volume (Or.inl rfl) u H _ _
    huf.coeFn_toLp (fun j => (hgrad j).coeFn_toLp)]
  constructor
  · intro j
    have h := Correctors.hasWeakPartialDerivative_mul_smooth isOpen_univ j (hre j) hsfull
    simp only [one_mul] at hdfull h
    simpa only [Complex.mul_re, Complex.add_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, mul_zero, sub_zero, hdfull, mul_comm] using h
  · intro j
    have h := Correctors.hasWeakPartialDerivative_mul_smooth isOpen_univ j (him j) hsfull
    simp only [one_mul] at hdfull h
    simpa only [Complex.mul_im, Complex.add_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, mul_zero, add_zero, zero_add, hdfull, mul_comm] using h

end EinsteinFull.Blueprint
