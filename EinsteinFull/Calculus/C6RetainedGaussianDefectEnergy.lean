import EinsteinFull.Calculus.C4MovingGaussianOrbitDerivative
import EinsteinFull.Calculus.C4ComplexCaccioppoliEnergy
import EinsteinFull.Calculus.S5EnergySupport
import EinsteinRelation.Correctors.WeakPartialAddition
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation EinsteinRelation.External.AKM
private theorem retainedGaussian_spatial_derivative {d : ℕ} (x : Vec d)
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

/-- The comparison Gaussian and all of its first derivatives are bounded
smooth multipliers on the actual physical H1 graph. -/
private theorem retainedGaussian_admissible {d : ℕ} {L r : ℝ}
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
    exact hcomp'.unique (retainedGaussian_spatial_derivative x j L r)
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

/-- Subtraction in the full physical H1 graph, with the actual L2 difference. -/
private theorem retainedGraph_sub {d : ℕ}
    (u v : Lp ℂ 2 (volume : Measure (Vec d)))
    (Gu Gv : Fin d → Lp ℂ 2 (volume : Measure (Vec d)))
    (hu : IsPhysicalH1Graph volume (Or.inl rfl) u Gu)
    (hv : IsPhysicalH1Graph volume (Or.inl rfl) v Gv) :
    IsPhysicalH1Graph volume (Or.inl rfl) (u-v) (fun j => Gu j-Gv j) := by
  rw [isPhysicalH1Graph_iff_representatives volume (Or.inl rfl)
    (u-v) (fun j => Gu j-Gv j) _ _ (Lp.coeFn_sub u v)
    (fun j => Lp.coeFn_sub (Gu j) (Gv j))]
  constructor
  · intro j
    have hn := hv.1 j
    have hneg : HasWeakPartialDerivative Set.univ j
        (fun x => -(v x).re) (fun x => -(Gv j x).re) := by
      refine ⟨hn.1.neg, hn.2.1.neg, ?_⟩
      intro ψ hψ
      simpa only [neg_mul, integral_neg, neg_neg] using congrArg Neg.neg (hn.2.2 ψ hψ)
    simpa only [Pi.sub_apply, Complex.sub_re, sub_eq_add_neg, Complex.add_re, Complex.neg_re] using
      Correctors.hasWeakPartialDerivative_add (hu.1 j) hneg
  · intro j
    have hn := hv.2 j
    have hneg : HasWeakPartialDerivative Set.univ j
        (fun x => -(v x).im) (fun x => -(Gv j x).im) := by
      refine ⟨hn.1.neg, hn.2.1.neg, ?_⟩
      intro ψ hψ
      simpa only [neg_mul, integral_neg, neg_neg] using congrArg Neg.neg (hn.2.2 ψ hψ)
    simpa only [Pi.sub_apply, Complex.sub_im, sub_eq_add_neg, Complex.add_im, Complex.neg_im] using
      Correctors.hasWeakPartialDerivative_add (hu.2 j) hneg

/-- Subtracting the literal forward weak equations with one shared Gaussian
conjugate test retains the actual two coefficient fields and gradients. -/
private theorem physical_retained_gaussian_defect_test {d : ℕ}
    (a b : Vec d → Mat d) (i : Fin d) (ζ : ℂ)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume)
    (hb : ∀ j k, MemLp (fun x => (b x j k : ℂ)) ∞ volume)
    (u v g h : Lp ℂ 2 (volume : Measure (Vec d)))
    (hug : IsPhysicalComplexGeneratorPair a i ζ u g)
    (hvh : IsPhysicalComplexGeneratorPair b i ζ v h)
    {L r : ℝ} (hL : 0 < L) (hr : 0 < r) :
    let η : Vec d → ℝ := fun x => Real.exp (-euclideanSq x / (L*r))
    let D : Vec d → Fin d → ℝ := fun x j => -2*x j/(L*r)*η x
    ∃ Gu Gv : Fin d → Lp ℂ 2 (volume : Measure (Vec d)),
      IsPhysicalH1Graph volume (Or.inl rfl) u Gu ∧
      IsPhysicalH1Graph volume (Or.inl rfl) v Gv ∧
      Integrable (fun x => ∑ j, ∑ k,
          ((a x j k : ℂ)*Gu k x-(b x j k : ℂ)*Gv k x) *
            (((η x ^ 2 : ℝ) : ℂ)*star (Gu j x-Gv j x) +
              star (u x-v x)*((2*η x*D x j : ℝ) : ℂ))) ∧
      Integrable (fun x => (∑ j, ((a x j i : ℂ)*Gu j x-(b x j i : ℂ)*Gv j x)) *
          (((η x ^ 2 : ℝ) : ℂ)*star (u x-v x))) ∧
      (∫ x, (g x-h x) * (((η x ^ 2 : ℝ) : ℂ) * star (u x-v x))) =
        -(1/2 : ℂ) * (∫ x, ∑ j, ∑ k,
          ((a x j k : ℂ)*Gu k x-(b x j k : ℂ)*Gv k x) *
            (((η x ^ 2 : ℝ) : ℂ)*star (Gu j x-Gv j x) +
              star (u x-v x)*((2*η x*D x j : ℝ) : ℂ))) +
        ζ * (∫ x, (∑ j, ((a x j i : ℂ)*Gu j x-(b x j i : ℂ)*Gv j x)) *
          (((η x ^ 2 : ℝ) : ℂ)*star (u x-v x))) := by
  intro η D
  obtain ⟨Gu, hu, hwu⟩ := hug
  obtain ⟨Gv, hv, hwv⟩ := hvh
  obtain ⟨hsmooth, hbound, hder, hDbound⟩ := retainedGaussian_admissible hL hr
  obtain ⟨w, J, hw, hwr, hJr⟩ := physicalH1Graph_cutoff_test η hsmooth hbound hDbound
    (u-v) (fun j => Gu j-Gv j) (retainedGraph_sub u v Gu Gv hu hv)
  have hwval : ∀ᵐ x ∂volume, w x = ((η x ^ 2 : ℝ) : ℂ)*star (u x-v x) := by
    filter_upwards [hwr, Lp.coeFn_sub u v] with x hx hd
    rw [hx, hd, Complex.ofReal_pow]
    rfl
  have hJval : ∀ᵐ x ∂volume, ∀ j, J j x =
      ((η x ^ 2 : ℝ) : ℂ)*star (Gu j x-Gv j x) +
        star (u x-v x)*((2*η x*D x j : ℝ) : ℂ) := by
    filter_upwards [ae_all_iff.mpr hJr, Lp.coeFn_sub u v,
      ae_all_iff.mpr (fun j => Lp.coeFn_sub (Gu j) (Gv j))] with x hx hd hG j
    rw [hx j, hd, hG j, hder j x]
    dsimp only [D, η]
    simp only [Pi.sub_apply]
    push_cast
    ring
  have hT (c : Vec d → Mat d)
      (hc : ∀ j k, MemLp (fun x => (c x j k : ℂ)) ∞ volume)
      (G : Fin d → Lp ℂ 2 (volume : Measure (Vec d))) :
      Integrable (fun x => ∑ j, ∑ k, (c x j k : ℂ)*G k x*J j x) := by
    apply integrable_finsetSum
    intro j _
    apply integrable_finsetSum
    intro k _
    convert ((Lp.memLp (G k)).integrable_mul (Lp.memLp (J j))).mul_of_top_left
      (hc j k) using 1
    funext x
    simp only [Pi.mul_apply]
    ring
  have hF (c : Vec d → Mat d)
      (hc : ∀ j k, MemLp (fun x => (c x j k : ℂ)) ∞ volume)
      (G : Fin d → Lp ℂ 2 (volume : Measure (Vec d))) :
      Integrable (fun x => (∑ j, (c x j i : ℂ)*G j x)*w x) := by
    simp_rw [Finset.sum_mul]
    apply integrable_finsetSum
    intro j _
    convert ((Lp.memLp (G j)).integrable_mul (Lp.memLp w)).mul_of_top_left
      (hc j i) using 1
    funext x
    simp only [Pi.mul_apply]
    ring
  have heq := congrArg₂ (fun z z' : ℂ => z-z') (hwu w J hw) (hwv w J hw)
  have hgw : Integrable (fun x => g x*w x) := by
    convert (Lp.memLp g).integrable_mul (Lp.memLp w) using 1
  have hhw : Integrable (fun x => h x*w x) := by
    convert (Lp.memLp h).integrable_mul (Lp.memLp w) using 1
  have hleft : (∫ x, g x*w x)-(∫ x, h x*w x) =
      ∫ x, (g x-h x)*(((η x ^ 2 : ℝ) : ℂ)*star (u x-v x)) := by
    rw [← integral_sub hgw hhw]
    apply integral_congr_ae
    filter_upwards [hwval] with x hx
    rw [hx]
    ring
  have hprincipal : (∫ x, ∑ j, ∑ k, (a x j k : ℂ)*Gu k x*J j x) -
      (∫ x, ∑ j, ∑ k, (b x j k : ℂ)*Gv k x*J j x) =
      ∫ x, ∑ j, ∑ k, ((a x j k : ℂ)*Gu k x-(b x j k : ℂ)*Gv k x) *
        (((η x ^ 2 : ℝ) : ℂ)*star (Gu j x-Gv j x) +
          star (u x-v x)*((2*η x*D x j : ℝ) : ℂ)) := by
    rw [← integral_sub (hT a ha Gu) (hT b hb Gv)]
    apply integral_congr_ae
    filter_upwards [hJval] with x hx
    simp only [← Finset.sum_sub_distrib, hx, sub_mul]
  have hforce : (∫ x, (∑ j, (a x j i : ℂ)*Gu j x)*w x) -
      (∫ x, (∑ j, (b x j i : ℂ)*Gv j x)*w x) =
      ∫ x, (∑ j, ((a x j i : ℂ)*Gu j x-(b x j i : ℂ)*Gv j x)) *
        (((η x ^ 2 : ℝ) : ℂ)*star (u x-v x)) := by
    rw [← integral_sub (hF a ha Gu) (hF b hb Gv)]
    apply integral_congr_ae
    filter_upwards [hwval] with x hx
    rw [hx, Finset.sum_sub_distrib, sub_mul]
  have hTI : Integrable (fun x => ∑ j, ∑ k,
          ((a x j k : ℂ)*Gu k x-(b x j k : ℂ)*Gv k x) *
            (((η x ^ 2 : ℝ) : ℂ)*star (Gu j x-Gv j x) +
              star (u x-v x)*((2*η x*D x j : ℝ) : ℂ))) := by
    apply ((hT a ha Gu).sub (hT b hb Gv)).congr
    filter_upwards [hJval] with x hx
    simp only [Pi.sub_apply, ← Finset.sum_sub_distrib, hx, sub_mul]
  have hFI : Integrable (fun x => (∑ j, ((a x j i : ℂ)*Gu j x-(b x j i : ℂ)*Gv j x)) *
          (((η x ^ 2 : ℝ) : ℂ)*star (u x-v x))) := by
    apply ((hF a ha Gu).sub (hF b hb Gv)).congr
    filter_upwards [hwval] with x hx
    simp only [Pi.sub_apply]
    rw [hx, Finset.sum_sub_distrib, sub_mul]
  refine ⟨Gu, Gv, hu, hv, hTI, hFI, ?_⟩
  rw [hleft] at heq
  rw [← hprincipal, ← hforce]
  rw [heq]
  ring

/-- The real part of the complex matrix pairing has its Euclidean bound. -/
private theorem retained_pairing_re_bound {d : ℕ} {A : Mat d} {Λ : ℝ}
    (hA : S5Elliptic A Λ) (X Y : Fin d → ℂ) :
    |(∑ j, ∑ k, (A j k : ℂ)*Y k*star (X j)).re| ≤
      2*Λ*s5CNrm X*s5CNrm Y := by
  have he : (∑ j, ∑ k, (A j k : ℂ)*Y k*star (X j)).re =
      s5Bil A (fun j => (X j).re) (fun k => (Y k).re) +
      s5Bil A (fun j => (X j).im) (fun k => (Y k).im) := by
    simp only [s5Bil, ← Finset.sum_add_distrib, Complex.re_sum]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    simp only [mul_assoc, Complex.mul_re,
      Complex.star_def, Complex.conj_re, Complex.conj_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero]
    ring
  have hΛ : 0 ≤ Λ := le_trans zero_le_one hA.one_le
  have hr : |s5Bil A (fun j => (X j).re) (fun k => (Y k).re)| ≤
      Λ*s5CNrm X*s5CNrm Y := by
    apply (s5Bil_abs_le hA _ _).trans
    exact mul_le_mul (mul_le_mul_of_nonneg_left (s5Nrm_re_le X) hΛ)
      (s5Nrm_re_le Y) (s5Nrm_nonneg _) (mul_nonneg hΛ (s5CNrm_nonneg X))
  have hi : |s5Bil A (fun j => (X j).im) (fun k => (Y k).im)| ≤
      Λ*s5CNrm X*s5CNrm Y := by
    apply (s5Bil_abs_le hA _ _).trans
    exact mul_le_mul (mul_le_mul_of_nonneg_left (s5Nrm_im_le X) hΛ)
      (s5Nrm_im_le Y) (s5Nrm_nonneg _) (mul_nonneg hΛ (s5CNrm_nonneg X))
  rw [he]
  calc
    _ ≤ |s5Bil A (fun j => (X j).re) (fun k => (Y k).re)| +
        |s5Bil A (fun j => (X j).im) (fun k => (Y k).im)| := abs_add_le _ _
    _ ≤ _ := by linarith only [hr, hi]

/-- Young absorption with the exact principal-energy budget used below. -/
private theorem retained_young (Λ x y : ℝ) (hΛ : 0 < Λ) :
    x*y ≤ Λ⁻¹/4*x^2+Λ*y^2 := by
  have h := mul_nonneg (inv_nonneg.mpr hΛ.le) (sq_nonneg (x-2*Λ*y))
  have he : Λ⁻¹*(x-2*Λ*y)^2 = Λ⁻¹*x^2-4*x*y+4*Λ*y^2 := by
    field_simp
    ring
  rw [he] at h
  linarith only [h]

/-- The three coefficient-defect terms consume a quarter of the gradient
energy and the remaining cutoff/force budgets. This is scalar algebra. -/
private theorem retained_defect_absorb (Λ η X Y D : ℝ) (u ζ T B F : ℂ)
    (hΛ : 0 < Λ) (hη : 0 ≤ η)
    (hT : |T.re| ≤ 4*Λ*X*Y) (hB : ‖B‖ ≤ 4*Λ*D*Y) (hF : ‖F‖ ≤ 4*Λ*Y) :
    (-((η^2 : ℝ) : ℂ)*T - ((2*η : ℝ) : ℂ)*(star u*B) +
      2*ζ*(F*(((η^2 : ℝ) : ℂ)*star u))).re ≤
    Λ⁻¹/4*η^2*X^2 + 16*Λ^3*(D^2+‖ζ‖^2*η^2)*‖u‖^2 +
      (16*Λ^3+2*Λ⁻¹)*η^2*Y^2 := by
  have ht : -η^2*T.re ≤ 4*Λ*η^2*X*Y := by
    have := (neg_le_abs T.re).trans hT
    nlinarith only [mul_le_mul_of_nonneg_left this (sq_nonneg η)]
  have hb : -(2*η)*(star u*B).re ≤ 8*Λ*η*D*Y*‖u‖ := by
    have hnorm : -(star u*B).re ≤ ‖u‖*(4*Λ*D*Y) :=
      ((neg_le_abs _).trans (Complex.abs_re_le_norm _)).trans (by
        rw [norm_mul, norm_star]
        exact mul_le_mul_of_nonneg_left hB (norm_nonneg _))
    nlinarith only [mul_le_mul_of_nonneg_left hnorm (mul_nonneg (show 0 ≤ (2 : ℝ) by norm_num) hη)]
  have hf : (2*ζ*(F*(((η^2 : ℝ) : ℂ)*star u))).re ≤
      8*Λ*‖ζ‖*η^2*Y*‖u‖ := by
    calc
      _ ≤ ‖2*ζ*(F*(((η^2 : ℝ) : ℂ)*star u))‖ := Complex.re_le_norm _
      _ = 2*‖ζ‖*‖F‖*η^2*‖u‖ := by
        simp only [norm_mul, norm_star, Complex.norm_ofNat, Complex.norm_real,
          Real.norm_eq_abs, abs_of_nonneg (sq_nonneg η)]
        ring
      _ ≤ (2*‖ζ‖*(4*Λ*Y))*η^2*‖u‖ := by gcongr
      _ = _ := by ring
  have hyT := retained_young Λ (η*X) (4*Λ*η*Y) hΛ
  have hyB := retained_young Λ (2*η*Y) (4*Λ*D*‖u‖) hΛ
  have hyF := retained_young Λ (2*η*Y) (4*Λ*‖ζ‖*η*‖u‖) hΛ
  have he : (-((η^2 : ℝ) : ℂ)*T - ((2*η : ℝ) : ℂ)*(star u*B) +
      2*ζ*(F*(((η^2 : ℝ) : ℂ)*star u))).re =
      -η^2*T.re-(2*η)*(star u*B).re +
        (2*ζ*(F*(((η^2 : ℝ) : ℂ)*star u))).re := by
    simp only [Complex.add_re, Complex.sub_re, neg_mul, Complex.neg_re,
      Complex.re_ofReal_mul]
  rw [he]
  nlinarith only [ht, hb, hf, hyT, hyB, hyF]

/-- Pointwise comparison with the full coefficient defect. The two Gaussian
cutoff costs are absorbed by the literal moving-weight derivative. -/
private theorem retained_gaussian_defect_pointwise {d : ℕ} {A B : Mat d} {Λ : ℝ}
    (hA : S5Elliptic A Λ) (hB : S5Elliptic B Λ)
    (x : Vec d) (X Y : Fin d → ℂ) (u : ℂ) (i : Fin d) (ζ : ℂ)
    {L r : ℝ} (hL : 64*Λ^3 ≤ L) (hr : 0 < r) :
    let η := Real.exp (-euclideanSq x/(L*r))
    let D : Fin d → ℝ := fun j => -2*x j/(L*r)*η
    let W := -2*euclideanSq x/(L*r^2)*η^2
    let J : Fin d → ℂ := fun j => ((η^2 : ℝ) : ℂ)*star (X j) +
      star u*((2*η*D j : ℝ) : ℂ)
    2*(-(1/2 : ℂ)*(∑ j, ∑ k,
        ((A j k : ℂ)*X k+((A j k : ℂ)-(B j k : ℂ))*Y k)*J j) +
      ζ*((∑ j, ((A j i : ℂ)*X j+((A j i : ℂ)-(B j i : ℂ))*Y j))*
        (((η^2 : ℝ) : ℂ)*star u))).re + W*‖u‖^2 ≤
      -(Λ⁻¹/4)*η^2*(∑ j, ‖X j‖^2) +
        32*Λ^3*‖ζ‖^2*η^2*‖u‖^2 +
        (16*Λ^3+2*Λ⁻¹)*η^2*(∑ j, ‖Y j‖^2) := by
  intro η D W J
  let T := (∑ j, ∑ k, (A j k : ℂ)*Y k*star (X j)) -
    (∑ j, ∑ k, (B j k : ℂ)*Y k*star (X j))
  let K := (∑ j, ∑ k, (D j : ℂ)*(A j k : ℂ)*Y k) -
    (∑ j, ∑ k, (D j : ℂ)*(B j k : ℂ)*Y k)
  let F := (∑ j, (A j i : ℂ)*Y j) - (∑ j, (B j i : ℂ)*Y j)
  have hT : |T.re| ≤ 4*Λ*s5CNrm X*s5CNrm Y := by
    dsimp only [T]
    rw [Complex.sub_re]
    exact (abs_sub _ _).trans (by
      linarith only [retained_pairing_re_bound hA X Y, retained_pairing_re_bound hB X Y])
  have hK : ‖K‖ ≤ 4*Λ*s5Nrm D*s5CNrm Y := by
    exact (norm_sub_le _ _).trans (by
      linarith only [s5_cbil_norm_le hA D Y, s5_cbil_norm_le hB D Y])
  have hF : ‖F‖ ≤ 4*Λ*s5CNrm Y := by
    exact (norm_sub_le _ _).trans (by
      linarith only [s5_row_norm_le hA i Y, s5_row_norm_le hB i Y])
  have hΛ : 0 < Λ := lt_of_lt_of_le zero_lt_one hA.one_le
  have hLp : 0 < L := lt_of_lt_of_le (by positivity) hL
  have hq : 0 ≤ euclideanSq x := by
    change 0 ≤ ∑ j : Fin d, x j*x j
    exact Finset.sum_nonneg fun j _ => mul_self_nonneg _
  have hD : s5Nrm D^2 = 4*euclideanSq x/(L^2*r^2)*η^2 := by
    rw [s5Nrm_sq]
    simp only [D, euclideanSq, dot, Finset.sum_mul, Finset.mul_sum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j _
    field_simp
    ring
  have habsorb : 32*Λ^3*s5Nrm D^2+W ≤ 0 := by
    rw [hD]
    have he : 32*Λ^3*(4*euclideanSq x/(L^2*r^2)*η^2)+W =
        (128*Λ^3-2*L)*(euclideanSq x*η^2/(L^2*r^2)) := by
      dsimp only [W]
      field_simp
      ring
    rw [he]
    exact mul_nonpos_of_nonpos_of_nonneg (by linarith only [hL]) (by positivity)
  let M := -(1/2 : ℂ)*(∑ j, ∑ k, (A j k : ℂ)*X k*J j) +
    ζ*((∑ j, (A j i : ℂ)*X j)*(((η^2 : ℝ) : ℂ)*star u))
  let E := -((η^2 : ℝ) : ℂ)*T - ((2*η : ℝ) : ℂ)*(star u*K) +
    2*ζ*(F*(((η^2 : ℝ) : ℂ)*star u))
  have hbase := complexForced_cutoff_coercive hA X u D η i ζ
  change M.re ≤ _ at hbase
  have herr := retained_defect_absorb Λ η (s5CNrm X) (s5CNrm Y) (s5Nrm D)
    u ζ T K F hΛ (Real.exp_nonneg _) hT hK hF
  change E.re ≤ _ at herr
  have heprincipal : (∑ j, ∑ k,
        ((A j k : ℂ)*X k+((A j k : ℂ)-(B j k : ℂ))*Y k)*J j) =
      (∑ j, ∑ k, (A j k : ℂ)*X k*J j) + ((η^2 : ℝ) : ℂ)*T +
        ((2*η : ℝ) : ℂ)*(star u*K) := by
    have hjk (j k : Fin d) :
        ((A j k : ℂ)*X k+((A j k : ℂ)-(B j k : ℂ))*Y k)*J j =
        (A j k : ℂ)*X k*J j +
          ((η^2 : ℝ) : ℂ)*((A j k : ℂ)*Y k*star (X j)-(B j k : ℂ)*Y k*star (X j)) +
          ((2*η : ℝ) : ℂ)*star u*((D j : ℂ)*(A j k : ℂ)*Y k-
            (D j : ℂ)*(B j k : ℂ)*Y k) := by
      dsimp only [J]
      push_cast
      ring
    simp only [hjk, Finset.sum_add_distrib, ← Finset.mul_sum,
      Finset.sum_sub_distrib, T, K]
    ring
  have heforce : (∑ j, ((A j i : ℂ)*X j+((A j i : ℂ)-(B j i : ℂ))*Y j)) =
      (∑ j, (A j i : ℂ)*X j)+F := by
    simp only [F, sub_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have he : 2*(-(1/2 : ℂ)*(∑ j, ∑ k,
        ((A j k : ℂ)*X k+((A j k : ℂ)-(B j k : ℂ))*Y k)*J j) +
      ζ*((∑ j, ((A j i : ℂ)*X j+((A j i : ℂ)-(B j i : ℂ))*Y j))*
        (((η^2 : ℝ) : ℂ)*star u))) = 2*M+E := by
    rw [heprincipal, heforce]
    dsimp only [M, E]
    ring
  have her : 2*(-(1/2 : ℂ)*(∑ j, ∑ k,
        ((A j k : ℂ)*X k+((A j k : ℂ)-(B j k : ℂ))*Y k)*J j) +
      ζ*((∑ j, ((A j i : ℂ)*X j+((A j i : ℂ)-(B j i : ℂ))*Y j))*
        (((η^2 : ℝ) : ℂ)*star u))).re = 2*M.re+E.re := by
    have hre (z : ℂ) : ((2 : ℂ)*z).re = 2*z.re := Complex.re_ofReal_mul 2 z
    simpa only [Complex.add_re, hre] using congrArg Complex.re he
  rw [her]
  have hNX : s5CNrm X^2 = ∑ j, ‖X j‖^2 :=
    Real.sq_sqrt (Finset.sum_nonneg fun j _ => sq_nonneg _)
  have hNY : s5CNrm Y^2 = ∑ j, ‖Y j‖^2 :=
    Real.sq_sqrt (Finset.sum_nonneg fun j _ => sq_nonneg _)
  rw [hNX, hNY] at herr
  have hw := mul_nonpos_of_nonpos_of_nonneg habsorb (sq_nonneg ‖u‖)
  nlinarith only [hbase, herr, hw]

/-- Gaussian weighted energy for the difference of two physical generators,
with the coefficient defect confined to the exterior of their agreement ball. -/
theorem physical_retained_gaussian_defect_energy
    (d : ℕ) (Λ : ℝ) (hΛ : 1 ≤ Λ) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (a b : Vec d → Mat d) (i : Fin d) (ζ : ℂ),
      (∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume) →
      (∀ j k, MemLp (fun x => (b x j k : ℂ)) ∞ volume) →
      (∀ᵐ x ∂volume, S5Elliptic (a x) Λ) →
      (∀ᵐ x ∂volume, S5Elliptic (b x) Λ) →
      ∀ (R L r : ℝ), 0 < R → 64 * Λ ^ 3 ≤ L → 0 < r →
      (∀ᵐ x ∂volume, euclideanNorm x < R → a x = b x) →
      ∀ (u v g h : Lp ℂ 2 (volume : Measure (Vec d))),
      IsPhysicalComplexGeneratorPair a i ζ u g →
      IsPhysicalComplexGeneratorPair b i ζ v h →
      let η : Vec d → ℝ := fun x => Real.exp (-euclideanSq x / (L*r))
      let W : Vec d → ℝ := fun x => -2 * euclideanSq x / (L*r^2) * η x ^ 2
      ∃ Gu Gv : Fin d → Lp ℂ 2 (volume : Measure (Vec d)),
        IsPhysicalH1Graph volume (Or.inl rfl) u Gu ∧
        IsPhysicalH1Graph volume (Or.inl rfl) v Gv ∧
        (Λ⁻¹ / 4) * (∫ x, η x ^ 2 * ∑ j, ‖Gu j x - Gv j x‖ ^ 2) ≤
          -2 * (∫ x, (g x-h x) * (((η x ^ 2 : ℝ) : ℂ) * star (u x-v x))).re +
          32 * Λ ^ 3 * ‖ζ‖ ^ 2 * (∫ x, η x ^ 2 * ‖u x-v x‖ ^ 2) -
          (∫ x, W x * ‖u x-v x‖ ^ 2) +
          C * (∫ x in {x : Vec d | R ≤ euclideanNorm x}, η x ^ 2 *
            ((∑ j, ‖Gv j x‖ ^ 2) + (1+‖ζ‖ ^ 2) * ‖v x‖ ^ 2)) := by
  have hΛp : 0 < Λ := lt_of_lt_of_le zero_lt_one hΛ
  let C : ℝ := 16*Λ^3+2*Λ⁻¹+1
  have hC : 1 ≤ C := by
    dsimp only [C]
    have hp : 0 ≤ 16*Λ^3+2*Λ⁻¹ := by positivity
    linarith only [hp]
  have hC0 : 16*Λ^3+2*Λ⁻¹ ≤ C := by dsimp only [C]; linarith
  refine ⟨C, hC, ?_⟩
  intro a b i ζ ha hb hA hB R L r _hR hL hr hab u v g h hug hvh η W
  have hLp : 0 < L := lt_of_lt_of_le (by positivity) hL
  have hden : 0 < L*r := mul_pos hLp hr
  let D : Vec d → Fin d → ℝ := fun x j => -2*x j/(L*r)*η x
  obtain ⟨Gu, Gv, hu, hv, hTI, hFI, hweak⟩ :=
    physical_retained_gaussian_defect_test a b i ζ ha hb u v g h hug hvh hLp hr
  let T : Vec d → ℂ := fun x => ∑ j, ∑ k,
    ((a x j k : ℂ)*Gu k x-(b x j k : ℂ)*Gv k x) *
      (((η x^2 : ℝ) : ℂ)*star (Gu j x-Gv j x) +
        star (u x-v x)*((2*η x*D x j : ℝ) : ℂ))
  let F : Vec d → ℂ := fun x =>
    (∑ j, ((a x j i : ℂ)*Gu j x-(b x j i : ℂ)*Gv j x)) *
      (((η x^2 : ℝ) : ℂ)*star (u x-v x))
  let M : Vec d → ℂ := fun x => -(1/2 : ℂ)*T x+ζ*F x
  change Integrable T at hTI
  change Integrable F at hFI
  have hM : Integrable M := (hTI.const_mul _).add (hFI.const_mul _)
  have hMi : (∫ x, M x) =
      ∫ x, (g x-h x)*(((η x^2 : ℝ) : ℂ)*star (u x-v x)) := by
    rw [show (∫ x, M x) = -(1/2 : ℂ)*(∫ x, T x)+ζ*(∫ x, F x) by
      rw [integral_add (hTI.const_mul _) (hFI.const_mul _),
        integral_const_mul, integral_const_mul]]
    exact hweak.symm
  obtain ⟨hsmooth, _, _, _⟩ := retainedGaussian_admissible hLp hr
  have hq (x : Vec d) : 0 ≤ euclideanSq x := by
    change 0 ≤ ∑ j : Fin d, x j*x j
    exact Finset.sum_nonneg fun j _ => mul_self_nonneg _
  have hη (x : Vec d) : 0 ≤ η x ∧ η x ≤ 1 :=
    ⟨Real.exp_nonneg _, Real.exp_le_one_iff.mpr
      (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (hq x)) hden.le)⟩
  have hηsq : MemLp (fun x => η x^2) ∞ volume := by
    apply memLp_top_of_bound (hsmooth.continuous.pow 2).aestronglyMeasurable 1
    refine ae_of_all _ fun x => ?_
    change ‖η x^2‖ ≤ 1
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith [(hη x).1, (hη x).2,
      mul_nonneg (sub_nonneg.mpr (hη x).2) (hη x).1]
  have hW : MemLp W ∞ volume := by
    have hc : Continuous W := by
      dsimp only [W, euclideanSq, dot, η]
      fun_prop
    apply memLp_top_of_bound hc.aestronglyMeasurable (2 / r)
    refine ae_of_all _ fun x => ?_
    have hqη : euclideanSq x * η x ≤ L * r := by
      have h := (Real.mul_exp_neg_le_exp_neg_one (euclideanSq x / (L * r))).trans
        (Real.exp_le_one_iff.mpr (by norm_num))
      have hm := mul_le_mul_of_nonneg_left h hden.le
      have he : L * r * (euclideanSq x / (L * r) *
          Real.exp (-(euclideanSq x / (L * r)))) = euclideanSq x * η x := by
        dsimp only [η]
        rw [neg_div]
        field_simp
      simpa only [he, mul_one] using hm
    have hqηsq : euclideanSq x * η x ^ 2 ≤ L * r := by
      have hm := mul_le_mul_of_nonneg_left (hη x).2
        (mul_nonneg (hq x) (hη x).1)
      nlinarith only [hm, hqη]
    have hwneg : W x ≤ 0 := by
      dsimp only [W]
      exact mul_nonpos_of_nonpos_of_nonneg
        (div_nonpos_of_nonpos_of_nonneg (by nlinarith [hq x]) (by positivity))
        (sq_nonneg _)
    rw [Real.norm_eq_abs, abs_of_nonpos hwneg]
    have he : -W x = (2 / (L * r ^ 2)) * (euclideanSq x * η x ^ 2) := by
      dsimp only [W]
      ring
    rw [he]
    calc
      _ ≤ (2 / (L * r ^ 2)) * (L * r) :=
        mul_le_mul_of_nonneg_left hqηsq (by positivity)
      _ = 2 / r := by field_simp
  have hUN : Integrable (fun x => ‖u x-v x‖^2) := by
    convert ((Lp.memLp u).sub (Lp.memLp v)).norm.integrable_sq using 1
  have hGN : Integrable (fun x => ∑ j, ‖Gu j x-Gv j x‖^2) := by
    apply integrable_finsetSum
    intro j _
    convert ((Lp.memLp (Gu j)).sub (Lp.memLp (Gv j))).norm.integrable_sq using 1
  have hGNv : Integrable (fun x => ∑ j, ‖Gv j x‖^2) :=
    integrable_finsetSum _ fun j _ => (Lp.memLp (Gv j)).norm.integrable_sq
  have hηG : Integrable (fun x => η x^2*(∑ j, ‖Gu j x-Gv j x‖^2)) := by
    convert hGN.mul_of_top_left hηsq using 1
    funext x
    simp only [Pi.mul_apply]
    ring
  have hηU : Integrable (fun x => η x^2*‖u x-v x‖^2) := by
    convert hUN.mul_of_top_left hηsq using 1
    funext x
    simp only [Pi.mul_apply]
    ring
  have hWU : Integrable (fun x => W x*‖u x-v x‖^2) := by
    convert hUN.mul_of_top_left hW using 1
    funext x
    simp only [Pi.mul_apply]
    ring
  have hηGv : Integrable (fun x => η x^2*(∑ j, ‖Gv j x‖^2)) := by
    convert hGNv.mul_of_top_left hηsq using 1
    funext x
    simp only [Pi.mul_apply]
    ring
  have hηV : Integrable (fun x => η x^2*‖v x‖^2) := by
    convert (Lp.memLp v).norm.integrable_sq.mul_of_top_left hηsq using 1
    funext x
    simp only [Pi.mul_apply]
    ring
  let Q : Vec d → ℝ := fun x => η x^2*((∑ j, ‖Gv j x‖^2)+(1+‖ζ‖^2)*‖v x‖^2)
  let S : Set (Vec d) := {x | R ≤ euclideanNorm x}
  have hQ : Integrable Q := by
    convert hηGv.add (hηV.const_mul (1+‖ζ‖^2)) using 1
    funext x
    dsimp only [Q, Pi.add_apply]
    ring
  have hS : MeasurableSet S := by
    have hc : Continuous (fun x : Vec d => euclideanNorm x) := by
      unfold euclideanNorm euclideanSq dot
      fun_prop
    exact measurableSet_le measurable_const hc.measurable
  have hSQ : Integrable (S.indicator Q) := hQ.indicator hS
  have hpoint : ∀ᵐ x ∂volume,
      2*(M x).re+W x*‖u x-v x‖^2 ≤
        -(Λ⁻¹/4)*(η x^2*(∑ j, ‖Gu j x-Gv j x‖^2)) +
        (32*Λ^3*‖ζ‖^2)*(η x^2*‖u x-v x‖^2)+C*S.indicator Q x := by
    filter_upwards [hA, hB, hab] with x hxA hxB hxeq
    have hmat (j k : Fin d) :
        (a x j k : ℂ)*Gu k x-(b x j k : ℂ)*Gv k x =
        (a x j k : ℂ)*(Gu k x-Gv k x)+
          ((a x j k : ℂ)-(b x j k : ℂ))*Gv k x := by ring
    have hrow (j : Fin d) :
        (a x j i : ℂ)*Gu j x-(b x j i : ℂ)*Gv j x =
        (a x j i : ℂ)*(Gu j x-Gv j x)+
          ((a x j i : ℂ)-(b x j i : ℂ))*Gv j x := by ring
    by_cases hxS : x ∈ S
    · have hp : 2*(M x).re+W x*‖u x-v x‖^2 ≤
          -(Λ⁻¹/4)*η x^2*(∑ j, ‖Gu j x-Gv j x‖^2) +
            32*Λ^3*‖ζ‖^2*η x^2*‖u x-v x‖^2 +
            (16*Λ^3+2*Λ⁻¹)*η x^2*(∑ j, ‖Gv j x‖^2) := by
        dsimp only [M, T, F]
        simp only [hmat, hrow]
        exact retained_gaussian_defect_pointwise hxA hxB x
          (fun j => Gu j x-Gv j x) (fun j => Gv j x) (u x-v x) i ζ hL hr
      have htail : (16*Λ^3+2*Λ⁻¹)*η x^2*(∑ j, ‖Gv j x‖^2) ≤ C*Q x := by
        calc
          _ ≤ C*(η x^2*(∑ j, ‖Gv j x‖^2)) := by
            rw [mul_assoc]
            exact mul_le_mul_of_nonneg_right hC0
              (mul_nonneg (sq_nonneg (η x)) (Finset.sum_nonneg fun j _ => sq_nonneg ‖Gv j x‖))
          _ ≤ C*Q x := by
            apply mul_le_mul_of_nonneg_left _ (le_trans zero_le_one hC)
            dsimp only [Q]
            have := mul_nonneg (sq_nonneg (η x))
              (mul_nonneg (show 0 ≤ 1+‖ζ‖^2 by positivity) (sq_nonneg ‖v x‖))
            nlinarith only [this]
      rw [Set.indicator_of_mem hxS]
      nlinarith only [hp, htail]
    · have heq : a x = b x := hxeq (lt_of_not_ge hxS)
      have hp := retained_gaussian_defect_pointwise hxA hxA x
        (fun j => Gu j x-Gv j x) (fun _ => 0) (u x-v x) i ζ hL hr
      simp only [mul_zero, add_zero, norm_zero, zero_pow (by decide : 2 ≠ 0),
        Finset.sum_const_zero] at hp
      rw [Set.indicator_of_notMem hxS, mul_zero, add_zero]
      dsimp only [M, T, F]
      rw [← heq]
      simp only [← mul_sub]
      simpa only [η, W, D, mul_assoc] using hp
  have hMr : Integrable (fun x => (M x).re) := hM.re
  have hReal : (∫ x, (M x).re) = (∫ x, M x).re := integral_re hM
  have hint := integral_mono_ae ((hMr.const_mul 2).add hWU)
    (((hηG.const_mul (-(Λ⁻¹/4))).add
      (hηU.const_mul (32*Λ^3*‖ζ‖^2))).add (hSQ.const_mul C)) hpoint
  simp only [Pi.add_apply] at hint
  have hRight := integral_add ((hηG.const_mul (-(Λ⁻¹/4))).add
    (hηU.const_mul (32*Λ^3*‖ζ‖^2))) (hSQ.const_mul C)
  have hInner := integral_add (hηG.const_mul (-(Λ⁻¹/4)))
    (hηU.const_mul (32*Λ^3*‖ζ‖^2))
  simp only [Pi.add_apply] at hRight hInner
  rw [integral_add (hMr.const_mul 2) hWU, integral_const_mul,
    hReal, hMi,
    hRight, hInner,
    integral_const_mul, integral_const_mul, integral_const_mul,
    integral_indicator hS] at hint
  refine ⟨Gu, Gv, hu, hv, ?_⟩
  linarith only [hint]

end EinsteinFull.Blueprint
