import EinsteinFull.Calculus.C6GaussianLocalDivergenceTesting
import EinsteinFull.Calculus.C4ComplexCaccioppoliEnergy
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation EinsteinRelation.External.AKM

private theorem comparison_gaussian_spatial_derivative {d : ℕ} (x : Vec d)
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
private theorem comparison_gaussian_admissible {d : ℕ} {L r : ℝ}
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
    exact hcomp'.unique (comparison_gaussian_spatial_derivative x j L r)
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

/-- The time derivative of the Gaussian absorbs the full cutoff-gradient
error in the forced energy test. A positive gradient dissipation remains.
This is pointwise and applies to both actual and retained physical fields. -/

private theorem comparison_gaussian_coercive {d : ℕ}
    {A : Fin d → Fin d → ℝ} {Λ : ℝ} (hA : S5Elliptic A Λ)
    (x : Vec d) (X : Fin d → ℂ) (u : ℂ) (i : Fin d) (ζ : ℂ)
    {L r : ℝ} (hL : 32 * Λ ^ 3 ≤ L) (hr : 0 < r) :
    let η := Real.exp (-euclideanSq x / (L * r))
    let D : Fin d → ℝ := fun j => -2 * x j / (L * r) * η
    let W := -2 * euclideanSq x / (L * r ^ 2) * η ^ 2
    2 * (-(1 / 2 : ℂ) * (∑ j, ∑ k, (A j k : ℂ) * X k *
        (((η ^ 2 : ℝ) : ℂ) * star (X j) +
          star u * ((2 * η * D j : ℝ) : ℂ))) +
      ζ * ((∑ j, (A j i : ℂ) * X j) * (((η ^ 2 : ℝ) : ℂ) * star u))).re +
        W * ‖u‖ ^ 2 ≤
      -(Λ⁻¹ / 2) * η ^ 2 * (∑ j, ‖X j‖ ^ 2) +
        16 * Λ ^ 3 * ‖ζ‖ ^ 2 * η ^ 2 * ‖u‖ ^ 2 := by
  intro η D W
  have hΛ : 0 < Λ := lt_of_lt_of_le zero_lt_one hA.one_le
  have hLp : 0 < L := lt_of_lt_of_le (by positivity) hL
  have hL0 : L ≠ 0 := ne_of_gt hLp
  have hr0 : r ≠ 0 := ne_of_gt hr
  have hsq : 0 ≤ euclideanSq x := by
    change 0 ≤ ∑ j : Fin d, x j * x j
    exact Finset.sum_nonneg fun j _ => mul_self_nonneg _
  have hD : s5Nrm D ^ 2 = 4 * euclideanSq x / (L ^ 2 * r ^ 2) * η ^ 2 := by
    rw [s5Nrm_sq]
    simp only [D, euclideanSq, dot, Finset.sum_mul, Finset.mul_sum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j _
    field_simp
    ring
  have habsorb : 16 * Λ ^ 3 * s5Nrm D ^ 2 + W ≤ 0 := by
    rw [hD]
    have he : 16 * Λ ^ 3 * (4 * euclideanSq x / (L ^ 2 * r ^ 2) * η ^ 2) + W =
        (64 * Λ ^ 3 - 2 * L) * (euclideanSq x * η ^ 2 / (L ^ 2 * r ^ 2)) := by
      dsimp only [W]
      field_simp
      ring
    rw [he]
    exact mul_nonpos_of_nonpos_of_nonneg (by linarith only [hL]) (by positivity)
  have h := complexForced_cutoff_coercive hA X u D η i ζ
  have hw := mul_nonpos_of_nonpos_of_nonneg habsorb (sq_nonneg ‖u‖)
  nlinarith only [h, hw]


private theorem weighted_two_mul_le (c x y : ℝ) (hc : 0 < c) :
    2 * x * y ≤ c * x ^ 2 + c⁻¹ * y ^ 2 := by
  have h := mul_nonneg (inv_pos.mpr hc).le (sq_nonneg (c * x - y))
  have he : c⁻¹ * (c * x - y) ^ 2 = c * x ^ 2 - 2 * x * y + c⁻¹ * y ^ 2 := by
    field_simp
    ring
  rw [he] at h
  linarith only [h]

/-- The divergence source is tested against the literal conjugate cutoff
 gradient. Both its principal and cutoff contributions are retained. -/
private theorem divergence_source_cutoff_bound {d : ℕ}
    (F X : Fin d → ℂ) (u : ℂ) (D : Fin d → ℝ) {η Λ L : ℝ}
    (hη : 0 ≤ η) (hΛ : 0 < Λ) (hL : 0 < L) :
    2 * (∑ j, F j * ((((η ^ 2 : ℝ) : ℂ) * star (X j)) +
      star u * ((2 * η * D j : ℝ) : ℂ))).re ≤
      (Λ⁻¹ / 4) * η ^ 2 * (∑ j, ‖X j‖ ^ 2) +
        (4 * Λ + 16 / L) * η ^ 2 * (∑ j, ‖F j‖ ^ 2) +
        (L / 4) * (∑ j, D j ^ 2) * ‖u‖ ^ 2 := by
  have hj (j : Fin d) :
      2 * (F j * ((((η ^ 2 : ℝ) : ℂ) * star (X j)) +
        star u * ((2 * η * D j : ℝ) : ℂ))).re ≤
      (Λ⁻¹ / 4) * η ^ 2 * ‖X j‖ ^ 2 +
        (4 * Λ + 16 / L) * η ^ 2 * ‖F j‖ ^ 2 +
        (L / 4) * D j ^ 2 * ‖u‖ ^ 2 := by
    have hn : (F j * ((((η ^ 2 : ℝ) : ℂ) * star (X j)) +
        star u * ((2 * η * D j : ℝ) : ℂ))).re ≤
        ‖F j‖ * (η ^ 2 * ‖X j‖ + ‖u‖ * (2 * η * |D j|)) := by
      apply (Complex.re_le_norm _).trans
      rw [norm_mul]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      refine (norm_add_le _ _).trans ?_
      simp only [norm_mul, norm_star, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (sq_nonneg η), abs_of_nonneg hη, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      exact le_rfl
    have hy₁ := weighted_two_mul_le (Λ⁻¹ / 4) (η * ‖X j‖) (η * ‖F j‖) (by positivity)
    have hi₁ : (Λ⁻¹ / 4)⁻¹ = 4 * Λ := by field_simp
    rw [hi₁] at hy₁
    have hy₂ := weighted_two_mul_le (L / 4) (|D j| * ‖u‖) (2 * η * ‖F j‖) (by positivity)
    have hi₂ : (L / 4)⁻¹ = 4 / L := by field_simp
    rw [hi₂] at hy₂
    simp only [mul_pow, sq_abs] at hy₁ hy₂
    ring_nf at hn hy₁ hy₂ ⊢
    linarith only [hn, hy₁, hy₂]
  have hs := Finset.sum_le_sum fun j (_ : j ∈ (Finset.univ : Finset (Fin d))) => hj j
  simpa only [← Complex.reCLM_apply, map_sum, Finset.mul_sum, Finset.sum_mul,
    Finset.sum_add_distrib] using hs

/-- A divergence forcing term is absorbed using half the moving Gaussian
 decay, leaving a quarter of the gradient coercivity. -/
private theorem comparison_gaussian_divergence_coercive {d : ℕ}
    {A : Fin d → Fin d → ℝ} {Λ : ℝ} (hA : S5Elliptic A Λ)
    (x : Vec d) (X F : Fin d → ℂ) (u : ℂ) (i : Fin d) (ζ : ℂ)
    {L r : ℝ} (hL : 64 * Λ ^ 3 ≤ L) (hr : 0 < r) :
    let η := Real.exp (-euclideanSq x / (L * r))
    let D : Fin d → ℝ := fun j => -2 * x j / (L * r) * η
    let W := -2 * euclideanSq x / (L * r ^ 2) * η ^ 2
    2 * (-(1 / 2 : ℂ) * (∑ j, ∑ k, (A j k : ℂ) * X k *
        (((η ^ 2 : ℝ) : ℂ) * star (X j) + star u * ((2 * η * D j : ℝ) : ℂ))) +
      ζ * ((∑ j, (A j i : ℂ) * X j) * (((η ^ 2 : ℝ) : ℂ) * star u)) +
      (∑ j, F j * ((((η ^ 2 : ℝ) : ℂ) * star (X j)) +
        star u * ((2 * η * D j : ℝ) : ℂ)))).re + W * ‖u‖ ^ 2 ≤
      -(Λ⁻¹ / 4) * η ^ 2 * (∑ j, ‖X j‖ ^ 2) +
        16 * Λ ^ 3 * ‖ζ‖ ^ 2 * η ^ 2 * ‖u‖ ^ 2 +
        (4 * Λ + 16 / L) * η ^ 2 * (∑ j, ‖F j‖ ^ 2) := by
  intro η D W
  have hΛ : 0 < Λ := lt_of_lt_of_le zero_lt_one hA.one_le
  have hLp : 0 < L := lt_of_lt_of_le (by positivity) hL
  have hb := comparison_gaussian_coercive hA x X u i ζ
    (L := L / 2) (r := 2 * r) (by linarith only [hL]) (by positivity)
  have he₁ : L / 2 * (2 * r) = L * r := by ring
  have he₂ : L / 2 * (2 * r) ^ 2 = 2 * (L * r ^ 2) := by ring
  dsimp only at hb
  rw [he₁, he₂] at hb
  have hW : -2 * euclideanSq x / (2 * (L * r ^ 2)) * η ^ 2 = W / 2 := by
    dsimp only [W]
    ring
  change _ + (-2 * euclideanSq x / (2 * (L * r ^ 2)) * η ^ 2) * ‖u‖ ^ 2 ≤ _ at hb
  rw [hW] at hb
  have hDs : (∑ j, D j ^ 2) = 4 * euclideanSq x / (L ^ 2 * r ^ 2) * η ^ 2 := by
    simp only [D, euclideanSq, dot, Finset.sum_mul, Finset.mul_sum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j _
    field_simp
    ring
  have hD : (L / 4) * (∑ j, D j ^ 2) = -W / 2 := by
    rw [hDs]
    dsimp only [W]
    field_simp
  have hf := divergence_source_cutoff_bound F X u D (η := η) (Λ := Λ) (L := L)
    (Real.exp_nonneg _) hΛ hLp
  rw [hD] at hf
  simp only [Complex.add_re] at *
  linarith only [hb, hf]

private theorem c2e_gaussian_half {d : ℕ} {s : ℝ} (hs : 0 < s)
    (f : Vec d → ℂ)
    (hf : MemLp (fun x => (Real.exp (-euclideanSq x / (2*s)) : ℂ) * f x) 2 volume) :
    MemLp (fun x => (Real.exp (-euclideanSq x / s) : ℂ) * f x) 2 volume := by
  obtain ⟨_, hb, _, _⟩ := comparison_gaussian_admissible (d := d) (L := 2) (r := s)
    (by norm_num) hs
  convert hb.fun_mul (r := 2) hf using 1
  funext x
  rw [← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add]
  congr 3
  ring

private theorem c2e_gaussian_derivative_mul {d : ℕ} {s : ℝ} (hs : 0 < s)
    (f : Vec d → ℂ)
    (hf : MemLp (fun x => (Real.exp (-euclideanSq x / (2*s)) : ℂ) * f x) 2 volume)
    (j : Fin d) :
    MemLp (fun x => ((-2*x j/s*Real.exp (-euclideanSq x/s) : ℝ) : ℂ) * f x)
      2 volume := by
  obtain ⟨_, _, hd, hdb⟩ := comparison_gaussian_admissible (d := d) (L := 2) (r := s)
    (by norm_num) hs
  convert ((hdb j).const_mul (2 : ℂ)).fun_mul (r := 2) hf using 1
  funext x
  rw [hd]
  have he : Real.exp (-euclideanSq x/s) =
      Real.exp (-euclideanSq x/(2*s)) * Real.exp (-euclideanSq x/(2*s)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he]
  push_cast
  field_simp

private theorem c2e_gaussian_test_identity {d : ℕ} {s : ℝ} (hs : 0 < s)
    (u : Vec d → ℂ) (G P : Fin d → Vec d → ℂ) (q : Vec d → ℂ)
    (hre : ∀ j, HasWeakPartialDerivative univ j (fun x => (u x).re) (fun x => (G j x).re))
    (him : ∀ j, HasWeakPartialDerivative univ j (fun x => (u x).im) (fun x => (G j x).im))
    (hdivre : HasWeakDivergence univ (fun x j => (P j x).re) (fun x => (q x).re))
    (hdivim : HasWeakDivergence univ (fun x j => (P j x).im) (fun x => (q x).im))
    (hu : MemLp (fun x => (Real.exp (-euclideanSq x/(2*s)) : ℂ) * u x) 2 volume)
    (hG : ∀ j, MemLp (fun x => (Real.exp (-euclideanSq x/(2*s)) : ℂ) * G j x) 2 volume)
    (hP : ∀ j, MemLp (fun x => (Real.exp (-euclideanSq x/(2*s)) : ℂ) * P j x) 2 volume)
    (hq : MemLp (fun x => (Real.exp (-euclideanSq x/(2*s)) : ℂ) * q x) 2 volume) :
    let η : Vec d → ℝ := fun x => Real.exp (-euclideanSq x/s)
    (∫ x, q x * ((η x : ℂ)^2 * star (u x))) =
      -(∫ x, ∑ j, P j x * ((η x : ℂ)^2 * star (G j x) +
        ((2*η x*(-2*x j/s*η x) : ℝ) : ℂ) * star (u x))) := by
  intro η
  obtain ⟨U, H, hUH, hUx, hHx⟩ := physical_gaussian_local_h1_realization s hs u G hre him hu hG
  have ht := physical_gaussian_local_divergence_testing s hs P q hdivre hdivim hP hq
    (star U) (fun j => star (H j)) (physicalH1Graph_star U H hUH)
  have hleft : (∫ x, (Real.exp (-euclideanSq x/s) : ℂ) * q x * (star U) x) =
      ∫ x, q x * ((η x : ℂ)^2 * star (u x)) := by
    apply integral_congr_ae
    filter_upwards [hUx, Lp.coeFn_star U] with x hx hstar
    rw [hstar]
    simp only [Pi.star_apply]
    rw [hx]
    simp only [star_mul, Complex.star_def, Complex.conj_ofReal]
    dsimp only [η]
    ring
  have hright : (∫ x, ∑ j, P j x * ((Real.exp (-euclideanSq x/s) : ℂ) * (star (H j)) x +
        ((-2*x j/s*Real.exp (-euclideanSq x/s) : ℝ) : ℂ) * (star U) x)) =
      ∫ x, ∑ j, P j x * ((η x : ℂ)^2 * star (G j x) +
        ((2*η x*(-2*x j/s*η x) : ℝ) : ℂ) * star (u x)) := by
    apply integral_congr_ae
    filter_upwards [hUx, Lp.coeFn_star U, ae_all_iff.mpr hHx,
      ae_all_iff.mpr (fun j => Lp.coeFn_star (H j))] with x hx hstar hgrad hgradstar
    apply Finset.sum_congr rfl
    intro j _
    rw [hgradstar j, hstar]
    simp only [Pi.star_apply]
    rw [hgrad j, hx]
    simp only [star_add, star_mul, Complex.star_def, Complex.conj_ofReal]
    dsimp only [η]
    push_cast
    ring
  rw [hleft, hright] at ht
  exact ht

/-- Gaussian energy from the literal local H1 gradient and weak divergence equation.
The quarter-Gaussian L2 assumptions suffice for the noncompact conjugate test. -/
theorem physical_locally_h1_forced_gaussian_energy
    {d : ℕ} (a : Vec d → Mat d) (i : Fin d) (ζ : ℂ)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume)
    {Λ : ℝ} (hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ)
    (u g : Vec d → ℂ) (G R : Fin d → Vec d → ℂ)
    (hGre : ∀ j, HasWeakPartialDerivative Set.univ j (fun x => (u x).re) (fun x => (G j x).re))
    (hGim : ∀ j, HasWeakPartialDerivative Set.univ j (fun x => (u x).im) (fun x => (G j x).im))
    (hdivre : HasWeakDivergence Set.univ
      (fun x j => ((1/2 : ℂ) * (∑ k, (a x j k : ℂ) * G k x) - R j x).re)
      (fun x => (g x - ζ * (∑ j, (a x j i : ℂ) * G j x)).re))
    (hdivim : HasWeakDivergence Set.univ
      (fun x j => ((1/2 : ℂ) * (∑ k, (a x j k : ℂ) * G k x) - R j x).im)
      (fun x => (g x - ζ * (∑ j, (a x j i : ℂ) * G j x)).im))
    {L r : ℝ} (hΛ : 0 < Λ) (hL : 64 * Λ ^ 3 ≤ L) (hr : 0 < r)
    (hu : MemLp (fun x => (Real.exp (-euclideanSq x/(4*L*r)) : ℂ) * u x) 2 volume)
    (hg : MemLp (fun x => (Real.exp (-euclideanSq x/(4*L*r)) : ℂ) * g x) 2 volume)
    (hG : ∀ j, MemLp (fun x => (Real.exp (-euclideanSq x/(4*L*r)) : ℂ) * G j x) 2 volume)
    (hR : ∀ j, MemLp (fun x => (Real.exp (-euclideanSq x/(4*L*r)) : ℂ) * R j x) 2 volume) :
    let η : Vec d → ℝ := fun x => Real.exp (-euclideanSq x / (L * r))
    let W : Vec d → ℝ := fun x => -2 * euclideanSq x / (L * r ^ 2) * η x ^ 2
    Integrable (fun x => η x ^ 2 * ∑ j, ‖G j x‖ ^ 2) ∧
      Integrable (fun x => W x * ‖u x‖ ^ 2) ∧
      (Λ⁻¹ / 4) * (∫ x, η x ^ 2 * ∑ j, ‖G j x‖ ^ 2) ≤
        -2 * (∫ x, g x * (((η x ^ 2 : ℝ) : ℂ) * star (u x))).re +
          16 * Λ ^ 3 * ‖ζ‖ ^ 2 * (∫ x, η x ^ 2 * ‖u x‖ ^ 2) -
            (∫ x, W x * ‖u x‖ ^ 2) +
              (4 * Λ + 16 / L) * (∫ x, η x ^ 2 * ∑ j, ‖R j x‖ ^ 2) := by
  classical
  intro η W
  have hLp : 0 < L := lt_of_lt_of_le (by positivity) hL
  have hs : 0 < L*r := mul_pos hLp hr
  have half (f : Vec d → ℂ)
      (hf : MemLp (fun x => (Real.exp (-euclideanSq x/(4*L*r)) : ℂ)*f x) 2 volume) :
      MemLp (fun x => (Real.exp (-euclideanSq x/(2*(L*r))) : ℂ)*f x) 2 volume := by
    apply c2e_gaussian_half (s := 2*(L*r)) (by positivity) f
    convert hf using 1
    funext x
    congr 2
    congr 1
    ring
  have huhalf := half u hu
  have hghalf := half g hg
  have hGhalf := fun j => half (G j) (hG j)
  have hRhalf := fun j => half (R j) (hR j)
  have hηu := c2e_gaussian_half hs u huhalf
  have hηg := c2e_gaussian_half hs g hghalf
  have hηG := fun j => c2e_gaussian_half hs (G j) (hGhalf j)
  have hηR := fun j => c2e_gaussian_half hs (R j) (hRhalf j)
  let D : Fin d → Vec d → ℝ := fun j x => -2*x j/(L*r)*η x
  have hDu := fun j => c2e_gaussian_derivative_mul hs u huhalf j
  let K : Fin d → Vec d → ℂ := fun j x =>
    (η x : ℂ)*star (G j x) + (2 : ℂ)*star (((D j x : ℝ) : ℂ)*u x)
  have hK (j : Fin d) : MemLp (K j) 2 volume := by
    convert (hηG j).star.add ((hDu j).star.const_mul (2 : ℂ)) using 1
    funext x
    dsimp only [K, Pi.add_apply, Pi.mul_apply, Pi.star_apply, η, D]
    simp only [star_mul, Complex.star_def, Complex.conj_ofReal]
    ring
  let V : Vec d → ℂ := fun x => (η x : ℂ)^2*star (u x)
  let J : Fin d → Vec d → ℂ := fun j x => (η x : ℂ)*K j x
  have hJ (j : Fin d) (x : Vec d) : J j x =
      ((η x^2 : ℝ) : ℂ)*star (G j x) + star (u x)*((2*η x*D j x : ℝ) : ℂ) := by
    simp only [J, K, star_mul, Complex.star_def, Complex.conj_ofReal]
    push_cast
    ring
  have hηNI (f : Vec d → ℂ)
      (hf : MemLp (fun x => (η x : ℂ)*f x) 2 volume) :
      Integrable (fun x => η x^2*‖f x‖^2) := by
    convert hf.norm.integrable_sq using 1
    funext x
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
  have hηGI : Integrable (fun x => η x^2*∑ j, ‖G j x‖^2) := by
    simp_rw [Finset.mul_sum]
    exact integrable_finsetSum _ fun j _ => hηNI (G j) (hηG j)
  have hηUI := hηNI u hηu
  have hηRI : Integrable (fun x => η x^2*∑ j, ‖R j x‖^2) := by
    simp_rw [Finset.mul_sum]
    exact integrable_finsetSum _ fun j _ => hηNI (R j) (hηR j)
  have hWUI : Integrable (fun x => W x*‖u x‖^2) := by
    have hi : Integrable (fun x => ∑ j, ‖((D j x : ℝ) : ℂ)*u x‖^2) :=
      integrable_finsetSum _ fun j _ => (hDu j).norm.integrable_sq
    convert hi.const_mul (-(L/2)) using 1
    funext x
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs,
      D, W, euclideanSq, dot, Finset.mul_sum, Finset.sum_mul, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j _
    field_simp
  let T : Vec d → ℂ := fun x => ∑ j, ∑ k, (a x j k : ℂ)*G k x*J j x
  let F : Vec d → ℂ := fun x => (∑ j, (a x j i : ℂ)*G j x)*V x
  let S : Vec d → ℂ := fun x => ∑ j, R j x*J j x
  let M : Vec d → ℂ := fun x => -(1/2 : ℂ)*T x+ζ*F x+S x
  have hT : Integrable T := by
    apply integrable_finsetSum
    intro j _
    apply integrable_finsetSum
    intro k _
    convert ((hηG k).integrable_mul (hK j)).mul_of_top_left (ha j k) using 1
    funext x
    dsimp only [J, Pi.mul_apply]
    ring
  have hF : Integrable F := by
    have he : F = fun x => ∑ j, (a x j i : ℂ)*((η x : ℂ)*G j x)*star ((η x : ℂ)*u x) := by
      funext x
      simp only [F, V, Finset.sum_mul, star_mul, Complex.star_def, Complex.conj_ofReal]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [he]
    exact integrable_finsetSum _ fun j _ => by
      convert ((hηG j).integrable_mul hηu.star).mul_of_top_left (ha j i) using 1
      funext x
      dsimp only [Pi.mul_apply, Pi.star_apply, η]
      ring
  have hS : Integrable S := by
    apply integrable_finsetSum
    intro j _
    convert (hηR j).integrable_mul (hK j) using 1
    funext x
    dsimp only [J, Pi.mul_apply, η]
    ring
  have hgV : Integrable (fun x => g x*V x) := by
    convert hηg.integrable_mul hηu.star using 1
    funext x
    dsimp only [V, Pi.mul_apply, Pi.star_apply, η]
    simp only [star_mul, Complex.star_def, Complex.conj_ofReal]
    ring
  let P : Fin d → Vec d → ℂ := fun j x => (1/2 : ℂ)*(∑ k, (a x j k : ℂ)*G k x)-R j x
  let q : Vec d → ℂ := fun x => g x-ζ*(∑ j, (a x j i : ℂ)*G j x)
  have hcoeff (j k : Fin d) : MemLp
      (fun x => (Real.exp (-euclideanSq x/(2*(L*r))) : ℂ)*((a x j k : ℂ)*G k x)) 2 volume := by
    convert (ha j k).fun_mul (r := 2) (hGhalf k) using 1
    funext x
    ring
  have hP (j : Fin d) : MemLp
      (fun x => (Real.exp (-euclideanSq x/(2*(L*r))) : ℂ)*P j x) 2 volume := by
    convert ((memLp_finsetSum Finset.univ fun k _ => hcoeff j k).const_mul (1/2 : ℂ)).sub (hRhalf j) using 1
    funext x
    dsimp only [P, Pi.sub_apply]
    rw [← Finset.mul_sum]
    ring
  have hq : MemLp (fun x => (Real.exp (-euclideanSq x/(2*(L*r))) : ℂ)*q x) 2 volume := by
    have hc (j : Fin d) : MemLp
        (fun x => (Real.exp (-euclideanSq x/(2*(L*r))) : ℂ)*((a x j i : ℂ)*G j x)) 2 volume := by
      convert (ha j i).fun_mul (r := 2) (hGhalf j) using 1
      funext x
      ring
    convert hghalf.sub ((memLp_finsetSum Finset.univ fun j _ => hc j).const_mul ζ) using 1
    funext x
    dsimp only [q, Pi.sub_apply]
    rw [← Finset.mul_sum]
    ring
  have ht := c2e_gaussian_test_identity hs u G P q hGre hGim hdivre hdivim huhalf hGhalf hP hq
  change (∫ x, q x*V x) = -(∫ x, ∑ j, P j x*_) at ht
  have hleft : (∫ x, q x*V x) = (∫ x, g x*V x)-ζ*(∫ x, F x) := by
    rw [← integral_const_mul, ← integral_sub hgV (hF.const_mul ζ)]
    apply integral_congr_ae
    exact ae_of_all _ fun x => by dsimp only [q, F]; ring
  have hright : (∫ x, ∑ j, P j x*
      ((η x : ℂ)^2*star (G j x)+((2*η x*(-2*x j/(L*r)*η x) : ℝ) : ℂ)*star (u x))) =
      (1/2 : ℂ)*(∫ x, T x)-(∫ x, S x) := by
    rw [← integral_const_mul, ← integral_sub (hT.const_mul _) hS]
    apply integral_congr_ae
    refine ae_of_all _ fun x => ?_
    simp only [T, S, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    have he : (η x : ℂ)^2*star (G j x)+
        ((2*η x*(-2*x j/(L*r)*η x) : ℝ) : ℂ)*star (u x) = J j x := by
      rw [hJ]
      dsimp only [D]
      push_cast
      ring
    rw [he]
    dsimp only [P]
    rw [← Finset.mul_sum, ← Finset.sum_mul]
    ring
  rw [hleft, hright] at ht
  have hM : Integrable M := ((hT.const_mul _).add (hF.const_mul _)).add hS
  have hMi : (∫ x, M x) = ∫ x, g x*V x := by
    change (∫ x, (-(1/2 : ℂ)*T x+ζ*F x)+S x) = _
    rw [integral_add (f := fun x => -(1/2 : ℂ)*T x+ζ*F x) (g := S)
        ((hT.const_mul _).add (hF.const_mul _)) hS,
      integral_add (f := fun x => -(1/2 : ℂ)*T x) (g := fun x => ζ*F x)
        (hT.const_mul _) (hF.const_mul _), integral_const_mul, integral_const_mul]
    linear_combination -ht
  have hpoint : ∀ᵐ x ∂volume, 2*(M x).re+W x*‖u x‖^2 ≤
      -(Λ⁻¹/4)*(η x^2*∑ j, ‖G j x‖^2)+
        (16*Λ^3*‖ζ‖^2)*(η x^2*‖u x‖^2)+
          (4*Λ+16/L)*(η x^2*∑ j, ‖R j x‖^2) := by
    filter_upwards [hA] with x hx
    simp only [M, T, F, S, V, hJ, ← Complex.ofReal_pow]
    simpa only [η, D, W, mul_assoc] using comparison_gaussian_divergence_coercive hx x
      (fun j => G j x) (fun j => R j x) (u x) i ζ hL hr
  have hMr : Integrable (fun x => (M x).re) := hM.re
  have hMri : (∫ x, (M x).re) = (∫ x, M x).re := integral_re hM
  have hint := integral_mono_ae ((hMr.const_mul 2).add hWUI)
    (((hηGI.const_mul (-(Λ⁻¹/4))).add (hηUI.const_mul (16*Λ^3*‖ζ‖^2))).add
      (hηRI.const_mul (4*Λ+16/L))) hpoint
  change (∫ x, 2*(M x).re+W x*‖u x‖^2) ≤
    ∫ x, -(Λ⁻¹/4)*(η x^2*∑ j, ‖G j x‖^2)+
      (16*Λ^3*‖ζ‖^2)*(η x^2*‖u x‖^2)+(4*Λ+16/L)*(η x^2*∑ j, ‖R j x‖^2) at hint
  rw [integral_add (hMr.const_mul 2) hWUI, integral_const_mul,
    hMri, hMi,
    integral_add (f := fun x => -(Λ⁻¹/4)*(η x^2*∑ j, ‖G j x‖^2)+
        (16*Λ^3*‖ζ‖^2)*(η x^2*‖u x‖^2))
      (g := fun x => (4*Λ+16/L)*(η x^2*∑ j, ‖R j x‖^2))
      ((hηGI.const_mul (-(Λ⁻¹/4))).add (hηUI.const_mul (16*Λ^3*‖ζ‖^2)))
      (hηRI.const_mul (4*Λ+16/L)),
    integral_add (hηGI.const_mul (-(Λ⁻¹/4))) (hηUI.const_mul (16*Λ^3*‖ζ‖^2)),
    integral_const_mul, integral_const_mul, integral_const_mul] at hint
  exact ⟨hηGI, hWUI, by simp only [Complex.ofReal_pow]; dsimp only [V] at hint; linarith only [hint]⟩

end EinsteinFull.Blueprint
