import EinsteinFull.Calculus.PhysicalComplexEvolution
import EinsteinFull.Work.W6.PhysicalLocalEnergySupport
import Mathlib.Analysis.Calculus.ParametricIntegral
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation EinsteinRelation.External.AKM
-- Independent copies of the checked scalar and Hilbert-space calculations in C10.
private theorem comparison_gaussian_time_derivative {d : ℕ} (x : Vec d)
    {L t : ℝ} (hL : 0 < L) (ht : t < 2) :
    HasDerivAt (fun r : ℝ => Real.exp (-euclideanSq x / (L * (2 - r))) ^ 2)
      (-2 * euclideanSq x / (L * (2 - t) ^ 2) *
        Real.exp (-euclideanSq x / (L * (2 - t))) ^ 2) t := by
  have hr : L * (2 - t) ≠ 0 := ne_of_gt (mul_pos hL (sub_pos.mpr ht))
  have hden := ((hasDerivAt_const t (2 : ℝ)).sub (hasDerivAt_id t)).const_mul L
  have hq := ((hasDerivAt_const t (-euclideanSq x)).div hden hr).exp.pow 2
  convert hq using 1
  · rfl
  · dsimp
    field_simp [ne_of_gt hL, ne_of_gt (sub_pos.mpr ht)]
    ring

private theorem comparison_gaussian_weight_energy_hasDerivAt {d : ℕ}
    (u : Lp ℂ 2 (volume : Measure (Vec d))) {L t : ℝ}
    (hL : 0 < L) (ht : t < 2) :
    HasDerivAt (fun s : ℝ => ∫ x,
      Real.exp (-euclideanSq x / (L * (2 - s))) ^ 2 * ‖u x‖ ^ 2)
      (∫ x, (-2 * euclideanSq x / (L * (2 - t) ^ 2) *
        Real.exp (-euclideanSq x / (L * (2 - t))) ^ 2) * ‖u x‖ ^ 2) t := by
  let η : ℝ → Vec d → ℝ := fun s x => Real.exp (-euclideanSq x / (L * (2 - s)))
  let W : ℝ → Vec d → ℝ := fun s x =>
    -2 * euclideanSq x / (L * (2 - s) ^ 2) * η s x ^ 2
  let δ : ℝ := (2 - t) / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hq (x : Vec d) : 0 ≤ euclideanSq x := by
    change 0 ≤ ∑ j : Fin d, x j * x j
    exact Finset.sum_nonneg fun j _ => mul_self_nonneg _
  have hη (s : ℝ) (hs : s < 2) (x : Vec d) : 0 ≤ η s x ∧ η s x ≤ 1 :=
    ⟨Real.exp_nonneg _, Real.exp_le_one_iff.mpr
      (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (hq x)) (by positivity))⟩
  have hcη (s : ℝ) : Continuous (η s) := by
    dsimp only [η, euclideanSq, dot]
    fun_prop
  have hcW (s : ℝ) : Continuous (W s) := by
    dsimp only [W, η, euclideanSq, dot]
    fun_prop
  have hW (s : ℝ) (hs : s < 2) (x : Vec d) : ‖W s x‖ ≤ 2 / (2 - s) := by
    have hden : 0 < L * (2 - s) := by positivity
    have hqη : euclideanSq x * η s x ≤ L * (2 - s) := by
      have he := (Real.mul_exp_neg_le_exp_neg_one (euclideanSq x / (L * (2 - s)))).trans
        (Real.exp_le_one_iff.mpr (by norm_num))
      have hm := mul_le_mul_of_nonneg_left he hden.le
      have heq : L * (2 - s) * (euclideanSq x / (L * (2 - s)) *
          Real.exp (-(euclideanSq x / (L * (2 - s))))) = euclideanSq x * η s x := by
        dsimp only [η]
        rw [neg_div]
        field_simp [ne_of_gt hL, ne_of_gt (sub_pos.mpr hs)]
      simpa only [heq, mul_one] using hm
    have hqηsq : euclideanSq x * η s x ^ 2 ≤ L * (2 - s) := by
      have hm := mul_le_mul_of_nonneg_left (hη s hs x).2
        (mul_nonneg (hq x) (hη s hs x).1)
      nlinarith only [hm, hqη]
    have hwneg : W s x ≤ 0 := by
      dsimp only [W]
      exact mul_nonpos_of_nonpos_of_nonneg
        (div_nonpos_of_nonpos_of_nonneg (by nlinarith [hq x]) (by positivity))
        (sq_nonneg _)
    rw [Real.norm_eq_abs, abs_of_nonpos hwneg]
    have he : -W s x = (2 / (L * (2 - s) ^ 2)) * (euclideanSq x * η s x ^ 2) := by
      dsimp only [W]
      ring
    rw [he]
    calc
      _ ≤ (2 / (L * (2 - s) ^ 2)) * (L * (2 - s)) :=
        mul_le_mul_of_nonneg_left hqηsq (by positivity)
      _ = 2 / (2 - s) := by field_simp [ne_of_gt hL, ne_of_gt (sub_pos.mpr hs)]
  have hUN := (Lp.memLp u).norm.integrable_sq
  have hmeas (s : ℝ) : AEStronglyMeasurable
      (fun x => η s x ^ 2 * ‖u x‖ ^ 2) volume :=
    ((hcη s).aestronglyMeasurable.pow 2).mul hUN.aestronglyMeasurable
  have hint : Integrable (fun x => η t x ^ 2 * ‖u x‖ ^ 2) := by
    apply hUN.mono' (hmeas t)
    refine ae_of_all _ fun x => ?_
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (sq_nonneg _), abs_of_nonneg (sq_nonneg _)]
    have hsq : η t x ^ 2 ≤ 1 := by
      nlinarith [(hη t ht x).1, (hη t ht x).2,
        mul_nonneg (sub_nonneg.mpr (hη t ht x).2) (hη t ht x).1]
    exact mul_le_of_le_one_left (sq_nonneg _) hsq
  have hwm : AEStronglyMeasurable (fun x => W t x * ‖u x‖ ^ 2) volume :=
    (hcW t).aestronglyMeasurable.mul hUN.aestronglyMeasurable
  have hb : ∀ᵐ x ∂volume, ∀ s ∈ Ioo (t - δ) (t + δ),
      ‖W s x * ‖u x‖ ^ 2‖ ≤ (2 / δ) * ‖u x‖ ^ 2 := by
    refine ae_of_all _ fun x s hs => ?_
    have hsr : δ ≤ 2 - s := by dsimp only [δ] at *; linarith [hs.2]
    have hs2 : s < 2 := by linarith
    rw [norm_mul, Real.norm_eq_abs (‖u x‖ ^ 2), abs_of_nonneg (sq_nonneg _)]
    exact mul_le_mul_of_nonneg_right
      ((hW s hs2 x).trans (div_le_div_of_nonneg_left (by norm_num) hδ hsr))
      (sq_nonneg _)
  have hd : ∀ᵐ x ∂volume, ∀ s ∈ Ioo (t - δ) (t + δ),
      HasDerivAt (fun z => η z x ^ 2 * ‖u x‖ ^ 2) (W s x * ‖u x‖ ^ 2) s := by
    refine ae_of_all _ fun x s hs => ?_
    have hs2 : s < 2 := by dsimp only [δ] at *; linarith [hs.2]
    exact (comparison_gaussian_time_derivative x hL hs2).mul_const _
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Ioo_mem_nhds (by linarith) (by linarith))
    (Eventually.of_forall hmeas) hint hwm hb (hUN.const_mul (2 / δ)) hd).2

/-- A moving bounded quadratic form can be differentiated along an actual
Hilbert-space curve using only its fixed-vector derivative and a local
operator Lipschitz bound. The mixed increment is proved negligible. -/
private theorem moving_quadratic_energy_hasDerivAt
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (M : ℝ → E →L[ℝ] E) {u : ℝ → E} {g : E} {t b C : ℝ}
    (hu : HasDerivAt u g t)
    (hM : ∀ᶠ s in 𝓝 t, ‖M s - M t‖ ≤ C * ‖s - t‖)
    (hb : HasDerivAt (fun s => inner ℝ (u t) (M s (u t))) b t) :
    HasDerivAt (fun s => inner ℝ (u s) (M s (u s)))
      (inner ℝ (u t) (M t g) + inner ℝ g (M t (u t)) + b) t := by
  let R : ℝ → ℝ := fun s =>
    inner ℝ (u s - u t) ((M s - M t) (u s)) +
      inner ℝ (u t) ((M s - M t) (u s - u t))
  let f : ℝ → ℝ := fun s => ‖u s - u t‖ * (‖u s‖ + ‖u t‖)
  have hf : Tendsto f (𝓝 t) (𝓝 0) := by
    have hd := (hu.continuousAt.tendsto.sub (tendsto_const_nhds (x := u t))).norm
    have hn := hu.continuousAt.tendsto.norm.add (tendsto_const_nhds (x := ‖u t‖))
    simpa only [f, sub_self, norm_zero, zero_mul] using hd.mul hn
  have hfo : f =o[𝓝 t] (fun _ : ℝ => (1 : ℝ)) :=
    (Asymptotics.isLittleO_one_iff ℝ).mpr hf
  have hmo : (fun s => ‖M s - M t‖) =O[𝓝 t] (fun s => s - t) :=
    (Asymptotics.IsBigO.of_bound C hM).norm_left
  have hbound (s : ℝ) : ‖R s‖ ≤ f s * ‖M s - M t‖ := by
    have h1 := norm_inner_le_norm (𝕜 := ℝ) (u s - u t) ((M s - M t) (u s))
    have h2 := norm_inner_le_norm (𝕜 := ℝ) (u t) ((M s - M t) (u s - u t))
    have h3 := (M s - M t).le_opNorm (u s)
    have h4 := (M s - M t).le_opNorm (u s - u t)
    have h5 := norm_add_le (inner ℝ (u s - u t) ((M s - M t) (u s)))
      (inner ℝ (u t) ((M s - M t) (u s - u t)))
    dsimp only [R, f]
    nlinarith only [h5, h1, h2,
      mul_le_mul_of_nonneg_left h3 (norm_nonneg (u s - u t)),
      mul_le_mul_of_nonneg_left h4 (norm_nonneg (u t))]
  have hRo : R =o[𝓝 t] (fun s => s - t) := by
    have hr : R =O[𝓝 t] (fun s => f s * ‖M s - M t‖) := by
      apply Asymptotics.IsBigO.of_bound 1
      exact Eventually.of_forall fun s => by
        have hfn : 0 ≤ f s := by dsimp only [f]; positivity
        simpa only [one_mul, norm_mul, norm_norm, Real.norm_of_nonneg hfn] using hbound s
    exact hr.trans_isLittleO (by simpa only [one_mul] using hfo.mul_isBigO hmo)
  have hbase := hu.inner ℝ ((M t).hasFDerivAt.comp_hasDerivAt t hu)
  have hq := (hbase.add hb).sub_const (inner ℝ (u t) (M t (u t)))
  apply HasDerivAt.of_isLittleO
  have hsum := hq.isLittleO.add hRo
  convert hsum using 1
  funext s
  dsimp only [R, Pi.add_apply, Function.comp_apply]
  simp only [sub_apply, map_sub, inner_sub_left, inner_sub_right]
  simp only [smul_eq_mul]
  ring

/-- Differentiate the shrinking Gaussian energy along a differentiable complex L² orbit. -/
theorem moving_gaussian_orbit_energy_hasDerivAt
    {d : ℕ} {u : ℝ → Lp ℂ 2 (volume : Measure (Vec d))}
    {g : Lp ℂ 2 (volume : Measure (Vec d))} {t L : ℝ}
    (hu : HasDerivAt u g t) (hL : 0 < L) (ht : t < 2) :
    HasDerivAt (fun s : ℝ => ∫ x : Vec d,
      Real.exp (-euclideanSq x / (L * (2-s))) ^ 2 * ‖u s x‖ ^ 2)
      ((∫ x : Vec d, (-2 * euclideanSq x / (L * (2-t)^2) *
        Real.exp (-euclideanSq x / (L * (2-t))) ^ 2) * ‖u t x‖ ^ 2) +
       2 * (∫ x : Vec d, g x *
        (((Real.exp (-euclideanSq x / (L * (2-t))) ^ 2 : ℝ) : ℂ) *
          star (u t x))).re) t := by
  let η : ℝ → Vec d → ℝ := fun s x => Real.exp (-euclideanSq x / (L * (2 - s)))
  let W : ℝ → Vec d → ℝ := fun s x =>
    -2 * euclideanSq x / (L * (2 - s) ^ 2) * η s x ^ 2
  let δ : ℝ := (2 - t) / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hq (x : Vec d) : 0 ≤ euclideanSq x := by
    change 0 ≤ ∑ j : Fin d, x j * x j
    exact Finset.sum_nonneg fun j _ => mul_self_nonneg _
  have hη (s : ℝ) (hs : s < 2) (x : Vec d) : 0 ≤ η s x ∧ η s x ≤ 1 :=
    ⟨Real.exp_nonneg _, Real.exp_le_one_iff.mpr
      (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (hq x)) (by positivity))⟩
  have hcη (s : ℝ) : Continuous (η s) := by
    dsimp only [η, euclideanSq, dot]
    fun_prop
  have hcW (s : ℝ) : Continuous (W s) := by
    dsimp only [W, η, euclideanSq, dot]
    fun_prop
  have hW (s : ℝ) (hs : s < 2) (x : Vec d) : ‖W s x‖ ≤ 2 / (2 - s) := by
    have hden : 0 < L * (2 - s) := by positivity
    have hqη : euclideanSq x * η s x ≤ L * (2 - s) := by
      have he := (Real.mul_exp_neg_le_exp_neg_one (euclideanSq x / (L * (2 - s)))).trans
        (Real.exp_le_one_iff.mpr (by norm_num))
      have hm := mul_le_mul_of_nonneg_left he hden.le
      have heq : L * (2 - s) * (euclideanSq x / (L * (2 - s)) *
          Real.exp (-(euclideanSq x / (L * (2 - s))))) = euclideanSq x * η s x := by
        dsimp only [η]
        rw [neg_div]
        field_simp [ne_of_gt hL, ne_of_gt (sub_pos.mpr hs)]
      simpa only [heq, mul_one] using hm
    have hqηsq : euclideanSq x * η s x ^ 2 ≤ L * (2 - s) := by
      have hm := mul_le_mul_of_nonneg_left (hη s hs x).2
        (mul_nonneg (hq x) (hη s hs x).1)
      nlinarith only [hm, hqη]
    have hwneg : W s x ≤ 0 := by
      dsimp only [W]
      exact mul_nonpos_of_nonpos_of_nonneg
        (div_nonpos_of_nonpos_of_nonneg (by nlinarith [hq x]) (by positivity))
        (sq_nonneg _)
    rw [Real.norm_eq_abs, abs_of_nonpos hwneg]
    have he : -W s x = (2 / (L * (2 - s) ^ 2)) * (euclideanSq x * η s x ^ 2) := by
      dsimp only [W]
      ring
    rw [he]
    calc
      _ ≤ (2 / (L * (2 - s) ^ 2)) * (L * (2 - s)) :=
        mul_le_mul_of_nonneg_left hqηsq (by positivity)
      _ = 2 / (2 - s) := by field_simp [ne_of_gt hL, ne_of_gt (sub_pos.mpr hs)]
  have hb (s : ℝ) (hs : s < 2) : MemLp (fun x => ((η s x ^ 2 : ℝ) : ℂ)) ∞ volume := by
    apply memLp_top_of_bound
      (Complex.continuous_ofReal.comp ((hcη s).pow 2)).aestronglyMeasurable 1
    refine ae_of_all _ fun x => ?_
    change ‖((η s x ^ 2 : ℝ) : ℂ)‖ ≤ 1
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith [(hη s hs x).1, (hη s hs x).2,
      mul_nonneg (sub_nonneg.mpr (hη s hs x).2) (hη s hs x).1]
  let M : ℝ → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℝ]
      Lp ℂ 2 (volume : Measure (Vec d)) := fun s =>
    if hs : s < 2 then
      (((ContinuousLinearMap.mul ℂ ℂ).holderL volume ∞ 2 2 ((hb s hs).toLp _)).restrictScalars ℝ)
    else 0
  have hMx (s : ℝ) (hs : s < 2) (v : Lp ℂ 2 (volume : Measure (Vec d))) :
      M s v =ᵐ[volume] fun x => ((η s x ^ 2 : ℝ) : ℂ) * v x := by
    have hm := (ContinuousLinearMap.mul ℂ ℂ).coeFn_holder (r := 2) ((hb s hs).toLp _) v
    filter_upwards [(hb s hs).coeFn_toLp, hm] with x hx hmx
    dsimp only [M]
    rw [dite_eq_left hs]
    change (((ContinuousLinearMap.mul ℂ ℂ).holderL volume ∞ 2 2 ((hb s hs).toLp _)) v) x = _
    simpa only [ContinuousLinearMap.holderL_apply_apply, ContinuousLinearMap.mul_apply', hx] using hmx
  have hinner (s : ℝ) (hs : s < 2) (v w : Lp ℂ 2 (volume : Measure (Vec d))) :
      inner ℝ v (M s w) =
        (∫ x, w x * (((η s x ^ 2 : ℝ) : ℂ) * star (v x))).re := by
    calc
      inner ℝ v (M s w) = (∫ x, M s w x * star (v x)).re := by
        rw [L2.inner_def]
        simp only [real_inner_eq_re_inner (𝕜 := ℂ), RCLike.inner_apply]
        exact integral_re ((Lp.memLp (M s w)).integrable_mul (Lp.memLp v).star)
      _ = _ := by
        apply congrArg Complex.re
        apply integral_congr_ae
        filter_upwards [hMx s hs w] with x hx
        rw [hx]
        ring
  have henergy (s : ℝ) (hs : s < 2) (v : Lp ℂ 2 (volume : Measure (Vec d))) :
      inner ℝ v (M s v) = ∫ x, η s x ^ 2 * ‖v x‖ ^ 2 := by
    rw [L2.inner_def]
    simp only [real_inner_eq_re_inner (𝕜 := ℂ), RCLike.inner_apply]
    apply integral_congr_ae
    filter_upwards [hMx s hs v] with x hx
    rw [hx]
    change ((((η s x ^ 2 : ℝ) : ℂ) * v x) * star (v x)).re = _
    simp only [mul_assoc, Complex.star_def, Complex.mul_conj',
      ← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]
  have hlocal : ∀ᶠ s in 𝓝 t, s ∈ Ioo (t - δ) (t + δ) :=
    Ioo_mem_nhds (by linarith) (by linarith)
  have hlip : ∀ᶠ s in 𝓝 t, ‖M s - M t‖ ≤ (2 / δ) * ‖s - t‖ := by
    filter_upwards [hlocal] with s hs
    have hs2 : s < 2 := by dsimp [δ] at hs; linarith [hs.2]
    have hpoint (x : Vec d) : ‖η s x ^ 2 - η t x ^ 2‖ ≤ (2 / δ) * ‖s - t‖ := by
      apply Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
        (f' := fun z => W z x) (s := Ioo (t - δ) (t + δ))
        (fun z hz => (comparison_gaussian_time_derivative x hL
          (by dsimp [δ] at hz; linarith [hz.2])).hasDerivWithinAt)
        (fun z hz => ?_) (convex_Ioo _ _) ⟨by linarith, by linarith⟩ hs
      have hz2 : z < 2 := by dsimp [δ] at hz; linarith [hz.2]
      exact (hW z hz2 x).trans (div_le_div_of_nonneg_left (by norm_num) hδ
        (by dsimp [δ] at hz ⊢; linarith [hz.2]))
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro v
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [hMx s hs2 v, hMx t ht v, Lp.coeFn_sub (M s v) (M t v)] with x hx hy hsub
    change ‖((M s - M t) v) x‖ ≤ _
    rw [sub_apply, hsub]
    simp only [Pi.sub_apply]
    rw [hx, hy, ← sub_mul, norm_mul]
    have he : ‖((η s x ^ 2 : ℝ) : ℂ) - ((η t x ^ 2 : ℝ) : ℂ)‖ =
        ‖η s x ^ 2 - η t x ^ 2‖ := by rw [← Complex.ofReal_sub, Complex.norm_real]
    rw [he]
    exact mul_le_mul_of_nonneg_right (hpoint x) (norm_nonneg _)
  have hweight := comparison_gaussian_weight_energy_hasDerivAt (u t) hL ht
  have hweight' : HasDerivAt (fun s => inner ℝ (u t) (M s (u t)))
      (∫ x, W t x * ‖u t x‖ ^ 2) t := by
    apply hweight.congr_of_eventuallyEq
    filter_upwards [hlocal] with s hs
    exact henergy s (by dsimp [δ] at hs; linarith [hs.2]) (u t)
  have h := moving_quadratic_energy_hasDerivAt M hu hlip hweight'
  have hsym (v w : Lp ℂ 2 (volume : Measure (Vec d))) :
      inner ℝ v (M t w) = inner ℝ w (M t v) := by
    rw [L2.inner_def, L2.inner_def]
    simp only [real_inner_eq_re_inner (𝕜 := ℂ), RCLike.inner_apply]
    apply integral_congr_ae
    filter_upwards [hMx t ht v, hMx t ht w] with x hv hw
    rw [hv, hw]
    change ((((η t x ^ 2 : ℝ) : ℂ) * w x) * star (v x)).re =
      ((((η t x ^ 2 : ℝ) : ℂ) * v x) * star (w x)).re
    simp only [Complex.star_def, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im]
    ring
  have hc : inner ℝ (u t) (M t g) + inner ℝ g (M t (u t)) =
      2 * (∫ x, g x * (((η t x ^ 2 : ℝ) : ℂ) * star (u t x))).re := by
    rw [hsym g (u t), hinner t ht]
    ring
  rw [hc, add_comm] at h
  apply h.congr_of_eventuallyEq
  filter_upwards [hlocal] with s hs
  exact (henergy s (by dsimp [δ] at hs; linarith [hs.2]) (u s)).symm

-- Exact supervisor type and scoped closure checks.
example
    {d : ℕ} {u : ℝ → Lp ℂ 2 (volume : Measure (Vec d))}
    {g : Lp ℂ 2 (volume : Measure (Vec d))} {t L : ℝ}
    (hu : HasDerivAt u g t) (hL : 0 < L) (ht : t < 2) :
    HasDerivAt (fun s : ℝ => ∫ x : Vec d,
      Real.exp (-euclideanSq x / (L * (2-s))) ^ 2 * ‖u s x‖ ^ 2)
      ((∫ x : Vec d, (-2 * euclideanSq x / (L * (2-t)^2) *
        Real.exp (-euclideanSq x / (L * (2-t))) ^ 2) * ‖u t x‖ ^ 2) +
       2 * (∫ x : Vec d, g x *
        (((Real.exp (-euclideanSq x / (L * (2-t))) ^ 2 : ℝ) : ℂ) *
          star (u t x))).re) t :=
  moving_gaussian_orbit_energy_hasDerivAt hu hL ht

#print axioms moving_gaussian_orbit_energy_hasDerivAt
#lint
run_cmd do
  let env ← Lean.getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    if (env.getModuleIdxFor? name).isNone then
      let axioms ← Lean.collectAxioms name
      for ax in axioms do
        unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
          throwError "Unexpected axiom {ax} in {name}"
      count := count + 1
  Lean.logInfo m!"Standard-axiom audit passed for all {count} local declarations."

end EinsteinFull.Blueprint
