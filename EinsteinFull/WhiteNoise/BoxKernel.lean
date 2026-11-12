import Mathlib

/-!
# The box kernel

For `x y : Fin d → ℝ`, `boxKernel x y = ∏ i, boxSign (y i) (x i)` is, as a function of `y`, the
signed indicator of the box between `0` and `x`. This file proves the `d`-fold fundamental theorem
of calculus `∫ (∏ i, boxSign (y i) (x i)) * mixedDeriv d g x dx = (-1) ^ d * g y` for smooth
compactly supported `g` (`integral_prod_boxSign_mul_mixedDeriv`), where `mixedDeriv d` is the mixed
derivative `∂₀ ⋯ ∂_{d-1}`. It computes `‖boxKernel x‖²_{L²} = ∏ i, |x i|` and the Parseval identity
for the coefficients of the box kernel in a Hilbert basis of `L²(Fin d → ℝ)`
(`hasSum_kernelCoeff_sq`), and introduces the finite Gaussian-weighted measure
`weightMeasure d`, under which `x ↦ ∏ i, |x i|` is integrable.
-/

open MeasureTheory Set Filter Topology
open scoped InnerProductSpace RealInnerProductSpace ENNReal NNReal

noncomputable section

namespace EinsteinFull.WhiteNoise

section FTC

open scoped ContDiff

/-- The signed one-dimensional box kernel `1{y ≤ t} - 1{y ≤ 0}`; as a function of `y` it is the
signed indicator of the interval between `0` and `t`. -/
def boxSign (y t : ℝ) : ℝ := (if y ≤ t then 1 else 0) - (if y ≤ 0 then 1 else 0)

lemma measurable_boxSign : Measurable (fun p : ℝ × ℝ => boxSign p.1 p.2) := by
  unfold boxSign
  refine Measurable.sub ?_ ?_
  · exact Measurable.ite (measurableSet_le measurable_fst measurable_snd) measurable_const
      measurable_const
  · exact Measurable.ite (measurableSet_le measurable_fst measurable_const) measurable_const
      measurable_const

lemma abs_boxSign_le (y t : ℝ) : |boxSign y t| ≤ 1 := by
  unfold boxSign; split_ifs <;> norm_num

/-- Partial derivative in the coordinate `i`. -/
def pderiv {d : ℕ} (i : Fin d) (h : (Fin d → ℝ) → ℝ) : (Fin d → ℝ) → ℝ :=
  fun x => fderiv ℝ h x (Pi.single i 1)

/-- The mixed derivative `∂₀ ∂₁ ⋯ ∂_{d-1}`. -/
def mixedDeriv (d : ℕ) (g : (Fin d → ℝ) → ℝ) : (Fin d → ℝ) → ℝ :=
  (List.finRange d).foldr pderiv g

lemma contDiff_pderiv {d : ℕ} (i : Fin d) {h : (Fin d → ℝ) → ℝ} (hh : ContDiff ℝ ∞ h) :
    ContDiff ℝ ∞ (pderiv i h) :=
  (hh.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

lemma hasCompactSupport_pderiv {d : ℕ} (i : Fin d) {h : (Fin d → ℝ) → ℝ}
    (hh : HasCompactSupport h) : HasCompactSupport (pderiv i h) := by
  refine (hh.fderiv (𝕜 := ℝ)).mono' ?_
  intro x hx
  apply subset_tsupport
  intro h0
  apply hx
  simp [pderiv, h0]

lemma contDiff_foldr_pderiv {d : ℕ} (l : List (Fin d)) {g : (Fin d → ℝ) → ℝ}
    (hg : ContDiff ℝ ∞ g) : ContDiff ℝ ∞ (l.foldr pderiv g) := by
  induction l with
  | nil => exact hg
  | cons i l ih => exact contDiff_pderiv i ih

lemma hasCompactSupport_foldr_pderiv {d : ℕ} (l : List (Fin d)) {g : (Fin d → ℝ) → ℝ}
    (hg : HasCompactSupport g) : HasCompactSupport (l.foldr pderiv g) := by
  induction l with
  | nil => exact hg
  | cons i l ih => exact hasCompactSupport_pderiv i ih

lemma hasFDerivAt_finCons_right {d : ℕ} (a : ℝ) (z : Fin d → ℝ) :
    HasFDerivAt (fun w : Fin d → ℝ => (Fin.cons a w : Fin (d + 1) → ℝ))
      ((0 : (Fin d → ℝ) →L[ℝ] ℝ).finCons (ContinuousLinearMap.id ℝ (Fin d → ℝ))) z :=
  hasFDerivAt_finCons'.mpr ⟨hasFDerivAt_const a z, hasFDerivAt_id z⟩

lemma finCons_zero_single {d : ℕ} (i : Fin d) :
    (Fin.cons (0 : ℝ) (Pi.single i (1 : ℝ)) : Fin (d + 1) → ℝ) = Pi.single i.succ 1 := by
  ext j
  refine Fin.cases ?_ (fun j => ?_) j
  · simp
  · simp [Pi.single_apply, Fin.succ_inj]

lemma pderiv_succ_finCons {d : ℕ} (i : Fin d) {H : (Fin (d + 1) → ℝ) → ℝ}
    (hH : Differentiable ℝ H) (a : ℝ) (z : Fin d → ℝ) :
    pderiv i.succ H (Fin.cons a z) = pderiv i (fun w => H (Fin.cons a w)) z := by
  have h1 := (hH (Fin.cons a z)).hasFDerivAt.comp z (hasFDerivAt_finCons_right a z)
  simp only [pderiv]
  rw [show (fun w => H (Fin.cons a w)) = H ∘ (fun w => (Fin.cons a w : Fin (d + 1) → ℝ)) from rfl,
    h1.fderiv, ContinuousLinearMap.comp_apply, ← finCons_zero_single]
  rfl

lemma foldr_pderiv_succ_finCons {d : ℕ} (l : List (Fin d)) {g : (Fin (d + 1) → ℝ) → ℝ}
    (hg : ContDiff ℝ ∞ g) (a : ℝ) :
    (fun z => (l.foldr (fun i h => pderiv i.succ h) g) (Fin.cons a z)) =
      l.foldr pderiv (fun z => g (Fin.cons a z)) := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    funext z
    have hsm : ContDiff ℝ ∞ (l.foldr (fun i h => pderiv i.succ h) g) := by
      rw [← List.foldr_map (f := Fin.succ) (g := pderiv)]
      exact contDiff_foldr_pderiv _ hg
    simp only [List.foldr_cons]
    rw [pderiv_succ_finCons i (hsm.differentiable (by simp)) a z, ih]

lemma mixedDeriv_succ (d : ℕ) (g : (Fin (d + 1) → ℝ) → ℝ) :
    mixedDeriv (d + 1) g =
      pderiv 0 ((List.finRange d).foldr (fun i h => pderiv i.succ h) g) := by
  rw [mixedDeriv, List.finRange_succ, List.foldr_cons, List.foldr_map]

lemma hasCompactSupport_comp_finCons_left {d : ℕ} {h : (Fin (d + 1) → ℝ) → ℝ}
    (hh : HasCompactSupport h) (z : Fin d → ℝ) :
    HasCompactSupport (fun u : ℝ => h (Fin.cons u z)) := by
  obtain ⟨R, hR⟩ := hh.isCompact.isBounded.subset_closedBall 0
  refine HasCompactSupport.intro (isCompact_closedBall (0 : ℝ) R) (fun u hu => ?_)
  apply image_eq_zero_of_notMem_tsupport
  intro hmem
  apply hu
  have h1 := hR hmem
  simp only [Metric.mem_closedBall, dist_zero_right] at h1 ⊢
  exact (norm_le_pi_norm (Fin.cons u z : Fin (d + 1) → ℝ) 0).trans h1

lemma hasCompactSupport_comp_finCons_right {d : ℕ} {h : (Fin (d + 1) → ℝ) → ℝ}
    (hh : HasCompactSupport h) (a : ℝ) :
    HasCompactSupport (fun z : Fin d → ℝ => h (Fin.cons a z)) := by
  obtain ⟨R, hR⟩ := hh.isCompact.isBounded.subset_closedBall 0
  refine HasCompactSupport.intro (isCompact_closedBall (0 : Fin d → ℝ) R) (fun z hz => ?_)
  apply image_eq_zero_of_notMem_tsupport
  intro hmem
  apply hz
  have h1 := hR hmem
  simp only [Metric.mem_closedBall, dist_zero_right] at h1 ⊢
  refine (pi_norm_le_iff_of_nonneg ((norm_nonneg _).trans h1)).2 (fun i => ?_)
  have := norm_le_pi_norm (Fin.cons a z : Fin (d + 1) → ℝ) i.succ
  simp only [Fin.cons_succ] at this
  exact this.trans h1

lemma contDiff_finCons_right {d : ℕ} (a : ℝ) :
    ContDiff ℝ ∞ (fun z : Fin d → ℝ => (Fin.cons a z : Fin (d + 1) → ℝ)) := by
  refine contDiff_pi.2 (fun j => ?_)
  refine Fin.cases ?_ (fun j => ?_) j
  · simpa using contDiff_const
  · simpa using contDiff_apply ℝ ℝ j

lemma contDiff_finCons_left {d : ℕ} (z : Fin d → ℝ) :
    ContDiff ℝ ∞ (fun u : ℝ => (Fin.cons u z : Fin (d + 1) → ℝ)) := by
  refine contDiff_pi.2 (fun j => ?_)
  refine Fin.cases ?_ (fun j => ?_) j
  · simp only [Fin.cons_zero]; exact contDiff_id
  · simp only [Fin.cons_succ]; exact contDiff_const

/-- One-dimensional fundamental theorem of calculus against the signed box kernel. -/
lemma integral_boxSign_mul_deriv {φ : ℝ → ℝ} (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ)
    (y : ℝ) : ∫ t, boxSign y t * deriv φ t = -φ y := by
  have hd : ∀ t, HasDerivAt φ (deriv φ t) t := fun t =>
    ((hφ.differentiable (by simp)) t).hasDerivAt
  have hint : Integrable (deriv φ) :=
    (hφ.continuous_deriv (by simp)).integrable_of_hasCompactSupport hc.deriv
  have htop : Tendsto φ atTop (𝓝 0) := hc.is_zero_at_infty.mono_left atTop_le_cocompact
  have hbot : Tendsto φ atBot (𝓝 0) := hc.is_zero_at_infty.mono_left atBot_le_cocompact
  have hall : ∫ t, deriv φ t = 0 := by
    rw [integral_of_hasDerivAt_of_tendsto hd hint hbot htop, sub_zero]
  have hIoi : ∫ t in Ioi y, deriv φ t = -φ y := by
    rw [integral_Ioi_of_hasDerivAt_of_tendsto' (fun t _ => hd t) hint.integrableOn htop,
      zero_sub]
  have hfun : (fun t => boxSign y t * deriv φ t) =
      fun t => (Ici y).indicator (deriv φ) t - (if y ≤ 0 then 1 else 0) * deriv φ t := by
    funext t
    simp only [boxSign, indicator, mem_Ici, sub_mul]
    split_ifs <;> simp
  rw [hfun, integral_sub (hint.indicator measurableSet_Ici) (hint.const_mul _),
    integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi, hIoi,
    integral_const_mul, hall, mul_zero, sub_zero]

lemma integrable_prod_boxSign_mul {d : ℕ} (y : Fin d → ℝ) {h : (Fin d → ℝ) → ℝ}
    (hh : Continuous h) (hc : HasCompactSupport h) :
    Integrable (fun x : Fin d → ℝ => (∏ i, boxSign (y i) (x i)) * h x) := by
  refine (hh.integrable_of_hasCompactSupport hc).bdd_mul (c := 1) ?_ (ae_of_all _ fun x => ?_)
  · refine (Finset.measurable_prod _ (fun i _ => ?_)).aestronglyMeasurable
    exact measurable_boxSign.comp (measurable_const.prodMk (measurable_pi_apply i))
  · rw [Real.norm_eq_abs, Finset.abs_prod]
    exact Finset.prod_le_one₀ (fun i _ => abs_nonneg _) (fun i _ => abs_boxSign_le _ _)

/-- `d`-fold fundamental theorem of calculus against the product box kernel. -/
theorem integral_prod_boxSign_mul_mixedDeriv : ∀ (d : ℕ) (g : (Fin d → ℝ) → ℝ),
    ContDiff ℝ ∞ g → HasCompactSupport g → ∀ y : Fin d → ℝ,
    ∫ x, (∏ i, boxSign (y i) (x i)) * mixedDeriv d g x = (-1) ^ d * g y
  | 0, g, _, _, y => by
    simp only [Finset.univ_eq_empty, Finset.prod_empty, one_mul, pow_zero, mixedDeriv,
      List.finRange_zero, List.foldr_nil]
    rw [integral_unique]
    have h1 : (volume : Measure (Fin 0 → ℝ)).real univ = 1 := by simp [Measure.real, volume_pi]
    rw [h1, one_smul]
    exact congrArg g (Subsingleton.elim _ _)
  | d + 1, g, hg, hc, y => by
    set H := (List.finRange d).foldr (fun i h => pderiv i.succ h) g with hHdef
    have hHmap : H = ((List.finRange d).map Fin.succ).foldr pderiv g := by
      rw [hHdef, List.foldr_map]
    have hHs : ContDiff ℝ ∞ H := hHmap ▸ contDiff_foldr_pderiv _ hg
    have hHc : HasCompactSupport H := hHmap ▸ hasCompactSupport_foldr_pderiv _ hc
    rw [mixedDeriv_succ]
    set F : (Fin (d + 1) → ℝ) → ℝ := fun x => (∏ i, boxSign (y i) (x i)) * pderiv 0 H x
      with hF
    have hFi : Integrable F :=
      integrable_prod_boxSign_mul y (contDiff_pderiv 0 hHs).continuous
        (hasCompactSupport_pderiv 0 hHc)
    have hmp := (volume_preserving_piFinSuccAbove (fun _ : Fin (d + 1) => ℝ) 0).symm
    have he : ∀ p : ℝ × (Fin d → ℝ),
        (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d + 1) => ℝ) 0).symm p =
          Fin.cons p.1 p.2 := fun p => by
      simp [MeasurableEquiv.piFinSuccAbove]
      try rfl
    have hFi' := (hmp.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)).2 hFi
    change ∫ x, F x = _
    rw [← hmp.integral_comp' F]
    rw [Measure.volume_eq_prod, integral_prod_symm
      (fun p => F ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d + 1) => ℝ) 0).symm p)) hFi']
    have hin : ∀ x' : Fin d → ℝ,
        ∫ t, F ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d + 1) => ℝ) 0).symm (t, x')) =
          (∏ i : Fin d, boxSign (y i.succ) (x' i)) * -(H (Fin.cons (y 0) x')) := by
      intro x'
      have hφs : ContDiff ℝ ∞ (fun u => H (Fin.cons u x')) := hHs.comp (contDiff_finCons_left x')
      have hφc := hasCompactSupport_comp_finCons_left hHc x'
      have hder : ∀ t, pderiv 0 H (Fin.cons t x') = deriv (fun u => H (Fin.cons u x')) t := by
        intro t
        have hcurve : HasDerivAt (fun u : ℝ => (Fin.cons u x' : Fin (d + 1) → ℝ))
            (Pi.single 0 1) t := by
          have h0 := hasDerivAt_update (Fin.cons t x' : Fin (d + 1) → ℝ) 0 t
          convert h0 using 1
          funext u
          simp [Fin.update_cons_zero]
        exact ((hHs.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt t hcurve).deriv.symm
      simp only [he, hF, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, hder]
      rw [← integral_boxSign_mul_deriv (hφs.of_le (by simp)) hφc, ← integral_const_mul]
      congr 1
      funext t
      ring
    simp only [hin]
    have hslice := congrFun (foldr_pderiv_succ_finCons (List.finRange d) hg (y 0))
    simp only [← hHdef] at hslice
    simp only [hslice, mul_neg, integral_neg]
    have ih := integral_prod_boxSign_mul_mixedDeriv d (fun z => g (Fin.cons (y 0) z))
      (hg.comp (contDiff_finCons_right _)) (hasCompactSupport_comp_finCons_right hc _)
      (Fin.tail y)
    simp only [Fin.tail, Fin.cons_self_tail] at ih
    rw [show (fun z => g (Fin.cons (y 0) z)) = fun z => g (Fin.cons (y 0) z) from rfl]
    unfold mixedDeriv at ih
    rw [ih, pow_succ]
    ring


end FTC

section Kernel

lemma boxSign_sq (t a : ℝ) : boxSign t a ^ 2 = (Set.uIoc 0 a).indicator 1 t := by
  unfold boxSign
  simp only [Set.indicator, Set.mem_uIoc, Pi.one_apply]
  by_cases h1 : t ≤ a <;> by_cases h2 : t ≤ 0 <;> simp [h1, h2]

lemma integrable_boxSign_sq (a : ℝ) : Integrable (fun t => boxSign t a ^ 2) := by
  simp_rw [boxSign_sq]
  exact (integrableOn_const (by rw [Real.volume_uIoc]; exact ENNReal.ofReal_ne_top)
    ).integrable_indicator measurableSet_uIoc

lemma integral_boxSign_sq (a : ℝ) : ∫ t, boxSign t a ^ 2 = |a| := by
  simp_rw [boxSign_sq]
  rw [integral_indicator_one measurableSet_uIoc, Measure.real, Real.volume_uIoc, sub_zero,
    ENNReal.toReal_ofReal (abs_nonneg a)]

variable {d : ℕ}

/-- The product box kernel: `boxKernel x` is the signed indicator of the box between `0` and `x`. -/
def boxKernel (x y : Fin d → ℝ) : ℝ := ∏ i, boxSign (y i) (x i)

lemma measurable_boxKernel :
    Measurable (fun p : (Fin d → ℝ) × (Fin d → ℝ) => boxKernel p.1 p.2) :=
  Finset.measurable_prod _ fun i _ => measurable_boxSign.comp
    (f := fun p : (Fin d → ℝ) × (Fin d → ℝ) => (p.2 i, p.1 i)) (by fun_prop)

lemma measurable_boxKernel_left (x : Fin d → ℝ) : Measurable (boxKernel x) :=
  measurable_boxKernel.comp (measurable_const.prodMk measurable_id)

lemma boxKernel_sq (x y : Fin d → ℝ) : boxKernel x y ^ 2 = ∏ i, boxSign (y i) (x i) ^ 2 := by
  rw [boxKernel, Finset.prod_pow]

lemma integrable_boxKernel_sq (x : Fin d → ℝ) : Integrable (fun y => boxKernel x y ^ 2) := by
  simp_rw [boxKernel_sq]
  exact Integrable.fintype_prod (f := fun i t => boxSign t (x i) ^ 2)
    (fun i => integrable_boxSign_sq _)

lemma integral_boxKernel_sq (x : Fin d → ℝ) : ∫ y, boxKernel x y ^ 2 = ∏ i, |x i| := by
  simp_rw [boxKernel_sq]
  rw [integral_fin_nat_prod_volume_eq_prod (fun i t => boxSign t (x i) ^ 2)]
  exact Finset.prod_congr rfl fun i _ => integral_boxSign_sq _

lemma memLp_boxKernel (x : Fin d → ℝ) : MemLp (boxKernel x) 2 (volume : Measure (Fin d → ℝ)) :=
  (memLp_two_iff_integrable_sq (measurable_boxKernel_left x).aestronglyMeasurable).2
    (integrable_boxKernel_sq x)

/-- The box kernel as an element of `L²`. -/
def boxKernelL (x : Fin d → ℝ) : Lp ℝ 2 (volume : Measure (Fin d → ℝ)) :=
  (memLp_boxKernel x).toLp _

lemma norm_boxKernelL_sq (x : Fin d → ℝ) : ‖boxKernelL x‖ ^ 2 = ∏ i, |x i| := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def, ← integral_boxKernel_sq x]
  refine integral_congr_ae ?_
  filter_upwards [(memLp_boxKernel x).coeFn_toLp] with y h
  rw [boxKernelL, h, real_inner_eq_re_inner, RCLike.inner_apply, conj_trivial, sq]
  rfl

section Basis

variable {ι : Type*} (b : HilbertBasis ι ℝ (Lp ℝ 2 (volume : Measure (Fin d → ℝ))))

/-- The coefficient `⟪b k, boxKernelL x⟫`. -/
def kernelCoeff (k : ι) (x : Fin d → ℝ) : ℝ := ⟪b k, boxKernelL x⟫

lemma kernelCoeff_eq_integral (k : ι) (x : Fin d → ℝ) :
    kernelCoeff b k x = ∫ y, (b k : (Fin d → ℝ) → ℝ) y * boxKernel x y := by
  rw [kernelCoeff, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [(memLp_boxKernel x).coeFn_toLp] with y h
  rw [boxKernelL, h, real_inner_eq_re_inner, RCLike.inner_apply, conj_trivial]
  simp [mul_comm]

lemma measurable_kernelCoeff (k : ι) : Measurable (kernelCoeff b k) := by
  have h : kernelCoeff b k = fun x => ∫ y, (b k : (Fin d → ℝ) → ℝ) y * boxKernel x y :=
    funext (kernelCoeff_eq_integral b k)
  rw [h]
  exact (((Lp.stronglyMeasurable (b k)).comp_measurable measurable_snd).mul
    measurable_boxKernel.stronglyMeasurable).integral_prod_right'.measurable

lemma hasSum_kernelCoeff_sq (x : Fin d → ℝ) :
    HasSum (fun k => kernelCoeff b k x ^ 2) (∏ i, |x i|) := by
  have h := b.hasSum_inner_mul_inner (boxKernelL x) (boxKernelL x)
  rw [real_inner_self_eq_norm_sq, norm_boxKernelL_sq] at h
  convert h using 2 with k
  rw [kernelCoeff, real_inner_comm, sq]

lemma kernelCoeff_sq_le (k : ι) (x : Fin d → ℝ) : kernelCoeff b k x ^ 2 ≤ ∏ i, |x i| :=
  le_hasSum (hasSum_kernelCoeff_sq b x) k (fun _ _ => sq_nonneg _)

end Basis

/-- The Gaussian weight `∏ exp (-(x i)²)`. -/
def gaussWeight (x : Fin d → ℝ) : ℝ≥0 := ∏ i, Real.toNNReal (Real.exp (-(x i) ^ 2))

lemma coe_gaussWeight (x : Fin d → ℝ) : (gaussWeight x : ℝ) = ∏ i, Real.exp (-(x i) ^ 2) := by
  rw [gaussWeight, NNReal.coe_prod]
  exact Finset.prod_congr rfl fun i _ => Real.coe_toNNReal _ (Real.exp_pos _).le

lemma measurable_gaussWeight : Measurable (gaussWeight (d := d)) := by
  unfold gaussWeight
  fun_prop

/-- The inverse weight `∏ exp ((x i)²)`. -/
def invWeight (x : Fin d → ℝ) : ℝ := ∏ i, Real.exp ((x i) ^ 2)

lemma gaussWeight_mul_invWeight (x : Fin d → ℝ) : (gaussWeight x : ℝ) * invWeight x = 1 := by
  rw [coe_gaussWeight, invWeight, ← Finset.prod_mul_distrib]
  exact Finset.prod_eq_one fun i _ => by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]

lemma continuous_invWeight : Continuous (invWeight (d := d)) := by
  unfold invWeight
  fun_prop

variable (d) in
/-- The finite Gaussian-weighted measure on `Fin d → ℝ`. -/
def weightMeasure : Measure (Fin d → ℝ) :=
  (volume : Measure (Fin d → ℝ)).withDensity fun x => (gaussWeight x : ℝ≥0∞)

lemma integrable_exp_neg_sq_mul_abs : Integrable (fun t : ℝ => Real.exp (-t ^ 2) * |t|) := by
  have h := (integrable_mul_exp_neg_mul_sq (b := 1) one_pos).abs
  refine h.congr (ae_of_all _ fun t => ?_)
  simp only [abs_mul, Real.abs_exp, neg_mul, one_mul]
  ring

lemma integrable_prod_abs_weightMeasure :
    Integrable (fun x : Fin d → ℝ => ∏ i, |x i|) (weightMeasure d) := by
  rw [weightMeasure, integrable_withDensity_iff_integrable_smul measurable_gaussWeight]
  have h := Integrable.fintype_prod (f := fun (_ : Fin d) t => Real.exp (-t ^ 2) * |t|)
    (fun _ => integrable_exp_neg_sq_mul_abs)
  refine h.congr (ae_of_all _ fun x => ?_)
  simp only [NNReal.smul_def, smul_eq_mul, coe_gaussWeight, Finset.prod_mul_distrib]

instance : IsFiniteMeasure (weightMeasure d) := by
  refine isFiniteMeasure_withDensity ?_
  have h := Integrable.fintype_prod (f := fun (_ : Fin d) (t : ℝ) => Real.exp (-1 * t ^ 2))
    (fun _ => integrable_exp_neg_mul_sq one_pos)
  have h2 : Integrable (fun x : Fin d → ℝ => (gaussWeight x : ℝ)) := by
    refine h.congr (ae_of_all _ fun x => ?_)
    simp [coe_gaussWeight]
  have := h2.hasFiniteIntegral
  rw [hasFiniteIntegral_iff_enorm] at this
  refine ne_of_lt (lt_of_le_of_lt (le_of_eq ?_) this)
  refine lintegral_congr fun x => ?_
  simp [Real.enorm_eq_ofReal (NNReal.coe_nonneg _)]


end Kernel

end EinsteinFull.WhiteNoise
