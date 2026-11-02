import EinsteinFull.Calculus.ParabolicBridgeTcv

/-!
# Slices of the mollified function

Product test functions `ψ(x) k(s)` and the weak spatial derivative of every time slice of the
delayed mollification of an extended function.
-/

open scoped ENNReal

noncomputable section
namespace EinsteinFull.ParabolicBridge

open MeasureTheory Set Filter Topology PDE

variable {d : ℕ} {ε : ℝ} {hε : 0 < ε}

theorem tsupport_prod_mul_subset (f : Vec d → ℝ) (g : ℝ → ℝ) :
    tsupport (fun z : Vec d × ℝ => f z.1 * g z.2) ⊆ tsupport f ×ˢ tsupport g := by
  refine closure_minimal ?_ ((isClosed_tsupport f).prod (isClosed_tsupport g))
  intro z hz
  have h1 : f z.1 ≠ 0 := left_ne_zero_of_mul hz
  have h2 : g z.2 ≠ 0 := right_ne_zero_of_mul hz
  exact ⟨subset_tsupport f h1, subset_tsupport g h2⟩

theorem hasCompactSupport_prod_mul (f : Vec d → ℝ) (g : ℝ → ℝ) (hf : HasCompactSupport f)
    (hg : HasCompactSupport g) : HasCompactSupport (fun z : Vec d × ℝ => f z.1 * g z.2) :=
  (hf.prod hg).of_isClosed_subset (isClosed_tsupport _) (tsupport_prod_mul_subset f g)

theorem fderiv_prod_mul_fst (f : Vec d → ℝ) (g : ℝ → ℝ) (hf : Differentiable ℝ f)
    (hg : Differentiable ℝ g) (z : Vec d × ℝ) (v : Vec d) :
    fderiv ℝ (fun w : Vec d × ℝ => f w.1 * g w.2) z (v, 0) = g z.2 * fderiv ℝ f z.1 v := by
  have h1 : HasFDerivAt (fun w : Vec d × ℝ => f w.1)
      ((fderiv ℝ f z.1).comp (ContinuousLinearMap.fst ℝ (Vec d) ℝ)) z :=
    (hf z.1).hasFDerivAt.comp z (hasFDerivAt_fst)
  have h2 : HasFDerivAt (fun w : Vec d × ℝ => g w.2)
      ((fderiv ℝ g z.2).comp (ContinuousLinearMap.snd ℝ (Vec d) ℝ)) z :=
    (hg z.2).hasFDerivAt.comp z (hasFDerivAt_snd)
  have h3 := h1.mul h2
  have h4 : fderiv ℝ (fun w : Vec d × ℝ => f w.1 * g w.2) z =
      f z.1 • (fderiv ℝ g z.2).comp (ContinuousLinearMap.snd ℝ (Vec d) ℝ) +
        g z.2 • (fderiv ℝ f z.1).comp (ContinuousLinearMap.fst ℝ (Vec d) ℝ) := h3.fderiv
  rw [h4]
  simp

theorem ker_contDiff : ContDiff ℝ (⊤ : ℕ∞) (ker ε hε) :=
  tmoll_contDiff.comp (contDiff_id.sub contDiff_const)

/-- The time kernel `s ↦ ker (t - s)`. -/
theorem kerAt_contDiff (t : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (fun s => ker ε hε (t - s)) :=
  ker_contDiff.comp (contDiff_const.sub contDiff_id)

theorem tsupport_kerAt_subset (t : ℝ) :
    tsupport (fun s => ker ε hε (t - s)) ⊆ Icc (t - 3 * ε) (t - ε) := by
  refine closure_minimal ?_ isClosed_Icc
  intro s hs
  have h : ¬ (t - s ≤ ε ∨ 3 * ε ≤ t - s) := fun h => hs (ker_eq_zero h)
  push_neg at h
  constructor <;> linarith [h.1, h.2]

theorem kerAt_hasCompactSupport (t : ℝ) :
    HasCompactSupport (fun s => ker ε hε (t - s)) :=
  isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) (tsupport_kerAt_subset t)

theorem setIntegral_prod_slice {U : Set (Vec d)} {J : Set ℝ}
    (h : Vec d × ℝ → ℝ) (hh : IntegrableOn h (U ×ˢ J) volume)
    (κ : ℝ → ℝ) (hκ : Continuous κ) {B : ℝ} (hκb : ∀ s, |κ s| ≤ B)
    (f : Vec d → ℝ) (hf : Continuous f) {C : ℝ} (hfb : ∀ x, |f x| ≤ C) :
    ∫ z in U ×ˢ J, h z * (κ z.2 * f z.1) = ∫ x in U, f x * ∫ s in J, κ s * h (x, s) := by
  have hg : IntegrableOn (fun z : Vec d × ℝ => h z * (κ z.2 * f z.1)) (U ×ˢ J) volume := by
    refine Integrable.mul_bdd (c := B * C) hh ?_ ?_
    · exact ((hκ.comp continuous_snd).mul (hf.comp continuous_fst)).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun z => ?_
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      exact mul_le_mul (hκb _) (hfb _) (abs_nonneg _) ((abs_nonneg _).trans (hκb 0))
  have hg' := hg
  rw [Measure.volume_eq_prod] at hg'
  rw [Measure.volume_eq_prod, setIntegral_prod _ hg']
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  show ∫ s in J, h (x, s) * (κ (x, s).2 * f (x, s).1) = f x * ∫ s in J, κ s * h (x, s)
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
  show h (x, s) * (κ s * f x) = f x * (κ s * h (x, s))
  ring

theorem MolS_indicator_eq (U : Set (Vec d)) (J : Set ℝ) (hJ : MeasurableSet J)
    (V : Vec d × ℝ → ℝ) (x : Vec d) (hx : x ∈ U) (t : ℝ)
    (hker : ∀ s, s ∉ J → ker ε hε (t - s) = 0) :
    MolS ε hε ((U ×ˢ J).indicator V) (x, t) = ∫ s in J, ker ε hε (t - s) * V (x, s) := by
  have h0 := MolS_eq (ε := ε) (hε := hε) ((U ×ˢ J).indicator V) (x, t)
  dsimp only at h0
  rw [h0]
  have h1 : ∫ s, ker ε hε (t - s) * (U ×ˢ J).indicator V (x, s) =
      ∫ s in J, ker ε hε (t - s) * (U ×ˢ J).indicator V (x, s) :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero (fun s hs => by
      rw [hker s hs, zero_mul])).symm
  refine h1.trans (setIntegral_congr_fun hJ fun s hs => ?_)
  show ker ε hε (t - s) * (U ×ˢ J).indicator V (x, s) = ker ε hε (t - s) * V (x, s)
  rw [Set.indicator_of_mem (show (x, s) ∈ U ×ˢ J from ⟨hx, hs⟩)]

/-- Pairing of the cylinder integral with a product test function against the time slice of the
delayed mollification. -/
theorem slice_pairing (U : Set (Vec d)) (hU : MeasurableSet U) (J : Set ℝ) (hJ : MeasurableSet J)
    (t : ℝ) (hker : ∀ s, s ∉ J → ker ε hε (t - s) = 0) (F : Vec d × ℝ → ℝ)
    (hF : IntegrableOn F (U ×ˢ J) volume) (f : Vec d → ℝ) (hf : Continuous f)
    (hcf : HasCompactSupport f) :
    ∫ z in U ×ˢ J, F z * (ker ε hε (t - z.2) * f z.1) =
      ∫ x in U, MolS ε hε ((U ×ˢ J).indicator F) (x, t) * f x := by
  obtain ⟨B, hB0, hB⟩ := ker_bound (ε := ε) (hε := hε)
  obtain ⟨C, hC⟩ := hf.bounded_above_of_compact_support hcf
  have hκ : Continuous fun s => ker ε hε (t - s) :=
    (ker_continuous (ε := ε) (hε := hε)).comp' (continuous_const.sub continuous_id)
  have hκb : ∀ s, |ker ε hε (t - s)| ≤ B := fun s => hB (t - s)
  have hfb : ∀ x, |f x| ≤ C := fun x => by
    have := hC x
    rwa [Real.norm_eq_abs] at this
  have h1 : ∫ z in U ×ˢ J, F z * (ker ε hε (t - z.2) * f z.1) =
      ∫ x in U, f x * ∫ s in J, ker ε hε (t - s) * F (x, s) :=
    setIntegral_prod_slice (κ := fun s => ker ε hε (t - s)) (B := B) (C := C) F hF hκ hκb f hf hfb
  rw [h1]
  refine setIntegral_congr_fun hU fun x hx => ?_
  show f x * ∫ s in J, ker ε hε (t - s) * F (x, s) =
    MolS ε hε ((U ×ˢ J).indicator F) (x, t) * f x
  rw [MolS_indicator_eq U J hJ F x hx t hker, mul_comm]

theorem prodTest_contDiff (ψ : Vec d → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (t : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun z : Vec d × ℝ => ψ z.1 * ker ε hε (t - z.2)) :=
  (hψ.comp contDiff_fst).mul ((kerAt_contDiff t).comp contDiff_snd)

theorem prodTest_hasCompactSupport (ψ : Vec d → ℝ) (hcψ : HasCompactSupport ψ) (t : ℝ) :
    HasCompactSupport (fun z : Vec d × ℝ => ψ z.1 * ker ε hε (t - z.2)) :=
  hasCompactSupport_prod_mul ψ (fun s => ker ε hε (t - s)) hcψ (kerAt_hasCompactSupport t)

theorem prodTest_tsupport_subset (U : Set (Vec d)) (b e t : ℝ) (ht : b + 3 * ε < t ∧ t ≤ e)
    (ψ : Vec d → ℝ) (hsub : tsupport ψ ⊆ U) :
    tsupport (fun z : Vec d × ℝ => ψ z.1 * ker ε hε (t - z.2)) ⊆ U ×ˢ Ioo b e := by
  refine (tsupport_prod_mul_subset ψ (fun s => ker ε hε (t - s))).trans
    (Set.prod_mono hsub ?_)
  refine (tsupport_kerAt_subset t).trans ?_
  intro s hs
  exact ⟨by linarith [hs.1, ht.1], by linarith [hs.2, ht.2, hε]⟩

theorem prodTest_fderiv (ψ : Vec d → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (t : ℝ)
    (z : Vec d × ℝ) (v : Vec d) :
    fderiv ℝ (fun w : Vec d × ℝ => ψ w.1 * ker ε hε (t - w.2)) z (v, 0) =
      ker ε hε (t - z.2) * fderiv ℝ ψ z.1 v :=
  fderiv_prod_mul_fst ψ (fun s => ker ε hε (t - s)) (hψ.differentiable (by simp))
    ((kerAt_contDiff t).differentiable (by simp)) z v

/-- The weak spatial derivative of a time slice of the delayed mollification. -/
theorem slice_weakPartial (U : Set (Vec d)) (hU : IsOpen U) (b e t : ℝ)
    (ht : b + 3 * ε < t ∧ t ≤ e) (V G : Vec d × ℝ → ℝ)
    (hV : IntegrableOn V (U ×ˢ Ioo b e) volume) (hG : IntegrableOn G (U ×ˢ Ioo b e) volume)
    (i : Fin d)
    (H1 : ∀ φ : Vec d × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ U ×ˢ Ioo b e →
      ∫ z in U ×ˢ Ioo b e, V z * fderiv ℝ φ z (basisVec i, 0) =
        -∫ z in U ×ˢ Ioo b e, G z * φ z) :
    HasWeakPartialDerivOn U i (fun x => MolS ε hε ((U ×ˢ Ioo b e).indicator V) (x, t))
      (fun x => MolS ε hε ((U ×ˢ Ioo b e).indicator G) (x, t)) := by
  intro ψ hψ hcψ hsub
  have hker : ∀ s, s ∉ Ioo b e → ker ε hε (t - s) = 0 := by
    intro s hs
    apply ker_eq_zero
    simp only [mem_Ioo, not_and_or, not_lt] at hs
    rcases hs with hs | hs
    · right; linarith [ht.1]
    · left; linarith [ht.2, hε]
  have hfc : Continuous fun x => fderiv ℝ ψ x (basisVec i) :=
    (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hcf : HasCompactSupport fun x => fderiv ℝ ψ x (basisVec i) :=
    (hcψ.fderiv ℝ).comp_left (g := fun L : Vec d →L[ℝ] ℝ => L (basisVec i)) (by simp)
  have hmain := H1 (fun z : Vec d × ℝ => ψ z.1 * ker ε hε (t - z.2))
    (prodTest_contDiff ψ hψ t) (prodTest_hasCompactSupport ψ hcψ t)
    (prodTest_tsupport_subset U b e t ht ψ hsub)
  have e1 : ∫ z in U ×ˢ Ioo b e,
      V z * fderiv ℝ (fun w : Vec d × ℝ => ψ w.1 * ker ε hε (t - w.2)) z (basisVec i, 0) =
      ∫ z in U ×ˢ Ioo b e, V z * (ker ε hε (t - z.2) * fderiv ℝ ψ z.1 (basisVec i)) :=
    integral_congr_ae (Filter.Eventually.of_forall fun z => by
      simp only [prodTest_fderiv ψ hψ t z (basisVec i)])
  have e2 : ∫ z in U ×ˢ Ioo b e, G z * (ψ z.1 * ker ε hε (t - z.2)) =
      ∫ z in U ×ˢ Ioo b e, G z * (ker ε hε (t - z.2) * ψ z.1) :=
    integral_congr_ae (Filter.Eventually.of_forall fun z => by beta_reduce; ring)
  rw [e1, e2, slice_pairing U hU.measurableSet (Ioo b e) measurableSet_Ioo t hker V hV _ hfc hcf,
    slice_pairing U hU.measurableSet (Ioo b e) measurableSet_Ioo t hker G hG ψ hψ.continuous hcψ]
    at hmain
  exact hmain

end EinsteinFull.ParabolicBridge
