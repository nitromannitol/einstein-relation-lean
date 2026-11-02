import EinsteinFull.Calculus.S4PathIntegralSupport
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.Martingale.Basic

/-!
# The quadratic-variation bound for solutions of a martingale problem

If `P` solves the martingale problem of `L` and `f ∈ C_c^∞`, then
`E (f (γ t) - f (γ 0) - ∫₀ᵗ L f (γ u) du)² = E ∫₀ᵗ Γ f (γ u) du`, where
`Γ f = L (f²) - 2 f L f`.  Only the martingale property of the compensated test functions
of `f` and `f²` is used.
-/

open MeasureTheory
open scoped NNReal

namespace EinsteinFull
open EinsteinRelation

theorem continuous_path_coord {d : ℕ} (u : ℝ≥0) : Continuous fun γ : Path d => γ u :=
  continuous_eval_const u

/-- Martingale increments are orthogonal to bounded functions of the past. -/
theorem integral_martingale_mul_coord {d : ℕ} {P : Measure (Path d)} [IsProbabilityMeasure P]
    {M : ℝ≥0 → Path d → ℝ} (hM : Martingale M (pathFiltration d) P)
    {g : Vec d → ℝ} (hg : Continuous g) {K : ℝ} (hK : ∀ y, |g y| ≤ K) {u t : ℝ≥0} (hut : u ≤ t) :
    ∫ γ, M t γ * g (γ u) ∂P = ∫ γ, M u γ * g (γ u) ∂P := by
  have hG : StronglyMeasurable[pathFiltration d u] (fun γ : Path d => g (γ u)) := by
    rw [pathFiltration_eq_canonical]
    exact hg.comp_stronglyMeasurable
      (MarkovProcess.ContinuousPath.measurable_coordinateProcess_canonicalFiltration
        (alpha := Vec d) u).stronglyMeasurable
  have hGm : StronglyMeasurable (fun γ : Path d => g (γ u)) :=
    (hg.comp (continuous_path_coord u)).stronglyMeasurable
  have hMt : Integrable (M t) P := hM.integrable t
  have hGM : Integrable ((fun γ : Path d => g (γ u)) * M t) P :=
    hMt.bdd_mul hGm.aestronglyMeasurable (ae_of_all _ fun γ => by
      rw [Real.norm_eq_abs]; exact hK _)
  calc ∫ γ, M t γ * g (γ u) ∂P
      = ∫ γ, ((fun γ : Path d => g (γ u)) * M t) γ ∂P := by
        refine integral_congr_ae (ae_of_all _ fun γ => ?_)
        simp only [Pi.mul_apply]
        ring
    _ = ∫ γ, (P[(fun γ : Path d => g (γ u)) * M t | pathFiltration d u]) γ ∂P :=
        (integral_condExp ((pathFiltration d).le u)).symm
    _ = ∫ γ, ((fun γ : Path d => g (γ u)) * P[M t | pathFiltration d u]) γ ∂P :=
        integral_congr_ae (condExp_mul_of_stronglyMeasurable_left hG hGM hMt)
    _ = ∫ γ, M u γ * g (γ u) ∂P := by
        refine integral_congr_ae ?_
        filter_upwards [hM.2 u t hut] with γ hγ
        simp only [Pi.mul_apply, hγ]
        ring

/-- The cross term `E[M_t ∫₀ᵗ g(γ_s) ds] = E ∫₀ᵗ M_s g(γ_s) ds` for a continuous bounded
martingale. -/
theorem integral_martingale_mul_pathInt {d : ℕ} {P : Measure (Path d)} [IsProbabilityMeasure P]
    {M : ℝ≥0 → Path d → ℝ} (hM : Martingale M (pathFiltration d) P)
    (hMc : Continuous fun p : Path d × ℝ => M p.2.toNNReal p.1)
    {g : Vec d → ℝ} (hg : Continuous g) {K C : ℝ} (hK : ∀ y, |g y| ≤ K) {t : ℝ≥0}
    (hC : ∀ s ≤ t, ∀ γ, |M s γ| ≤ C) :
    ∫ γ, M t γ * pathInt g γ t ∂P =
      ∫ γ, (∫ s in (0 : ℝ)..t, M s.toNNReal γ * g (γ s.toNNReal)) ∂P := by
  have ht0 : (0 : ℝ) ≤ t := t.coe_nonneg
  haveI hfin : IsFiniteMeasure (volume.restrict (Set.uIoc (0 : ℝ) t)) := by
    rw [Set.uIoc_of_le ht0]
    infer_instance
  have hMt : ∀ s : ℝ≥0, Continuous (M s) := fun s =>
    (hMc.comp (continuous_id.prodMk (continuous_const : Continuous fun _ : Path d => (s : ℝ)))).congr
      (fun γ => by simp)
  have hev : Continuous fun p : ℝ × Path d => p.2 p.1.toNNReal :=
    (continuous_pathEval d).comp (continuous_snd.prodMk continuous_fst)
  have hcont1 : Continuous fun p : ℝ × Path d => M t p.2 * g (p.2 p.1.toNNReal) :=
    ((hMt t).comp continuous_snd).mul (hg.comp hev)
  have hcont2 : Continuous fun p : ℝ × Path d => M p.1.toNNReal p.2 * g (p.2 p.1.toNNReal) :=
    (hMc.comp (continuous_snd.prodMk continuous_fst)).mul (hg.comp hev)
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC t le_rfl 0)
  have hint1 : Integrable (Function.uncurry fun (s : ℝ) (γ : Path d) =>
      M t γ * g (γ s.toNNReal)) ((volume.restrict (Set.uIoc (0 : ℝ) t)).prod P) := by
    refine Integrable.of_bound hcont1.aestronglyMeasurable (C * K) (ae_of_all _ ?_)
    intro p
    show ‖M t p.2 * g (p.2 p.1.toNNReal)‖ ≤ C * K
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hC t le_rfl _) (hK _) (abs_nonneg _) hC0
  have hint2 : Integrable (Function.uncurry fun (s : ℝ) (γ : Path d) =>
      M s.toNNReal γ * g (γ s.toNNReal)) ((volume.restrict (Set.uIoc (0 : ℝ) t)).prod P) := by
    refine Integrable.of_bound hcont2.aestronglyMeasurable (C * K) ?_
    have hS : ∀ᵐ s ∂(volume.restrict (Set.uIoc (0 : ℝ) t)), s.toNNReal ≤ t := by
      refine (ae_restrict_iff' measurableSet_uIoc).2 (ae_of_all _ fun s hs => ?_)
      rw [Set.uIoc_of_le ht0] at hs
      exact Real.toNNReal_le_iff_le_coe.mpr hs.2
    rw [Measure.ae_prod_iff_ae_ae]
    · filter_upwards [hS] with s hs
      refine ae_of_all _ fun γ => ?_
      show ‖M s.toNNReal γ * g (γ s.toNNReal)‖ ≤ C * K
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hC _ hs _) (hK _) (abs_nonneg _) hC0
    · exact measurableSet_le (hcont2.norm.measurable) measurable_const
  calc ∫ γ, M t γ * pathInt g γ t ∂P
      = ∫ γ, (∫ s in (0 : ℝ)..t, M t γ * g (γ s.toNNReal)) ∂P := by
        refine integral_congr_ae (ae_of_all _ fun γ => ?_)
        show M t γ * pathInt g γ t = ∫ s in (0 : ℝ)..t, M t γ * g (γ s.toNNReal)
        rw [intervalIntegral.integral_const_mul]
        rfl
    _ = ∫ s in (0 : ℝ)..t, ∫ γ, M t γ * g (γ s.toNNReal) ∂P :=
        (intervalIntegral_integral_swap hint1).symm
    _ = ∫ s in (0 : ℝ)..t, ∫ γ, M s.toNNReal γ * g (γ s.toNNReal) ∂P := by
        refine intervalIntegral.integral_congr fun s hs => ?_
        rw [Set.uIcc_of_le ht0] at hs
        exact integral_martingale_mul_coord hM hg hK (Real.toNNReal_le_iff_le_coe.mpr hs.2)
    _ = ∫ γ, (∫ s in (0 : ℝ)..t, M s.toNNReal γ * g (γ s.toNNReal)) ∂P :=
        intervalIntegral_integral_swap hint2

/-- Continuity of the compensated test function in `(γ, s)`. -/
theorem continuous_compensatedTest {d : ℕ} {L : (Vec d → ℝ) → Vec d → ℝ} {φ : Vec d → ℝ}
    (hφ : Continuous φ) (hL : Continuous (L φ)) :
    Continuous fun p : Path d × ℝ => compensatedTest L φ p.2.toNNReal p.1 := by
  show Continuous fun p : Path d × ℝ =>
    φ (p.1 p.2.toNNReal) - φ (p.1 0) - pathInt (L φ) p.1 ((p.2.toNNReal : ℝ))
  exact ((hφ.comp (continuous_pathEval d)).sub
    (hφ.comp ((continuous_path_coord 0).comp continuous_fst))).sub
    ((continuous_pathInt_prod hL).comp (continuous_fst.prodMk
      (NNReal.continuous_coe.comp (continuous_real_toNNReal.comp continuous_snd))))

theorem abs_compensatedTest_le {d : ℕ} {L : (Vec d → ℝ) → Vec d → ℝ} {φ : Vec d → ℝ} {C K : ℝ}
    (hφ : ∀ y, |φ y| ≤ C) (hL : ∀ y, |L φ y| ≤ K) (s : ℝ≥0) (γ : Path d) :
    |compensatedTest L φ s γ| ≤ 2 * C + K * s := by
  rw [compensatedTest_eq]
  have h1 := abs_sub (φ (γ s) - φ (γ 0)) (pathInt (L φ) γ (s : ℝ))
  have h2 := abs_sub (φ (γ s)) (φ (γ 0))
  have h3 := abs_pathInt_le hL γ (t := (s : ℝ)) s.coe_nonneg
  have h4 := hφ (γ s)
  have h5 := hφ (γ 0)
  linarith

theorem integrable_of_continuous_bounded {d : ℕ} {P : Measure (Path d)} [IsFiniteMeasure P]
    {φ : Path d → ℝ} (hc : Continuous φ) {C : ℝ} (hC : ∀ γ, |φ γ| ≤ C) : Integrable φ P :=
  Integrable.of_bound hc.aestronglyMeasurable C (ae_of_all _ fun γ => by
    rw [Real.norm_eq_abs]; exact hC γ)

/-- **Quadratic-variation bound.** -/
theorem integral_sq_compensatedTest_le {d : ℕ} {L : (Vec d → ℝ) → Vec d → ℝ}
    {P : Measure (Path d)} (hP : SolvesMartingaleProblem L 0 P)
    {f : Vec d → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfc : HasCompactSupport f)
    {K K2 : ℝ} (hK : ∀ y, |L f y| ≤ K) (hLc : Continuous (L f))
    (hK2 : ∀ y, |L (fun z => f z ^ 2) y| ≤ K2) (hL2c : Continuous (L fun z => f z ^ 2))
    {B : ℝ} (hB : ∀ y, L (fun z => f z ^ 2) y - 2 * f y * L f y ≤ B) (t : ℝ≥0) :
    ∫ γ, compensatedTest L f t γ ^ 2 ∂P ≤ B * t := by
  obtain ⟨hprob, h0, hmp⟩ := hP
  haveI := hprob
  have hfcont : Continuous f := hf.continuous
  obtain ⟨Cf, hCf⟩ := hfcont.bounded_above_of_compact_support hfc
  have hCf' : ∀ y, |f y| ≤ Cf := fun y => by
    have := hCf y
    rwa [Real.norm_eq_abs] at this
  have hf2 : ContDiff ℝ (⊤ : ℕ∞) (fun z => f z ^ 2) := hf.pow 2
  have hfc2 : HasCompactSupport (fun z => f z ^ 2) :=
    hfc.comp_left (g := fun x : ℝ => x ^ 2) (by simp)
  obtain ⟨-, hMint, hMart⟩ := hmp f hf hfc
  obtain ⟨-, hNint, hNart⟩ := hmp _ hf2 hfc2
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (hK 0)
  have hf2c : Continuous fun z => f z ^ 2 := hfcont.pow 2
  have hT0 : (0 : ℝ) ≤ t := t.coe_nonneg
  have hTt : (t : ℝ).toNNReal = t := Real.toNNReal_coe
  -- notation
  have hΓc : Continuous fun y => L (fun z => f z ^ 2) y - 2 * f y * L f y :=
    hL2c.sub ((continuous_const.mul hfcont).mul hLc)
  -- boundedness / continuity of the pieces
  have hMc := continuous_compensatedTest (L := L) hfcont hLc
  have hMb := abs_compensatedTest_le (L := L) hCf' hK
  have hMt : Continuous (compensatedTest L f t) :=
    (hMc.comp (continuous_id.prodMk (continuous_const : Continuous fun _ : Path d => (t : ℝ)))).congr
      (fun γ => by simp)
  have hAc : Continuous fun γ : Path d => pathInt (L f) γ (t : ℝ) :=
    continuous_pathInt_path hLc _
  have hAb : ∀ γ : Path d, |pathInt (L f) γ (t : ℝ)| ≤ K * t := fun γ =>
    abs_pathInt_le hK γ hT0
  have hMtb : ∀ γ, |compensatedTest L f t γ| ≤ 2 * Cf + K * t := hMb t
  -- the cross term
  have hcross := integral_martingale_mul_pathInt (P := P) hMart hMc hLc hK
    (C := 2 * Cf + K * t) (t := t) (fun s hs γ => by
      refine (hMb s γ).trans ?_
      have hst : (s : ℝ) ≤ t := hs
      have := mul_le_mul_of_nonneg_left hst hK0
      linarith)
  -- pointwise identity
  have hid : ∀ γ : Path d,
      compensatedTest L f t γ ^ 2 =
        compensatedTest L (fun z => f z ^ 2) t γ -
          2 * (compensatedTest L f t γ * pathInt (L f) γ (t : ℝ)) -
          2 * (f (γ 0) * compensatedTest L f t γ) +
          2 * (∫ s in (0 : ℝ)..t, compensatedTest L f s.toNNReal γ * L f (γ s.toNNReal)) +
          pathInt (fun y => L (fun z => f z ^ 2) y - 2 * f y * L f y) γ (t : ℝ) := by
    intro γ
    have h := pathwise_square_identity hfcont hLc hL2c γ (t : ℝ)
    rw [hTt] at h
    have hE : ∫ s in (0 : ℝ)..t, compensatedTest L f s.toNNReal γ * L f (γ s.toNNReal) =
        ∫ s in (0 : ℝ)..t, (f (γ s.toNNReal) - f (γ 0) - pathInt (L f) γ s) *
          L f (γ s.toNNReal) := by
      refine intervalIntegral.integral_congr fun s hs => ?_
      rw [Set.uIcc_of_le hT0] at hs
      show (f (γ s.toNNReal) - f (γ 0) - pathInt (L f) γ ((s.toNNReal : ℝ≥0) : ℝ)) *
          L f (γ s.toNNReal) = _
      rw [Real.coe_toNNReal s hs.1]
    have hN : compensatedTest L (fun z => f z ^ 2) t γ =
        f (γ t) ^ 2 - f (γ 0) ^ 2 - pathInt (L fun z => f z ^ 2) γ (t : ℝ) := rfl
    have hM : compensatedTest L f t γ = f (γ t) - f (γ 0) - pathInt (L f) γ (t : ℝ) := rfl
    rw [hE, hN, hM]
    linarith [h]
  -- integrability of the pieces
  have hCf0 : 0 ≤ Cf := (abs_nonneg _).trans (hCf' 0)
  have hB0 : 0 ≤ 2 * Cf + K * t := by
    have := mul_nonneg hK0 hT0
    linarith
  have iN : Integrable (compensatedTest L (fun z => f z ^ 2) t) P := hNint t
  have iMA : Integrable (fun γ => compensatedTest L f t γ * pathInt (L f) γ (t : ℝ)) P :=
    integrable_of_continuous_bounded (hMt.mul hAc) (C := (2 * Cf + K * t) * (K * t)) fun γ => by
      rw [abs_mul]
      exact mul_le_mul (hMtb γ) (hAb γ) (abs_nonneg _) hB0
  have ifM : Integrable (fun γ : Path d => f (γ 0) * compensatedTest L f t γ) P :=
    integrable_of_continuous_bounded ((hfcont.comp (continuous_path_coord 0)).mul hMt)
      (C := Cf * (2 * Cf + K * t)) fun γ => by
      rw [abs_mul]
      exact mul_le_mul (hCf' _) (hMtb γ) (abs_nonneg _) hCf0
  have hE4c : Continuous fun γ : Path d =>
      ∫ s in (0 : ℝ)..t, compensatedTest L f s.toNNReal γ * L f (γ s.toNNReal) := by
    have hu : Continuous (Function.uncurry fun (γ : Path d) (s : ℝ) =>
        compensatedTest L f s.toNNReal γ * L f (γ s.toNNReal)) :=
      hMc.mul (hLc.comp (continuous_pathEval d))
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hu 0 t
  have iE4 : Integrable (fun γ : Path d =>
      ∫ s in (0 : ℝ)..t, compensatedTest L f s.toNNReal γ * L f (γ s.toNNReal)) P :=
    integrable_of_continuous_bounded hE4c (C := (2 * Cf + K * t) * K * t) fun γ => by
      have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := (t : ℝ))
        (C := (2 * Cf + K * t) * K)
        (f := fun s : ℝ => compensatedTest L f s.toNNReal γ * L f (γ s.toNNReal))
        (fun s hs => by
          rw [Set.uIoc_of_le hT0] at hs
          have hst : s.toNNReal ≤ t := Real.toNNReal_le_iff_le_coe.mpr hs.2
          rw [Real.norm_eq_abs, abs_mul]
          refine mul_le_mul ((hMb _ γ).trans ?_) (hK _) (abs_nonneg _) hB0
          have hst' : ((s.toNNReal : ℝ≥0) : ℝ) ≤ t := hst
          have := mul_le_mul_of_nonneg_left hst' hK0
          linarith)
      rw [Real.norm_eq_abs, sub_zero, abs_of_nonneg hT0] at h
      linarith
  have hΓb : ∀ y, |L (fun z => f z ^ 2) y - 2 * f y * L f y| ≤ K2 + 2 * Cf * K := fun y => by
    have h1 := abs_sub (L (fun z => f z ^ 2) y) (2 * f y * L f y)
    have h2 : |2 * f y * L f y| ≤ 2 * Cf * K := by
      rw [abs_mul, abs_mul, abs_two]
      exact mul_le_mul (mul_le_mul_of_nonneg_left (hCf' y) (by norm_num)) (hK y) (abs_nonneg _)
        (by linarith)
    linarith [hK2 y]
  have iE5 : Integrable (fun γ : Path d =>
      pathInt (fun y => L (fun z => f z ^ 2) y - 2 * f y * L f y) γ (t : ℝ)) P :=
    integrable_of_continuous_bounded (continuous_pathInt_path hΓc _)
      (C := (K2 + 2 * Cf * K) * t) fun γ => abs_pathInt_le hΓb γ hT0
  -- expectations
  have hz : ∀ φ : Vec d → ℝ, ∀ γ : Path d, compensatedTest L φ 0 γ = 0 := fun φ γ => by
    simp [compensatedTest]
  have hN0 : ∫ γ, compensatedTest L (fun z => f z ^ 2) t γ ∂P = 0 := by
    have := hNart.setIntegral_eq (zero_le (a := t)) MeasurableSet.univ
    rw [setIntegral_univ, setIntegral_univ] at this
    simp only [hz, integral_zero] at this
    exact this.symm
  have hM0 : ∫ γ, compensatedTest L f t γ ∂P = 0 := by
    have := hMart.setIntegral_eq (zero_le (a := t)) MeasurableSet.univ
    rw [setIntegral_univ, setIntegral_univ] at this
    simp only [hz, integral_zero] at this
    exact this.symm
  have hf0M : ∫ γ, f (γ 0) * compensatedTest L f t γ ∂P = 0 := by
    have : ∫ γ, f (γ 0) * compensatedTest L f t γ ∂P =
        ∫ γ, f 0 * compensatedTest L f t γ ∂P := by
      refine integral_congr_ae ?_
      filter_upwards [h0] with γ hγ
      rw [hγ]
    rw [this, integral_const_mul, hM0, mul_zero]
  have hsplit : ∫ γ, compensatedTest L f t γ ^ 2 ∂P =
      ∫ γ, pathInt (fun y => L (fun z => f z ^ 2) y - 2 * f y * L f y) γ (t : ℝ) ∂P := by
    have i1 : Integrable (fun γ => compensatedTest L (fun z => f z ^ 2) t γ -
        2 * (compensatedTest L f t γ * pathInt (L f) γ (t : ℝ))) P := iN.sub (iMA.const_mul 2)
    have i2 : Integrable (fun γ => compensatedTest L (fun z => f z ^ 2) t γ -
        2 * (compensatedTest L f t γ * pathInt (L f) γ (t : ℝ)) -
        2 * (f (γ 0) * compensatedTest L f t γ)) P := i1.sub (ifM.const_mul 2)
    have i3 : Integrable (fun γ => compensatedTest L (fun z => f z ^ 2) t γ -
        2 * (compensatedTest L f t γ * pathInt (L f) γ (t : ℝ)) -
        2 * (f (γ 0) * compensatedTest L f t γ) +
        2 * (∫ s in (0 : ℝ)..t, compensatedTest L f s.toNNReal γ * L f (γ s.toNNReal))) P :=
      i2.add (iE4.const_mul 2)
    rw [integral_congr_ae (ae_of_all _ hid), integral_add i3 iE5, integral_add i2 (iE4.const_mul 2),
      integral_sub i1 (ifM.const_mul 2), integral_sub iN (iMA.const_mul 2), integral_const_mul,
      integral_const_mul, integral_const_mul, hN0, hf0M, hcross]
    ring
  rw [hsplit]
  have hle : ∫ γ, pathInt (fun y => L (fun z => f z ^ 2) y - 2 * f y * L f y) γ (t : ℝ) ∂P ≤
      ∫ γ, B * t ∂P := by
    refine integral_mono iE5 (integrable_const _) fun γ => ?_
    unfold pathInt
    have := intervalIntegral.integral_mono_on hT0
      ((hΓc.comp (γ.continuous.comp continuous_real_toNNReal)).intervalIntegrable _ _)
      (intervalIntegrable_const (μ := volume) (c := B)) (fun s _ => hB (γ s.toNNReal))
    simp only [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at this
    exact le_of_le_of_eq this (mul_comm _ _)
  refine hle.trans ?_
  simp

end EinsteinFull
