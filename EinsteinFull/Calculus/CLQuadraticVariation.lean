import EinsteinFull.Calculus.S4MartingaleVarianceSupport
import EinsteinFull.Calculus.S4MartingaleSllnSupport

/-!
# The quadratic variation of compensated test functions

For a compactly supported smooth test function, the second moment of its compensated process is
the expected time integral of the carré du champ `L (f²) - 2 f L f`.
-/

open MeasureTheory Filter
open scoped BigOperators NNReal Topology ENNReal

namespace EinsteinFull
open EinsteinRelation

variable {d : ℕ}

/-- The second moment of a compensated test function is the expected time integral of its
carré du champ. -/
theorem integral_sq_compensatedTest_eq {d : ℕ} {L : (Vec d → ℝ) → Vec d → ℝ}
    {P : Measure (Path d)} (hP : SolvesMartingaleProblem L 0 P)
    {f : Vec d → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfc : HasCompactSupport f)
    {K K2 : ℝ} (hK : ∀ y, |L f y| ≤ K) (hLc : Continuous (L f))
    (hK2 : ∀ y, |L (fun z => f z ^ 2) y| ≤ K2) (hL2c : Continuous (L fun z => f z ^ 2))
    (t : ℝ≥0) :
    ∫ γ, compensatedTest L f t γ ^ 2 ∂P =
      ∫ γ, pathInt (fun y => L (fun z => f z ^ 2) y - 2 * f y * L f y) γ (t : ℝ) ∂P := by
  obtain ⟨hprob, h0, hmp⟩ := hP
  have := hprob
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
  exact hsplit


theorem svGenerator_sub {a : Vec d → Mat d} {b : Vec d → Vec d} {f g : Vec d → ℝ}
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (x : Vec d) :
    External.Draft.svGenerator a b (fun y => f y - g y) x =
      External.Draft.svGenerator a b f x - External.Draft.svGenerator a b g x := by
  have hfd : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hgd : Differentiable ℝ g := hg.differentiable (by norm_num)
  have h1 : ∀ y, fderiv ℝ (fun y => f y - g y) y = fderiv ℝ f y - fderiv ℝ g y := fun y =>
    fderiv_sub (hfd y) (hgd y)
  have hf1 : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hg1 : Differentiable ℝ (fderiv ℝ g) :=
    (hg.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have h2 : ∀ v w : Vec d, fderiv ℝ (fun y => fderiv ℝ f y v - fderiv ℝ g y v) x w =
      fderiv ℝ (fun y => fderiv ℝ f y v) x w - fderiv ℝ (fun y => fderiv ℝ g y v) x w := by
    intro v w
    rw [show (fun y => fderiv ℝ f y v - fderiv ℝ g y v) =
        (fun y => fderiv ℝ f y v) - (fun y => fderiv ℝ g y v) from rfl,
      fderiv_sub ((hf1.clm_apply (differentiable_const v)) x)
        ((hg1.clm_apply (differentiable_const v)) x), sub_apply]
  unfold External.Draft.svGenerator
  simp only [h1, sub_apply, h2, mul_sub, Finset.sum_sub_distrib]
  ring


section Reduced

variable {Λ₀ : ℝ} {ω : FieldPair d} (hs : IsSmoothFieldPair ω) (i : Fin d) (lam : ℝ)

include hs in
/-- The carré du champ of a smooth function under the reduced generator. -/
theorem reducedGenerator_sq_sub {u : Vec d → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u) (y : Vec d) :
    reducedGenerator i ω lam (fun z => u z ^ 2) y - 2 * u y * reducedGenerator i ω lam u y =
      ∑ k, ∑ l, reducedCoefficient ω y k l *
        (fderiv ℝ u y (unitVector k) * fderiv ℝ u y (unitVector l)) := by
  rw [reducedGenerator_eq_svGenerator hs i lam (contDiff_two_of_top (hu.pow 2)),
    reducedGenerator_eq_svGenerator hs i lam (contDiff_two_of_top hu),
    svGenerator_sq_sub _ _ (contDiff_two_of_top hu) y]

include hs in
theorem compensatedTest_sub_reduced {u v : Vec d → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (hv : ContDiff ℝ (⊤ : ℕ∞) v) (t : ℝ≥0) (γ : Path d) :
    compensatedTest (reducedGenerator i ω lam) (fun y => u y - v y) t γ =
      compensatedTest (reducedGenerator i ω lam) u t γ -
        compensatedTest (reducedGenerator i ω lam) v t γ := by
  have hL : ∀ y, reducedGenerator i ω lam (fun y => u y - v y) y =
      reducedGenerator i ω lam u y - reducedGenerator i ω lam v y := by
    intro y
    rw [reducedGenerator_eq_svGenerator hs i lam (contDiff_two_of_top (hu.sub hv)),
      reducedGenerator_eq_svGenerator hs i lam (contDiff_two_of_top hu),
      reducedGenerator_eq_svGenerator hs i lam (contDiff_two_of_top hv)]
    exact svGenerator_sub (contDiff_two_of_top hu) (contDiff_two_of_top hv) y
  have hcu := continuous_reducedGenerator_apply hs i lam hu
  have hcv := continuous_reducedGenerator_apply hs i lam hv
  have i1 : IntervalIntegrable (fun s : ℝ => reducedGenerator i ω lam u (γ s.toNNReal)) volume 0 t :=
    (hcu.comp (γ.continuous.comp continuous_real_toNNReal)).intervalIntegrable 0 t
  have i2 : IntervalIntegrable (fun s : ℝ => reducedGenerator i ω lam v (γ s.toNNReal)) volume 0 t :=
    (hcv.comp (γ.continuous.comp continuous_real_toNNReal)).intervalIntegrable 0 t
  unfold compensatedTest
  simp_rw [hL]
  rw [intervalIntegral.integral_sub i1 i2]
  ring

end Reduced


/-- The carré du champ of a function, from its derivatives. -/
noncomputable def carreDuChamp (ω : FieldPair d) (u : Vec d → ℝ) (y : Vec d) : ℝ :=
  ∑ k, ∑ l, reducedCoefficient ω y k l * (fderiv ℝ u y (unitVector k) * fderiv ℝ u y (unitVector l))

section ReducedMP

variable {Λ₀ : ℝ} (hΛ : 0 < Λ₀) {ω : FieldPair d} (hω : IsRegular Λ₀ ω) (hs : IsSmoothFieldPair ω)
  (i : Fin d) (lam : ℝ) {P : Measure (Path d)}
  (hP : SolvesMartingaleProblem (reducedGenerator i ω lam) 0 P)

include hΛ hω hs hP in
/-- For a smooth compactly supported test function, the second moment of its compensated process
under a reduced martingale problem is the expected time integral of the carré du champ. -/
theorem integral_sq_compensated_reduced {u : Vec d → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (huc : HasCompactSupport u) (t : ℝ≥0) :
    ∫ γ, compensatedTest (reducedGenerator i ω lam) u t γ ^ 2 ∂P =
      ∫ γ, pathInt (carreDuChamp ω u) γ (t : ℝ) ∂P := by
  obtain ⟨K, hK⟩ := bounded_reducedGenerator_apply hΛ hω hs i lam hu huc
  have hu2 : ContDiff ℝ (⊤ : ℕ∞) (fun z => u z ^ 2) := hu.pow 2
  have huc2 : HasCompactSupport (fun z => u z ^ 2) := huc.comp_left (g := fun x : ℝ => x ^ 2) (by simp)
  obtain ⟨K2, hK2⟩ := bounded_reducedGenerator_apply hΛ hω hs i lam hu2 huc2
  rw [integral_sq_compensatedTest_eq hP hu huc hK (continuous_reducedGenerator_apply hs i lam hu)
    hK2 (continuous_reducedGenerator_apply hs i lam hu2) t]
  congr 1
  funext γ
  congr 1
  funext y
  exact reducedGenerator_sq_sub hs i lam hu y

end ReducedMP

end EinsteinFull
