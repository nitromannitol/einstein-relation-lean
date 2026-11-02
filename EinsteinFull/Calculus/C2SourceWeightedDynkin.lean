import EinsteinFull.Calculus.S4MartingaleVarianceSupport
import EinsteinFull.Calculus.S4CountableBasicSupport
import EinsteinFull.Calculus.S4GeneratorRegularitySupport
import EinsteinFull.Calculus.S4ReducedCoefficientSupport
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

open EinsteinRelation MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology BigOperators

namespace EinsteinFull

/-- A bounded observable of the past is orthogonal to later martingale increments. -/
theorem c2_integral_martingale_mul_past {d : ℕ} {P : Measure (Path d)}
    [IsProbabilityMeasure P] {M : ℝ≥0 → Path d → ℝ}
    (hM : Martingale M (pathFiltration d) P) {u t : ℝ≥0} (hut : u ≤ t)
    {G : Path d → ℝ} (hG : StronglyMeasurable[pathFiltration d u] G)
    {K : ℝ} (hK : ∀ γ, |G γ| ≤ K) :
    ∫ γ, M t γ * G γ ∂P = ∫ γ, M u γ * G γ ∂P := by
  have hGm : StronglyMeasurable G := hG.mono ((pathFiltration d).le u)
  have hMt : Integrable (M t) P := hM.integrable t
  have hGM : Integrable (G * M t) P :=
    hMt.bdd_mul hGm.aestronglyMeasurable (ae_of_all _ fun γ => by
      rw [Real.norm_eq_abs]; exact hK γ)
  calc ∫ γ, M t γ * G γ ∂P
      = ∫ γ, (G * M t) γ ∂P := by
        refine integral_congr_ae (ae_of_all _ fun γ => ?_)
        simp only [Pi.mul_apply, mul_comm]
    _ = ∫ γ, (P[G * M t | pathFiltration d u]) γ ∂P :=
        (integral_condExp ((pathFiltration d).le u)).symm
    _ = ∫ γ, (G * P[M t | pathFiltration d u]) γ ∂P :=
        integral_congr_ae (condExp_mul_of_stronglyMeasurable_left hG hGM hMt)
    _ = ∫ γ, M u γ * G γ ∂P := by
        refine integral_congr_ae ?_
        filter_upwards [hM.2 u t hut] with γ hγ
        simp only [Pi.mul_apply, hγ, mul_comm]

/-- Exchange a bounded past-adapted time integral with a martingale endpoint. -/
theorem c2_integral_martingale_mul_adapted_integral {d : ℕ}
    {P : Measure (Path d)} [IsProbabilityMeasure P]
    {M : ℝ≥0 → Path d → ℝ} (hM : Martingale M (pathFiltration d) P)
    (hMm : Measurable (fun p : ℝ × Path d => M p.1.toNNReal p.2))
    {G : ℝ → Path d → ℝ}
    (hGm : Measurable (fun p : ℝ × Path d => G p.1 p.2))
    (hGa : ∀ s : ℝ, StronglyMeasurable[pathFiltration d s.toNNReal] (G s))
    {K C : ℝ} {t : ℝ≥0} (hK : ∀ s, s.toNNReal ≤ t → ∀ γ, |G s γ| ≤ K)
    (hC : ∀ s ≤ t, ∀ γ, |M s γ| ≤ C) :
    (∫ γ, M t γ * (∫ s in (0 : ℝ)..t, G s γ) ∂P) =
      ∫ γ, (∫ s in (0 : ℝ)..t, M s.toNNReal γ * G s γ) ∂P := by
  have ht0 : (0 : ℝ) ≤ t := t.coe_nonneg
  haveI hfin : IsFiniteMeasure (volume.restrict (Set.uIoc (0 : ℝ) t)) := by
    rw [Set.uIoc_of_le ht0]
    infer_instance
  have hMt : StronglyMeasurable (M t) :=
    (hM.stronglyMeasurable t).mono ((pathFiltration d).le t)
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC t le_rfl 0)
  have hS : ∀ᵐ s ∂(volume.restrict (Set.uIoc (0 : ℝ) t)), s.toNNReal ≤ t := by
    refine (ae_restrict_iff' measurableSet_uIoc).2 (ae_of_all _ fun s hs => ?_)
    rw [Set.uIoc_of_le ht0] at hs
    exact Real.toNNReal_le_iff_le_coe.mpr hs.2
  have hm1 : Measurable (fun p : ℝ × Path d => M t p.2 * G p.1 p.2) :=
    (hMt.measurable.comp measurable_snd).mul hGm
  have hm2 : Measurable (fun p : ℝ × Path d => M p.1.toNNReal p.2 * G p.1 p.2) :=
    hMm.mul hGm
  have hi1 : Integrable (Function.uncurry fun (s : ℝ) (γ : Path d) =>
      M t γ * G s γ) ((volume.restrict (Set.uIoc (0 : ℝ) t)).prod P) := by
    refine Integrable.of_bound hm1.aestronglyMeasurable (C * K) ?_
    rw [Measure.ae_prod_iff_ae_ae]
    · filter_upwards [hS] with s hs
      refine ae_of_all _ fun γ => ?_
      show ‖M t γ * G s γ‖ ≤ C * K
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hC t le_rfl _) (hK s hs _) (abs_nonneg _) hC0
    · exact measurableSet_le hm1.norm measurable_const
  have hi2 : Integrable (Function.uncurry fun (s : ℝ) (γ : Path d) =>
      M s.toNNReal γ * G s γ) ((volume.restrict (Set.uIoc (0 : ℝ) t)).prod P) := by
    refine Integrable.of_bound hm2.aestronglyMeasurable (C * K) ?_
    rw [Measure.ae_prod_iff_ae_ae]
    · filter_upwards [hS] with s hs
      refine ae_of_all _ fun γ => ?_
      show ‖M s.toNNReal γ * G s γ‖ ≤ C * K
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hC _ hs _) (hK s hs _) (abs_nonneg _) hC0
    · exact measurableSet_le hm2.norm measurable_const
  calc (∫ γ, M t γ * (∫ s in (0 : ℝ)..t, G s γ) ∂P) =
      ∫ γ, (∫ s in (0 : ℝ)..t, M t γ * G s γ) ∂P := by
        refine integral_congr_ae (ae_of_all _ fun γ => ?_)
        simp only
        rw [intervalIntegral.integral_const_mul]
    _ = ∫ s in (0 : ℝ)..t, ∫ γ, M t γ * G s γ ∂P :=
        (intervalIntegral_integral_swap hi1).symm
    _ = ∫ s in (0 : ℝ)..t, ∫ γ, M s.toNNReal γ * G s γ ∂P := by
        refine intervalIntegral.integral_congr fun s hs => ?_
        rw [Set.uIcc_of_le ht0] at hs
        exact c2_integral_martingale_mul_past hM
          (Real.toNNReal_le_iff_le_coe.mpr hs.2) (hGa s) (hK s (Real.toNNReal_le_iff_le_coe.mpr hs.2))
    _ = ∫ γ, (∫ s in (0 : ℝ)..t, M s.toNNReal γ * G s γ) ∂P :=
        intervalIntegral_integral_swap hi2

-- Draft: deterministic finite-variation product; requires AbsolutelyContinuousFun.
theorem c2_integral_product_indefinite {a b : ℝ} (hab : a ≤ b)
    {W G L : ℝ → ℝ} (hW : AbsolutelyContinuousOnInterval W a b)
    (hL : IntervalIntegrable L volume a b)
    (hWG : ∀ᵐ u ∂(volume.restrict (Set.Ioc a b)), deriv W u = G u) :
    W b * (∫ u in a..b, L u) =
      ∫ u in a..b, G u * (∫ v in a..u, L v) + W u * L u := by
  let A : ℝ → ℝ := fun u => ∫ v in a..u, L v
  have hA : AbsolutelyContinuousOnInterval A a b :=
    hL.absolutelyContinuousOnInterval_intervalIntegral (by simp)
  have hda : ∀ᵐ u ∂(volume.restrict (Set.Ioc a b)), deriv A u = L u := by
    filter_upwards [ae_restrict_of_ae hL.ae_hasDerivAt_integral,
      ae_restrict_mem measurableSet_Ioc] with u hu hmem
    have humem : u ∈ Set.uIcc a b := by
      rw [Set.uIcc_of_le hab]; exact ⟨hmem.1.le, hmem.2⟩
    exact (hu humem a (by simp)).deriv
  have hp := hW.integral_deriv_mul_eq_sub hA
  have heq : (∫ u in a..b, deriv W u * A u + W u * deriv A u) =
      ∫ u in a..b, G u * A u + W u * L u := by
    rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab]
    apply integral_congr_ae
    filter_upwards [hWG, hda] with u huW huA
    rw [huW, huA]
  rw [heq] at hp
  simpa [A] using hp.symm

-- Draft: uniform bound for the actual compensated test; requires S4PathIntegralSupport.
theorem c2_compensatedTest_horizon_bound {d : ℕ}
    {L : (Vec d → ℝ) → Vec d → ℝ} {f : Vec d → ℝ} {B C : ℝ}
    (hf : ∀ y, |f y| ≤ B) (hL : ∀ y, |L f y| ≤ C) (T : ℝ≥0) :
    ∀ s ≤ T, ∀ γ : Path d, |compensatedTest L f s γ| ≤ 2 * B + C * T := by
  intro s hs γ
  have hC : 0 ≤ C := (abs_nonneg _).trans (hL 0)
  have hst : (s : ℝ) ≤ T := hs
  have hInt := abs_pathInt_le hL γ s.coe_nonneg
  have hmul := mul_le_mul_of_nonneg_left hst hC
  rw [compensatedTest_eq]
  have htri := abs_sub (f (γ s) - f (γ 0)) (pathInt (L f) γ s)
  have htri' := abs_sub (f (γ s)) (f (γ 0))
  have hfs := hf (γ s)
  have hf0 := hf (γ 0)
  linarith

-- Draft: joint measurability and a horizon bound give each pathwise time integral.
theorem c2_intervalIntegrable_bounded_time_slice {Ω : Type*} [MeasurableSpace Ω]
    {J : ℝ → Ω → ℝ} {t C : ℝ}
    (hJ : Measurable (fun p : ℝ × Ω => J p.1 p.2))
    (hC : ∀ s ∈ Set.uIcc 0 t, ∀ ω, |J s ω| ≤ C) (ω : Ω) :
    IntervalIntegrable (fun s => J s ω) volume 0 t := by
  apply intervalIntegrable_iff.mpr
  have hm : Measurable (fun s => J s ω) :=
    hJ.comp (measurable_id.prodMk measurable_const)
  apply IntegrableOn.of_bound (by simp) hm.aestronglyMeasurable C
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with s hs
  simpa only [Real.norm_eq_abs] using hC s (Set.uIoc_subset_uIcc hs) ω

-- Draft: bounded jointly measurable time integrals are law-integrable.
theorem c2_integrable_bounded_time_integral {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {J : ℝ → Ω → ℝ}
    {t C : ℝ} (ht : 0 ≤ t)
    (hJ : Measurable (fun p : ℝ × Ω => J p.1 p.2))
    (hC : ∀ s ∈ Set.uIcc 0 t, ∀ ω, |J s ω| ≤ C) :
    Integrable (fun ω => ∫ s in (0 : ℝ)..t, J s ω) P := by
  have hm : Measurable (fun p : Ω × ℝ => J p.2 p.1) :=
    hJ.comp (measurable_snd.prodMk measurable_fst)
  have hInt : StronglyMeasurable (fun ω => ∫ s in Set.Ioc (0 : ℝ) t, J s ω) :=
    hm.stronglyMeasurable.integral_prod_right' (ν := volume.restrict (Set.Ioc 0 t))
  apply Integrable.of_bound
    (by simpa only [intervalIntegral.integral_of_le ht] using hInt.aestronglyMeasurable)
    (C * t)
  refine ae_of_all _ fun ω => ?_
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ))
    (b := t) (f := fun s => J s ω) (C := C)
    (fun s hs => by simpa only [Real.norm_eq_abs] using hC s (Set.uIoc_subset_uIcc hs) ω)
  simpa only [sub_zero, abs_of_nonneg ht] using hb

-- Draft pointwise ingredient; combine with c2_weighted_dynkin_assembly.
theorem c2_pointwise_weighted_dynkin_assembly {t : ℝ}
    {W F M A G L : ℝ → ℝ} {F0 : ℝ}
    (hrel : ∀ s, s ∈ Set.uIcc 0 t → F s = M s + F0 + A s)
    (hweight : W t - 1 = ∫ s in (0 : ℝ)..t, G s)
    (hproduct : W t * A t = ∫ s in (0 : ℝ)..t, G s * A s + W s * L s)
    (hg : IntervalIntegrable G volume 0 t)
    (hmg : IntervalIntegrable (fun s => M s * G s) volume 0 t)
    (hga : IntervalIntegrable (fun s => G s * A s) volume 0 t)
    (hwl : IntervalIntegrable (fun s => W s * L s) volume 0 t) :
    W t * F t - F0 = M t + M t * (∫ s in (0 : ℝ)..t, G s) +
      (∫ s in (0 : ℝ)..t, W s * L s + G s * F s) -
      ∫ s in (0 : ℝ)..t, M s * G s := by
  have hz : (∫ s in (0 : ℝ)..t, W s * L s + G s * F s) =
      (∫ s in (0 : ℝ)..t, M s * G s) +
        F0 * (∫ s in (0 : ℝ)..t, G s) + W t * A t := by
    rw [hproduct, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_add hmg (hg.const_mul F0),
      ← intervalIntegral.integral_add (hmg.add (hg.const_mul F0)) (hga.add hwl)]
    apply intervalIntegral.integral_congr
    intro s hs
    simp only
    rw [hrel s hs]
    ring
  rw [hz, hrel t (Set.right_mem_uIcc)]
  have hm := congrArg (fun z : ℝ => M t * z) hweight
  have hf0 := congrArg (fun z : ℝ => F0 * z) hweight
  nlinarith [hm, hf0]

-- Generic final algebra (draft, not built): pathwise decomposition plus cross expectation.
theorem c2_weighted_dynkin_assembly {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) {F F0 M W I H Z : Ω → ℝ}
    (hF0 : Integrable F0 P) (hM : Integrable M P)
    (hWI : Integrable (fun ω => M ω * I ω) P)
    (hH : Integrable H P) (hZ : Integrable Z P)
    (hWF : Integrable (fun ω => W ω * F ω) P)
    (hzero : ∫ ω, M ω ∂P = 0)
    (hcross : (∫ ω, M ω * I ω ∂P) = ∫ ω, H ω ∂P)
    (hpath : ∀ ω, W ω * F ω - F0 ω =
      M ω + M ω * I ω + Z ω - H ω) :
    (∫ ω, W ω * F ω ∂P) - (∫ ω, F0 ω ∂P) = ∫ ω, Z ω ∂P := by
  have heq : (∫ ω, W ω * F ω - F0 ω ∂P) =
      ∫ ω, M ω + M ω * I ω + Z ω - H ω ∂P :=
    integral_congr_ae (ae_of_all _ hpath)
  rw [integral_sub hWF hF0] at heq
  have hsum : (∫ ω, M ω + M ω * I ω + Z ω - H ω ∂P) =
      (∫ ω, M ω ∂P) + (∫ ω, M ω * I ω ∂P) + (∫ ω, Z ω ∂P) -
        (∫ ω, H ω ∂P) := by
    have h1 := integral_sub ((hM.add hWI).add hZ) hH
    have h2 := integral_add (hM.add hWI) hZ
    have h3 := integral_add hM hWI
    simp only [Pi.sub_apply, Pi.add_apply] at h1 h2 h3
    rw [h2, h3] at h1
    exact h1
  rw [hsum, hzero, hcross] at heq
  linarith

-- For actual variables, derive hpath by W-1 = I, F = M+F0+A,
-- WA = integral(G*A + W*Lf), and Z = H + F0*I + WA.
-- Derive Z integrability and hpath using pointwise interval integrability of
-- each bounded factor; derive hcross from c2_integral_martingale_mul_adapted_integral.

-- Draft joint measurability of time/path integral for bounded measurable g.
theorem c2_measurable_path_integral_joint {d : ℕ} {g : Vec d → ℝ}
    (hg : Measurable g) {K : ℝ} (hK : ∀ y, |g y| ≤ K) :
    Measurable (fun p : ℝ × Path d =>
      ∫ s in (0 : ℝ)..(p.1.toNNReal : ℝ), g (p.2 s.toNNReal)) := by
  change Measurable (Function.uncurry (fun t : ℝ => fun γ : Path d =>
    ∫ s in (0 : ℝ)..(t.toNNReal : ℝ), g (γ s.toNNReal)))
  apply measurable_uncurry_of_continuous_of_measurable
  · intro γ
    have hm : Measurable (fun s : ℝ => g (γ s.toNNReal)) :=
      hg.comp (γ.continuous.measurable.comp continuous_real_toNNReal.measurable)
    have hi : ∀ a b, IntervalIntegrable (fun s : ℝ => g (γ s.toNNReal)) volume a b := by
      intro a b
      apply intervalIntegrable_iff.mpr
      exact IntegrableOn.of_bound (by simp) hm.aestronglyMeasurable K
        (ae_of_all _ fun s => by simpa only [Real.norm_eq_abs] using hK (γ s.toNNReal))
    exact (intervalIntegral.continuous_primitive hi 0).comp
      (NNReal.continuous_coe.comp continuous_real_toNNReal)
  · intro t
    have h := stronglyMeasurable_pathIntegral_of_measurable g hg t.toNNReal
    rw [← pathFiltration_eq_canonical] at h
    exact (h.mono ((pathFiltration d).le t.toNNReal)).measurable


-- Draft; uses c2_measurable_path_integral_joint.
theorem c2_compensatedTest_joint_measurable {d : ℕ}
    {L : (Vec d → ℝ) → Vec d → ℝ} {f : Vec d → ℝ}
    (hf : Measurable f) (hL : Measurable (L f))
    {C : ℝ} (hC : ∀ y, |L f y| ≤ C) :
    Measurable (fun p : ℝ × Path d => compensatedTest L f p.1.toNNReal p.2) := by
  have heval : Measurable (fun p : ℝ × Path d => p.2 p.1.toNNReal) :=
    (continuous_snd.eval (continuous_real_toNNReal.comp continuous_fst)).measurable
  have heval0 : Measurable (fun p : ℝ × Path d => p.2 0) :=
    (continuous_snd.eval continuous_const).measurable
  have hi := c2_measurable_path_integral_joint hL hC
  convert ((hf.comp heval).sub (hf.comp heval0)).sub hi using 1
  funext p
  rfl

-- Draft: absolute continuity plus an a.e. derivative identifies the weight integral.
theorem c2_weight_integral_of_ae_deriv {W G : ℝ → ℝ} {t : ℝ} (ht : 0 ≤ t)
    (hW : AbsolutelyContinuousOnInterval W 0 t) (hW0 : W 0 = 1)
    (hderiv : ∀ᵐ s ∂(volume.restrict (Set.Ioc (0 : ℝ) t)), deriv W s = G s) :
    W t - 1 = ∫ s in (0 : ℝ)..t, G s := by
  have heq : (∫ s in (0 : ℝ)..t, deriv W s) = ∫ s in (0 : ℝ)..t, G s := by
    rw [intervalIntegral.integral_of_le ht, intervalIntegral.integral_of_le ht]
    exact integral_congr_ae hderiv
  rw [← heq, hW.integral_deriv_eq_sub, hW0]


-- Draft: actual reduced generator is measurable and bounded on compact smooth tests.
theorem c2_reduced_generator_measurable_bounded {d : ℕ} {Λ₀ : ℝ}
    (hΛ : 0 < Λ₀) {ω : FieldPair d} (hω : IsRegular Λ₀ ω)
    (i : Fin d) {f : Vec d → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hc : HasCompactSupport f) :
    Measurable (External.Draft.svGenerator (reducedCoefficient ω)
      (forcedDrift (reducedCoefficient ω) i 0) f) ∧
    ∃ C : ℝ, ∀ y, |External.Draft.svGenerator (reducedCoefficient ω)
      (forcedDrift (reducedCoefficient ω) i 0) f y| ≤ C := by
  obtain ⟨hA, _, ⟨Ma, hAb⟩, _, hb, ⟨Mb, hbb⟩⟩ := reduced_svHypotheses hΛ hω i 0
  have hcoef : BddCoef (reducedCoefficient ω)
      (forcedDrift (reducedCoefficient ω) i 0) (max Ma Mb) :=
    ⟨fun k j => (hA.matrix_elem k j).measurable,
      fun k => (measurable_pi_apply k).comp hb,
      fun y k j => (hAb y k j).trans (le_max_left _ _),
      fun y k => (hbb y k).trans (le_max_right _ _)⟩
  exact ⟨hcoef.measurable_gen f, bounded_svGenerator _ _ hAb hbb
    (contDiff_two_of_top hf) hc⟩


/-- The exponential of a bounded path potential is jointly measurable in time and path. -/
theorem c2_path_weight_joint_measurable {d : ℕ} {g : Vec d → ℝ}
    (hg : Measurable g) {K : ℝ} (hK : ∀ y, |g y| ≤ K) :
    Measurable (fun p : ℝ × Path d => Real.exp
      (-(∫ u in Set.Ioc (0 : ℝ) (p.1.toNNReal : ℝ), g (p.2 u.toNNReal)))) := by
  have hj := c2_measurable_path_integral_joint hg hK
  apply Real.continuous_exp.measurable.comp
  apply Measurable.neg
  convert hj using 1
  funext p
  rw [intervalIntegral.integral_of_le p.1.toNNReal.coe_nonneg]

/-- A bounded potential gives a path-uniform bound for its exponential weight. -/
theorem c2_path_weight_horizon_bound {d : ℕ} {g : Vec d → ℝ}
    {K : ℝ} (hK : ∀ y, |g y| ≤ K) (T : ℝ≥0) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (s : ℝ≥0), s ≤ T → ∀ γ : Path d,
      |Real.exp (-(∫ u in Set.Ioc (0 : ℝ) (s : ℝ), g (γ u.toNNReal)))| ≤ B := by
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (hK 0)
  refine ⟨Real.exp (K * T), (Real.exp_pos _).le, ?_⟩
  intro s hs γ
  rw [abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  have hfinite : volume (Set.Ioc (0 : ℝ) (s : ℝ)) < ∞ := by simp
  have h := norm_setIntegral_le_of_norm_le_const (f := fun u : ℝ => g (γ u.toNNReal))
    (C := K) hfinite (fun u _ => by simpa only [Real.norm_eq_abs] using hK (γ u.toNNReal))
  have hb : |∫ u in Set.Ioc (0 : ℝ) (s : ℝ), g (γ u.toNNReal)| ≤ K * (s : ℝ) := by
    simpa only [Real.norm_eq_abs, Real.volume_real_Ioc_of_le s.coe_nonneg, sub_zero] using h
  have hst : (s : ℝ) ≤ T := hs
  have hm := mul_le_mul_of_nonneg_left hst hK0
  have hl := (abs_le.mp hb).1
  linarith

/-- The time derivative candidate of a bounded potential weight is jointly
measurable and bounded uniformly over a finite time horizon. -/
theorem c2_path_weight_derivative_joint_bound {d : ℕ} {g : Vec d → ℝ}
    (hg : Measurable g) {K : ℝ} (hK : ∀ y, |g y| ≤ K) (T : ℝ≥0) :
    let G := fun (s : ℝ) (γ : Path d) => -(g (γ s.toNNReal) * Real.exp
      (-(∫ u in Set.Ioc (0 : ℝ) (s.toNNReal : ℝ), g (γ u.toNNReal))))
    Measurable (fun p : ℝ × Path d => G p.1 p.2) ∧
      ∃ C : ℝ, ∀ s, s.toNNReal ≤ T → ∀ γ, |G s γ| ≤ C := by
  dsimp only
  obtain ⟨B, hB, hBb⟩ := c2_path_weight_horizon_bound hK T
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (hK 0)
  constructor
  · have heval : Measurable (fun p : ℝ × Path d => p.2 p.1.toNNReal) :=
      (continuous_snd.eval (continuous_real_toNNReal.comp continuous_fst)).measurable
    exact ((hg.comp heval).mul (c2_path_weight_joint_measurable hg hK)).neg
  · refine ⟨K * B, fun s hs γ => ?_⟩
    rw [abs_neg, abs_mul]
    exact mul_le_mul (hK _) (hBb s.toNNReal hs γ) (abs_nonneg _) hK0

/-- An adapted path weight has an adapted derivative candidate when its
potential is measurable. -/
theorem c2_path_weight_derivative_stronglyAdapted {d : ℕ} {g : Vec d → ℝ}
    (hg : Measurable g)
    (hW : StronglyAdapted (pathFiltration d) (fun t : ℝ≥0 => fun γ : Path d =>
      Real.exp (-(∫ u in Set.Ioc (0 : ℝ) (t : ℝ), g (γ u.toNNReal))))) :
    StronglyAdapted (pathFiltration d) (fun t : ℝ≥0 => fun γ : Path d =>
      -(g (γ t) * Real.exp (-(∫ u in Set.Ioc (0 : ℝ) (t : ℝ),
        g (γ u.toNNReal))))) := by
  intro t
  have hp : StronglyMeasurable[pathFiltration d t] (fun γ : Path d => γ t) := by
    rw [pathFiltration_eq_canonical]
    exact (MarkovProcess.ContinuousPath.measurable_coordinateProcess_canonicalFiltration
      (alpha := Vec d) t).stronglyMeasurable
  exact (((hg.comp hp.measurable).stronglyMeasurable).mul (hW t)).neg

/-- The reduced martingale is orthogonal to the past-adapted derivative
candidate of a bounded path weight. -/
theorem c2_reduced_compensated_weight_cross {d : ℕ} {Λ₀ : ℝ}
    (hΛ : 0 < Λ₀) {ω : FieldPair d} (hω : IsRegular Λ₀ ω)
    (i : Fin d) {x : Vec d} {P : Measure (Path d)}
    (hP : SolvesMartingaleProblem (External.Draft.svGenerator
      (reducedCoefficient ω) (forcedDrift (reducedCoefficient ω) i 0)) x P)
    {f : Vec d → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f)
    {g : Vec d → ℝ} (hg : Measurable g) {K : ℝ} (hK : ∀ y, |g y| ≤ K)
    (hW : StronglyAdapted (pathFiltration d) (fun t : ℝ≥0 => fun γ : Path d =>
      Real.exp (-(∫ u in Set.Ioc (0 : ℝ) (t : ℝ), g (γ u.toNNReal)))))
    (T : ℝ≥0) :
    let L := External.Draft.svGenerator (reducedCoefficient ω)
      (forcedDrift (reducedCoefficient ω) i 0)
    let G := fun (s : ℝ) (γ : Path d) => -(g (γ s.toNNReal) * Real.exp
      (-(∫ u in Set.Ioc (0 : ℝ) (s.toNNReal : ℝ), g (γ u.toNNReal))))
    (∫ γ, compensatedTest L f T γ * (∫ s in (0 : ℝ)..T, G s γ) ∂P) =
      ∫ γ, (∫ s in (0 : ℝ)..T, compensatedTest L f s.toNNReal γ * G s γ) ∂P := by
  dsimp only
  letI : IsProbabilityMeasure P := hP.1
  obtain ⟨hL, C, hC⟩ := c2_reduced_generator_measurable_bounded hΛ hω i hf hc
  obtain ⟨B, hB⟩ := hf.continuous.bounded_above_of_compact_support hc
  have hfB : ∀ y, |f y| ≤ B := fun y => by simpa only [Real.norm_eq_abs] using hB y
  obtain ⟨hG, D, hD⟩ := c2_path_weight_derivative_joint_bound hg hK T
  exact c2_integral_martingale_mul_adapted_integral (hP.2.2 f hf hc).2.2
    (c2_compensatedTest_joint_measurable hf.continuous.measurable hL hC)
    hG (fun s => c2_path_weight_derivative_stronglyAdapted hg hW s.toNNReal)
    hD (c2_compensatedTest_horizon_bound hfB hC T)

end EinsteinFull
