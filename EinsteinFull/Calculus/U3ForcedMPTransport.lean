import EinsteinFull.Calculus.U3SignedWeightNormalization

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology BigOperators
namespace EinsteinFull
open EinsteinRelation EinsteinRelation.External.GantertSection7Support

/-- The finite-horizon signed tilt of the supplied zero-force law is a probability measure. -/
theorem u3_reduced_force_tilt_probability {d : ℕ} (hd : 1 ≤ d) {Λ₀ : ℝ} (hΛ : 0 < Λ₀)
    {ω : FieldPair d} (hω : IsRegular Λ₀ ω) (i : Fin d)
    {x : Vec d} {P : Measure (Path d)}
    (hP : SolvesMartingaleProblem (External.Draft.svGenerator
      (reducedCoefficient ω) (forcedDrift (reducedCoefficient ω) i 0)) x P)
    (lam : ℝ) (T : ℝ≥0) :
    let Z : Path d → ℝ := fun γ => Real.exp
      (lam * ((γ T) i - x i) - ∫ u in Set.Ioc (0 : ℝ) (T : ℝ),
        (lam * forcedDrift (reducedCoefficient ω) i 0 (γ u.toNNReal) i +
          (lam ^ 2 / 2) * reducedCoefficient ω (γ u.toNNReal) i i))
    IsProbabilityMeasure (P.withDensity (fun γ => ENNReal.ofReal (Z γ))) := by
  dsimp only
  obtain ⟨hi, hn⟩ := u3_reduced_force_exponential_weight_integral hd hΛ hω i hP lam T
  constructor
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall fun _ =>
      (Real.exp_pos _).le), hn]
  simp

/-- The actual signed density process is adapted, integrable, and has unit mean. -/
theorem u3_reduced_force_density_adapted_integrable {d : ℕ} (hd : 1 ≤ d)
    {Λ₀ : ℝ} (hΛ : 0 < Λ₀) {ω : FieldPair d} (hω : IsRegular Λ₀ ω)
    (i : Fin d) {x : Vec d} {P : Measure (Path d)}
    (hP : SolvesMartingaleProblem (External.Draft.svGenerator
      (reducedCoefficient ω) (forcedDrift (reducedCoefficient ω) i 0)) x P)
    (lam : ℝ) :
    let Z : ℝ≥0 → Path d → ℝ := fun t γ => Real.exp
      (lam * ((γ t) i - x i) - ∫ u in Set.Ioc (0 : ℝ) (t : ℝ),
        (lam * forcedDrift (reducedCoefficient ω) i 0 (γ u.toNNReal) i +
          (lam ^ 2 / 2) * reducedCoefficient ω (γ u.toNNReal) i i))
    StronglyAdapted (pathFiltration d) Z ∧
      ∀ t, Integrable (Z t) P ∧ (∫ γ, Z t γ ∂P) = 1 := by
  dsimp only
  constructor
  · intro t
    letI : MeasurableSpace (Path d) := pathFiltration d t
    have hcoord : Measurable (fun γ : Path d => γ t i) :=
      (measurable_pi_apply i).comp ((Filtration.stronglyAdapted_natural
        (fun s => (measurable_pathPosition (d := d) s).stronglyMeasurable) t).measurable)
    have hw := (c25_reduced_force_path_weight_stronglyAdapted hΛ hω i lam) t
    have he : Measurable (fun γ : Path d => Real.exp (lam * (γ t i - x i))) :=
      Real.continuous_exp.measurable.comp (measurable_const.mul (hcoord.sub measurable_const))
    have hprod := he.stronglyMeasurable.mul hw
    convert hprod using 1 <;> funext γ
    simp only [Pi.mul_apply, sub_eq_add_neg, Real.exp_add]
  · intro t
    exact u3_reduced_force_exponential_weight_integral hd hΛ hω i hP lam t

/-- The signed density process has one integrable majorant on a finite horizon. -/
theorem u3_reduced_force_density_horizon_majorant {d : ℕ} (hd : 1 ≤ d)
    {Λ₀ : ℝ} (hΛ : 0 < Λ₀) {ω : FieldPair d} (hω : IsRegular Λ₀ ω)
    (i : Fin d) {x : Vec d} {P : Measure (Path d)}
    (hP : SolvesMartingaleProblem (External.Draft.svGenerator
      (reducedCoefficient ω) (forcedDrift (reducedCoefficient ω) i 0)) x P)
    (lam : ℝ) (T : ℝ≥0) :
    ∃ H : Path d → ℝ, Integrable H P ∧ ∀ t : ℝ≥0, t ≤ T → ∀ γ : Path d,
      Real.exp (lam * ((γ t) i - x i) - ∫ u in Set.Ioc (0 : ℝ) (t : ℝ),
        (lam * forcedDrift (reducedCoefficient ω) i 0 (γ u.toNNReal) i +
          (lam ^ 2 / 2) * reducedCoefficient ω (γ u.toNNReal) i i)) ≤ H γ := by
  obtain ⟨_, K, hK⟩ := c2_reduced_force_potential_measurable_bounded hΛ hω i lam
  obtain ⟨B, hB, hbound⟩ := c2_path_weight_horizon_bound hK T
  have hmax := c16_reduced_textbook_exp_coordinate_max_integrable hd hΛ hω i hP |lam| T
  refine ⟨fun γ => B * Real.exp (|lam| *
    sSup ((fun t : ℝ≥0 => |(γ t) i - x i|) '' Set.Icc 0 T)), hmax.const_mul B, ?_⟩
  intro t ht γ
  have hc := c27_exp_coord_le_max i lam x γ T t ht
  have hw := hbound t ht γ
  rw [abs_of_pos (Real.exp_pos _)] at hw
  have h := mul_le_mul hc hw (Real.exp_pos _).le (Real.exp_pos _).le
  simpa only [sub_eq_add_neg, Real.exp_add, mul_comm] using h

/-- A bounded adapted factor preserves martingale orthogonality on every past event. -/
theorem u3_integral_martingale_mul_past_on_event {d : ℕ} {P : Measure (Path d)}
    [IsProbabilityMeasure P] {M : ℝ≥0 → Path d → ℝ}
    (hM : Martingale M (pathFiltration d) P) {s u t : ℝ≥0}
    (hsu : s ≤ u) (hut : u ≤ t) {E : Set (Path d)}
    (hE : MeasurableSet[pathFiltration d s] E) {G : Path d → ℝ}
    (hG : StronglyMeasurable[pathFiltration d u] G)
    {K : ℝ} (hK : ∀ γ, |G γ| ≤ K) :
    (∫ γ in E, M t γ * G γ ∂P) = ∫ γ in E, M u γ * G γ ∂P := by
  have hEu : MeasurableSet[pathFiltration d u] E := (pathFiltration d).mono hsu E hE
  have hEa : MeasurableSet E := (pathFiltration d).le s E hE
  have hKi : ∀ γ, |E.indicator G γ| ≤ K := fun γ => by
    by_cases hγ : γ ∈ E
    · simpa [Set.indicator_of_mem hγ] using hK γ
    · simpa [Set.indicator_of_notMem hγ] using (abs_nonneg (G γ)).trans (hK γ)
  have h := c2_integral_martingale_mul_past hM hut (hG.indicator hEu) hKi
  rw [← integral_indicator hEa, ← integral_indicator hEa]
  convert h using 1 <;> apply integral_congr_ae <;> filter_upwards [] with γ <;>
    by_cases hγ : γ ∈ E <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, hγ]

/-- A bounded adapted time integral may be exchanged with a martingale endpoint
on any event measurable at the beginning of the interval. -/
theorem u3_integral_martingale_mul_adapted_integral_on_event {d : ℕ}
    {P : Measure (Path d)} [IsProbabilityMeasure P]
    {M : ℝ≥0 → Path d → ℝ} (hM : Martingale M (pathFiltration d) P)
    (hMm : Measurable (fun p : ℝ × Path d => M p.1.toNNReal p.2))
    {G : ℝ → Path d → ℝ}
    (hGm : Measurable (fun p : ℝ × Path d => G p.1 p.2))
    (hGa : ∀ r : ℝ, StronglyMeasurable[pathFiltration d r.toNNReal] (G r))
    {K C : ℝ} {s t : ℝ≥0} (hst : s ≤ t) {E : Set (Path d)}
    (hE : MeasurableSet[pathFiltration d s] E)
    (hK : ∀ r, r.toNNReal ≤ t → ∀ γ, |G r γ| ≤ K)
    (hC : ∀ r ≤ t, ∀ γ, |M r γ| ≤ C) :
    (∫ γ in E, M t γ * (∫ r in (s : ℝ)..t, G r γ) ∂P) =
      ∫ γ in E, (∫ r in (s : ℝ)..t, M r.toNNReal γ * G r γ) ∂P := by
  have ht0 : (s : ℝ) ≤ t := by exact_mod_cast hst
  haveI hfin : IsFiniteMeasure (volume.restrict (Set.uIoc (s : ℝ) t)) := by
    rw [Set.uIoc_of_le ht0]
    infer_instance
  have hMt : StronglyMeasurable (M t) :=
    (hM.stronglyMeasurable t).mono ((pathFiltration d).le t)
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC t le_rfl 0)
  have hS : ∀ᵐ r ∂(volume.restrict (Set.uIoc (s : ℝ) t)), r.toNNReal ≤ t := by
    refine (ae_restrict_iff' measurableSet_uIoc).2 (ae_of_all _ fun r hr => ?_)
    rw [Set.uIoc_of_le ht0] at hr
    exact Real.toNNReal_le_iff_le_coe.mpr hr.2
  have hm1 : Measurable (fun p : ℝ × Path d => M t p.2 * G p.1 p.2) :=
    (hMt.measurable.comp measurable_snd).mul hGm
  have hm2 : Measurable (fun p : ℝ × Path d => M p.1.toNNReal p.2 * G p.1 p.2) :=
    hMm.mul hGm
  have hi1 : Integrable (Function.uncurry fun (r : ℝ) (γ : Path d) =>
      M t γ * G r γ) ((volume.restrict (Set.uIoc (s : ℝ) t)).prod (P.restrict E)) := by
    refine Integrable.of_bound hm1.aestronglyMeasurable (C * K) ?_
    rw [Measure.ae_prod_iff_ae_ae]
    · filter_upwards [hS] with r hr
      refine ae_of_all _ fun γ => ?_
      show ‖M t γ * G r γ‖ ≤ C * K
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hC t le_rfl _) (hK r hr _) (abs_nonneg _) hC0
    · exact measurableSet_le hm1.norm measurable_const
  have hi2 : Integrable (Function.uncurry fun (r : ℝ) (γ : Path d) =>
      M r.toNNReal γ * G r γ) ((volume.restrict (Set.uIoc (s : ℝ) t)).prod (P.restrict E)) := by
    refine Integrable.of_bound hm2.aestronglyMeasurable (C * K) ?_
    rw [Measure.ae_prod_iff_ae_ae]
    · filter_upwards [hS] with r hr
      refine ae_of_all _ fun γ => ?_
      show ‖M r.toNNReal γ * G r γ‖ ≤ C * K
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hC _ hr _) (hK r hr _) (abs_nonneg _) hC0
    · exact measurableSet_le hm2.norm measurable_const
  calc (∫ γ in E, M t γ * (∫ r in (s : ℝ)..t, G r γ) ∂P) =
      ∫ γ in E, (∫ r in (s : ℝ)..t, M t γ * G r γ) ∂P := by
        refine integral_congr_ae (ae_of_all _ fun γ => ?_)
        simp only
        rw [intervalIntegral.integral_const_mul]
    _ = ∫ r in (s : ℝ)..t, ∫ γ in E, M t γ * G r γ ∂P :=
        (intervalIntegral_integral_swap hi1).symm
    _ = ∫ r in (s : ℝ)..t, ∫ γ in E, M r.toNNReal γ * G r γ ∂P := by
        refine intervalIntegral.integral_congr fun r hr => ?_
        rw [Set.uIcc_of_le ht0] at hr
        have hsr : s ≤ r.toNNReal := by
          apply NNReal.coe_le_coe.mp
          rw [Real.coe_toNNReal r (le_trans s.coe_nonneg hr.1)]
          exact hr.1
        have hrt : r.toNNReal ≤ t := Real.toNNReal_le_iff_le_coe.mpr hr.2
        exact u3_integral_martingale_mul_past_on_event hM hsr hrt hE (hGa r) (hK r hrt)
    _ = ∫ γ in E, (∫ r in (s : ℝ)..t, M r.toNNReal γ * G r γ) ∂P :=
        intervalIntegral_integral_swap hi2

/-- A bounded adapted time integral may be exchanged with an integrably dominated martingale endpoint
on any event measurable at the beginning of the interval. -/
theorem u3_integral_dominated_martingale_mul_adapted_integral_on_event {d : ℕ}
    {P : Measure (Path d)} [IsProbabilityMeasure P]
    {M : ℝ≥0 → Path d → ℝ} (hM : Martingale M (pathFiltration d) P)
    (hMm : Measurable (fun p : ℝ × Path d => M p.1.toNNReal p.2))
    {G : ℝ → Path d → ℝ}
    (hGm : Measurable (fun p : ℝ × Path d => G p.1 p.2))
    (hGa : ∀ r : ℝ, StronglyMeasurable[pathFiltration d r.toNNReal] (G r))
    {K : ℝ} {H : Path d → ℝ} {s t : ℝ≥0} (hst : s ≤ t) {E : Set (Path d)}
    (hE : MeasurableSet[pathFiltration d s] E)
    (hK : ∀ r, r.toNNReal ≤ t → ∀ γ, |G r γ| ≤ K)
    (hHm : Measurable H) (hH : Integrable H P)
    (hC : ∀ r ≤ t, ∀ γ, |M r γ| ≤ H γ) :
    (∫ γ in E, M t γ * (∫ r in (s : ℝ)..t, G r γ) ∂P) =
      ∫ γ in E, (∫ r in (s : ℝ)..t, M r.toNNReal γ * G r γ) ∂P := by
  have ht0 : (s : ℝ) ≤ t := by exact_mod_cast hst
  haveI hfin : IsFiniteMeasure (volume.restrict (Set.uIoc (s : ℝ) t)) := by
    rw [Set.uIoc_of_le ht0]
    infer_instance
  have hMt : StronglyMeasurable (M t) :=
    (hM.stronglyMeasurable t).mono ((pathFiltration d).le t)
  have hHr : Integrable H (P.restrict E) := hH.mono_measure Measure.restrict_le_self
  have hmaj := (hHr.norm.const_mul K).comp_snd
    (volume.restrict (Set.uIoc (s : ℝ) t))
  have hS : ∀ᵐ r ∂(volume.restrict (Set.uIoc (s : ℝ) t)), r.toNNReal ≤ t := by
    refine (ae_restrict_iff' measurableSet_uIoc).2 (ae_of_all _ fun r hr => ?_)
    rw [Set.uIoc_of_le ht0] at hr
    exact Real.toNNReal_le_iff_le_coe.mpr hr.2
  have hm1 : Measurable (fun p : ℝ × Path d => M t p.2 * G p.1 p.2) :=
    (hMt.measurable.comp measurable_snd).mul hGm
  have hm2 : Measurable (fun p : ℝ × Path d => M p.1.toNNReal p.2 * G p.1 p.2) :=
    hMm.mul hGm
  have hi1 : Integrable (Function.uncurry fun (r : ℝ) (γ : Path d) =>
      M t γ * G r γ) ((volume.restrict (Set.uIoc (s : ℝ) t)).prod (P.restrict E)) := by
    refine hmaj.mono' hm1.aestronglyMeasurable ?_
    rw [Measure.ae_prod_iff_ae_ae]
    · filter_upwards [hS] with r hr
      refine ae_of_all _ fun γ => ?_
      show ‖M t γ * G r γ‖ ≤ K * ‖H γ‖
      rw [Real.norm_eq_abs, abs_mul]
      have hh := (hC t le_rfl γ).trans (le_abs_self (H γ))
      simpa [Real.norm_eq_abs, mul_comm] using
        (mul_le_mul hh (hK r hr γ) (abs_nonneg _) (abs_nonneg (H γ)))
    · exact measurableSet_le hm1.norm (measurable_const.mul (hHm.comp measurable_snd).norm)
  have hi2 : Integrable (Function.uncurry fun (r : ℝ) (γ : Path d) =>
      M r.toNNReal γ * G r γ) ((volume.restrict (Set.uIoc (s : ℝ) t)).prod (P.restrict E)) := by
    refine hmaj.mono' hm2.aestronglyMeasurable ?_
    rw [Measure.ae_prod_iff_ae_ae]
    · filter_upwards [hS] with r hr
      refine ae_of_all _ fun γ => ?_
      show ‖M r.toNNReal γ * G r γ‖ ≤ K * ‖H γ‖
      rw [Real.norm_eq_abs, abs_mul]
      have hh := (hC _ hr γ).trans (le_abs_self (H γ))
      simpa [Real.norm_eq_abs, mul_comm] using
        (mul_le_mul hh (hK r hr γ) (abs_nonneg _) (abs_nonneg (H γ)))
    · exact measurableSet_le hm2.norm (measurable_const.mul (hHm.comp measurable_snd).norm)
  calc (∫ γ in E, M t γ * (∫ r in (s : ℝ)..t, G r γ) ∂P) =
      ∫ γ in E, (∫ r in (s : ℝ)..t, M t γ * G r γ) ∂P := by
        refine integral_congr_ae (ae_of_all _ fun γ => ?_)
        simp only
        rw [intervalIntegral.integral_const_mul]
    _ = ∫ r in (s : ℝ)..t, ∫ γ in E, M t γ * G r γ ∂P :=
        (intervalIntegral_integral_swap hi1).symm
    _ = ∫ r in (s : ℝ)..t, ∫ γ in E, M r.toNNReal γ * G r γ ∂P := by
        refine intervalIntegral.integral_congr fun r hr => ?_
        rw [Set.uIcc_of_le ht0] at hr
        have hsr : s ≤ r.toNNReal := by
          apply NNReal.coe_le_coe.mp
          rw [Real.coe_toNNReal r (le_trans s.coe_nonneg hr.1)]
          exact hr.1
        have hrt : r.toNNReal ≤ t := Real.toNNReal_le_iff_le_coe.mpr hr.2
        exact u3_integral_martingale_mul_past_on_event hM hsr hrt hE (hGa r) (hK r hrt)
    _ = ∫ γ in E, (∫ r in (s : ℝ)..t, M r.toNNReal γ * G r γ) ∂P :=
        intervalIntegral_integral_swap hi2

/-- Pathwise weighted Dynkin decomposition over an arbitrary ordered interval. -/
theorem u3_pathwise_weighted_dynkin_interval {a b : ℝ} (hab : a ≤ b)
    {W G L F M A : ℝ → ℝ}
    (hW : AbsolutelyContinuousOnInterval W a b)
    (hWG : ∀ᵐ u ∂(volume.restrict (Set.Ioc a b)), deriv W u = G u)
    (hL : IntervalIntegrable L volume a b)
    (hA : ∀ u ∈ Set.uIcc a b, A u = ∫ v in a..u, L v)
    (hrel : ∀ u ∈ Set.uIcc a b, F u = M u + (F a - M a) + A u)
    (hG : IntervalIntegrable G volume a b)
    (hMG : IntervalIntegrable (fun u => M u * G u) volume a b)
    (hGA : IntervalIntegrable (fun u => G u * A u) volume a b)
    (hWL : IntervalIntegrable (fun u => W u * L u) volume a b) :
    W b * F b - W a * F a = (M b - M a) * W a +
      M b * (∫ u in a..b, G u) +
      (∫ u in a..b, W u * L u + G u * F u) -
      ∫ u in a..b, M u * G u := by
  have hw : W b - W a = ∫ u in a..b, G u := by
    have heq : (∫ u in a..b, deriv W u) = ∫ u in a..b, G u := by
      rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab]
      exact integral_congr_ae hWG
    rw [← heq, hW.integral_deriv_eq_sub]
  have hp : W b * A b = ∫ u in a..b, G u * A u + W u * L u := by
    rw [hA b (Set.right_mem_uIcc), c2_integral_product_indefinite hab hW hL hWG]
    apply intervalIntegral.integral_congr
    intro u hu
    simp only
    rw [hA u hu]
  have hz : (∫ u in a..b, W u * L u + G u * F u) =
      (∫ u in a..b, M u * G u) +
        (F a - M a) * (∫ u in a..b, G u) + W b * A b := by
    rw [hp, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_add hMG (hG.const_mul (F a - M a)),
      ← intervalIntegral.integral_add (hMG.add (hG.const_mul (F a - M a))) (hGA.add hWL)]
    apply intervalIntegral.integral_congr
    intro u hu
    simp only
    rw [hrel u hu]
    ring
  rw [hz, hrel b (Set.right_mem_uIcc)]
  have hm := congrArg (fun z : ℝ => M b * z) hw
  have hf := congrArg (fun z : ℝ => (F a - M a) * z) hw
  nlinarith [hm, hf]

/-- The stopped forced compensator is adapted and integrable under every probability law. -/
theorem u3_forced_compensated_stopped_integrable {d : ℕ} {Λ₀ : ℝ}
    (hΛ : 0 < Λ₀) {ω : FieldPair d} (hω : IsRegular Λ₀ ω)
    (i : Fin d) (lam : ℝ) (T : ℝ≥0) (f : Vec d → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f)
    (Q : Measure (Path d)) [IsProbabilityMeasure Q] :
    let L := External.Draft.svGenerator (reducedCoefficient ω)
      (forcedDrift (reducedCoefficient ω) i lam)
    StronglyAdapted (pathFiltration d) (fun t => compensatedTest L f (min t T)) ∧
      ∀ t, Integrable (compensatedTest L f (min t T)) Q := by
  dsimp only
  obtain ⟨hA, _, ⟨Ma, hAb⟩, _, hb, ⟨Mb, hbb⟩⟩ := reduced_svHypotheses hΛ hω i lam
  have hcoef : BddCoef (reducedCoefficient ω)
      (forcedDrift (reducedCoefficient ω) i lam) (max Ma Mb) :=
    ⟨fun k j => (hA.matrix_elem k j).measurable,
      fun k => (measurable_pi_apply k).comp hb,
      fun y k j => (hAb y k j).trans (le_max_left _ _),
      fun y k => (hbb y k).trans (le_max_right _ _)⟩
  obtain ⟨C, hC⟩ := bounded_svGenerator _ _ hAb hbb (contDiff_two_of_top hf) hc
  obtain ⟨B, hB⟩ := hf.continuous.bounded_above_of_compact_support hc
  have hfB : ∀ y, |f y| ≤ B := fun y => by simpa only [Real.norm_eq_abs] using hB y
  have had := stronglyAdapted_compensatedTest_of_measurable
    (External.Draft.svGenerator (reducedCoefficient ω)
      (forcedDrift (reducedCoefficient ω) i lam)) f hf.continuous (hcoef.measurable_gen f)
  have hstop : StronglyAdapted (pathFiltration d) (fun t =>
      compensatedTest (External.Draft.svGenerator (reducedCoefficient ω)
        (forcedDrift (reducedCoefficient ω) i lam)) f (min t T)) := by
    intro t
    exact (had (min t T)).mono ((pathFiltration d).mono (min_le_left _ _))
  refine ⟨hstop, fun t => ?_⟩
  apply Integrable.of_bound ((hstop t).mono ((pathFiltration d).le t)).aestronglyMeasurable
    (2 * B + C * T)
  exact Filter.Eventually.of_forall fun γ => by
    simpa only [Real.norm_eq_abs] using
      c2_compensatedTest_horizon_bound hfB hC T (min t T) (min_le_right _ _) γ

/-- At zero force the actual finite-horizon tilt is the original law, and the
original martingale problem supplies the deterministically stopped martingale. -/
theorem u3_zero_force_tilted_compensated_martingale {d : ℕ}
    {ω : FieldPair d} (i : Fin d) {x : Vec d} {P : Measure (Path d)}
    (hP : SolvesMartingaleProblem (External.Draft.svGenerator
      (reducedCoefficient ω) (forcedDrift (reducedCoefficient ω) i 0)) x P)
    (T : ℝ≥0) (f : Vec d → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hc : HasCompactSupport f) :
    let Z : Path d → ℝ := fun γ => Real.exp
      ((0 : ℝ) * ((γ T) i - x i) - ∫ u in Set.Ioc (0 : ℝ) (T : ℝ),
        ((0 : ℝ) * forcedDrift (reducedCoefficient ω) i 0 (γ u.toNNReal) i +
          ((0 : ℝ) ^ 2 / 2) * reducedCoefficient ω (γ u.toNNReal) i i))
    Martingale (fun t : ℝ≥0 => compensatedTest (External.Draft.svGenerator
      (reducedCoefficient ω) (forcedDrift (reducedCoefficient ω) i 0)) f (min t T))
      (pathFiltration d) (P.withDensity (fun γ => ENNReal.ofReal (Z γ))) := by
  dsimp only
  have hden : (fun γ : Path d => ENNReal.ofReal (Real.exp
      ((0 : ℝ) * ((γ T) i - x i) - ∫ u in Set.Ioc (0 : ℝ) (T : ℝ),
        ((0 : ℝ) * forcedDrift (reducedCoefficient ω) i 0 (γ u.toNNReal) i +
          ((0 : ℝ) ^ 2 / 2) * reducedCoefficient ω (γ u.toNNReal) i i)))) = 1 := by
    funext γ
    simp
  rw [hden, withDensity_one]
  letI : IsProbabilityMeasure P := hP.1
  have hM := (hP.2.2 f hf hc).2.2
  refine ⟨fun t => (hM.stronglyMeasurable (min t T)).mono
    ((pathFiltration d).mono (min_le_left _ _)), ?_⟩
  intro s t hst
  by_cases hs : s ≤ T
  · simpa only [min_eq_left hs] using hM.condExp_ae_eq (le_min hst hs)
  · have hTs : T ≤ s := le_of_not_ge hs
    have hTt : T ≤ t := hTs.trans hst
    simp only [min_eq_right hTs, min_eq_right hTt]
    exact (condExp_of_stronglyMeasurable ((pathFiltration d).le s)
      ((hM.stronglyMeasurable T).mono ((pathFiltration d).mono hTs))
      (hM.integrable T)).eventuallyEq


/-- A bounded jointly measurable integrand has integrable slices on any interval. -/
theorem u3_intervalIntegrable_bounded_slice {Ω : Type*} [MeasurableSpace Ω]
    {J : ℝ → Ω → ℝ} {a b C : ℝ}
    (hJ : Measurable (fun p : ℝ × Ω => J p.1 p.2))
    (hC : ∀ r ∈ Set.uIcc a b, ∀ ω, |J r ω| ≤ C) (ω : Ω) :
    IntervalIntegrable (fun r => J r ω) volume a b := by
  apply intervalIntegrable_iff.mpr
  have hm : Measurable (fun r => J r ω) :=
    hJ.comp (measurable_id.prodMk measurable_const)
  apply IntegrableOn.of_bound (by simp) hm.aestronglyMeasurable C
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with r hr
  simpa only [Real.norm_eq_abs] using hC r (Set.uIoc_subset_uIcc hr) ω

/-- Bounded time integrals remain integrable after restricting a finite measure. -/
theorem u3_integrable_bounded_interval {Ω : Type*} [MeasurableSpace Ω]
    {Q : Measure Ω} [IsFiniteMeasure Q] {J : ℝ → Ω → ℝ}
    {a b C : ℝ} (hab : a ≤ b)
    (hJ : Measurable (fun p : ℝ × Ω => J p.1 p.2))
    (hC : ∀ r ∈ Set.uIcc a b, ∀ ω, |J r ω| ≤ C) :
    Integrable (fun ω => ∫ r in a..b, J r ω) Q := by
  have hm : Measurable (fun p : Ω × ℝ => J p.2 p.1) :=
    hJ.comp (measurable_snd.prodMk measurable_fst)
  have hInt : StronglyMeasurable (fun ω => ∫ r in Set.Ioc a b, J r ω) :=
    hm.stronglyMeasurable.integral_prod_right' (ν := volume.restrict (Set.Ioc a b))
  apply Integrable.of_bound
    (by simpa only [intervalIntegral.integral_of_le hab] using hInt.aestronglyMeasurable)
    (C * (b - a))
  refine ae_of_all _ fun ω => ?_
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := a)
    (b := b) (f := fun r => J r ω) (C := C)
    (fun r hr => by simpa only [Real.norm_eq_abs] using hC r (Set.uIoc_subset_uIcc hr) ω)
  simpa only [abs_of_nonneg (sub_nonneg.mpr hab)] using hb

/-- Integrating the interval decomposition cancels its two martingale terms. -/
theorem u3_weighted_interval_assembly {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) {X Y U V Z H : Ω → ℝ}
    (hX : Integrable X Q) (hY : Integrable Y Q)
    (hU : Integrable U Q) (hV : Integrable V Q)
    (hZ : Integrable Z Q) (hH : Integrable H Q)
    (hzero : ∫ ω, U ω ∂Q = 0)
    (hcross : (∫ ω, V ω ∂Q) = ∫ ω, H ω ∂Q)
    (hpath : ∀ᵐ ω ∂Q, X ω - Y ω = U ω + V ω + Z ω - H ω) :
    (∫ ω, X ω ∂Q) - (∫ ω, Y ω ∂Q) = ∫ ω, Z ω ∂Q := by
  have heq := integral_congr_ae hpath
  rw [integral_sub hX hY] at heq
  have hsum : (∫ ω, U ω + V ω + Z ω - H ω ∂Q) =
      (∫ ω, U ω ∂Q) + (∫ ω, V ω ∂Q) + (∫ ω, Z ω ∂Q) -
        (∫ ω, H ω ∂Q) := by
    have h1 := integral_sub ((hU.add hV).add hZ) hH
    have h2 := integral_add (hU.add hV) hZ
    have h3 := integral_add hU hV
    simp only [Pi.sub_apply, Pi.add_apply] at h1 h2 h3
    rw [h2, h3] at h1
    exact h1
  rw [hsum, hzero, hcross] at heq
  linarith

/-- The bounded potential weight is absolutely continuous on every positive subinterval. -/
theorem u3_path_weight_interval_ac {d : ℕ} {g : Vec d → ℝ}
    (hg : Measurable g) {K : ℝ} (hK : ∀ y, |g y| ≤ K)
    (γ : Path d) (s t : ℝ≥0) (hst : s ≤ t) :
    AbsolutelyContinuousOnInterval (fun u : ℝ => Real.exp
      (-(∫ v in Set.Ioc (0 : ℝ) (u.toNNReal : ℝ), g (γ v.toNNReal)))) s t := by
  apply (c2_path_weight_toNNReal_absolutelyContinuousOnInterval hg hK γ t).mono
  rw [Set.uIcc_of_le (show (s : ℝ) ≤ t by exact_mod_cast hst),
    Set.uIcc_of_le t.coe_nonneg]
  exact fun _ hu => ⟨s.coe_nonneg.trans hu.1, hu.2⟩

/-- The potential weight has its usual derivative on every positive subinterval. -/
theorem u3_path_weight_interval_deriv {d : ℕ} {g : Vec d → ℝ}
    (hg : Measurable g) {K : ℝ} (hK : ∀ y, |g y| ≤ K)
    (γ : Path d) (s t : ℝ≥0) :
    ∀ᵐ u ∂(volume.restrict (Set.Ioc (s : ℝ) t)),
      deriv (fun v : ℝ => Real.exp
        (-(∫ w in Set.Ioc (0 : ℝ) (v.toNNReal : ℝ), g (γ w.toNNReal)))) u =
      -(g (γ u.toNNReal) * Real.exp
        (-(∫ w in Set.Ioc (0 : ℝ) (u.toNNReal : ℝ), g (γ w.toNNReal)))) := by
  exact ae_restrict_of_ae_restrict_of_subset (Set.Ioc_subset_Ioc s.coe_nonneg le_rfl)
    (c2_path_weight_toNNReal_ae_deriv hg hK γ t)

/-- A compensated test on a subinterval differs from its initial value by
    the test increment minus the generator integral over that subinterval. -/
theorem u3_compensatedTest_interval {d : ℕ}
    (L : (Vec d → ℝ) → Vec d → ℝ) (f : Vec d → ℝ)
    (s u : ℝ≥0) (γ : Path d)
    (h₀ : IntervalIntegrable (fun r : ℝ => L f (γ r.toNNReal)) volume 0 s)
    (h₁ : IntervalIntegrable (fun r : ℝ => L f (γ r.toNNReal)) volume s u) :
    compensatedTest L f u γ - compensatedTest L f s γ =
      f (γ u) - f (γ s) - ∫ r in (s : ℝ)..u, L f (γ r.toNNReal) := by
  have h := intervalIntegral.integral_add_adjacent_intervals h₀ h₁
  simp only [compensatedTest_eq, pathInt]
  linarith

/-- A bounded past factor has zero integral against a martingale increment on a past event. -/
theorem u3_integral_martingale_increment_mul_past_on_event {d : ℕ}
    {P : Measure (Path d)} [IsProbabilityMeasure P]
    {M : ℝ≥0 → Path d → ℝ} (hM : Martingale M (pathFiltration d) P)
    {s t : ℝ≥0} (hst : s ≤ t) {E : Set (Path d)}
    (hE : MeasurableSet[pathFiltration d s] E) {G : Path d → ℝ}
    (hG : StronglyMeasurable[pathFiltration d s] G)
    {K C : ℝ} (hK : ∀ γ, |G γ| ≤ K)
    (hC : ∀ r ≤ t, ∀ γ, |M r γ| ≤ C) :
    (∫ γ in E, (M t γ - M s γ) * G γ ∂P) = 0 := by
  have hGm := hG.mono ((pathFiltration d).le s)
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC t le_rfl 0)
  have hi : ∀ r ≤ t, Integrable (fun γ => M r γ * G γ) (P.restrict E) := by
    intro r hr
    refine Integrable.of_bound
      (((hM.stronglyMeasurable r).mono ((pathFiltration d).le r)).mul hGm).aestronglyMeasurable
      (C * K) (ae_of_all _ fun γ => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hC r hr γ) (hK γ) (abs_nonneg _) hC0
  have he := u3_integral_martingale_mul_past_on_event hM le_rfl hst hE hG hK
  have hs := integral_sub (hi t le_rfl) (hi s hst)
  have hfun : (fun γ => (M t γ - M s γ) * G γ) =
      (fun γ => M t γ * G γ - M s γ * G γ) := by
    funext γ
    ring
  rw [hfun, hs, he, sub_self]


/-- The bounded-potential pathwise decomposition for a compact test on a subinterval. -/
theorem u3_bounded_weighted_dynkin_pathwise {d : ℕ}
    {L : (Vec d → ℝ) → Vec d → ℝ} {f : Vec d → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f)
    (hL : Measurable (L f)) {C : ℝ} (hC : ∀ y, |L f y| ≤ C)
    {g : Vec d → ℝ} (hg : Measurable g) {K : ℝ} (hK : ∀ y, |g y| ≤ K)
    (s t : ℝ≥0) (hst : s ≤ t) (γ : Path d) :
    let W : ℝ → ℝ := fun r => Real.exp
      (-(∫ v in Set.Ioc (0 : ℝ) (r.toNNReal : ℝ), g (γ v.toNNReal)))
    let G : ℝ → ℝ := fun r => -(g (γ r.toNNReal) * W r)
    let M : ℝ → ℝ := fun r => compensatedTest L f r.toNNReal γ
    W t * f (γ t) - W s * f (γ s) =
      (M t - M s) * W s + M t * (∫ r in (s : ℝ)..t, G r) +
        (∫ r in (s : ℝ)..t, W r * L f (γ r.toNNReal) + G r * f (γ r.toNNReal)) -
        ∫ r in (s : ℝ)..t, M r * G r := by
  dsimp only
  obtain ⟨B, hB⟩ := hf.continuous.bounded_above_of_compact_support hc
  have hfB : ∀ y, |f y| ≤ B := fun y => by simpa only [Real.norm_eq_abs] using hB y
  have hab : (s : ℝ) ≤ t := by exact_mod_cast hst
  have ht0 : (0 : ℝ) ≤ t := t.coe_nonneg
  have heval : Measurable (fun p : ℝ × Path d => p.2 p.1.toNNReal) :=
    (continuous_snd.eval (continuous_real_toNNReal.comp continuous_fst)).measurable
  have hLmj : Measurable (fun p : ℝ × Path d => L f (p.2 p.1.toNNReal)) := hL.comp heval
  have hFmj : Measurable (fun p : ℝ × Path d => f (p.2 p.1.toNNReal)) :=
    hf.continuous.measurable.comp heval
  have hWmj := c2_path_weight_joint_measurable hg hK
  obtain ⟨hGmj, D, hD⟩ := c2_path_weight_derivative_joint_bound hg hK t
  obtain ⟨Bw, _, hBw⟩ := c2_path_weight_horizon_bound hK t
  have hMmj := c2_compensatedTest_joint_measurable hf.continuous.measurable hL hC
  have hMb := c2_compensatedTest_horizon_bound hfB hC t
  have htime : ∀ r ∈ Set.uIcc (s : ℝ) t, 0 ≤ r ∧ r.toNNReal ≤ t := by
    intro r hr
    rw [Set.uIcc_of_le hab] at hr
    exact ⟨s.coe_nonneg.trans hr.1, Real.toNNReal_le_iff_le_coe.mpr hr.2⟩
  let W : ℝ → Path d → ℝ := fun r γ => Real.exp
    (-(∫ v in Set.Ioc (0 : ℝ) (r.toNNReal : ℝ), g (γ v.toNNReal)))
  let G : ℝ → Path d → ℝ := fun r γ => -(g (γ r.toNNReal) * W r γ)
  let M : ℝ → Path d → ℝ := fun r γ => compensatedTest L f r.toNNReal γ
  let Lt : ℝ → Path d → ℝ := fun r γ => L f (γ r.toNNReal)
  let F : ℝ → Path d → ℝ := fun r γ => f (γ r.toNNReal)
  let A : ℝ → Path d → ℝ := fun r γ =>
    (∫ v in (0 : ℝ)..(r.toNNReal : ℝ), Lt v γ) -
      (∫ v in (0 : ℝ)..(s : ℝ), Lt v γ)
  have hG : ∀ r ∈ Set.uIcc (s : ℝ) t, ∀ γ, |G r γ| ≤ D :=
    fun r hr γ => hD r (htime r hr).2 γ
  have hM : ∀ r ∈ Set.uIcc (s : ℝ) t, ∀ γ, |M r γ| ≤ 2 * B + C * t :=
    fun r hr γ => hMb r.toNNReal (htime r hr).2 γ
  have hW : ∀ r ∈ Set.uIcc (s : ℝ) t, ∀ γ, |W r γ| ≤ Bw :=
    fun r hr γ => hBw r.toNNReal (htime r hr).2 γ
  have hLt : ∀ r ∈ Set.uIcc (s : ℝ) t, ∀ γ, |Lt r γ| ≤ C := fun _ _ γ => hC _
  have hF : ∀ r ∈ Set.uIcc (s : ℝ) t, ∀ γ, |F r γ| ≤ B := fun _ _ γ => hfB _
  have hAm : Measurable (fun p : ℝ × Path d => A p.1 p.2) := by
    have hm := c2_measurable_path_integral_joint hL hC
    have hfix := hm.comp ((measurable_const : Measurable (fun _ : ℝ × Path d => (s : ℝ))).prodMk measurable_snd)
    convert hm.sub hfix using 1 <;> funext p <;> simp [A, Lt, Function.comp_def]
  have hAeq : ∀ r ∈ Set.uIcc (s : ℝ) t, ∀ γ,
      A r γ = ∫ v in (s : ℝ)..r, Lt v γ := by
    intro r hr γ
    have hi0 := u3_intervalIntegrable_bounded_slice (J := Lt) hLmj
      (a := (0 : ℝ)) (b := (s : ℝ)) (fun _ _ γ => hC _) γ
    have hi1 := u3_intervalIntegrable_bounded_slice (J := Lt) hLmj
      (a := (s : ℝ)) (b := r) (fun _ _ γ => hC _) γ
    have hh := intervalIntegral.integral_add_adjacent_intervals hi0 hi1
    dsimp [A]
    rw [max_eq_left (htime r hr).1]
    linarith
  have hA : ∀ r ∈ Set.uIcc (s : ℝ) t, ∀ γ, |A r γ| ≤ C * t := by
    intro r hr γ
    have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
    have hr' := htime r hr
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := (s : ℝ)) (b := r)
      (f := fun v => Lt v γ) (C := C) (fun v _ => by simpa [Real.norm_eq_abs] using hC (γ v.toNNReal))
    rw [Set.uIcc_of_le hab] at hr
    have : |r - (s : ℝ)| ≤ t := by rw [abs_of_nonneg (sub_nonneg.mpr hr.1)]; linarith [hr.2, s.coe_nonneg]
    have hh : |A r γ| ≤ C * |r - (s : ℝ)| := by
      rw [hAeq r (by rw [Set.uIcc_of_le hab]; exact hr) γ]
      simpa only [Real.norm_eq_abs] using h
    exact hh.trans (mul_le_mul_of_nonneg_left this hC0)
  have hrel : ∀ r ∈ Set.uIcc (s : ℝ) t, F r γ = M r γ + (F s γ - M s γ) + A r γ := by
    intro r hr
    have hi0 := u3_intervalIntegrable_bounded_slice (J := Lt) hLmj (a := (0 : ℝ)) (b := (s : ℝ)) (fun _ _ γ => hC _) γ
    have hi1 := u3_intervalIntegrable_bounded_slice (J := Lt) hLmj (a := (s : ℝ)) (b := r) (fun _ _ γ => hC _) γ
    have h := u3_compensatedTest_interval L f s r.toNNReal γ hi0 (by simpa [Real.coe_toNNReal r (htime r hr).1] using hi1)
    rw [hAeq r hr γ]
    dsimp [F, M, Lt]
    simp only [Real.toNNReal_coe, Real.coe_toNNReal r (htime r hr).1] at h ⊢
    linarith
  have hp := u3_pathwise_weighted_dynkin_interval hab
    (u3_path_weight_interval_ac hg hK γ s t hst)
    (u3_path_weight_interval_deriv hg hK γ s t)
    (u3_intervalIntegrable_bounded_slice hLmj hLt γ) (by intro r hr; exact hAeq r hr γ) hrel
    (u3_intervalIntegrable_bounded_slice hGmj hG γ)
    (u3_intervalIntegrable_bounded_slice (hMmj.mul hGmj) (c2_abs_mul_le_of_bounds hM hG) γ)
    (u3_intervalIntegrable_bounded_slice (hGmj.mul hAm) (c2_abs_mul_le_of_bounds hG hA) γ)
    (u3_intervalIntegrable_bounded_slice (hWmj.mul hLmj) (c2_abs_mul_le_of_bounds hW hLt) γ)
  simpa only [W, G, M, F, Lt, Real.toNNReal_coe] using hp

/-- Conditional weighted Dynkin identity for a bounded generator and potential. -/
theorem u3_weighted_dynkin_on_past_event {d : ℕ}
    {L : (Vec d → ℝ) → Vec d → ℝ} {x : Vec d} {P : Measure (Path d)}
    (hP : SolvesMartingaleProblem L x P) {f : Vec d → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f)
    (hL : Measurable (L f)) {C : ℝ} (hC : ∀ y, |L f y| ≤ C)
    {g : Vec d → ℝ} (hg : Measurable g) {K : ℝ} (hK : ∀ y, |g y| ≤ K)
    (s t : ℝ≥0) (hst : s ≤ t) (E : Set (Path d))
    (hE : MeasurableSet[pathFiltration d s] E) :
    (∫ γ in E, Real.exp (-(∫ v in Set.Ioc (0 : ℝ) (t : ℝ), g (γ v.toNNReal))) * f (γ t) ∂P) -
      (∫ γ in E, Real.exp (-(∫ v in Set.Ioc (0 : ℝ) (s : ℝ), g (γ v.toNNReal))) * f (γ s) ∂P) =
      ∫ γ in E, (∫ r in (s : ℝ)..(t : ℝ),
        Real.exp (-(∫ v in Set.Ioc (0 : ℝ) (r.toNNReal : ℝ), g (γ v.toNNReal))) *
          (L f (γ r.toNNReal) - g (γ r.toNNReal) * f (γ r.toNNReal))) ∂P := by
  letI : IsProbabilityMeasure P := hP.1
  let Q := P.restrict E
  haveI : IsFiniteMeasure Q := inferInstance
  obtain ⟨B, hB⟩ := hf.continuous.bounded_above_of_compact_support hc
  have hfB : ∀ y, |f y| ≤ B := fun y => by simpa only [Real.norm_eq_abs] using hB y
  have hab : (s : ℝ) ≤ t := by exact_mod_cast hst
  let W : ℝ → Path d → ℝ := fun r γ => Real.exp
    (-(∫ v in Set.Ioc (0 : ℝ) (r.toNNReal : ℝ), g (γ v.toNNReal)))
  let G : ℝ → Path d → ℝ := fun r γ => -(g (γ r.toNNReal) * W r γ)
  let M : ℝ → Path d → ℝ := fun r γ => compensatedTest L f r.toNNReal γ
  let Lt : ℝ → Path d → ℝ := fun r γ => L f (γ r.toNNReal)
  let F : ℝ → Path d → ℝ := fun r γ => f (γ r.toNNReal)
  let Z : ℝ → Path d → ℝ := fun r γ => W r γ * Lt r γ + G r γ * F r γ
  have heval : Measurable (fun p : ℝ × Path d => p.2 p.1.toNNReal) :=
    (continuous_snd.eval (continuous_real_toNNReal.comp continuous_fst)).measurable
  have hmW : Measurable (fun p : ℝ × Path d => W p.1 p.2) := c2_path_weight_joint_measurable hg hK
  obtain ⟨hmG, D, hD⟩ := c2_path_weight_derivative_joint_bound hg hK t
  obtain ⟨Bw, hBw0, hBw⟩ := c2_path_weight_horizon_bound hK t
  have hmM := c2_compensatedTest_joint_measurable hf.continuous.measurable hL hC
  have hMb := c2_compensatedTest_horizon_bound hfB hC t
  have hmL : Measurable (fun p : ℝ × Path d => Lt p.1 p.2) := hL.comp heval
  have hmF : Measurable (fun p : ℝ × Path d => F p.1 p.2) := hf.continuous.measurable.comp heval
  have hmZ : Measurable (fun p : ℝ × Path d => Z p.1 p.2) := (hmW.mul hmL).add (hmG.mul hmF)
  have htime : ∀ r ∈ Set.uIcc (s : ℝ) t, r.toNNReal ≤ t := by
    intro r hr
    rw [Set.uIcc_of_le hab] at hr
    exact Real.toNNReal_le_iff_le_coe.mpr hr.2
  have bG : ∀ r ∈ Set.uIcc (s : ℝ) t, ∀ γ, |G r γ| ≤ D := fun r hr γ => hD r (htime r hr) γ
  have bM : ∀ r ∈ Set.uIcc (s : ℝ) t, ∀ γ, |M r γ| ≤ 2 * B + C * t := fun r hr γ => hMb _ (htime r hr) γ
  have bW : ∀ r ∈ Set.uIcc (s : ℝ) t, ∀ γ, |W r γ| ≤ Bw := fun r hr γ => hBw _ (htime r hr) γ
  have bL : ∀ r ∈ Set.uIcc (s : ℝ) t, ∀ γ, |Lt r γ| ≤ C := fun _ _ γ => hC _
  have bF : ∀ r ∈ Set.uIcc (s : ℝ) t, ∀ γ, |F r γ| ≤ B := fun _ _ γ => hfB _
  have bMG := c2_abs_mul_le_of_bounds bM bG
  have bZ : ∀ r ∈ Set.uIcc (s : ℝ) t, ∀ γ, |Z r γ| ≤ Bw * C + D * B :=
    fun r hr γ => (abs_add_le _ _).trans (add_le_add
      (c2_abs_mul_le_of_bounds bW bL r hr γ) (c2_abs_mul_le_of_bounds bG bF r hr γ))
  have hiG : Integrable (fun γ => ∫ r in (s : ℝ)..t, G r γ) Q :=
    u3_integrable_bounded_interval hab hmG bG
  have hiMG : Integrable (fun γ => ∫ r in (s : ℝ)..t, M r γ * G r γ) Q :=
    u3_integrable_bounded_interval hab (hmM.mul hmG) bMG
  have hiZ : Integrable (fun γ => ∫ r in (s : ℝ)..t, Z r γ) Q :=
    u3_integrable_bounded_interval hab hmZ bZ
  have hWt : ∀ u : ℝ≥0, u ≤ t → Integrable (fun γ => W u γ * F u γ) Q := by
    intro u hu
    apply Integrable.of_bound
      (((hmW.comp (measurable_const.prodMk measurable_id)).mul
        (hmF.comp (measurable_const.prodMk measurable_id))).aestronglyMeasurable) (Bw * B)
    refine ae_of_all _ fun γ => ?_
    change |W u γ * F u γ| ≤ Bw * B
    simp only [W, F, Real.toNNReal_coe, abs_mul]
    exact mul_le_mul (hBw u hu γ) (hfB (γ u)) (abs_nonneg _) hBw0
  have hMt : ∀ u : ℝ≥0, u ≤ t → Integrable (fun γ => M u γ) Q := by
    intro u hu
    apply Integrable.of_bound (hmM.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable (2 * B + C * t)
    exact ae_of_all _ fun γ => by
      change |M u γ| ≤ 2 * B + C * t
      simpa only [M, Real.toNNReal_coe] using hMb u hu γ
  have hIbound : ∀ γ, |∫ r in (s : ℝ)..t, G r γ| ≤ D * (t - s) := by
    intro γ
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := (s : ℝ)) (b := t)
      (f := fun r => G r γ) (C := D) (fun r hr => by simpa only [Real.norm_eq_abs] using bG r (Set.uIoc_subset_uIcc hr) γ)
    simpa only [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hab)] using h
  have hU : Integrable (fun γ => (M t γ - M s γ) * W s γ) Q := by
    apply Integrable.of_bound (((hMt t le_rfl).sub (hMt s hst)).aestronglyMeasurable.mul
      ((hmW.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable)) ((2 * (2 * B + C * t)) * Bw)
    refine ae_of_all _ fun γ => ?_
    change |(M t γ - M s γ) * W s γ| ≤ (2 * (2 * B + C * t)) * Bw
    simp only [M, W, Real.toNNReal_coe, abs_mul]
    have hn : 0 ≤ 2 * B + C * t := (abs_nonneg _).trans (hMb t le_rfl γ)
    have hh := mul_le_mul (le_trans (abs_sub _ _) (add_le_add (hMb t le_rfl γ) (hMb s hst γ))) (hBw s hst γ) (abs_nonneg _) (add_nonneg hn hn)
    convert hh using 1 <;> ring
  have hV : Integrable (fun γ => M t γ * (∫ r in (s : ℝ)..t, G r γ)) Q := by
    apply Integrable.of_bound ((hMt t le_rfl).aestronglyMeasurable.mul hiG.aestronglyMeasurable)
      ((2 * B + C * t) * (D * (t - s)))
    refine ae_of_all _ fun γ => ?_
    change |M t γ * (∫ r in (s : ℝ)..t, G r γ)| ≤ (2 * B + C * t) * (D * (t - s))
    simp only [M, Real.toNNReal_coe, abs_mul]
    exact mul_le_mul (hMb t le_rfl γ) (hIbound γ) (abs_nonneg _) ((abs_nonneg _).trans (hMb t le_rfl γ))
  have hzero := u3_integral_martingale_increment_mul_past_on_event (hP.2.2 f hf hc).2.2 hst hE
    (c2_path_weight_stronglyAdapted_of_measurable hg s) (hBw s hst) hMb
  have hcross := u3_integral_martingale_mul_adapted_integral_on_event (hP.2.2 f hf hc).2.2 hmM hmG
    (fun r => c2_path_weight_derivative_stronglyAdapted hg
      (c2_path_weight_stronglyAdapted_of_measurable hg) r.toNNReal) hst hE hD hMb
  have hres := u3_weighted_interval_assembly Q (hWt t le_rfl) (hWt s hst) hU hV hiZ hiMG
    (by simpa only [Q, M, W, Real.toNNReal_coe] using hzero)
    (by simpa only [Q, M, G, W, Real.toNNReal_coe] using hcross)
    (ae_of_all _ fun γ => by
      simpa only [W, G, M, Lt, F, Z, Real.toNNReal_coe] using
        u3_bounded_weighted_dynkin_pathwise hf hc hL hC hg hK s t hst γ)
  have heq : (∫ γ, (∫ r in (s : ℝ)..(t : ℝ), Z r γ) ∂Q) =
      ∫ γ in E, (∫ r in (s : ℝ)..(t : ℝ),
        W r γ * (L f (γ r.toNNReal) - g (γ r.toNNReal) * f (γ r.toNNReal))) ∂P := by
    apply integral_congr_ae
    exact ae_of_all _ fun γ => by
      apply intervalIntegral.integral_congr
      intro r hr
      dsimp [Z, G, Lt, F]
      ring
  rw [heq] at hres
  simpa only [Q, W, F, Real.toNNReal_coe] using hres

/-- Conditional actual-force weighted Dynkin identity on a past event. -/
theorem u3_reduced_force_weighted_dynkin_on_past_event {d : ℕ} {Λ₀ : ℝ}
    (hΛ : 0 < Λ₀) {ω : FieldPair d} (hω : IsRegular Λ₀ ω) (i : Fin d) (lam : ℝ)
    {x : Vec d} {P : Measure (Path d)}
    (hP : SolvesMartingaleProblem (External.Draft.svGenerator
      (reducedCoefficient ω) (forcedDrift (reducedCoefficient ω) i 0)) x P)
    (f : Vec d → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f)
    (s t : ℝ≥0) (hst : s ≤ t) (A : Set (Path d))
    (hA : MeasurableSet[(pathFiltration d) s] A) :
    let V := fun y : Vec d => lam * forcedDrift (reducedCoefficient ω) i 0 y i +
      (lam ^ 2 / 2) * reducedCoefficient ω y i i
    let W : ℝ≥0 → Path d → ℝ := fun t γ =>
      Real.exp (-(∫ u in Set.Ioc (0 : ℝ) (t : ℝ), V (γ u.toNNReal)))
    (∫ γ in A, W t γ * f (γ t) ∂P) - (∫ γ in A, W s γ * f (γ s) ∂P) =
      ∫ γ in A, (∫ u in (s : ℝ)..(t : ℝ),
        W u.toNNReal γ * (External.Draft.svGenerator (reducedCoefficient ω)
          (forcedDrift (reducedCoefficient ω) i 0) f (γ u.toNNReal) -
            V (γ u.toNNReal) * f (γ u.toNNReal))) ∂P := by
  dsimp only
  obtain ⟨hVm, K, hK⟩ := c2_reduced_force_potential_measurable_bounded hΛ hω i lam
  obtain ⟨hL, C, hC⟩ := c2_reduced_generator_measurable_bounded hΛ hω i hf hc
  exact u3_weighted_dynkin_on_past_event hP hf hc hL hC hVm hK s t hst A hA

theorem u3_double_integral_tendsto_zero_on_interval {α : Type*} [MeasurableSpace α] {P : Measure α}
    {s T : ℝ≥0} (hst : s ≤ T) {H : ℕ → ℝ → α → ℝ} {G : α → ℝ}
    (hHm : ∀ k, Measurable (fun p : ℝ × α => H k p.1 p.2))
    (hbound : ∀ k γ, ∀ u ∈ Set.Ioc (s : ℝ) (T : ℝ), ‖H k u γ‖ ≤ G γ)
    (hG : Integrable G P)
    (hzero : ∀ γ, ∀ u ∈ Set.Ioc (s : ℝ) (T : ℝ), ∀ᶠ k in atTop, H k u γ = 0) :
    Tendsto (fun k : ℕ => ∫ γ, (∫ u in Set.Ioc (s : ℝ) (T : ℝ), H k u γ) ∂P) atTop (𝓝 0) := by
  have hfinite : volume (Set.Ioc (s : ℝ) (T : ℝ)) < ⊤ := by simp
  have hinner : ∀ γ, Tendsto (fun k : ℕ => ∫ u in Set.Ioc (s : ℝ) (T : ℝ), H k u γ) atTop
      (𝓝 0) := by
    intro γ
    have hlim := tendsto_integral_of_dominated_convergence (μ := volume.restrict
      (Set.Ioc (s : ℝ) (T : ℝ))) (fun _ => G γ) (F := fun k u => H k u γ) (f := fun _ => 0)
      (fun k => ((hHm k).comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable)
      (by simp)
      (fun k => (ae_restrict_iff' measurableSet_Ioc).mpr
        (Filter.Eventually.of_forall fun u hu => hbound k γ u hu))
      ((ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall fun u hu =>
        tendsto_const_nhds.congr' ((hzero γ u hu).mono fun k hk => hk.symm)))
    simpa using hlim
  have hlim := tendsto_integral_of_dominated_convergence (μ := P) (fun γ => ((T : ℝ) - (s : ℝ)) * G γ)
    (F := fun k γ => ∫ u in Set.Ioc (s : ℝ) (T : ℝ), H k u γ) (f := fun _ => 0)
    (fun k => (StronglyMeasurable.integral_prod_left
      (μ := volume.restrict (Set.Ioc (s : ℝ) (T : ℝ))) (f := fun u γ => H k u γ)
      (hHm k).stronglyMeasurable).aestronglyMeasurable)
    (hG.const_mul ((T : ℝ) - (s : ℝ)))
    (fun k => Filter.Eventually.of_forall fun γ => by
      have h := norm_setIntegral_le_of_norm_le_const (C := G γ) hfinite
        (fun u hu => hbound k γ u hu)
      rw [Real.volume_real_Ioc_of_le (by exact_mod_cast hst)] at h
      rwa [mul_comm] at h)
    (Filter.Eventually.of_forall hinner)
  simpa using hlim

/-- The cutoff error terms in the weighted Dynkin identity vanish in the limit. -/
theorem u3_cutoff_remainder_tendsto_on_past_event {d : ℕ} (hd : 1 ≤ d) {Λ₀ : ℝ} (hΛ : 0 < Λ₀)
    {ω : FieldPair d} (hω : IsRegular Λ₀ ω) (i : Fin d) (lam : ℝ)
    {x : Vec d} {P : Measure (Path d)}
    (hP : SolvesMartingaleProblem (External.Draft.svGenerator
      (reducedCoefficient ω) (forcedDrift (reducedCoefficient ω) i 0)) x P) (s T : ℝ≥0) (hst : s ≤ T) (E : Set (Path d))
    {χ : Vec d → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hcs : HasCompactSupport χ)
    (h1 : ∀ y : Vec d, ‖y‖ ≤ 1 → χ y = 1) :
    let V : Vec d → ℝ := fun y => lam * forcedDrift (reducedCoefficient ω) i 0 y i +
      (lam ^ 2 / 2) * reducedCoefficient ω y i i
    let f : ℕ → Vec d → ℝ := fun k z => χ (((k : ℝ) + 1)⁻¹ • z) *
      Real.exp (lam * (z i - x i))
    Tendsto (fun k : ℕ => ∫ γ : Path d, (∫ u in Set.Ioc (s : ℝ) (T : ℝ),
      Real.exp (-(∫ v in Set.Ioc (0 : ℝ) (u.toNNReal : ℝ), V (γ v.toNNReal))) *
        (External.Draft.svGenerator (reducedCoefficient ω)
          (forcedDrift (reducedCoefficient ω) i 0) (f k) (γ u.toNNReal) -
            V (γ u.toNNReal) * f k (γ u.toNNReal))) ∂(P.restrict E)) atTop (𝓝 0) := by
  intro V f
  obtain ⟨hcont, _, ⟨A, hA⟩, _, hm, ⟨B, hB⟩⟩ := reduced_svHypotheses hΛ hω i 0
  obtain ⟨hVm, K, hK⟩ := c2_reduced_force_potential_measurable_bounded hΛ hω i lam
  obtain ⟨Bw, hBw0, hBw⟩ := c2_path_weight_horizon_bound hK T
  obtain ⟨C, hC0, hC⟩ := c27_cutoff_exp_generator hA hB i lam x hχ hcs h1
  have hmax := c16_reduced_textbook_exp_coordinate_max_integrable hd hΛ hω i hP |lam| T
  have hfk : ∀ k : ℕ, ContDiff ℝ (⊤ : ℕ∞) (f k) ∧ HasCompactSupport (f k) := fun k => by
    refine ⟨(hχ.comp (contDiff_const_smul _)).mul ?_, ?_⟩
    · exact Real.contDiff_exp.comp (contDiff_const.mul ((contDiff_apply ℝ ℝ i).sub contDiff_const))
    · exact (hcs.comp_homeomorph (Homeomorph.smulOfNeZero (((k : ℝ) + 1)⁻¹)
        (inv_ne_zero (by positivity)))).mul_right
  have hGm : ∀ k : ℕ, Measurable (External.Draft.svGenerator (reducedCoefficient ω)
      (forcedDrift (reducedCoefficient ω) i 0) (f k)) := fun k =>
    (c2_reduced_generator_measurable_bounded hΛ hω i (hfk k).1 (hfk k).2).1
  have heval : Measurable (fun p : ℝ × Path d => p.2 p.1.toNNReal) :=
    (continuous_snd.eval (continuous_real_toNNReal.comp continuous_fst)).measurable
  have hWj := c2_path_weight_joint_measurable hVm hK
  refine u3_double_integral_tendsto_zero_on_interval (P := P.restrict E) (s := s) (T := T) hst (G := fun γ : Path d =>
    Bw * (C * Real.exp (|lam| * sSup ((fun t : ℝ≥0 => |(γ t) i - x i|) '' Set.Icc 0 T))))
    (H := fun k u γ => Real.exp (-(∫ v in Set.Ioc (0 : ℝ) (u.toNNReal : ℝ), V (γ v.toNNReal))) *
        (External.Draft.svGenerator (reducedCoefficient ω)
          (forcedDrift (reducedCoefficient ω) i 0) (f k) (γ u.toNNReal) -
            V (γ u.toNNReal) * f k (γ u.toNNReal))) ?_ ?_ (((hmax.const_mul C).const_mul Bw).mono_measure Measure.restrict_le_self) ?_
  · exact fun k => hWj.mul (((hGm k).comp heval).sub ((hVm.comp heval).mul
      ((hfk k).1.continuous.measurable.comp heval)))
  · intro k γ u hu
    have huT : u.toNNReal ≤ T := Real.toNNReal_le_iff_le_coe.mpr hu.2
    rw [Real.norm_eq_abs, abs_mul]
    refine mul_le_mul (hBw u.toNNReal huT γ) ?_ (abs_nonneg _) hBw0
    refine ((hC k (γ u.toNNReal)).2).trans ?_
    exact mul_le_mul_of_nonneg_left (c27_exp_coord_le_max i lam x γ T _ huT) hC0
  · intro γ u hu
    obtain ⟨R, hR⟩ := c27_path_norm_bounded γ T
    obtain ⟨N, hN⟩ := exists_nat_gt R
    filter_upwards [Filter.eventually_ge_atTop N] with k hk
    have hkN : (N : ℝ) ≤ k := Nat.cast_le.mpr hk
    have := (hC k (γ u.toNNReal)).1 (by
      have := hR u.toNNReal (Real.toNNReal_le_iff_le_coe.mpr hu.2)
      linarith)
    simp only [V, f] at this ⊢
    rw [this, mul_zero]


/-- The signed density has equal integrals on every event in the past. -/
theorem u3_reduced_force_density_integral_on_past_event {d : ℕ} (hd : 1 ≤ d)
    {Λ₀ : ℝ} (hΛ : 0 < Λ₀) {ω : FieldPair d} (hω : IsRegular Λ₀ ω)
    (i : Fin d) {x : Vec d} {P : Measure (Path d)}
    (hP : SolvesMartingaleProblem (External.Draft.svGenerator
      (reducedCoefficient ω) (forcedDrift (reducedCoefficient ω) i 0)) x P)
    (lam : ℝ) (s t : ℝ≥0) (hst : s ≤ t) (E : Set (Path d))
    (hE : MeasurableSet[pathFiltration d s] E) :
    let Z : ℝ≥0 → Path d → ℝ := fun v γ => Real.exp
      (lam * ((γ v) i - x i) - ∫ u in Set.Ioc (0 : ℝ) (v : ℝ),
        (lam * forcedDrift (reducedCoefficient ω) i 0 (γ u.toNNReal) i +
          (lam ^ 2 / 2) * reducedCoefficient ω (γ u.toNNReal) i i))
    (∫ γ in E, Z t γ ∂P) = ∫ γ in E, Z s γ ∂P := by
  intro Z
  letI : IsProbabilityMeasure P := hP.1
  obtain ⟨χ, hχ, hcs, h1, h01⟩ := c27_exists_cutoff d
  let f : ℕ → Vec d → ℝ := fun k z => χ (((k : ℝ) + 1)⁻¹ • z) * Real.exp (lam * (z i - x i))
  let V : Vec d → ℝ := fun y => lam * forcedDrift (reducedCoefficient ω) i 0 y i +
      (lam ^ 2 / 2) * reducedCoefficient ω y i i
  let W : ℝ≥0 → Path d → ℝ := fun v γ => Real.exp (-(∫ u in Set.Ioc (0 : ℝ) (v : ℝ), V (γ u.toNNReal)))
  have hfk : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (f k) ∧ HasCompactSupport (f k) := fun k => by
    refine ⟨(hχ.comp (contDiff_const_smul _)).mul ?_, ?_⟩
    · exact Real.contDiff_exp.comp (contDiff_const.mul ((contDiff_apply ℝ ℝ i).sub contDiff_const))
    · exact (hcs.comp_homeomorph (Homeomorph.smulOfNeZero (((k : ℝ) + 1)⁻¹)
        (inv_ne_zero (by positivity)))).mul_right
  have hlim : ∀ v : ℝ≥0, Tendsto (fun k : ℕ => ∫ γ in E, W v γ * f k (γ v) ∂P)
      atTop (𝓝 (∫ γ in E, Z v γ ∂P)) := by
    intro v
    have hZ := (u3_reduced_force_exponential_weight_integral hd hΛ hω i hP lam v).1
    have hWm := (c25_reduced_force_path_weight_measurable hΛ hω i lam v).1
    have heq : ∀ γ, Z v γ = W v γ * Real.exp (lam * (γ v i - x i)) := fun γ => by
      dsimp [Z, W, V]; rw [← Real.exp_add]; congr 1; ring
    refine tendsto_integral_of_dominated_convergence (μ := P.restrict E) (Z v) (fun k => ?_)
      (hZ.mono_measure Measure.restrict_le_self) (fun k => ?_) ?_
    · exact (hWm.mul (((hfk k).1.continuous.measurable).comp
        (continuous_eval_const v).measurable)).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun γ => ?_
      have hc := h01 (((k : ℝ) + 1)⁻¹ • γ v)
      have key : ∀ w g c : ℝ, 0 < w → 0 < g → 0 ≤ c → c ≤ 1 → ‖w * (c * g)‖ ≤ w * g :=
        fun w g c hw hg hc0 hc1 => by
          rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
          nlinarith [mul_pos hw hg]
      rw [heq γ]
      exact key _ _ _ (by dsimp [W]; exact Real.exp_pos _) (Real.exp_pos _) hc.1 hc.2
    · refine Filter.Eventually.of_forall fun γ => ?_
      obtain ⟨N, hN⟩ := exists_nat_gt ‖γ v‖
      apply tendsto_const_nhds.congr'
      filter_upwards [Filter.eventually_ge_atTop N] with k hk
      have hkN : (N : ℝ) ≤ k := Nat.cast_le.mpr hk
      have hk0 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
      have hn : ‖((k : ℝ) + 1)⁻¹ • γ v‖ ≤ 1 := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hk0), inv_mul_le_iff₀ hk0]
        linarith
      rw [heq γ]; dsimp [f]; rw [h1 _ hn, one_mul]
  have hrem := u3_cutoff_remainder_tendsto_on_past_event hd hΛ hω i lam hP s t hst E hχ hcs h1
  have hdyn := fun k => u3_reduced_force_weighted_dynkin_on_past_event hΛ hω i lam hP (f k) (hfk k).1 (hfk k).2 s t hst E hE
  have hzero : Tendsto (fun k : ℕ => (∫ γ in E, W t γ * f k (γ t) ∂P) -
      (∫ γ in E, W s γ * f k (γ s) ∂P)) atTop (𝓝 0) := by
    refine hrem.congr fun k => ?_
    have h := hdyn k
    simpa only [V, W, f, intervalIntegral.integral_of_le (show (s : ℝ) ≤ t by exact_mod_cast hst)] using h.symm
  have h := tendsto_nhds_unique ((hlim t).sub (hlim s)) hzero
  linarith

/-- The signed exponential density is a martingale under the supplied source law. -/
theorem u3_reduced_force_density_martingale {d : ℕ} (hd : 1 ≤ d)
    {Λ₀ : ℝ} (hΛ : 0 < Λ₀) {ω : FieldPair d} (hω : IsRegular Λ₀ ω)
    (i : Fin d) {x : Vec d} {P : Measure (Path d)}
    (hP : SolvesMartingaleProblem (External.Draft.svGenerator
      (reducedCoefficient ω) (forcedDrift (reducedCoefficient ω) i 0)) x P)
    (lam : ℝ) :
    let Z : ℝ≥0 → Path d → ℝ := fun v γ => Real.exp
      (lam * ((γ v) i - x i) - ∫ u in Set.Ioc (0 : ℝ) (v : ℝ),
        (lam * forcedDrift (reducedCoefficient ω) i 0 (γ u.toNNReal) i +
          (lam ^ 2 / 2) * reducedCoefficient ω (γ u.toNNReal) i i))
    Martingale Z (pathFiltration d) P := by
  intro Z
  letI : IsProbabilityMeasure P := hP.1
  have h := u3_reduced_force_density_adapted_integrable hd hΛ hω i hP lam
  refine ⟨h.1, ?_⟩
  intro s t hst
  apply Filter.EventuallyEq.symm
  apply ae_eq_condExp_of_forall_setIntegral_eq ((pathFiltration d).le s) (h.2 t).1
  · intro E hE hfinite
    exact (h.2 s).1.integrableOn
  · intro E hE hfinite
    exact (u3_reduced_force_density_integral_on_past_event hd hΛ hω i hP lam s t hst E hE).symm
  · exact (h.1 s).aestronglyMeasurable

/-- A terminal tilt agrees on past events with the tilt at the event's time. -/
theorem u3_reduced_force_terminal_tilt_on_past_event {d : ℕ} (hd : 1 ≤ d)
    {Λ₀ : ℝ} (hΛ : 0 < Λ₀) {ω : FieldPair d} (hω : IsRegular Λ₀ ω)
    (i : Fin d) {x : Vec d} {P : Measure (Path d)}
    (hP : SolvesMartingaleProblem (External.Draft.svGenerator
      (reducedCoefficient ω) (forcedDrift (reducedCoefficient ω) i 0)) x P)
    (lam : ℝ) (s T : ℝ≥0) (hsT : s ≤ T) (E : Set (Path d))
    (hE : MeasurableSet[pathFiltration d s] E) :
    let Z : ℝ≥0 → Path d → ℝ := fun v γ => Real.exp
      (lam * ((γ v) i - x i) - ∫ u in Set.Ioc (0 : ℝ) (v : ℝ),
        (lam * forcedDrift (reducedCoefficient ω) i 0 (γ u.toNNReal) i +
          (lam ^ 2 / 2) * reducedCoefficient ω (γ u.toNNReal) i i))
    P.withDensity (fun γ => ENNReal.ofReal (Z T γ)) E =
      P.withDensity (fun γ => ENNReal.ofReal (Z s γ)) E := by
  intro Z
  have hm : MeasurableSet E := (pathFiltration d).le s E hE
  have hi := u3_reduced_force_density_adapted_integrable hd hΛ hω i hP lam
  rw [withDensity_apply _ hm, withDensity_apply _ hm,
    ← ofReal_integral_eq_lintegral_ofReal ((hi.2 T).1.integrableOn)
      (Filter.Eventually.of_forall fun γ => (Real.exp_pos _).le),
    ← ofReal_integral_eq_lintegral_ofReal ((hi.2 s).1.integrableOn)
      (Filter.Eventually.of_forall fun γ => (Real.exp_pos _).le)]
  rw [u3_reduced_force_density_integral_on_past_event hd hΛ hω i hP lam s T hsT E hE]

/-- Exponential conjugation converts the zero-force textbook generator to the signed one. -/
theorem u3_reduced_svGenerator_exponential_conjugation {d : ℕ} {Λ₀ : ℝ}
    {ω : FieldPair d} (hω : IsRegular Λ₀ ω) (i : Fin d) (lam : ℝ)
    (x y : Vec d) {f : Vec d → ℝ} (hf : ContDiff ℝ 2 f) :
    External.Draft.svGenerator (reducedCoefficient ω)
      (forcedDrift (reducedCoefficient ω) i 0)
      (fun z => f z * Real.exp (lam * (z i - x i))) y -
      (lam * forcedDrift (reducedCoefficient ω) i 0 y i +
        lam ^ 2 / 2 * reducedCoefficient ω y i i) *
        (f y * Real.exp (lam * (y i - x i))) =
      Real.exp (lam * (y i - x i)) *
        External.Draft.svGenerator (reducedCoefficient ω)
          (forcedDrift (reducedCoefficient ω) i lam) f y := by
  have hs (j k : Fin d) : reducedCoefficient ω y j k = reducedCoefficient ω y k j := by
    have h := congrArg (fun M : Mat d => M j k) (reducedCoefficient_symm hω y)
    exact h.symm
  rw [c27_svGenerator_mul_exp _ _ _ _ _ hf]
  congr 1
  unfold External.Draft.svGenerator
  simp only [forcedDrift, zero_mul, add_zero, Matrix.mulVec, dotProduct,
    unitVector, Pi.single_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp only [mul_add, Finset.sum_add_distrib]
  have hcross : (∑ j, ∑ k, reducedCoefficient ω y j k *
      (lam * (if j = i then 1 else 0) * fderiv ℝ f y (unitVector k))) =
      lam * ∑ k, reducedCoefficient ω y k i * fderiv ℝ f y (unitVector k) := by
    simp only [mul_ite, ite_mul, mul_one, mul_zero, zero_mul]
    rw [Finset.sum_eq_single i (fun j _ hj => by simp [hj]) (by simp)]
    simp only [↓reduceIte, mul_one]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    rw [hs i k]
    ring
  have hcross' : (∑ j, ∑ k, reducedCoefficient ω y j k *
      (lam * (if k = i then 1 else 0) * fderiv ℝ f y (unitVector j))) =
      lam * ∑ j, reducedCoefficient ω y j i * fderiv ℝ f y (unitVector j) := by
    simp only [mul_ite, ite_mul, mul_one, mul_zero, zero_mul]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  simp only [mul_ite, mul_one, mul_zero, unitVector] at hcross hcross'
  rw [hcross, hcross']
  simp only [add_mul, Finset.sum_add_distrib]
  have hfactor : (∑ j, lam * reducedCoefficient ω y j i *
      fderiv ℝ f y (unitVector j)) = lam * ∑ j, reducedCoefficient ω y j i *
        fderiv ℝ f y (unitVector j) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  simp only [unitVector] at hfactor
  rw [hfactor]
  ring


/-- Weighted Dynkin identity for the signed textbook generator on past events. -/
theorem u3_reduced_force_density_dynkin_on_past_event {d : ℕ} {Λ₀ : ℝ}
    (hΛ : 0 < Λ₀) {ω : FieldPair d} (hω : IsRegular Λ₀ ω) (i : Fin d) (lam : ℝ)
    {x : Vec d} {P : Measure (Path d)}
    (hP : SolvesMartingaleProblem (External.Draft.svGenerator
      (reducedCoefficient ω) (forcedDrift (reducedCoefficient ω) i 0)) x P)
    (f : Vec d → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f)
    (s t : ℝ≥0) (hst : s ≤ t) (A : Set (Path d))
    (hA : MeasurableSet[(pathFiltration d) s] A) :
    let Z : ℝ≥0 → Path d → ℝ := fun v γ => Real.exp
      (lam * ((γ v) i - x i) - ∫ u in Set.Ioc (0 : ℝ) (v : ℝ),
        (lam * forcedDrift (reducedCoefficient ω) i 0 (γ u.toNNReal) i +
          (lam ^ 2 / 2) * reducedCoefficient ω (γ u.toNNReal) i i))
    (∫ γ in A, Z t γ * f (γ t) ∂P) - (∫ γ in A, Z s γ * f (γ s) ∂P) =
      ∫ γ in A, (∫ u in (s : ℝ)..(t : ℝ), Z u.toNNReal γ *
        External.Draft.svGenerator (reducedCoefficient ω)
          (forcedDrift (reducedCoefficient ω) i lam) f (γ u.toNNReal)) ∂P := by
  let g : Vec d → ℝ := fun z => f z * Real.exp (lam * (z i - x i))
  have hg : ContDiff ℝ (⊤ : ℕ∞) g := hf.mul
    (Real.contDiff_exp.comp (contDiff_const.mul ((contDiff_apply ℝ ℝ i).sub contDiff_const)))
  have hgc : HasCompactSupport g := hc.mul_right
  have h := u3_reduced_force_weighted_dynkin_on_past_event hΛ hω i lam hP g hg hgc s t hst A hA
  have hident (v : ℝ≥0) (γ : Path d) :
      Real.exp (-(∫ u in Set.Ioc (0 : ℝ) (v : ℝ),
        (lam * forcedDrift (reducedCoefficient ω) i 0 (γ u.toNNReal) i +
          (lam ^ 2 / 2) * reducedCoefficient ω (γ u.toNNReal) i i))) *
        g (γ v) = Real.exp (lam * (γ v i - x i) -
          ∫ u in Set.Ioc (0 : ℝ) (v : ℝ),
            (lam * forcedDrift (reducedCoefficient ω) i 0 (γ u.toNNReal) i +
              (lam ^ 2 / 2) * reducedCoefficient ω (γ u.toNNReal) i i)) * f (γ v) := by
    dsimp [g]
    rw [Real.exp_sub, Real.exp_neg]
    ring
  dsimp only at h ⊢
  simp_rw [hident] at h
  convert h using 1
  apply integral_congr_ae
  filter_upwards [] with γ
  apply intervalIntegral.integral_congr
  intro u hu
  dsimp [g]
  rw [u3_reduced_svGenerator_exponential_conjugation hω i lam x (γ u.toNNReal) (hf.of_le (by simp))]
  rw [Real.exp_sub, Real.exp_neg]
  ring

/-- Integrals of past-measurable observables do not depend on the later tilt horizon. -/
theorem u3_reduced_force_terminal_tilt_integral_on_past {d : ℕ} (hd : 1 ≤ d)
    {Λ₀ : ℝ} (hΛ : 0 < Λ₀) {ω : FieldPair d} (hω : IsRegular Λ₀ ω)
    (i : Fin d) {x : Vec d} {P : Measure (Path d)}
    (hP : SolvesMartingaleProblem (External.Draft.svGenerator
      (reducedCoefficient ω) (forcedDrift (reducedCoefficient ω) i 0)) x P)
    (lam : ℝ) (s T : ℝ≥0) (hsT : s ≤ T) (f : Path d → ℝ)
    (hf : StronglyMeasurable[pathFiltration d s] f) :
    let Z : ℝ≥0 → Path d → ℝ := fun v γ => Real.exp
      (lam * ((γ v) i - x i) - ∫ u in Set.Ioc (0 : ℝ) (v : ℝ),
        (lam * forcedDrift (reducedCoefficient ω) i 0 (γ u.toNNReal) i +
          (lam ^ 2 / 2) * reducedCoefficient ω (γ u.toNNReal) i i))
    (∫ γ, f γ ∂(P.withDensity (fun γ => ENNReal.ofReal (Z T γ)))) =
      ∫ γ, f γ ∂(P.withDensity (fun γ => ENNReal.ofReal (Z s γ))) := by
  intro Z
  have heq : (P.withDensity (fun γ => ENNReal.ofReal (Z T γ))).trim
      ((pathFiltration d).le s) =
      (P.withDensity (fun γ => ENNReal.ofReal (Z s γ))).trim
      ((pathFiltration d).le s) := by
    refine @Measure.ext _ (pathFiltration d s) _ _ (fun E hE => ?_)
    rw [trim_measurableSet_eq _ hE, trim_measurableSet_eq _ hE]
    exact u3_reduced_force_terminal_tilt_on_past_event hd hΛ hω i hP lam s T hsT E hE
  rw [integral_trim ((pathFiltration d).le s) hf,
    integral_trim ((pathFiltration d).le s) hf, heq]


/-- A terminal tilt integrates a past observable using its current density. -/
theorem u3_reduced_force_terminal_tilt_integral_eq_density {d : ℕ} (hd : 1 ≤ d)
    {Λ₀ : ℝ} (hΛ : 0 < Λ₀) {ω : FieldPair d} (hω : IsRegular Λ₀ ω)
    (i : Fin d) {x : Vec d} {P : Measure (Path d)}
    (hP : SolvesMartingaleProblem (External.Draft.svGenerator
      (reducedCoefficient ω) (forcedDrift (reducedCoefficient ω) i 0)) x P)
    (lam : ℝ) (s T : ℝ≥0) (hsT : s ≤ T) (f : Path d → ℝ)
    (hf : StronglyMeasurable[pathFiltration d s] f) :
    let Z : ℝ≥0 → Path d → ℝ := fun v γ => Real.exp
      (lam * ((γ v) i - x i) - ∫ u in Set.Ioc (0 : ℝ) (v : ℝ),
        (lam * forcedDrift (reducedCoefficient ω) i 0 (γ u.toNNReal) i +
          (lam ^ 2 / 2) * reducedCoefficient ω (γ u.toNNReal) i i))
    (∫ γ, f γ ∂(P.withDensity (fun γ => ENNReal.ofReal (Z T γ)))) =
      ∫ γ, Z s γ * f γ ∂P := by
  intro Z
  have hz : Measurable (Z s) :=
    (((u3_reduced_force_density_adapted_integrable hd hΛ hω i hP lam).1 s).mono
      ((pathFiltration d).le s)).measurable
  rw [u3_reduced_force_terminal_tilt_integral_on_past hd hΛ hω i hP lam s T hsT f hf,
    integral_withDensity_eq_integral_toReal_smul hz.ennreal_ofReal
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards [] with γ
  rw [ENNReal.toReal_ofReal (Real.exp_pos _).le, smul_eq_mul]


/-- The same density transfer holds when integration is restricted to a past event. -/
theorem u3_reduced_force_terminal_tilt_setIntegral_eq_density {d : ℕ} (hd : 1 ≤ d)
    {Λ₀ : ℝ} (hΛ : 0 < Λ₀) {ω : FieldPair d} (hω : IsRegular Λ₀ ω)
    (i : Fin d) {x : Vec d} {P : Measure (Path d)}
    (hP : SolvesMartingaleProblem (External.Draft.svGenerator
      (reducedCoefficient ω) (forcedDrift (reducedCoefficient ω) i 0)) x P)
    (lam : ℝ) (s T : ℝ≥0) (hsT : s ≤ T) (E : Set (Path d))
    (hE : MeasurableSet[pathFiltration d s] E) (f : Path d → ℝ)
    (hf : StronglyMeasurable[pathFiltration d s] f) :
    let Z : ℝ≥0 → Path d → ℝ := fun v γ => Real.exp
      (lam * ((γ v) i - x i) - ∫ u in Set.Ioc (0 : ℝ) (v : ℝ),
        (lam * forcedDrift (reducedCoefficient ω) i 0 (γ u.toNNReal) i +
          (lam ^ 2 / 2) * reducedCoefficient ω (γ u.toNNReal) i i))
    (∫ γ in E, f γ ∂(P.withDensity (fun γ => ENNReal.ofReal (Z T γ)))) =
      ∫ γ in E, Z s γ * f γ ∂P := by
  intro Z
  have hEa : MeasurableSet E := (pathFiltration d).le s E hE
  have h := u3_reduced_force_terminal_tilt_integral_eq_density hd hΛ hω i hP
    lam s T hsT (E.indicator f) (hf.indicator hE)
  dsimp only at h
  rw [integral_indicator hEa] at h
  calc
    (∫ γ in E, f γ ∂(P.withDensity (fun γ => ENNReal.ofReal (Z T γ)))) =
        ∫ γ, Z s γ * E.indicator f γ ∂P := h
    _ = ∫ γ, E.indicator (fun γ => Z s γ * f γ) γ ∂P := by
      apply integral_congr_ae
      filter_upwards [] with γ
      by_cases hγ : γ ∈ E <;> simp [hγ]
    _ = ∫ γ in E, Z s γ * f γ ∂P := integral_indicator hEa


/-- The signed density can be moved inside a bounded adapted time integral on past events. -/
theorem u3_reduced_force_density_mul_adapted_integral_on_event {d : ℕ} (hd : 1 ≤ d)
    {Λ₀ : ℝ} (hΛ : 0 < Λ₀) {ω : FieldPair d} (hω : IsRegular Λ₀ ω)
    (i : Fin d) {x : Vec d} {P : Measure (Path d)}
    (hP : SolvesMartingaleProblem (External.Draft.svGenerator
      (reducedCoefficient ω) (forcedDrift (reducedCoefficient ω) i 0)) x P)
    (lam : ℝ) {G : ℝ → Path d → ℝ}
    (hGm : Measurable (fun p : ℝ × Path d => G p.1 p.2))
    (hGa : ∀ r : ℝ, StronglyMeasurable[pathFiltration d r.toNNReal] (G r))
    {K : ℝ} {s t : ℝ≥0} (hst : s ≤ t) {E : Set (Path d)}
    (hE : MeasurableSet[pathFiltration d s] E)
    (hK : ∀ r, r.toNNReal ≤ t → ∀ γ, |G r γ| ≤ K) :
    let Z : ℝ≥0 → Path d → ℝ := fun v γ => Real.exp
      (lam * ((γ v) i - x i) - ∫ u in Set.Ioc (0 : ℝ) (v : ℝ),
        (lam * forcedDrift (reducedCoefficient ω) i 0 (γ u.toNNReal) i +
          (lam ^ 2 / 2) * reducedCoefficient ω (γ u.toNNReal) i i))
    (∫ γ in E, Z t γ * (∫ r in (s : ℝ)..t, G r γ) ∂P) =
      ∫ γ in E, (∫ r in (s : ℝ)..t, Z r.toNNReal γ * G r γ) ∂P := by
  intro Z
  letI : IsProbabilityMeasure P := hP.1
  obtain ⟨hg, L, hL⟩ := c2_reduced_force_potential_measurable_bounded hΛ hω i lam
  obtain ⟨B, hB, hbound⟩ := c2_path_weight_horizon_bound hL t
  have heval : Measurable (fun p : ℝ × Path d => p.2 p.1.toNNReal) :=
    (continuous_snd.eval (continuous_real_toNNReal.comp continuous_fst)).measurable
  have he : Measurable (fun p : ℝ × Path d => Real.exp
      (lam * (p.2 p.1.toNNReal i - x i))) := Real.measurable_exp.comp
    (measurable_const.mul (((measurable_pi_apply i).comp heval).sub measurable_const))
  have hMm : Measurable (fun p : ℝ × Path d => Z p.1.toNNReal p.2) := by
    convert he.mul (c2_path_weight_joint_measurable hg hL) using 1 <;> funext p
    simp only [Z, sub_eq_add_neg, Real.exp_add, Pi.mul_apply]
  let H : Path d → ℝ := fun γ => B * Real.exp (|lam| *
    sSup ((fun v : ℝ≥0 => |(γ v) i - x i|) '' Set.Icc 0 t))
  have hHm : Measurable H := measurable_const.mul (Real.measurable_exp.comp
    (measurable_const.mul (c16_continuous_coordinate_max i x t).measurable))
  have hHi : Integrable H P :=
    (c16_reduced_textbook_exp_coordinate_max_integrable hd hΛ hω i hP |lam| t).const_mul B
  refine u3_integral_dominated_martingale_mul_adapted_integral_on_event
    (u3_reduced_force_density_martingale hd hΛ hω i hP lam) hMm hGm hGa hst hE hK hHm hHi ?_
  intro r hr γ
  rw [abs_of_pos (Real.exp_pos _)]
  have hc := c27_exp_coord_le_max i lam x γ t r hr
  have hw := hbound r hr γ
  rw [abs_of_pos (Real.exp_pos _)] at hw
  have h := mul_le_mul hc hw (Real.exp_pos _).le (Real.exp_pos _).le
  simpa only [Z, H, sub_eq_add_neg, Real.exp_add, mul_comm] using h


/-- A signed terminal tilt transfers a bounded generator integral to the running density. -/
theorem u3_reduced_force_tilt_generator_integral_on_event {d : ℕ} (hd : 1 ≤ d)
    {Λ₀ : ℝ} (hΛ : 0 < Λ₀) {ω : FieldPair d} (hω : IsRegular Λ₀ ω)
    (i : Fin d) {x : Vec d} {P : Measure (Path d)}
    (hP : SolvesMartingaleProblem (External.Draft.svGenerator
      (reducedCoefficient ω) (forcedDrift (reducedCoefficient ω) i 0)) x P)
    (lam : ℝ) (f : Vec d → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hc : HasCompactSupport f) (s t T : ℝ≥0) (hst : s ≤ t) (htT : t ≤ T)
    (E : Set (Path d)) (hE : MeasurableSet[pathFiltration d s] E) :
    let L := External.Draft.svGenerator (reducedCoefficient ω)
      (forcedDrift (reducedCoefficient ω) i lam)
    let Z : ℝ≥0 → Path d → ℝ := fun v γ => Real.exp
      (lam * ((γ v) i - x i) - ∫ u in Set.Ioc (0 : ℝ) (v : ℝ),
        (lam * forcedDrift (reducedCoefficient ω) i 0 (γ u.toNNReal) i +
          (lam ^ 2 / 2) * reducedCoefficient ω (γ u.toNNReal) i i))
    (∫ γ in E, (∫ r in (s : ℝ)..t, L f (γ r.toNNReal))
      ∂(P.withDensity (fun γ => ENNReal.ofReal (Z T γ)))) =
      ∫ γ in E, (∫ r in (s : ℝ)..t, Z r.toNNReal γ * L f (γ r.toNNReal)) ∂P := by
  intro L Z
  obtain ⟨hA, _, ⟨Ma, hAb⟩, _, hb, ⟨Mb, hbb⟩⟩ := reduced_svHypotheses hΛ hω i lam
  have hcoef : BddCoef (reducedCoefficient ω) (forcedDrift (reducedCoefficient ω) i lam)
      (max Ma Mb) := ⟨fun k j => (hA.matrix_elem k j).measurable,
        fun k => (measurable_pi_apply k).comp hb,
        fun y k j => (hAb y k j).trans (le_max_left _ _),
        fun y k => (hbb y k).trans (le_max_right _ _)⟩
  have hg : Measurable (L f) := hcoef.measurable_gen f
  obtain ⟨C, hC⟩ := bounded_svGenerator _ _ hAb hbb (contDiff_two_of_top hf) hc
  have heval : Measurable (fun p : ℝ × Path d => p.2 p.1.toNNReal) :=
    (continuous_snd.eval (continuous_real_toNNReal.comp continuous_fst)).measurable
  have hGm : Measurable (fun p : ℝ × Path d => L f (p.2 p.1.toNNReal)) := hg.comp heval
  have hGa (r : ℝ) : StronglyMeasurable[pathFiltration d r.toNNReal]
      (fun γ : Path d => L f (γ r.toNNReal)) := by
    exact hg.stronglyMeasurable.comp_measurable
      (Filtration.stronglyAdapted_natural
        (fun v => (measurable_pathPosition (d := d) v).stronglyMeasurable) r.toNNReal).measurable
  have hInt (γ : Path d) (a b : ℝ) :
      IntervalIntegrable (fun r : ℝ => L f (γ r.toNNReal)) volume a b :=
    u3_intervalIntegrable_bounded_slice hGm (fun r _ γ => hC (γ r.toNNReal)) γ
  have hObs : StronglyMeasurable[pathFiltration d t]
      (fun γ : Path d => ∫ r in (s : ℝ)..t, L f (γ r.toNNReal)) := by
    have ht := stronglyMeasurable_pathIntegral_of_measurable (L f) hg t
    have hs := stronglyMeasurable_pathIntegral_of_measurable (L f) hg s
    rw [← pathFiltration_eq_canonical] at ht hs
    have hh := ht.sub (hs.mono ((pathFiltration d).mono hst))
    convert hh using 1
    funext γ
    have heq := intervalIntegral.integral_add_adjacent_intervals (hInt γ 0 s) (hInt γ s t)
    simp only [Pi.sub_apply]
    linarith
  rw [u3_reduced_force_terminal_tilt_setIntegral_eq_density hd hΛ hω i hP lam t T htT E
    ((pathFiltration d).mono hst E hE) _ hObs]
  exact u3_reduced_force_density_mul_adapted_integral_on_event hd hΛ hω i hP lam
    hGm hGa hst hE (fun r _ γ => hC (γ r.toNNReal))



/-- The terminally tilted law satisfies the signed Dynkin identity on every past event. -/
theorem u3_reduced_force_tilt_dynkin_on_past_event {d : ℕ} (hd : 1 ≤ d)
    {Λ₀ : ℝ} (hΛ : 0 < Λ₀) {ω : FieldPair d} (hω : IsRegular Λ₀ ω)
    (i : Fin d) {x : Vec d} {P : Measure (Path d)}
    (hP : SolvesMartingaleProblem (External.Draft.svGenerator
      (reducedCoefficient ω) (forcedDrift (reducedCoefficient ω) i 0)) x P)
    (lam : ℝ) (f : Vec d → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hc : HasCompactSupport f) (s t T : ℝ≥0) (hst : s ≤ t) (htT : t ≤ T)
    (E : Set (Path d)) (hE : MeasurableSet[pathFiltration d s] E) :
    let L := External.Draft.svGenerator (reducedCoefficient ω)
      (forcedDrift (reducedCoefficient ω) i lam)
    let Z : ℝ≥0 → Path d → ℝ := fun v γ => Real.exp
      (lam * ((γ v) i - x i) - ∫ u in Set.Ioc (0 : ℝ) (v : ℝ),
        (lam * forcedDrift (reducedCoefficient ω) i 0 (γ u.toNNReal) i +
          (lam ^ 2 / 2) * reducedCoefficient ω (γ u.toNNReal) i i))
    let Q := P.withDensity (fun γ => ENNReal.ofReal (Z T γ))
    (∫ γ in E, f (γ t) ∂Q) - (∫ γ in E, f (γ s) ∂Q) =
      ∫ γ in E, (∫ r in (s : ℝ)..t, L f (γ r.toNNReal)) ∂Q := by
  intro L Z Q
  have had (v : ℝ≥0) : StronglyMeasurable[pathFiltration d v]
      (fun γ : Path d => f (γ v)) := hf.continuous.comp_stronglyMeasurable
    (Filtration.stronglyAdapted_natural
      (fun r => (measurable_pathPosition (d := d) r).stronglyMeasurable) v)
  rw [u3_reduced_force_terminal_tilt_setIntegral_eq_density hd hΛ hω i hP lam t T htT E
      ((pathFiltration d).mono hst E hE) _ (had t),
    u3_reduced_force_terminal_tilt_setIntegral_eq_density hd hΛ hω i hP lam s T
      (hst.trans htT) E hE _ (had s),
    u3_reduced_force_tilt_generator_integral_on_event hd hΛ hω i hP lam f hf hc
      s t T hst htT E hE]
  exact u3_reduced_force_density_dynkin_on_past_event hΛ hω i lam hP f hf hc s t hst E hE


/-- Under the signed terminal tilt, each compact test martingale is stopped at the horizon. -/
theorem u3_reduced_force_tilted_compensated_martingale {d : ℕ} (hd : 1 ≤ d)
    {Λ₀ : ℝ} (hΛ : 0 < Λ₀) {ω : FieldPair d} (hω : IsRegular Λ₀ ω)
    (i : Fin d) {x : Vec d} {P : Measure (Path d)}
    (hP : SolvesMartingaleProblem (External.Draft.svGenerator
      (reducedCoefficient ω) (forcedDrift (reducedCoefficient ω) i 0)) x P)
    (lam : ℝ) (T : ℝ≥0) (f : Vec d → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hc : HasCompactSupport f) :
    let L := External.Draft.svGenerator (reducedCoefficient ω)
      (forcedDrift (reducedCoefficient ω) i lam)
    let Z : Path d → ℝ := fun γ => Real.exp
      (lam * ((γ T) i - x i) - ∫ u in Set.Ioc (0 : ℝ) (T : ℝ),
        (lam * forcedDrift (reducedCoefficient ω) i 0 (γ u.toNNReal) i +
          (lam ^ 2 / 2) * reducedCoefficient ω (γ u.toNNReal) i i))
    Martingale (fun t : ℝ≥0 => compensatedTest L f (min t T))
      (pathFiltration d) (P.withDensity (fun γ => ENNReal.ofReal (Z γ))) := by
  intro L Z
  let Q := P.withDensity (fun γ => ENNReal.ofReal (Z γ))
  letI : IsProbabilityMeasure Q := u3_reduced_force_tilt_probability hd hΛ hω i hP lam T
  obtain ⟨had, hint⟩ := u3_forced_compensated_stopped_integrable hΛ hω i lam T f hf hc Q
  obtain ⟨hA, _, ⟨Ma, hAb⟩, _, hb, ⟨Mb, hbb⟩⟩ := reduced_svHypotheses hΛ hω i lam
  have hcoef : BddCoef (reducedCoefficient ω) (forcedDrift (reducedCoefficient ω) i lam)
      (max Ma Mb) := ⟨fun k j => (hA.matrix_elem k j).measurable,
        fun k => (measurable_pi_apply k).comp hb,
        fun y k j => (hAb y k j).trans (le_max_left _ _),
        fun y k => (hbb y k).trans (le_max_right _ _)⟩
  have hg : Measurable (L f) := hcoef.measurable_gen f
  obtain ⟨C, hC⟩ := bounded_svGenerator _ _ hAb hbb (contDiff_two_of_top hf) hc
  have heval : Measurable (fun p : ℝ × Path d => p.2 p.1.toNNReal) :=
    (continuous_snd.eval (continuous_real_toNNReal.comp continuous_fst)).measurable
  have hGm : Measurable (fun p : ℝ × Path d => L f (p.2 p.1.toNNReal)) := hg.comp heval
  have hInt (γ : Path d) (a b : ℝ) :
      IntervalIntegrable (fun r : ℝ => L f (γ r.toNNReal)) volume a b :=
    u3_intervalIntegrable_bounded_slice hGm (fun r _ γ => hC (γ r.toNNReal)) γ
  have hevent (s t : ℝ≥0) (hst : s ≤ t) (htT : t ≤ T)
      (E : Set (Path d)) (hE : MeasurableSet[pathFiltration d s] E) :
      (∫ γ in E, compensatedTest L f s γ ∂Q) =
        ∫ γ in E, compensatedTest L f t γ ∂Q := by
    have hsT := hst.trans htT
    have hs : Integrable (compensatedTest L f s) Q := by simpa [min_eq_left hsT] using hint s
    have ht : Integrable (compensatedTest L f t) Q := by simpa [min_eq_left htT] using hint t
    have hdiff := integral_sub (ht.integrableOn (s := E)) (hs.integrableOn (s := E))
    have hinc : (∫ γ in E, compensatedTest L f t γ - compensatedTest L f s γ ∂Q) =
        ∫ γ in E, (f (γ t) - f (γ s) - ∫ r in (s : ℝ)..t, L f (γ r.toNNReal)) ∂Q := by
      apply integral_congr_ae
      exact ae_of_all _ fun γ => u3_compensatedTest_interval L f s t γ (hInt γ 0 s) (hInt γ s t)
    have hdyn := u3_reduced_force_tilt_dynkin_on_past_event hd hΛ hω i hP lam f hf hc
      s t T hst htT E hE
    have hfBound := hf.continuous.bounded_above_of_compact_support hc
    obtain ⟨B, hB⟩ := hfBound
    have hfi (v : ℝ≥0) : Integrable (fun γ : Path d => f (γ v)) Q := by
      apply Integrable.of_bound ((hf.continuous.comp_stronglyMeasurable (measurable_pathPosition v).stronglyMeasurable).aestronglyMeasurable) B
      exact ae_of_all _ fun γ => hB (γ v)
    have hgi : Integrable (fun γ : Path d => ∫ r in (s : ℝ)..t, L f (γ r.toNNReal)) Q :=
      u3_integrable_bounded_interval (by exact_mod_cast hst) hGm (fun r _ γ => hC (γ r.toNNReal))
    have houter := integral_sub (((hfi t).sub (hfi s)).integrableOn (s := E))
      (hgi.integrableOn (s := E))
    have hinner := integral_sub ((hfi t).integrableOn (s := E)) ((hfi s).integrableOn (s := E))
    simp only [Pi.sub_apply] at houter hinner hdiff
    rw [houter, hinner] at hinc
    dsimp only at hdyn
    linarith
  refine ⟨had, fun s t hst => ?_⟩
  by_cases hs : s ≤ T
  · have hst' : s ≤ min t T := le_min hst hs
    have heq : ∀ E, MeasurableSet[pathFiltration d s] E →
        (∫ γ in E, compensatedTest L f s γ ∂Q) =
          ∫ γ in E, compensatedTest L f (min t T) γ ∂Q :=
      fun E hE => hevent s (min t T) hst' (min_le_right _ _) E hE
    symm
    apply ae_eq_condExp_of_forall_setIntegral_eq ((pathFiltration d).le s) (hint t)
      (fun _ _ _ => (hint s).integrableOn) ?_ (had s).aestronglyMeasurable
    intro E hE _
    simpa only [min_eq_left hs] using heq E hE
  · have hTs : T ≤ s := le_of_not_ge hs
    have hTt : T ≤ t := hTs.trans hst
    simp only [min_eq_right hTs, min_eq_right hTt]
    exact (condExp_of_stronglyMeasurable ((pathFiltration d).le s)
      (by simpa [min_eq_right hTs] using had s)
      (by simpa [min_eq_right hTs] using hint s)).eventuallyEq

end EinsteinFull





