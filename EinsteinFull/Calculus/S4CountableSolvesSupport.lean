import EinsteinFull.Calculus.S4CountableMartingaleSupport

/-!
# Countable conditions imply the martingale problem

The converse of `countableCond_of_solves`: for bounded measurable coefficients, the countable
conditions `CountableCond` imply `SolvesMartingaleProblem (svGenerator A b) x P`.
-/

open MeasureTheory Topology Filter
open scoped NNReal

namespace EinsteinFull
open EinsteinRelation

/-- The canonical filtration of the continuous coordinate process. -/
noncomputable abbrev canonF (d : ℕ) :=
  MarkovProcess.ContinuousPath.canonicalFiltration (alpha := Vec d)

theorem solves_of_countableCond {d : ℕ} {A : Vec d → Mat d} {b : Vec d → Vec d} {M : ℝ}
    (h : BddCoef A b M) {x : Vec d} {P : Measure (Path d)}
    (hC : CountableCond (External.Draft.svGenerator A b) x P) :
    SolvesMartingaleProblem (External.Draft.svGenerator A b) x P := by
  obtain ⟨hprob, hstart, hcond⟩ := hC
  haveI := hprob
  refine ⟨hprob, hstart, fun f hf hc => ?_⟩
  have hf2 := contDiff_two_of_top hf
  have hf0 : Continuous f := hf.continuous
  obtain ⟨Cf, hCf⟩ : ∃ Cf : ℝ, ∀ y, |f y| ≤ Cf := by
    obtain ⟨C, hC⟩ := hf0.bounded_above_of_compact_support hc
    exact ⟨C, fun y => by
      have := hC y
      rwa [Real.norm_eq_abs] at this⟩
  obtain ⟨CL, hCL⟩ := bounded_svGenerator A b h.Ab h.bb hf2 hc
  have hLm := h.measurable_gen f
  have hadapt := stronglyAdapted_compensatedTest_of_measurable (External.Draft.svGenerator A b)
    f hf0 hLm
  have hmeas : ∀ t, StronglyMeasurable
      (compensatedTest (External.Draft.svGenerator A b) f t) := fun t =>
    (hadapt t).mono ((pathFiltration d).le t)
  have hbd := norm_compensatedTest_le (External.Draft.svGenerator A b) f hCf hCL
  have hint : ∀ t : ℝ≥0, Integrable (compensatedTest (External.Draft.svGenerator A b) f t) P :=
    fun t => Integrable.of_bound (hmeas t).aestronglyMeasurable (2 * Cf + CL * t)
      (Filter.Eventually.of_forall fun γ => hbd t γ)
  refine ⟨fun t => Filter.Eventually.of_forall fun γ =>
    intervalIntegrable_path_of_bounded hLm hCL γ 0 t, hint, ?_⟩
  rw [pathFiltration_eq_canonical] at hadapt ⊢
  obtain ⟨m, u, hu𝔉, huH, hu0, hu1, hu2⟩ := tfam_dense d f hf hc
  -- rational times
  have hrat : ∀ S T : MarkovProcess.DenseTime, S ≤ T → ∀ B, MeasurableSet[canonF d
      (MarkovProcess.DenseTime.castOrderEmbedding S)] B →
      ∫ γ in B, (compensatedTest (External.Draft.svGenerator A b) f
        (MarkovProcess.DenseTime.castOrderEmbedding T) γ -
        compensatedTest (External.Draft.svGenerator A b) f
          (MarkovProcess.DenseTime.castOrderEmbedding S) γ) ∂P = 0 := by
    intro S T hST B hB
    refine setIntegral_eq_zero_of_piSystem ((canonF d).le _) (cylSys_gen d S).symm
      (cylSys_piSystem d S) (cylSys_univ d S) ((hint _).sub (hint _)) ?_ B hB
    intro B' hB'
    have hlim := tendsto_setIntegral_compensated h huH hu0 hu1 hu2 P (B := B')
      (MarkovProcess.DenseTime.castOrderEmbedding S)
      (MarkovProcess.DenseTime.castOrderEmbedding T)
    have hz : (fun k => ∫ γ in B', (compensatedTest (External.Draft.svGenerator A b) (u k)
        (MarkovProcess.DenseTime.castOrderEmbedding T) γ -
        compensatedTest (External.Draft.svGenerator A b) (u k)
          (MarkovProcess.DenseTime.castOrderEmbedding S) γ) ∂P) = fun _ => 0 :=
      funext fun k => hcond (u k) (hu𝔉 k) S T hST B' hB'
    rw [hz] at hlim
    exact tendsto_nhds_unique hlim tendsto_const_nhds
  -- real times
  have hCL0 : 0 ≤ CL := (abs_nonneg _).trans (hCL 0)
  have hcont : ∀ γ : Path d, Continuous fun τ : ℝ≥0 =>
      compensatedTest (External.Draft.svGenerator A b) f τ γ := fun γ =>
    continuous_compensatedTest_time_of_bounded _ f hf0 hLm hCL γ
  have hreal : ∀ s t : ℝ≥0, s ≤ t → ∀ B, MeasurableSet[canonF d s] B →
      ∫ γ in B, compensatedTest (External.Draft.svGenerator A b) f t γ ∂P =
        ∫ γ in B, compensatedTest (External.Draft.svGenerator A b) f s γ ∂P := by
    intro s t hst B hB
    let δ : ℕ → ℝ≥0 := fun n => Real.toNNReal (1 / ((n : ℝ) + 1))
    have hδpos : ∀ n, 0 < δ n := fun n => Real.toNNReal_pos.2 (by positivity)
    have hδ0 : Tendsto δ atTop (𝓝 0) := by
      have h0 : Tendsto δ atTop (𝓝 (Real.toNNReal 0)) :=
        (continuous_real_toNNReal.tendsto 0).comp tendsto_one_div_add_atTop_nhds_zero_nat
      rwa [Real.toNNReal_zero] at h0
    have hδ1 : ∀ n, δ n ≤ 1 := fun n => by
      have h1 : (1 / ((n : ℝ) + 1)) ≤ 1 := by
        rw [div_le_one (by positivity)]
        linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
      exact (Real.toNNReal_le_toNNReal h1).trans_eq Real.toNNReal_one
    have hSex : ∀ n, ∃ q : MarkovProcess.DenseTime,
        s < MarkovProcess.DenseTime.castOrderEmbedding q ∧
          MarkovProcess.DenseTime.castOrderEmbedding q < s + δ n := fun n =>
      MarkovProcess.DenseTime.exists_cast_btwn (lt_add_of_pos_right s (hδpos n))
    have hTex : ∀ n, ∃ q : MarkovProcess.DenseTime,
        t < MarkovProcess.DenseTime.castOrderEmbedding q ∧
          MarkovProcess.DenseTime.castOrderEmbedding q < t + δ n := fun n =>
      MarkovProcess.DenseTime.exists_cast_btwn (lt_add_of_pos_right t (hδpos n))
    choose Sq hSq using hSex
    choose Tq hTq using hTex
    have hcastmax : ∀ n, MarkovProcess.DenseTime.castOrderEmbedding (max (Sq n) (Tq n)) =
        max (MarkovProcess.DenseTime.castOrderEmbedding (Sq n))
          (MarkovProcess.DenseTime.castOrderEmbedding (Tq n)) := fun n =>
      (MarkovProcess.DenseTime.castOrderEmbedding.monotone).map_max
    have hTlow : ∀ n, t ≤ MarkovProcess.DenseTime.castOrderEmbedding (max (Sq n) (Tq n)) :=
      fun n => by
        rw [hcastmax]
        exact (hTq n).1.le.trans (le_max_right _ _)
    have hTup : ∀ n, MarkovProcess.DenseTime.castOrderEmbedding (max (Sq n) (Tq n)) ≤
        t + δ n := fun n => by
      rw [hcastmax]
      exact max_le (((hSq n).2.le).trans (add_le_add_left hst _)) (hTq n).2.le
    have hsδ : Tendsto (fun n => s + δ n) atTop (𝓝 s) := by
      have h0 : Tendsto (fun n => s + δ n) atTop (𝓝 (s + 0)) := tendsto_const_nhds.add hδ0
      rwa [add_zero] at h0
    have htδ : Tendsto (fun n => t + δ n) atTop (𝓝 t) := by
      have h0 : Tendsto (fun n => t + δ n) atTop (𝓝 (t + 0)) := tendsto_const_nhds.add hδ0
      rwa [add_zero] at h0
    have hSlim : Tendsto (fun n => MarkovProcess.DenseTime.castOrderEmbedding (Sq n)) atTop
        (𝓝 s) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsδ
        (fun n => (hSq n).1.le) (fun n => (hSq n).2.le)
    have hTlim : Tendsto (fun n => MarkovProcess.DenseTime.castOrderEmbedding
        (max (Sq n) (Tq n))) atTop (𝓝 t) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds htδ hTlow hTup
    have hBm : MeasurableSet B := (canonF d).le s B hB
    have hzero : ∀ n, ∫ γ in B, (compensatedTest (External.Draft.svGenerator A b) f
        (MarkovProcess.DenseTime.castOrderEmbedding (max (Sq n) (Tq n))) γ -
        compensatedTest (External.Draft.svGenerator A b) f
          (MarkovProcess.DenseTime.castOrderEmbedding (Sq n)) γ) ∂P = 0 := fun n =>
      hrat (Sq n) (max (Sq n) (Tq n)) (le_max_left _ _) B
        ((canonF d).mono (hSq n).1.le B hB)
    have hlim : Tendsto (fun n => ∫ γ in B, (compensatedTest (External.Draft.svGenerator A b) f
        (MarkovProcess.DenseTime.castOrderEmbedding (max (Sq n) (Tq n))) γ -
        compensatedTest (External.Draft.svGenerator A b) f
          (MarkovProcess.DenseTime.castOrderEmbedding (Sq n)) γ) ∂P) atTop
        (𝓝 (∫ γ in B, (compensatedTest (External.Draft.svGenerator A b) f t γ -
          compensatedTest (External.Draft.svGenerator A b) f s γ) ∂P)) := by
      refine tendsto_integral_of_dominated_convergence
        (fun _ => 4 * Cf + 2 * CL * ((t : ℝ) + 1)) ?_ (integrable_const _) ?_ ?_
      · exact fun n => ((hmeas _).sub (hmeas _)).aestronglyMeasurable
      · intro n
        refine Filter.Eventually.of_forall fun γ => ?_
        have hT1 := hbd (MarkovProcess.DenseTime.castOrderEmbedding (max (Sq n) (Tq n))) γ
        have hS1 := hbd (MarkovProcess.DenseTime.castOrderEmbedding (Sq n)) γ
        have h3 := norm_sub_le
          (compensatedTest (External.Draft.svGenerator A b) f
            (MarkovProcess.DenseTime.castOrderEmbedding (max (Sq n) (Tq n))) γ)
          (compensatedTest (External.Draft.svGenerator A b) f
            (MarkovProcess.DenseTime.castOrderEmbedding (Sq n)) γ)
        have hTle : ((MarkovProcess.DenseTime.castOrderEmbedding (max (Sq n) (Tq n)) : ℝ≥0) :
            ℝ) ≤ (t : ℝ) + 1 := by
          have : MarkovProcess.DenseTime.castOrderEmbedding (max (Sq n) (Tq n)) ≤ t + 1 :=
            (hTup n).trans (add_le_add le_rfl (hδ1 n))
          exact_mod_cast this
        have hSle : ((MarkovProcess.DenseTime.castOrderEmbedding (Sq n) : ℝ≥0) : ℝ) ≤
            (t : ℝ) + 1 := by
          have : MarkovProcess.DenseTime.castOrderEmbedding (Sq n) ≤ t + 1 :=
            ((hSq n).2.le.trans (add_le_add_left hst _)).trans
              (add_le_add le_rfl (hδ1 n))
          exact_mod_cast this
        have e1 := mul_le_mul_of_nonneg_left hTle hCL0
        have e2 := mul_le_mul_of_nonneg_left hSle hCL0
        linarith
      · exact Filter.Eventually.of_forall fun γ =>
          (((hcont γ).tendsto t).comp hTlim).sub (((hcont γ).tendsto s).comp hSlim)
    have hz : (fun n => ∫ γ in B, (compensatedTest (External.Draft.svGenerator A b) f
        (MarkovProcess.DenseTime.castOrderEmbedding (max (Sq n) (Tq n))) γ -
        compensatedTest (External.Draft.svGenerator A b) f
          (MarkovProcess.DenseTime.castOrderEmbedding (Sq n)) γ) ∂P) = fun _ => 0 :=
      funext hzero
    rw [hz] at hlim
    have hI0 := tendsto_nhds_unique hlim tendsto_const_nhds
    have hsub := integral_sub (hint t).integrableOn (hint s).integrableOn (μ := P.restrict B)
    linarith
  refine ⟨hadapt, fun r s hrs => ?_⟩
  exact (ae_eq_condExp_of_forall_setIntegral_eq ((canonF d).le r) (hint s)
    (fun B _ _ => (hint r).integrableOn) (fun B hB _ => (hreal r s hrs B hB).symm)
    (hadapt r).aestronglyMeasurable).symm

end EinsteinFull
