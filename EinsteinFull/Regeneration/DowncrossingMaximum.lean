import EinsteinFull.Calculus.U1RegularKernelContinuity
import EinsteinFull.Blueprint.Foundation.Proofs.SbxS7ConditionalTrialExhaustion

/-!
# Maximum before a downcrossing

A path which rises before a downcrossing must subsequently make a larger
downcrossing from the first time it reaches that rise.
-/

open MeasureTheory ProbabilityTheory EinsteinRelation EinsteinRelation.Regeneration
open EinsteinFull.Blueprint
open scoped NNReal ENNReal

namespace EinsteinFull.Regeneration

/-- A finite downcrossing time witnesses an actual downcrossing. -/
theorem exists_crossing_of_firstHittingBelow_ne_top {d : ℕ} (γ : Path d)
    (i : Fin d) (a : ℝ) (hfin : firstHittingBelow γ i a ≠ ⊤) :
    ∃ t : ℝ≥0, γ t i - γ 0 i ≤ a := by
  by_contra h
  have hn : ∀ t : ℝ≥0, ¬ γ t i - γ 0 i ≤ a := by simpa only [not_exists] using h
  apply hfin
  unfold firstHittingBelow
  simp only [hn, iInf_of_empty, iInf_const]

/-- A maximum before a finite lower crossing forces a deeper crossing after the first rise. -/
theorem shifted_downcrossing_of_maximum {d : ℕ} (γ : Path d) (i : Fin d) (R b : ℝ)
    (hdown : firstHittingBelow γ i (-R) ≠ ⊤)
    (hmax : b < coordinateMaximum γ i (firstHittingBelow γ i (-R)).toNNReal) :
    firstHittingAbove γ i b ≠ ⊤ ∧
      firstHittingBelow (pathTimeShift γ (firstHittingAbove γ i b).toNNReal) i (-(R + b)) ≠ ⊤ := by
  have hex : ∃ s ∈ Set.Icc (0 : ℝ≥0) (firstHittingBelow γ i (-R)).toNNReal,
      b < γ s i - γ 0 i := by
    by_contra hn
    have hle : coordinateMaximum γ i (firstHittingBelow γ i (-R)).toNNReal ≤ b := by
      apply coordinateMaximum_le
      intro s hs
      exact le_of_not_gt (fun h => hn ⟨s, hs, h⟩)
    exact (not_le_of_gt hmax) hle
  obtain ⟨s, hs, hsheight⟩ := hex
  have hupper : firstHittingAbove γ i b ≤ firstHittingBelow γ i (-R) := by
    calc
      _ ≤ (s : ℝ≥0∞) := firstHittingAbove_le_of_crossing γ i b s hsheight.le
      _ ≤ _ := by
        rw [← ENNReal.coe_toNNReal hdown]
        exact_mod_cast hs.2
  have hupfin : firstHittingAbove γ i b ≠ ⊤ := ne_top_of_le_ne_top hdown hupper
  have hheight := ConditionalTrialExhaustion.crossing_at_firstHittingAbove_of_ne_top γ i b hupfin
  obtain ⟨t, ht⟩ := exists_crossing_of_firstHittingBelow_ne_top γ i (-R) hdown
  have htime : (firstHittingAbove γ i b).toNNReal ≤ t := by
    have hh := hupper.trans (firstHittingBelow_le_of_crossing γ i (-R) t ht)
    rw [← ENNReal.coe_toNNReal hupfin, ENNReal.coe_le_coe] at hh
    exact hh
  have hcross : (pathTimeShift γ (firstHittingAbove γ i b).toNNReal)
      (t - (firstHittingAbove γ i b).toNNReal) i -
      (pathTimeShift γ (firstHittingAbove γ i b).toNNReal) 0 i ≤ -(R + b) := by
    simp only [pathTimeShift, ContinuousMap.coe_mk, add_zero, add_tsub_cancel_of_le htime]
    linarith
  exact ⟨hupfin, ne_top_of_le_ne_top ENNReal.coe_ne_top
    (firstHittingBelow_le_of_crossing _ i _ _ hcross)⟩

/-- A uniform backward-crossing bound controls the maximum before the first crossing. -/
theorem maximum_before_downcrossing_le_of_uniform_crossing {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (G : EinsteinRelation.External.GantertSection7Support.GantertFixedEnvironmentRealization
      hd Λ hΛ ω hω lam h0 h1) (x : Vec d) (i : Fin d) (R b : ℝ) (c : ℝ≥0∞)
    (hbound : ∀ y, G.pathLaw y {γ | firstHittingBelow γ i (-(R + b)) ≠ ⊤} ≤ c) :
    G.pathLaw x {γ | firstHittingBelow γ i (-R) ≠ ⊤ ∧
      b < coordinateMaximum γ i (firstHittingBelow γ i (-R)).toNNReal} ≤ c := by
  let : IsMarkovKernel G.pathLaw := G.pathLaw_isMarkovKernel
  let T : Path d → ℝ≥0∞ := fun γ => firstHittingAbove γ i b
  have hT : IsStoppingTime (MarkovProcess.ContinuousPath.canonicalFiltration (alpha := Vec d)) T := by
    simpa only [T, passageSequence, div_one] using
      (coupling_scope_isStoppingTime_passageSequence 1 (by norm_num) 1 1 b (by norm_num) i 0)
  let A : Set (Path d) := {γ | T γ < ⊤}
  let D : Set (Path d) := {γ | firstHittingBelow γ i (-(R + b)) ≠ ⊤}
  have hD : MeasurableSet D := (measurableSet_singleton (⊤ : ℝ≥0∞)).preimage
    ((measurable_firstHittingBelow i).comp (measurable_const.prodMk measurable_id)) |>.compl
  have hS : Measurable (fun γ : Path d =>
      MarkovProcess.ContinuousPath.shift ((T γ).untopD 0) γ) :=
    MarkovProcess.ContinuousPath.continuous_shift.measurable.comp
      (((measurable_firstHittingAbove i).comp (measurable_const.prodMk measurable_id)).ennreal_toNNReal.prodMk
        measurable_id)
  have hr := EinsteinFull.u1_supplied_regular_extended_stopping_restart hd ω lam Λ hΛ hω h0 h1 G T hT x A
    (MarkovProcess.StoppingTime.measurableSet_stoppingTime_lt_top hT) (fun _ h => h)
  have hshift : ((G.pathLaw x).restrict A).map
      (fun γ => MarkovProcess.ContinuousPath.shift ((T γ).untopD 0) γ) D ≤ c := by
    rw [hr, Measure.bind_apply hD]
    · calc
        _ ≤ ∫⁻ _γ in A, c ∂G.pathLaw x := lintegral_mono (fun γ => hbound _)
        _ = c * G.pathLaw x A := by simp only [lintegral_const, Measure.restrict_apply_univ]
        _ ≤ c * 1 := mul_le_mul_right prob_le_one c
        _ = c := mul_one c
    · exact G.pathLaw.aemeasurable.comp_measurable ((continuous_eval.measurable).comp
        (measurable_id.prodMk ((measurable_firstHittingAbove i).comp
          (measurable_const.prodMk measurable_id)).ennreal_toNNReal))
  rw [Measure.map_apply hS hD, Measure.restrict_apply (hD.preimage hS)] at hshift
  calc
    _ ≤ G.pathLaw x (A ∩ (fun γ =>
        MarkovProcess.ContinuousPath.shift ((T γ).untopD 0) γ) ⁻¹' D) := by
      apply measure_mono
      intro γ hγ
      obtain ⟨hu, hd⟩ := shifted_downcrossing_of_maximum γ i R b hγ.1 hγ.2
      refine ⟨lt_top_iff_ne_top.mpr hu, ?_⟩
      change firstHittingBelow (MarkovProcess.ContinuousPath.shift ((T γ).untopD 0) γ)
        i (-(R + b)) ≠ ⊤
      exact hd
    _ = G.pathLaw x ((fun γ => MarkovProcess.ContinuousPath.shift ((T γ).untopD 0) γ) ⁻¹' D ∩ A) := by
      rw [Set.inter_comm]
    _ ≤ c := hshift

end EinsteinFull.Regeneration
