import EinsteinFull.Regeneration.WeightedStoppingRestart
import EinsteinFull.Regeneration.UniformFirstCandidate
import EinsteinFull.Regeneration.GMPDowncrossingSmallTilt
import EinsteinFull.Regeneration.DowncrossingExponentialMoment
import EinsteinRelation.Probability.HittingTimes

/-!
# The failure factor of a regeneration trial

A trial fails when the path falls `R` below its start. The running maximum at the
rounding of the failure time exceeds the maximum before the fall by at most one
window maximum, so the strong Markov property at the fall bounds the exponential
moment of the maximum at the failure by the moment of the maximum before the fall
times the window moment.
-/

open MeasureTheory ProbabilityTheory EinsteinRelation EinsteinRelation.Regeneration
open EinsteinRelation.External.GantertSection7Support
open scoped NNReal ENNReal

namespace EinsteinFull.Regeneration

/-- A first downward hitting time is at most `T` exactly when the fall occurs by `T`. -/
theorem firstHittingBelow_le_iff {d : ℕ} (γ : Path d) (i : Fin d) (a : ℝ) (T : ℝ≥0) :
    firstHittingBelow γ i a ≤ (T : ℝ≥0∞) ↔ ∃ t ∈ Set.Icc (0 : ℝ≥0) T, γ t i - γ 0 i ≤ a :=
  EinsteinRelation.Probability.downcrossing_inf_le_iff γ i a T

/-- Paths that agree up to `T` have the same downward hitting events by `T`. -/
theorem firstHittingBelow_le_iff_of_agree {d : ℕ} (γ γ' : Path d) (i : Fin d) (a : ℝ)
    (T : ℝ≥0) (hpre : ∀ t ≤ T, γ t = γ' t) :
    firstHittingBelow γ i a ≤ (T : ℝ≥0∞) ↔ firstHittingBelow γ' i a ≤ (T : ℝ≥0∞) := by
  rw [firstHittingBelow_le_iff, firstHittingBelow_le_iff]
  constructor
  · rintro ⟨t, ht, h⟩
    exact ⟨t, ht, by rw [← hpre t ht.2, ← hpre 0 zero_le]; exact h⟩
  · rintro ⟨t, ht, h⟩
    exact ⟨t, ht, by rw [hpre t ht.2, hpre 0 zero_le]; exact h⟩

/-- A downward hitting time before `T` is the same for paths agreeing up to `T`. -/
theorem firstHittingBelow_eq_of_agree {d : ℕ} (γ γ' : Path d) (i : Fin d) (a : ℝ)
    (T : ℝ≥0) (hpre : ∀ t ≤ T, γ t = γ' t) (hle : firstHittingBelow γ i a ≤ (T : ℝ≥0∞)) :
    firstHittingBelow γ' i a = firstHittingBelow γ i a := by
  have hfin : firstHittingBelow γ i a ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top hle
  set s := (firstHittingBelow γ i a).toNNReal with hs
  have hsT : s ≤ T := by
    apply ENNReal.coe_le_coe.mp
    rw [hs, ENNReal.coe_toNNReal hfin]
    exact hle
  have h1 : firstHittingBelow γ' i a ≤ (s : ℝ≥0∞) :=
    (firstHittingBelow_le_iff_of_agree γ γ' i a s (fun t ht => hpre t (ht.trans hsT))).mp
      (by rw [hs, ENNReal.coe_toNNReal hfin])
  apply le_antisymm (h1.trans (by rw [hs, ENNReal.coe_toNNReal hfin]))
  have hfin' : firstHittingBelow γ' i a ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top h1
  set s' := (firstHittingBelow γ' i a).toNNReal with hs'
  have hs'T : s' ≤ T := by
    have : (s' : ℝ≥0∞) ≤ s := by rw [hs', ENNReal.coe_toNNReal hfin']; exact h1
    exact (ENNReal.coe_le_coe.mp this).trans hsT
  have h2 : firstHittingBelow γ i a ≤ (s' : ℝ≥0∞) :=
    (firstHittingBelow_le_iff_of_agree γ γ' i a s' (fun t ht => hpre t (ht.trans hs'T))).mpr
      (by rw [hs', ENNReal.coe_toNNReal hfin'])
  exact h2.trans (by rw [hs', ENNReal.coe_toNNReal hfin'])

/-- A first downward hitting time is a stopping time of the canonical filtration. -/
theorem isStoppingTime_firstHittingBelow {d : ℕ} (i : Fin d) (a : ℝ) :
    IsStoppingTime (MarkovProcess.ContinuousPath.canonicalFiltration (alpha := Vec d))
      (fun γ : Path d => firstHittingBelow γ i a) := by
  intro T
  have heq : {γ : Path d | firstHittingBelow γ i a ≤ (T : ℝ≥0∞)} =
      (MarkovProcess.ContinuousPath.stoppedPath T) ⁻¹'
        {γ : Path d | firstHittingBelow γ i a ≤ (T : ℝ≥0∞)} := by
    ext γ
    exact firstHittingBelow_le_iff_of_agree γ (MarkovProcess.ContinuousPath.stoppedPath T γ) i a T
      (fun t ht => (MarkovProcess.ContinuousPath.stoppedPath_apply_of_le T γ t ht).symm)
  change @MeasurableSet (Path d)
    (MarkovProcess.ContinuousPath.canonicalFiltration (alpha := Vec d) T)
    {γ : Path d | firstHittingBelow γ i a ≤ (T : ℝ≥0∞)}
  rw [heq]
  exact measurable_stoppedPath_canonicalHistory T
    (((measurable_firstHittingBelow (d := d) i).comp (measurable_const.prodMk measurable_id))
      measurableSet_Iic)

/-- The failure weight of a trial: the exponential of the running maximum at the
rounded fall time, with the slack `12R` of a trial start, on the event of a fall. -/
noncomputable def trialFailureWeight {d : ℕ} (Δ : ℝ≥0) (lam R a : ℝ) (i : Fin d)
    (γ : Path d) : ℝ≥0∞ :=
  {γ : Path d | firstHittingBelow γ i (-R) ≠ ⊤}.indicator
    (fun γ => ENNReal.ofReal (Real.exp (a * lam * (max (12 * R)
      (coordinateMaximum γ i (roundUp Δ (firstHittingBelow γ i (-R))).toNNReal) + R)))) γ

/-- The fall weight: the exponential of the running maximum before the fall. -/
noncomputable def fallWeight {d : ℕ} (lam R a : ℝ) (i : Fin d) (γ : Path d) : ℝ≥0∞ :=
  {γ : Path d | firstHittingBelow γ i (-R) ≠ ⊤}.indicator
    (fun γ => ENNReal.ofReal (Real.exp (a * lam *
      coordinateMaximum γ i (firstHittingBelow γ i (-R)).toNNReal))) γ

/-- The window weight of a path. -/
noncomputable def windowWeight {d : ℕ} (Δ : ℝ≥0) (lam a : ℝ) (i : Fin d) (η : Path d) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (a * lam * coordinateMaximum η i Δ))

theorem measurable_fallWeight {d : ℕ} (lam R a : ℝ) (i : Fin d) :
    Measurable (fallWeight (d := d) lam R a i) :=
  (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_const.mul
    (measurable_maximum_at_downcrossing R i)))).indicator
    (measurableSet_eq_fun (measurable_first_downcrossing R i) measurable_const).compl

theorem measurable_windowWeight {d : ℕ} (Δ : ℝ≥0) (lam a : ℝ) (i : Fin d) :
    Measurable (windowWeight (d := d) Δ lam a i) :=
  ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_const.mul
    ((measurable_coordinateMaximum i).comp (measurable_const.prodMk measurable_id))))

/-- The failure weight is dominated by the fall weight times the window weight of the
path after the fall. -/
theorem trialFailureWeight_le {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ) (lam R a : ℝ) (hlam : 0 < lam)
    (hR : 0 < R) (ha : 0 ≤ a) (i : Fin d) (γ : Path d) :
    trialFailureWeight Δ lam R a i γ ≤ ENNReal.ofReal (Real.exp (a * lam * (13 * R))) *
      (fallWeight lam R a i γ * windowWeight Δ lam a i
        (pathTimeShift γ (firstHittingBelow γ i (-R)).toNNReal)) := by
  by_cases hH : firstHittingBelow γ i (-R) ≠ ⊤
  · simp only [trialFailureWeight, fallWeight, windowWeight]
    rw [Set.indicator_of_mem (show γ ∈ {γ : Path d | firstHittingBelow γ i (-R) ≠ ⊤} from hH),
      Set.indicator_of_mem (show γ ∈ {γ : Path d | firstHittingBelow γ i (-R) ≠ ⊤} from hH),
      ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
      ← Real.exp_add, ← Real.exp_add]
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    set H := (firstHittingBelow γ i (-R)).toNNReal with hHdef
    set U := (roundUp Δ (firstHittingBelow γ i (-R))).toNNReal with hUdef
    have hround : roundUp Δ (firstHittingBelow γ i (-R)) ≠ ⊤ := by
      rw [roundUp, ite_eq_right hH]
      exact ENNReal.coe_ne_top
    have hHU : H ≤ U := by
      apply ENNReal.coe_le_coe.mp
      rw [hHdef, hUdef, ENNReal.coe_toNNReal hH, ENNReal.coe_toNNReal hround]
      exact le_roundUp Δ hΔ _
    have hUH : U - H ≤ Δ := by
      apply tsub_le_iff_left.mpr
      exact roundUp_toNNReal_le_add_step Δ hΔ _ hH
    have hsplit : U = H + (U - H) := (add_tsub_cancel_of_le hHU).symm
    have hfall : γ H i - γ 0 i ≤ -R := by
      obtain ⟨t, ht, hcross⟩ := (firstHittingBelow_le_iff γ i (-R) H).mp
        (by rw [hHdef, ENNReal.coe_toNNReal hH])
      have htime := firstHittingBelow_le_of_crossing γ i (-R) t hcross
      rw [← ENNReal.coe_toNNReal hH, ← hHdef] at htime
      have htH : t = H := le_antisymm ht.2 (ENNReal.coe_le_coe.mp htime)
      rw [← htH]
      exact hcross
    have hM : coordinateMaximum γ i U ≤ coordinateMaximum γ i H +
        coordinateMaximum (pathTimeShift γ H) i Δ := by
      rw [hsplit, coordinateMaximum_add]
      apply max_le
      · exact le_add_of_nonneg_right (coordinateMaximum_nonneg _ i _)
      · have h1 := coordinateMaximum_mono (pathTimeShift γ H) i hUH
        have h2 := coordinateMaximum_nonneg γ i H
        linarith
    have hMH := coordinateMaximum_nonneg γ i H
    have hal : 0 ≤ a * lam := mul_nonneg ha hlam.le
    have hmax : max (12 * R) (coordinateMaximum γ i U) + R ≤
        13 * R + coordinateMaximum γ i H + coordinateMaximum (pathTimeShift γ H) i Δ := by
      have hW := coordinateMaximum_nonneg (pathTimeShift γ H) i Δ
      have h1 : max (12 * R) (coordinateMaximum γ i U) ≤
          12 * R + coordinateMaximum γ i H + coordinateMaximum (pathTimeShift γ H) i Δ :=
        max_le (by linarith) (by linarith)
      linarith
    nlinarith
  · simp only [trialFailureWeight]
    rw [Set.indicator_of_notMem (show γ ∉ {γ : Path d | firstHittingBelow γ i (-R) ≠ ⊤}
      from hH)]
    exact zero_le

end EinsteinFull.Regeneration
