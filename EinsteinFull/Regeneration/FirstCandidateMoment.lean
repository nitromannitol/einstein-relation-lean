import EinsteinFull.Regeneration.PassageGeometry
import EinsteinFull.Regeneration.WeightedStoppingRestart
import EinsteinFull.Blueprint.Foundation.Proofs.SbxS7ConditionalTrialExhaustion

/-!
# Exponential moment of the first rounded candidate

The first rounded candidate of a candidate search is the rounding of the first
good passage. Each failed guard moves the path by more than `R / 2` within one
regeneration interval, and the next passage lies at most one window maximum plus
`R` higher. If the window functional of a failed guard has expectation at most
`ρ < 1` from every start, the strong Markov property at the passages bounds the
exponential moment of the height of the first rounded candidate above the search
level by a geometric series.
-/

open MeasureTheory ProbabilityTheory EinsteinRelation EinsteinRelation.Regeneration
open EinsteinRelation.External.GantertSection7Support
open scoped NNReal ENNReal

namespace EinsteinFull.Regeneration

/-- The event that a path moves by more than `R / 2` in coordinate `i` within time `Δ`. -/
def windowEscape {d : ℕ} (Δ : ℝ≥0) (R : ℝ) (i : Fin d) : Set (Path d) :=
  {η | ∃ s : ℝ≥0, s ≤ Δ ∧ R / 2 < |η s i - η 0 i|}

/-- The window escape event is open, hence measurable. -/
theorem measurableSet_windowEscape {d : ℕ} (Δ : ℝ≥0) (R : ℝ) (i : Fin d) :
    MeasurableSet (windowEscape (d := d) Δ R i) := by
  have hopen : IsOpen (windowEscape (d := d) Δ R i) := by
    have heq : windowEscape (d := d) Δ R i =
        ⋃ s : {s : ℝ≥0 // s ≤ Δ}, {η : Path d | R / 2 < |η s.1 i - η 0 i|} := by
      ext η
      simp only [windowEscape, Set.mem_ofPred_eq, Set.mem_iUnion, Subtype.exists, exists_prop]
    rw [heq]
    refine isOpen_iUnion fun s => isOpen_lt continuous_const ?_
    have hci : Continuous fun v : Vec d => v i := continuous_apply i
    have hs : Continuous fun η : Path d => η s.1 i := hci.comp (continuous_eval_const s.1)
    have h0 : Continuous fun η : Path d => η 0 i := hci.comp (continuous_eval_const 0)
    exact (hs.sub h0).abs
  exact hopen.measurableSet

/-- The weight of a failed guard: the exponential of the window maximum plus one
slab, on the window escape event. -/
noncomputable def failedWindowWeight {d : ℕ} (Δ : ℝ≥0) (lam R b : ℝ) (i : Fin d)
    (η : Path d) : ℝ≥0∞ :=
  (windowEscape Δ R i).indicator
    (fun η => ENNReal.ofReal (Real.exp (b * lam * (coordinateMaximum η i Δ + R)))) η

theorem measurable_failedWindowWeight {d : ℕ} (Δ : ℝ≥0) (lam R b : ℝ) (i : Fin d) :
    Measurable (failedWindowWeight (d := d) Δ lam R b i) := by
  apply Measurable.indicator _ (measurableSet_windowEscape Δ R i)
  apply ENNReal.measurable_ofReal.comp
  apply Real.measurable_exp.comp
  apply measurable_const.mul
  exact ((measurable_coordinateMaximum i).comp (measurable_const.prodMk measurable_id)).add
    measurable_const

/-- The weight after `n` failed guards: the exponential height of the `n`th passage
above the search level, on the event that the passage is finite and the earlier
guards failed. -/
noncomputable def failedPassageWeight {d : ℕ} (Δ : ℝ≥0) (lam R a b : ℝ) (i : Fin d)
    (n : ℕ) (γ : Path d) : ℝ≥0∞ :=
  {γ : Path d | passageSequence Δ lam R a γ i n ≠ ⊤ ∧
      ∀ j < n, ¬ IsGoodPassage Δ lam R a γ i j}.indicator
    (fun γ => ENNReal.ofReal (Real.exp (b * lam *
      (γ (passageSequence Δ lam R a γ i n).toNNReal i - γ 0 i - a / lam)))) γ

theorem measurable_passage {d : ℕ} (Δ : ℝ≥0) (lam R a : ℝ) (i : Fin d) (n : ℕ) :
    Measurable (fun γ : Path d => passageSequence Δ lam R a γ i n) :=
  (measurable_passageSequence_joint Δ lam R i n).comp (measurable_const.prodMk measurable_id)

theorem measurableSet_isGoodPassage {d : ℕ} (Δ : ℝ≥0) (lam R a : ℝ) (i : Fin d) (n : ℕ) :
    MeasurableSet {γ : Path d | IsGoodPassage Δ lam R a γ i n} :=
  (measurableSet_IsGoodPassage Δ lam R i n).preimage (measurable_const.prodMk measurable_id)

theorem measurable_failedPassageWeight {d : ℕ} (Δ : ℝ≥0) (lam R a b : ℝ) (i : Fin d)
    (n : ℕ) : Measurable (failedPassageWeight (d := d) Δ lam R a b i n) := by
  have hV := measurable_passage (d := d) Δ lam R a i n
  apply Measurable.indicator
  · apply ENNReal.measurable_ofReal.comp
    apply Real.measurable_exp.comp
    apply measurable_const.mul
    have hev : Measurable (fun γ : Path d => γ (passageSequence Δ lam R a γ i n).toNNReal) :=
      continuous_eval.measurable.comp (measurable_id.prodMk hV.ennreal_toNNReal)
    exact (((measurable_pi_apply i).comp hev).sub
      ((measurable_pi_apply i).comp ((continuous_eval_const 0).measurable))).sub
      measurable_const
  · have heq : {γ : Path d | ∀ j < n, ¬ IsGoodPassage Δ lam R a γ i j} =
        ⋂ j ∈ Finset.range n, {γ : Path d | IsGoodPassage Δ lam R a γ i j}ᶜ := by
      ext γ
      simp only [Set.mem_ofPred_eq, Set.mem_iInter, Finset.mem_range, Set.mem_compl_iff]
    have hgood : MeasurableSet {γ : Path d | ∀ j < n, ¬ IsGoodPassage Δ lam R a γ i j} := by
      rw [heq]
      exact Finset.measurableSet_biInter _ fun j _ =>
        (measurableSet_isGoodPassage Δ lam R a i j).compl
    exact (measurableSet_eq_fun hV measurable_const).compl.inter hgood

/-- One more failed guard multiplies the weight by at most the failed-window weight
of the path after the previous passage. -/
theorem failedPassageWeight_succ_le {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ) (lam R a b : ℝ)
    (hlam : 0 < lam) (hR : 0 < R) (hb : 0 ≤ b) (i : Fin d) (n : ℕ) (γ : Path d) :
    failedPassageWeight Δ lam R a b i (n + 1) γ ≤
      failedPassageWeight Δ lam R a b i n γ *
        failedWindowWeight Δ lam R b i
          (pathTimeShift γ (passageSequence Δ lam R a γ i n).toNNReal) := by
  by_cases hcond : passageSequence Δ lam R a γ i (n + 1) ≠ ⊤ ∧
      ∀ j < n + 1, ¬ IsGoodPassage Δ lam R a γ i j
  · obtain ⟨hfin, hbad⟩ := hcond
    have hnfin : passageSequence Δ lam R a γ i n ≠ ⊤ :=
      ne_top_of_le_ne_top hfin (monotone_passageSequence Δ hΔ lam R a hR γ i (Nat.le_succ n))
    have hprev : passageSequence Δ lam R a γ i n ≠ ⊤ ∧
        ∀ j < n, ¬ IsGoodPassage Δ lam R a γ i j :=
      ⟨hnfin, fun j hj => hbad j (Nat.lt_succ_of_lt hj)⟩
    have hesc := window_escape_of_not_good Δ hΔ lam R a γ i n hnfin (hbad n (Nat.lt_succ_self n))
    have hinc := passage_increment_le Δ hΔ lam R a hR γ i n hfin
    simp only [failedPassageWeight, failedWindowWeight]
    rw [Set.indicator_of_mem (show γ ∈ {γ : Path d | passageSequence Δ lam R a γ i (n + 1) ≠ ⊤ ∧
        ∀ j < n + 1, ¬ IsGoodPassage Δ lam R a γ i j} from ⟨hfin, hbad⟩),
      Set.indicator_of_mem (show γ ∈ {γ : Path d | passageSequence Δ lam R a γ i n ≠ ⊤ ∧
        ∀ j < n, ¬ IsGoodPassage Δ lam R a γ i j} from hprev),
      Set.indicator_of_mem (show pathTimeShift γ (passageSequence Δ lam R a γ i n).toNNReal ∈
        windowEscape Δ R i from hesc)]
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    have hbl : 0 ≤ b * lam := mul_nonneg hb hlam.le
    nlinarith
  · simp only [failedPassageWeight]
    rw [Set.indicator_of_notMem (show γ ∉ {γ : Path d | passageSequence Δ lam R a γ i (n + 1) ≠ ⊤ ∧
        ∀ j < n + 1, ¬ IsGoodPassage Δ lam R a γ i j} from hcond)]
    exact zero_le


/-- Stopping a path after its `n`th passage does not change the failed-passage
weight. -/
theorem failedPassageWeight_stoppedPath {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ) (lam R a b : ℝ)
    (hR : 0 < R) (i : Fin d) (n : ℕ) (γ : Path d) (t : ℝ≥0)
    (ht : passageSequence Δ lam R a γ i n ≤ t) :
    failedPassageWeight Δ lam R a b i n (MarkovProcess.ContinuousPath.stoppedPath t γ) =
      failedPassageWeight Δ lam R a b i n γ := by
  set γ' := MarkovProcess.ContinuousPath.stoppedPath t γ with hγ'
  have hpre : ∀ s ∈ Set.Icc (0 : ℝ≥0) t, γ s = γ' s := fun s hs =>
    (MarkovProcess.ContinuousPath.stoppedPath_apply_of_le t γ s hs.2).symm
  have hVj : ∀ j ≤ n, passageSequence Δ lam R a γ i j = passageSequence Δ lam R a γ' i j := by
    intro j hj
    exact (passageSequence_prefix_determined Δ hΔ lam R a hR γ γ' i j t hpre).2
      ((monotone_passageSequence Δ hΔ lam R a hR γ i hj).trans ht)
  have hnfin : passageSequence Δ lam R a γ i n ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top ht
  have hgood : ∀ j < n, (IsGoodPassage Δ lam R a γ i j ↔ IsGoodPassage Δ lam R a γ' i j) := by
    intro j hj
    have hVeq := hVj j hj.le
    have hj1fin : passageSequence Δ lam R a γ i (j + 1) ≠ ⊤ :=
      ne_top_of_le_ne_top hnfin (monotone_passageSequence Δ hΔ lam R a hR γ i hj)
    obtain ⟨hround, _⟩ := passage_displacement_succ Δ lam R a hR γ i j hj1fin
    have hUle : roundUp Δ (passageSequence Δ lam R a γ i j) ≤ t :=
      ((rounded_passage_lt_next Δ lam R a hR γ i j hround).le.trans
        (monotone_passageSequence Δ hΔ lam R a hR γ i hj)).trans ht
    have hUle' : (roundUp Δ (passageSequence Δ lam R a γ i j)).toNNReal ≤ t := by
      apply ENNReal.coe_le_coe.mp
      rw [ENNReal.coe_toNNReal hround]
      exact hUle
    simp only [IsGoodPassage]
    rw [← hVeq]
    constructor
    · rintro ⟨h1, h2, h3⟩
      refine ⟨h1, h2, fun s hs => ?_⟩
      have hs' : s ≤ t := hs.2.trans hUle'
      have hV' : (passageSequence Δ lam R a γ i j).toNNReal ≤ t := hs.1.trans hs'
      rw [← hpre s ⟨zero_le, hs'⟩, ← hpre _ ⟨zero_le, hV'⟩]
      exact h3 s hs
    · rintro ⟨h1, h2, h3⟩
      refine ⟨h1, h2, fun s hs => ?_⟩
      have hs' : s ≤ t := hs.2.trans hUle'
      have hV' : (passageSequence Δ lam R a γ i j).toNNReal ≤ t := hs.1.trans hs'
      rw [hpre s ⟨zero_le, hs'⟩, hpre _ ⟨zero_le, hV'⟩]
      exact h3 s hs
  have hVn := hVj n le_rfl
  have hVt : (passageSequence Δ lam R a γ i n).toNNReal ≤ t := by
    apply ENNReal.coe_le_coe.mp
    rw [ENNReal.coe_toNNReal hnfin]
    exact ht
  have hmem : (γ' ∈ {γ : Path d | passageSequence Δ lam R a γ i n ≠ ⊤ ∧
      ∀ j < n, ¬ IsGoodPassage Δ lam R a γ i j}) ↔
      (γ ∈ {γ : Path d | passageSequence Δ lam R a γ i n ≠ ⊤ ∧
      ∀ j < n, ¬ IsGoodPassage Δ lam R a γ i j}) := by
    simp only [Set.mem_ofPred_eq, ← hVn]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun j hj hg => h2 j hj ((hgood j hj).mp hg)⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun j hj hg => h2 j hj ((hgood j hj).mpr hg)⟩
  simp only [failedPassageWeight]
  by_cases hγ : γ ∈ {γ : Path d | passageSequence Δ lam R a γ i n ≠ ⊤ ∧
      ∀ j < n, ¬ IsGoodPassage Δ lam R a γ i j}
  · rw [Set.indicator_of_mem hγ, Set.indicator_of_mem (hmem.mpr hγ), ← hVn,
      ← hpre _ ⟨zero_le, hVt⟩, ← hpre 0 ⟨le_rfl, zero_le⟩]
  · rw [Set.indicator_of_notMem hγ, Set.indicator_of_notMem (fun h => hγ (hmem.mp h))]

/-- The failed-passage weight is decided by the stopped history at the passage. -/
theorem measurable_failedPassageWeight_stopping {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ)
    (lam R a b : ℝ) (hR : 0 < R) (i : Fin d) (n : ℕ) :
    Measurable[(EinsteinFull.Blueprint.coupling_scope_isStoppingTime_passageSequence
      Δ hΔ lam R a hR i n).measurableSpace]
      (failedPassageWeight (d := d) Δ lam R a b i n) := by
  apply measurable_stopping_of_prefix _ (measurable_passage Δ lam R a i n)
  · intro γ t
    exact ((passageSequence_prefix_determined Δ hΔ lam R a hR γ
      (MarkovProcess.ContinuousPath.stoppedPath t γ) i n t
      (fun s hs => (MarkovProcess.ContinuousPath.stoppedPath_apply_of_le t γ s hs.2).symm)).1).symm
  · exact measurable_failedPassageWeight Δ lam R a b i n
  · intro γ htop
    simp only [failedPassageWeight]
    apply Set.indicator_of_notMem
    rintro ⟨h, _⟩
    exact h htop
  · intro γ t ht
    exact failedPassageWeight_stoppedPath Δ hΔ lam R a b hR i n γ t ht

theorem toNNReal_eq_untopD (t : ℝ≥0∞) : t.toNNReal = WithTop.untopD 0 t := rfl

/-- The failed-passage weights decay geometrically when the failed-window weight has
expectation at most `ρ` from every start. -/
theorem lintegral_failedPassageWeight_le {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (f Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (h0 : 0 ≤ f) (h1 : f ≤ 1)
    (G : GantertFixedEnvironmentRealization hd Λ hΛ ω hω f h0 h1)
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (lam R a b : ℝ) (hlam : 0 < lam) (hR : 0 < R)
    (ha : 0 ≤ a / lam) (hb : 0 ≤ b) (i : Fin d) (ρ : ℝ)
    (hwin : ∀ y, ∫⁻ η, failedWindowWeight Δ lam R b i η ∂G.pathLaw y ≤ ENNReal.ofReal ρ)
    (x : Vec d) (n : ℕ) :
    ∫⁻ γ, failedPassageWeight Δ lam R a b i n γ ∂G.pathLaw x ≤ ENNReal.ofReal ρ ^ n := by
  have : IsMarkovKernel G.pathLaw := G.pathLaw_isMarkovKernel
  induction n with
  | zero =>
    calc ∫⁻ γ, failedPassageWeight Δ lam R a b i 0 γ ∂G.pathLaw x
        ≤ ∫⁻ _γ, 1 ∂G.pathLaw x := by
          apply lintegral_mono
          intro γ
          simp only [failedPassageWeight]
          by_cases hγ : γ ∈ {γ : Path d | passageSequence Δ lam R a γ i 0 ≠ ⊤ ∧
              ∀ j < 0, ¬ IsGoodPassage Δ lam R a γ i j}
          · rw [Set.indicator_of_mem hγ,
              passage_displacement_zero Δ lam R a ha γ i hγ.1, sub_self, mul_zero,
              Real.exp_zero, ENNReal.ofReal_one]
          · rw [Set.indicator_of_notMem hγ]
            exact zero_le
      _ = ENNReal.ofReal ρ ^ 0 := by simp
  | succ n ih =>
    let T : Path d → WithTop ℝ≥0 := fun γ => passageSequence Δ lam R a γ i n
    have hT := EinsteinFull.Blueprint.coupling_scope_isStoppingTime_passageSequence
      Δ hΔ lam R a hR i n (d := d)
    have hrestart := lintegral_mul_shift_extended_stopping hd ω f Λ hΛ hω h0 h1 G T
      (measurable_passage Δ lam R a i n) hT x (failedPassageWeight Δ lam R a b i n)
      (measurable_failedPassageWeight_stopping Δ hΔ lam R a b hR i n)
      (fun γ htop => by
        simp only [failedPassageWeight]
        apply Set.indicator_of_notMem
        rintro ⟨h, _⟩
        exact h htop)
      (failedWindowWeight Δ lam R b i) (measurable_failedWindowWeight Δ lam R b i)
    have hshift (γ : Path d) : pathTimeShift γ (passageSequence Δ lam R a γ i n).toNNReal =
        MarkovProcess.ContinuousPath.shift ((T γ).untopD 0) γ := by
      ext t
      rfl
    calc ∫⁻ γ, failedPassageWeight Δ lam R a b i (n + 1) γ ∂G.pathLaw x
        ≤ ∫⁻ γ, failedPassageWeight Δ lam R a b i n γ *
            failedWindowWeight Δ lam R b i
              (MarkovProcess.ContinuousPath.shift ((T γ).untopD 0) γ) ∂G.pathLaw x := by
          apply lintegral_mono
          intro γ
          beta_reduce
          rw [← hshift]
          exact failedPassageWeight_succ_le Δ hΔ lam R a b hlam hR hb i n γ
      _ = ∫⁻ γ, failedPassageWeight Δ lam R a b i n γ *
            (∫⁻ η, failedWindowWeight Δ lam R b i η ∂G.pathLaw (γ ((T γ).untopD 0)))
              ∂G.pathLaw x := hrestart
      _ ≤ ∫⁻ γ, failedPassageWeight Δ lam R a b i n γ * ENNReal.ofReal ρ ∂G.pathLaw x := by
          apply lintegral_mono
          intro γ
          beta_reduce
          gcongr
          exact hwin _
      _ = ENNReal.ofReal ρ * ∫⁻ γ, failedPassageWeight Δ lam R a b i n γ ∂G.pathLaw x := by
          rw [lintegral_mul_const _ (measurable_failedPassageWeight Δ lam R a b i n), mul_comm]
      _ ≤ ENNReal.ofReal ρ * ENNReal.ofReal ρ ^ n := by gcongr
      _ = ENNReal.ofReal ρ ^ (n + 1) := by rw [pow_succ, mul_comm]

/-- Exponential moment of the height of the first rounded candidate above the
search level. -/
theorem first_candidate_height_lintegral_le {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (f Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (h0 : 0 ≤ f) (h1 : f ≤ 1)
    (G : GantertFixedEnvironmentRealization hd Λ hΛ ω hω f h0 h1)
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (lam R a b : ℝ) (hlam : 0 < lam) (hR : 0 < R)
    (ha : 0 ≤ a / lam) (hb : 0 ≤ b) (i : Fin d) (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hwin : ∀ y, ∫⁻ η, failedWindowWeight Δ lam R b i η ∂G.pathLaw y ≤ ENNReal.ofReal ρ)
    (x : Vec d) :
    ∫⁻ γ, {γ : Path d | firstRoundedCandidate Δ lam R a γ i ≠ ⊤}.indicator
      (fun γ => ENNReal.ofReal (Real.exp (b * lam *
        (γ (firstRoundedCandidate Δ lam R a γ i).toNNReal i - γ 0 i - a / lam)))) γ
      ∂G.pathLaw x ≤ ENNReal.ofReal (Real.exp (b * lam * (R / 2)) / (1 - ρ)) := by
  have hpoint : ∀ γ : Path d, {γ : Path d | firstRoundedCandidate Δ lam R a γ i ≠ ⊤}.indicator
      (fun γ => ENNReal.ofReal (Real.exp (b * lam *
        (γ (firstRoundedCandidate Δ lam R a γ i).toNNReal i - γ 0 i - a / lam)))) γ ≤
      ENNReal.ofReal (Real.exp (b * lam * (R / 2))) *
        ∑' n, failedPassageWeight Δ lam R a b i n γ := by
    intro γ
    by_cases hC : firstRoundedCandidate Δ lam R a γ i ≠ ⊤
    · rw [Set.indicator_of_mem (show γ ∈ {γ : Path d | firstRoundedCandidate Δ lam R a γ i ≠ ⊤}
        from hC)]
      obtain ⟨k, hk, hmin, heq⟩ := firstRoundedCandidate_eq_first_good Δ hΔ lam R a hR γ i hC
      have hVk : passageSequence Δ lam R a γ i k ≠ ⊤ := hk.1
      have hwin' := good_passage_roundUp_le Δ hΔ lam R a γ i k hk
      have hYk : failedPassageWeight Δ lam R a b i k γ = ENNReal.ofReal (Real.exp (b * lam *
          (γ (passageSequence Δ lam R a γ i k).toNNReal i - γ 0 i - a / lam))) := by
        simp only [failedPassageWeight]
        exact Set.indicator_of_mem (show γ ∈ {γ : Path d | passageSequence Δ lam R a γ i k ≠ ⊤ ∧
          ∀ j < k, ¬ IsGoodPassage Δ lam R a γ i j} from ⟨hVk, hmin⟩) _
      calc ENNReal.ofReal (Real.exp (b * lam *
            (γ (firstRoundedCandidate Δ lam R a γ i).toNNReal i - γ 0 i - a / lam)))
          ≤ ENNReal.ofReal (Real.exp (b * lam * (R / 2)) * Real.exp (b * lam *
            (γ (passageSequence Δ lam R a γ i k).toNNReal i - γ 0 i - a / lam))) := by
            apply ENNReal.ofReal_le_ofReal
            rw [← Real.exp_add, heq]
            apply Real.exp_le_exp.mpr
            have hbl : 0 ≤ b * lam := mul_nonneg hb hlam.le
            nlinarith
        _ = ENNReal.ofReal (Real.exp (b * lam * (R / 2))) *
            failedPassageWeight Δ lam R a b i k γ := by
            rw [hYk, ENNReal.ofReal_mul (Real.exp_pos _).le]
        _ ≤ _ := by
            gcongr
            exact ENNReal.le_tsum (f := fun n => failedPassageWeight Δ lam R a b i n γ) k
    · rw [Set.indicator_of_notMem (show γ ∉ {γ : Path d | firstRoundedCandidate Δ lam R a γ i ≠ ⊤}
        from hC)]
      exact zero_le
  have hρ' : ENNReal.ofReal ρ < 1 := ENNReal.ofReal_lt_one.mpr hρ1
  calc _ ≤ ∫⁻ γ, ENNReal.ofReal (Real.exp (b * lam * (R / 2))) *
          ∑' n, failedPassageWeight Δ lam R a b i n γ ∂G.pathLaw x := lintegral_mono hpoint
    _ = ENNReal.ofReal (Real.exp (b * lam * (R / 2))) *
          ∑' n, ∫⁻ γ, failedPassageWeight Δ lam R a b i n γ ∂G.pathLaw x := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_tsum fun n => (measurable_failedPassageWeight Δ lam R a b i n).aemeasurable]
    _ ≤ ENNReal.ofReal (Real.exp (b * lam * (R / 2))) * ∑' n : ℕ, ENNReal.ofReal ρ ^ n := by
        gcongr with n
        exact lintegral_failedPassageWeight_le hd ω f Λ hΛ hω h0 h1 G Δ hΔ lam R a b hlam hR
          ha hb i ρ hwin x n
    _ = ENNReal.ofReal (Real.exp (b * lam * (R / 2)) / (1 - ρ)) := by
        rw [ENNReal.tsum_geometric, ← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ hρ0,
          ← ENNReal.ofReal_inv_of_pos (by linarith), ← ENNReal.ofReal_mul (Real.exp_pos _).le]
        congr 1

end EinsteinFull.Regeneration
