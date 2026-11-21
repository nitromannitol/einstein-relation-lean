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


/-- Stopping a path after its fall does not change the fall weight. -/
theorem fallWeight_stoppedPath {d : ℕ} (lam R a : ℝ) (i : Fin d) (γ : Path d) (t : ℝ≥0)
    (ht : firstHittingBelow γ i (-R) ≤ (t : ℝ≥0∞)) :
    fallWeight lam R a i (MarkovProcess.ContinuousPath.stoppedPath t γ) = fallWeight lam R a i γ := by
  have hpre : ∀ s ≤ t, γ s = MarkovProcess.ContinuousPath.stoppedPath t γ s :=
    fun s hs => (MarkovProcess.ContinuousPath.stoppedPath_apply_of_le t γ s hs).symm
  have hH := firstHittingBelow_eq_of_agree γ (MarkovProcess.ContinuousPath.stoppedPath t γ) i (-R)
    t hpre ht
  have hfin : firstHittingBelow γ i (-R) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top ht
  have hHt : (firstHittingBelow γ i (-R)).toNNReal ≤ t := by
    apply ENNReal.coe_le_coe.mp
    rw [ENNReal.coe_toNNReal hfin]
    exact ht
  have hmax : coordinateMaximum (MarkovProcess.ContinuousPath.stoppedPath t γ) i
      (firstHittingBelow γ i (-R)).toNNReal = coordinateMaximum γ i (firstHittingBelow γ i (-R)).toNNReal := by
    unfold coordinateMaximum
    congr 1
    apply Set.image_congr
    intro s hs
    rw [← hpre s (hs.2.trans hHt), ← hpre 0 zero_le]
  simp only [fallWeight]
  rw [Set.indicator_of_mem (show MarkovProcess.ContinuousPath.stoppedPath t γ ∈
      {γ : Path d | firstHittingBelow γ i (-R) ≠ ⊤} by
      change firstHittingBelow (MarkovProcess.ContinuousPath.stoppedPath t γ) i (-R) ≠ ⊤
      rw [hH]
      exact hfin),
    Set.indicator_of_mem (show γ ∈ {γ : Path d | firstHittingBelow γ i (-R) ≠ ⊤} from hfin), hH,
    hmax]

/-- The strong Markov property at the fall bounds the failure weight of a supplied
realization by the fall weight times a uniform window moment. -/
theorem lintegral_trialFailureWeight_le {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (f Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (h0 : 0 ≤ f) (h1 : f ≤ 1)
    (G : GantertFixedEnvironmentRealization hd Λ hΛ ω hω f h0 h1)
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (lam R a : ℝ) (hlam : 0 < lam) (hR : 0 < R) (ha : 0 ≤ a)
    (i : Fin d) (Cw : ℝ)
    (hwin : ∀ y, ∫⁻ η, windowWeight Δ lam a i η ∂G.pathLaw y ≤ ENNReal.ofReal Cw) (x : Vec d) :
    ∫⁻ γ, trialFailureWeight Δ lam R a i γ ∂G.pathLaw x ≤
      ENNReal.ofReal (Real.exp (a * lam * (13 * R))) *
        (ENNReal.ofReal Cw * ∫⁻ γ, fallWeight lam R a i γ ∂G.pathLaw x) := by
  let T : Path d → WithTop ℝ≥0 := fun γ => firstHittingBelow γ i (-R)
  have hTm : Measurable T := measurable_first_downcrossing R i
  have hT := isStoppingTime_firstHittingBelow (d := d) i (-R)
  have hw : Measurable[hT.measurableSpace] (fallWeight (d := d) lam R a i) := by
    apply measurable_stopping_of_prefix T hTm hT
    · intro γ t
      exact (firstHittingBelow_le_iff_of_agree γ (MarkovProcess.ContinuousPath.stoppedPath t γ) i
        (-R) t (fun s hs => (MarkovProcess.ContinuousPath.stoppedPath_apply_of_le t γ s hs).symm)).symm
    · exact measurable_fallWeight lam R a i
    · intro γ htop
      simp only [fallWeight]
      exact Set.indicator_of_notMem (show γ ∉ {γ : Path d | firstHittingBelow γ i (-R) ≠ ⊤} from
        fun h => h htop) _
    · intro γ t ht
      exact fallWeight_stoppedPath lam R a i γ t ht
  have hrestart := lintegral_mul_shift_extended_stopping hd ω f Λ hΛ hω h0 h1 G T hTm hT x
    (fallWeight lam R a i) hw (fun γ htop => by
      simp only [fallWeight]
      exact Set.indicator_of_notMem (show γ ∉ {γ : Path d | firstHittingBelow γ i (-R) ≠ ⊤} from
        fun h => h htop) _)
    (windowWeight Δ lam a i) (measurable_windowWeight Δ lam a i)
  have hshift (γ : Path d) : pathTimeShift γ (firstHittingBelow γ i (-R)).toNNReal =
      MarkovProcess.ContinuousPath.shift ((T γ).untopD 0) γ := by
    ext t
    rfl
  calc ∫⁻ γ, trialFailureWeight Δ lam R a i γ ∂G.pathLaw x
      ≤ ∫⁻ γ, ENNReal.ofReal (Real.exp (a * lam * (13 * R))) *
          (fallWeight lam R a i γ * windowWeight Δ lam a i
            (MarkovProcess.ContinuousPath.shift ((T γ).untopD 0) γ)) ∂G.pathLaw x := by
        apply lintegral_mono
        intro γ
        beta_reduce
        rw [← hshift]
        exact trialFailureWeight_le Δ hΔ lam R a hlam hR ha i γ
    _ = ENNReal.ofReal (Real.exp (a * lam * (13 * R))) *
          ∫⁻ γ, fallWeight lam R a i γ * (∫⁻ η, windowWeight Δ lam a i η
            ∂G.pathLaw (γ ((T γ).untopD 0))) ∂G.pathLaw x := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hrestart]
    _ ≤ ENNReal.ofReal (Real.exp (a * lam * (13 * R))) *
          ∫⁻ γ, fallWeight lam R a i γ * ENNReal.ofReal Cw ∂G.pathLaw x := by
        gcongr with γ
        exact hwin _
    _ = _ := by
        rw [lintegral_mul_const _ (measurable_fallWeight lam R a i), mul_comm (∫⁻ _, _ ∂_)]


/-- Uniform failure factor of the trials of supplied reduced diffusions, under the
positive slab-exit estimate of GMP Lemma 4.3. -/
theorem uniform_trial_failure_factor (d : ℕ) (hd : 2 ≤ d) (Λ r L : ℝ) (hL : 1 ≤ L) :
    ∃ c Cw l₀ : ℝ, 0 < c ∧ 0 ≤ Cw ∧ 0 < l₀ ∧
      ∀ (Q : EnvironmentLaw d Λ r) (μ : ℝ) (hμ : 0 < μ) (hμ1 : μ ≤ 1)
        (P : QuenchedPathLaws d),
        IsGMPReducedKernel hd Q.ellipticity_parameter Q μ hμ.le hμ1 P →
        (∀ᵐ ω ∂Q.measure, ∀ y : Vec d, (2 / 3 : ℝ) ≤ (P (y, ω)).real {γ |
          coordinateSlabExit γ (Renewal.forceCoord hd) (L / μ) ≠ ⊤ ∧
          γ (coordinateSlabExit γ (Renewal.forceCoord hd) (L / μ)).toNNReal
            (Renewal.forceCoord hd) - γ 0 (Renewal.forceCoord hd) = L / μ}) →
        ∀ l : ℝ, l₀ ≤ l → ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 →
        ∀ᵐ ω ∂Q.measure, ∀ y : Vec d,
          ∫⁻ γ, trialFailureWeight (Renewal.regenDelta μ) μ (l / μ) (θ * c)
            (Renewal.forceCoord hd) γ ∂P (y, ω) ≤
            ENNReal.ofReal (Real.exp (θ * c * (13 * l)) * ((1 + θ * Cw) * (1 / 2 + θ / 4))) := by
  obtain ⟨a₀, l₀, ha₀, hl₀, hsmall⟩ :=
    uniform_coupled_downcrossing_small_tilt_of_positive_exit d hd Λ r L hL
  obtain ⟨b₁, C, hb₁, hC, hwin⟩ := uniform_reduced_window_maximum_moment hd Λ r
  refine ⟨min a₀ b₁, C, l₀, lt_min ha₀ hb₁, hC.le, hl₀, ?_⟩
  intro Q μ hμ hμ1 P hP hpositive l hl θ hθ0 hθ1
  set c := min a₀ b₁ with hc
  have hca : c ≤ a₀ := min_le_left _ _
  have hcb : c ≤ b₁ := min_le_right _ _
  have hlpos : 0 < l := lt_of_lt_of_le hl₀ hl
  filter_upwards [hP, hpositive, hwin Q μ hμ hμ1 P hP] with ω hreal hp hW
  obtain ⟨hω, G, hrow⟩ := hreal
  have : IsMarkovKernel G.pathLaw := G.pathLaw_isMarkovKernel
  have hpositiveG : ∀ y : Vec d, (2 / 3 : ℝ) ≤ (G.pathLaw y).real {γ |
      coordinateSlabExit γ (Renewal.forceCoord hd) (L / μ) ≠ ⊤ ∧
      γ (coordinateSlabExit γ (Renewal.forceCoord hd) (L / μ)).toNNReal
        (Renewal.forceCoord hd) - γ 0 (Renewal.forceCoord hd) = L / μ} := by
    intro y
    rw [← hrow y]
    exact hp y
  intro y
  let i := Renewal.forceCoord hd
  let Δ := Renewal.regenDelta μ
  let R := l / μ
  have hR : 0 < R := div_pos hlpos hμ
  have hμR : μ * R = l := by simp only [R]; field_simp
  -- window moment
  have hwinG : ∀ x, ∫⁻ η, windowWeight Δ μ (θ * c) i η ∂G.pathLaw x ≤
      ENNReal.ofReal (1 + θ * C) := by
    intro x
    obtain ⟨hint, hle⟩ := hW x i
    rw [hrow x] at hint hle
    have hlint : ∫⁻ η, ENNReal.ofReal (Real.exp (b₁ * (μ * coordinateMaximum η i Δ)))
        ∂G.pathLaw x ≤ ENNReal.ofReal C := by
      rw [← ofReal_integral_eq_lintegral_ofReal hint
        (Filter.Eventually.of_forall fun η => (Real.exp_pos _).le)]
      exact ENNReal.ofReal_le_ofReal hle
    calc ∫⁻ η, windowWeight Δ μ (θ * c) i η ∂G.pathLaw x
        ≤ ∫⁻ η, 1 + ENNReal.ofReal θ *
            ENNReal.ofReal (Real.exp (b₁ * (μ * coordinateMaximum η i Δ))) ∂G.pathLaw x := by
          apply lintegral_mono
          intro η
          simp only [windowWeight]
          rw [← ENNReal.ofReal_mul hθ0, ← ENNReal.ofReal_one,
            ← ENNReal.ofReal_add zero_le_one (mul_nonneg hθ0 (Real.exp_pos _).le)]
          apply ENNReal.ofReal_le_ofReal
          have hM := coordinateMaximum_nonneg η i Δ
          have hX : 0 ≤ μ * coordinateMaximum η i Δ := mul_nonneg hμ.le hM
          have h1 : θ * c * μ * coordinateMaximum η i Δ ≤ θ * (b₁ * (μ * coordinateMaximum η i Δ)) := by
            have := mul_le_mul_of_nonneg_right hcb hX
            nlinarith
          calc Real.exp (θ * c * μ * coordinateMaximum η i Δ)
              ≤ Real.exp (θ * (b₁ * (μ * coordinateMaximum η i Δ))) := Real.exp_le_exp.mpr h1
            _ ≤ 1 + θ * Real.exp (b₁ * (μ * coordinateMaximum η i Δ)) :=
              exp_mul_le_one_add_mul_exp θ _ hθ0 hθ1
      _ = 1 + ENNReal.ofReal θ * ∫⁻ η, ENNReal.ofReal
            (Real.exp (b₁ * (μ * coordinateMaximum η i Δ))) ∂G.pathLaw x := by
          rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, one_mul,
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ ≤ 1 + ENNReal.ofReal θ * ENNReal.ofReal C := by gcongr
      _ = ENNReal.ofReal (1 + θ * C) := by
          rw [← ENNReal.ofReal_mul hθ0, ← ENNReal.ofReal_one,
            ← ENNReal.ofReal_add zero_le_one (mul_nonneg hθ0 hC.le)]
  -- fall moment
  have hfall : ∫⁻ γ, fallWeight μ R (θ * c) i γ ∂G.pathLaw y ≤ ENNReal.ofReal (1 / 2 + θ / 4) := by
    let ν : Measure (CoupledSample d) :=
      (G.pathLaw y).map (fun γ : Path d => ((γ, fun _ => false) : CoupledSample d))
    have hνm : Measurable (fun γ : Path d => ((γ, fun _ => false) : CoupledSample d)) :=
      measurable_id.prodMk measurable_const
    have hν : ν.map Prod.fst = G.pathLaw y := by
      rw [Measure.map_map measurable_fst hνm]
      exact Measure.map_id
    obtain ⟨hint, hle⟩ := hsmall Q μ hμ hμ1 ω hω G hpositiveG y ν hν l hl θ hθ0 hθ1
    set E := {z : CoupledSample d | firstHittingBelow z.1 (Renewal.forceCoord hd) (-(l / μ)) ≠ ⊤}
    set F := fun z : CoupledSample d => Real.exp ((θ * a₀) * μ *
      coordinateMaximum z.1 (Renewal.forceCoord hd)
        (firstHittingBelow z.1 (Renewal.forceCoord hd) (-(l / μ))).toNNReal)
    have hmono : ∀ γ : Path d, fallWeight μ R (θ * c) i γ ≤
        ENNReal.ofReal (E.indicator F ((γ, fun _ => false) : CoupledSample d)) := by
      intro γ
      by_cases hH : firstHittingBelow γ i (-R) ≠ ⊤
      · simp only [fallWeight]
        rw [Set.indicator_of_mem (show γ ∈ {γ : Path d | firstHittingBelow γ i (-R) ≠ ⊤} from hH),
          Set.indicator_of_mem (show ((γ, fun _ => false) : CoupledSample d) ∈ E from hH)]
        apply ENNReal.ofReal_le_ofReal
        apply Real.exp_le_exp.mpr
        have hM := coordinateMaximum_nonneg γ i (firstHittingBelow γ i (-R)).toNNReal
        have h1 : θ * c ≤ θ * a₀ := mul_le_mul_of_nonneg_left hca hθ0
        have h2 : 0 ≤ μ * coordinateMaximum γ i (firstHittingBelow γ i (-R)).toNNReal :=
          mul_nonneg hμ.le hM
        change θ * c * μ * coordinateMaximum γ i (firstHittingBelow γ i (-R)).toNNReal ≤
          θ * a₀ * μ * coordinateMaximum γ i (firstHittingBelow γ i (-R)).toNNReal
        nlinarith
      · simp only [fallWeight]
        rw [Set.indicator_of_notMem (show γ ∉ {γ : Path d | firstHittingBelow γ i (-R) ≠ ⊤}
          from hH)]
        exact zero_le
    have hEm : MeasurableSet E :=
      (measurableSet_eq_fun ((measurable_first_downcrossing (l / μ) (Renewal.forceCoord hd)).comp
        measurable_fst) measurable_const).compl
    calc ∫⁻ γ, fallWeight μ R (θ * c) i γ ∂G.pathLaw y
        ≤ ∫⁻ γ, ENNReal.ofReal (E.indicator F ((γ, fun _ => false) : CoupledSample d))
          ∂G.pathLaw y := lintegral_mono hmono
      _ = ∫⁻ z, ENNReal.ofReal (E.indicator F z) ∂ν := by
          rw [lintegral_map _ hνm]
          exact ENNReal.measurable_ofReal.comp (Measurable.indicator
            (Real.measurable_exp.comp (measurable_const.mul
              ((measurable_maximum_at_downcrossing (l / μ) (Renewal.forceCoord hd)).comp
                measurable_fst))) hEm)
      _ = ENNReal.ofReal (∫ z, E.indicator F z ∂ν) := by
          rw [ofReal_integral_eq_lintegral_ofReal hint
            (Filter.Eventually.of_forall fun z => Set.indicator_nonneg
              (fun z _ => (Real.exp_pos _).le) z)]
      _ ≤ ENNReal.ofReal (1 / 2 + θ / 4) := ENNReal.ofReal_le_ofReal hle
  have hmain := lintegral_trialFailureWeight_le hd (zeroPotentialReducedPair ω) μ
    (sourceReducedBound Λ) (one_le_sourceReducedBound Q.ellipticity_parameter) hω hμ.le hμ1 G Δ
    (EinsteinRelation.regenDelta_pos hμ) μ R (θ * c) hμ hR (mul_nonneg hθ0 (lt_min ha₀ hb₁).le) i
    (1 + θ * C) hwinG y
  rw [hrow y]
  calc ∫⁻ γ, trialFailureWeight Δ μ R (θ * c) i γ ∂G.pathLaw y
      ≤ ENNReal.ofReal (Real.exp (θ * c * μ * (13 * R))) *
          (ENNReal.ofReal (1 + θ * C) * ∫⁻ γ, fallWeight μ R (θ * c) i γ ∂G.pathLaw y) := hmain
    _ ≤ ENNReal.ofReal (Real.exp (θ * c * μ * (13 * R))) *
          (ENNReal.ofReal (1 + θ * C) * ENNReal.ofReal (1 / 2 + θ / 4)) := by gcongr
    _ = _ := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (Real.exp_pos _).le]
        congr 2
        congr 1
        rw [← hμR]
        ring

end EinsteinFull.Regeneration
