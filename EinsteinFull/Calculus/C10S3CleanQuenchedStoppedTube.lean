import EinsteinFull.Calculus.C10S3CleanStoppedTube
import EinsteinFull.Calculus.C19S3CleanHistoryParameterIntegral
import EinsteinFull.Calculus.FellerRegularSet
import MarkovProcess.Path.Shift

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation

/-- The closed Euclidean tube is a Borel event. -/
theorem c10_clean_closed_tube_measurable {d : ℕ} (Δ : ℝ≥0) (R : ℝ) :
    MeasurableSet {γ : Path d | ∀ s ∈ Set.Icc (0 : ℝ≥0) Δ,
      euclideanNorm (γ s - γ 0) ≤ R / 2} := by
  have hc : IsClosed {γ : Path d | ∀ s ∈ Set.Icc (0 : ℝ≥0) Δ,
      euclideanNorm (γ s - γ 0) ≤ R / 2} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun s => isClosed_iInter fun _ =>
      isClosed_le ((Calculus.Feller.continuous_euclideanNorm d).comp
        ((continuous_eval_const s).sub (continuous_eval_const 0))) continuous_const
  exact hc.measurableSet


/-- The finite failed prefix is jointly measurable in its level and path. -/
theorem c10_clean_joint_guard_prefix_measurable {d : ℕ} (Δ : ℝ≥0)
    (lam R : ℝ) (i : Fin d) (N : ℕ) :
    MeasurableSet {p : ℝ × Path d |
      Regeneration.passageSequence Δ lam R p.1 p.2 i (2 * N) < ⊤ ∧
      ∀ k < N, Regeneration.passageSequence Δ lam R p.1 p.2 i (2 * k) ≠ ⊤ ∧
        ¬Regeneration.IsGoodPassage Δ lam R p.1 p.2 i (2 * k)} := by
  have ht := Regeneration.measurable_passageSequence_joint Δ lam R i (2 * N)
  have heq : {p : ℝ × Path d | ∀ k < N,
      Regeneration.passageSequence Δ lam R p.1 p.2 i (2 * k) ≠ ⊤ ∧
        ¬Regeneration.IsGoodPassage Δ lam R p.1 p.2 i (2 * k)} =
      ⋂ k : ℕ, ⋂ (_ : k < N), {p : ℝ × Path d |
        Regeneration.passageSequence Δ lam R p.1 p.2 i (2 * k) ≠ ⊤ ∧
          ¬Regeneration.IsGoodPassage Δ lam R p.1 p.2 i (2 * k)} := by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
  have hp : MeasurableSet {p : ℝ × Path d | ∀ k < N,
      Regeneration.passageSequence Δ lam R p.1 p.2 i (2 * k) ≠ ⊤ ∧
        ¬Regeneration.IsGoodPassage Δ lam R p.1 p.2 i (2 * k)} := by
    rw [heq]
    apply MeasurableSet.iInter
    intro k
    apply MeasurableSet.iInter
    intro _
    exact ((measurableSet_eq_fun
      (Regeneration.measurable_passageSequence_joint Δ lam R i (2 * k))
      measurable_const).compl).inter
        (Regeneration.measurableSet_IsGoodPassage Δ lam R i (2 * k)).compl
  exact (measurableSet_lt ht measurable_const).inter hp

/-- The tube at a passage is jointly measurable in its level and path. -/
theorem c10_clean_joint_passage_tube_measurable {d : ℕ} (Δ : ℝ≥0)
    (lam R : ℝ) (i : Fin d) (N : ℕ) :
    MeasurableSet {p : ℝ × Path d | ∀ s ∈ Set.Icc (0 : ℝ≥0) Δ,
      euclideanNorm (p.2 ((Regeneration.passageSequence Δ lam R p.1 p.2 i
        (2 * N)).toNNReal + s) - p.2 (Regeneration.passageSequence Δ lam R
        p.1 p.2 i (2 * N)).toNNReal) ≤ R / 2} := by
  have ht := (Regeneration.measurable_passageSequence_joint Δ lam R i (2 * N)).ennreal_toNNReal
  have hs : Measurable (fun p : ℝ × Path d => MarkovProcess.ContinuousPath.shift
      (Regeneration.passageSequence Δ lam R p.1 p.2 i (2 * N)).toNNReal p.2) :=
    MarkovProcess.ContinuousPath.continuous_shift.measurable.comp (ht.prodMk measurable_snd)
  simpa only [Set.preimage_setOf_eq, MarkovProcess.ContinuousPath.shift_apply, add_zero]
    using (c10_clean_closed_tube_measurable Δ R).preimage hs

/-- Restart a bounded future test at a history-measurable level. -/

theorem c10_clean_history_level_restart {d : ℕ} (hd : 2 ≤ d)
    {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ)
    (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ)
    (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K) (m : ℕ)
    (A : Regeneration.CoupledSample d → ℝ)
    (hA : Measurable[Regeneration.finiteHistorySigma
      (Regeneration.Renewal.regenDelta lam) m] A)
    (F : ℝ × Regeneration.CoupledSample d → ℝ) (hF : Measurable F)
    (hbF : Regeneration.BoundedRealTest F) :
    let Δ := Regeneration.Renewal.regenDelta lam
    let μ := Regeneration.annealedCoupledLaw Q.measure K
    (∫ q, F (A q.2, Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)) ∂μ) =
    ∫ q, ∫ w, F (A q.2, w) ∂K (q.2.1 ((m : ℝ≥0) * Δ), q.1) ∂μ := by
  have hr := c19_s3_actual_history_parameter_integral hd Q lam h0 h1 l δ P K hK m A hA (fun _ => 1) measurable_const
    (show Regeneration.BoundedRealTest (fun _ => 1) from ⟨1, by intro z; simp⟩)
    F hF hbF
  simpa only [one_mul] using hr

/-- The literal failed-prefix event is the joint level/path prefix after restart. -/

theorem c10_clean_guard_prefix_event_eq {d : ℕ} (Δ : ℝ≥0) (lam R : ℝ)
    (A : Regeneration.CoupledSample d → ℝ) (m : ℕ) (i : Fin d) (N : ℕ) :
    c10CleanCouplingScopeEvenGuardFailure Δ lam R A m i Set.univ N ∩
      {q | c10CleanCouplingScopePassage Δ lam R A m i (2 * N) q.2 ≠ ⊤} =
    (fun q : FieldPair d × Regeneration.CoupledSample d =>
      (A q.2, (Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)).1)) ⁻¹'
      {p : ℝ × Path d |
        Regeneration.passageSequence Δ lam R p.1 p.2 i (2 * N) < ⊤ ∧
        ∀ k < N, Regeneration.passageSequence Δ lam R p.1 p.2 i (2 * k) ≠ ⊤ ∧
          ¬Regeneration.IsGoodPassage Δ lam R p.1 p.2 i (2 * k)} := by
  ext q
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_setOf_eq,
    c10CleanCouplingScopeEvenGuardFailure, c10CleanCouplingScopeEvenGuard, c10CleanCouplingScopePassage,
    Set.mem_univ, true_and, lt_top_iff_ne_top]
  exact and_comm

/-- A uniform tube bound survives conditioning on the finite failed-guard prefix. -/
theorem c10_clean_guard_prefix_tube_bound
    {d : ℕ} (K : Kernel (Vec d) (Path d))
    (Δ : ℝ≥0) (lam R a : ℝ)
    (i : Fin d) (N : ℕ) (x : Vec d) (ε : ℝ≥0∞)
    (hrestart :
      let T : Path d → ℝ≥0∞ := fun γ => Regeneration.passageSequence Δ lam R a γ i (2 * N)
      let A : Set (Path d) := {γ | T γ < ⊤ ∧ ∀ r < N,
        Regeneration.passageSequence Δ lam R a γ i (2 * r) ≠ ⊤ ∧
          ¬Regeneration.IsGoodPassage Δ lam R a γ i (2 * r)}
      ((K x).restrict A).map
        (fun γ => MarkovProcess.ContinuousPath.shift ((T γ).untopD 0) γ) =
      Measure.bind ((K x).restrict A) (fun γ => K (γ ((T γ).untopD 0))))
    (hTube : ∀ y, ε ≤ K y {γ | ∀ s ∈ Set.Icc (0 : ℝ≥0) Δ,
      euclideanNorm (γ s - γ 0) ≤ R / 2}) :
    let T : Path d → ℝ≥0∞ := fun γ => Regeneration.passageSequence Δ lam R a γ i (2 * N)
    let A : Set (Path d) := {γ | T γ < ⊤ ∧ ∀ r < N,
      Regeneration.passageSequence Δ lam R a γ i (2 * r) ≠ ⊤ ∧
        ¬Regeneration.IsGoodPassage Δ lam R a γ i (2 * r)}
    ε * K x A ≤ K x (A ∩ {γ | ∀ s ∈ Set.Icc (0 : ℝ≥0) Δ,
      euclideanNorm (γ ((T γ).toNNReal + s) - γ ((T γ).toNNReal)) ≤ R / 2}) := by
  classical
  dsimp only
  let T : Path d → ℝ≥0∞ := fun γ => Regeneration.passageSequence Δ lam R a γ i (2 * N)
  let A : Set (Path d) := {γ | T γ < ⊤ ∧ ∀ r < N,
    Regeneration.passageSequence Δ lam R a γ i (2 * r) ≠ ⊤ ∧
      ¬Regeneration.IsGoodPassage Δ lam R a γ i (2 * r)}
  let B : Set (Path d) := {γ | ∀ s ∈ Set.Icc (0 : ℝ≥0) Δ,
    euclideanNorm (γ s - γ 0) ≤ R / 2}
  let S : Path d → Path d := fun γ => MarkovProcess.ContinuousPath.shift ((T γ).untopD 0) γ
  have hB : MeasurableSet B := c10_clean_closed_tube_measurable Δ R
  have hT : Measurable T := (Regeneration.measurable_passageSequence_joint Δ lam R i (2 * N)).comp
    (measurable_const.prodMk measurable_id)
  have hS : Measurable S := MarkovProcess.ContinuousPath.continuous_shift.measurable.comp
    (hT.ennreal_toNNReal.prodMk measurable_id)
  have hre := hrestart
  change ((K x).restrict A).map S = Measure.bind ((K x).restrict A)
    (fun γ => K (γ ((T γ).untopD 0))) at hre
  have hmeasure : ((K x).restrict A).map S B =
      ∫⁻ γ in A, K (γ ((T γ).untopD 0)) B ∂K x := by
    rw [hre, Measure.bind_apply hB]
    exact K.aemeasurable.comp_measurable ((continuous_eval.measurable).comp
      (measurable_id.prodMk hT.ennreal_toNNReal))
  have hlower : ε * K x A ≤ ((K x).restrict A).map S B := by
    rw [hmeasure, ← Measure.restrict_apply_univ, ← lintegral_const]
    exact lintegral_mono (fun γ => hTube _)
  rw [Measure.map_apply hS hB, Measure.restrict_apply (hB.preimage hS)] at hlower
  simpa only [A, B, S, T, Set.preimage_setOf_eq, Set.inter_comm,
    MarkovProcess.ContinuousPath.shift_apply, add_zero, ENNReal.toNNReal] using hlower


/-- The fixed-level tube estimate applies directly to every supplied realization. -/
theorem c10_clean_supplied_guard_prefix_tube_bound
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (r : EinsteinRelation.External.GantertSection7Support.GantertFixedEnvironmentRealization
      hd Λ hΛ ω hω lam h0 h1)
    (Δ : ℝ≥0) (R a : ℝ)
    (i : Fin d) (N : ℕ) (x : Vec d) (ε : ℝ≥0∞)
    (hrestart :
      let T : Path d → ℝ≥0∞ := fun γ => Regeneration.passageSequence Δ lam R a γ i (2 * N)
      let A : Set (Path d) := {γ | T γ < ⊤ ∧ ∀ r < N,
        Regeneration.passageSequence Δ lam R a γ i (2 * r) ≠ ⊤ ∧
          ¬Regeneration.IsGoodPassage Δ lam R a γ i (2 * r)}
      ((r.pathLaw x).restrict A).map
        (fun γ => MarkovProcess.ContinuousPath.shift ((T γ).untopD 0) γ) =
      Measure.bind ((r.pathLaw x).restrict A) (fun γ => r.pathLaw (γ ((T γ).untopD 0))))
    (hTube : ∀ y, ε ≤ r.pathLaw y {γ | ∀ s ∈ Set.Icc (0 : ℝ≥0) Δ,
      euclideanNorm (γ s - y) ≤ R / 2}) :
    let T : Path d → ℝ≥0∞ := fun γ => Regeneration.passageSequence Δ lam R a γ i (2 * N)
    let A : Set (Path d) := {γ | T γ < ⊤ ∧ ∀ k < N,
      Regeneration.passageSequence Δ lam R a γ i (2 * k) ≠ ⊤ ∧
        ¬Regeneration.IsGoodPassage Δ lam R a γ i (2 * k)}
    ε * r.pathLaw x A ≤ r.pathLaw x (A ∩ {γ | ∀ s ∈ Set.Icc (0 : ℝ≥0) Δ,
      euclideanNorm (γ ((T γ).toNNReal + s) - γ (T γ).toNNReal) ≤ R / 2}) := by
  letI : IsMarkovKernel r.pathLaw := r.pathLaw_isMarkovKernel
  have htube : ∀ y, ε ≤ r.pathLaw y {γ | ∀ s ∈ Set.Icc (0 : ℝ≥0) Δ,
      euclideanNorm (γ s - γ 0) ≤ R / 2} := by
    intro y
    have heq : {γ : Path d | ∀ s ∈ Set.Icc (0 : ℝ≥0) Δ,
        euclideanNorm (γ s - γ 0) ≤ R / 2} =ᵐ[r.pathLaw y]
        {γ : Path d | ∀ s ∈ Set.Icc (0 : ℝ≥0) Δ,
        euclideanNorm (γ s - y) ≤ R / 2} := by
      filter_upwards [r.pathLaw_starts_at y] with γ hγ
      change γ 0 = y at hγ
      apply propext
      change (∀ s ∈ Set.Icc (0 : ℝ≥0) Δ, euclideanNorm (γ s - γ 0) ≤ R / 2) ↔
        (∀ s ∈ Set.Icc (0 : ℝ≥0) Δ, euclideanNorm (γ s - y) ≤ R / 2)
      rw [hγ]
    rw [measure_congr heq]
    exact hTube y
  exact c10_clean_guard_prefix_tube_bound r.pathLaw Δ lam R a i N x ε hrestart htube


/-- The fixed-level estimate transfers to a coupled law with the supplied path marginal. -/
theorem c10_clean_coupled_guard_prefix_tube_bound
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (r : EinsteinRelation.External.GantertSection7Support.GantertFixedEnvironmentRealization
      hd Λ hΛ ω hω lam h0 h1)
    (ν : Measure (Regeneration.CoupledSample d)) (x : Vec d)
    (hpath : ν.map Prod.fst = r.pathLaw x)
    (Δ : ℝ≥0) (R a : ℝ)
    (i : Fin d) (N : ℕ) (ε : ℝ≥0∞)
    (hrestart :
      let T : Path d → ℝ≥0∞ := fun γ => Regeneration.passageSequence Δ lam R a γ i (2 * N)
      let A : Set (Path d) := {γ | T γ < ⊤ ∧ ∀ r < N,
        Regeneration.passageSequence Δ lam R a γ i (2 * r) ≠ ⊤ ∧
          ¬Regeneration.IsGoodPassage Δ lam R a γ i (2 * r)}
      ((r.pathLaw x).restrict A).map
        (fun γ => MarkovProcess.ContinuousPath.shift ((T γ).untopD 0) γ) =
      Measure.bind ((r.pathLaw x).restrict A) (fun γ => r.pathLaw (γ ((T γ).untopD 0))))
    (hTube : ∀ y, ε ≤ r.pathLaw y {γ | ∀ s ∈ Set.Icc (0 : ℝ≥0) Δ,
      euclideanNorm (γ s - y) ≤ R / 2}) :
    let T : Path d → ℝ≥0∞ := fun γ => Regeneration.passageSequence Δ lam R a γ i (2 * N)
    let A : Set (Path d) := {γ | T γ < ⊤ ∧ ∀ k < N,
      Regeneration.passageSequence Δ lam R a γ i (2 * k) ≠ ⊤ ∧
        ¬Regeneration.IsGoodPassage Δ lam R a γ i (2 * k)}
    let B : Set (Path d) := {γ | ∀ s ∈ Set.Icc (0 : ℝ≥0) Δ,
      euclideanNorm (γ ((T γ).toNNReal + s) - γ (T γ).toNNReal) ≤ R / 2}
    ε * ν (Prod.fst ⁻¹' A) ≤ ν (Prod.fst ⁻¹' (A ∩ B)) := by
  classical
  dsimp only
  let T : Path d → ℝ≥0∞ := fun γ => Regeneration.passageSequence Δ lam R a γ i (2 * N)
  let A : Set (Path d) := {γ | T γ < ⊤ ∧ ∀ k < N,
    Regeneration.passageSequence Δ lam R a γ i (2 * k) ≠ ⊤ ∧
      ¬Regeneration.IsGoodPassage Δ lam R a γ i (2 * k)}
  let B : Set (Path d) := {γ | ∀ s ∈ Set.Icc (0 : ℝ≥0) Δ,
    euclideanNorm (γ ((T γ).toNNReal + s) - γ (T γ).toNNReal) ≤ R / 2}
  have hA : MeasurableSet A := by
    exact (c10_clean_joint_guard_prefix_measurable Δ lam R i N).preimage
      (measurable_const.prodMk measurable_id)
  have hT : Measurable T := (Regeneration.measurable_passageSequence_joint Δ lam R i (2 * N)).comp
    (measurable_const.prodMk measurable_id)
  have hS : Measurable (fun γ : Path d => MarkovProcess.ContinuousPath.shift (T γ).toNNReal γ) :=
    MarkovProcess.ContinuousPath.continuous_shift.measurable.comp (hT.ennreal_toNNReal.prodMk measurable_id)
  have hB : MeasurableSet B := by
    simpa only [B, Set.preimage_setOf_eq, MarkovProcess.ContinuousPath.shift_apply, add_zero]
      using (c10_clean_closed_tube_measurable Δ R).preimage hS
  have h := c10_clean_supplied_guard_prefix_tube_bound hd ω lam Λ hΛ hω h0 h1 r
    Δ R a i N x ε hrestart hTube
  change ε * r.pathLaw x A ≤ r.pathLaw x (A ∩ B) at h
  rw [← hpath, Measure.map_apply measurable_fst hA,
    Measure.map_apply measurable_fst (hA.inter hB)] at h
  exact h



/-- At every grid endpoint the coupled fibre is almost surely a probability law. -/
theorem c10_clean_grid_endpoint_probability {d : ℕ} (hd : 2 ≤ d)
    {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ)
    (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ)
    (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K) (m : ℕ) :
    ∀ᵐ q ∂Regeneration.annealedCoupledLaw Q.measure K,
      IsProbabilityMeasure (K (q.2.1 ((m : ℝ≥0) *
        Regeneration.Renewal.regenDelta lam), q.1)) := by
  by_cases hm : m = 0
  · subst m
    have hs := Regeneration.ae_origin_start_of_isGMPReducedKernel hd Q lam h0.le h1
      P K hK.1 hK.2.1 hK.2.2.1
    have hp : ∀ᵐ q ∂Regeneration.annealedCoupledLaw Q.measure K,
        IsProbabilityMeasure (K (0, q.1)) := by
      unfold Regeneration.annealedCoupledLaw
      apply Measure.ae_compProd_of_ae_ae
        (show MeasurableSet {q : FieldPair d × Regeneration.CoupledSample d |
          IsProbabilityMeasure (K (0, q.1))} from
          by
            rw [show {q : FieldPair d × Regeneration.CoupledSample d |
              IsProbabilityMeasure (K (0, q.1))} =
              {q | K (0, q.1) Set.univ = 1} from by
                ext q
                exact ⟨fun h => h.measure_univ, fun h => ⟨h⟩⟩]
            exact ((K.measurable_coe MeasurableSet.univ)
              (measurableSet_singleton 1)).preimage (measurable_const.prodMk measurable_fst))
      filter_upwards [hK.1.1] with ω hω
      exact Filter.Eventually.of_forall fun _ => hω
    filter_upwards [hs, hp] with q hq hprob
    simpa only [Nat.cast_zero, zero_mul, hq] using hprob
  · have hΔ : 0 < Regeneration.Renewal.regenDelta lam :=
      Real.toNNReal_pos.mpr (inv_pos.mpr (sq_pos_of_pos h0))
    have ht : 0 < (m : ℝ≥0) * Regeneration.Renewal.regenDelta lam :=
      mul_pos (by exact_mod_cast Nat.pos_of_ne_zero hm) hΔ
    exact Regeneration.ae_at_endpoint_of_product_ae hd Q lam h0.le h1 P K
      hK.1 hK.2.1 hK.2.2.1 _ ht _ hK.1.2


/-- Bounded history-level conditional expectations are integrable. -/
theorem c10_clean_history_level_conditional_integrable {d : ℕ} (hd : 2 ≤ d)
    {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ)
    (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ)
    (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K) (m : ℕ)
    (A : Regeneration.CoupledSample d → ℝ) (hA : Measurable A)
    (F : ℝ × Regeneration.CoupledSample d → ℝ) (hF : Measurable F)
    (hbF : Regeneration.BoundedRealTest F) :
    let Δ := Regeneration.Renewal.regenDelta lam
    Integrable (fun q : FieldPair d × Regeneration.CoupledSample d =>
      ∫ w, F (A q.2, w) ∂K (q.2.1 ((m : ℝ≥0) * Δ), q.1))
      (Regeneration.annealedCoupledLaw Q.measure K) := by
  dsimp only
  let Δ := Regeneration.Renewal.regenDelta lam
  let μ := Regeneration.annealedCoupledLaw Q.measure K
  haveI : IsProbabilityMeasure μ :=
    Regeneration.annealedCoupledLaw_isProbabilityMeasure Q.measure K hK.1
  let E : FieldPair d × Regeneration.CoupledSample d → Vec d × FieldPair d :=
    fun q => (q.2.1 ((m : ℝ≥0) * Δ), q.1)
  have hE : Measurable E := ((continuous_eval_const _).measurable.comp
    measurable_snd.fst).prodMk measurable_fst
  let L : Kernel (FieldPair d × Regeneration.CoupledSample d) (Regeneration.CoupledSample d) :=
    (EinsteinRelation.Probability.probabilityPart K).comap E hE
  let J : (FieldPair d × Regeneration.CoupledSample d) × Regeneration.CoupledSample d → ℝ :=
    fun q => F (A q.1.2, q.2)
  have hJ : Measurable J := hF.comp (((hA.comp measurable_fst.snd)).prodMk measurable_snd)
  let G : FieldPair d × Regeneration.CoupledSample d → ℝ := fun q => ∫ w, J (q, w) ∂L q
  have hG : Measurable G := (hJ.stronglyMeasurable.integral_kernel_prod_right' (κ := L)).measurable
  obtain ⟨C, hC⟩ := hbF
  have hC0 : 0 ≤ C := (abs_nonneg (F (0, (0, fun _ => false)))).trans (hC _)
  have hbG : ∀ q, ‖G q‖ ≤ C := by
    intro q
    dsimp only [G, L, E, Kernel.comap_apply]
    by_cases hp : K (q.2.1 ((m : ℝ≥0) * Δ), q.1) Set.univ = 1
    · haveI : IsProbabilityMeasure (K (q.2.1 ((m : ℝ≥0) * Δ), q.1)) := ⟨hp⟩
      rw [EinsteinRelation.Probability.probabilityPart_eq_of_isProbabilityMeasure]
      simpa using norm_integral_le_of_norm_le_const
        (μ := K (q.2.1 ((m : ℝ≥0) * Δ), q.1)) (f := fun w => J (q, w)) (C := C)
        (Filter.Eventually.of_forall fun w => by
          simpa only [Real.norm_eq_abs, J] using hC (A q.2, w))
    · simp only [EinsteinRelation.Probability.probabilityPart_apply, if_neg hp,
        integral_zero_measure, norm_zero]
      exact hC0
  have hi : Integrable G μ := Integrable.of_bound hG.aestronglyMeasurable C
    (Filter.Eventually.of_forall hbG)
  apply hi.congr
  filter_upwards [c10_clean_grid_endpoint_probability hd Q lam h0 h1 l δ P K hK m] with q hq
  haveI := hq
  simp only [G, J, L, E, Kernel.comap_apply, Δ,
    EinsteinRelation.Probability.probabilityPart_eq_of_isProbabilityMeasure]


/-- The environment coordinate of the annealed law has law `Q.measure`. -/
theorem c10_clean_annealed_environment_map {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (K : Regeneration.CoupledQuenchedLaws d)
    (hK : Regeneration.HasProbabilityLaws Q.measure K) :
    (Regeneration.annealedCoupledLaw Q.measure K).map Prod.fst = Q.measure := by
  ext s hs
  rw [Measure.map_apply measurable_fst hs]
  rw [show (Prod.fst : FieldPair d × Regeneration.CoupledSample d → FieldPair d) ⁻¹' s =
    s ×ˢ Set.univ by ext x; simp]
  change (Q.measure.compProd (EinsteinRelation.Probability.probabilityPart
    (Regeneration.originCoupledLaw K))) (s ×ˢ Set.univ) = Q.measure s
  rw [Measure.compProd_apply_prod hs MeasurableSet.univ]
  calc
    _ = ∫⁻ _ω in s, (1 : ℝ≥0∞) ∂Q.measure := by
      apply setLIntegral_congr_fun_ae hs
      filter_upwards [hK.1,
        EinsteinRelation.Probability.probabilityPart_ae_eq Q.measure
          (Regeneration.originCoupledLaw K) hK.1] with ω hω heq _hωs
      rw [heq]
      exact hω.measure_univ
    _ = _ := by simp only [lintegral_one, Measure.restrict_apply_univ]

/-- The actual grid endpoint retains the prescribed path marginal. -/
theorem c10_clean_grid_endpoint_path_marginal {d : ℕ} (hd : 2 ≤ d)
    {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ)
    (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ)
    (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K) (m : ℕ) :
    ∀ᵐ q ∂Regeneration.annealedCoupledLaw Q.measure K,
      (K (q.2.1 ((m : ℝ≥0) * Regeneration.Renewal.regenDelta lam), q.1)).map Prod.fst =
        P (q.2.1 ((m : ℝ≥0) * Regeneration.Renewal.regenDelta lam), q.1) := by
  by_cases hm : m = 0
  · subst m
    have hs := Regeneration.ae_origin_start_of_isGMPReducedKernel hd Q lam h0.le h1
      P K hK.1 hK.2.1 hK.2.2.1
    have hqmp : Measure.QuasiMeasurePreserving
        (Prod.fst : FieldPair d × Regeneration.CoupledSample d → FieldPair d)
        (Regeneration.annealedCoupledLaw Q.measure K) Q.measure := by
      refine ⟨measurable_fst, ?_⟩
      rw [c10_clean_annealed_environment_map Q K hK.1]
    have hpq := hqmp.ae hK.2.1.1
    filter_upwards [hs, hpq] with q hq hp
    simpa only [Nat.cast_zero, zero_mul, hq] using hp
  · have hΔ : 0 < Regeneration.Renewal.regenDelta lam :=
      Real.toNNReal_pos.mpr (inv_pos.mpr (sq_pos_of_pos h0))
    have ht : 0 < (m : ℝ≥0) * Regeneration.Renewal.regenDelta lam :=
      mul_pos (by exact_mod_cast Nat.pos_of_ne_zero hm) hΔ
    exact Regeneration.ae_at_endpoint_of_product_ae hd Q lam h0.le h1 P K
      hK.1 hK.2.1 hK.2.2.1 _ ht _ hK.2.1.2


/-- The fixed-level bound holds at almost every actual grid endpoint, for all levels. -/
theorem c10_clean_grid_endpoint_guard_prefix_bound {d : ℕ} (hd : 2 ≤ d)
    {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ)
    (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ)
    (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K)
    (hrestart : ∀ (ω : FieldPair d)
      (hω : IsRegular (sourceReducedBound Λ₀) (zeroPotentialReducedPair ω))
      (r : EinsteinRelation.External.GantertSection7Support.GantertFixedEnvironmentRealization
        hd (sourceReducedBound Λ₀) (one_le_sourceReducedBound Q.ellipticity_parameter)
        (zeroPotentialReducedPair ω) hω lam h0.le h1)
      (x : Vec d) (a : ℝ) (N : ℕ),
      let Δ := Regeneration.Renewal.regenDelta lam
      let R := l / lam
      let i := Regeneration.Renewal.forceCoord hd
      let T : Path d → ℝ≥0∞ := fun γ => Regeneration.passageSequence Δ lam R a γ i (2 * N)
      let A : Set (Path d) := {γ | T γ < ⊤ ∧ ∀ k < N,
        Regeneration.passageSequence Δ lam R a γ i (2 * k) ≠ ⊤ ∧
          ¬Regeneration.IsGoodPassage Δ lam R a γ i (2 * k)}
      ((r.pathLaw x).restrict A).map
        (fun γ => MarkovProcess.ContinuousPath.shift ((T γ).untopD 0) γ) =
        Measure.bind ((r.pathLaw x).restrict A) (fun γ => r.pathLaw (γ ((T γ).untopD 0))))
    (ε : ℝ) (hTube : ∀ᵐ ω ∂Q.measure, ∀ x : Vec d,
      ENNReal.ofReal ε ≤ P (x, ω) {γ | ∀ s ∈ Set.Icc (0 : ℝ≥0)
        (Regeneration.Renewal.regenDelta lam), euclideanNorm (γ s - x) ≤ (l / lam) / 2})
    (m : ℕ) :
    let Δ := Regeneration.Renewal.regenDelta lam
    let R := l / lam
    let i := Regeneration.Renewal.forceCoord hd
    ∀ᵐ q ∂Regeneration.annealedCoupledLaw Q.measure K, ∀ (a : ℝ) (N : ℕ),
      let T : Path d → ℝ≥0∞ := fun γ => Regeneration.passageSequence Δ lam R a γ i (2 * N)
      let A : Set (Path d) := {γ | T γ < ⊤ ∧ ∀ k < N,
        Regeneration.passageSequence Δ lam R a γ i (2 * k) ≠ ⊤ ∧
          ¬Regeneration.IsGoodPassage Δ lam R a γ i (2 * k)}
      let B : Set (Path d) := {γ | ∀ s ∈ Set.Icc (0 : ℝ≥0) Δ,
        euclideanNorm (γ ((T γ).toNNReal + s) - γ (T γ).toNNReal) ≤ R / 2}
      ENNReal.ofReal ε * K (q.2.1 ((m : ℝ≥0) * Δ), q.1) (Prod.fst ⁻¹' A) ≤
        K (q.2.1 ((m : ℝ≥0) * Δ), q.1) (Prod.fst ⁻¹' (A ∩ B)) := by
  dsimp only
  have hqmp : Measure.QuasiMeasurePreserving
      (Prod.fst : FieldPair d × Regeneration.CoupledSample d → FieldPair d)
      (Regeneration.annealedCoupledLaw Q.measure K) Q.measure := by
    refine ⟨measurable_fst, ?_⟩
    rw [c10_clean_annealed_environment_map Q K hK.1]
  have he := hqmp.ae (hK.2.2.1.and hTube)
  have hm := c10_clean_grid_endpoint_path_marginal hd Q lam h0 h1 l δ P K hK m
  filter_upwards [he, hm] with q henv hpath
  obtain ⟨⟨hω, r, hr⟩, htube⟩ := henv
  have htube' : ∀ y, ENNReal.ofReal ε ≤ r.pathLaw y
      {γ | ∀ s ∈ Set.Icc (0 : ℝ≥0) (Regeneration.Renewal.regenDelta lam),
        euclideanNorm (γ s - y) ≤ (l / lam) / 2} := by
    intro y
    rw [← hr y]
    exact htube y
  intro a N
  exact c10_clean_coupled_guard_prefix_tube_bound hd (zeroPotentialReducedPair q.1) lam
    (sourceReducedBound Λ₀) (one_le_sourceReducedBound Q.ellipticity_parameter) hω h0.le h1 r
    (K (q.2.1 ((m : ℝ≥0) * Regeneration.Renewal.regenDelta lam), q.1)) _
    (hpath.trans (hr _)) _ _ a _ N _ (hrestart q.1 hω r _ a N) htube'

/-- The endpoint prefix estimate in real-valued probabilities. -/
theorem c10_clean_grid_endpoint_guard_prefix_real_bound {d : ℕ} (hd : 2 ≤ d)
    {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ)
    (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ)
    (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K)
    (hrestart : ∀ (ω : FieldPair d)
      (hω : IsRegular (sourceReducedBound Λ₀) (zeroPotentialReducedPair ω))
      (r : EinsteinRelation.External.GantertSection7Support.GantertFixedEnvironmentRealization
        hd (sourceReducedBound Λ₀) (one_le_sourceReducedBound Q.ellipticity_parameter)
        (zeroPotentialReducedPair ω) hω lam h0.le h1)
      (x : Vec d) (a : ℝ) (N : ℕ),
      let Δ := Regeneration.Renewal.regenDelta lam
      let R := l / lam
      let i := Regeneration.Renewal.forceCoord hd
      let T : Path d → ℝ≥0∞ := fun γ => Regeneration.passageSequence Δ lam R a γ i (2 * N)
      let A : Set (Path d) := {γ | T γ < ⊤ ∧ ∀ k < N,
        Regeneration.passageSequence Δ lam R a γ i (2 * k) ≠ ⊤ ∧
          ¬Regeneration.IsGoodPassage Δ lam R a γ i (2 * k)}
      ((r.pathLaw x).restrict A).map
        (fun γ => MarkovProcess.ContinuousPath.shift ((T γ).untopD 0) γ) =
        Measure.bind ((r.pathLaw x).restrict A) (fun γ => r.pathLaw (γ ((T γ).untopD 0))))
    (ε : ℝ) (hε : 0 ≤ ε) (hTube : ∀ᵐ ω ∂Q.measure, ∀ x : Vec d,
      ENNReal.ofReal ε ≤ P (x, ω) {γ | ∀ s ∈ Set.Icc (0 : ℝ≥0)
        (Regeneration.Renewal.regenDelta lam), euclideanNorm (γ s - x) ≤ (l / lam) / 2})
    (m : ℕ) :
    let Δ := Regeneration.Renewal.regenDelta lam
    let R := l / lam
    let i := Regeneration.Renewal.forceCoord hd
    ∀ᵐ q ∂Regeneration.annealedCoupledLaw Q.measure K, ∀ (a : ℝ) (N : ℕ),
      let T : Path d → ℝ≥0∞ := fun γ => Regeneration.passageSequence Δ lam R a γ i (2 * N)
      let A : Set (Path d) := {γ | T γ < ⊤ ∧ ∀ k < N,
        Regeneration.passageSequence Δ lam R a γ i (2 * k) ≠ ⊤ ∧
          ¬Regeneration.IsGoodPassage Δ lam R a γ i (2 * k)}
      let B : Set (Path d) := {γ | ∀ s ∈ Set.Icc (0 : ℝ≥0) Δ,
        euclideanNorm (γ ((T γ).toNNReal + s) - γ (T γ).toNNReal) ≤ R / 2}
      ε * (K (q.2.1 ((m : ℝ≥0) * Δ), q.1)).real (Prod.fst ⁻¹' A) ≤
        (K (q.2.1 ((m : ℝ≥0) * Δ), q.1)).real (Prod.fst ⁻¹' (A ∩ B)) := by
  dsimp only
  filter_upwards [c10_clean_grid_endpoint_probability hd Q lam h0 h1 l δ P K hK m,
    c10_clean_grid_endpoint_guard_prefix_bound hd Q lam h0 h1 l δ P K hK hrestart ε hTube m]
    with q hprob hbound
  haveI := hprob
  intro a N
  have h := ENNReal.toReal_mono (measure_ne_top _ _) (hbound a N)
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hε, Measure.real_def] using h



/-- A uniform quenched tube bound yields the integrated stopped-tube estimate,
assuming the literal finite-passage restart equality. -/
theorem c10_clean_stopped_tube_of_uniform_quenched_tube {d : ℕ} (hd : 2 ≤ d)
    {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ)
    (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ)
    (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K)
    (hrestart : ∀ (ω : FieldPair d)
      (hω : IsRegular (sourceReducedBound Λ₀) (zeroPotentialReducedPair ω))
      (r : EinsteinRelation.External.GantertSection7Support.GantertFixedEnvironmentRealization
        hd (sourceReducedBound Λ₀) (one_le_sourceReducedBound Q.ellipticity_parameter)
        (zeroPotentialReducedPair ω) hω lam h0.le h1)
      (x : Vec d) (a : ℝ) (N : ℕ),
      let Δ := Regeneration.Renewal.regenDelta lam
      let R := l / lam
      let i := Regeneration.Renewal.forceCoord hd
      let T : Path d → ℝ≥0∞ := fun γ => Regeneration.passageSequence Δ lam R a γ i (2 * N)
      let A : Set (Path d) := {γ | T γ < ⊤ ∧ ∀ k < N,
        Regeneration.passageSequence Δ lam R a γ i (2 * k) ≠ ⊤ ∧
          ¬Regeneration.IsGoodPassage Δ lam R a γ i (2 * k)}
      ((r.pathLaw x).restrict A).map
        (fun γ => MarkovProcess.ContinuousPath.shift ((T γ).untopD 0) γ) =
        Measure.bind ((r.pathLaw x).restrict A) (fun γ => r.pathLaw (γ ((T γ).untopD 0))))
    (ε : ℝ) (hε : 0 < ε)
    (hTube : ∀ᵐ ω ∂Q.measure, ∀ x : Vec d, ENNReal.ofReal ε ≤ P (x, ω)
      {γ | ∀ s ∈ Set.Icc (0 : ℝ≥0) (Regeneration.Renewal.regenDelta lam),
        euclideanNorm (γ s - x) ≤ (l / lam) / 2}) : let Δ := Regeneration.Renewal.regenDelta lam; let R := l / lam; let i := Regeneration.Renewal.forceCoord hd; ∀ (m : ℕ) (A : Regeneration.CoupledSample d → ℝ), @Measurable (Regeneration.CoupledSample d) ℝ (Regeneration.finiteHistorySigma Δ m) inferInstance A → ∀ N : ℕ, let μ := Regeneration.annealedCoupledLaw Q.measure K; let E := c10CleanCouplingScopeEvenGuardFailure Δ lam R A m i Set.univ N ∩ {q | c10CleanCouplingScopePassage Δ lam R A m i (2 * N) q.2 ≠ ⊤}; let Tube := {q : FieldPair d × Regeneration.CoupledSample d | ∀ s ∈ Set.Icc (0 : ℝ≥0) Δ, euclideanNorm ((Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)).1 ((c10CleanCouplingScopePassage Δ lam R A m i (2 * N) q.2).toNNReal + s) - (Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)).1 (c10CleanCouplingScopePassage Δ lam R A m i (2 * N) q.2).toNNReal) ≤ R / 2}; ε * μ.real E ≤ μ.real (E ∩ Tube) := by
  classical
  dsimp only
  intro m A hA N
  let Δ := Regeneration.Renewal.regenDelta lam
  let R := l / lam
  let i := Regeneration.Renewal.forceCoord hd
  let μ := Regeneration.annealedCoupledLaw Q.measure K
  let V : Set (ℝ × Path d) := {p |
    Regeneration.passageSequence Δ lam R p.1 p.2 i (2 * N) < ⊤ ∧
    ∀ k < N, Regeneration.passageSequence Δ lam R p.1 p.2 i (2 * k) ≠ ⊤ ∧
      ¬Regeneration.IsGoodPassage Δ lam R p.1 p.2 i (2 * k)}
  let B : Set (ℝ × Path d) := {p | ∀ s ∈ Set.Icc (0 : ℝ≥0) Δ,
    euclideanNorm (p.2 ((Regeneration.passageSequence Δ lam R p.1 p.2 i
      (2 * N)).toNNReal + s) - p.2 (Regeneration.passageSequence Δ lam R
      p.1 p.2 i (2 * N)).toNNReal) ≤ R / 2}
  have hV : MeasurableSet V := c10_clean_joint_guard_prefix_measurable Δ lam R i N
  have hB : MeasurableSet B := c10_clean_joint_passage_tube_measurable Δ lam R i N
  let S : Set (ℝ × Regeneration.CoupledSample d) :=
    (fun p => (p.1, p.2.1)) ⁻¹' V
  let U : Set (ℝ × Regeneration.CoupledSample d) :=
    (fun p => (p.1, p.2.1)) ⁻¹' (V ∩ B)
  have hS : MeasurableSet S := hV.preimage (measurable_fst.prodMk measurable_snd.fst)
  have hU : MeasurableSet U := (hV.inter hB).preimage (measurable_fst.prodMk measurable_snd.fst)
  let F : ℝ × Regeneration.CoupledSample d → ℝ := S.indicator (fun _ => 1)
  let G : ℝ × Regeneration.CoupledSample d → ℝ := U.indicator (fun _ => 1)
  have hF : Measurable F := measurable_const.indicator hS
  have hG : Measurable G := measurable_const.indicator hU
  have hbF : Regeneration.BoundedRealTest F := by
    refine ⟨1, fun p => ?_⟩
    by_cases hp : p ∈ S <;> simp [F, hp]
  have hbG : Regeneration.BoundedRealTest G := by
    refine ⟨1, fun p => ?_⟩
    by_cases hp : p ∈ U <;> simp [G, hp]
  have hAg : Measurable A := hA.mono (EinsteinRelation.Probability.finiteHistorySigma_le Δ m) le_rfl
  have hiF := c10_clean_history_level_conditional_integrable hd Q lam h0 h1 l δ P K hK m A hAg F hF hbF
  have hiG := c10_clean_history_level_conditional_integrable hd Q lam h0 h1 l δ P K hK m A hAg G hG hbG
  have hrF := c10_clean_history_level_restart hd Q lam h0 h1 l δ P K hK m A hA F hF hbF
  have hrG := c10_clean_history_level_restart hd Q lam h0 h1 l δ P K hK m A hA G hG hbG
  let E : Set (FieldPair d × Regeneration.CoupledSample d) :=
    c10CleanCouplingScopeEvenGuardFailure Δ lam R A m i Set.univ N ∩
      {q | c10CleanCouplingScopePassage Δ lam R A m i (2 * N) q.2 ≠ ⊤}
  let Tube : Set (FieldPair d × Regeneration.CoupledSample d) := {q |
    ∀ s ∈ Set.Icc (0 : ℝ≥0) Δ,
      euclideanNorm ((Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)).1
        ((c10CleanCouplingScopePassage Δ lam R A m i (2 * N) q.2).toNNReal + s) -
        (Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)).1
          (c10CleanCouplingScopePassage Δ lam R A m i (2 * N) q.2).toNNReal) ≤ R / 2}
  let H : FieldPair d × Regeneration.CoupledSample d → ℝ × Path d := fun q =>
    (A q.2, (Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)).1)
  have hH : Measurable H := (hAg.comp measurable_snd).prodMk
    (((Regeneration.measurable_sampleTimeShift Δ).comp
      (measurable_const.prodMk measurable_snd)).fst)
  have hE : E = H ⁻¹' V := c10_clean_guard_prefix_event_eq Δ lam R A m i N
  have hTube' : Tube = H ⁻¹' B := by
    ext q
    rfl
  have hEm : MeasurableSet E := by
    rw [hE]
    exact hV.preimage hH
  have hETm : MeasurableSet (E ∩ Tube) := by
    rw [hE, hTube']
    exact (hV.inter hB).preimage hH
  have houterF : (∫ q, F (A q.2, Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)) ∂μ) = μ.real E := by
    rw [← integral_indicator_one hEm]
    apply integral_congr_ae
    filter_upwards [] with q
    by_cases hq : H q ∈ V <;> simp [F, S, hE, H, hq] at *
  have houterG : (∫ q, G (A q.2, Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)) ∂μ) = μ.real (E ∩ Tube) := by
    rw [← integral_indicator_one hETm]
    apply integral_congr_ae
    filter_upwards [] with q
    simp only [G, U, hE, hTube', H, Set.indicator_apply,
      Set.mem_preimage, Set.mem_inter_iff, Pi.one_apply]
  have hbound : ∀ᵐ q ∂μ,
      ε * (∫ w, F (A q.2, w) ∂K (q.2.1 ((m : ℝ≥0) * Δ), q.1)) ≤
        ∫ w, G (A q.2, w) ∂K (q.2.1 ((m : ℝ≥0) * Δ), q.1) := by
    filter_upwards [c10_clean_grid_endpoint_guard_prefix_real_bound hd Q lam h0 h1 l δ P K hK hrestart ε hε.le hTube m] with q hq
    let Vq : Set (Regeneration.CoupledSample d) := {w | (A q.2, w.1) ∈ V}
    let Uq : Set (Regeneration.CoupledSample d) := {w | (A q.2, w.1) ∈ V ∩ B}
    have hVq : MeasurableSet Vq := hV.preimage (measurable_const.prodMk measurable_fst)
    have hUq : MeasurableSet Uq := (hV.inter hB).preimage (measurable_const.prodMk measurable_fst)
    have hif : (∫ w, F (A q.2, w) ∂K (q.2.1 ((m : ℝ≥0) * Δ), q.1)) =
        (K (q.2.1 ((m : ℝ≥0) * Δ), q.1)).real Vq := by
      rw [← integral_indicator_one hVq]
      apply integral_congr_ae
      filter_upwards [] with w
      simp only [F, S, Vq, Set.indicator_apply, Set.mem_preimage, Set.mem_setOf_eq, Pi.one_apply]
    have hig : (∫ w, G (A q.2, w) ∂K (q.2.1 ((m : ℝ≥0) * Δ), q.1)) =
        (K (q.2.1 ((m : ℝ≥0) * Δ), q.1)).real Uq := by
      rw [← integral_indicator_one hUq]
      apply integral_congr_ae
      filter_upwards [] with w
      simp only [G, U, Uq, Set.indicator_apply, Set.mem_preimage,
        Set.mem_setOf_eq, Set.mem_inter_iff, Pi.one_apply]
    rw [hif, hig]
    simpa [Vq, Uq, V, B, Δ, R, i, Set.preimage_inter, Set.ofPred_and] using hq (A q.2) N
  have hm := integral_mono_ae (hiF.const_mul ε) hiG hbound
  rw [integral_const_mul, ← hrF, ← hrG, houterF, houterG] at hm
  exact hm


/-- The uniform quenched tube bound yields the actual even guard estimate. -/
theorem c10_clean_actual_guard_of_uniform_quenched_tube {d : ℕ} (hd : 2 ≤ d)
    {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ)
    (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ)
    (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K)
    (hrestart : ∀ (ω : FieldPair d)
      (hω : IsRegular (sourceReducedBound Λ₀) (zeroPotentialReducedPair ω))
      (r : EinsteinRelation.External.GantertSection7Support.GantertFixedEnvironmentRealization
        hd (sourceReducedBound Λ₀) (one_le_sourceReducedBound Q.ellipticity_parameter)
        (zeroPotentialReducedPair ω) hω lam h0.le h1)
      (x : Vec d) (a : ℝ) (N : ℕ),
      let Δ := Regeneration.Renewal.regenDelta lam
      let R := l / lam
      let i := Regeneration.Renewal.forceCoord hd
      let T : Path d → ℝ≥0∞ := fun γ => Regeneration.passageSequence Δ lam R a γ i (2 * N)
      let A : Set (Path d) := {γ | T γ < ⊤ ∧ ∀ k < N,
        Regeneration.passageSequence Δ lam R a γ i (2 * k) ≠ ⊤ ∧
          ¬Regeneration.IsGoodPassage Δ lam R a γ i (2 * k)}
      ((r.pathLaw x).restrict A).map
        (fun γ => MarkovProcess.ContinuousPath.shift ((T γ).untopD 0) γ) =
        Measure.bind ((r.pathLaw x).restrict A) (fun γ => r.pathLaw (γ ((T γ).untopD 0))))
 (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (hTube : ∀ᵐ ω ∂Q.measure, ∀ x : Vec d, ENNReal.ofReal ε ≤ P (x, ω) {γ | ∀ s ∈ Set.Icc (0 : ℝ≥0) (Regeneration.Renewal.regenDelta lam), euclideanNorm (γ s - x) ≤ (l / lam) / 2}) : let Δ := Regeneration.Renewal.regenDelta lam; let R := l / lam; let i := Regeneration.Renewal.forceCoord hd; ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ∀ (m : ℕ) (A : Regeneration.CoupledSample d → ℝ), @Measurable (Regeneration.CoupledSample d) ℝ (Regeneration.finiteHistorySigma Δ m) inferInstance A → ∀ N : ℕ, let E := c10CleanCouplingScopeEvenGuardFailure Δ lam R A m i Set.univ N ∩ {q | c10CleanCouplingScopePassage Δ lam R A m i (2 * N) q.2 ≠ ⊤}; ε * (Regeneration.annealedCoupledLaw Q.measure K).real E ≤ (Regeneration.annealedCoupledLaw Q.measure K).real (E ∩ {q | q.2 ∈ c10CleanCouplingScopeEvenGuard Δ lam R A m i N}) := by
  refine ⟨ε, hε, hε1, ?_⟩
  intro m A hA N
  let μ := Regeneration.annealedCoupledLaw Q.measure K
  let : IsProbabilityMeasure μ :=
    Regeneration.annealedCoupledLaw_isProbabilityMeasure Q.measure K hK.1
  have hΔ : 0 < Regeneration.Renewal.regenDelta lam :=
    Real.toNNReal_pos.mpr (inv_pos.mpr (sq_pos_of_pos h0))
  exact c10_clean_coupling_scope_guard_estimate_of_tube_estimate μ
    (Regeneration.Renewal.regenDelta lam) hΔ lam (l / lam) ε A m
    (Regeneration.Renewal.forceCoord hd) N
    (c10_clean_stopped_tube_of_uniform_quenched_tube hd Q lam h0 h1 l δ
      P K hK hrestart ε hε hTube m A hA N)


end EinsteinFull.Blueprint
