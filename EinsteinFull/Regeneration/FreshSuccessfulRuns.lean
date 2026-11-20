import EinsteinRelation.Regeneration.FreshEventMass
import EinsteinRelation.Probability.FiniteHistoryFiltration
import EinsteinFull.Blueprint.Foundation.Proofs.SbxS7FiniteTrialSupport

/-!
# Fresh successful runs

Finite consecutive runs of successful bits have their Bernoulli mass even
when conditioned on an arbitrary event in the preceding exact history.
-/

open MeasureTheory EinsteinRelation EinsteinRelation.Regeneration
open scoped NNReal ENNReal

namespace EinsteinFull.Regeneration

/-- The successful bits in a consecutive interval of the coupling grid. -/
def successfulRun {d : ℕ} (n N : ℕ) : Set (CoupledSample d) :=
  {z | ∀ k < N, z.2 (n + k) = true}

/-- A successful run is observed when its final bit has been read. -/
theorem measurableSet_successfulRun_history {d : ℕ} (Δ : ℝ≥0) (n N : ℕ) :
    MeasurableSet[finiteHistorySigma Δ (n + N)] (successfulRun (d := d) n N) := by
  change MeasurableSet[finiteHistorySigma Δ (n + N)]
    {z : CoupledSample d | ∀ k < N, z.2 (n + k) = true}
  simp only [Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro k
  apply MeasurableSet.iInter
  intro hk
  have hbit : @Measurable (CoupledSample d) Bool (finiteHistorySigma Δ (n + N))
      inferInstance (fun z => z.2 (n + k)) := by
    have hglobal : Measurable (fun z : CoupledSample d => z.2 (n + k)) :=
      (measurable_pi_apply (n + k)).comp measurable_snd
    have heq : (fun z : CoupledSample d => z.2 (n + k)) =
        (fun z => z.2 (n + k)) ∘ Probability.stoppedHistorySample Δ (n + N) := by
      funext z
      exact (Probability.stoppedHistorySample_bit Δ (n + N) z (n + k) (by omega)).symm
    rw [heq]
    exact hglobal.comp (Probability.measurable_stoppedHistorySample Δ (n + N))
  exact hbit (measurableSet_singleton true)

/-- A run of `N` fresh successes has conditional mass `δ ^ N` given the exact past. -/
theorem measure_annealed_successful_run {d : ℕ} (Q : Measure (FieldPair d))
    [IsProbabilityMeasure Q] (K : CoupledQuenchedLaws d) (hK : HasProbabilityLaws Q K)
    (Δ : ℝ≥0) (δ : ℝ) (hδ : 0 ≤ δ) (hFresh : HasFreshBits Q Δ δ K)
    (n N : ℕ) (A : Set (CoupledSample d))
    (hA : MeasurableSet[finiteHistorySigma Δ n] A) :
    annealedCoupledLaw Q K {q | q.2 ∈ A ∧ q.2 ∈ successfulRun n N} =
      ENNReal.ofReal δ ^ N * annealedCoupledLaw Q K {q | q.2 ∈ A} := by
  induction N with
  | zero => simp [successfulRun]
  | succ N ih =>
    have hhistory : MeasurableSet[finiteHistorySigma Δ (n + N)] (A ∩ successfulRun n N) :=
      (finiteHistorySigma_mono Δ (Nat.le_add_right n N) A hA).inter
        (measurableSet_successfulRun_history Δ n N)
    have hfresh := measure_annealed_fresh_bit Q K hK Δ δ hδ hFresh (n + N)
      (A ∩ successfulRun n N) hhistory
    have hevent : {q : FieldPair d × CoupledSample d | q.2 ∈ A ∧
        q.2 ∈ successfulRun n (N + 1)} =
        {q : FieldPair d × CoupledSample d | q.2 ∈ A ∩ successfulRun n N ∧
          q.2.2 (n + N) = true} := by
      ext q
      simp only [Set.mem_ofPred_eq, successfulRun, Set.mem_inter_iff]
      constructor
      · rintro ⟨ha, hh⟩
        exact ⟨⟨ha, fun k hk => hh k (by omega)⟩, hh N (by omega)⟩
      · rintro ⟨⟨ha, hh⟩, hl⟩
        refine ⟨ha, fun k hk => ?_⟩
        by_cases hk' : k < N
        · exact hh k hk'
        · have : k = N := by omega
          simpa [this] using hl
    rw [hevent, hfresh]
    change ENNReal.ofReal δ * (annealedCoupledLaw Q K)
      {q | q.2 ∈ A ∧ q.2 ∈ successfulRun n N} = _
    rw [ih, pow_succ]
    ac_rfl

/-- None of the first `m` disjoint blocks is a successful run. -/
def failedSuccessfulBlocks {d : ℕ} (M N m : ℕ) : Set (CoupledSample d) :=
  {z | ∀ j < m, z ∉ successfulRun (M + j * N) N}

/-- Completed failed blocks belong to the exact history of the next block. -/
theorem measurableSet_failedSuccessfulBlocks_history {d : ℕ} (Δ : ℝ≥0) (M N m : ℕ) :
    MeasurableSet[finiteHistorySigma Δ (M + m * N)]
      (failedSuccessfulBlocks (d := d) M N m) := by
  change MeasurableSet[finiteHistorySigma Δ (M + m * N)]
    {z : CoupledSample d | ∀ j < m, z ∉ successfulRun (M + j * N) N}
  simp only [Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro j
  apply MeasurableSet.iInter
  intro hj
  apply MeasurableSet.compl
  apply finiteHistorySigma_mono Δ (show M + j * N + N ≤ M + m * N by nlinarith)
  exact measurableSet_successfulRun_history Δ (M + j * N) N

/-- A positive chance of each fresh run gives a geometric bound on failed blocks. -/
theorem measure_failedSuccessfulBlocks_le {d : ℕ} (Q : Measure (FieldPair d))
    [IsProbabilityMeasure Q] (K : CoupledQuenchedLaws d) (hK : HasProbabilityLaws Q K)
    (Δ : ℝ≥0) (δ : ℝ) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hFresh : HasFreshBits Q Δ δ K) (M N m : ℕ) :
    annealedCoupledLaw Q K {q | q.2 ∈ failedSuccessfulBlocks M N m} ≤
      ENNReal.ofReal (1 - δ ^ N) ^ m := by
  let μ := annealedCoupledLaw Q K
  have : IsProbabilityMeasure μ := annealedCoupledLaw_isProbabilityMeasure Q K hK
  have hp0 : 0 ≤ δ ^ N := pow_nonneg hδ _
  have hp1 : δ ^ N ≤ 1 := pow_le_one₀ hδ hδ1
  let F : ℕ → Set (FieldPair d × CoupledSample d) :=
    fun j => {q | q.2 ∈ failedSuccessfulBlocks M N j}
  have hstep (j : ℕ) : μ (F (j + 1)) ≤ ENNReal.ofReal (1 - δ ^ N) * μ (F j) := by
    let A := failedSuccessfulBlocks (d := d) M N j
    let G : Set (FieldPair d × CoupledSample d) :=
      {q | q.2 ∈ successfulRun (M + j * N) N}
    have hG : MeasurableSet G := measurable_snd
      ((Probability.finiteHistorySigma_le Δ (M + j * N + N)) _
        (measurableSet_successfulRun_history Δ (M + j * N) N))
    have hmass := measure_annealed_successful_run Q K hK Δ δ hδ hFresh
      (M + j * N) N A (measurableSet_failedSuccessfulBlocks_history Δ M N j)
    have hreal : δ ^ N * μ.real (F j) ≤ μ.real (F j ∩ G) := by
      have hh := congrArg ENNReal.toReal hmass
      rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hδ] at hh
      exact le_of_eq hh.symm
    have hf : F (j + 1) = F j \ G := by
      ext q
      simp only [F, G, failedSuccessfulBlocks, Set.mem_ofPred_eq, Set.mem_sdiff]
      constructor
      · intro h
        exact ⟨fun k hk => h k (by omega), h j (by omega)⟩
      · rintro ⟨h, hj⟩ k hk
        by_cases hk' : k < j
        · exact h k hk'
        · have : k = j := by omega
          simpa [this] using hj
    rw [hf]
    exact EinsteinFull.Blueprint.ConditionalTrialExhaustion.measure_sdiff_le_of_success_measure
      μ (F j) G hG (δ ^ N) hp1 hreal
  have h := EinsteinFull.Blueprint.ConditionalTrialExhaustion.finite_product_of_failure_step
    μ F (ENNReal.ofReal (1 - δ ^ N)) hstep m
  have hbase : μ (F 0) = 1 := by simp [F, failedSuccessfulBlocks, μ]
  simpa [hbase] using h

/-- Fresh successful runs of every finite length occur arbitrarily late almost surely. -/
theorem ae_arbitrarily_late_successful_runs {d : ℕ} (Q : Measure (FieldPair d))
    [IsProbabilityMeasure Q] (K : CoupledQuenchedLaws d) (hK : HasProbabilityLaws Q K)
    (Δ : ℝ≥0) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hFresh : HasFreshBits Q Δ δ K) :
    ∀ᵐ q ∂annealedCoupledLaw Q K, ∀ N M : ℕ,
      ∃ n ≥ M, ∀ k < N, q.2.2 (n + k) = true := by
  let μ := annealedCoupledLaw Q K
  have : IsProbabilityMeasure μ := annealedCoupledLaw_isProbabilityMeasure Q K hK
  apply ae_all_iff.mpr
  intro N
  apply ae_all_iff.mpr
  intro M
  have hnull : μ (⋂ m : ℕ, {q | q.2 ∈ failedSuccessfulBlocks M N m}) = 0 := by
    apply le_antisymm _ zero_le
    apply ge_of_tendsto' (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one
      (ENNReal.ofReal_lt_one.mpr (by have := pow_pos hδ N; linarith : 1 - δ ^ N < 1)))
    intro m
    calc
      μ (⋂ j : ℕ, {q | q.2 ∈ failedSuccessfulBlocks M N j}) ≤
          μ {q | q.2 ∈ failedSuccessfulBlocks M N m} := measure_mono (Set.iInter_subset _ m)
      _ ≤ ENNReal.ofReal (1 - δ ^ N) ^ m :=
        measure_failedSuccessfulBlocks_le Q K hK Δ δ hδ.le hδ1 hFresh M N m
  have havoid : ∀ᵐ q ∂μ, q ∉ ⋂ m : ℕ, {q | q.2 ∈ failedSuccessfulBlocks M N m} := by
    rw [ae_iff]
    simpa only [not_not, Set.ofPred_mem_eq] using hnull
  filter_upwards [havoid] with q hq
  by_contra hbad
  apply hq
  simp only [Set.mem_iInter, Set.mem_ofPred_eq, failedSuccessfulBlocks]
  intro m j hj hrun
  apply hbad
  refine ⟨M + j * N, Nat.le_add_right M _, ?_⟩
  exact hrun

end EinsteinFull.Regeneration
