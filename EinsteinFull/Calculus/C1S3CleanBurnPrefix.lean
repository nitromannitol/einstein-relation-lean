import EinsteinFull.Calculus.C1S3CleanBurnEvent
import EinsteinRelation.Regeneration.TrialPrefix
import EinsteinRelation.Regeneration.Chronology
import EinsteinRelation.Probability.StoppedHistory

open MeasureTheory
open scoped NNReal ENNReal

noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation EinsteinRelation.Regeneration

private theorem c1_s3_burn_trial_start_le_failure {d : ℕ}
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (R : ℝ) (z : Regeneration.CoupledSample d)
    (i : Fin d) (S : ℝ≥0∞) : S ≤ Regeneration.trialFailureTime Δ R z i S := by
  apply le_trans _ (Regeneration.le_roundUp Δ hΔ _)
  unfold Regeneration.trialDownwardTime
  split_ifs with hS
  · exact le_top
  · exact le_add_of_nonneg_right zero_le

/-- Each literal successor advances by at least two grid periods, including
branches whose selected time is infinite. -/
private theorem c1_s3_burn_trial_start_add_two_step_le_succ {d : ℕ}
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (lam R : ℝ) (hlam : 0 < lam) (hR : 0 < R)
    (z : Regeneration.CoupledSample d) (i : Fin d) (n : ℕ) :
    Regeneration.trialStartSequence Δ lam R z i n + 2 * (Δ : ℝ≥0∞) ≤
      Regeneration.trialStartSequence Δ lam R z i (n + 1) := by
  let F := Regeneration.trialFailureTime Δ R z i
    (Regeneration.trialStartSequence Δ lam R z i n)
  by_cases hF : F = ⊤
  · rw [Regeneration.trialStartSequence, ite_eq_left hF]
    exact le_top
  · have hmax := Regeneration.displacement_le_coordinateMaximum z.1 i
      F.toNNReal F.toNNReal le_rfl
    have hpos : 0 < lam * (Regeneration.coordinateMaximum z.1 i F.toNNReal -
        (z.1 F.toNNReal i - z.1 0 i) + R) / lam := by
      rw [mul_div_cancel_left₀ _ hlam.ne']
      linarith
    have hstep := Regeneration.step_le_firstSuccessfulCandidate Δ hΔ lam R _
      hlam hR hpos (Regeneration.sampleTimeShift Δ z F.toNNReal) i
    rw [Regeneration.trialStartSequence, ite_eq_right hF, two_mul, ← add_assoc]
    exact add_le_add
      (add_le_add (c1_s3_burn_trial_start_le_failure Δ hΔ R z i _) hstep) le_rfl

private theorem c1_s3_burn_trial_start_monotone {d : ℕ}
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (lam R : ℝ) (hlam : 0 < lam) (hR : 0 < R)
    (z : Regeneration.CoupledSample d) (i : Fin d) :
    Monotone (Regeneration.trialStartSequence Δ lam R z i) := by
  apply monotone_nat_of_le_succ
  intro n
  exact (le_add_of_nonneg_right zero_le).trans
    (c1_s3_burn_trial_start_add_two_step_le_succ Δ hΔ lam R hlam hR z i n)

private theorem c1_s3_mem_trial_burn_prebridge_of_prefix {d : ℕ}
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (lam R : ℝ) (hlam : 0 < lam) (hR : 0 < R)
    (m : ℕ) (i : Fin d) (J N k : ℕ) (z z' : Regeneration.CoupledSample d)
    (hpre : ∀ t ∈ Set.Icc (0 : ℝ≥0) (((m + k : ℕ) : ℝ≥0) * Δ), z.1 t = z'.1 t)
    (hbits : ∀ j < m + k, z.2 j = z'.2 j)
    (hz : z ∈ c1S3TrialBurnPrebridge Δ lam R m i J N k) :
    z' ∈ c1S3TrialBurnPrebridge Δ lam R m i J N k := by
  let w := Regeneration.forceSampleBit k
    (Regeneration.sampleTimeShift Δ z ((m : ℝ≥0) * Δ))
  let w' := Regeneration.forceSampleBit k
    (Regeneration.sampleTimeShift Δ z' ((m : ℝ≥0) * Δ))
  have hp : ∀ t ∈ Set.Icc (0 : ℝ≥0) ((k : ℝ≥0) * Δ), w.1 t = w'.1 t := by
    intro t ht
    apply hpre ((m : ℝ≥0) * Δ + t)
    refine ⟨zero_le, ?_⟩
    rw [Nat.cast_add, add_mul]
    exact add_le_add le_rfl ht.2
  have hb : ∀ j : ℕ, (j : ℝ≥0) * Δ ≤ (k : ℝ≥0) * Δ → w.2 j = w'.2 j := by
    intro j hj
    have hjk : j ≤ k := by exact_mod_cast (mul_le_mul_iff_left₀ hΔ).mp hj
    by_cases heq : j = k
    · subst j
      simp only [w, w', Regeneration.forceSampleBit, Function.update_self]
    · have hjlt : j < k := lt_of_le_of_ne hjk heq
      dsimp only [w, w', Regeneration.forceSampleBit]
      rw [Function.update_of_ne heq, Function.update_of_ne heq]
      change z.2 (Regeneration.gridIndex Δ ((m : ℝ≥0) * Δ) + j) =
        z'.2 (Regeneration.gridIndex Δ ((m : ℝ≥0) * Δ) + j)
      rw [Regeneration.gridIndex_mul Δ hΔ]
      exact hbits _ (Nat.add_lt_add_left hjlt m)
  change Regeneration.trialStartSequence Δ lam R w i (J + N) = _ ∧
    Regeneration.trialStartSequence Δ lam R w i J ≠ ⊤ ∧ _ at hz
  have htime : (((k + 1 : ℕ) : ℝ≥0) * Δ) = (k : ℝ≥0) * Δ + Δ := by
    rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul]
  have hSJ : Regeneration.trialStartSequence Δ lam R w i J ≤
      ((((k + 1 : ℕ) : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞) := by
    rw [← hz.1]
    exact c1_s3_burn_trial_start_monotone Δ hΔ lam R hlam hR w i (Nat.le_add_right J N)
  have hn := Regeneration.trialStartSequence_eq_of_prefix Δ hΔ lam R hR
    w w' i (J + N) ((k : ℝ≥0) * Δ) hp hb (by rw [hz.1, htime])
  have hJ := Regeneration.trialStartSequence_eq_of_prefix Δ hΔ lam R hR
    w w' i J ((k : ℝ≥0) * Δ) hp hb (by rwa [← htime])
  have hJtime : (Regeneration.trialStartSequence Δ lam R w i J).toNNReal - Δ ≤
      (k : ℝ≥0) * Δ := by
    apply (tsub_le_iff_right).mpr
    rw [← htime]
    exact ENNReal.coe_le_coe.mp (by rwa [ENNReal.coe_toNNReal hz.2.1])
  have heval : z.1 ((m : ℝ≥0) * Δ +
      ((Regeneration.trialStartSequence Δ lam R w i J).toNNReal - Δ)) =
      z'.1 ((m : ℝ≥0) * Δ +
        ((Regeneration.trialStartSequence Δ lam R w i J).toNNReal - Δ)) := by
    apply hpre _ ⟨zero_le, ?_⟩
    rw [Nat.cast_add, add_mul]
    exact add_le_add le_rfl hJtime
  have hm : (m : ℝ≥0) * Δ ≤ ((m + k : ℕ) : ℝ≥0) * Δ := by
    rw [Nat.cast_add, add_mul]
    exact le_add_of_nonneg_right zero_le
  have hmax : Regeneration.coordinateMaximum z.1 i ((m : ℝ≥0) * Δ) =
      Regeneration.coordinateMaximum z'.1 i ((m : ℝ≥0) * Δ) := by
    unfold Regeneration.coordinateMaximum
    congr 1
    apply Set.image_congr
    intro t ht
    rw [hpre t ⟨ht.1, ht.2.trans hm⟩, hpre 0 ⟨le_rfl, zero_le⟩]
  change Regeneration.trialStartSequence Δ lam R w' i (J + N) = _ ∧
    Regeneration.trialStartSequence Δ lam R w' i J ≠ ⊤ ∧ _
  rw [← hn, ← hJ, ← hmax, ← heval, ← hpre 0 ⟨le_rfl, zero_le⟩]
  exact hz

/-- The exact Burn-selected prefix is measurable before the absolute coin
`m+k`; the stopped extension uses only path times through `(m+k)Δ`. -/
theorem c1_s3_measurableSet_trial_burn_prebridge_finiteHistory {d : ℕ}
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (lam R : ℝ) (hlam : 0 < lam) (hR : 0 < R)
    (m : ℕ) (i : Fin d) (J N k : ℕ) :
    @MeasurableSet (Regeneration.CoupledSample d)
      (Regeneration.finiteHistorySigma Δ (m + k))
      (c1S3TrialBurnPrebridge Δ lam R m i J N k) := by
  have heq : c1S3TrialBurnPrebridge Δ lam R m i J N k =
      Probability.stoppedHistorySample Δ (m + k) ⁻¹'
        c1S3TrialBurnPrebridge Δ lam R m i J N k := by
    ext z
    have hp : ∀ t ∈ Set.Icc (0 : ℝ≥0) (((m + k : ℕ) : ℝ≥0) * Δ),
        z.1 t = (Probability.stoppedHistorySample Δ (m + k) z).1 t :=
      fun t ht => (Probability.stoppedHistorySample_path Δ (m + k) z t ht.2).symm
    have hb : ∀ j < m + k,
        z.2 j = (Probability.stoppedHistorySample Δ (m + k) z).2 j :=
      fun j hj => (Probability.stoppedHistorySample_bit Δ (m + k) z j hj).symm
    exact ⟨c1_s3_mem_trial_burn_prebridge_of_prefix
      Δ hΔ lam R hlam hR m i J N k z _ hp hb,
      c1_s3_mem_trial_burn_prebridge_of_prefix
        Δ hΔ lam R hlam hR m i J N k _ z
        (fun t ht => (hp t ht).symm) (fun j hj => (hb j hj).symm)⟩
  rw [heq]
  exact Probability.measurable_stoppedHistorySample Δ (m + k)
    (c1_s3_measurableSet_trial_burn_prebridge Δ lam R m i J N k)


end EinsteinFull.Blueprint
