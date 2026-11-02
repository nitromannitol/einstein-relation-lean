import EinsteinFull.Blueprint.Foundation.Proofs.SbxS7FiniteTrialSupport
import EinsteinFull.Blueprint.Foundation.Proofs.SbxS7CouplingScope
import EinsteinFull.Regeneration.GMPVelocityTransfer
import EinsteinFull.Regeneration.GMPSplitEndpointTransfer
import EinsteinRelation.Probability.FiniteHistoryShiftedTest
import EinsteinRelation.Regeneration.BoundedMeasurableKilledFutureVersion
import EinsteinRelation.Regeneration.AnnealedUniformEndpointRestart
import EinsteinRelation.Regeneration.FirstRegenerationEndpointFormula
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Measure.Continuity
import MarkovProcess.Path.Stopping
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
import Mathlib.Tactic.Linter

/-!
Conditional trial-exhaustion consumers for the actual rounded passage guards.
The conditional guard estimate and almost-sure finite passages are producer
obligations, not additional premises of the source-facing graph node. None of
the helpers in this module asserts that this node has been reduced or proved.
-/

open MeasureTheory
open scoped NNReal ENNReal

namespace EinsteinFull.Blueprint

open EinsteinRelation

namespace ConditionalTrialExhaustion

/-- Strictly ordered rounded grid times differ by at least one grid step. -/
theorem roundUp_add_step_le_of_lt (Δ : ℝ≥0) (hΔ : 0 < Δ)
    (s t : ℝ≥0∞) (hs : s ≠ ⊤) (ht : t ≠ ⊤)
    (hlt : Regeneration.roundUp Δ s < Regeneration.roundUp Δ t) :
    Regeneration.roundUp Δ s + (Δ : ℝ≥0∞) ≤ Regeneration.roundUp Δ t := by
  simp only [Regeneration.roundUp, ite_eq_right hs, ite_eq_right ht] at hlt ⊢
  rw [← ENNReal.coe_add]
  apply ENNReal.coe_le_coe.mpr
  have hnat : Nat.ceil (s.toReal / (Δ : ℝ)) < Nat.ceil (t.toReal / (Δ : ℝ)) := by
    exact_mod_cast (mul_lt_mul_iff_left₀ hΔ).mp (ENNReal.coe_lt_coe.mp hlt)
  calc
    (Nat.ceil (s.toReal / (Δ : ℝ)) : ℝ≥0) * Δ + Δ =
        ((Nat.ceil (s.toReal / (Δ : ℝ)) : ℝ≥0) + 1) * Δ := by ring
    _ ≤ (Nat.ceil (t.toReal / (Δ : ℝ)) : ℝ≥0) * Δ :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.succ_le_of_lt hnat) zero_le

/-- The literal chronology separates two-step passage windows by a full grid
step, even when the initial level is nonpositive. -/
theorem passage_add_step_le_two_later {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ)
    (lam R a : ℝ) (hR : 0 < R) (γ : Path d) (i : Fin d) (n : ℕ)
    (hfin : Regeneration.passageSequence Δ lam R a γ i (n + 2) ≠ ⊤) :
    Regeneration.passageSequence Δ lam R a γ i n + (Δ : ℝ≥0∞) ≤
      Regeneration.passageSequence Δ lam R a γ i (n + 2) := by
  let V := Regeneration.passageSequence Δ lam R a γ i
  have hmono : Monotone V := Regeneration.monotone_passageSequence Δ hΔ lam R a hR γ i
  have hv (j : ℕ) (hj : j ≤ n + 2) : V j ≠ ⊤ :=
    ne_top_of_le_ne_top hfin (hmono hj)
  have hu (j : ℕ) (hj : j ≤ n + 2) : Regeneration.roundUp Δ (V j) ≠ ⊤ := by
    rw [Regeneration.roundUp, ite_eq_right (hv j hj)]
    exact ENNReal.coe_ne_top
  have hlt : Regeneration.roundUp Δ (V n) < Regeneration.roundUp Δ (V (n + 1)) :=
    (Regeneration.rounded_passage_lt_next Δ lam R a hR γ i n (hu n (by omega))).trans_le
      (Regeneration.le_roundUp Δ hΔ (V (n + 1)))
  calc
    V n + (Δ : ℝ≥0∞) ≤ Regeneration.roundUp Δ (V n) + (Δ : ℝ≥0∞) :=
      add_le_add (Regeneration.le_roundUp Δ hΔ (V n)) le_rfl
    _ ≤ Regeneration.roundUp Δ (V (n + 1)) :=
      roundUp_add_step_le_of_lt Δ hΔ (V n) (V (n + 1))
        (hv n (by omega)) (hv (n + 1) (by omega)) hlt
    _ ≤ V (n + 2) :=
      (Regeneration.rounded_passage_lt_next Δ lam R a hR γ i (n + 1)
        (hu (n + 1) (by omega))).le

/-- Rounding a finite time adds at most one full grid step. -/
theorem roundUp_toNNReal_le_add (Δ : ℝ≥0) (hΔ : 0 < Δ)
    (t : ℝ≥0∞) (ht : t ≠ ⊤) :
    (Regeneration.roundUp Δ t).toNNReal ≤ t.toNNReal + Δ := by
  rw [Regeneration.roundUp, ite_eq_right ht, ENNReal.toNNReal_coe]
  apply NNReal.coe_le_coe.mp
  change (Nat.ceil (t.toReal / (Δ : ℝ)) : ℝ) * (Δ : ℝ) ≤ t.toReal + (Δ : ℝ)
  have hΔR : (0 : ℝ) < Δ := NNReal.coe_pos.mpr hΔ
  have hq : 0 ≤ t.toReal / (Δ : ℝ) := div_nonneg ENNReal.toReal_nonneg hΔR.le
  have hc : (Nat.ceil (t.toReal / (Δ : ℝ)) : ℝ) <
      t.toReal / (Δ : ℝ) + 1 := Nat.ceil_lt_add_one hq
  have hmul := mul_lt_mul_of_pos_right hc hΔR
  rw [add_mul, div_mul_cancel₀ _ hΔR.ne', one_mul] at hmul
  exact hmul.le

/-- A full Euclidean tube at the actual passage implies the literal rounded
coordinate guard, retaining every time in the closed rounding interval. -/
theorem isGoodPassage_of_euclidean_tube {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ)
    (lam R a : ℝ) (γ : Path d) (i : Fin d) (n : ℕ)
    (hfin : Regeneration.passageSequence Δ lam R a γ i n ≠ ⊤)
    (htube : ∀ s ∈ Set.Icc (0 : ℝ≥0) Δ,
      euclideanNorm (γ ((Regeneration.passageSequence Δ lam R a γ i n).toNNReal + s) -
        γ (Regeneration.passageSequence Δ lam R a γ i n).toNNReal) ≤ R / 2) :
    Regeneration.IsGoodPassage Δ lam R a γ i n := by
  have hufin : Regeneration.roundUp Δ
      (Regeneration.passageSequence Δ lam R a γ i n) ≠ ⊤ := by
    rw [Regeneration.roundUp, ite_eq_right hfin]
    exact ENNReal.coe_ne_top
  refine ⟨hfin, hufin, fun t ht => ?_⟩
  have hs : t - (Regeneration.passageSequence Δ lam R a γ i n).toNNReal ≤ Δ :=
    (tsub_le_iff_right).mpr (by
      simpa only [add_comm] using
        (ht.2.trans (roundUp_toNNReal_le_add Δ hΔ _ hfin)))
  have hnorm := htube (t - (Regeneration.passageSequence Δ lam R a γ i n).toNNReal)
    ⟨zero_le, hs⟩
  rw [add_tsub_cancel_of_le ht.1] at hnorm
  exact (Regeneration.coordinate_abs_le_euclideanNorm
    (γ t - γ (Regeneration.passageSequence Δ lam R a γ i n).toNNReal) i).trans hnorm

end ConditionalTrialExhaustion

/-- The literal passage sequence following a deterministic restart, with its
level evaluated on the original sample. -/
noncomputable def couplingScopePassage {d : ℕ} (Δ : ℝ≥0) (lam R : ℝ)
    (A : Regeneration.CoupledSample d → ℝ) (m : ℕ) (i : Fin d)
    (n : ℕ) (z : Regeneration.CoupledSample d) : ℝ≥0∞ :=
  Regeneration.passageSequence Δ lam R (A z)
    (Regeneration.sampleTimeShift Δ z ((m : ℝ≥0) * Δ)).1 i n

/-- Even trials test the actual rounded guard, rather than a replacement
oscillation condition. -/
def couplingScopeEvenGuard {d : ℕ} (Δ : ℝ≥0) (lam R : ℝ)
    (A : Regeneration.CoupledSample d → ℝ) (m : ℕ) (i : Fin d)
    (n : ℕ) : Set (Regeneration.CoupledSample d) :=
  {z | Regeneration.IsGoodPassage Δ lam R (A z)
    (Regeneration.sampleTimeShift Δ z ((m : ℝ≥0) * Δ)).1 i (2 * n)}

/-- A finite prefix of failed even guards on finite passages, localized by
an original-sample event. This does not assert that the passages are finite. -/
def couplingScopeEvenGuardFailure {d : ℕ} (Δ : ℝ≥0) (lam R : ℝ)
    (A : Regeneration.CoupledSample d → ℝ) (m : ℕ) (i : Fin d)
    (B : Set (Regeneration.CoupledSample d)) (N : ℕ) :
    Set (FieldPair d × Regeneration.CoupledSample d) :=
  {q | q.2 ∈ B ∧ ∀ r < N, couplingScopePassage Δ lam R A m i (2 * r) q.2 ≠ ⊤ ∧
    q.2 ∉ couplingScopeEvenGuard Δ lam R A m i r}

/-- Full tube tests at the even actual passages do not overlap. This is a
deterministic scheduling fact and asserts no conditional probability bound. -/
theorem coupling_scope_even_passage_windows_separated {d : ℕ}
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (lam R : ℝ) (hR : 0 < R)
    (A : Regeneration.CoupledSample d → ℝ) (m : ℕ) (i : Fin d)
    (z : Regeneration.CoupledSample d) (r : ℕ)
    (hfin : couplingScopePassage Δ lam R A m i (2 * r + 2) z ≠ ⊤) :
    couplingScopePassage Δ lam R A m i (2 * r) z + (Δ : ℝ≥0∞) ≤
      couplingScopePassage Δ lam R A m i (2 * r + 2) z :=
  ConditionalTrialExhaustion.passage_add_step_le_two_later Δ hΔ lam R (A z) hR
    (Regeneration.sampleTimeShift Δ z ((m : ℝ≥0) * Δ)).1 i (2 * r) hfin

/-- Joint passage measurability keeps the sample-dependent level. -/
theorem coupling_scope_measurable_passage {d : ℕ} (Δ : ℝ≥0) (lam R : ℝ)
    (A : Regeneration.CoupledSample d → ℝ) (hA : Measurable A)
    (m : ℕ) (i : Fin d) (n : ℕ) :
    Measurable (couplingScopePassage Δ lam R A m i n) :=
  (Regeneration.measurable_passageSequence_joint Δ lam R i n).comp
    (hA.prodMk (((Regeneration.measurable_sampleTimeShift Δ).comp
      (measurable_const.prodMk measurable_id)).fst))

/-- The actual even guard is a measurable event. -/
theorem coupling_scope_measurableSet_even_guard {d : ℕ} (Δ : ℝ≥0) (lam R : ℝ)
    (A : Regeneration.CoupledSample d → ℝ) (hA : Measurable A)
    (m : ℕ) (i : Fin d) (n : ℕ) :
    MeasurableSet (couplingScopeEvenGuard Δ lam R A m i n) :=
  (hA.prodMk (((Regeneration.measurable_sampleTimeShift Δ).comp
    (measurable_const.prodMk measurable_id)).fst))
      (Regeneration.measurableSet_IsGoodPassage Δ lam R i (2 * n))

/-- A finite passage after a deterministic restart is determined by the
original path through the displayed absolute grid time and the past level. -/
theorem coupling_scope_passage_eq_of_prefix {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ)
    (lam R : ℝ) (hR : 0 < R) (A : Regeneration.CoupledSample d → ℝ)
    (m : ℕ) (i : Fin d) (n k : ℕ) (z z' : Regeneration.CoupledSample d)
    (hAeq : A z = A z')
    (hpre : ∀ t ∈ Set.Icc (0 : ℝ≥0) (((m + k : ℕ) : ℝ≥0) * Δ), z.1 t = z'.1 t)
    (hle : couplingScopePassage Δ lam R A m i n z ≤
      (((k : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞)) :
    couplingScopePassage Δ lam R A m i n z =
      couplingScopePassage Δ lam R A m i n z' := by
  unfold couplingScopePassage at hle ⊢
  rw [← hAeq]
  apply (Regeneration.passageSequence_prefix_determined Δ hΔ lam R (A z) hR
    _ _ i n ((k : ℝ≥0) * Δ) ?_).2 hle
  intro t ht
  apply hpre ((m : ℝ≥0) * Δ + t)
  refine ⟨zero_le, ?_⟩
  calc (m : ℝ≥0) * Δ + t ≤ (m : ℝ≥0) * Δ + (k : ℝ≥0) * Δ :=
      add_le_add le_rfl ht.2
    _ = ((m + k : ℕ) : ℝ≥0) * Δ := by rw [Nat.cast_add, add_mul]

/-- Once its actual rounded endpoint has been observed, the guard keeps its
closed all-time coordinate condition under any extension of that history. -/
theorem coupling_scope_even_guard_iff_of_prefix {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ)
    (lam R : ℝ) (hR : 0 < R) (A : Regeneration.CoupledSample d → ℝ)
    (m : ℕ) (i : Fin d) (n k : ℕ) (z z' : Regeneration.CoupledSample d)
    (hAeq : A z = A z')
    (hpre : ∀ t ∈ Set.Icc (0 : ℝ≥0) (((m + k : ℕ) : ℝ≥0) * Δ), z.1 t = z'.1 t)
    (hle : Regeneration.roundUp Δ (couplingScopePassage Δ lam R A m i (2 * n) z) ≤
      (((k : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞)) :
    z ∈ couplingScopeEvenGuard Δ lam R A m i n ↔
      z' ∈ couplingScopeEvenGuard Δ lam R A m i n := by
  have hv := (Regeneration.le_roundUp Δ hΔ _).trans hle
  have heq := coupling_scope_passage_eq_of_prefix Δ hΔ lam R hR A m i (2 * n) k
    z z' hAeq hpre hv
  have hfin := ne_top_of_le_ne_top ENNReal.coe_ne_top hv
  have hufin := ne_top_of_le_ne_top ENNReal.coe_ne_top hle
  have hvT : (couplingScopePassage Δ lam R A m i (2 * n) z).toNNReal ≤
      (k : ℝ≥0) * Δ := ENNReal.coe_le_coe.mp (by rwa [ENNReal.coe_toNNReal hfin])
  have huT : (Regeneration.roundUp Δ
      (couplingScopePassage Δ lam R A m i (2 * n) z)).toNNReal ≤
      (k : ℝ≥0) * Δ := ENNReal.coe_le_coe.mp (by rwa [ENNReal.coe_toNNReal hufin])
  have hp (t : ℝ≥0) (ht : t ≤ (k : ℝ≥0) * Δ) :
      (Regeneration.sampleTimeShift Δ z ((m : ℝ≥0) * Δ)).1 t =
      (Regeneration.sampleTimeShift Δ z' ((m : ℝ≥0) * Δ)).1 t := by
    apply hpre ((m : ℝ≥0) * Δ + t)
    refine ⟨zero_le, ?_⟩
    calc (m : ℝ≥0) * Δ + t ≤ (m : ℝ≥0) * Δ + (k : ℝ≥0) * Δ :=
        add_le_add le_rfl ht
      _ = ((m + k : ℕ) : ℝ≥0) * Δ := by rw [Nat.cast_add, add_mul]
  change Regeneration.IsGoodPassage Δ lam R (A z) _ i (2 * n) ↔
    Regeneration.IsGoodPassage Δ lam R (A z') _ i (2 * n)
  unfold Regeneration.IsGoodPassage
  dsimp only [couplingScopePassage] at heq hvT huT
  rw [← heq]
  constructor <;> rintro ⟨hf, hu, hosc⟩ <;> refine ⟨hf, hu, fun t ht => ?_⟩
  · rw [← hp t (ht.2.trans huT), ← hp _ hvT]
    exact hosc t ht
  · rw [hp t (ht.2.trans huT), hp _ hvT]
    exact hosc t ht

/-- A rounded actual passage sublevel uses the exact pre-bit finite history.
No stopping-time property for a regeneration time is asserted. -/
theorem coupling_scope_measurableSet_rounded_passage_le_finiteHistory {d : ℕ}
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (lam R : ℝ) (hR : 0 < R)
    (A : Regeneration.CoupledSample d → ℝ) (m : ℕ)
    (hA : @Measurable (Regeneration.CoupledSample d) ℝ
      (Regeneration.finiteHistorySigma Δ m) inferInstance A)
    (i : Fin d) (n k : ℕ) :
    @MeasurableSet (Regeneration.CoupledSample d)
      (Regeneration.finiteHistorySigma Δ (m + k))
      {z | Regeneration.roundUp Δ (couplingScopePassage Δ lam R A m i n z) ≤
        (((k : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞)} := by
  have hAg := hA.mono (Probability.finiteHistorySigma_le Δ m) le_rfl
  have hAmk := hA.mono (Regeneration.finiteHistorySigma_mono Δ (Nat.le_add_right m k)) le_rfl
  let E := {z | Regeneration.roundUp Δ (couplingScopePassage Δ lam R A m i n z) ≤
    (((k : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞)}
  have hset : E = Probability.stoppedHistorySample Δ (m + k) ⁻¹' E := by
    ext z
    have hAeq := (Probability.finiteHistory_test_stopped Δ (m + k) A hAmk z).symm
    have hpre : ∀ t ∈ Set.Icc (0 : ℝ≥0) (((m + k : ℕ) : ℝ≥0) * Δ),
        z.1 t = (Probability.stoppedHistorySample Δ (m + k) z).1 t :=
      fun t ht => (Probability.stoppedHistorySample_path Δ (m + k) z t ht.2).symm
    constructor
    · intro hz
      have heq := coupling_scope_passage_eq_of_prefix Δ hΔ lam R hR A m i n k
        z _ hAeq hpre ((Regeneration.le_roundUp Δ hΔ _).trans hz)
      change Regeneration.roundUp Δ _ ≤ _
      rw [← heq]
      exact hz
    · intro hz
      have heq := coupling_scope_passage_eq_of_prefix Δ hΔ lam R hR A m i n k
        _ z hAeq.symm (fun t ht => (hpre t ht).symm)
        ((Regeneration.le_roundUp Δ hΔ _).trans hz)
      change Regeneration.roundUp Δ _ ≤ _
      rw [← heq]
      exact hz
  change @MeasurableSet _ (Regeneration.finiteHistorySigma Δ (m + k)) E
  rw [hset]
  exact Probability.measurable_stoppedHistorySample Δ (m + k)
    (measurableSet_le ((Regeneration.measurable_roundUp Δ).comp
      (coupling_scope_measurable_passage Δ lam R A hAg m i n)) measurable_const)

/-- The observed actual guard is measurable before the bit at the observation
index. Its endpoint and the entire closed guard interval have been observed. -/
theorem coupling_scope_measurableSet_even_guard_observed_finiteHistory {d : ℕ}
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (lam R : ℝ) (hR : 0 < R)
    (A : Regeneration.CoupledSample d → ℝ) (m : ℕ)
    (hA : @Measurable (Regeneration.CoupledSample d) ℝ
      (Regeneration.finiteHistorySigma Δ m) inferInstance A)
    (i : Fin d) (n k : ℕ) :
    @MeasurableSet (Regeneration.CoupledSample d)
      (Regeneration.finiteHistorySigma Δ (m + k))
      {z | Regeneration.roundUp Δ (couplingScopePassage Δ lam R A m i (2 * n) z) ≤
        (((k : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞) ∧
        z ∈ couplingScopeEvenGuard Δ lam R A m i n} := by
  have hAg := hA.mono (Probability.finiteHistorySigma_le Δ m) le_rfl
  have hAmk := hA.mono (Regeneration.finiteHistorySigma_mono Δ (Nat.le_add_right m k)) le_rfl
  let E := {z | Regeneration.roundUp Δ (couplingScopePassage Δ lam R A m i (2 * n) z) ≤
    (((k : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞) ∧ z ∈ couplingScopeEvenGuard Δ lam R A m i n}
  have transfer (z z' : Regeneration.CoupledSample d) (hAeq : A z = A z')
      (hp : ∀ t ∈ Set.Icc (0 : ℝ≥0) (((m + k : ℕ) : ℝ≥0) * Δ), z.1 t = z'.1 t)
      (hz : z ∈ E) : z' ∈ E := by
    have heq := coupling_scope_passage_eq_of_prefix Δ hΔ lam R hR A m i (2 * n) k
      z z' hAeq hp ((Regeneration.le_roundUp Δ hΔ _).trans hz.1)
    refine ⟨?_, (coupling_scope_even_guard_iff_of_prefix Δ hΔ lam R hR A m i n k
      z z' hAeq hp hz.1).mp hz.2⟩
    rw [← heq]
    exact hz.1
  have hset : E = Probability.stoppedHistorySample Δ (m + k) ⁻¹' E := by
    ext z
    have hAeq := (Probability.finiteHistory_test_stopped Δ (m + k) A hAmk z).symm
    have hp : ∀ t ∈ Set.Icc (0 : ℝ≥0) (((m + k : ℕ) : ℝ≥0) * Δ),
        z.1 t = (Probability.stoppedHistorySample Δ (m + k) z).1 t :=
      fun t ht => (Probability.stoppedHistorySample_path Δ (m + k) z t ht.2).symm
    exact ⟨transfer z _ hAeq hp,
      transfer _ z hAeq.symm (fun t ht => (hp t ht).symm)⟩
  change @MeasurableSet _ (Regeneration.finiteHistorySigma Δ (m + k)) E
  rw [hset]
  exact Probability.measurable_stoppedHistorySample Δ (m + k)
    ((measurableSet_le ((Regeneration.measurable_roundUp Δ).comp
      (coupling_scope_measurable_passage Δ lam R A hAg m i (2 * n))) measurable_const).inter
      (coupling_scope_measurableSet_even_guard Δ lam R A hAg m i n))

/-- Observed failure, including its actual rounded endpoint, is known in the
same pre-bit history as observed success. -/
theorem coupling_scope_measurableSet_even_guard_failure_observed_finiteHistory {d : ℕ}
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (lam R : ℝ) (hR : 0 < R)
    (A : Regeneration.CoupledSample d → ℝ) (m : ℕ)
    (hA : @Measurable (Regeneration.CoupledSample d) ℝ
      (Regeneration.finiteHistorySigma Δ m) inferInstance A)
    (i : Fin d) (n k : ℕ) :
    @MeasurableSet (Regeneration.CoupledSample d)
      (Regeneration.finiteHistorySigma Δ (m + k))
      {z | Regeneration.roundUp Δ (couplingScopePassage Δ lam R A m i (2 * n) z) ≤
        (((k : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞) ∧
        z ∉ couplingScopeEvenGuard Δ lam R A m i n} := by
  have h := (coupling_scope_measurableSet_rounded_passage_le_finiteHistory
    Δ hΔ lam R hR A m hA i (2 * n) k).diff
    (coupling_scope_measurableSet_even_guard_observed_finiteHistory
      Δ hΔ lam R hR A m hA i n k)
  convert h using 1
  ext z
  simp only [Set.mem_ofPred_eq, Set.mem_sdiff]
  tauto

/-- Failure prefixes use only measurable actual passage and guard events. -/
theorem coupling_scope_measurableSet_even_guard_failure {d : ℕ} (Δ : ℝ≥0)
    (lam R : ℝ) (A : Regeneration.CoupledSample d → ℝ) (hA : Measurable A)
    (m : ℕ) (i : Fin d) (B : Set (Regeneration.CoupledSample d))
    (hB : MeasurableSet B) (N : ℕ) :
    MeasurableSet (couplingScopeEvenGuardFailure Δ lam R A m i B N) := by
  simp only [couplingScopeEvenGuardFailure, Set.ofPred_and, Set.ofPred_forall]
  apply (measurable_snd hB).inter
  apply MeasurableSet.iInter
  intro r
  apply MeasurableSet.iInter
  intro _hr
  exact ((measurableSet_eq_fun
    ((coupling_scope_measurable_passage Δ lam R A hA m i (2 * r)).comp measurable_snd)
    measurable_const).compl).inter
      (measurable_snd (coupling_scope_measurableSet_even_guard Δ lam R A hA m i r)).compl

/-- Actual even-guard failures whose rounded observation windows have all
ended by the displayed grid index. This retains the original past event. -/
def couplingScopeEvenGuardHistoryFailure {d : ℕ} (Δ : ℝ≥0) (lam R : ℝ)
    (A : Regeneration.CoupledSample d → ℝ) (m : ℕ) (i : Fin d)
    (B : Set (Regeneration.CoupledSample d)) (N k : ℕ) :
    Set (Regeneration.CoupledSample d) :=
  {z | z ∈ B ∧ ∀ r < N,
    Regeneration.roundUp Δ (couplingScopePassage Δ lam R A m i (2 * r) z) ≤
      (((k : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞) ∧
    z ∉ couplingScopeEvenGuard Δ lam R A m i r}

/-- Observation adds only the requirement that the actual guard windows have
ended; finite entry is already implied by their finite rounded endpoints. -/
theorem coupling_scope_even_guard_history_failure_eq {d : ℕ}
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (lam R : ℝ)
    (A : Regeneration.CoupledSample d → ℝ) (m : ℕ) (i : Fin d)
    (B : Set (Regeneration.CoupledSample d)) (N k : ℕ) (ω : FieldPair d) :
    couplingScopeEvenGuardHistoryFailure Δ lam R A m i B N k =
      {z | (ω, z) ∈ couplingScopeEvenGuardFailure Δ lam R A m i B N ∧
        ∀ r < N, Regeneration.roundUp Δ
          (couplingScopePassage Δ lam R A m i (2 * r) z) ≤
            (((k : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞)} := by
  ext z
  constructor
  · rintro ⟨hb, hall⟩
    refine ⟨⟨hb, fun r hr => ⟨?_, (hall r hr).2⟩⟩, fun r hr => (hall r hr).1⟩
    exact ne_top_of_le_ne_top ENNReal.coe_ne_top
      ((Regeneration.le_roundUp Δ hΔ _).trans (hall r hr).1)
  · rintro ⟨⟨hb, hall⟩, htime⟩
    exact ⟨hb, fun r hr => ⟨htime r hr, (hall r hr).2⟩⟩

/-- Every finite collection of completed actual guard failures belongs to
exactly the history excluding the bit at the observation index. -/
theorem coupling_scope_measurableSet_even_guard_history_failure_finiteHistory {d : ℕ}
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (lam R : ℝ) (hR : 0 < R)
    (A : Regeneration.CoupledSample d → ℝ) (m : ℕ)
    (hA : @Measurable (Regeneration.CoupledSample d) ℝ
      (Regeneration.finiteHistorySigma Δ m) inferInstance A)
    (i : Fin d) (B : Set (Regeneration.CoupledSample d))
    (hB : MeasurableSet[Regeneration.finiteHistorySigma Δ m] B) (N k : ℕ) :
    @MeasurableSet (Regeneration.CoupledSample d)
      (Regeneration.finiteHistorySigma Δ (m + k))
      (couplingScopeEvenGuardHistoryFailure Δ lam R A m i B N k) := by
  simp only [couplingScopeEvenGuardHistoryFailure, Set.ofPred_and, Set.ofPred_forall]
  apply (Regeneration.finiteHistorySigma_mono Δ (Nat.le_add_right m k) B hB).inter
  apply MeasurableSet.iInter
  intro r
  apply MeasurableSet.iInter
  intro _hr
  exact coupling_scope_measurableSet_even_guard_failure_observed_finiteHistory
    Δ hΔ lam R hR A m hA i r k

/-- Freshness applies at the observation index to the completed actual guard
failures, even when their restart level depends on the original history. -/
theorem coupling_scope_measure_even_guard_history_failure_fresh_bit {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (K : Regeneration.CoupledQuenchedLaws d) (hK : Regeneration.HasProbabilityLaws Q K)
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (δ : ℝ) (hδ : 0 ≤ δ)
    (hFresh : Regeneration.HasFreshBits Q Δ δ K)
    (lam R : ℝ) (hR : 0 < R) (A : Regeneration.CoupledSample d → ℝ) (m : ℕ)
    (hA : @Measurable (Regeneration.CoupledSample d) ℝ
      (Regeneration.finiteHistorySigma Δ m) inferInstance A)
    (i : Fin d) (B : Set (Regeneration.CoupledSample d))
    (hB : MeasurableSet[Regeneration.finiteHistorySigma Δ m] B) (N k : ℕ) :
    Regeneration.annealedCoupledLaw Q K
      {q | q.2 ∈ couplingScopeEvenGuardHistoryFailure Δ lam R A m i B N k ∧
        q.2.2 (m + k) = true} =
      ENNReal.ofReal δ * Regeneration.annealedCoupledLaw Q K
        {q | q.2 ∈ couplingScopeEvenGuardHistoryFailure Δ lam R A m i B N k} :=
  Regeneration.measure_annealed_fresh_bit Q K hK Δ δ hδ hFresh (m + k) _
    (coupling_scope_measurableSet_even_guard_history_failure_finiteHistory
      Δ hΔ lam R hR A m hA i B hB N k)

/-- At a deterministic grid restart, the actual completed failure history
can multiply any bounded measurable future test in the supplied restart law.
This identity averages the fresh bit and asserts no stopping-time restart. -/
theorem coupling_scope_even_guard_history_failure_restart {d : ℕ}
    (K : Regeneration.CoupledQuenchedLaws d) (xω : Vec d × FieldPair d)
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (hRestart : Regeneration.DeterministicRestartAt Δ K xω)
    (lam R : ℝ) (hR : 0 < R) (A : Regeneration.CoupledSample d → ℝ) (m : ℕ)
    (hA : @Measurable (Regeneration.CoupledSample d) ℝ
      (Regeneration.finiteHistorySigma Δ m) inferInstance A)
    (i : Fin d) (B : Set (Regeneration.CoupledSample d))
    (hB : MeasurableSet[Regeneration.finiteHistorySigma Δ m] B) (N k : ℕ)
    (Φ : Regeneration.CoupledSample d → ℝ) (hΦ : Measurable Φ)
    (hbΦ : Regeneration.BoundedRealTest Φ) :
    let E := couplingScopeEvenGuardHistoryFailure Δ lam R A m i B N k
    (∫ z, E.indicator (fun _ => (1 : ℝ)) z *
      Φ (Regeneration.sampleTimeShift Δ z (((m + k : ℕ) : ℝ≥0) * Δ)) ∂K xω) =
      ∫ z, E.indicator (fun _ => (1 : ℝ)) z *
        (∫ w, Φ w ∂K (z.1 (((m + k : ℕ) : ℝ≥0) * Δ), xω.2)) ∂K xω := by
  apply hRestart (m + k) _ Φ
  · exact measurable_const.indicator
      (coupling_scope_measurableSet_even_guard_history_failure_finiteHistory
        Δ hΔ lam R hR A m hA i B hB N k)
  · refine ⟨1, fun z => ?_⟩
    by_cases hz : z ∈ couplingScopeEvenGuardHistoryFailure Δ lam R A m i B N k
    · rw [Set.indicator_of_mem hz, abs_one]
    · rw [Set.indicator_of_notMem hz, abs_zero]
      exact zero_le_one
  · exact hΦ
  · exact hbΦ

/-- Every earlier rounded guard endpoint precedes a finite later passage.
The chronology uses the actual successive levels and strict crossings. -/
theorem coupling_scope_rounded_passage_le_later {d : ℕ}
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (lam R : ℝ) (hR : 0 < R)
    (A : Regeneration.CoupledSample d → ℝ) (m : ℕ) (i : Fin d)
    (z : Regeneration.CoupledSample d) (r N : ℕ) (hrN : r < N)
    (hfin : couplingScopePassage Δ lam R A m i N z ≠ ⊤) :
    Regeneration.roundUp Δ (couplingScopePassage Δ lam R A m i r z) ≤
      couplingScopePassage Δ lam R A m i N z := by
  have hmono := Regeneration.monotone_passageSequence Δ hΔ lam R (A z) hR
    (Regeneration.sampleTimeShift Δ z ((m : ℝ≥0) * Δ)).1 i
  have hrfin : couplingScopePassage Δ lam R A m i r z ≠ ⊤ :=
    ne_top_of_le_ne_top hfin (hmono hrN.le)
  have hurfin : Regeneration.roundUp Δ
      (couplingScopePassage Δ lam R A m i r z) ≠ ⊤ := by
    rw [Regeneration.roundUp, ite_eq_right hrfin]
    exact ENNReal.coe_ne_top
  exact (Regeneration.rounded_passage_lt_next Δ lam R (A z) hR
    (Regeneration.sampleTimeShift Δ z ((m : ℝ≥0) * Δ)).1 i r hurfin).le.trans
      (hmono hrN)

/-- By the next finite observed even passage, all preceding actual failure
windows have ended. Observation therefore loses no earlier failure event. -/
theorem coupling_scope_even_guard_history_failure_iff_of_next_le {d : ℕ}
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (lam R : ℝ) (hR : 0 < R)
    (A : Regeneration.CoupledSample d → ℝ) (m : ℕ) (i : Fin d)
    (B : Set (Regeneration.CoupledSample d)) (N k : ℕ)
    (ω : FieldPair d) (z : Regeneration.CoupledSample d)
    (hle : Regeneration.roundUp Δ (couplingScopePassage Δ lam R A m i (2 * N) z) ≤
      (((k : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞)) :
    z ∈ couplingScopeEvenGuardHistoryFailure Δ lam R A m i B N k ↔
      (ω, z) ∈ couplingScopeEvenGuardFailure Δ lam R A m i B N := by
  rw [coupling_scope_even_guard_history_failure_eq Δ hΔ lam R A m i B N k ω]
  refine and_iff_left ?_
  intro r hr
  have hfin := ne_top_of_le_ne_top ENNReal.coe_ne_top
    ((Regeneration.le_roundUp Δ hΔ _).trans hle)
  exact (coupling_scope_rounded_passage_le_later Δ hΔ lam R hR A m i z
    (2 * r) (2 * N) (by omega) hfin).trans
      ((Regeneration.le_roundUp Δ hΔ _).trans hle)

/-- The actual failure prefix, restricted to observing the next rounded even
passage by a grid time, is a pre-bit event at that grid time. -/
theorem coupling_scope_measurableSet_even_guard_failure_next_le_finiteHistory {d : ℕ}
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (lam R : ℝ) (hR : 0 < R)
    (A : Regeneration.CoupledSample d → ℝ) (m : ℕ)
    (hA : @Measurable (Regeneration.CoupledSample d) ℝ
      (Regeneration.finiteHistorySigma Δ m) inferInstance A)
    (i : Fin d) (B : Set (Regeneration.CoupledSample d))
    (hB : MeasurableSet[Regeneration.finiteHistorySigma Δ m] B) (N k : ℕ)
    (ω : FieldPair d) :
    @MeasurableSet (Regeneration.CoupledSample d)
      (Regeneration.finiteHistorySigma Δ (m + k))
      {z | Regeneration.roundUp Δ (couplingScopePassage Δ lam R A m i (2 * N) z) ≤
        (((k : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞) ∧
        (ω, z) ∈ couplingScopeEvenGuardFailure Δ lam R A m i B N} := by
  have h := (coupling_scope_measurableSet_rounded_passage_le_finiteHistory
    Δ hΔ lam R hR A m hA i (2 * N) k).inter
    (coupling_scope_measurableSet_even_guard_history_failure_finiteHistory
      Δ hΔ lam R hR A m hA i B hB N k)
  convert h using 1
  ext z
  constructor
  · rintro ⟨ht, hf⟩
    exact ⟨ht, (coupling_scope_even_guard_history_failure_iff_of_next_le
      Δ hΔ lam R hR A m i B N k ω z ht).mpr hf⟩
  · rintro ⟨ht, hf⟩
    exact ⟨ht, (coupling_scope_even_guard_history_failure_iff_of_next_le
      Δ hΔ lam R hR A m i B N k ω z ht).mp hf⟩

/-- The next failure is precisely entry followed by failure of the actual
guard. The finite-entry restriction is retained. -/
theorem coupling_scope_even_guard_failure_succ {d : ℕ} (Δ : ℝ≥0) (lam R : ℝ)
    (A : Regeneration.CoupledSample d → ℝ) (m : ℕ) (i : Fin d)
    (B : Set (Regeneration.CoupledSample d)) (N : ℕ) :
    couplingScopeEvenGuardFailure Δ lam R A m i B (N + 1) =
      (couplingScopeEvenGuardFailure Δ lam R A m i B N ∩
        {q | couplingScopePassage Δ lam R A m i (2 * N) q.2 ≠ ⊤}) \
        {q | q.2 ∈ couplingScopeEvenGuard Δ lam R A m i N} := by
  ext q
  constructor
  · rintro ⟨hb, hall⟩
    exact ⟨⟨⟨hb, fun r hr => hall r (Nat.lt_succ_of_lt hr)⟩,
      (hall N (Nat.lt_succ_self N)).1⟩, (hall N (Nat.lt_succ_self N)).2⟩
  · rintro ⟨⟨⟨hb, hall⟩, hfin⟩, hbad⟩
    refine ⟨hb, fun r hr => ?_⟩
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hr) with hlt | rfl
    · exact hall r hlt
    · exact ⟨hfin, hbad⟩

/-- A uniform integrated success bound on the entered finite trials gives
the geometric bound on the actual even-guard failure prefixes. This helper
leaves the genuine conditional guard estimate as a producer obligation. -/
theorem coupling_scope_even_guard_failure_product_of_estimate {d : ℕ}
    (μ : Measure (FieldPair d × Regeneration.CoupledSample d)) [IsProbabilityMeasure μ]
    (Δ : ℝ≥0) (lam R : ℝ) (A : Regeneration.CoupledSample d → ℝ)
    (hA : Measurable A) (m : ℕ) (i : Fin d)
    (B : Set (Regeneration.CoupledSample d)) (ε : ℝ) (hε : ε ≤ 1)
    (hwin : ∀ N,
      let E := couplingScopeEvenGuardFailure Δ lam R A m i B N ∩
        {q | couplingScopePassage Δ lam R A m i (2 * N) q.2 ≠ ⊤}
      ε * μ.real E ≤ μ.real (E ∩
        {q | q.2 ∈ couplingScopeEvenGuard Δ lam R A m i N})) (N : ℕ) :
    μ (couplingScopeEvenGuardFailure Δ lam R A m i B N) ≤
      ENNReal.ofReal (1 - ε) ^ N * μ {q | q.2 ∈ B} := by
  have hstep (n : ℕ) :
      μ (couplingScopeEvenGuardFailure Δ lam R A m i B (n + 1)) ≤
        ENNReal.ofReal (1 - ε) *
          μ (couplingScopeEvenGuardFailure Δ lam R A m i B n) := by
    rw [coupling_scope_even_guard_failure_succ]
    exact (ConditionalTrialExhaustion.measure_sdiff_le_of_success_measure μ _ _
      (measurable_snd (coupling_scope_measurableSet_even_guard Δ lam R A hA m i n))
      ε hε (hwin n)).trans (mul_le_mul_right (measure_mono Set.inter_subset_left) _)
  simpa only [couplingScopeEvenGuardFailure, Nat.not_lt_zero, IsEmpty.forall_iff,
    implies_true, and_true] using
    ConditionalTrialExhaustion.finite_product_of_failure_step μ _
      (ENNReal.ofReal (1 - ε)) hstep N

/-- Finite passage guards yield finite first rounded candidates by the literal
infimum definition; no candidate-attainment assumption is needed. -/
theorem coupling_scope_first_candidate_finite_of_good {d : ℕ} (Δ : ℝ≥0)
    (lam R a : ℝ) (γ : Path d) (i : Fin d) (n : ℕ)
    (hgood : Regeneration.IsGoodPassage Δ lam R a γ i n) :
    Regeneration.firstRoundedCandidate Δ lam R a γ i ≠ ⊤ :=
  ne_top_of_le_ne_top hgood.2.1
    (iInf_le_of_le n (iInf_le_of_le hgood le_rfl))

/-- Under the actual joint probability law, integrated conditional guard
estimates and finite passages imply a finite first candidate on the localized
event. Neither analytic hypothesis is asserted to hold by this consumer. -/
theorem coupling_scope_ae_first_candidate_finite_of_guard_estimate {d : ℕ}
    (μ : Measure (FieldPair d × Regeneration.CoupledSample d)) [IsProbabilityMeasure μ]
    (Δ : ℝ≥0) (lam R : ℝ) (A : Regeneration.CoupledSample d → ℝ)
    (hA : Measurable A) (m : ℕ) (i : Fin d)
    (B : Set (Regeneration.CoupledSample d)) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hfinite : ∀ᵐ q ∂μ, ∀ n, couplingScopePassage Δ lam R A m i n q.2 ≠ ⊤)
    (hwin : ∀ N,
      let E := couplingScopeEvenGuardFailure Δ lam R A m i B N ∩
        {q | couplingScopePassage Δ lam R A m i (2 * N) q.2 ≠ ⊤}
      ε * μ.real E ≤ μ.real (E ∩
        {q | q.2 ∈ couplingScopeEvenGuard Δ lam R A m i N})) :
    ∀ᵐ q ∂μ, q.2 ∈ B →
      Regeneration.firstRoundedCandidate Δ lam R (A q.2)
        (Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)).1 i ≠ ⊤ := by
  let F := couplingScopeEvenGuardFailure Δ lam R A m i B
  have hnull : μ (⋂ n, F n) = 0 := by
    apply le_antisymm _ zero_le
    apply ge_of_tendsto' (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one
      (ENNReal.ofReal_lt_one.mpr (by linarith : 1 - ε < 1)))
    intro n
    calc
      μ (⋂ k, F k) ≤ μ (F n) := measure_mono (Set.iInter_subset _ n)
      _ ≤ ENNReal.ofReal (1 - ε) ^ n * μ {q | q.2 ∈ B} :=
        coupling_scope_even_guard_failure_product_of_estimate μ Δ lam R A hA m i B
          ε hε1 hwin n
      _ ≤ ENNReal.ofReal (1 - ε) ^ n * 1 := mul_le_mul_right prob_le_one _
      _ = ENNReal.ofReal (1 - ε) ^ n := mul_one _
  have havoid : ∀ᵐ q ∂μ, q ∉ ⋂ n, F n := by
    rw [ae_iff]
    simpa only [not_not, Set.ofPred_mem_eq] using hnull
  filter_upwards [hfinite, havoid] with q hfin hnot hb
  by_contra htop
  apply hnot
  apply Set.mem_iInter.mpr
  intro N
  refine ⟨hb, fun r _hr => ⟨hfin (2 * r), ?_⟩⟩
  intro hg
  exact coupling_scope_first_candidate_finite_of_good Δ lam R (A q.2) _ i (2 * r)
    hg htop

/-- Successive deterministic grid restarts have the same literal path. This
uses no renewal or Markov property of the split-coin filtration. -/
theorem coupling_scope_path_restart_add {d : ℕ} (Δ : ℝ≥0)
    (z : Regeneration.CoupledSample d) (m k : ℕ) :
    Regeneration.pathTimeShift
      (Regeneration.sampleTimeShift Δ z ((m : ℝ≥0) * Δ)).1 ((k : ℝ≥0) * Δ) =
      (Regeneration.sampleTimeShift Δ z (((m + k : ℕ) : ℝ≥0) * Δ)).1 := by
  ext t j
  change z.1 ((m : ℝ≥0) * Δ + ((k : ℝ≥0) * Δ + t)) j =
    z.1 (((m + k : ℕ) : ℝ≥0) * Δ + t) j
  rw [Nat.cast_add, add_mul, add_assoc]

/-- Uniform genuine guard estimates at all deterministic grid restarts give
almost-sure finiteness of every actual candidate. The hypotheses are exactly
the finite-passage and integrated guard producer obligations; this is a
conditional helper, not a source-node reduction. -/
theorem coupling_scope_ae_candidates_finite_of_guard_estimates {d : ℕ}
    (μ : Measure (FieldPair d × Regeneration.CoupledSample d)) [IsProbabilityMeasure μ]
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (lam R : ℝ) (i : Fin d)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hpassage : ∀ (m : ℕ) (A : Regeneration.CoupledSample d → ℝ),
      @Measurable (Regeneration.CoupledSample d) ℝ
        (Regeneration.finiteHistorySigma Δ m) inferInstance A →
      ∀ᵐ q ∂μ, ∀ n, couplingScopePassage Δ lam R A m i n q.2 ≠ ⊤)
    (hwin : ∀ (m : ℕ) (A : Regeneration.CoupledSample d → ℝ),
      @Measurable (Regeneration.CoupledSample d) ℝ
        (Regeneration.finiteHistorySigma Δ m) inferInstance A →
      ∀ N,
        let E := couplingScopeEvenGuardFailure Δ lam R A m i Set.univ N ∩
          {q | couplingScopePassage Δ lam R A m i (2 * N) q.2 ≠ ⊤}
        ε * μ.real E ≤ μ.real (E ∩
          {q | q.2 ∈ couplingScopeEvenGuard Δ lam R A m i N}))
    (m : ℕ) (A : Regeneration.CoupledSample d → ℝ)
    (hA : @Measurable (Regeneration.CoupledSample d) ℝ
      (Regeneration.finiteHistorySigma Δ m) inferInstance A) :
    ∀ᵐ q ∂μ, ∀ N, couplingScopeCandidate Δ lam R A m i N q.2 ≠ ⊤ := by
  have hfirst (m' : ℕ) (A' : Regeneration.CoupledSample d → ℝ)
      (hA' : @Measurable (Regeneration.CoupledSample d) ℝ
        (Regeneration.finiteHistorySigma Δ m') inferInstance A') :
      ∀ᵐ q ∂μ, Regeneration.firstRoundedCandidate Δ lam R (A' q.2)
        (Regeneration.sampleTimeShift Δ q.2 ((m' : ℝ≥0) * Δ)).1 i ≠ ⊤ := by
    have h := coupling_scope_ae_first_candidate_finite_of_guard_estimate μ Δ lam R A'
      (hA'.mono (Probability.finiteHistorySigma_le Δ m') le_rfl) m' i Set.univ
      ε hε hε1 (hpassage m' A' hA') (hwin m' A' hA')
    filter_upwards [h] with q hq
    exact hq (Set.mem_univ _)
  have hrestart : ∀ᵐ q ∂μ, ∀ k : ℕ,
      Regeneration.firstRoundedCandidate Δ lam R (3 * lam * R)
        (Regeneration.sampleTimeShift Δ q.2 ((k : ℝ≥0) * Δ)).1 i ≠ ⊤ :=
    ae_all_iff.mpr (fun k => hfirst k (fun _ => 3 * lam * R) measurable_const)
  filter_upwards [hfirst m A hA, hrestart] with q hbase hall
  intro N
  induction N with
  | zero => exact hbase
  | succ n ih =>
    obtain ⟨k, hk⟩ := Regeneration.roundedCandidateSequence_mem_grid Δ hΔ lam R (A q.2)
      (Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)) i n ih
    have ht : (couplingScopeCandidate Δ lam R A m i n q.2).toNNReal =
        (k : ℝ≥0) * Δ := by rw [show couplingScopeCandidate Δ lam R A m i n q.2 = _
          from hk, ENNReal.toNNReal_coe]
    change Regeneration.roundedCandidateSequence Δ lam R (A q.2)
      (Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)) i (n + 1) ≠ ⊤
    have ih' : Regeneration.roundedCandidateSequence Δ lam R (A q.2)
        (Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)) i n ≠ ⊤ := ih
    rw [Regeneration.roundedCandidateSequence, ite_eq_right ih']
    apply ENNReal.add_ne_top.mpr
    refine ⟨ih, ?_⟩
    change Regeneration.firstRoundedCandidate Δ lam R (3 * lam * R)
      (Regeneration.pathTimeShift
        (Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)).1
        (couplingScopeCandidate Δ lam R A m i n q.2).toNNReal) i ≠ ⊤
    rw [ht, coupling_scope_path_restart_add]
    exact hall (m + k)

/-- The literal level at which the construction restarts after a rounded
failure at `mΔ`. It retains the running maximum and the actual displacement. -/
noncomputable def couplingScopeRestartLevel {d : ℕ} (Δ : ℝ≥0) (lam R : ℝ)
    (m : ℕ) (i : Fin d) (z : Regeneration.CoupledSample d) : ℝ :=
  lam * (Regeneration.coordinateMaximum z.1 i ((m : ℝ≥0) * Δ) -
    (z.1 ((m : ℝ≥0) * Δ) i - z.1 0 i) + R)

/-- The actual failure-restart level uses only the path through its displayed
grid time, and is measurable for the exact pre-bit finite history. -/
theorem coupling_scope_measurable_restart_level_finiteHistory {d : ℕ}
    (Δ : ℝ≥0) (lam R : ℝ) (m : ℕ) (i : Fin d) :
    @Measurable (Regeneration.CoupledSample d) ℝ
      (Regeneration.finiteHistorySigma Δ m) inferInstance
      (couplingScopeRestartLevel Δ lam R m i) := by
  have hM : Measurable (fun z : Regeneration.CoupledSample d =>
      Regeneration.coordinateMaximum z.1 i ((m : ℝ≥0) * Δ)) :=
    (Regeneration.measurable_coordinateMaximum i).comp
      (measurable_const.prodMk measurable_fst)
  have hx (t : ℝ≥0) : Measurable (fun z : Regeneration.CoupledSample d => z.1 t i) :=
    (measurable_pi_apply i).comp ((continuous_eval_const t).measurable.comp measurable_fst)
  have hglobal : Measurable (couplingScopeRestartLevel Δ lam R m i) :=
    measurable_const.mul ((hM.sub ((hx _).sub (hx 0))).add_const R)
  have heq (z : Regeneration.CoupledSample d) :
      couplingScopeRestartLevel Δ lam R m i
        (Probability.stoppedHistorySample Δ m z) = couplingScopeRestartLevel Δ lam R m i z := by
    have hmax : Regeneration.coordinateMaximum (Probability.stoppedHistorySample Δ m z).1
        i ((m : ℝ≥0) * Δ) =
        Regeneration.coordinateMaximum z.1 i ((m : ℝ≥0) * Δ) := by
      unfold Regeneration.coordinateMaximum
      congr 1
      apply Set.image_congr
      intro t ht
      rw [Probability.stoppedHistorySample_path Δ m z t ht.2,
        Probability.stoppedHistorySample_path Δ m z 0 zero_le]
    unfold couplingScopeRestartLevel
    rw [hmax, Probability.stoppedHistorySample_path Δ m z _ le_rfl,
      Probability.stoppedHistorySample_path Δ m z 0 zero_le]
  convert hglobal.comp (Probability.measurable_stoppedHistorySample Δ m) using 1
  exact (funext heq).symm

/-- A finite next successful candidate at the literal failure-restart level
gives a finite next full trial, including its final one-grid bridge period. -/
theorem coupling_scope_trial_reentry_finite {d : ℕ} (Δ : ℝ≥0) (lam R : ℝ)
    (z : Regeneration.CoupledSample d) (i : Fin d) (n m : ℕ)
    (ht : Regeneration.trialFailureTime Δ R z i
      (Regeneration.trialStartSequence Δ lam R z i n) =
        (((m : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞))
    (hsuccess : Regeneration.firstSuccessfulCandidate Δ lam R
      (couplingScopeRestartLevel Δ lam R m i z)
      (Regeneration.sampleTimeShift Δ z ((m : ℝ≥0) * Δ)) i ≠ ⊤) :
    Regeneration.trialStartSequence Δ lam R z i (n + 1) ≠ ⊤ := by
  have htfin : Regeneration.trialFailureTime Δ R z i
      (Regeneration.trialStartSequence Δ lam R z i n) ≠ ⊤ := ht ▸ ENNReal.coe_ne_top
  rw [Regeneration.trialStartSequence, ite_eq_right htfin, ht, ENNReal.toNNReal_coe]
  exact ENNReal.add_ne_top.mpr
    ⟨ENNReal.add_ne_top.mpr ⟨ENNReal.coe_ne_top, hsuccess⟩, ENNReal.coe_ne_top⟩

/-- Genuine integrated rounded-guard estimates give a finite successful
candidate under the actual annealed law by the supplied fresh-bit clause.
The finite-passage and conditional guard estimates remain analytic obligations. -/
theorem coupling_scope_ae_successful_candidate_finite_of_guard_estimates {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (K : Regeneration.CoupledQuenchedLaws d) (hK : Regeneration.HasProbabilityLaws Q K)
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hFresh : Regeneration.HasFreshBits Q Δ δ K)
    (lam R : ℝ) (hlam : 0 < lam) (hR : 0 < R) (i : Fin d)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hpassage : ∀ (m : ℕ) (A : Regeneration.CoupledSample d → ℝ),
      @Measurable (Regeneration.CoupledSample d) ℝ
        (Regeneration.finiteHistorySigma Δ m) inferInstance A →
      ∀ᵐ q ∂Regeneration.annealedCoupledLaw Q K,
        ∀ n, couplingScopePassage Δ lam R A m i n q.2 ≠ ⊤)
    (hwin : ∀ (m : ℕ) (A : Regeneration.CoupledSample d → ℝ),
      @Measurable (Regeneration.CoupledSample d) ℝ
        (Regeneration.finiteHistorySigma Δ m) inferInstance A →
      ∀ N,
        let μ := Regeneration.annealedCoupledLaw Q K
        let E := couplingScopeEvenGuardFailure Δ lam R A m i Set.univ N ∩
          {q | couplingScopePassage Δ lam R A m i (2 * N) q.2 ≠ ⊤}
        ε * μ.real E ≤ μ.real (E ∩
          {q | q.2 ∈ couplingScopeEvenGuard Δ lam R A m i N}))
    (m : ℕ) (A : Regeneration.CoupledSample d → ℝ)
    (hA : @Measurable (Regeneration.CoupledSample d) ℝ
      (Regeneration.finiteHistorySigma Δ m) inferInstance A) :
    ∀ᵐ q ∂Regeneration.annealedCoupledLaw Q K,
      Regeneration.firstSuccessfulCandidate Δ lam R (A q.2)
        (Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)) i ≠ ⊤ := by
  have : IsProbabilityMeasure (Regeneration.annealedCoupledLaw Q K) :=
    Regeneration.annealedCoupledLaw_isProbabilityMeasure Q K hK
  have hcandidates := coupling_scope_ae_candidates_finite_of_guard_estimates
    (Regeneration.annealedCoupledLaw Q K) Δ hΔ lam R i ε hε hε1 hpassage hwin m A hA
  have hexhaust := coupling_scope_ae_successful_candidate_finite_of_candidates Q K hK
    Δ hΔ δ hδ hδ1 hFresh lam R hlam hR A m hA i
  filter_upwards [hcandidates, hexhaust] with q hfin hex
  exact hex hfin

/-- Successful candidates at the initial level and every literal rounded
failure level leave no gap in the actual trial recursion. A full trial still
includes the bridge period after selection. -/
theorem coupling_scope_trial_entries_of_successful_candidates {d : ℕ}
    (Δ : ℝ≥0) (lam R : ℝ) (z : Regeneration.CoupledSample d) (i : Fin d)
    (hfirst : Regeneration.firstSuccessfulCandidate Δ lam R (3 * lam * R) z i ≠ ⊤)
    (hrestart : ∀ m : ℕ, Regeneration.firstSuccessfulCandidate Δ lam R
      (couplingScopeRestartLevel Δ lam R m i z)
      (Regeneration.sampleTimeShift Δ z ((m : ℝ≥0) * Δ)) i ≠ ⊤) :
    Regeneration.trialStartSequence Δ lam R z i 0 ≠ ⊤ ∧
      ∀ n : ℕ, Regeneration.trialFailureTime Δ R z i
        (Regeneration.trialStartSequence Δ lam R z i n) ≠ ⊤ →
          Regeneration.trialStartSequence Δ lam R z i (n + 1) ≠ ⊤ := by
  constructor
  · exact ENNReal.add_ne_top.mpr ⟨hfirst, ENNReal.coe_ne_top⟩
  · intro n hn
    obtain ⟨m, hm⟩ := Regeneration.trialFailureTime_mem_grid Δ R z i _ hn
    exact coupling_scope_trial_reentry_finite Δ lam R z i n m hm (hrestart m)

/-- Countably many deterministic restart levels suffice for all actual
failed-trial reentries under the annealed origin law. No law at a randomly
chosen endpoint is substituted for a deterministic restart identity. -/
theorem coupling_scope_ae_trial_entries_of_guard_estimates {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (K : Regeneration.CoupledQuenchedLaws d) (hK : Regeneration.HasProbabilityLaws Q K)
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hFresh : Regeneration.HasFreshBits Q Δ δ K)
    (lam R : ℝ) (hlam : 0 < lam) (hR : 0 < R) (i : Fin d)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hpassage : ∀ (m : ℕ) (A : Regeneration.CoupledSample d → ℝ),
      @Measurable (Regeneration.CoupledSample d) ℝ
        (Regeneration.finiteHistorySigma Δ m) inferInstance A →
      ∀ᵐ q ∂Regeneration.annealedCoupledLaw Q K,
        ∀ n, couplingScopePassage Δ lam R A m i n q.2 ≠ ⊤)
    (hwin : ∀ (m : ℕ) (A : Regeneration.CoupledSample d → ℝ),
      @Measurable (Regeneration.CoupledSample d) ℝ
        (Regeneration.finiteHistorySigma Δ m) inferInstance A →
      ∀ N,
        let μ := Regeneration.annealedCoupledLaw Q K
        let E := couplingScopeEvenGuardFailure Δ lam R A m i Set.univ N ∩
          {q | couplingScopePassage Δ lam R A m i (2 * N) q.2 ≠ ⊤}
        ε * μ.real E ≤ μ.real (E ∩
          {q | q.2 ∈ couplingScopeEvenGuard Δ lam R A m i N}))
 :
    ∀ᵐ q ∂Regeneration.annealedCoupledLaw Q K,
      Regeneration.trialStartSequence Δ lam R q.2 i 0 ≠ ⊤ ∧
        ∀ n : ℕ, Regeneration.trialFailureTime Δ R q.2 i
          (Regeneration.trialStartSequence Δ lam R q.2 i n) ≠ ⊤ →
            Regeneration.trialStartSequence Δ lam R q.2 i (n + 1) ≠ ⊤ := by
  have hfirst := coupling_scope_ae_successful_candidate_finite_of_guard_estimates
    Q K hK Δ hΔ δ hδ hδ1 hFresh lam R hlam hR i ε hε hε1 hpassage hwin
    0 (fun _ => 3 * lam * R) measurable_const
  have hrestart : ∀ᵐ q ∂Regeneration.annealedCoupledLaw Q K, ∀ m : ℕ,
      Regeneration.firstSuccessfulCandidate Δ lam R
        (couplingScopeRestartLevel Δ lam R m i q.2)
        (Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)) i ≠ ⊤ := by
    apply ae_all_iff.mpr
    intro m
    exact coupling_scope_ae_successful_candidate_finite_of_guard_estimates
      Q K hK Δ hΔ δ hδ hδ1 hFresh lam R hlam hR i ε hε hε1 hpassage hwin
      m (couplingScopeRestartLevel Δ lam R m i)
      (coupling_scope_measurable_restart_level_finiteHistory Δ lam R m i)
  filter_upwards [hfirst, hrestart] with q hbase hall
  simp only [Nat.cast_zero, zero_mul, Regeneration.sampleTimeShift_zero] at hbase
  exact coupling_scope_trial_entries_of_successful_candidates Δ lam R q.2 i hbase hall

/-- With no gaps at finite failed trials, infinite first regeneration is
exactly infinite entry into the literal full-trial sequence. The converse
uses actual attained regeneration trials and propagation of infinite failure. -/
theorem coupling_scope_first_regeneration_eq_top_iff_all_trials_finite {d : ℕ}
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (lam R : ℝ) (z : Regeneration.CoupledSample d) (i : Fin d)
    (hbase : Regeneration.trialStartSequence Δ lam R z i 0 ≠ ⊤)
    (hreentry : ∀ n : ℕ, Regeneration.trialFailureTime Δ R z i
      (Regeneration.trialStartSequence Δ lam R z i n) ≠ ⊤ →
        Regeneration.trialStartSequence Δ lam R z i (n + 1) ≠ ⊤) :
    Regeneration.firstRegenerationTime Δ lam R z i = ⊤ ↔
      ∀ n : ℕ, Regeneration.trialStartSequence Δ lam R z i n ≠ ⊤ := by
  constructor
  · intro htop n
    induction n with
    | zero => exact hbase
    | succ n ih =>
      apply hreentry n
      intro hfail
      have htrial : Regeneration.IsRegenerationTrial Δ lam R z i n := ⟨ih, hfail⟩
      have hle : Regeneration.firstRegenerationTime Δ lam R z i ≤
          Regeneration.trialStartSequence Δ lam R z i n :=
        iInf_le_of_le n (iInf_le_of_le htrial le_rfl)
      exact ih (top_le_iff.mp (htop ▸ hle))
  · intro hall
    by_contra hfin
    obtain ⟨n, hn, _⟩ := Regeneration.firstRegenerationTime_attained Δ hΔ lam R z i hfin
    exact hall (n + 1) (Regeneration.trialStartSequence_eq_top_after_infinite_failure
      Δ lam R z i n (n + 1) hn.2 (Nat.lt_succ_self n))

/-- A finite first actual successful candidate starts the first full trial
one grid interval later. This identifies the real last bit and prestart event. -/
theorem coupling_scope_first_trial_slice_of_successful_candidate {d : ℕ}
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (lam R : ℝ) (z : Regeneration.CoupledSample d)
    (i : Fin d) (m : ℕ)
    (hselected : Regeneration.firstSuccessfulCandidate Δ lam R (3 * lam * R) z i =
      (((m : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞)) :
    Regeneration.trialStartSequence Δ lam R z i 0 =
        ((((m + 1 : ℕ) : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞) ∧
      z ∈ Regeneration.forcedBitTrialEvent Δ lam R i m ∧ z.2 m = true := by
  have ht : Regeneration.trialStartSequence Δ lam R z i 0 =
      ((((m + 1 : ℕ) : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞) := by
    rw [Regeneration.trialStartSequence, hselected, Nat.cast_add, Nat.cast_one,
      add_mul, one_mul, ENNReal.coe_add]
  obtain ⟨hpre, hb⟩ :=
    (coupling_scope_trial_start_slice_iff Δ hΔ lam R z i 0 m).mp ht
  exact ⟨ht, ⟨0, hpre⟩, hb⟩

/-- No return after the selected bridge realizes the literal first
regeneration time. The original support condition is retained for every
point of the closed bridge interval, with the explicit Euclidean region. -/
theorem coupling_scope_first_regeneration_of_selected_bridge {d : ℕ}
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (lam R : ℝ) (z : Regeneration.CoupledSample d)
    (i : Fin d) (m : ℕ)
    (hselected : Regeneration.firstSuccessfulCandidate Δ lam R (3 * lam * R) z i =
      (((m : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞))
    (hbridge : ∀ n : ℕ, z.2 n = true → ∀ t : ℝ≥0,
      (n : ℝ≥0) * Δ ≤ t → t ≤ ((n + 1 : ℕ) : ℝ≥0) * Δ →
        z.1 t ∈ Regeneration.couplingRegion i R (z.1 ((n : ℝ≥0) * Δ)))
    (hD : Regeneration.NoBacktracking R
      (Regeneration.pathTimeShift z.1 (((m + 1 : ℕ) : ℝ≥0) * Δ)) i) :
    Regeneration.firstRegenerationTime Δ lam R z i =
        ((((m + 1 : ℕ) : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞) ∧
      z ∈ Regeneration.forcedBitTrialEvent Δ lam R i m ∧ z.2 m = true ∧
        ∀ t ∈ Set.Icc ((m : ℝ≥0) * Δ) (((m + 1 : ℕ) : ℝ≥0) * Δ),
          z.1 t ∈ Regeneration.couplingRegion i R (z.1 ((m : ℝ≥0) * Δ)) := by
  obtain ⟨_, hpre, hb⟩ :=
    coupling_scope_first_trial_slice_of_successful_candidate Δ hΔ lam R z i m hselected
  exact ⟨(Regeneration.firstRegenerationTime_eq_iff_forcedBitTrialEvent
    Δ hΔ lam R z i m).mpr ⟨hpre, hb, hD⟩,
    hpre, hb, fun t ht => hbridge m hb t ht.1 ht.2⟩

/-- Finite entry into a successor trial requires both a finite preceding
trial and an actual finite downward failure. Infinite starts cannot reappear. -/
theorem coupling_scope_trial_start_succ_finite_requires_failure {d : ℕ}
    (Δ : ℝ≥0) (lam R : ℝ) (z : Regeneration.CoupledSample d) (i : Fin d) (n : ℕ)
    (hsucc : Regeneration.trialStartSequence Δ lam R z i (n + 1) ≠ ⊤) :
    Regeneration.trialStartSequence Δ lam R z i n ≠ ⊤ ∧
      Regeneration.trialFailureTime Δ R z i
        (Regeneration.trialStartSequence Δ lam R z i n) ≠ ⊤ := by
  have hfail : Regeneration.trialFailureTime Δ R z i
      (Regeneration.trialStartSequence Δ lam R z i n) ≠ ⊤ := by
    intro htop
    apply hsucc
    rw [Regeneration.trialStartSequence, ite_eq_left htop]
  refine ⟨?_, hfail⟩
  intro htop
  apply hfail
  rw [Regeneration.trialFailureTime, Regeneration.trialDownwardTime, ite_eq_left htop,
    Regeneration.roundUp, ite_eq_left rfl]

/-- At an entered finite trial, the return-estimate event is exactly the
actual no-backtracking future after the bridge, with its original barrier. -/
theorem coupling_scope_trial_return_event_eq {d : ℕ} (Δ : ℝ≥0) (lam R : ℝ)
    (i : Fin d) (n : ℕ) :
    {q : FieldPair d × Regeneration.CoupledSample d |
      Regeneration.trialStartSequence Δ lam R q.2 i n ≠ ⊤} ∩
        {q | Regeneration.trialFailureTime Δ R q.2 i
          (Regeneration.trialStartSequence Δ lam R q.2 i n) = ⊤} =
      {q : FieldPair d × Regeneration.CoupledSample d |
        Regeneration.trialStartSequence Δ lam R q.2 i n ≠ ⊤} ∩
        {q | Regeneration.NoBacktracking R (Regeneration.pathTimeShift q.2.1
          (Regeneration.trialStartSequence Δ lam R q.2 i n).toNNReal) i} := by
  ext q
  constructor
  · rintro ⟨hfin, hfail⟩
    exact ⟨hfin, (Regeneration.trialFailureTime_eq_top_iff_noBacktracking
      Δ R q.2 i _ hfin).mp hfail⟩
  · rintro ⟨hfin, hD⟩
    exact ⟨hfin, (Regeneration.trialFailureTime_eq_top_iff_noBacktracking
      Δ R q.2 i _ hfin).mpr hD⟩

/-- A quantitative no-return bound on each entered actual trial gives the
finite-product bound for actual full-trial entry. This is a conditional
consumer; neither the no-return estimate nor the guard estimate is admitted. -/
theorem coupling_scope_finite_trial_product_of_return_estimate {d : ℕ}
    (μ : Measure (FieldPair d × Regeneration.CoupledSample d)) [IsProbabilityMeasure μ]
    (Δ : ℝ≥0) (lam R : ℝ) (i : Fin d) (η : ℝ) (hη : η ≤ 1)
    (hreturn : ∀ n : ℕ,
      let E := {q : FieldPair d × Regeneration.CoupledSample d |
        Regeneration.trialStartSequence Δ lam R q.2 i n ≠ ⊤}
      η * μ.real E ≤ μ.real (E ∩ {q | Regeneration.trialFailureTime Δ R q.2 i
        (Regeneration.trialStartSequence Δ lam R q.2 i n) = ⊤})) (N : ℕ) :
    μ {q | Regeneration.trialStartSequence Δ lam R q.2 i N ≠ ⊤} ≤
      ENNReal.ofReal (1 - η) ^ N *
        μ {q | Regeneration.trialStartSequence Δ lam R q.2 i 0 ≠ ⊤} := by
  have hstep (n : ℕ) :
      μ {q | Regeneration.trialStartSequence Δ lam R q.2 i (n + 1) ≠ ⊤} ≤
        ENNReal.ofReal (1 - η) *
          μ {q | Regeneration.trialStartSequence Δ lam R q.2 i n ≠ ⊤} := by
    have hmeas : MeasurableSet {q : FieldPair d × Regeneration.CoupledSample d |
        Regeneration.trialFailureTime Δ R q.2 i
          (Regeneration.trialStartSequence Δ lam R q.2 i n) = ⊤} :=
      measurableSet_eq_fun ((Regeneration.measurable_trialFailureTime Δ R i).comp
        (((Regeneration.measurable_trialStartSequence Δ lam R i n).comp measurable_snd).prodMk
          measurable_snd)) measurable_const
    apply le_trans (measure_mono ?_)
      (ConditionalTrialExhaustion.measure_sdiff_le_of_success_measure μ _ _ hmeas η hη
        (hreturn n))
    intro q hq
    exact coupling_scope_trial_start_succ_finite_requires_failure Δ lam R q.2 i n hq
  exact ConditionalTrialExhaustion.finite_product_of_failure_step μ
    (fun n => {q | Regeneration.trialStartSequence Δ lam R q.2 i n ≠ ⊤})
    (ENNReal.ofReal (1 - η)) hstep N

/-- A no-backtracking estimate for the actual shifted future gives the
finite-trial entry bound. The estimate remains an explicit input. -/
theorem coupling_scope_finite_trial_product_of_noBacktracking_estimate {d : ℕ}
    (μ : Measure (FieldPair d × Regeneration.CoupledSample d)) [IsProbabilityMeasure μ]
    (Δ : ℝ≥0) (lam R : ℝ) (i : Fin d) (η : ℝ) (hη : η ≤ 1)
    (hreturn : ∀ n : ℕ,
      let E := {q : FieldPair d × Regeneration.CoupledSample d |
        Regeneration.trialStartSequence Δ lam R q.2 i n ≠ ⊤}
      η * μ.real E ≤ μ.real (E ∩ {q | Regeneration.NoBacktracking R
        (Regeneration.pathTimeShift q.2.1
          (Regeneration.trialStartSequence Δ lam R q.2 i n).toNNReal) i})) (N : ℕ) :
    μ {q | Regeneration.trialStartSequence Δ lam R q.2 i N ≠ ⊤} ≤
      ENNReal.ofReal (1 - η) ^ N *
        μ {q | Regeneration.trialStartSequence Δ lam R q.2 i 0 ≠ ⊤} := by
  apply coupling_scope_finite_trial_product_of_return_estimate μ Δ lam R i η hη _ N
  intro n
  dsimp only
  rw [coupling_scope_trial_return_event_eq Δ lam R i n]
  exact hreturn n

/-- No-gap entry and a strict conditional no-return estimate exclude infinite
first regeneration. The estimated event is the literal infinite-failure event
at the entered trial; finiteness itself is not a hypothesis of the estimate. -/
theorem coupling_scope_ae_first_regeneration_finite_of_return_estimate {d : ℕ}
    (μ : Measure (FieldPair d × Regeneration.CoupledSample d)) [IsProbabilityMeasure μ]
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (lam R : ℝ) (i : Fin d)
    (hentry : ∀ᵐ q ∂μ, Regeneration.trialStartSequence Δ lam R q.2 i 0 ≠ ⊤ ∧
      ∀ n : ℕ, Regeneration.trialFailureTime Δ R q.2 i
        (Regeneration.trialStartSequence Δ lam R q.2 i n) ≠ ⊤ →
          Regeneration.trialStartSequence Δ lam R q.2 i (n + 1) ≠ ⊤)
    (η : ℝ) (hη : 0 < η) (hη1 : η ≤ 1)
    (hreturn : ∀ n : ℕ,
      let E := {q : FieldPair d × Regeneration.CoupledSample d |
        Regeneration.trialStartSequence Δ lam R q.2 i n ≠ ⊤}
      η * μ.real E ≤ μ.real (E ∩ {q | Regeneration.trialFailureTime Δ R q.2 i
        (Regeneration.trialStartSequence Δ lam R q.2 i n) = ⊤})) :
    ∀ᵐ q ∂μ, Regeneration.firstRegenerationTime Δ lam R q.2 i ≠ ⊤ := by
  let F := fun n : ℕ => {q : FieldPair d × Regeneration.CoupledSample d |
    Regeneration.trialStartSequence Δ lam R q.2 i n ≠ ⊤}
  have hnull : μ (⋂ n, F n) = 0 := by
    apply le_antisymm _ zero_le
    apply ge_of_tendsto' (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one
      (ENNReal.ofReal_lt_one.mpr (by linarith : 1 - η < 1)))
    intro n
    calc
      μ (⋂ k, F k) ≤ μ (F n) := measure_mono (Set.iInter_subset _ n)
      _ ≤ ENNReal.ofReal (1 - η) ^ n * μ (F 0) :=
        coupling_scope_finite_trial_product_of_return_estimate μ Δ lam R i η hη1 hreturn n
      _ ≤ ENNReal.ofReal (1 - η) ^ n * 1 := mul_le_mul_right prob_le_one _
      _ = ENNReal.ofReal (1 - η) ^ n := mul_one _
  have havoid : ∀ᵐ q ∂μ, q ∉ ⋂ n, F n := by
    rw [ae_iff]
    simpa only [not_not, Set.ofPred_mem_eq] using hnull
  filter_upwards [hentry, havoid] with q hq hnot
  intro htop
  apply hnot
  exact Set.mem_iInter.mpr
    ((coupling_scope_first_regeneration_eq_top_iff_all_trials_finite
      Δ hΔ lam R q.2 i hq.1 hq.2).mp htop)

/-- Mechanical first-regeneration exhaustion under the actual annealed
origin law. The two quantitative estimates and finite-passage transport remain
explicit internal producer obligations, not additional source-node premises.
In particular, the original nonzero-D witness alone is not used as a uniform
conditional no-return estimate at the actual entered trials. -/
theorem coupling_scope_ae_first_regeneration_finite_of_guard_and_return_estimates {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (K : Regeneration.CoupledQuenchedLaws d) (hK : Regeneration.HasProbabilityLaws Q K)
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hFresh : Regeneration.HasFreshBits Q Δ δ K)
    (lam R : ℝ) (hlam : 0 < lam) (hR : 0 < R) (i : Fin d)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hpassage : ∀ (m : ℕ) (A : Regeneration.CoupledSample d → ℝ),
      @Measurable (Regeneration.CoupledSample d) ℝ
        (Regeneration.finiteHistorySigma Δ m) inferInstance A →
      ∀ᵐ q ∂Regeneration.annealedCoupledLaw Q K,
        ∀ n, couplingScopePassage Δ lam R A m i n q.2 ≠ ⊤)
    (hwin : ∀ (m : ℕ) (A : Regeneration.CoupledSample d → ℝ),
      @Measurable (Regeneration.CoupledSample d) ℝ
        (Regeneration.finiteHistorySigma Δ m) inferInstance A →
      ∀ N,
        let μ := Regeneration.annealedCoupledLaw Q K
        let E := couplingScopeEvenGuardFailure Δ lam R A m i Set.univ N ∩
          {q | couplingScopePassage Δ lam R A m i (2 * N) q.2 ≠ ⊤}
        ε * μ.real E ≤ μ.real (E ∩
          {q | q.2 ∈ couplingScopeEvenGuard Δ lam R A m i N}))
    (η : ℝ) (hη : 0 < η) (hη1 : η ≤ 1)
    (hreturn : ∀ n : ℕ,
      let μ := Regeneration.annealedCoupledLaw Q K
      let E := {q : FieldPair d × Regeneration.CoupledSample d |
        Regeneration.trialStartSequence Δ lam R q.2 i n ≠ ⊤}
      η * μ.real E ≤ μ.real (E ∩ {q | Regeneration.NoBacktracking R
        (Regeneration.pathTimeShift q.2.1
          (Regeneration.trialStartSequence Δ lam R q.2 i n).toNNReal) i})) :
    ∀ᵐ q ∂Regeneration.annealedCoupledLaw Q K,
      Regeneration.firstRegenerationTime Δ lam R q.2 i ≠ ⊤ := by
  have : IsProbabilityMeasure (Regeneration.annealedCoupledLaw Q K) :=
    Regeneration.annealedCoupledLaw_isProbabilityMeasure Q K hK
  apply coupling_scope_ae_first_regeneration_finite_of_return_estimate
    (Regeneration.annealedCoupledLaw Q K) Δ hΔ lam R i
    (coupling_scope_ae_trial_entries_of_guard_estimates Q K hK Δ hΔ δ hδ hδ1 hFresh
      lam R hlam hR i ε hε hε1 hpassage hwin) η hη hη1
  intro n
  dsimp only
  rw [coupling_scope_trial_return_event_eq]
  exact hreturn n

open scoped Function

namespace ConditionalTrialExhaustion


end ConditionalTrialExhaustion

/-- Annealed history on field/path/coin pairs observes the path through `mΔ`
and exactly the bits strictly before `m`, through the sample projection. -/
@[instance_reducible]
def couplingScopeAnnealedHistory {d : ℕ} (Δ : ℝ≥0) (m : ℕ) :
    MeasurableSpace (FieldPair d × Regeneration.CoupledSample d) :=
  (Regeneration.finiteHistorySigma Δ m).comap Prod.snd

/-- The annealed deterministic history is a sub-sigma-algebra of the actual
field/path/coin measurable space. -/
theorem coupling_scope_annealed_history_le {d : ℕ} (Δ : ℝ≥0) (m : ℕ) :
    couplingScopeAnnealedHistory (d := d) Δ m ≤
      (inferInstance : MeasurableSpace (FieldPair d × Regeneration.CoupledSample d)) := by
  exact (MeasurableSpace.comap_mono (Probability.finiteHistorySigma_le Δ m)).trans
    measurable_snd.comap_le

/-- Full trial entry at `(m+1)Δ` is known at that endpoint. This uses the
prebridge at `mΔ` and the genuine bit `m`, which is included only at `m+1`. -/
theorem coupling_scope_measurableSet_trial_start_slice_annealedHistory {d : ℕ}
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (lam R : ℝ) (hR : 0 < R)
    (i : Fin d) (n m : ℕ) :
    @MeasurableSet (FieldPair d × Regeneration.CoupledSample d)
      (couplingScopeAnnealedHistory Δ (m + 1))
      {q | Regeneration.trialStartSequence Δ lam R q.2 i n =
        ((((m + 1 : ℕ) : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞)} := by
  have hpre := coupling_scope_measurableSet_trial_prebridge_finiteHistory
    Δ hΔ lam R hR i n m
  have hbit : @MeasurableSet (Regeneration.CoupledSample d)
      (Regeneration.finiteHistorySigma Δ (m + 1)) {z | z.2 m = true} := by
    have hb : @Measurable (Regeneration.CoupledSample d) Bool
        (Regeneration.finiteHistorySigma Δ (m + 1)) inferInstance (fun z => z.2 m) := by
      have hglobal : Measurable (fun z : Regeneration.CoupledSample d => z.2 m) :=
        (measurable_pi_apply m).comp measurable_snd
      have heq : (fun z : Regeneration.CoupledSample d => z.2 m) =
          (fun z => z.2 m) ∘ Probability.stoppedHistorySample Δ (m + 1) := by
        funext z
        exact (Probability.stoppedHistorySample_bit Δ (m + 1) z m
          (Nat.lt_succ_self m)).symm
      rw [heq]
      exact hglobal.comp (Probability.measurable_stoppedHistorySample Δ (m + 1))
    exact hb (measurableSet_singleton true)
  have hs : @MeasurableSet (Regeneration.CoupledSample d)
      (Regeneration.finiteHistorySigma Δ (m + 1))
      {z | Regeneration.trialStartSequence Δ lam R z i n =
        ((((m + 1 : ℕ) : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞)} := by
    have heq : {z | Regeneration.trialStartSequence Δ lam R z i n =
        ((((m + 1 : ℕ) : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞)} =
        couplingScopeTrialPrebridge Δ lam R i n m ∩ {z | z.2 m = true} := by
      ext z
      exact coupling_scope_trial_start_slice_iff Δ hΔ lam R z i n m
    rw [heq]
    exact (Regeneration.finiteHistorySigma_mono Δ (Nat.le_succ m) _ hpre).inter hbit
  exact hs.preimage (Measurable.of_comap_le le_rfl)

/-- Every finite full-trial entry has a unique positive deterministic grid
endpoint. This is a pathwise partition, including trials after failures. -/
theorem coupling_scope_trial_entry_eq_iUnion_slices {d : ℕ}
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (lam R : ℝ) (i : Fin d) (n : ℕ) :
    {q : FieldPair d × Regeneration.CoupledSample d |
      Regeneration.trialStartSequence Δ lam R q.2 i n ≠ ⊤} =
      ⋃ m : ℕ, {q | Regeneration.trialStartSequence Δ lam R q.2 i n =
        ((((m + 1 : ℕ) : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞)} := by
  ext q
  constructor
  · intro hfin
    obtain ⟨k, hk⟩ := Regeneration.trialStartSequence_mem_grid Δ hΔ lam R q.2 i n hfin
    cases k with
    | zero =>
      have hle := Regeneration.delta_le_trialStartSequence Δ lam R q.2 i n
      rw [hk, Nat.cast_zero, zero_mul, ENNReal.coe_zero] at hle
      exact (hΔ.ne' (ENNReal.coe_eq_zero.mp (le_zero_iff.mp hle))).elim
    | succ m => exact Set.mem_iUnion.mpr ⟨m, hk⟩
  · intro hq
    obtain ⟨m, hm⟩ := Set.mem_iUnion.mp hq
    change Regeneration.trialStartSequence Δ lam R q.2 i n ≠ ⊤
    rw [hm]
    exact ENNReal.coe_ne_top

/-- Distinct deterministic endpoints give disjoint slices for each actual
full trial, without independence or a regeneration-time restart. -/
theorem coupling_scope_trial_start_slices_pairwise_disjoint {d : ℕ}
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (lam R : ℝ) (i : Fin d) (n : ℕ) :
    Pairwise (Disjoint on (fun m : ℕ =>
      {q : FieldPair d × Regeneration.CoupledSample d |
        Regeneration.trialStartSequence Δ lam R q.2 i n =
          ((((m + 1 : ℕ) : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞)})) := by
  intro m k hmk
  apply Set.disjoint_left.mpr
  intro q hm hk
  have ht := ENNReal.coe_injective (hm.symm.trans hk)
  have hcast := mul_right_cancel₀ hΔ.ne' ht
  have hnat : m + 1 = k + 1 := by exact_mod_cast hcast
  exact hmk (Nat.add_right_cancel hnat)

/-- On an actual start slice, the literal infinite-failure event is exactly
no backtracking after the deterministic endpoint of that slice. -/
theorem coupling_scope_trial_return_slice_eq {d : ℕ} (Δ : ℝ≥0) (lam R : ℝ)
    (i : Fin d) (n m : ℕ) :
    {q : FieldPair d × Regeneration.CoupledSample d |
      Regeneration.trialStartSequence Δ lam R q.2 i n =
        ((((m + 1 : ℕ) : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞)} ∩
      {q | Regeneration.trialFailureTime Δ R q.2 i
        (Regeneration.trialStartSequence Δ lam R q.2 i n) = ⊤} =
    {q : FieldPair d × Regeneration.CoupledSample d |
      Regeneration.trialStartSequence Δ lam R q.2 i n =
        ((((m + 1 : ℕ) : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞)} ∩
      {q | Regeneration.NoBacktracking R
        (Regeneration.pathTimeShift q.2.1 (((m + 1 : ℕ) : ℝ≥0) * Δ)) i} := by
  ext q
  constructor
  · rintro ⟨hstart, hfail⟩
    have hfin : Regeneration.trialStartSequence Δ lam R q.2 i n ≠ ⊤ := by
      rw [hstart]
      exact ENNReal.coe_ne_top
    have hD := (Regeneration.trialFailureTime_eq_top_iff_noBacktracking
      Δ R q.2 i _ hfin).mp hfail
    rw [hstart, ENNReal.toNNReal_coe] at hD
    exact ⟨hstart, hD⟩
  · rintro ⟨hstart, hD⟩
    have hfin : Regeneration.trialStartSequence Δ lam R q.2 i n ≠ ⊤ := by
      rw [hstart]
      exact ENNReal.coe_ne_top
    refine ⟨hstart, (Regeneration.trialFailureTime_eq_top_iff_noBacktracking
      Δ R q.2 i _ hfin).mpr ?_⟩
    rwa [hstart, ENNReal.toNNReal_coe]

/-- Integrated lower bounds on the disjoint actual trial slices assemble
into a lower bound on finite entry of the whole trial. -/
theorem coupling_scope_return_estimate_of_slice_estimates {d : ℕ}
    (μ : Measure (FieldPair d × Regeneration.CoupledSample d)) [IsProbabilityMeasure μ]
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (lam R : ℝ) (i : Fin d) (η : ℝ) (hη : 0 ≤ η)
    (hlower : ∀ n m : ℕ,
      let S := {q : FieldPair d × Regeneration.CoupledSample d |
        Regeneration.trialStartSequence Δ lam R q.2 i n =
          ((((m + 1 : ℕ) : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞)}
      ENNReal.ofReal η * μ S ≤ μ (S ∩ {q | Regeneration.trialFailureTime Δ R q.2 i
        (Regeneration.trialStartSequence Δ lam R q.2 i n) = ⊤})) :
    ∀ n : ℕ,
      let E := {q : FieldPair d × Regeneration.CoupledSample d |
        Regeneration.trialStartSequence Δ lam R q.2 i n ≠ ⊤}
      η * μ.real E ≤ μ.real (E ∩ {q | Regeneration.trialFailureTime Δ R q.2 i
        (Regeneration.trialStartSequence Δ lam R q.2 i n) = ⊤}) := by
  intro n
  let E := {q : FieldPair d × Regeneration.CoupledSample d |
    Regeneration.trialStartSequence Δ lam R q.2 i n ≠ ⊤}
  let S := fun m : ℕ => {q : FieldPair d × Regeneration.CoupledSample d |
    Regeneration.trialStartSequence Δ lam R q.2 i n =
      ((((m + 1 : ℕ) : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞)}
  let F := {q : FieldPair d × Regeneration.CoupledSample d |
    Regeneration.trialFailureTime Δ R q.2 i
      (Regeneration.trialStartSequence Δ lam R q.2 i n) = ⊤}
  have hS (m : ℕ) : MeasurableSet (S m) :=
    measurableSet_eq_fun
      ((Regeneration.measurable_trialStartSequence Δ lam R i n).comp measurable_snd)
      measurable_const
  have hF : MeasurableSet F :=
    measurableSet_eq_fun ((Regeneration.measurable_trialFailureTime Δ R i).comp
      (((Regeneration.measurable_trialStartSequence Δ lam R i n).comp measurable_snd).prodMk
        measurable_snd)) measurable_const
  have hdis : Pairwise (Disjoint on S) :=
    coupling_scope_trial_start_slices_pairwise_disjoint Δ hΔ lam R i n
  have hdisF : Pairwise (Disjoint on (fun m => S m ∩ F)) := by
    intro m k hmk
    exact (hdis hmk).mono Set.inter_subset_left Set.inter_subset_left
  have hpart : E = ⋃ m, S m := coupling_scope_trial_entry_eq_iUnion_slices Δ hΔ lam R i n
  have hpartF : E ∩ F = ⋃ m, S m ∩ F := by
    rw [hpart, Set.iUnion_inter]
  have hbound : ENNReal.ofReal η * μ E ≤ μ (E ∩ F) := by
    calc
      ENNReal.ofReal η * μ E = ENNReal.ofReal η * ∑' m, μ (S m) := by
        rw [← measure_iUnion hdis hS, ← hpart]
      _ = ∑' m, ENNReal.ofReal η * μ (S m) := by rw [ENNReal.tsum_mul_left]
      _ ≤ ∑' m, μ (S m ∩ F) := ENNReal.tsum_le_tsum (hlower n)
      _ = μ (⋃ m, S m ∩ F) :=
        (measure_iUnion hdisF (fun m => (hS m).inter hF)).symm
      _ = μ (E ∩ F) := by rw [← hpartF]
  have hreal := (ENNReal.toReal_le_toReal
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top μ E))
    (measure_ne_top μ (E ∩ F))).mpr hbound
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hη, measureReal_def, E, F] using hreal

/-- A fixed-trial prebridge belongs to the actual annealed history before
bit `m` and before the whole successful bridge interval. -/
theorem coupling_scope_measurableSet_trial_prebridge_annealedHistory {d : ℕ}
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (lam R : ℝ) (hR : 0 < R) (i : Fin d) (n m : ℕ) :
    @MeasurableSet (FieldPair d × Regeneration.CoupledSample d)
      (couplingScopeAnnealedHistory Δ m)
      {q | q.2 ∈ couplingScopeTrialPrebridge Δ lam R i n m} :=
  (coupling_scope_measurableSet_trial_prebridge_finiteHistory Δ hΔ lam R hR i n m).preimage
    (Measurable.of_comap_le le_rfl)

/-- The actual fresh-bit identity converts a prebridge conditional success
bound for bit `m` together with no return after its bridge into the return
bound on the actual entered trial slice. The conditional estimate is an
unproved analytic input to this helper, with the original prebridge retained. -/
theorem coupling_scope_trial_slice_return_bound_of_prebridge_condExp {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (K : Regeneration.CoupledQuenchedLaws d) (hK : Regeneration.HasProbabilityLaws Q K)
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (δ : ℝ) (hδ : 0 ≤ δ)
    (hFresh : Regeneration.HasFreshBits Q Δ δ K)
    (lam R : ℝ) (hR : 0 < R) (i : Fin d) (η : ℝ) (hη : 0 ≤ η) (n m : ℕ)
    (hcond : ∀ᵐ q ∂Regeneration.annealedCoupledLaw Q K,
      q.2 ∈ couplingScopeTrialPrebridge Δ lam R i n m →
        δ * η ≤ ((Regeneration.annealedCoupledLaw Q K)[
          ({p : FieldPair d × Regeneration.CoupledSample d | p.2.2 m = true ∧
            Regeneration.NoBacktracking R
              (Regeneration.pathTimeShift p.2.1 (((m + 1 : ℕ) : ℝ≥0) * Δ)) i}).indicator
                (fun _ => (1 : ℝ)) | couplingScopeAnnealedHistory Δ m]) q) :
    let μ := Regeneration.annealedCoupledLaw Q K
    let S := {q : FieldPair d × Regeneration.CoupledSample d |
      Regeneration.trialStartSequence Δ lam R q.2 i n =
        ((((m + 1 : ℕ) : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞)}
    ENNReal.ofReal η * μ S ≤ μ (S ∩ {q | Regeneration.trialFailureTime Δ R q.2 i
      (Regeneration.trialStartSequence Δ lam R q.2 i n) = ⊤}) := by
  have : IsProbabilityMeasure (Regeneration.annealedCoupledLaw Q K) :=
    Regeneration.annealedCoupledLaw_isProbabilityMeasure Q K hK
  let μ := Regeneration.annealedCoupledLaw Q K
  let A := {q : FieldPair d × Regeneration.CoupledSample d |
    q.2 ∈ couplingScopeTrialPrebridge Δ lam R i n m}
  let S := {q : FieldPair d × Regeneration.CoupledSample d |
    Regeneration.trialStartSequence Δ lam R q.2 i n =
      ((((m + 1 : ℕ) : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞)}
  let G := {q : FieldPair d × Regeneration.CoupledSample d |
    Regeneration.NoBacktracking R
      (Regeneration.pathTimeShift q.2.1 (((m + 1 : ℕ) : ℝ≥0) * Δ)) i}
  let B := {q : FieldPair d × Regeneration.CoupledSample d | q.2.2 m = true} ∩ G
  have hG : MeasurableSet G :=
    (Regeneration.measurableSet_NoBacktracking R i).preimage
      (Probability.continuous_path_time_shift.measurable.comp
        (measurable_const.prodMk measurable_snd.fst))
  have hB : MeasurableSet B :=
    (measurableSet_eq_fun ((measurable_pi_apply m).comp measurable_snd.snd)
      measurable_const).inter hG
  have hwin : ENNReal.ofReal (δ * η) * μ A ≤ μ (A ∩ B) :=
    ConditionalTrialExhaustion.measure_inter_ge_of_condExp μ
      (couplingScopeAnnealedHistory Δ m) (coupling_scope_annealed_history_le Δ m) A B
      (coupling_scope_measurableSet_trial_prebridge_annealedHistory Δ hΔ lam R hR i n m)
      hB (δ * η) (mul_nonneg hδ hη) hcond
  have hmass : μ S = ENNReal.ofReal δ * μ A :=
    coupling_scope_measure_trial_start_slice Q K hK Δ hΔ δ hδ hFresh lam R hR i n m
  have hsuccess : A ∩ B = S ∩ G := by
    ext q
    change (q.2 ∈ couplingScopeTrialPrebridge Δ lam R i n m ∧
      q.2.2 m = true ∧ q ∈ G) ↔
      (Regeneration.trialStartSequence Δ lam R q.2 i n =
        ((((m + 1 : ℕ) : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞) ∧ q ∈ G)
    rw [coupling_scope_trial_start_slice_iff Δ hΔ lam R q.2 i n m]
    exact and_assoc.symm
  change ENNReal.ofReal η * μ S ≤ _
  calc
    ENNReal.ofReal η * μ S = ENNReal.ofReal (δ * η) * μ A := by
      rw [hmass, ENNReal.ofReal_mul hδ]
      ac_rfl
    _ ≤ μ (A ∩ B) := hwin
    _ = μ (S ∩ G) := by rw [hsuccess]
    _ = _ := congrArg μ (coupling_scope_trial_return_slice_eq Δ lam R i n m).symm

/-- Prebridge conditional bounds on the actual origin law give the integrated
return estimate needed by literal full-trial exhaustion. Freshness and all
countable slice bookkeeping are supplied here. -/
theorem coupling_scope_return_estimate_of_prebridge_condExp {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (K : Regeneration.CoupledQuenchedLaws d) (hK : Regeneration.HasProbabilityLaws Q K)
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (δ : ℝ) (hδ : 0 ≤ δ)
    (hFresh : Regeneration.HasFreshBits Q Δ δ K)
    (lam R : ℝ) (hR : 0 < R) (i : Fin d) (η : ℝ) (hη : 0 ≤ η)
    (hcond : ∀ n m : ℕ, ∀ᵐ q ∂Regeneration.annealedCoupledLaw Q K,
      q.2 ∈ couplingScopeTrialPrebridge Δ lam R i n m →
        δ * η ≤ ((Regeneration.annealedCoupledLaw Q K)[
          ({p : FieldPair d × Regeneration.CoupledSample d | p.2.2 m = true ∧
            Regeneration.NoBacktracking R
              (Regeneration.pathTimeShift p.2.1 (((m + 1 : ℕ) : ℝ≥0) * Δ)) i}).indicator
                (fun _ => (1 : ℝ)) | couplingScopeAnnealedHistory Δ m]) q) :
    ∀ n : ℕ,
      let μ := Regeneration.annealedCoupledLaw Q K
      let E := {q : FieldPair d × Regeneration.CoupledSample d |
        Regeneration.trialStartSequence Δ lam R q.2 i n ≠ ⊤}
      η * μ.real E ≤ μ.real (E ∩ {q | Regeneration.trialFailureTime Δ R q.2 i
        (Regeneration.trialStartSequence Δ lam R q.2 i n) = ⊤}) := by
  have : IsProbabilityMeasure (Regeneration.annealedCoupledLaw Q K) :=
    Regeneration.annealedCoupledLaw_isProbabilityMeasure Q K hK
  exact coupling_scope_return_estimate_of_slice_estimates
    (Regeneration.annealedCoupledLaw Q K) Δ hΔ lam R i η hη
    (fun n m => coupling_scope_trial_slice_return_bound_of_prebridge_condExp
      Q K hK Δ hΔ δ hδ hFresh lam R hR i η hη n m (hcond n m))

/-- Prebridge conditional no-return estimates and no-gap actual trial entry
imply literal first-regeneration finiteness under the actual annealed law. -/
theorem coupling_scope_ae_first_regeneration_finite_of_prebridge_condExp {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (K : Regeneration.CoupledQuenchedLaws d) (hK : Regeneration.HasProbabilityLaws Q K)
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (δ : ℝ) (hδ : 0 ≤ δ)
    (hFresh : Regeneration.HasFreshBits Q Δ δ K)
    (lam R : ℝ) (hR : 0 < R) (i : Fin d)
    (hentry : ∀ᵐ q ∂Regeneration.annealedCoupledLaw Q K,
      Regeneration.trialStartSequence Δ lam R q.2 i 0 ≠ ⊤ ∧
        ∀ n : ℕ, Regeneration.trialFailureTime Δ R q.2 i
          (Regeneration.trialStartSequence Δ lam R q.2 i n) ≠ ⊤ →
            Regeneration.trialStartSequence Δ lam R q.2 i (n + 1) ≠ ⊤)
    (η : ℝ) (hη : 0 < η) (hη1 : η ≤ 1)
    (hcond : ∀ n m : ℕ, ∀ᵐ q ∂Regeneration.annealedCoupledLaw Q K,
      q.2 ∈ couplingScopeTrialPrebridge Δ lam R i n m →
        δ * η ≤ ((Regeneration.annealedCoupledLaw Q K)[
          ({p : FieldPair d × Regeneration.CoupledSample d | p.2.2 m = true ∧
            Regeneration.NoBacktracking R
              (Regeneration.pathTimeShift p.2.1 (((m + 1 : ℕ) : ℝ≥0) * Δ)) i}).indicator
                (fun _ => (1 : ℝ)) | couplingScopeAnnealedHistory Δ m]) q) :
    ∀ᵐ q ∂Regeneration.annealedCoupledLaw Q K,
      Regeneration.firstRegenerationTime Δ lam R q.2 i ≠ ⊤ := by
  have : IsProbabilityMeasure (Regeneration.annealedCoupledLaw Q K) :=
    Regeneration.annealedCoupledLaw_isProbabilityMeasure Q K hK
  exact coupling_scope_ae_first_regeneration_finite_of_return_estimate
    (Regeneration.annealedCoupledLaw Q K) Δ hΔ lam R i hentry η hη hη1
    (coupling_scope_return_estimate_of_prebridge_condExp Q K hK
      Δ hΔ δ hδ hFresh lam R hR i η hη.le hcond)

namespace ConditionalTrialExhaustion

/-- A strictly positive limiting coordinate velocity forces that coordinate
to escape to positive infinity along the actual continuous path. -/
theorem directional_escape_of_positive_velocity {d : ℕ}
    (γ : Path d) (v : Vec d) (i : Fin d)
    (hv : HasPathVelocity γ v) (hpos : 0 < v i) :
    Filter.Tendsto (fun t : ℝ≥0 => γ t i) Filter.atTop Filter.atTop := by
  have hcoord : Filter.Tendsto (fun t : ℝ≥0 => (t : ℝ)⁻¹ * γ t i)
      Filter.atTop (nhds (v i)) :=
    ((continuous_apply i).tendsto v).comp hv
  have hmul := hcoord.pos_mul_atTop hpos
    (NNReal.tendsto_coe_atTop.mpr Filter.tendsto_id)
  apply hmul.congr'
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ≥0)] with t ht
  have ht' : (t : ℝ) ≠ 0 := ne_of_gt (NNReal.coe_pos.mpr ht)
  change (t : ℝ)⁻¹ * γ t i * (t : ℝ) = γ t i
  rw [mul_comm ((t : ℝ)⁻¹ * γ t i), ← mul_assoc, mul_inv_cancel₀ ht', one_mul]

/-- A finite restart preserves directional escape; no stopping or Markov
property is used, and the restart may be chosen from the realized path. -/
theorem directional_escape_pathTimeShift {d : ℕ} (γ : Path d) (i : Fin d)
    (hescape : Filter.Tendsto (fun t : ℝ≥0 => γ t i) Filter.atTop Filter.atTop)
    (s : ℝ≥0) :
    Filter.Tendsto (fun t : ℝ≥0 => (Regeneration.pathTimeShift γ s) t i)
      Filter.atTop Filter.atTop := by
  exact hescape.comp (Filter.tendsto_atTop_mono
    (fun _t : ℝ≥0 => le_add_of_nonneg_left (show 0 ≤ s from zero_le))
    Filter.tendsto_id)

/-- Escape supplies a crossing of every finite real level, hence the literal
extended infimum is finite, including nonpositive thresholds. -/
theorem firstHittingAbove_ne_top_of_escape {d : ℕ} (γ : Path d) (i : Fin d)
    (hescape : Filter.Tendsto (fun t : ℝ≥0 => γ t i) Filter.atTop Filter.atTop)
    (a : ℝ) : Regeneration.firstHittingAbove γ i a ≠ ⊤ := by
  obtain ⟨t, ht⟩ := (hescape.eventually_ge_atTop (a + γ 0 i)).exists
  have hcross : a ≤ γ t i - γ 0 i := by linarith only [ht]
  exact ne_top_of_le_ne_top ENNReal.coe_ne_top
    (Regeneration.firstHittingAbove_le_of_crossing γ i a t hcross)

/-- Continuity closes the weak crossing set, so a finite actual hitting
time is itself a crossing. No strict-threshold convention is substituted. -/
theorem crossing_at_firstHittingAbove_of_ne_top {d : ℕ}
    (γ : Path d) (i : Fin d) (a : ℝ)
    (hfinite : Regeneration.firstHittingAbove γ i a ≠ ⊤) :
    a ≤ γ (Regeneration.firstHittingAbove γ i a).toNNReal i - γ 0 i := by
  have htime : Regeneration.firstHittingAbove γ i a ≤
      ((Regeneration.firstHittingAbove γ i a).toNNReal : ℝ≥0∞) :=
    (ENNReal.coe_toNNReal hfinite).symm.le
  obtain ⟨u, hu, hcross⟩ :=
    (Regeneration.firstHittingAbove_le_iff γ i a _).mp htime
  have hle := Regeneration.firstHittingAbove_le_of_crossing γ i a u hcross
  rw [← ENNReal.coe_toNNReal hfinite, ENNReal.coe_le_coe] at hle
  have heq : u = (Regeneration.firstHittingAbove γ i a).toNNReal :=
    le_antisymm hu.2 hle
  exact heq ▸ hcross

/-- A finite rounding stays finite with the source's literal ceiling rule. -/
theorem roundUp_ne_top (Δ : ℝ≥0) (t : ℝ≥0∞) (ht : t ≠ ⊤) :
    Regeneration.roundUp Δ t ≠ ⊤ := by
  rw [Regeneration.roundUp, ite_eq_right ht]
  exact ENNReal.coe_ne_top

/-- Induction uses the actual finite running maximum at the rounded previous
passage. Escape suffices for every selected level without a guard estimate. -/
theorem passageSequence_ne_top_of_escape {d : ℕ} (Δ : ℝ≥0) (lam R a : ℝ)
    (γ : Path d) (i : Fin d)
    (hescape : Filter.Tendsto (fun t : ℝ≥0 => γ t i) Filter.atTop Filter.atTop)
    (n : ℕ) : Regeneration.passageSequence Δ lam R a γ i n ≠ ⊤ := by
  induction n with
  | zero => exact firstHittingAbove_ne_top_of_escape γ i hescape (a / lam)
  | succ n ih =>
    rw [Regeneration.passageSequence, ite_eq_right (roundUp_ne_top Δ _ ih)]
    exact firstHittingAbove_ne_top_of_escape γ i hescape _

/-- Each next selected passage attains its actual running-maximum threshold.
The threshold is taken after rounding the preceding passage exactly as in
the source recursion. -/
theorem passageSequence_next_attained_of_escape {d : ℕ}
    (Δ : ℝ≥0) (lam R a : ℝ) (γ : Path d) (i : Fin d)
    (hescape : Filter.Tendsto (fun t : ℝ≥0 => γ t i) Filter.atTop Filter.atTop)
    (n : ℕ) :
    ∃ t : ℝ≥0, Regeneration.passageSequence Δ lam R a γ i (n + 1) =
      (t : ℝ≥0∞) ∧
      Regeneration.coordinateMaximum γ i
        (Regeneration.roundUp Δ (Regeneration.passageSequence Δ lam R a γ i n)).toNNReal
          + R ≤ γ t i - γ 0 i := by
  have hn := passageSequence_ne_top_of_escape Δ lam R a γ i hescape n
  have hnext := passageSequence_ne_top_of_escape Δ lam R a γ i hescape (n + 1)
  refine ⟨(Regeneration.passageSequence Δ lam R a γ i (n + 1)).toNNReal,
    (ENNReal.coe_toNNReal hnext).symm, ?_⟩
  rw [Regeneration.passageSequence, ite_eq_right (roundUp_ne_top Δ _ hn)] at hnext ⊢
  exact crossing_at_firstHittingAbove_of_ne_top γ i _ hnext

/-- The actual passages are finite after every finite restart, including
path-dependent restart times and levels on the same escaping path. -/
theorem shifted_passageSequence_ne_top_of_escape {d : ℕ}
    (Δ : ℝ≥0) (lam R : ℝ) (γ : Path d) (i : Fin d)
    (hescape : Filter.Tendsto (fun t : ℝ≥0 => γ t i) Filter.atTop Filter.atTop)
    (s : ℝ≥0) (a : ℝ) (n : ℕ) :
    Regeneration.passageSequence Δ lam R a (Regeneration.pathTimeShift γ s) i n ≠ ⊤ :=
  passageSequence_ne_top_of_escape Δ lam R a _ i
    (directional_escape_pathTimeShift γ i hescape s) n

/-- After any finite restart the first hit is finite and attained, with the
actual displacement measured from that restart position. -/
theorem shifted_firstHittingAbove_attained_of_escape {d : ℕ}
    (γ : Path d) (i : Fin d)
    (hescape : Filter.Tendsto (fun t : ℝ≥0 => γ t i) Filter.atTop Filter.atTop)
    (s : ℝ≥0) (a : ℝ) :
    ∃ t : ℝ≥0, Regeneration.firstHittingAbove (Regeneration.pathTimeShift γ s) i a =
      (t : ℝ≥0∞) ∧ a ≤ γ (s + t) i - γ s i := by
  have hf := firstHittingAbove_ne_top_of_escape _ i
    (directional_escape_pathTimeShift γ i hescape s) a
  refine ⟨(Regeneration.firstHittingAbove (Regeneration.pathTimeShift γ s) i a).toNNReal,
    (ENNReal.coe_toNNReal hf).symm, ?_⟩
  simpa only [Regeneration.pathTimeShift, ContinuousMap.coe_mk, add_zero] using
    crossing_at_firstHittingAbove_of_ne_top (Regeneration.pathTimeShift γ s) i a hf

/-- For a positive spatial gap each attained next selected passage is strictly
later than the preceding rounded endpoint, as required by the source guard. -/
theorem rounded_passage_lt_next_of_escape {d : ℕ}
    (Δ : ℝ≥0) (lam R a : ℝ) (hR : 0 < R) (γ : Path d) (i : Fin d)
    (hescape : Filter.Tendsto (fun t : ℝ≥0 => γ t i) Filter.atTop Filter.atTop)
    (n : ℕ) :
    Regeneration.roundUp Δ (Regeneration.passageSequence Δ lam R a γ i n) <
      Regeneration.passageSequence Δ lam R a γ i (n + 1) :=
  Regeneration.rounded_passage_lt_next Δ lam R a hR γ i n
    (roundUp_ne_top Δ _ (passageSequence_ne_top_of_escape Δ lam R a γ i hescape n))

end ConditionalTrialExhaustion

/-- One almost-everywhere escape event supplies every actual grid-restarted
passage simultaneously. The level may be any function of the realized sample;
no uncountable intersection of almost-everywhere events is taken. -/
theorem coupling_scope_ae_passages_finite_of_escape {d : ℕ}
    (μ : Measure (FieldPair d × Regeneration.CoupledSample d))
    (Δ : ℝ≥0) (lam R : ℝ) (i : Fin d)
    (hescape : ∀ᵐ q ∂μ,
      Filter.Tendsto (fun t : ℝ≥0 => q.2.1 t i) Filter.atTop Filter.atTop) :
    ∀ᵐ q ∂μ, ∀ (m : ℕ) (A : Regeneration.CoupledSample d → ℝ) (n : ℕ),
      couplingScopePassage Δ lam R A m i n q.2 ≠ ⊤ := by
  filter_upwards [hescape] with q hq m A n
  exact ConditionalTrialExhaustion.shifted_passageSequence_ne_top_of_escape
    Δ lam R q.2.1 i hq ((m : ℝ≥0) * Δ) (A q.2) n

/-- A positive limiting velocity under the actual joint law supplies the
common escape event used by all restart and guard indices. -/
theorem coupling_scope_ae_passages_finite_of_positive_velocity {d : ℕ}
    (μ : Measure (FieldPair d × Regeneration.CoupledSample d))
    (Δ : ℝ≥0) (lam R : ℝ) (i : Fin d) (v : Vec d) (hpos : 0 < v i)
    (hv : ∀ᵐ q ∂μ, HasPathVelocity q.2.1 v) :
    ∀ᵐ q ∂μ, ∀ (m : ℕ) (A : Regeneration.CoupledSample d → ℝ) (n : ℕ),
      couplingScopePassage Δ lam R A m i n q.2 ≠ ⊤ := by
  apply coupling_scope_ae_passages_finite_of_escape μ Δ lam R i
  filter_upwards [hv] with q hq
  exact ConditionalTrialExhaustion.directional_escape_of_positive_velocity q.2.1 v i hq hpos

/-- A positive velocity for the supplied origin path law passes through the
literal path marginal to finite actual passages under the joint coupled law.
This assumes the velocity of that very supplied law; it makes no physical to
reduced law identification. Measurability is required only for the level and
the countable family of actual finite-passage events. -/
theorem coupling_scope_ae_passages_finite_of_quenched_positive_velocity {d : ℕ}
    (Q : Measure (FieldPair d))
    (K : Regeneration.CoupledQuenchedLaws d) (hK : Regeneration.HasProbabilityLaws Q K)
    (P : QuenchedPathLaws d) (hpath : Regeneration.HasPathMarginals Q K P)
    (v : Vec d) (i : Fin d) (hpos : 0 < v i)
    (hv : HasQuenchedVelocity Q (originLaw P) v)
    (Δ : ℝ≥0) (lam R : ℝ) (A : Regeneration.CoupledSample d → ℝ)
    (hA : Measurable A) (m : ℕ) :
    ∀ᵐ q ∂Regeneration.annealedCoupledLaw Q K,
      ∀ n, couplingScopePassage Δ lam R A m i n q.2 ≠ ⊤ := by
  have hmeas : MeasurableSet {q : FieldPair d × Regeneration.CoupledSample d |
      ∀ n, couplingScopePassage Δ lam R A m i n q.2 ≠ ⊤} := by
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun n =>
      ((measurableSet_singleton (⊤ : ℝ≥0∞)).preimage
        ((coupling_scope_measurable_passage Δ lam R A hA m i n).comp measurable_snd)).compl
  apply Measure.ae_compProd_of_ae_ae hmeas
  filter_upwards [hK.1, hpath.1, hv] with ω hprob hmap hvel
  let : IsProbabilityMeasure (Regeneration.originCoupledLaw K ω) := hprob
  rw [Probability.probabilityPart_eq_of_isProbabilityMeasure
    (Regeneration.originCoupledLaw K) ω]
  have hcoupled : ∀ᵐ z ∂K (0, ω), HasPathVelocity z.1 v := by
    have hmapvel : ∀ᵐ γ ∂(K (0, ω)).map Prod.fst, HasPathVelocity γ v := by
      rw [hmap]
      exact hvel
    exact ae_of_ae_map measurable_fst.aemeasurable hmapvel
  filter_upwards [hcoupled] with z hz n
  exact ConditionalTrialExhaustion.shifted_passageSequence_ne_top_of_escape
    Δ lam R z.1 i
    (ConditionalTrialExhaustion.directional_escape_of_positive_velocity z.1 v i hz hpos)
    ((m : ℝ≥0) * Δ) (A z) n

/-- The approved GMP input supplies finite passages of its physical origin
process after all finite restarts. This conclusion stays under that physical
law; applying it to a supplied reduced law requires internal law transport. -/
theorem coupling_scope_gmp_physical_origin_passages_finite {d : ℕ}
    (hd : 2 ≤ d) {L r : ℝ} (Q : EnvironmentLaw d L r)
    {lam : ℝ} (h₀ : 0 < lam) (h₁ : lam ≤ 1)
    (P : ProbabilityTheory.Kernel (FieldPair d) (Path d))
    (hP : IsGMPPhysicalOriginLaw hd Q.ellipticity_parameter Q lam h₀.le h₁ P)
    (Δ : ℝ≥0) (R : ℝ) :
    ∀ᵐ ω ∂Q.measure, ∀ᵐ γ ∂P ω, ∀ (s : ℝ≥0) (a : ℝ) (n : ℕ),
      Regeneration.passageSequence Δ lam R a (Regeneration.pathTimeShift γ s)
        (EinsteinRelation.External.GantertSection7Support.firstCoordinateIndex hd) n ≠ ⊤ := by
  obtain ⟨v, hv, hpos, _hunique⟩ :=
    EinsteinFull.Regeneration.gmp_physical_origin_velocity hd Q h₀ h₁ P hP
  filter_upwards [hv] with ω hω
  filter_upwards [hω] with γ hγ s a n
  exact ConditionalTrialExhaustion.shifted_passageSequence_ne_top_of_escape
    Δ lam R γ (EinsteinRelation.External.GantertSection7Support.firstCoordinateIndex hd)
    (ConditionalTrialExhaustion.directional_escape_of_positive_velocity
      γ v (EinsteinRelation.External.GantertSection7Support.firstCoordinateIndex hd)
      hγ hpos) s a n

/-- Actual path escape discharges the predecessor's finite-passage obligation.
Uniform integrated guard estimates remain explicit analytic obligations; this
conditional helper does not assert the source-node reduction. -/
theorem coupling_scope_ae_candidates_finite_of_escape_and_guard_estimates {d : ℕ}
    (μ : Measure (FieldPair d × Regeneration.CoupledSample d)) [IsProbabilityMeasure μ]
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (lam R : ℝ) (i : Fin d)
    (hescape : ∀ᵐ q ∂μ,
      Filter.Tendsto (fun t : ℝ≥0 => q.2.1 t i) Filter.atTop Filter.atTop)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hwin : ∀ (m : ℕ) (A : Regeneration.CoupledSample d → ℝ),
      @Measurable (Regeneration.CoupledSample d) ℝ
        (Regeneration.finiteHistorySigma Δ m) inferInstance A →
      ∀ N,
        let E := couplingScopeEvenGuardFailure Δ lam R A m i Set.univ N ∩
          {q | couplingScopePassage Δ lam R A m i (2 * N) q.2 ≠ ⊤}
        ε * μ.real E ≤ μ.real (E ∩
          {q | q.2 ∈ couplingScopeEvenGuard Δ lam R A m i N}))
    (m : ℕ) (A : Regeneration.CoupledSample d → ℝ)
    (hA : @Measurable (Regeneration.CoupledSample d) ℝ
      (Regeneration.finiteHistorySigma Δ m) inferInstance A) :
    ∀ᵐ q ∂μ, ∀ N, couplingScopeCandidate Δ lam R A m i N q.2 ≠ ⊤ := by
  apply coupling_scope_ae_candidates_finite_of_guard_estimates
    μ Δ hΔ lam R i ε hε hε1 _ hwin m A hA
  intro m' A' _hA'
  filter_upwards [coupling_scope_ae_passages_finite_of_escape μ Δ lam R i hescape]
    with q hq n
  exact hq m' A' n

/-- Once the supplied path law has positive velocity, the actual path marginal
discharges every finite-passage premise in the predecessor's candidate
consumer. Producing the uniform guard estimate and identifying the supplied
reduced law with the physical velocity law remain separate internal work. -/
theorem coupling_scope_ae_candidates_finite_of_quenched_velocity_and_guard_estimates {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (K : Regeneration.CoupledQuenchedLaws d) (hK : Regeneration.HasProbabilityLaws Q K)
    (P : QuenchedPathLaws d) (hpath : Regeneration.HasPathMarginals Q K P)
    (v : Vec d) (i : Fin d) (hpos : 0 < v i)
    (hv : HasQuenchedVelocity Q (originLaw P) v)
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (lam R : ℝ)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hwin : ∀ (m : ℕ) (A : Regeneration.CoupledSample d → ℝ),
      @Measurable (Regeneration.CoupledSample d) ℝ
        (Regeneration.finiteHistorySigma Δ m) inferInstance A →
      ∀ N,
        let μ := Regeneration.annealedCoupledLaw Q K
        let E := couplingScopeEvenGuardFailure Δ lam R A m i Set.univ N ∩
          {q | couplingScopePassage Δ lam R A m i (2 * N) q.2 ≠ ⊤}
        ε * μ.real E ≤ μ.real (E ∩
          {q | q.2 ∈ couplingScopeEvenGuard Δ lam R A m i N}))
    (m : ℕ) (A : Regeneration.CoupledSample d → ℝ)
    (hA : @Measurable (Regeneration.CoupledSample d) ℝ
      (Regeneration.finiteHistorySigma Δ m) inferInstance A) :
    ∀ᵐ q ∂Regeneration.annealedCoupledLaw Q K,
      ∀ N, couplingScopeCandidate Δ lam R A m i N q.2 ≠ ⊤ := by
  let : IsProbabilityMeasure (Regeneration.annealedCoupledLaw Q K) :=
    Regeneration.annealedCoupledLaw_isProbabilityMeasure Q K hK
  apply coupling_scope_ae_candidates_finite_of_guard_estimates
    (Regeneration.annealedCoupledLaw Q K) Δ hΔ lam R i ε hε hε1 _ hwin m A hA
  intro m' A' hA'
  exact coupling_scope_ae_passages_finite_of_quenched_positive_velocity
    Q K hK P hpath v i hpos hv Δ lam R A'
    (hA'.mono (Probability.finiteHistorySigma_le Δ m') le_rfl) m'

/-- Two deterministic grid shifts retain the actual path and the actual bit
indices. No restart law or independence assertion is involved. -/
theorem coupling_scope_sample_restart_add {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ)
    (z : Regeneration.CoupledSample d) (m k : ℕ) :
    Regeneration.sampleTimeShift Δ
      (Regeneration.sampleTimeShift Δ z ((m : ℝ≥0) * Δ)) ((k : ℝ≥0) * Δ) =
      Regeneration.sampleTimeShift Δ z (((m + k : ℕ) : ℝ≥0) * Δ) := by
  apply Prod.ext
  · exact coupling_scope_path_restart_add Δ z m k
  · funext n
    change z.2 (Regeneration.gridIndex Δ ((m : ℝ≥0) * Δ) +
      (Regeneration.gridIndex Δ ((k : ℝ≥0) * Δ) + n)) =
      z.2 (Regeneration.gridIndex Δ (((m + k : ℕ) : ℝ≥0) * Δ) + n)
    rw [Regeneration.gridIndex_mul Δ hΔ m, Regeneration.gridIndex_mul Δ hΔ k,
      Regeneration.gridIndex_mul Δ hΔ (m + k), Nat.add_assoc]

/-- The literal failure-restart level in a trial begun after `mΔ`, evaluated
at relative failure index `k`. Its history ends at absolute index `m+k`. -/
noncomputable def couplingScopeSelectedRestartLevel {d : ℕ} (Δ : ℝ≥0) (lam R : ℝ)
    (m k : ℕ) (i : Fin d) (z : Regeneration.CoupledSample d) : ℝ :=
  couplingScopeRestartLevel Δ lam R k i
    (Regeneration.sampleTimeShift Δ z ((m : ℝ≥0) * Δ))

/-- Selected levels use the shifted running maximum and the original
absolute endpoint; the displacement sign agrees with the source recursion. -/
theorem coupling_scope_selected_restart_level_eq {d : ℕ} (Δ : ℝ≥0) (lam R : ℝ)
    (m k : ℕ) (i : Fin d) (z : Regeneration.CoupledSample d) :
    couplingScopeSelectedRestartLevel Δ lam R m k i z = lam *
      (Regeneration.coordinateMaximum
        (Regeneration.pathTimeShift z.1 ((m : ℝ≥0) * Δ)) i ((k : ℝ≥0) * Δ) -
        (z.1 (((m + k : ℕ) : ℝ≥0) * Δ) i - z.1 ((m : ℝ≥0) * Δ) i) + R) := by
  unfold couplingScopeSelectedRestartLevel couplingScopeRestartLevel
  simp only [Regeneration.sampleTimeShift, Regeneration.pathTimeShift, ContinuousMap.coe_mk,
    add_zero, Nat.cast_add, add_mul]

/-- The exact selected level is measurable before the bit at absolute
failure index `m+k`; no new measurability premise is assumed. -/
theorem coupling_scope_measurable_selected_restart_level_finiteHistory {d : ℕ}
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (lam R : ℝ) (m k : ℕ) (i : Fin d) :
    @Measurable (Regeneration.CoupledSample d) ℝ
      (Regeneration.finiteHistorySigma Δ (m + k)) inferInstance
      (couplingScopeSelectedRestartLevel Δ lam R m k i) :=
  Probability.measurable_finiteHistory_grid_shift_test Δ hΔ m k _
    (coupling_scope_measurable_restart_level_finiteHistory Δ lam R k i)

/-- The selected source level divided by the positive force is strictly
positive, by the actual shifted running-maximum bound. -/
theorem coupling_scope_selected_restart_level_div_pos {d : ℕ}
    (Δ : ℝ≥0) (lam R : ℝ) (hlam : 0 < lam) (hR : 0 < R)
    (m k : ℕ) (i : Fin d) (z : Regeneration.CoupledSample d) :
    0 < couplingScopeSelectedRestartLevel Δ lam R m k i z / lam := by
  let w := Regeneration.sampleTimeShift Δ z ((m : ℝ≥0) * Δ)
  have hmax := Regeneration.displacement_le_coordinateMaximum w.1 i
    ((k : ℝ≥0) * Δ) ((k : ℝ≥0) * Δ) le_rfl
  change 0 < (lam * (Regeneration.coordinateMaximum w.1 i ((k : ℝ≥0) * Δ) -
    (w.1 ((k : ℝ≥0) * Δ) i - w.1 0 i) + R)) / lam
  rw [mul_div_cancel_left₀ _ hlam.ne']
  linarith

/-- Passage transport uses the selected level on the original sample and
retains the literal double grid shift. -/
theorem coupling_scope_selected_passage_eq {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ)
    (lam R : ℝ) (m k : ℕ) (i : Fin d) (n : ℕ) (z : Regeneration.CoupledSample d) :
    couplingScopePassage Δ lam R (couplingScopeRestartLevel Δ lam R k i) k i n
      (Regeneration.sampleTimeShift Δ z ((m : ℝ≥0) * Δ)) =
      couplingScopePassage Δ lam R
        (couplingScopeSelectedRestartLevel Δ lam R m k i) (m + k) i n z := by
  unfold couplingScopePassage couplingScopeSelectedRestartLevel
  rw [coupling_scope_sample_restart_add Δ hΔ]

/-- The closed rounded guard is transported without changing its interval
or replacing its oscillation condition. -/
theorem coupling_scope_selected_even_guard_iff {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ)
    (lam R : ℝ) (m k : ℕ) (i : Fin d) (n : ℕ) (z : Regeneration.CoupledSample d) :
    Regeneration.sampleTimeShift Δ z ((m : ℝ≥0) * Δ) ∈
      couplingScopeEvenGuard Δ lam R (couplingScopeRestartLevel Δ lam R k i) k i n ↔
    z ∈ couplingScopeEvenGuard Δ lam R
      (couplingScopeSelectedRestartLevel Δ lam R m k i) (m + k) i n := by
  change Regeneration.IsGoodPassage Δ lam R _ _ i (2 * n) ↔ _
  rw [coupling_scope_sample_restart_add Δ hΔ]
  rfl

/-- Successful-candidate transport retains the actual shifted coins. -/
theorem coupling_scope_selected_successful_candidate_eq {d : ℕ}
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (lam R : ℝ) (m k : ℕ) (i : Fin d)
    (z : Regeneration.CoupledSample d) :
    Regeneration.firstSuccessfulCandidate Δ lam R
      (couplingScopeRestartLevel Δ lam R k i
        (Regeneration.sampleTimeShift Δ z ((m : ℝ≥0) * Δ)))
      (Regeneration.sampleTimeShift Δ
        (Regeneration.sampleTimeShift Δ z ((m : ℝ≥0) * Δ)) ((k : ℝ≥0) * Δ)) i =
    Regeneration.firstSuccessfulCandidate Δ lam R
      (couplingScopeSelectedRestartLevel Δ lam R m k i z)
      (Regeneration.sampleTimeShift Δ z (((m + k : ℕ) : ℝ≥0) * Δ)) i := by
  rw [coupling_scope_sample_restart_add Δ hΔ]
  rfl

/-- Countably many selected levels give one common event of gap-free trial
entry at every deterministic starting grid. This conditional consumer does
not assert any probability law at a randomly selected endpoint. -/
theorem coupling_scope_ae_all_grid_trial_entries_of_successful_candidates {d : ℕ}
    (μ : Measure (FieldPair d × Regeneration.CoupledSample d))
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (lam R : ℝ) (i : Fin d)
    (hsuccess : ∀ (a : ℕ) (A : Regeneration.CoupledSample d → ℝ),
      @Measurable (Regeneration.CoupledSample d) ℝ
        (Regeneration.finiteHistorySigma Δ a) inferInstance A →
      ∀ᵐ q ∂μ, Regeneration.firstSuccessfulCandidate Δ lam R (A q.2)
        (Regeneration.sampleTimeShift Δ q.2 ((a : ℝ≥0) * Δ)) i ≠ ⊤) :
    ∀ᵐ q ∂μ, ∀ m : ℕ,
      let w := Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)
      Regeneration.trialStartSequence Δ lam R w i 0 ≠ ⊤ ∧
        ∀ n : ℕ, Regeneration.trialFailureTime Δ R w i
          (Regeneration.trialStartSequence Δ lam R w i n) ≠ ⊤ →
            Regeneration.trialStartSequence Δ lam R w i (n + 1) ≠ ⊤ := by
  apply ae_all_iff.mpr
  intro m
  have hfirst := hsuccess m (fun _ => 3 * lam * R) measurable_const
  have hrestart : ∀ᵐ q ∂μ, ∀ k : ℕ,
      Regeneration.firstSuccessfulCandidate Δ lam R
        (couplingScopeSelectedRestartLevel Δ lam R m k i q.2)
        (Regeneration.sampleTimeShift Δ q.2 (((m + k : ℕ) : ℝ≥0) * Δ)) i ≠ ⊤ := by
    apply ae_all_iff.mpr
    intro k
    exact hsuccess (m + k) _
      (coupling_scope_measurable_selected_restart_level_finiteHistory Δ hΔ lam R m k i)
  filter_upwards [hfirst, hrestart] with q hbase hall
  apply coupling_scope_trial_entries_of_successful_candidates Δ lam R _ i hbase
  intro k
  rw [coupling_scope_selected_successful_candidate_eq Δ hΔ lam R m k i q.2]
  exact hall k

/-- The actual rounded failure is never earlier than its entered trial. -/
theorem coupling_scope_trial_start_le_failure {d : ℕ}
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (R : ℝ) (z : Regeneration.CoupledSample d)
    (i : Fin d) (S : ℝ≥0∞) : S ≤ Regeneration.trialFailureTime Δ R z i S := by
  apply le_trans _ (Regeneration.le_roundUp Δ hΔ _)
  unfold Regeneration.trialDownwardTime
  split_ifs with hS
  · exact le_top
  · exact le_add_of_nonneg_right zero_le

/-- Each literal successor advances by at least two grid periods, including
branches whose selected time is infinite. -/
theorem coupling_scope_trial_start_add_two_step_le_succ {d : ℕ}
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
      (add_le_add (coupling_scope_trial_start_le_failure Δ hΔ R z i _) hstep) le_rfl

/-- Trial-index growth strengthens the individual `2Δ` lower bound to
`2(n+1)Δ`, as required to reach the original past after a shifted restart. -/
theorem coupling_scope_nat_two_step_le_trial_start {d : ℕ}
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (lam R : ℝ) (hlam : 0 < lam) (hR : 0 < R)
    (z : Regeneration.CoupledSample d) (i : Fin d) (n : ℕ) :
    ((n + 1 : ℕ) : ℝ≥0∞) * (2 * (Δ : ℝ≥0∞)) ≤
      Regeneration.trialStartSequence Δ lam R z i n := by
  induction n with
  | zero =>
      simpa only [Nat.zero_add, Nat.cast_one, one_mul] using
        Regeneration.two_step_le_trialStartSequence Δ hΔ lam R hlam hR z i 0
  | succ n ih =>
      calc
        ((n + 1 + 1 : ℕ) : ℝ≥0∞) * (2 * (Δ : ℝ≥0∞)) =
            ((n + 1 : ℕ) : ℝ≥0∞) * (2 * (Δ : ℝ≥0∞)) + 2 * (Δ : ℝ≥0∞) := by
          rw [Nat.cast_add_one, add_mul, one_mul]
        _ ≤ Regeneration.trialStartSequence Δ lam R z i n + 2 * (Δ : ℝ≥0∞) :=
          add_le_add ih le_rfl
        _ ≤ _ := coupling_scope_trial_start_add_two_step_le_succ
          Δ hΔ lam R hlam hR z i n

/-- If every entered trial is finite, its prebridge times tend to infinity.
The finite-time conversion is made only after using that finiteness. -/
theorem coupling_scope_trial_prebridge_tendsto_atTop {d : ℕ}
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (lam R : ℝ) (hlam : 0 < lam) (hR : 0 < R)
    (z : Regeneration.CoupledSample d) (i : Fin d)
    (hfinite : ∀ n, Regeneration.trialStartSequence Δ lam R z i n ≠ ⊤) :
    Filter.Tendsto (fun n => (Regeneration.trialStartSequence Δ lam R z i n).toNNReal - Δ)
      Filter.atTop Filter.atTop := by
  have hn : Filter.Tendsto (fun n : ℕ => (n : ℝ≥0) * Δ) Filter.atTop Filter.atTop :=
    (tendsto_natCast_atTop_atTop (R := ℝ≥0)).atTop_mul_const' hΔ
  apply Filter.tendsto_atTop_mono (f := fun n : ℕ => (n : ℝ≥0) * Δ) _ hn
  intro n
  apply le_tsub_of_add_le_right
  have hgrowth := coupling_scope_nat_two_step_le_trial_start Δ hΔ lam R hlam hR z i n
  rw [← ENNReal.coe_toNNReal (hfinite n)] at hgrowth
  have hbound : ((n + 1 : ℕ) : ℝ≥0) * (2 * Δ) ≤
      (Regeneration.trialStartSequence Δ lam R z i n).toNNReal := by
    exact_mod_cast hgrowth
  calc
    (n : ℝ≥0) * Δ + Δ = ((n + 1 : ℕ) : ℝ≥0) * Δ := by
      rw [Nat.cast_add_one, add_mul, one_mul]
    _ ≤ ((n + 1 : ℕ) : ℝ≥0) * (2 * Δ) := by
      gcongr
      exact le_mul_of_one_le_left (show 0 ≤ Δ from zero_le) (by norm_num : (1 : ℝ≥0) ≤ 2)
    _ ≤ _ := hbound

/-- Burn compares the original entire prefix with the selected prebridge
position plus `R`, retaining the source locality gap. -/
def couplingScopeTrialBurn {d : ℕ} (Δ : ℝ≥0) (lam R : ℝ) (m : ℕ)
    (i : Fin d) (J : ℕ) : Set (FieldPair d × Regeneration.CoupledSample d) :=
  {q | let w := Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)
    let S := Regeneration.trialStartSequence Δ lam R w i J
    S ≠ ⊤ ∧ q.2.1 0 i + Regeneration.coordinateMaximum q.2.1 i ((m : ℝ≥0) * Δ) ≤
      q.2.1 ((m : ℝ≥0) * Δ + (S.toNNReal - Δ)) i + R}

/-- Lost retains Burn at its selected trial and the next literal finite
failures. The contraction for these events is a separate producer obligation. -/
def couplingScopeTrialLost {d : ℕ} (Δ : ℝ≥0) (lam R : ℝ) (m : ℕ)
    (i : Fin d) (J N : ℕ) : Set (FieldPair d × Regeneration.CoupledSample d) :=
  couplingScopeTrialBurn Δ lam R m i J ∩
    {q | ∀ r < N, let w := Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)
      Regeneration.trialFailureTime Δ R w i
        (Regeneration.trialStartSequence Δ lam R w i (J + r)) ≠ ⊤}

/-- Burn is measurable for the actual path and shifted full-trial selection. -/
theorem coupling_scope_measurableSet_trial_burn {d : ℕ} (Δ : ℝ≥0) (lam R : ℝ)
    (m : ℕ) (i : Fin d) (J : ℕ) : MeasurableSet (couplingScopeTrialBurn Δ lam R m i J) := by
  have hw : Measurable (fun q : FieldPair d × Regeneration.CoupledSample d =>
      Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)) :=
    (Regeneration.measurable_sampleTimeShift Δ).comp (measurable_const.prodMk measurable_snd)
  have hS := (Regeneration.measurable_trialStartSequence Δ lam R i J).comp hw
  have heval : Continuous (fun p : ℝ≥0 × Path d => p.2 p.1 i) :=
    (continuous_apply i).comp (continuous_snd.eval continuous_fst)
  have hzero : Measurable (fun q : FieldPair d × Regeneration.CoupledSample d =>
      q.2.1 0 i) :=
    heval.measurable.comp (measurable_const.prodMk measurable_snd.fst)
  have hmax : Measurable (fun q : FieldPair d × Regeneration.CoupledSample d =>
      Regeneration.coordinateMaximum q.2.1 i ((m : ℝ≥0) * Δ)) :=
    (Regeneration.measurable_coordinateMaximum i).comp
      (measurable_const.prodMk measurable_snd.fst)
  have htime : Measurable (fun q : FieldPair d × Regeneration.CoupledSample d =>
      (m : ℝ≥0) * Δ + ((Regeneration.trialStartSequence Δ lam R
        (Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)) i J).toNNReal - Δ)) :=
    measurable_const.add (hS.ennreal_toNNReal.sub_const Δ)
  have hcurrent := heval.measurable.comp (htime.prodMk measurable_snd.fst)
  exact (measurableSet_eq_fun hS measurable_const).compl.inter
    (measurableSet_le (hzero.add hmax) (hcurrent.add_const R))

/-- Every selected finite-failure prefix is measurable. -/
theorem coupling_scope_measurableSet_trial_lost {d : ℕ} (Δ : ℝ≥0) (lam R : ℝ)
    (m : ℕ) (i : Fin d) (J N : ℕ) : MeasurableSet (couplingScopeTrialLost Δ lam R m i J N) := by
  have hw : Measurable (fun q : FieldPair d × Regeneration.CoupledSample d =>
      Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)) :=
    (Regeneration.measurable_sampleTimeShift Δ).comp (measurable_const.prodMk measurable_snd)
  refine (coupling_scope_measurableSet_trial_burn Δ lam R m i J).inter ?_
  simp only [Set.ofPred_forall]
  refine MeasurableSet.iInter fun r => MeasurableSet.iInter fun _hr => ?_
  exact (measurableSet_eq_fun
    ((Regeneration.measurable_trialFailureTime Δ R i).comp
      (((Regeneration.measurable_trialStartSequence Δ lam R i (J + r)).comp hw).prodMk hw))
    measurable_const).compl

/-- Longer failure prefixes shrink the same Burn event. -/
theorem coupling_scope_trial_lost_antitone {d : ℕ} (Δ : ℝ≥0) (lam R : ℝ)
    (m : ℕ) (i : Fin d) (J : ℕ) : Antitone (couplingScopeTrialLost Δ lam R m i J) := by
  intro a b hab q hq
  exact ⟨hq.1, fun r hr => hq.2 r (hr.trans_le hab)⟩

/-- Directional escape eventually places a finite prebridge beyond the
original prefix, whenever all shifted full trials have finite starts. -/
theorem coupling_scope_exists_trial_burn_of_escape {d : ℕ}
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (lam R : ℝ) (hlam : 0 < lam) (hR : 0 < R)
    (m : ℕ) (i : Fin d) (q : FieldPair d × Regeneration.CoupledSample d)
    (hescape : Filter.Tendsto (fun t : ℝ≥0 => q.2.1 t i) Filter.atTop Filter.atTop)
    (hfinite : ∀ n, Regeneration.trialStartSequence Δ lam R
      (Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)) i n ≠ ⊤) :
    ∃ J, q ∈ couplingScopeTrialBurn Δ lam R m i J := by
  have ht := coupling_scope_trial_prebridge_tendsto_atTop Δ hΔ lam R hlam hR
    (Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)) i hfinite
  have habs := Filter.tendsto_atTop_mono
    (fun n => le_add_of_nonneg_left (show 0 ≤ (m : ℝ≥0) * Δ from zero_le)) ht
  have hheight := (hescape.comp habs).eventually_ge_atTop
    (q.2.1 0 i + Regeneration.coordinateMaximum q.2.1 i ((m : ℝ≥0) * Δ) - R)
  obtain ⟨J, hJ⟩ := hheight.exists
  exact ⟨J, hfinite J, sub_le_iff_le_add.mp hJ⟩

/-- Infinite shifted first regeneration with no entry gaps belongs to a
countable union of literal Lost intersections. Burn is reached using trial
index growth and escape, not postulated as an additional path premise. -/
theorem coupling_scope_infinite_shifted_regeneration_mem_lost {d : ℕ}
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (lam R : ℝ) (hlam : 0 < lam) (hR : 0 < R)
    (m : ℕ) (i : Fin d) (q : FieldPair d × Regeneration.CoupledSample d)
    (hescape : Filter.Tendsto (fun t : ℝ≥0 => q.2.1 t i) Filter.atTop Filter.atTop)
    (hentry : let w := Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)
      Regeneration.trialStartSequence Δ lam R w i 0 ≠ ⊤ ∧
        ∀ n, Regeneration.trialFailureTime Δ R w i
          (Regeneration.trialStartSequence Δ lam R w i n) ≠ ⊤ →
            Regeneration.trialStartSequence Δ lam R w i (n + 1) ≠ ⊤)
    (htop : Regeneration.firstRegenerationTime Δ lam R
      (Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)) i = ⊤) :
    q ∈ ⋃ J, ⋂ N, couplingScopeTrialLost Δ lam R m i J N := by
  let w := Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)
  have hfinite := (coupling_scope_first_regeneration_eq_top_iff_all_trials_finite
    Δ hΔ lam R w i hentry.1 hentry.2).mp htop
  obtain ⟨J, hJ⟩ := coupling_scope_exists_trial_burn_of_escape
    Δ hΔ lam R hlam hR m i q hescape hfinite
  refine Set.mem_iUnion.mpr ⟨J, Set.mem_iInter.mpr ?_⟩
  intro N
  change (q ∈ couplingScopeTrialBurn Δ lam R m i J) ∧
    ∀ r < N, Regeneration.trialFailureTime Δ R w i
      (Regeneration.trialStartSequence Δ lam R w i (J + r)) ≠ ⊤
  refine ⟨hJ, ?_⟩
  intro r _hr hfail
  have htrial : Regeneration.IsRegenerationTrial Δ lam R w i (J + r) :=
    ⟨hfinite (J + r), hfail⟩
  have hle : Regeneration.firstRegenerationTime Δ lam R w i ≤
      Regeneration.trialStartSequence Δ lam R w i (J + r) :=
    iInf_le_of_le (J + r) (iInf_le_of_le htrial le_rfl)
  exact hfinite (J + r) (top_le_iff.mp (htop ▸ hle))

/-- Genuine branchwise contraction for the literal Lost events excludes
infinite shifted first regeneration simultaneously at every grid start.
Producing that contraction remains an internal analytic obligation. -/
theorem coupling_scope_ae_all_grid_first_regeneration_finite_of_burn_estimate {d : ℕ}
    (μ : Measure (FieldPair d × Regeneration.CoupledSample d)) [IsProbabilityMeasure μ]
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (lam R : ℝ) (hlam : 0 < lam) (hR : 0 < R) (i : Fin d)
    (hescape : ∀ᵐ q ∂μ,
      Filter.Tendsto (fun t : ℝ≥0 => q.2.1 t i) Filter.atTop Filter.atTop)
    (hentry : ∀ᵐ q ∂μ, ∀ m : ℕ,
      let w := Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)
      Regeneration.trialStartSequence Δ lam R w i 0 ≠ ⊤ ∧
        ∀ n, Regeneration.trialFailureTime Δ R w i
          (Regeneration.trialStartSequence Δ lam R w i n) ≠ ⊤ →
            Regeneration.trialStartSequence Δ lam R w i (n + 1) ≠ ⊤)
    (η : ℝ) (hη : 0 < η)
    (hstep : ∀ m J N, μ (couplingScopeTrialLost Δ lam R m i J (N + 1)) ≤
      ENNReal.ofReal (1 - η) * μ (couplingScopeTrialLost Δ lam R m i J N)) :
    ∀ᵐ q ∂μ, ∀ m : ℕ, Regeneration.firstRegenerationTime Δ lam R
      (Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)) i ≠ ⊤ := by
  have hnull (m : ℕ) : μ (⋃ J, ⋂ N, couplingScopeTrialLost Δ lam R m i J N) = 0 := by
    apply measure_iUnion_null
    intro J
    exact ConditionalTrialExhaustion.measure_iInter_eq_zero_of_failure_step μ _
      (fun N => coupling_scope_measurableSet_trial_lost Δ lam R m i J N)
      (coupling_scope_trial_lost_antitone Δ lam R m i J) _
      (ENNReal.ofReal_lt_one.mpr (by linarith)) (hstep m J)
  have havoid : ∀ᵐ q ∂μ, ∀ m : ℕ,
      q ∉ ⋃ J, ⋂ N, couplingScopeTrialLost Δ lam R m i J N := by
    apply ae_all_iff.mpr
    intro m
    rw [ae_iff]
    simpa only [not_not, Set.ofPred_mem_eq] using hnull m
  filter_upwards [hescape, hentry, havoid] with q hq he hn m htop
  exact hn m (coupling_scope_infinite_shifted_regeneration_mem_lost
    Δ hΔ lam R hlam hR m i q hq (he m) htop)

/-- A tube at the finite actual passage implies the rounded even guard. -/
theorem coupling_scope_tube_inter_subset_guard {d : ℕ}
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (lam R : ℝ)
    (A : Regeneration.CoupledSample d → ℝ) (m : ℕ) (i : Fin d) (N : ℕ) :
    let E := couplingScopeEvenGuardFailure Δ lam R A m i Set.univ N ∩
      {q | couplingScopePassage Δ lam R A m i (2 * N) q.2 ≠ ⊤}
    let Tube := {q : FieldPair d × Regeneration.CoupledSample d |
      ∀ s ∈ Set.Icc (0 : ℝ≥0) Δ,
        euclideanNorm ((Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)).1
          ((couplingScopePassage Δ lam R A m i (2 * N) q.2).toNNReal + s) -
          (Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)).1
          (couplingScopePassage Δ lam R A m i (2 * N) q.2).toNNReal) ≤ R / 2}
    E ∩ Tube ⊆ E ∩ {q | q.2 ∈ couplingScopeEvenGuard Δ lam R A m i N} := by
  dsimp only
  intro q hq
  refine ⟨hq.1, ?_⟩
  exact ConditionalTrialExhaustion.isGoodPassage_of_euclidean_tube Δ hΔ lam R
    (A q.2) (Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)).1 i (2 * N)
    hq.1.2 hq.2

/-- An integrated tube estimate transfers to the actual guard on the same law. -/
theorem coupling_scope_guard_estimate_of_tube_estimate {d : ℕ}
    (μ : Measure (FieldPair d × Regeneration.CoupledSample d)) [IsProbabilityMeasure μ]
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (lam R ε : ℝ)
    (A : Regeneration.CoupledSample d → ℝ) (m : ℕ) (i : Fin d) (N : ℕ)
    (htube :
      let E := couplingScopeEvenGuardFailure Δ lam R A m i Set.univ N ∩
        {q | couplingScopePassage Δ lam R A m i (2 * N) q.2 ≠ ⊤}
      let Tube := {q : FieldPair d × Regeneration.CoupledSample d |
        ∀ s ∈ Set.Icc (0 : ℝ≥0) Δ,
          euclideanNorm ((Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)).1
            ((couplingScopePassage Δ lam R A m i (2 * N) q.2).toNNReal + s) -
            (Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)).1
            (couplingScopePassage Δ lam R A m i (2 * N) q.2).toNNReal) ≤ R / 2}
      ε * μ.real E ≤ μ.real (E ∩ Tube)) :
    let E := couplingScopeEvenGuardFailure Δ lam R A m i Set.univ N ∩
      {q | couplingScopePassage Δ lam R A m i (2 * N) q.2 ≠ ⊤}
    ε * μ.real E ≤ μ.real (E ∩
      {q | q.2 ∈ couplingScopeEvenGuard Δ lam R A m i N}) :=
  htube.trans (measureReal_mono (coupling_scope_tube_inter_subset_guard Δ hΔ lam R A m i N))

/-- Actual directional escape and integrated guards supply the selected
candidate facts needed for all starting grids on one common event. Freshness
is consumed at its supplied-law type, without shifting the annealed law. -/
theorem coupling_scope_ae_all_grid_trial_entries_of_escape_and_guard_estimates {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (K : Regeneration.CoupledQuenchedLaws d) (hK : Regeneration.HasProbabilityLaws Q K)
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hFresh : Regeneration.HasFreshBits Q Δ δ K)
    (lam R : ℝ) (hlam : 0 < lam) (hR : 0 < R) (i : Fin d)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hescape : ∀ᵐ q ∂Regeneration.annealedCoupledLaw Q K,
      Filter.Tendsto (fun t : ℝ≥0 => q.2.1 t i) Filter.atTop Filter.atTop)
    (hwin : ∀ (m : ℕ) (A : Regeneration.CoupledSample d → ℝ),
      @Measurable (Regeneration.CoupledSample d) ℝ
        (Regeneration.finiteHistorySigma Δ m) inferInstance A →
      ∀ N,
        let μ := Regeneration.annealedCoupledLaw Q K
        let E := couplingScopeEvenGuardFailure Δ lam R A m i Set.univ N ∩
          {q | couplingScopePassage Δ lam R A m i (2 * N) q.2 ≠ ⊤}
        ε * μ.real E ≤ μ.real (E ∩
          {q | q.2 ∈ couplingScopeEvenGuard Δ lam R A m i N})) :
    ∀ᵐ q ∂Regeneration.annealedCoupledLaw Q K, ∀ m : ℕ,
      let w := Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)
      Regeneration.trialStartSequence Δ lam R w i 0 ≠ ⊤ ∧
        ∀ n : ℕ, Regeneration.trialFailureTime Δ R w i
          (Regeneration.trialStartSequence Δ lam R w i n) ≠ ⊤ →
            Regeneration.trialStartSequence Δ lam R w i (n + 1) ≠ ⊤ := by
  apply coupling_scope_ae_all_grid_trial_entries_of_successful_candidates
    (Regeneration.annealedCoupledLaw Q K) Δ hΔ lam R i
  intro m A hA
  apply coupling_scope_ae_successful_candidate_finite_of_guard_estimates
    Q K hK Δ hΔ δ hδ hδ1 hFresh lam R hlam hR i ε hε hε1 _ hwin m A hA
  intro m' A' _hA'
  filter_upwards [coupling_scope_ae_passages_finite_of_escape
    (Regeneration.annealedCoupledLaw Q K) Δ lam R i hescape] with q hq n
  exact hq m' A' n

/-- A uniform integrated tube estimate supplies all-grid trial entries.
The tube estimate remains a separate supplied-law hypothesis. -/
theorem coupling_scope_ae_all_grid_trial_entries_of_escape_and_tube_estimates {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (K : Regeneration.CoupledQuenchedLaws d) (hK : Regeneration.HasProbabilityLaws Q K)
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hFresh : Regeneration.HasFreshBits Q Δ δ K)
    (lam R : ℝ) (hlam : 0 < lam) (hR : 0 < R) (i : Fin d)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hescape : ∀ᵐ q ∂Regeneration.annealedCoupledLaw Q K,
      Filter.Tendsto (fun t : ℝ≥0 => q.2.1 t i) Filter.atTop Filter.atTop)
    (htube : ∀ (m : ℕ) (A : Regeneration.CoupledSample d → ℝ),
      @Measurable (Regeneration.CoupledSample d) ℝ
        (Regeneration.finiteHistorySigma Δ m) inferInstance A → ∀ N,
      let μ := Regeneration.annealedCoupledLaw Q K
      let E := couplingScopeEvenGuardFailure Δ lam R A m i Set.univ N ∩
        {q | couplingScopePassage Δ lam R A m i (2 * N) q.2 ≠ ⊤}
      let Tube := {q : FieldPair d × Regeneration.CoupledSample d |
        ∀ s ∈ Set.Icc (0 : ℝ≥0) Δ,
          euclideanNorm ((Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)).1
            ((couplingScopePassage Δ lam R A m i (2 * N) q.2).toNNReal + s) -
            (Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)).1
            (couplingScopePassage Δ lam R A m i (2 * N) q.2).toNNReal) ≤ R / 2}
      ε * μ.real E ≤ μ.real (E ∩ Tube)) :
    ∀ᵐ q ∂Regeneration.annealedCoupledLaw Q K, ∀ m : ℕ,
      let w := Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)
      Regeneration.trialStartSequence Δ lam R w i 0 ≠ ⊤ ∧
        ∀ n : ℕ, Regeneration.trialFailureTime Δ R w i
          (Regeneration.trialStartSequence Δ lam R w i n) ≠ ⊤ →
            Regeneration.trialStartSequence Δ lam R w i (n + 1) ≠ ⊤ := by
  let : IsProbabilityMeasure (Regeneration.annealedCoupledLaw Q K) :=
    Regeneration.annealedCoupledLaw_isProbabilityMeasure Q K hK
  apply coupling_scope_ae_all_grid_trial_entries_of_escape_and_guard_estimates
    Q K hK Δ hΔ δ hδ hδ1 hFresh lam R hlam hR i ε hε hε1 hescape
  intro m A hA N
  exact coupling_scope_guard_estimate_of_tube_estimate _ Δ hΔ lam R ε A m i N
    (htube m A hA N)

/-- At Burn, the original full prebridge history lies below its selected
position plus `R`. The shifted past uses the proved literal trial slack. -/
theorem coupling_scope_trial_burn_full_prefix {d : ℕ}
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (lam R : ℝ) (hlam : 0 < lam) (hR : 0 < R)
    (m : ℕ) (i : Fin d) (J : ℕ) (q : FieldPair d × Regeneration.CoupledSample d)
    (hburn : q ∈ couplingScopeTrialBurn Δ lam R m i J) :
    let w := Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)
    let T := (Regeneration.trialStartSequence Δ lam R w i J).toNNReal - Δ
    q.2.1 0 i + Regeneration.coordinateMaximum q.2.1 i ((m : ℝ≥0) * Δ + T) ≤
      q.2.1 ((m : ℝ≥0) * Δ + T) i + R := by
  dsimp only
  rw [Regeneration.coordinateMaximum_add]
  have hslack := Regeneration.trial_prestart_maximum_slack Δ hΔ lam R hlam hR
    (Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)) i J hburn.1
  change Regeneration.coordinateMaximum
    (Regeneration.pathTimeShift q.2.1 ((m : ℝ≥0) * Δ)) i _ ≤
      q.2.1 ((m : ℝ≥0) * Δ + _) i - q.2.1 ((m : ℝ≥0) * Δ + 0) i + R at hslack
  rw [add_zero] at hslack
  rw [add_max]
  exact max_le hburn.2 (by linarith)

/-- With genuine Burn contraction at the actual grids, the literal cycle
recursion is finite for every cycle on one common full-measure event. -/
theorem coupling_scope_ae_all_cycles_finite_of_escape_and_burn_estimate {d : ℕ}
    (hd : 2 ≤ d) (lam l : ℝ) (hlam : 0 < lam) (hl : 0 < l)
    (μ : Measure (FieldPair d × Regeneration.CoupledSample d)) [IsProbabilityMeasure μ]
    (hescape : ∀ᵐ q ∂μ, Filter.Tendsto
      (fun t : ℝ≥0 => q.2.1 t (Regeneration.Renewal.forceCoord hd))
        Filter.atTop Filter.atTop)
    (hentry : ∀ᵐ q ∂μ, ∀ m : ℕ,
      let Δ := Regeneration.Renewal.regenDelta lam
      let w := Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)
      let i := Regeneration.Renewal.forceCoord hd
      Regeneration.trialStartSequence Δ lam (l / lam) w i 0 ≠ ⊤ ∧
        ∀ n, Regeneration.trialFailureTime Δ (l / lam) w i
          (Regeneration.trialStartSequence Δ lam (l / lam) w i n) ≠ ⊤ →
            Regeneration.trialStartSequence Δ lam (l / lam) w i (n + 1) ≠ ⊤)
    (η : ℝ) (hη : 0 < η)
    (hstep : ∀ m J N,
      let Δ := Regeneration.Renewal.regenDelta lam
      let i := Regeneration.Renewal.forceCoord hd
      μ (couplingScopeTrialLost Δ lam (l / lam) m i J (N + 1)) ≤
        ENNReal.ofReal (1 - η) * μ (couplingScopeTrialLost Δ lam (l / lam) m i J N)) :
    ∀ᵐ q ∂μ, ∀ k : ℕ, regenerationTime hd lam l k q.2 ≠ ⊤ := by
  have hΔ : 0 < Regeneration.Renewal.regenDelta lam :=
    Real.toNNReal_pos.mpr (inv_pos.mpr (sq_pos_of_pos hlam))
  exact coupling_scope_ae_finite_of_grid_exhaustion hd lam l hlam μ
    (ae_all_iff.mp (coupling_scope_ae_all_grid_first_regeneration_finite_of_burn_estimate
      μ _ hΔ lam (l / lam) hlam (div_pos hl hlam) _ hescape hentry η hη hstep))

/-- At the actual no-return probability, Burn contraction yields the literal
all-cycle grid/record conclusion under both supplied laws. The escape, entry
and contraction producers remain explicit; this is not the source-node proof. -/
theorem coupling_scope_both_laws_grid_record_of_burn_estimate {d : ℕ}
    (hd : 2 ≤ d) (lam l : ℝ) (hlam : 0 < lam) (hl : 0 < l)
    {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (K : Regeneration.CoupledQuenchedLaws d)
    (hK : Regeneration.HasProbabilityLaws Q.measure K)
    (hD : Regeneration.annealedCoupledLaw Q.measure K
      (regenerationNoReturn hd (l / lam)) ≠ 0)
    (hescape : ∀ᵐ q ∂Regeneration.annealedCoupledLaw Q.measure K, Filter.Tendsto
      (fun t : ℝ≥0 => q.2.1 t (Regeneration.Renewal.forceCoord hd))
        Filter.atTop Filter.atTop)
    (hentry : ∀ᵐ q ∂Regeneration.annealedCoupledLaw Q.measure K, ∀ m : ℕ,
      let Δ := Regeneration.Renewal.regenDelta lam
      let w := Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)
      let i := Regeneration.Renewal.forceCoord hd
      Regeneration.trialStartSequence Δ lam (l / lam) w i 0 ≠ ⊤ ∧
        ∀ n, Regeneration.trialFailureTime Δ (l / lam) w i
          (Regeneration.trialStartSequence Δ lam (l / lam) w i n) ≠ ⊤ →
            Regeneration.trialStartSequence Δ lam (l / lam) w i (n + 1) ≠ ⊤)
    (hstep : ∀ m J N,
      let Δ := Regeneration.Renewal.regenDelta lam
      let i := Regeneration.Renewal.forceCoord hd
      Regeneration.annealedCoupledLaw Q.measure K
        (couplingScopeTrialLost Δ lam (l / lam) m i J (N + 1)) ≤
        ENNReal.ofReal (1 - (Regeneration.annealedCoupledLaw Q.measure K
          (regenerationNoReturn hd (l / lam))).toReal) *
            Regeneration.annealedCoupledLaw Q.measure K
              (couplingScopeTrialLost Δ lam (l / lam) m i J N)) :
    ∀ k : ℕ, ∀ ρ ∈ ({Regeneration.annealedCoupledLaw Q.measure K,
        regenerationConditionedLaw hd Q lam l K hK hD} :
          Set (Measure (FieldPair d × Regeneration.CoupledSample d))),
      ∀ᵐ q ∂ρ, ∃ n : ℕ, 2 * k ≤ n ∧
        regenerationTime hd lam l k q.2 =
          (((n : ℝ≥0) * Regeneration.Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞) ∧
        regenerationRecord hd lam l k q =
          Regeneration.futureRecord (Regeneration.Renewal.regenDelta lam) (l / lam)
            q.1 q.2 (Regeneration.Renewal.forceCoord hd)
            ((n : ℝ≥0) * Regeneration.Renewal.regenDelta lam) := by
  let : IsProbabilityMeasure (Regeneration.annealedCoupledLaw Q.measure K) :=
    Regeneration.annealedCoupledLaw_isProbabilityMeasure Q.measure K hK
  have hpos : 0 < (Regeneration.annealedCoupledLaw Q.measure K
      (regenerationNoReturn hd (l / lam))).toReal :=
    ENNReal.toReal_pos hD (measure_ne_top _ _)
  have hall := coupling_scope_ae_all_cycles_finite_of_escape_and_burn_estimate
    hd lam l hlam hl (Regeneration.annealedCoupledLaw Q.measure K)
    hescape hentry _ hpos hstep
  intro k ρ hρ
  exact (coupling_scope_ae_finite_iff_grid_record hd lam l hlam hl k ρ).mp
    ((coupling_scope_both_laws_finite_iff hd Q lam l K hK hD k).mpr
      (ae_all_iff.mp hall k) ρ hρ)

/-- The literal full-trial starts are ordered, including their infinite branches. -/
theorem coupling_scope_trial_start_monotone {d : ℕ}
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (lam R : ℝ) (hlam : 0 < lam) (hR : 0 < R)
    (z : Regeneration.CoupledSample d) (i : Fin d) :
    Monotone (Regeneration.trialStartSequence Δ lam R z i) := by
  apply monotone_nat_of_le_succ
  intro n
  exact (le_add_of_nonneg_right zero_le).trans
    (coupling_scope_trial_start_add_two_step_le_succ Δ hΔ lam R hlam hR z i n)

/-- Entry at a later actual trial already witnesses every earlier finite failure. -/
theorem coupling_scope_earlier_failure_finite_of_trial_start {d : ℕ}
    (Δ : ℝ≥0) (lam R : ℝ) (z : Regeneration.CoupledSample d) (i : Fin d)
    (j n : ℕ) (hjn : j < n)
    (hn : Regeneration.trialStartSequence Δ lam R z i n ≠ ⊤) :
    Regeneration.trialFailureTime Δ R z i
      (Regeneration.trialStartSequence Δ lam R z i j) ≠ ⊤ := by
  intro hj
  exact hn (Regeneration.trialStartSequence_eq_top_after_infinite_failure
    Δ lam R z i j n hj hjn)

/-- A Burn-selected prospective trial, with only its current shifted coin
forced. This retains the literal original prefix and trial indices. -/
def couplingScopeTrialBurnPrebridge {d : ℕ} (Δ : ℝ≥0) (lam R : ℝ)
    (m : ℕ) (i : Fin d) (J N k : ℕ) : Set (Regeneration.CoupledSample d) :=
  {z |
    let w := Regeneration.forceSampleBit k
      (Regeneration.sampleTimeShift Δ z ((m : ℝ≥0) * Δ))
    let S := Regeneration.trialStartSequence Δ lam R w i J
    Regeneration.trialStartSequence Δ lam R w i (J + N) =
      ((((k + 1 : ℕ) : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞) ∧
    S ≠ ⊤ ∧ z.1 0 i + Regeneration.coordinateMaximum z.1 i ((m : ℝ≥0) * Δ) ≤
      z.1 ((m : ℝ≥0) * Δ + (S.toNNReal - Δ)) i + R}

/-- The Burn prebridge has its ordinary measurable representation before
passing to the smaller, pre-coin finite-history sigma algebra. -/
theorem coupling_scope_measurableSet_trial_burn_prebridge {d : ℕ}
    (Δ : ℝ≥0) (lam R : ℝ) (m : ℕ) (i : Fin d) (J N k : ℕ) :
    MeasurableSet (couplingScopeTrialBurnPrebridge Δ lam R m i J N k) := by
  have hw : Measurable (fun z : Regeneration.CoupledSample d =>
      Regeneration.forceSampleBit k (Regeneration.sampleTimeShift Δ z ((m : ℝ≥0) * Δ))) :=
    (Regeneration.measurable_forceSampleBit k).comp
      ((Regeneration.measurable_sampleTimeShift Δ).comp (measurable_const.prodMk measurable_id))
  have hS := (Regeneration.measurable_trialStartSequence Δ lam R i J).comp hw
  have heval : Continuous (fun p : ℝ≥0 × Path d => p.2 p.1 i) :=
    (continuous_apply i).comp (continuous_snd.eval continuous_fst)
  have hzero : Measurable (fun z : Regeneration.CoupledSample d => z.1 0 i) :=
    heval.measurable.comp (measurable_const.prodMk measurable_fst)
  have hmax : Measurable (fun z : Regeneration.CoupledSample d =>
      Regeneration.coordinateMaximum z.1 i ((m : ℝ≥0) * Δ)) :=
    (Regeneration.measurable_coordinateMaximum i).comp (measurable_const.prodMk measurable_fst)
  have ht : Measurable (fun z : Regeneration.CoupledSample d =>
      (m : ℝ≥0) * Δ + ((Regeneration.trialStartSequence Δ lam R
        (Regeneration.forceSampleBit k (Regeneration.sampleTimeShift Δ z
          ((m : ℝ≥0) * Δ))) i J).toNNReal - Δ)) :=
    measurable_const.add (hS.ennreal_toNNReal.sub_const Δ)
  exact (measurableSet_eq_fun
    ((Regeneration.measurable_trialStartSequence Δ lam R i (J + N)).comp hw)
    measurable_const).inter ((measurableSet_eq_fun hS measurable_const).compl.inter
      (measurableSet_le (hzero.add hmax)
        ((heval.measurable.comp (ht.prodMk measurable_fst)).add_const R)))

/-- Extending the history beyond the current prebridge preserves Burn and all
selected earlier starts. No current coin or bridge path is read. -/
theorem coupling_scope_mem_trial_burn_prebridge_of_prefix {d : ℕ}
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (lam R : ℝ) (hlam : 0 < lam) (hR : 0 < R)
    (m : ℕ) (i : Fin d) (J N k : ℕ) (z z' : Regeneration.CoupledSample d)
    (hpre : ∀ t ∈ Set.Icc (0 : ℝ≥0) (((m + k : ℕ) : ℝ≥0) * Δ), z.1 t = z'.1 t)
    (hbits : ∀ j < m + k, z.2 j = z'.2 j)
    (hz : z ∈ couplingScopeTrialBurnPrebridge Δ lam R m i J N k) :
    z' ∈ couplingScopeTrialBurnPrebridge Δ lam R m i J N k := by
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
    exact coupling_scope_trial_start_monotone Δ hΔ lam R hlam hR w i (Nat.le_add_right J N)
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
theorem coupling_scope_measurableSet_trial_burn_prebridge_finiteHistory {d : ℕ}
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (lam R : ℝ) (hlam : 0 < lam) (hR : 0 < R)
    (m : ℕ) (i : Fin d) (J N k : ℕ) :
    @MeasurableSet (Regeneration.CoupledSample d)
      (Regeneration.finiteHistorySigma Δ (m + k))
      (couplingScopeTrialBurnPrebridge Δ lam R m i J N k) := by
  have heq : couplingScopeTrialBurnPrebridge Δ lam R m i J N k =
      Probability.stoppedHistorySample Δ (m + k) ⁻¹'
        couplingScopeTrialBurnPrebridge Δ lam R m i J N k := by
    ext z
    have hp : ∀ t ∈ Set.Icc (0 : ℝ≥0) (((m + k : ℕ) : ℝ≥0) * Δ),
        z.1 t = (Probability.stoppedHistorySample Δ (m + k) z).1 t :=
      fun t ht => (Probability.stoppedHistorySample_path Δ (m + k) z t ht.2).symm
    have hb : ∀ j < m + k,
        z.2 j = (Probability.stoppedHistorySample Δ (m + k) z).2 j :=
      fun j hj => (Probability.stoppedHistorySample_bit Δ (m + k) z j hj).symm
    exact ⟨coupling_scope_mem_trial_burn_prebridge_of_prefix
      Δ hΔ lam R hlam hR m i J N k z _ hp hb,
      coupling_scope_mem_trial_burn_prebridge_of_prefix
        Δ hΔ lam R hlam hR m i J N k _ z
        (fun t ht => (hp t ht).symm) (fun j hj => (hb j hj).symm)⟩
  rw [heq]
  exact Probability.measurable_stoppedHistorySample Δ (m + k)
    (coupling_scope_measurableSet_trial_burn_prebridge Δ lam R m i J N k)

/-- Intersecting the pre-coin Burn event with the genuine fresh coin gives
exactly the literal Lost prefix at the selected grid slice. -/
theorem coupling_scope_trial_burn_prebridge_slice_eq {d : ℕ}
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (lam R : ℝ) (m : ℕ) (i : Fin d) (J N k : ℕ) :
    {q : FieldPair d × Regeneration.CoupledSample d |
      q.2 ∈ couplingScopeTrialBurnPrebridge Δ lam R m i J N k} ∩
      {q | q.2.2 (m + k) = true} =
    couplingScopeTrialLost Δ lam R m i J N ∩
      {q | Regeneration.trialStartSequence Δ lam R
        (Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)) i (J + N) =
          ((((k + 1 : ℕ) : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞)} := by
  ext q
  let w := Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)
  have hbit : w.2 k = q.2.2 (m + k) := by
    change q.2.2 (Regeneration.gridIndex Δ ((m : ℝ≥0) * Δ) + k) = _
    rw [Regeneration.gridIndex_mul Δ hΔ]
  constructor
  · rintro ⟨hA, hb⟩
    have hf := Regeneration.forceSampleBit_eq_self k w (hbit.trans hb)
    change Regeneration.trialStartSequence Δ lam R
      (Regeneration.forceSampleBit k w) i (J + N) = _ ∧ _ at hA
    rw [hf] at hA
    refine ⟨⟨hA.2, ?_⟩, hA.1⟩
    intro r hr
    exact coupling_scope_earlier_failure_finite_of_trial_start Δ lam R w i
      (J + r) (J + N) (Nat.add_lt_add_left hr J)
      (by rw [hA.1]; exact ENNReal.coe_ne_top)
  · rintro ⟨hL, hs⟩
    have hb : w.2 k = true :=
      ((coupling_scope_trial_start_slice_iff Δ hΔ lam R w i (J + N) k).mp hs).2
    refine ⟨?_, hbit.symm.trans hb⟩
    change Regeneration.trialStartSequence Δ lam R
      (Regeneration.forceSampleBit k w) i (J + N) = _ ∧ _
    rw [Regeneration.forceSampleBit_eq_self k w hb]
    exact ⟨hs, hL.1⟩

/-- Freshness is applied at the absolute grid coin, with the actual
Burn-selected prefix proved measurable in its pre-coin history. -/
theorem coupling_scope_measure_trial_lost_slice_fresh_bit {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (K : Regeneration.CoupledQuenchedLaws d) (hK : Regeneration.HasProbabilityLaws Q K)
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (δ : ℝ) (hδ : 0 ≤ δ)
    (hFresh : Regeneration.HasFreshBits Q Δ δ K)
    (lam R : ℝ) (hlam : 0 < lam) (hR : 0 < R) (m : ℕ) (i : Fin d) (J N k : ℕ) :
    Regeneration.annealedCoupledLaw Q K
      (couplingScopeTrialLost Δ lam R m i J N ∩
        {q | Regeneration.trialStartSequence Δ lam R
          (Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)) i (J + N) =
            ((((k + 1 : ℕ) : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞)}) =
      ENNReal.ofReal δ * Regeneration.annealedCoupledLaw Q K
        {q | q.2 ∈ couplingScopeTrialBurnPrebridge Δ lam R m i J N k} := by
  rw [← coupling_scope_trial_burn_prebridge_slice_eq Δ hΔ lam R m i J N k]
  exact Regeneration.measure_annealed_fresh_bit Q K hK Δ δ hδ hFresh (m + k) _
    (coupling_scope_measurableSet_trial_burn_prebridge_finiteHistory
      Δ hΔ lam R hlam hR m i J N k)

/-- Integrating a genuine conditional no-return estimate before the current
coin gives the success mass on the actual selected Lost/grid slice. This
conditional helper does not produce its analytic estimate. -/
theorem coupling_scope_trial_lost_slice_success_of_prebridge_condExp {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (K : Regeneration.CoupledQuenchedLaws d) (hK : Regeneration.HasProbabilityLaws Q K)
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (δ : ℝ) (hδ : 0 ≤ δ)
    (hFresh : Regeneration.HasFreshBits Q Δ δ K)
    (lam R : ℝ) (hlam : 0 < lam) (hR : 0 < R) (m : ℕ) (i : Fin d)
    (J N k : ℕ) (η : ℝ) (hη : 0 ≤ η)
    (hcond : ∀ᵐ q ∂Regeneration.annealedCoupledLaw Q K,
      q.2 ∈ couplingScopeTrialBurnPrebridge Δ lam R m i J N k →
        δ * η ≤ ((Regeneration.annealedCoupledLaw Q K)[
          ({p : FieldPair d × Regeneration.CoupledSample d | p.2.2 (m + k) = true ∧
            Regeneration.NoBacktracking R (Regeneration.pathTimeShift
              (Regeneration.sampleTimeShift Δ p.2 ((m : ℝ≥0) * Δ)).1
                (((k + 1 : ℕ) : ℝ≥0) * Δ)) i}).indicator (fun _ => (1 : ℝ)) |
                  couplingScopeAnnealedHistory Δ (m + k)]) q) :
    let μ := Regeneration.annealedCoupledLaw Q K
    let S := couplingScopeTrialLost Δ lam R m i J N ∩
      {q | Regeneration.trialStartSequence Δ lam R
        (Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)) i (J + N) =
          ((((k + 1 : ℕ) : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞)}
    ENNReal.ofReal η * μ S ≤ μ (S ∩ {q | Regeneration.trialFailureTime Δ R
      (Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)) i
        (Regeneration.trialStartSequence Δ lam R
          (Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)) i (J + N)) = ⊤}) := by
  let : IsProbabilityMeasure (Regeneration.annealedCoupledLaw Q K) :=
    Regeneration.annealedCoupledLaw_isProbabilityMeasure Q K hK
  let μ := Regeneration.annealedCoupledLaw Q K
  let A := {q : FieldPair d × Regeneration.CoupledSample d |
    q.2 ∈ couplingScopeTrialBurnPrebridge Δ lam R m i J N k}
  let S := couplingScopeTrialLost Δ lam R m i J N ∩
    {q : FieldPair d × Regeneration.CoupledSample d |
      Regeneration.trialStartSequence Δ lam R
        (Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)) i (J + N) =
          ((((k + 1 : ℕ) : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞)}
  let G := {q : FieldPair d × Regeneration.CoupledSample d |
    Regeneration.NoBacktracking R (Regeneration.pathTimeShift
      (Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)).1
        (((k + 1 : ℕ) : ℝ≥0) * Δ)) i}
  let B := {q : FieldPair d × Regeneration.CoupledSample d | q.2.2 (m + k) = true} ∩ G
  have hw : Measurable (fun q : FieldPair d × Regeneration.CoupledSample d =>
      Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)) :=
    (Regeneration.measurable_sampleTimeShift Δ).comp (measurable_const.prodMk measurable_snd)
  have hG : MeasurableSet G :=
    (Regeneration.measurableSet_NoBacktracking R i).preimage
      (Probability.continuous_path_time_shift.measurable.comp
        (measurable_const.prodMk hw.fst))
  have hB : MeasurableSet B :=
    (measurableSet_eq_fun ((measurable_pi_apply (m + k)).comp measurable_snd.snd)
      measurable_const).inter hG
  have hwin : ENNReal.ofReal (δ * η) * μ A ≤ μ (A ∩ B) :=
    ConditionalTrialExhaustion.measure_inter_ge_of_condExp μ
      (couplingScopeAnnealedHistory Δ (m + k))
      (coupling_scope_annealed_history_le Δ (m + k)) A B
      ((coupling_scope_measurableSet_trial_burn_prebridge_finiteHistory
        Δ hΔ lam R hlam hR m i J N k).preimage (Measurable.of_comap_le le_rfl))
      hB (δ * η) (mul_nonneg hδ hη) hcond
  have hmass : μ S = ENNReal.ofReal δ * μ A :=
    coupling_scope_measure_trial_lost_slice_fresh_bit
      Q K hK Δ hΔ δ hδ hFresh lam R hlam hR m i J N k
  have heq : A ∩ B = S ∩ G := by
    have hs : S = A ∩ {q | q.2.2 (m + k) = true} :=
      (coupling_scope_trial_burn_prebridge_slice_eq Δ hΔ lam R m i J N k).symm
    rw [hs]
    exact (Set.inter_assoc _ _ _).symm
  change ENNReal.ofReal η * μ S ≤ _
  calc
    ENNReal.ofReal η * μ S = ENNReal.ofReal (δ * η) * μ A := by
      rw [hmass, ENNReal.ofReal_mul hδ]
      ac_rfl
    _ ≤ μ (A ∩ B) := hwin
    _ = μ (S ∩ G) := by rw [heq]
    _ ≤ _ := by
      apply measure_mono
      rintro q ⟨hq, hqG⟩
      refine ⟨hq, ?_⟩
      apply (Regeneration.trialFailureTime_eq_top_iff_noBacktracking Δ R _ i _ ?_).mpr
      · rw [hq.2, ENNReal.toNNReal_coe]
        exact hqG
      · rw [hq.2]
        exact ENNReal.coe_ne_top

/-- Lost at length zero is exactly the literal Burn event. -/
theorem coupling_scope_trial_lost_zero {d : ℕ} (Δ : ℝ≥0) (lam R : ℝ)
    (m : ℕ) (i : Fin d) (J : ℕ) :
    couplingScopeTrialLost Δ lam R m i J 0 = couplingScopeTrialBurn Δ lam R m i J := by
  ext q
  exact ⟨And.left, fun h => ⟨h, fun _ hr => False.elim (Nat.not_lt_zero _ hr)⟩⟩

/-- Lost prefixes reveal one more actual downward failure at each step. -/
theorem coupling_scope_trial_lost_succ {d : ℕ} (Δ : ℝ≥0) (lam R : ℝ)
    (m : ℕ) (i : Fin d) (J N : ℕ) :
    couplingScopeTrialLost Δ lam R m i J (N + 1) =
      couplingScopeTrialLost Δ lam R m i J N ∩
        {q | Regeneration.trialFailureTime Δ R
          (Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)) i
            (Regeneration.trialStartSequence Δ lam R
              (Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)) i (J + N)) ≠ ⊤} := by
  ext q
  constructor
  · rintro ⟨hB, hF⟩
    exact ⟨⟨hB, fun r hr => hF r (Nat.lt_succ_of_lt hr)⟩, hF N (Nat.lt_succ_self N)⟩
  · rintro ⟨⟨hB, hF⟩, hN⟩
    refine ⟨hB, fun r hr => ?_⟩
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hr) with hr | rfl
    · exact hF r hr
    · exact hN

/-- The no-gap property propagates the Burn trial's finite entry along the
literal failed prefix. No additional candidate-finiteness premise is inserted. -/
theorem coupling_scope_trial_lost_entry_finite {d : ℕ}
    (Δ : ℝ≥0) (lam R : ℝ) (m : ℕ) (i : Fin d) (J N : ℕ)
    (q : FieldPair d × Regeneration.CoupledSample d)
    (hentry : ∀ n, Regeneration.trialFailureTime Δ R
      (Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)) i
        (Regeneration.trialStartSequence Δ lam R
          (Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)) i n) ≠ ⊤ →
      Regeneration.trialStartSequence Δ lam R
        (Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)) i (n + 1) ≠ ⊤)
    (hq : q ∈ couplingScopeTrialLost Δ lam R m i J N) :
    Regeneration.trialStartSequence Δ lam R
      (Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)) i (J + N) ≠ ⊤ := by
  cases N with
  | zero => exact hq.1.1
  | succ N =>
    rw [Nat.add_succ]
    exact hentry (J + N) (hq.2 N (Nat.lt_succ_self N))

/-- Disjoint literal trial slices assemble the no-return mass bound for a
Burn-selected failure prefix. The no-gap event is used only to exhaust entry. -/
theorem coupling_scope_trial_lost_success_bound_of_slice_estimates {d : ℕ}
    (μ : Measure (FieldPair d × Regeneration.CoupledSample d)) [IsProbabilityMeasure μ]
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (lam R : ℝ) (m : ℕ) (i : Fin d) (J N : ℕ)
    (hentry : ∀ᵐ q ∂μ, ∀ n,
      Regeneration.trialFailureTime Δ R
        (Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)) i
        (Regeneration.trialStartSequence Δ lam R
          (Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)) i n) ≠ ⊤ →
      Regeneration.trialStartSequence Δ lam R
        (Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)) i (n + 1) ≠ ⊤)
    (η : ℝ) (hη : 0 ≤ η)
    (hlower : ∀ k : ℕ,
      let S := couplingScopeTrialLost Δ lam R m i J N ∩
        {q | Regeneration.trialStartSequence Δ lam R
          (Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)) i (J + N) =
            ((((k + 1 : ℕ) : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞)}
      ENNReal.ofReal η * μ S ≤ μ (S ∩ {q | Regeneration.trialFailureTime Δ R
        (Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)) i
          (Regeneration.trialStartSequence Δ lam R
            (Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)) i (J + N)) = ⊤})) :
    η * μ.real (couplingScopeTrialLost Δ lam R m i J N) ≤
      μ.real (couplingScopeTrialLost Δ lam R m i J N ∩
        {q | Regeneration.trialFailureTime Δ R
          (Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)) i
            (Regeneration.trialStartSequence Δ lam R
              (Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)) i (J + N)) = ⊤}) := by
  let w := fun q : FieldPair d × Regeneration.CoupledSample d =>
    Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)
  let E := couplingScopeTrialLost Δ lam R m i J N
  let T := {q : FieldPair d × Regeneration.CoupledSample d |
    Regeneration.trialStartSequence Δ lam R (w q) i (J + N) ≠ ⊤}
  let F := {q : FieldPair d × Regeneration.CoupledSample d |
    Regeneration.trialFailureTime Δ R (w q) i
      (Regeneration.trialStartSequence Δ lam R (w q) i (J + N)) = ⊤}
  let S := fun k : ℕ => E ∩ {q : FieldPair d × Regeneration.CoupledSample d |
    Regeneration.trialStartSequence Δ lam R (w q) i (J + N) =
      ((((k + 1 : ℕ) : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞)}
  have hw : Measurable w :=
    (Regeneration.measurable_sampleTimeShift Δ).comp (measurable_const.prodMk measurable_snd)
  have hS (k : ℕ) : MeasurableSet (S k) :=
    (coupling_scope_measurableSet_trial_lost Δ lam R m i J N).inter
      (measurableSet_eq_fun
        ((Regeneration.measurable_trialStartSequence Δ lam R i (J + N)).comp hw)
        measurable_const)
  have hF : MeasurableSet F :=
    measurableSet_eq_fun ((Regeneration.measurable_trialFailureTime Δ R i).comp
      (((Regeneration.measurable_trialStartSequence Δ lam R i (J + N)).comp hw).prodMk hw))
      measurable_const
  have hdis : Pairwise (Disjoint on S) := by
    intro k l hkl
    apply Set.disjoint_left.mpr
    intro q hq hq'
    exact Set.disjoint_left.mp
      (coupling_scope_trial_start_slices_pairwise_disjoint Δ hΔ lam R i (J + N) hkl)
      (show (q.1, w q) ∈ _ from hq.2) (show (q.1, w q) ∈ _ from hq'.2)
  have hdisF : Pairwise (Disjoint on (fun k => S k ∩ F)) := by
    intro k l hkl
    exact (hdis hkl).mono Set.inter_subset_left Set.inter_subset_left
  have hpart : E ∩ T = ⋃ k, S k := by
    ext q
    constructor
    · rintro ⟨hq, ht⟩
      have hmem : (q.1, w q) ∈ ⋃ k,
          {p : FieldPair d × Regeneration.CoupledSample d |
            Regeneration.trialStartSequence Δ lam R p.2 i (J + N) =
              ((((k + 1 : ℕ) : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞)} := by
        rw [← coupling_scope_trial_entry_eq_iUnion_slices Δ hΔ lam R i (J + N)]
        exact ht
      obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hmem
      exact Set.mem_iUnion.mpr ⟨k, hq, hk⟩
    · intro hq
      obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hq
      exact ⟨hk.1, by change Regeneration.trialStartSequence Δ lam R (w q) i (J + N) ≠ ⊤
                      rw [hk.2]; exact ENNReal.coe_ne_top⟩
  have hmass : μ E = μ (E ∩ T) := by
    apply measure_congr
    filter_upwards [hentry] with q hq
    exact propext ⟨fun he => ⟨he,
      coupling_scope_trial_lost_entry_finite Δ lam R m i J N q hq he⟩, And.left⟩
  have hbound : ENNReal.ofReal η * μ E ≤ μ (E ∩ F) := by
    calc
      ENNReal.ofReal η * μ E = ENNReal.ofReal η * ∑' k, μ (S k) := by
        rw [hmass, hpart, measure_iUnion hdis hS]
      _ = ∑' k, ENNReal.ofReal η * μ (S k) := by rw [ENNReal.tsum_mul_left]
      _ ≤ ∑' k, μ (S k ∩ F) := ENNReal.tsum_le_tsum hlower
      _ = μ ((E ∩ T) ∩ F) := by
        rw [hpart, Set.iUnion_inter, measure_iUnion hdisF (fun k => (hS k).inter hF)]
      _ ≤ μ (E ∩ F) := measure_mono (Set.inter_subset_inter_left F Set.inter_subset_left)
  have hreal := (ENNReal.toReal_le_toReal
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top μ E))
    (measure_ne_top μ (E ∩ F))).mpr hbound
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hη, measureReal_def, E, F, w] using hreal

/-- The genuine selected-prebridge conditional estimate implies one Lost
contraction. Uniformity in later trials is retained in subsequent consumers. -/
theorem coupling_scope_trial_lost_step_of_prebridge_condExp {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (K : Regeneration.CoupledQuenchedLaws d) (hK : Regeneration.HasProbabilityLaws Q K)
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (δ : ℝ) (hδ : 0 ≤ δ)
    (hFresh : Regeneration.HasFreshBits Q Δ δ K)
    (lam R : ℝ) (hlam : 0 < lam) (hR : 0 < R) (m : ℕ) (i : Fin d) (J N : ℕ)
    (hentry : ∀ᵐ q ∂Regeneration.annealedCoupledLaw Q K, ∀ n,
      Regeneration.trialFailureTime Δ R
        (Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)) i
        (Regeneration.trialStartSequence Δ lam R
          (Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)) i n) ≠ ⊤ →
      Regeneration.trialStartSequence Δ lam R
        (Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)) i (n + 1) ≠ ⊤)
    (η : ℝ) (hη : 0 ≤ η) (hη1 : η ≤ 1)
    (hcond : ∀ k, ∀ᵐ q ∂Regeneration.annealedCoupledLaw Q K,
      q.2 ∈ couplingScopeTrialBurnPrebridge Δ lam R m i J N k →
        δ * η ≤ ((Regeneration.annealedCoupledLaw Q K)[
          ({p : FieldPair d × Regeneration.CoupledSample d | p.2.2 (m + k) = true ∧
            Regeneration.NoBacktracking R (Regeneration.pathTimeShift
              (Regeneration.sampleTimeShift Δ p.2 ((m : ℝ≥0) * Δ)).1
                (((k + 1 : ℕ) : ℝ≥0) * Δ)) i}).indicator (fun _ => (1 : ℝ)) |
                  couplingScopeAnnealedHistory Δ (m + k)]) q) :
    Regeneration.annealedCoupledLaw Q K (couplingScopeTrialLost Δ lam R m i J (N + 1)) ≤
      ENNReal.ofReal (1 - η) *
        Regeneration.annealedCoupledLaw Q K (couplingScopeTrialLost Δ lam R m i J N) := by
  let : IsProbabilityMeasure (Regeneration.annealedCoupledLaw Q K) :=
    Regeneration.annealedCoupledLaw_isProbabilityMeasure Q K hK
  have hw : Measurable (fun q : FieldPair d × Regeneration.CoupledSample d =>
      Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)) :=
    (Regeneration.measurable_sampleTimeShift Δ).comp (measurable_const.prodMk measurable_snd)
  have hF : MeasurableSet {q : FieldPair d × Regeneration.CoupledSample d |
      Regeneration.trialFailureTime Δ R
        (Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)) i
        (Regeneration.trialStartSequence Δ lam R
          (Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)) i (J + N)) = ⊤} :=
    measurableSet_eq_fun ((Regeneration.measurable_trialFailureTime Δ R i).comp
      (((Regeneration.measurable_trialStartSequence Δ lam R i (J + N)).comp hw).prodMk hw))
      measurable_const
  have hsuccess := coupling_scope_trial_lost_success_bound_of_slice_estimates
    (Regeneration.annealedCoupledLaw Q K) Δ hΔ lam R m i J N hentry η hη
    (fun k => coupling_scope_trial_lost_slice_success_of_prebridge_condExp
      Q K hK Δ hΔ δ hδ hFresh lam R hlam hR m i J N k η hη (hcond k))
  have h := ConditionalTrialExhaustion.measure_sdiff_le_of_success_measure
    (Regeneration.annealedCoupledLaw Q K) (couplingScopeTrialLost Δ lam R m i J N)
    _ hF η hη1 hsuccess
  rw [coupling_scope_trial_lost_succ]
  exact h

/-- The conditional estimate gives the finite geometric tail for actual
Burn-selected failures, with precisely the original Burn mass as prefactor. -/
theorem coupling_scope_trial_lost_product_of_prebridge_condExp {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (K : Regeneration.CoupledQuenchedLaws d) (hK : Regeneration.HasProbabilityLaws Q K)
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (δ : ℝ) (hδ : 0 ≤ δ)
    (hFresh : Regeneration.HasFreshBits Q Δ δ K)
    (lam R : ℝ) (hlam : 0 < lam) (hR : 0 < R) (m : ℕ) (i : Fin d) (J : ℕ)
    (hentry : ∀ᵐ q ∂Regeneration.annealedCoupledLaw Q K, ∀ n,
      Regeneration.trialFailureTime Δ R
        (Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)) i
        (Regeneration.trialStartSequence Δ lam R
          (Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)) i n) ≠ ⊤ →
      Regeneration.trialStartSequence Δ lam R
        (Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)) i (n + 1) ≠ ⊤)
    (η : ℝ) (hη : 0 ≤ η) (hη1 : η ≤ 1)
    (hcond : ∀ N k, ∀ᵐ q ∂Regeneration.annealedCoupledLaw Q K,
      q.2 ∈ couplingScopeTrialBurnPrebridge Δ lam R m i J N k →
        δ * η ≤ ((Regeneration.annealedCoupledLaw Q K)[
          ({p : FieldPair d × Regeneration.CoupledSample d | p.2.2 (m + k) = true ∧
            Regeneration.NoBacktracking R (Regeneration.pathTimeShift
              (Regeneration.sampleTimeShift Δ p.2 ((m : ℝ≥0) * Δ)).1
                (((k + 1 : ℕ) : ℝ≥0) * Δ)) i}).indicator (fun _ => (1 : ℝ)) |
                  couplingScopeAnnealedHistory Δ (m + k)]) q) (N : ℕ) :
    Regeneration.annealedCoupledLaw Q K (couplingScopeTrialLost Δ lam R m i J N) ≤
      ENNReal.ofReal (1 - η) ^ N *
        Regeneration.annealedCoupledLaw Q K (couplingScopeTrialBurn Δ lam R m i J) := by
  have h := ConditionalTrialExhaustion.finite_product_of_failure_step
    (Regeneration.annealedCoupledLaw Q K) (couplingScopeTrialLost Δ lam R m i J)
    (ENNReal.ofReal (1 - η))
    (fun n => coupling_scope_trial_lost_step_of_prebridge_condExp
      Q K hK Δ hΔ δ hδ hFresh lam R hlam hR m i J n hentry η hη hη1 (hcond n)) N
  rwa [coupling_scope_trial_lost_zero] at h

/-- Conditional estimates for the genuine Burn prebridges exclude infinite
first regeneration simultaneously at all original deterministic grids. -/
theorem coupling_scope_ae_all_grid_finite_of_burn_prebridge_condExp {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (K : Regeneration.CoupledQuenchedLaws d) (hK : Regeneration.HasProbabilityLaws Q K)
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (δ : ℝ) (hδ : 0 ≤ δ)
    (hFresh : Regeneration.HasFreshBits Q Δ δ K)
    (lam R : ℝ) (hlam : 0 < lam) (hR : 0 < R) (i : Fin d)
    (hescape : ∀ᵐ q ∂Regeneration.annealedCoupledLaw Q K,
      Filter.Tendsto (fun t : ℝ≥0 => q.2.1 t i) Filter.atTop Filter.atTop)
    (hentry : ∀ᵐ q ∂Regeneration.annealedCoupledLaw Q K, ∀ m : ℕ,
      let w := Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)
      Regeneration.trialStartSequence Δ lam R w i 0 ≠ ⊤ ∧
        ∀ n, Regeneration.trialFailureTime Δ R w i
          (Regeneration.trialStartSequence Δ lam R w i n) ≠ ⊤ →
            Regeneration.trialStartSequence Δ lam R w i (n + 1) ≠ ⊤)
    (η : ℝ) (hη : 0 < η) (hη1 : η ≤ 1)
    (hcond : ∀ m J N k, ∀ᵐ q ∂Regeneration.annealedCoupledLaw Q K,
      q.2 ∈ couplingScopeTrialBurnPrebridge Δ lam R m i J N k →
        δ * η ≤ ((Regeneration.annealedCoupledLaw Q K)[
          ({p : FieldPair d × Regeneration.CoupledSample d | p.2.2 (m + k) = true ∧
            Regeneration.NoBacktracking R (Regeneration.pathTimeShift
              (Regeneration.sampleTimeShift Δ p.2 ((m : ℝ≥0) * Δ)).1
                (((k + 1 : ℕ) : ℝ≥0) * Δ)) i}).indicator (fun _ => (1 : ℝ)) |
                  couplingScopeAnnealedHistory Δ (m + k)]) q) :
    ∀ᵐ q ∂Regeneration.annealedCoupledLaw Q K, ∀ m : ℕ,
      Regeneration.firstRegenerationTime Δ lam R
        (Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)) i ≠ ⊤ := by
  let : IsProbabilityMeasure (Regeneration.annealedCoupledLaw Q K) :=
    Regeneration.annealedCoupledLaw_isProbabilityMeasure Q K hK
  apply coupling_scope_ae_all_grid_first_regeneration_finite_of_burn_estimate
    _ Δ hΔ lam R hlam hR i hescape hentry η hη
  intro m J N
  exact coupling_scope_trial_lost_step_of_prebridge_condExp
    Q K hK Δ hΔ δ hδ hFresh lam R hlam hR m i J N
    (hentry.mono fun _ hq => (hq m).2) η hη.le hη1 (hcond m J N)

#print axioms coupling_scope_trial_lost_success_bound_of_slice_estimates
#print axioms coupling_scope_trial_lost_step_of_prebridge_condExp
#print axioms coupling_scope_trial_lost_product_of_prebridge_condExp
#print axioms coupling_scope_ae_all_grid_finite_of_burn_prebridge_condExp

#print axioms coupling_scope_trial_burn_prebridge_slice_eq
#print axioms coupling_scope_measure_trial_lost_slice_fresh_bit
#print axioms coupling_scope_trial_lost_slice_success_of_prebridge_condExp
#print axioms coupling_scope_trial_lost_zero
#print axioms coupling_scope_trial_lost_succ
#print axioms coupling_scope_trial_lost_entry_finite

/-- At the actual no-return mass, the uniform selected-prebridge conditional
estimate gives the literal all-cycle grid/record conclusion under both supplied
laws. Its analytic estimate and reduced-law escape are still producer obligations. -/
theorem coupling_scope_both_laws_grid_record_of_burn_prebridge_condExp {d : ℕ}
    (hd : 2 ≤ d) (lam l : ℝ) (hlam : 0 < lam) (hl : 0 < l)
    {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (K : Regeneration.CoupledQuenchedLaws d)
    (hK : Regeneration.HasProbabilityLaws Q.measure K)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hFresh : Regeneration.HasFreshBits Q.measure (Regeneration.Renewal.regenDelta lam) δ K)
    (hD : Regeneration.annealedCoupledLaw Q.measure K
      (regenerationNoReturn hd (l / lam)) ≠ 0)
    (hescape : ∀ᵐ q ∂Regeneration.annealedCoupledLaw Q.measure K, Filter.Tendsto
      (fun t : ℝ≥0 => q.2.1 t (Regeneration.Renewal.forceCoord hd))
        Filter.atTop Filter.atTop)
    (hentry : ∀ᵐ q ∂Regeneration.annealedCoupledLaw Q.measure K, ∀ m : ℕ,
      let Δ := Regeneration.Renewal.regenDelta lam
      let w := Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)
      let i := Regeneration.Renewal.forceCoord hd
      Regeneration.trialStartSequence Δ lam (l / lam) w i 0 ≠ ⊤ ∧
        ∀ n, Regeneration.trialFailureTime Δ (l / lam) w i
          (Regeneration.trialStartSequence Δ lam (l / lam) w i n) ≠ ⊤ →
            Regeneration.trialStartSequence Δ lam (l / lam) w i (n + 1) ≠ ⊤)
    (hcond : ∀ m J N k,
      let Δ := Regeneration.Renewal.regenDelta lam
      let i := Regeneration.Renewal.forceCoord hd
      let cD := (Regeneration.annealedCoupledLaw Q.measure K
        (regenerationNoReturn hd (l / lam))).toReal
      ∀ᵐ q ∂Regeneration.annealedCoupledLaw Q.measure K,
        q.2 ∈ couplingScopeTrialBurnPrebridge Δ lam (l / lam) m i J N k →
          δ * cD ≤ ((Regeneration.annealedCoupledLaw Q.measure K)[
            ({p : FieldPair d × Regeneration.CoupledSample d | p.2.2 (m + k) = true ∧
              Regeneration.NoBacktracking (l / lam) (Regeneration.pathTimeShift
                (Regeneration.sampleTimeShift Δ p.2 ((m : ℝ≥0) * Δ)).1
                  (((k + 1 : ℕ) : ℝ≥0) * Δ)) i}).indicator (fun _ => (1 : ℝ)) |
                    couplingScopeAnnealedHistory Δ (m + k)]) q) :
    ∀ k : ℕ, ∀ ρ ∈ ({Regeneration.annealedCoupledLaw Q.measure K,
        regenerationConditionedLaw hd Q lam l K hK hD} :
          Set (Measure (FieldPair d × Regeneration.CoupledSample d))),
      ∀ᵐ q ∂ρ, ∃ n : ℕ, 2 * k ≤ n ∧
        regenerationTime hd lam l k q.2 =
          (((n : ℝ≥0) * Regeneration.Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞) ∧
        regenerationRecord hd lam l k q =
          Regeneration.futureRecord (Regeneration.Renewal.regenDelta lam) (l / lam)
            q.1 q.2 (Regeneration.Renewal.forceCoord hd)
            ((n : ℝ≥0) * Regeneration.Renewal.regenDelta lam) := by
  let : IsProbabilityMeasure (Regeneration.annealedCoupledLaw Q.measure K) :=
    Regeneration.annealedCoupledLaw_isProbabilityMeasure Q.measure K hK
  have hΔ : 0 < Regeneration.Renewal.regenDelta lam :=
    Real.toNNReal_pos.mpr (inv_pos.mpr (sq_pos_of_pos hlam))
  apply coupling_scope_both_laws_grid_record_of_burn_estimate
    hd lam l hlam hl Q K hK hD hescape hentry
  intro m J N
  exact coupling_scope_trial_lost_step_of_prebridge_condExp
    Q.measure K hK _ hΔ δ hδ hFresh lam (l / lam) hlam (div_pos hl hlam)
    m _ J N (hentry.mono fun _ hq => (hq m).2) _ ENNReal.toReal_nonneg
    measureReal_le_one (hcond m J N)


/-- For a joint kernel with the actual source split property, its checked
probability and fresh-bit producers instantiate the selected-trial tail. The
conditional no-return estimate remains explicit. No joint kernel is constructed. -/
theorem coupling_scope_trial_lost_product_of_source_split_prebridge_condExp {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (δ : ℝ) (hδ : 0 ≤ δ)
    (lam R : ℝ) (hlam : 0 < lam) (hR : 0 < R) (m : ℕ) (i : Fin d) (J : ℕ)
    (hsource : ∀ᵐ ω ∂Q,
      External.Source.GMP.IsSourceSplitCoupling (fun x => P (x, ω)) Δ δ R i
        (fun x => K (x, ω)))
    (hentry : ∀ᵐ q ∂Regeneration.annealedCoupledLaw Q K, ∀ n,
      Regeneration.trialFailureTime Δ R
        (Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)) i
        (Regeneration.trialStartSequence Δ lam R
          (Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)) i n) ≠ ⊤ →
      Regeneration.trialStartSequence Δ lam R
        (Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)) i (n + 1) ≠ ⊤)
    (η : ℝ) (hη : 0 ≤ η) (hη1 : η ≤ 1)
    (hcond : ∀ N k, ∀ᵐ q ∂Regeneration.annealedCoupledLaw Q K,
      q.2 ∈ couplingScopeTrialBurnPrebridge Δ lam R m i J N k →
        δ * η ≤ ((Regeneration.annealedCoupledLaw Q K)[
          ({p : FieldPair d × Regeneration.CoupledSample d | p.2.2 (m + k) = true ∧
            Regeneration.NoBacktracking R (Regeneration.pathTimeShift
              (Regeneration.sampleTimeShift Δ p.2 ((m : ℝ≥0) * Δ)).1
                (((k + 1 : ℕ) : ℝ≥0) * Δ)) i}).indicator (fun _ => (1 : ℝ)) |
                  couplingScopeAnnealedHistory Δ (m + k)]) q) (N : ℕ) :
    Regeneration.annealedCoupledLaw Q K (couplingScopeTrialLost Δ lam R m i J N) ≤
      ENNReal.ofReal (1 - η) ^ N *
        Regeneration.annealedCoupledLaw Q K (couplingScopeTrialBurn Δ lam R m i J) := by
  obtain ⟨hK, _, hFresh, _⟩ :=
    EinsteinFull.Regeneration.source_split_joint_kernel_properties Q P K hsource hδ hR
  exact coupling_scope_trial_lost_product_of_prebridge_condExp
    Q K hK Δ hΔ δ hδ hFresh lam R hlam hR m i J hentry η hη hη1 hcond N


/-- Number of consecutive failures retained after the literal Burn trial `J`.
It is zero off Burn and infinite if every retained trial fails. This counts
trials, without assigning any bound to elapsed time or to the Burn index. -/
noncomputable def couplingScopeRetainedFailureCount {d : ℕ} (Δ : ℝ≥0)
    (lam R : ℝ) (m : ℕ) (i : Fin d) (J : ℕ)
    (q : FieldPair d × Regeneration.CoupledSample d) : ℕ∞ := by
  classical
  exact ⨆ N : ℕ, if q ∈ couplingScopeTrialLost Δ lam R m i J N then (N : ℕ∞) else 0

/-- A finite upper bound on the retained count is exactly failure of the next
literal Lost prefix. No almost-sure finite-entry assumption is used here. -/
theorem coupling_scope_retained_count_le_iff {d : ℕ} (Δ : ℝ≥0)
    (lam R : ℝ) (m : ℕ) (i : Fin d) (J N : ℕ)
    (q : FieldPair d × Regeneration.CoupledSample d) :
    couplingScopeRetainedFailureCount Δ lam R m i J q ≤ (N : ℕ∞) ↔
      q ∉ couplingScopeTrialLost Δ lam R m i J (N + 1) := by
  classical
  unfold couplingScopeRetainedFailureCount
  constructor
  · intro h hq
    have hnext : ((N + 1 : ℕ) : ℕ∞) ≤
        couplingScopeRetainedFailureCount Δ lam R m i J q := by
      exact le_iSup_of_le (N + 1) (by simp only [ite_eq_left hq, le_refl])
    have hbad := ENat.natCast_le_natCast.mp (hnext.trans h)
    omega
  · intro hq
    apply iSup_le
    intro k
    split_ifs with hk
    · apply ENat.natCast_le_natCast.mpr
      by_contra hkn
      exact hq (coupling_scope_trial_lost_antitone Δ lam R m i J
        (show N + 1 ≤ k by omega) hk)
    · exact bot_le

/-- The upper tails of the extended natural count are the original Lost
prefixes, with the failure index `J + r` unchanged. -/
theorem coupling_scope_retained_count_tail_iff {d : ℕ} (Δ : ℝ≥0)
    (lam R : ℝ) (m : ℕ) (i : Fin d) (J N : ℕ)
    (q : FieldPair d × Regeneration.CoupledSample d) :
    (N : ℕ∞) < couplingScopeRetainedFailureCount Δ lam R m i J q ↔
      q ∈ couplingScopeTrialLost Δ lam R m i J (N + 1) := by
  rw [← not_le, coupling_scope_retained_count_le_iff, not_not]

/-- Off the original Burn event the retained count is exactly zero. -/
theorem coupling_scope_retained_count_eq_zero_off_burn {d : ℕ} (Δ : ℝ≥0)
    (lam R : ℝ) (m : ℕ) (i : Fin d) (J : ℕ)
    (q : FieldPair d × Regeneration.CoupledSample d)
    (hq : q ∉ couplingScopeTrialBurn Δ lam R m i J) :
    couplingScopeRetainedFailureCount Δ lam R m i J q = 0 := by
  apply le_antisymm ?_ bot_le
  apply (coupling_scope_retained_count_le_iff Δ lam R m i J 0 q).mpr
  exact fun h => hq h.1

/-- Infinite count retains both Burn and failure of every actual trial after
`J`; infinity is never silently converted to a finite natural number. -/
theorem coupling_scope_retained_count_eq_top_iff {d : ℕ} (Δ : ℝ≥0)
    (lam R : ℝ) (m : ℕ) (i : Fin d) (J : ℕ)
    (q : FieldPair d × Regeneration.CoupledSample d) :
    couplingScopeRetainedFailureCount Δ lam R m i J q = ⊤ ↔
      q ∈ couplingScopeTrialBurn Δ lam R m i J ∧
      ∀ r, Regeneration.trialFailureTime Δ R
        (Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)) i
        (Regeneration.trialStartSequence Δ lam R
          (Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)) i (J + r)) ≠ ⊤ := by
  rw [ENat.eq_top_iff_forall_gt]
  simp only [coupling_scope_retained_count_tail_iff]
  constructor
  · intro h
    exact ⟨(h 0).1, fun r => (h r).2 r (Nat.lt_succ_self r)⟩
  · rintro ⟨hB, hF⟩ N
    exact ⟨hB, fun r _ => hF r⟩


/-- On Burn, a finite retained depth is exactly the first infinite failure
time after the specified consecutive finite failures at indices `J + r`. -/
theorem coupling_scope_retained_count_eq_natCast_iff {d : ℕ} (Δ : ℝ≥0)
    (lam R : ℝ) (m : ℕ) (i : Fin d) (J N : ℕ)
    (q : FieldPair d × Regeneration.CoupledSample d)
    (hB : q ∈ couplingScopeTrialBurn Δ lam R m i J) :
    couplingScopeRetainedFailureCount Δ lam R m i J q = (N : ℕ∞) ↔
      (∀ r < N, Regeneration.trialFailureTime Δ R
        (Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)) i
        (Regeneration.trialStartSequence Δ lam R
          (Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)) i (J + r)) ≠ ⊤) ∧
      Regeneration.trialFailureTime Δ R
        (Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)) i
        (Regeneration.trialStartSequence Δ lam R
          (Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)) i (J + N)) = ⊤ := by
  classical
  constructor
  · intro hN
    have hprefix : q ∈ couplingScopeTrialLost Δ lam R m i J N := by
      refine ⟨hB, fun r hr => ?_⟩
      have htail := (coupling_scope_retained_count_tail_iff Δ lam R m i J r q).mp
        (by rw [hN]; exact ENat.natCast_lt_natCast.mpr hr)
      exact htail.2 r (Nat.lt_succ_self r)
    refine ⟨hprefix.2, ?_⟩
    by_contra hfail
    have hnext : q ∈ couplingScopeTrialLost Δ lam R m i J (N + 1) := by
      rw [coupling_scope_trial_lost_succ]
      exact ⟨hprefix, hfail⟩
    exact ((coupling_scope_retained_count_le_iff Δ lam R m i J N q).mp hN.le) hnext
  · rintro ⟨hprefix, hfail⟩
    apply le_antisymm
    · apply (coupling_scope_retained_count_le_iff Δ lam R m i J N q).mpr
      intro hnext
      exact hnext.2 N (Nat.lt_succ_self N) hfail
    · exact le_iSup_of_le N (by simp only [ite_eq_left (show q ∈
        couplingScopeTrialLost Δ lam R m i J N from ⟨hB, hprefix⟩), le_refl])

/-- With the genuine no-gap property, a finite retained depth is realized by
a finite actual trial whose original shifted path never backtracks. -/
theorem coupling_scope_retained_count_finite_noBacktracking {d : ℕ} (Δ : ℝ≥0)
    (lam R : ℝ) (m : ℕ) (i : Fin d) (J N : ℕ)
    (q : FieldPair d × Regeneration.CoupledSample d)
    (hB : q ∈ couplingScopeTrialBurn Δ lam R m i J)
    (hN : couplingScopeRetainedFailureCount Δ lam R m i J q = (N : ℕ∞))
    (hentry : ∀ n, Regeneration.trialFailureTime Δ R
      (Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)) i
        (Regeneration.trialStartSequence Δ lam R
          (Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)) i n) ≠ ⊤ →
      Regeneration.trialStartSequence Δ lam R
        (Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)) i (n + 1) ≠ ⊤) :
    let w := Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)
    let S := Regeneration.trialStartSequence Δ lam R w i (J + N)
    S ≠ ⊤ ∧ Regeneration.NoBacktracking R (Regeneration.pathTimeShift w.1 S.toNNReal) i := by
  obtain ⟨hprefix, hfail⟩ :=
    (coupling_scope_retained_count_eq_natCast_iff Δ lam R m i J N q hB).mp hN
  have hS := coupling_scope_trial_lost_entry_finite Δ lam R m i J N q hentry ⟨hB, hprefix⟩
  exact ⟨hS, (Regeneration.trialFailureTime_eq_top_iff_noBacktracking Δ R _ i _ hS).mp hfail⟩

/-- The retained count is measurable, including its infinite and off-Burn
branches, by its original measurable finite prefixes. -/
theorem coupling_scope_measurable_retained_count {d : ℕ} (Δ : ℝ≥0)
    (lam R : ℝ) (m : ℕ) (i : Fin d) (J : ℕ) :
    Measurable (couplingScopeRetainedFailureCount Δ lam R m i J) := by
  apply ENat.measurable_iff.mpr
  intro N
  cases N with
  | zero =>
    have heq : (couplingScopeRetainedFailureCount Δ lam R m i J) ⁻¹' {0} =
        (couplingScopeTrialLost Δ lam R m i J 1)ᶜ := by
      ext q
      change _ = 0 ↔ _
      rw [← le_zero_iff]
      exact coupling_scope_retained_count_le_iff Δ lam R m i J 0 q
    rw [show ((0 : ℕ) : ℕ∞) = 0 from rfl, heq]
    exact (coupling_scope_measurableSet_trial_lost Δ lam R m i J 1).compl
  | succ N =>
    have heq : (couplingScopeRetainedFailureCount Δ lam R m i J) ⁻¹' {↑(N + 1)} =
        couplingScopeTrialLost Δ lam R m i J (N + 1) ∩
          (couplingScopeTrialLost Δ lam R m i J (N + 1 + 1))ᶜ := by
      ext q
      change _ = _ ↔ _ ∧ _
      rw [le_antisymm_iff, coupling_scope_retained_count_le_iff,
        Nat.cast_add, Nat.cast_one, ENat.natCast_add_one_le_iff,
        coupling_scope_retained_count_tail_iff, and_comm]
      rfl
    rw [heq]
    exact (coupling_scope_measurableSet_trial_lost Δ lam R m i J (N + 1)).inter
      (coupling_scope_measurableSet_trial_lost Δ lam R m i J (N + 1 + 1)).compl

/-- The extended natural retained count has the exact pointwise tail sum of
literal retained-failure indicators. -/
theorem coupling_scope_retained_count_toENNReal_eq_tsum {d : ℕ} (Δ : ℝ≥0)
    (lam R : ℝ) (m : ℕ) (i : Fin d) (J : ℕ)
    (q : FieldPair d × Regeneration.CoupledSample d) :
    (couplingScopeRetainedFailureCount Δ lam R m i J q).toENNReal =
      ∑' n : ℕ, (couplingScopeTrialLost Δ lam R m i J (n + 1)).indicator
        (fun _ => (1 : ℝ≥0∞)) q := by
  classical
  by_cases htop : couplingScopeRetainedFailureCount Δ lam R m i J q = ⊤
  · have hall : ∀ n, q ∈ couplingScopeTrialLost Δ lam R m i J (n + 1) := by
      intro n
      apply (coupling_scope_retained_count_tail_iff Δ lam R m i J n q).mp
      rw [htop]
      exact WithTop.coe_lt_top n
    simp only [htop, ENat.toENNReal_top, Set.indicator_of_mem (hall _)]
    exact (ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero).symm
  · obtain ⟨N, hN⟩ := ENat.ne_top_iff_exists.mp htop
    have hmem : ∀ n, q ∈ couplingScopeTrialLost Δ lam R m i J (n + 1) ↔ n < N := by
      intro n
      rw [← coupling_scope_retained_count_tail_iff, ← hN, ENat.natCast_lt_natCast]
    rw [← hN, ENat.toENNReal_coe]
    symm
    rw [tsum_eq_sum (s := Finset.range N)]
    · simp only [Set.indicator_apply, hmem]
      calc
        (∑ n ∈ Finset.range N, if n < N then (1 : ℝ≥0∞) else 0) =
            ∑ _n ∈ Finset.range N, (1 : ℝ≥0∞) := by
          apply Finset.sum_congr rfl
          intro n hn
          exact ite_eq_left (Finset.mem_range.mp hn)
        _ = N := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    · intro n hn
      exact Set.indicator_of_notMem (by simpa only [hmem, Finset.mem_range] using hn) _

/-- The count's nonnegative-real embedding is measurable by the exact tail
sum; this avoids any implicit replacement of the count by its real value. -/
theorem coupling_scope_measurable_retained_count_toENNReal {d : ℕ} (Δ : ℝ≥0)
    (lam R : ℝ) (m : ℕ) (i : Fin d) (J : ℕ) :
    Measurable (fun q =>
      (couplingScopeRetainedFailureCount Δ lam R m i J q).toENNReal) := by
  simp_rw [coupling_scope_retained_count_toENNReal_eq_tsum]
  exact Measurable.tsum fun n => measurable_const.indicator
    (coupling_scope_measurableSet_trial_lost Δ lam R m i J (n + 1))

/-- Finite retained-tail sums integrate to the corresponding finite sum of
actual Lost masses, under any measure on the original samples. -/
theorem coupling_scope_lintegral_retained_tail_finset {d : ℕ} (Δ : ℝ≥0)
    (lam R : ℝ) (m : ℕ) (i : Fin d) (J L : ℕ)
    (μ : Measure (FieldPair d × Regeneration.CoupledSample d)) :
    (∫⁻ q, ∑ n ∈ Finset.range L,
      (couplingScopeTrialLost Δ lam R m i J (n + 1)).indicator
        (fun _ => (1 : ℝ≥0∞)) q ∂μ) =
      ∑ n ∈ Finset.range L, μ (couplingScopeTrialLost Δ lam R m i J (n + 1)) := by
  rw [lintegral_finsetSum _ (fun n _ => measurable_const.indicator
    (coupling_scope_measurableSet_trial_lost Δ lam R m i J (n + 1)))]
  apply Finset.sum_congr rfl
  intro n _
  rw [lintegral_indicator_const
    (coupling_scope_measurableSet_trial_lost Δ lam R m i J (n + 1)), one_mul]

/-- Tonelli gives the exact infinite retained-tail identity, even when its
value is infinite. It requires no contraction or independent-trial model. -/
theorem coupling_scope_lintegral_retained_count_eq_tsum {d : ℕ} (Δ : ℝ≥0)
    (lam R : ℝ) (m : ℕ) (i : Fin d) (J : ℕ)
    (μ : Measure (FieldPair d × Regeneration.CoupledSample d)) :
    (∫⁻ q, (couplingScopeRetainedFailureCount Δ lam R m i J q).toENNReal ∂μ) =
      ∑' n : ℕ, μ (couplingScopeTrialLost Δ lam R m i J (n + 1)) := by
  simp_rw [coupling_scope_retained_count_toENNReal_eq_tsum]
  rw [lintegral_tsum (fun n => (measurable_const.indicator
    (coupling_scope_measurableSet_trial_lost Δ lam R m i J (n + 1))).aemeasurable)]
  apply tsum_congr
  intro n
  rw [lintegral_indicator_const
    (coupling_scope_measurableSet_trial_lost Δ lam R m i J (n + 1)), one_mul]


/-- A geometric bound for the actual Lost events sums with their original
Burn mass. At ratio zero this also covers sure success of the retained trial. -/
theorem coupling_scope_lintegral_retained_count_le_of_geometric_tail {d : ℕ}
    (Δ : ℝ≥0) (lam R : ℝ) (m : ℕ) (i : Fin d) (J : ℕ)
    (μ : Measure (FieldPair d × Regeneration.CoupledSample d)) (a : ℝ≥0∞)
    (htail : ∀ N, μ (couplingScopeTrialLost Δ lam R m i J N) ≤
      a ^ N * μ (couplingScopeTrialBurn Δ lam R m i J)) :
    (∫⁻ q, (couplingScopeRetainedFailureCount Δ lam R m i J q).toENNReal ∂μ) ≤
      a * (1 - a)⁻¹ * μ (couplingScopeTrialBurn Δ lam R m i J) := by
  rw [coupling_scope_lintegral_retained_count_eq_tsum]
  calc
    (∑' n : ℕ, μ (couplingScopeTrialLost Δ lam R m i J (n + 1))) ≤
        ∑' n : ℕ, a ^ (n + 1) * μ (couplingScopeTrialBurn Δ lam R m i J) :=
      ENNReal.tsum_le_tsum fun n => htail (n + 1)
    _ = _ := by rw [ENNReal.tsum_mul_right, ENNReal.tsum_geometric_add_one]

/-- Positive success mass makes the geometric retained-depth majorant finite
under the original finite law. No normalization by Burn is required. -/
theorem coupling_scope_lintegral_retained_count_ne_top_of_geometric_tail {d : ℕ}
    (Δ : ℝ≥0) (lam R : ℝ) (m : ℕ) (i : Fin d) (J : ℕ)
    (μ : Measure (FieldPair d × Regeneration.CoupledSample d)) [IsFiniteMeasure μ]
    (a : ℝ≥0∞) (ha : a < 1)
    (htail : ∀ N, μ (couplingScopeTrialLost Δ lam R m i J N) ≤
      a ^ N * μ (couplingScopeTrialBurn Δ lam R m i J)) :
    (∫⁻ q, (couplingScopeRetainedFailureCount Δ lam R m i J q).toENNReal ∂μ) ≠ ⊤ := by
  apply ne_top_of_le_ne_top _
    (coupling_scope_lintegral_retained_count_le_of_geometric_tail Δ lam R m i J μ a htail)
  exact ENNReal.mul_ne_top
    (ENNReal.mul_ne_top (ne_top_of_lt ha)
      (ENNReal.inv_ne_top.mpr (ne_of_gt (tsub_pos_iff_lt.mpr ha))))
    (measure_ne_top μ _)

/-- The actual retained count is almost surely finite and its real embedding
is integrable once its nonnegative integral is finite. -/
theorem coupling_scope_retained_count_integrable_of_lintegral_ne_top {d : ℕ}
    (Δ : ℝ≥0) (lam R : ℝ) (m : ℕ) (i : Fin d) (J : ℕ)
    (μ : Measure (FieldPair d × Regeneration.CoupledSample d))
    (hfin : (∫⁻ q,
      (couplingScopeRetainedFailureCount Δ lam R m i J q).toENNReal ∂μ) ≠ ⊤) :
    (∀ᵐ q ∂μ, couplingScopeRetainedFailureCount Δ lam R m i J q ≠ ⊤) ∧
      Integrable (fun q =>
        (couplingScopeRetainedFailureCount Δ lam R m i J q).toENNReal.toReal) μ := by
  have hm := coupling_scope_measurable_retained_count_toENNReal Δ lam R m i J
  refine ⟨?_, integrable_toReal_of_lintegral_ne_top hm.aemeasurable hfin⟩
  filter_upwards [ae_lt_top hm hfin] with q hq
  exact ENat.toENNReal_ne_top.mp hq.ne

/-- The real tail masses have an actual HasSum whose value is the expected
retained failure count. Finiteness is proved before converting from infinity. -/
theorem coupling_scope_hasSum_retained_tail_of_lintegral_ne_top {d : ℕ}
    (Δ : ℝ≥0) (lam R : ℝ) (m : ℕ) (i : Fin d) (J : ℕ)
    (μ : Measure (FieldPair d × Regeneration.CoupledSample d))
    (hfin : (∫⁻ q,
      (couplingScopeRetainedFailureCount Δ lam R m i J q).toENNReal ∂μ) ≠ ⊤) :
    HasSum (fun n : ℕ => μ.real (couplingScopeTrialLost Δ lam R m i J (n + 1)))
      (∫ q, (couplingScopeRetainedFailureCount Δ lam R m i J q).toENNReal.toReal ∂μ) := by
  have hm := coupling_scope_measurable_retained_count_toENNReal Δ lam R m i J
  rw [integral_toReal hm.aemeasurable (ae_lt_top hm hfin),
    coupling_scope_lintegral_retained_count_eq_tsum]
  have hsum : (∑' n : ℕ, μ (couplingScopeTrialLost Δ lam R m i J (n + 1))) ≠ ⊤ := by
    rwa [← coupling_scope_lintegral_retained_count_eq_tsum]
  have ht := ENNReal.hasSum_toReal hsum
  rw [← ENNReal.tsum_toReal_eq (ENNReal.ne_top_of_tsum_ne_top hsum)] at ht
  exact ht

/-- The literal D-conditioned expectation is the restricted Lost-tail sum
divided by the original no-return mass, retaining the actual supplied law. -/
theorem coupling_scope_lintegral_conditioned_retained_count_eq_tsum {d : ℕ}
    (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (lam l : ℝ)
    (K : Regeneration.CoupledQuenchedLaws d) (hK : Regeneration.HasProbabilityLaws Q.measure K)
    (hD : Regeneration.annealedCoupledLaw Q.measure K
      (regenerationNoReturn hd (l / lam)) ≠ 0)
    (m J : ℕ) :
    (∫⁻ q, (couplingScopeRetainedFailureCount (Regeneration.Renewal.regenDelta lam)
      lam (l / lam) m (Regeneration.Renewal.forceCoord hd) J q).toENNReal
        ∂regenerationConditionedLaw hd Q lam l K hK hD) =
      (Regeneration.annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam)))⁻¹ *
        ∑' n : ℕ, Regeneration.annealedCoupledLaw Q.measure K
          (regenerationNoReturn hd (l / lam) ∩
            couplingScopeTrialLost (Regeneration.Renewal.regenDelta lam)
              lam (l / lam) m (Regeneration.Renewal.forceCoord hd) J (n + 1)) := by
  rw [regenerationConditionedLaw, ProbabilityTheory.cond, lintegral_smul_measure,
    smul_eq_mul, coupling_scope_lintegral_retained_count_eq_tsum]
  congr 1
  apply tsum_congr
  intro n
  rw [Measure.restrict_apply (coupling_scope_measurableSet_trial_lost _ _ _ _ _ _ _),
    Set.inter_comm]

/-- Restriction and the exact positive D denominator transport the checked
annealed geometric majorant to the literal regeneration-conditioned law. -/
theorem coupling_scope_lintegral_conditioned_retained_count_le_of_geometric_tail {d : ℕ}
    (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (lam l : ℝ)
    (K : Regeneration.CoupledQuenchedLaws d) (hK : Regeneration.HasProbabilityLaws Q.measure K)
    (hD : Regeneration.annealedCoupledLaw Q.measure K
      (regenerationNoReturn hd (l / lam)) ≠ 0)
    (m J : ℕ) (a : ℝ≥0∞)
    (htail : ∀ N, Regeneration.annealedCoupledLaw Q.measure K
      (couplingScopeTrialLost (Regeneration.Renewal.regenDelta lam) lam (l / lam)
        m (Regeneration.Renewal.forceCoord hd) J N) ≤ a ^ N *
      Regeneration.annealedCoupledLaw Q.measure K
        (couplingScopeTrialBurn (Regeneration.Renewal.regenDelta lam) lam (l / lam)
          m (Regeneration.Renewal.forceCoord hd) J)) :
    (∫⁻ q, (couplingScopeRetainedFailureCount (Regeneration.Renewal.regenDelta lam)
      lam (l / lam) m (Regeneration.Renewal.forceCoord hd) J q).toENNReal
        ∂regenerationConditionedLaw hd Q lam l K hK hD) ≤
      (Regeneration.annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam)))⁻¹ *
        (a * (1 - a)⁻¹ * Regeneration.annealedCoupledLaw Q.measure K
          (couplingScopeTrialBurn (Regeneration.Renewal.regenDelta lam) lam (l / lam)
            m (Regeneration.Renewal.forceCoord hd) J)) := by
  rw [regenerationConditionedLaw, ProbabilityTheory.cond, lintegral_smul_measure, smul_eq_mul]
  apply mul_le_mul_right
  exact (lintegral_mono' Measure.restrict_le_self (le_refl _)).trans
    (coupling_scope_lintegral_retained_count_le_of_geometric_tail _ _ _ _ _ _ _ a htail)

/-- Both original laws have integrable retained failure count for each fixed
Burn selection. The normalization is finite by the given positive D mass. -/
theorem coupling_scope_both_laws_retained_count_integrable_of_geometric_tail {d : ℕ}
    (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (lam l : ℝ)
    (K : Regeneration.CoupledQuenchedLaws d) (hK : Regeneration.HasProbabilityLaws Q.measure K)
    (hD : Regeneration.annealedCoupledLaw Q.measure K
      (regenerationNoReturn hd (l / lam)) ≠ 0)
    (m J : ℕ) (a : ℝ≥0∞) (ha : a < 1)
    (htail : ∀ N, Regeneration.annealedCoupledLaw Q.measure K
      (couplingScopeTrialLost (Regeneration.Renewal.regenDelta lam) lam (l / lam)
        m (Regeneration.Renewal.forceCoord hd) J N) ≤ a ^ N *
      Regeneration.annealedCoupledLaw Q.measure K
        (couplingScopeTrialBurn (Regeneration.Renewal.regenDelta lam) lam (l / lam)
          m (Regeneration.Renewal.forceCoord hd) J)) :
    ∀ ρ ∈ ({Regeneration.annealedCoupledLaw Q.measure K,
        regenerationConditionedLaw hd Q lam l K hK hD} :
          Set (Measure (FieldPair d × Regeneration.CoupledSample d))),
      (∀ᵐ q ∂ρ, couplingScopeRetainedFailureCount (Regeneration.Renewal.regenDelta lam)
        lam (l / lam) m (Regeneration.Renewal.forceCoord hd) J q ≠ ⊤) ∧
      Integrable (fun q => (couplingScopeRetainedFailureCount (Regeneration.Renewal.regenDelta lam)
        lam (l / lam) m (Regeneration.Renewal.forceCoord hd) J q).toENNReal.toReal) ρ := by
  let μ := Regeneration.annealedCoupledLaw Q.measure K
  let : IsProbabilityMeasure μ := Regeneration.annealedCoupledLaw_isProbabilityMeasure Q.measure K hK
  have hfin := coupling_scope_lintegral_retained_count_ne_top_of_geometric_tail
    (Regeneration.Renewal.regenDelta lam) lam (l / lam) m (Regeneration.Renewal.forceCoord hd)
    J μ a ha htail
  intro ρ hρ
  apply coupling_scope_retained_count_integrable_of_lintegral_ne_top
  rcases Set.mem_insert_iff.mp hρ with rfl | hρ
  · exact hfin
  · have hρeq := Set.mem_singleton_iff.mp hρ
    rw [hρeq, regenerationConditionedLaw, ProbabilityTheory.cond,
      lintegral_smul_measure, smul_eq_mul]
    exact ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr hD)
      (ne_top_of_le_ne_top hfin (lintegral_mono' Measure.restrict_le_self (le_refl _)))


/-- Retained trial depth includes the successful trial after the consecutive
failures, on Burn only; it remains infinite if all retained trials fail. -/
noncomputable def couplingScopeRetainedTrialCount {d : ℕ} (Δ : ℝ≥0)
    (lam R : ℝ) (m : ℕ) (i : Fin d) (J : ℕ)
    (q : FieldPair d × Regeneration.CoupledSample d) : ℕ∞ := by
  classical
  exact if q ∈ couplingScopeTrialBurn Δ lam R m i J then
    couplingScopeRetainedFailureCount Δ lam R m i J q + 1 else 0

/-- Including the successful trial adds the original Burn indicator, with
zero still assigned outside Burn. -/
theorem coupling_scope_retained_trial_count_toENNReal_eq_add {d : ℕ} (Δ : ℝ≥0)
    (lam R : ℝ) (m : ℕ) (i : Fin d) (J : ℕ)
    (q : FieldPair d × Regeneration.CoupledSample d) :
    (couplingScopeRetainedTrialCount Δ lam R m i J q).toENNReal =
      (couplingScopeRetainedFailureCount Δ lam R m i J q).toENNReal +
        (couplingScopeTrialBurn Δ lam R m i J).indicator (fun _ => (1 : ℝ≥0∞)) q := by
  classical
  by_cases hB : q ∈ couplingScopeTrialBurn Δ lam R m i J
  · simp only [couplingScopeRetainedTrialCount, ite_eq_left hB, ENat.toENNReal_add,
      ENat.toENNReal_one, Set.indicator_of_mem hB]
  · simp only [couplingScopeRetainedTrialCount, ite_eq_right hB,
      coupling_scope_retained_count_eq_zero_off_burn Δ lam R m i J q hB,
      ENat.toENNReal_zero, Set.indicator_of_notMem hB, add_zero]

/-- The retained trial depth has the exact tail sum starting at Lost zero,
so the success trial is counted once precisely on the Burn event. -/
theorem coupling_scope_retained_trial_count_toENNReal_eq_tsum {d : ℕ} (Δ : ℝ≥0)
    (lam R : ℝ) (m : ℕ) (i : Fin d) (J : ℕ)
    (q : FieldPair d × Regeneration.CoupledSample d) :
    (couplingScopeRetainedTrialCount Δ lam R m i J q).toENNReal =
      ∑' n : ℕ, (couplingScopeTrialLost Δ lam R m i J n).indicator
        (fun _ => (1 : ℝ≥0∞)) q := by
  rw [coupling_scope_retained_trial_count_toENNReal_eq_add,
    coupling_scope_retained_count_toENNReal_eq_tsum]
  have hz := tsum_eq_zero_add'
    (f := fun n : ℕ => (couplingScopeTrialLost Δ lam R m i J n).indicator
      (fun _ => (1 : ℝ≥0∞)) q) ENNReal.summable
  rw [coupling_scope_trial_lost_zero] at hz
  exact (add_comm _ _).trans hz.symm

/-- Retained trial depth, including the success and infinite branches, is
measurable on the same original sample space. -/
theorem coupling_scope_measurable_retained_trial_count_toENNReal {d : ℕ} (Δ : ℝ≥0)
    (lam R : ℝ) (m : ℕ) (i : Fin d) (J : ℕ) :
    Measurable (fun q => (couplingScopeRetainedTrialCount Δ lam R m i J q).toENNReal) := by
  simp_rw [coupling_scope_retained_trial_count_toENNReal_eq_add]
  exact (coupling_scope_measurable_retained_count_toENNReal Δ lam R m i J).add
    (measurable_const.indicator (coupling_scope_measurableSet_trial_burn Δ lam R m i J))

/-- Tonelli gives the expected retained trial depth as the actual Lost-tail
sum including Burn; the equality also holds at infinity. -/
theorem coupling_scope_lintegral_retained_trial_count_eq_tsum {d : ℕ} (Δ : ℝ≥0)
    (lam R : ℝ) (m : ℕ) (i : Fin d) (J : ℕ)
    (μ : Measure (FieldPair d × Regeneration.CoupledSample d)) :
    (∫⁻ q, (couplingScopeRetainedTrialCount Δ lam R m i J q).toENNReal ∂μ) =
      ∑' n : ℕ, μ (couplingScopeTrialLost Δ lam R m i J n) := by
  simp_rw [coupling_scope_retained_trial_count_toENNReal_eq_tsum]
  rw [lintegral_tsum (fun n => (measurable_const.indicator
    (coupling_scope_measurableSet_trial_lost Δ lam R m i J n)).aemeasurable)]
  apply tsum_congr
  intro n
  rw [lintegral_indicator_const
    (coupling_scope_measurableSet_trial_lost Δ lam R m i J n), one_mul]

/-- The retained success depth has geometric expectation at most Burn mass
divided by success mass. This includes ratio zero without a separate division. -/
theorem coupling_scope_lintegral_retained_trial_count_le_of_geometric_tail {d : ℕ}
    (Δ : ℝ≥0) (lam R : ℝ) (m : ℕ) (i : Fin d) (J : ℕ)
    (μ : Measure (FieldPair d × Regeneration.CoupledSample d)) (a : ℝ≥0∞)
    (htail : ∀ N, μ (couplingScopeTrialLost Δ lam R m i J N) ≤
      a ^ N * μ (couplingScopeTrialBurn Δ lam R m i J)) :
    (∫⁻ q, (couplingScopeRetainedTrialCount Δ lam R m i J q).toENNReal ∂μ) ≤
      (1 - a)⁻¹ * μ (couplingScopeTrialBurn Δ lam R m i J) := by
  rw [coupling_scope_lintegral_retained_trial_count_eq_tsum]
  calc
    (∑' n : ℕ, μ (couplingScopeTrialLost Δ lam R m i J n)) ≤
        ∑' n : ℕ, a ^ n * μ (couplingScopeTrialBurn Δ lam R m i J) :=
      ENNReal.tsum_le_tsum htail
    _ = _ := by rw [ENNReal.tsum_mul_right, ENNReal.tsum_geometric]

/-- Under a genuine geometric tail with positive success mass, the retained
success depth is almost surely finite and has an integrable real embedding. -/
theorem coupling_scope_retained_trial_count_integrable_of_geometric_tail {d : ℕ}
    (Δ : ℝ≥0) (lam R : ℝ) (m : ℕ) (i : Fin d) (J : ℕ)
    (μ : Measure (FieldPair d × Regeneration.CoupledSample d)) [IsFiniteMeasure μ]
    (a : ℝ≥0∞) (ha : a < 1)
    (htail : ∀ N, μ (couplingScopeTrialLost Δ lam R m i J N) ≤
      a ^ N * μ (couplingScopeTrialBurn Δ lam R m i J)) :
    (∀ᵐ q ∂μ, couplingScopeRetainedTrialCount Δ lam R m i J q ≠ ⊤) ∧
      Integrable (fun q =>
        (couplingScopeRetainedTrialCount Δ lam R m i J q).toENNReal.toReal) μ := by
  have hm := coupling_scope_measurable_retained_trial_count_toENNReal Δ lam R m i J
  have hfin : (∫⁻ q,
      (couplingScopeRetainedTrialCount Δ lam R m i J q).toENNReal ∂μ) ≠ ⊤ :=
    ne_top_of_le_ne_top
      (ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr (ne_of_gt (tsub_pos_iff_lt.mpr ha)))
        (measure_ne_top μ _))
      (coupling_scope_lintegral_retained_trial_count_le_of_geometric_tail Δ lam R m i J μ a htail)
  refine ⟨?_, integrable_toReal_of_lintegral_ne_top hm.aemeasurable hfin⟩
  filter_upwards [ae_lt_top hm hfin] with q hq
  exact ENat.toENNReal_ne_top.mp hq.ne

/-- A null Burn branch contributes zero retained depth almost surely,
without conditioning on a possibly null Burn event. -/
theorem coupling_scope_retained_count_ae_zero_of_null_burn {d : ℕ} (Δ : ℝ≥0)
    (lam R : ℝ) (m : ℕ) (i : Fin d) (J : ℕ)
    (μ : Measure (FieldPair d × Regeneration.CoupledSample d))
    (hB : μ (couplingScopeTrialBurn Δ lam R m i J) = 0) :
    ∀ᵐ q ∂μ, couplingScopeRetainedFailureCount Δ lam R m i J q = 0 := by
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hB] with q hq
  exact coupling_scope_retained_count_eq_zero_off_burn Δ lam R m i J q hq

/-- Countable intersection gives one event of finite retained count at every
original grid and every deterministic Burn index under each supplied law. -/
theorem coupling_scope_both_laws_ae_all_grid_retained_count_finite_of_geometric_tails {d : ℕ}
    (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (lam l : ℝ)
    (K : Regeneration.CoupledQuenchedLaws d) (hK : Regeneration.HasProbabilityLaws Q.measure K)
    (hD : Regeneration.annealedCoupledLaw Q.measure K
      (regenerationNoReturn hd (l / lam)) ≠ 0)
    (a : ℝ≥0∞) (ha : a < 1)
    (htail : ∀ m J N, Regeneration.annealedCoupledLaw Q.measure K
      (couplingScopeTrialLost (Regeneration.Renewal.regenDelta lam) lam (l / lam)
        m (Regeneration.Renewal.forceCoord hd) J N) ≤ a ^ N *
      Regeneration.annealedCoupledLaw Q.measure K
        (couplingScopeTrialBurn (Regeneration.Renewal.regenDelta lam) lam (l / lam)
          m (Regeneration.Renewal.forceCoord hd) J)) :
    ∀ ρ ∈ ({Regeneration.annealedCoupledLaw Q.measure K,
        regenerationConditionedLaw hd Q lam l K hK hD} :
          Set (Measure (FieldPair d × Regeneration.CoupledSample d))),
      ∀ᵐ q ∂ρ, ∀ m J : ℕ,
        couplingScopeRetainedFailureCount (Regeneration.Renewal.regenDelta lam)
          lam (l / lam) m (Regeneration.Renewal.forceCoord hd) J q ≠ ⊤ := by
  intro ρ hρ
  apply ae_all_iff.mpr
  intro m
  apply ae_all_iff.mpr
  intro J
  exact (coupling_scope_both_laws_retained_count_integrable_of_geometric_tail
    hd Q lam l K hK hD m J a ha (htail m J) ρ hρ).1

/-- The actual prebridge conditional bound, when supplied, feeds the checked
geometric producer and yields the retained-failure expectation with success
parameter explicit. It asserts no unconditional analytic estimate. -/
theorem coupling_scope_lintegral_retained_count_le_of_prebridge_condExp {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (K : Regeneration.CoupledQuenchedLaws d) (hK : Regeneration.HasProbabilityLaws Q K)
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (δ : ℝ) (hδ : 0 ≤ δ)
    (hFresh : Regeneration.HasFreshBits Q Δ δ K)
    (lam R : ℝ) (hlam : 0 < lam) (hR : 0 < R) (m : ℕ) (i : Fin d) (J : ℕ)
    (hentry : ∀ᵐ q ∂Regeneration.annealedCoupledLaw Q K, ∀ n,
      Regeneration.trialFailureTime Δ R
        (Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)) i
        (Regeneration.trialStartSequence Δ lam R
          (Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)) i n) ≠ ⊤ →
      Regeneration.trialStartSequence Δ lam R
        (Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)) i (n + 1) ≠ ⊤)
    (η : ℝ) (hη : 0 < η) (hη1 : η ≤ 1)
    (hcond : ∀ N k, ∀ᵐ q ∂Regeneration.annealedCoupledLaw Q K,
      q.2 ∈ couplingScopeTrialBurnPrebridge Δ lam R m i J N k →
        δ * η ≤ ((Regeneration.annealedCoupledLaw Q K)[
          ({p : FieldPair d × Regeneration.CoupledSample d | p.2.2 (m + k) = true ∧
            Regeneration.NoBacktracking R (Regeneration.pathTimeShift
              (Regeneration.sampleTimeShift Δ p.2 ((m : ℝ≥0) * Δ)).1
                (((k + 1 : ℕ) : ℝ≥0) * Δ)) i}).indicator (fun _ => (1 : ℝ)) |
                  couplingScopeAnnealedHistory Δ (m + k)]) q) :
    (∫⁻ q, (couplingScopeRetainedFailureCount Δ lam R m i J q).toENNReal
      ∂Regeneration.annealedCoupledLaw Q K) ≤
      ENNReal.ofReal (1 - η) * (ENNReal.ofReal η)⁻¹ *
        Regeneration.annealedCoupledLaw Q K (couplingScopeTrialBurn Δ lam R m i J) ∧
    (∀ᵐ q ∂Regeneration.annealedCoupledLaw Q K,
      couplingScopeRetainedFailureCount Δ lam R m i J q ≠ ⊤) ∧
    Integrable (fun q => (couplingScopeRetainedFailureCount Δ lam R m i J q).toENNReal.toReal)
      (Regeneration.annealedCoupledLaw Q K) := by
  let μ := Regeneration.annealedCoupledLaw Q K
  let : IsProbabilityMeasure μ := Regeneration.annealedCoupledLaw_isProbabilityMeasure Q K hK
  have htail := coupling_scope_trial_lost_product_of_prebridge_condExp
    Q K hK Δ hΔ δ hδ hFresh lam R hlam hR m i J hentry η hη.le hη1 hcond
  have ha : ENNReal.ofReal (1 - η) < 1 := ENNReal.ofReal_lt_one.mpr (by linarith)
  have hsub : (1 : ℝ≥0∞) - ENNReal.ofReal (1 - η) = ENNReal.ofReal η := by
    calc
      (1 : ℝ≥0∞) - ENNReal.ofReal (1 - η) = ENNReal.ofReal (1 - (1 - η)) := by
        rw [ENNReal.ofReal_sub _ (sub_nonneg.mpr hη1), ENNReal.ofReal_one]
      _ = ENNReal.ofReal η := by congr 1; ring
  refine ⟨?_, coupling_scope_retained_count_integrable_of_lintegral_ne_top
    Δ lam R m i J μ (coupling_scope_lintegral_retained_count_ne_top_of_geometric_tail
      Δ lam R m i J μ _ ha htail)⟩
  simpa only [hsub] using coupling_scope_lintegral_retained_count_le_of_geometric_tail
    Δ lam R m i J μ _ htail

/-- The all-cycle grid/record consumer and all retained-depth conclusions
hold on a common full-measure event for each original law, conditional on the
same actual Burn contraction and entry/escape producers as before. -/
theorem coupling_scope_both_laws_grid_record_and_retained_counts_of_burn_estimate {d : ℕ}
    (hd : 2 ≤ d) (lam l : ℝ) (hlam : 0 < lam) (hl : 0 < l)
    {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (K : Regeneration.CoupledQuenchedLaws d)
    (hK : Regeneration.HasProbabilityLaws Q.measure K)
    (hD : Regeneration.annealedCoupledLaw Q.measure K
      (regenerationNoReturn hd (l / lam)) ≠ 0)
    (hescape : ∀ᵐ q ∂Regeneration.annealedCoupledLaw Q.measure K, Filter.Tendsto
      (fun t : ℝ≥0 => q.2.1 t (Regeneration.Renewal.forceCoord hd))
        Filter.atTop Filter.atTop)
    (hentry : ∀ᵐ q ∂Regeneration.annealedCoupledLaw Q.measure K, ∀ m : ℕ,
      let Δ := Regeneration.Renewal.regenDelta lam
      let w := Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)
      let i := Regeneration.Renewal.forceCoord hd
      Regeneration.trialStartSequence Δ lam (l / lam) w i 0 ≠ ⊤ ∧
        ∀ n, Regeneration.trialFailureTime Δ (l / lam) w i
          (Regeneration.trialStartSequence Δ lam (l / lam) w i n) ≠ ⊤ →
            Regeneration.trialStartSequence Δ lam (l / lam) w i (n + 1) ≠ ⊤)
    (hstep : ∀ m J N,
      let Δ := Regeneration.Renewal.regenDelta lam
      let i := Regeneration.Renewal.forceCoord hd
      Regeneration.annealedCoupledLaw Q.measure K
        (couplingScopeTrialLost Δ lam (l / lam) m i J (N + 1)) ≤
        ENNReal.ofReal (1 - (Regeneration.annealedCoupledLaw Q.measure K
          (regenerationNoReturn hd (l / lam))).toReal) *
            Regeneration.annealedCoupledLaw Q.measure K
              (couplingScopeTrialLost Δ lam (l / lam) m i J N)) :
    ∀ ρ ∈ ({Regeneration.annealedCoupledLaw Q.measure K,
        regenerationConditionedLaw hd Q lam l K hK hD} :
          Set (Measure (FieldPair d × Regeneration.CoupledSample d))),
      ∀ᵐ q ∂ρ,
        (∀ m J : ℕ, couplingScopeRetainedFailureCount (Regeneration.Renewal.regenDelta lam)
          lam (l / lam) m (Regeneration.Renewal.forceCoord hd) J q ≠ ⊤) ∧
        ∀ k : ℕ, ∃ n : ℕ, 2 * k ≤ n ∧
          regenerationTime hd lam l k q.2 =
            (((n : ℝ≥0) * Regeneration.Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞) ∧
          regenerationRecord hd lam l k q =
            Regeneration.futureRecord (Regeneration.Renewal.regenDelta lam) (l / lam)
              q.1 q.2 (Regeneration.Renewal.forceCoord hd)
              ((n : ℝ≥0) * Regeneration.Renewal.regenDelta lam) := by
  let μ := Regeneration.annealedCoupledLaw Q.measure K
  let : IsProbabilityMeasure μ := Regeneration.annealedCoupledLaw_isProbabilityMeasure Q.measure K hK
  have hpos : 0 < (μ (regenerationNoReturn hd (l / lam))).toReal :=
    ENNReal.toReal_pos hD (measure_ne_top μ _)
  have ha : ENNReal.ofReal (1 - (μ (regenerationNoReturn hd (l / lam))).toReal) < 1 :=
    ENNReal.ofReal_lt_one.mpr (by linarith)
  have htail : ∀ m J N, μ (couplingScopeTrialLost (Regeneration.Renewal.regenDelta lam)
      lam (l / lam) m (Regeneration.Renewal.forceCoord hd) J N) ≤
      ENNReal.ofReal (1 - (μ (regenerationNoReturn hd (l / lam))).toReal) ^ N *
        μ (couplingScopeTrialBurn (Regeneration.Renewal.regenDelta lam)
          lam (l / lam) m (Regeneration.Renewal.forceCoord hd) J) := by
    intro m J N
    have h := ConditionalTrialExhaustion.finite_product_of_failure_step
      μ (couplingScopeTrialLost (Regeneration.Renewal.regenDelta lam)
        lam (l / lam) m (Regeneration.Renewal.forceCoord hd) J) _ (hstep m J) N
    rwa [coupling_scope_trial_lost_zero] at h
  have hcount := coupling_scope_both_laws_ae_all_grid_retained_count_finite_of_geometric_tails
    hd Q lam l K hK hD _ ha htail
  have hrecord := coupling_scope_both_laws_grid_record_of_burn_estimate
    hd lam l hlam hl Q K hK hD hescape hentry hstep
  intro ρ hρ
  exact (hcount ρ hρ).and (ae_all_iff.mpr fun k => hrecord k ρ hρ)


/-- A null Burn branch contributes zero retained success depth as well as
zero failures, without a quotient by Burn mass. -/
theorem coupling_scope_retained_trial_count_ae_zero_of_null_burn {d : ℕ} (Δ : ℝ≥0)
    (lam R : ℝ) (m : ℕ) (i : Fin d) (J : ℕ)
    (μ : Measure (FieldPair d × Regeneration.CoupledSample d))
    (hB : μ (couplingScopeTrialBurn Δ lam R m i J) = 0) :
    ∀ᵐ q ∂μ, couplingScopeRetainedTrialCount Δ lam R m i J q = 0 := by
  classical
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hB] with q hq
  exact ite_eq_right hq

/-- A zero failure ratio (success mass one) forces no retained failures.
This case needs no strict positivity assumption on the failure ratio. -/
theorem coupling_scope_retained_count_ae_zero_of_geometric_tail_zero {d : ℕ} (Δ : ℝ≥0)
    (lam R : ℝ) (m : ℕ) (i : Fin d) (J : ℕ)
    (μ : Measure (FieldPair d × Regeneration.CoupledSample d))
    (htail : ∀ N, μ (couplingScopeTrialLost Δ lam R m i J N) ≤
      (0 : ℝ≥0∞) ^ N * μ (couplingScopeTrialBurn Δ lam R m i J)) :
    ∀ᵐ q ∂μ, couplingScopeRetainedFailureCount Δ lam R m i J q = 0 := by
  have hz : μ (couplingScopeTrialLost Δ lam R m i J 1) = 0 := by
    apply le_antisymm
    · simpa only [pow_one, zero_mul] using htail 1
    · exact zero_le
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hz] with q hq
  exact le_antisymm ((coupling_scope_retained_count_le_iff Δ lam R m i J 0 q).mpr hq) bot_le

/-- A proposed history kernel gives the literal fresh-coin and future
no-backtracking conditional expectation once its set-integral disintegration
has been proved. This theorem does not construct that kernel or its identities. -/
theorem coupling_scope_success_condExp_of_setIntegral_kernel {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (K : Regeneration.CoupledQuenchedLaws d) (hK : Regeneration.HasProbabilityLaws Q K)
    (Δ : ℝ≥0) (R : ℝ) (m k : ℕ) (i : Fin d)
    (g : FieldPair d × Regeneration.CoupledSample d → ℝ)
    (hg : Integrable g (Regeneration.annealedCoupledLaw Q K))
    (hgm : AEStronglyMeasurable[couplingScopeAnnealedHistory Δ (m + k)] g
      (Regeneration.annealedCoupledLaw Q K))
    (hdis : ∀ s : Set (FieldPair d × Regeneration.CoupledSample d),
      MeasurableSet[couplingScopeAnnealedHistory Δ (m + k)] s →
      ∫ q in s, g q ∂Regeneration.annealedCoupledLaw Q K =
      ∫ q in s, ({p : FieldPair d × Regeneration.CoupledSample d |
        p.2.2 (m + k) = true ∧ Regeneration.NoBacktracking R
          (Regeneration.pathTimeShift
            (Regeneration.sampleTimeShift Δ p.2 ((m : ℝ≥0) * Δ)).1
              (((k + 1 : ℕ) : ℝ≥0) * Δ)) i}).indicator (fun _ => (1 : ℝ)) q
        ∂Regeneration.annealedCoupledLaw Q K) :
    g =ᵐ[Regeneration.annealedCoupledLaw Q K]
      (Regeneration.annealedCoupledLaw Q K)[
        ({p : FieldPair d × Regeneration.CoupledSample d |
          p.2.2 (m + k) = true ∧ Regeneration.NoBacktracking R
            (Regeneration.pathTimeShift
              (Regeneration.sampleTimeShift Δ p.2 ((m : ℝ≥0) * Δ)).1
                (((k + 1 : ℕ) : ℝ≥0) * Δ)) i}).indicator (fun _ => (1 : ℝ)) |
          couplingScopeAnnealedHistory Δ (m + k)] := by
  let : IsProbabilityMeasure (Regeneration.annealedCoupledLaw Q K) :=
    Regeneration.annealedCoupledLaw_isProbabilityMeasure Q K hK
  have hw : Measurable (fun q : FieldPair d × Regeneration.CoupledSample d =>
      Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)) :=
    (Regeneration.measurable_sampleTimeShift Δ).comp (measurable_const.prodMk measurable_snd)
  have hG : MeasurableSet {q : FieldPair d × Regeneration.CoupledSample d |
      Regeneration.NoBacktracking R (Regeneration.pathTimeShift
        (Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)).1
          (((k + 1 : ℕ) : ℝ≥0) * Δ)) i} :=
    (Regeneration.measurableSet_NoBacktracking R i).preimage
      (Probability.continuous_path_time_shift.measurable.comp
        (measurable_const.prodMk hw.fst))
  have hB : MeasurableSet {q : FieldPair d × Regeneration.CoupledSample d |
      q.2.2 (m + k) = true ∧ Regeneration.NoBacktracking R
        (Regeneration.pathTimeShift
          (Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)).1
            (((k + 1 : ℕ) : ℝ≥0) * Δ)) i} :=
    (measurableSet_eq_fun ((measurable_pi_apply (m + k)).comp measurable_snd.snd)
      measurable_const).inter hG
  apply ae_eq_condExp_of_forall_setIntegral_eq (coupling_scope_annealed_history_le Δ (m + k))
    ((integrable_const 1).indicator hB)
  · intro s hs hfin
    exact hg.integrableOn
  · intro s hs hfin
    exact hdis s hs
  · exact hgm

open Regeneration in
/-- Successful endpoint restart with an original-environment dependent finite history. -/
theorem coupling_scope_joint_history_success_endpoint {d : ℕ}
    (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : HasProbabilityLaws Q.measure K) (hpath : HasPathMarginals Q.measure K P)
    (hP : IsGMPReducedKernel hd Q.ellipticity_parameter Q lam h0 h1 P)
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (δ R : ℝ) (i : Fin d)
    (hRestart : HasDeterministicRestart Q.measure Δ K)
    (hUniform : HasUniformSuccessfulEndpoint Q.measure Δ δ R i K)
    (m : ℕ) (H : FieldPair d × CoupledSample d → ℝ)
    (hH : @Measurable (FieldPair d × CoupledSample d) ℝ
      (MeasurableSpace.prod inferInstance (finiteHistorySigma Δ m)) inferInstance H)
    (hbH : BoundedRealTest H)
    (Ψ : (Vec d × FieldPair d) × CoupledSample d → ℝ)
    (hΨ : Measurable Ψ) (hbΨ : BoundedRealTest Ψ)
    (B : Vec d × FieldPair d → ℝ) (hB : Measurable B) (hbB : BoundedRealTest B)
    (hBeq : ∀ᵐ xω ∂(volume : Measure (Vec d)).prod Q.measure,
      B xω = ∫ w, Ψ (xω, w) ∂K xω) :
    (∫ q, H q * (if q.2.2 m = true then (1 : ℝ) else 0) *
      Ψ ((q.2.1 (((m + 1 : ℕ) : ℝ≥0) * Δ), q.1),
        sampleTimeShift Δ q.2 (((m + 1 : ℕ) : ℝ≥0) * Δ))
      ∂annealedCoupledLaw Q.measure K) =
      ∫ ω, δ * ∫ z, H (ω, z) * endpointAverage i R (z.1 ((m : ℝ≥0) * Δ))
        (fun y => B (y, ω)) ∂K (0, ω) ∂Q.measure := by
  classical
  let t : ℝ≥0 := ((m + 1 : ℕ) : ℝ≥0) * Δ
  have ht : 0 < t := mul_pos (by positivity) hΔ
  have hprob := ae_quenched_of_annealed Q.measure K hK
    (ae_at_endpoint_of_product_ae hd Q lam h0 h1 P K hK hpath hP t ht _ hK.2)
  have hversion := ae_quenched_of_annealed Q.measure K hK
    (ae_at_endpoint_of_product_ae hd Q lam h0 h1 P K hK hpath hP t ht _ hBeq)
  let F : FieldPair d × CoupledSample d → ℝ := fun q =>
    H q * (if q.2.2 m = true then 1 else 0) *
      Ψ ((q.2.1 t, q.1), sampleTimeShift Δ q.2 t)
  have hHfull : Measurable H :=
    hH.mono (sup_le_sup le_rfl
      (MeasurableSpace.comap_mono (Probability.finiteHistorySigma_le Δ m))) le_rfl
  have hF : Measurable F := by
    exact (hHfull.mul
      (Measurable.ite (((measurable_pi_apply m).comp measurable_snd.snd)
        (measurableSet_singleton true)) measurable_const measurable_const)).mul
      (hΨ.comp (((((continuous_eval_const t).measurable.comp measurable_snd.fst)).prodMk
        measurable_fst).prodMk ((measurable_sampleTimeShift Δ).comp
          (measurable_const.prodMk measurable_snd))))
  have hbF : BoundedRealTest F := by
    obtain ⟨CH, hCH⟩ := hbH
    obtain ⟨CP, hCP⟩ := hbΨ
    refine ⟨max CH 0 * max CP 0, fun q => ?_⟩
    dsimp [F]
    by_cases hq : q.2.2 m = true
    · simp only [hq, ↓reduceIte, mul_one, abs_mul]
      exact mul_le_mul ((hCH _).trans (le_max_left _ _))
        ((hCP _).trans (le_max_left _ _)) (abs_nonneg _) (le_max_right _ _)
    · simpa [hq] using
        (mul_nonneg (le_max_right CH (0 : ℝ)) (le_max_right CP (0 : ℝ)))
  change (∫ q, F q ∂annealedCoupledLaw Q.measure K) = _
  rw [integral_annealedCoupledLaw Q.measure K hK F hF hbF]
  apply integral_congr_ae
  filter_upwards [hK.1, hRestart.1, hUniform.1, hprob, hversion] with ω hω hr hu hp hv
  haveI := hω
  exact integral_future_eq_uniformEndpointAverage Δ δ R i K (0, ω) hr hu m hp (fun z => H (ω, z)) (hH.comp measurable_prodMk_left)
    (by obtain ⟨C, hC⟩ := hbH; exact ⟨C, fun z => hC (ω, z)⟩)
    (fun q => Ψ ((q.1, ω), q.2))
    (hΨ.comp ((measurable_fst.prodMk measurable_const).prodMk measurable_snd))
    (by obtain ⟨C, hC⟩ := hbΨ; exact ⟨C, fun q => hC _⟩)
    (fun y => B (y, ω)) (hB.comp measurable_prodMk_right)
    (by obtain ⟨C, hC⟩ := hbB; exact ⟨C, fun y => hC _⟩) hv

#print axioms coupling_scope_joint_history_success_endpoint

/-- The supplied deterministic restart law applies on the literal Burn slice
at the absolute grid index, against every bounded finite-history multiplier
and every bounded measurable full-future test. -/
theorem coupling_scope_trial_burn_prebridge_restart {d : ℕ}
    (K : Regeneration.CoupledQuenchedLaws d) (xω : Vec d × FieldPair d)
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (hRestart : Regeneration.DeterministicRestartAt Δ K xω)
    (lam R : ℝ) (hlam : 0 < lam) (hR : 0 < R) (m : ℕ) (i : Fin d) (J N k : ℕ)
    (H Φ : Regeneration.CoupledSample d → ℝ)
    (hH : @Measurable (Regeneration.CoupledSample d) ℝ
      (Regeneration.finiteHistorySigma Δ (m + k)) inferInstance H)
    (hbH : Regeneration.BoundedRealTest H)
    (hΦ : Measurable Φ) (hbΦ : Regeneration.BoundedRealTest Φ) :
    let A := couplingScopeTrialBurnPrebridge Δ lam R m i J N k
    (∫ z, A.indicator H z *
      Φ (Regeneration.sampleTimeShift Δ z (((m + k : ℕ) : ℝ≥0) * Δ)) ∂K xω) =
    ∫ z, A.indicator H z *
      (∫ w, Φ w ∂K (z.1 (((m + k : ℕ) : ℝ≥0) * Δ), xω.2)) ∂K xω := by
  apply hRestart (m + k) _ Φ
  · exact hH.indicator (coupling_scope_measurableSet_trial_burn_prebridge_finiteHistory
      Δ hΔ lam R hlam hR m i J N k)
  · obtain ⟨C, hC⟩ := hbH
    refine ⟨max C 0, fun z => ?_⟩
    by_cases hz : z ∈ couplingScopeTrialBurnPrebridge Δ lam R m i J N k
    · rw [Set.indicator_of_mem hz]
      exact (hC z).trans (le_max_left _ _)
    · rw [Set.indicator_of_notMem hz, abs_zero]
      exact le_max_right _ _
  · exact hΦ
  · exact hbΦ

#print axioms coupling_scope_trial_burn_prebridge_restart

/-- The actual selected Burn slice has the successful endpoint disintegration
for every bounded future record test and bounded original-environment test.
The future is killed exactly on backtracking and the coin is at `m+k`. -/
theorem coupling_scope_burn_success_killed_future {d : ℕ}
    (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1) (l δ : ℝ) (hl : 0 < l)
    (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K)
    (m : ℕ) (J N k : ℕ)
    (F : FieldPair d → ℝ) (hF : Measurable F) (hbF : Regeneration.BoundedRealTest F)
    (Φ : Regeneration.FutureState d (Regeneration.Renewal.forceCoord hd) (l / lam) → ℝ)
    (hΦ : Measurable Φ) (hbΦ : Regeneration.BoundedRealTest Φ) :
    let Δ := Regeneration.Renewal.regenDelta lam
    let R := l / lam
    let i := Regeneration.Renewal.forceCoord hd
    let A := couplingScopeTrialBurnPrebridge Δ lam R m i J N k
    ∃ B : Vec d × FieldPair d → ℝ, Measurable B ∧ Regeneration.BoundedRealTest B ∧
      (∀ᵐ p ∂(volume : Measure (Vec d)).prod Q.measure,
        B p = ∫ z, Regeneration.killedFutureTest R i Φ (p, z) ∂K p) ∧
      (∫ q, A.indicator (fun _ => (1 : ℝ)) q.2 *
        (if q.2.2 (m + k) = true then (1 : ℝ) else 0) *
        (F q.1 * Regeneration.killedFutureTest R i Φ
          ((q.2.1 (((m + k + 1 : ℕ) : ℝ≥0) * Δ), q.1),
            Regeneration.sampleTimeShift Δ q.2 (((m + k + 1 : ℕ) : ℝ≥0) * Δ)))
        ∂Regeneration.annealedCoupledLaw Q.measure K) =
      ∫ ω, δ * ∫ z, A.indicator (fun _ => (1 : ℝ)) z *
        Regeneration.endpointAverage i R (z.1 (((m + k : ℕ) : ℝ≥0) * Δ))
          (fun y => F ω * B (y, ω)) ∂K (0, ω) ∂Q.measure := by
  classical
  dsimp only
  let Δ := Regeneration.Renewal.regenDelta lam
  let R := l / lam
  let i := Regeneration.Renewal.forceCoord hd
  let A := couplingScopeTrialBurnPrebridge Δ lam R m i J N k
  have hΔ : 0 < Δ := Real.toNNReal_pos.mpr (inv_pos.mpr (sq_pos_of_pos h₀))
  have hR : 0 < R := div_pos hl h₀
  obtain ⟨C, _, B, hB, hbB, _, hBp⟩ :=
    Regeneration.exists_globally_bounded_measurable_killed_future_version
      Q.measure K hK.1 R i Φ hΦ hbΦ
  have hBp' : ∀ᵐ p ∂(volume : Measure (Vec d)).prod Q.measure,
      B p = ∫ z, Regeneration.killedFutureTest R i Φ (p, z) ∂K p := by
    filter_upwards [hBp] with p hp
    simpa only [Regeneration.killedFutureTest, Regeneration.spatialFutureRecord] using hp
  refine ⟨B, hB, ⟨C, hbB⟩, hBp', ?_⟩
  let G : Regeneration.CoupledSample d → ℝ := A.indicator (fun _ => 1)
  have hG : @Measurable (Regeneration.CoupledSample d) ℝ
      (Regeneration.finiteHistorySigma Δ (m + k)) inferInstance G :=
    measurable_const.indicator (coupling_scope_measurableSet_trial_burn_prebridge_finiteHistory
      Δ hΔ lam R h₀ hR m i J N k)
  have hbG : Regeneration.BoundedRealTest G := by
    refine ⟨1, fun z => ?_⟩
    by_cases hz : z ∈ A <;> simp [G, hz]
  let W : Vec d × FieldPair d → ℝ := fun p => F p.2 * B p
  have hW : Measurable W := (hF.comp measurable_snd).mul hB
  have hbW : Regeneration.BoundedRealTest W := by
    obtain ⟨D, hD⟩ := hbF
    refine ⟨max D 0 * max C 0, fun p => ?_⟩
    dsimp only [W]
    rw [abs_mul]
    exact mul_le_mul ((hD _).trans (le_max_left _ _))
      ((hbB _).trans (le_max_left _ _)) (abs_nonneg _) (le_max_right _ _)
  let Ψ : (Vec d × FieldPair d) × Regeneration.CoupledSample d → ℝ := fun p =>
    F p.1.2 * Regeneration.killedFutureTest R i Φ p
  have hΨ : Measurable Ψ := (hF.comp measurable_fst.snd).mul
    (Regeneration.measurable_killedFutureTest R i Φ hΦ)
  have hbΨ : Regeneration.BoundedRealTest Ψ := by
    obtain ⟨D, hD⟩ := hbF
    obtain ⟨E, hE⟩ := Regeneration.boundedRealTest_killedFutureTest R i Φ hbΦ
    refine ⟨max D 0 * max E 0, fun p => ?_⟩
    dsimp only [Ψ]
    rw [abs_mul]
    exact mul_le_mul ((hD _).trans (le_max_left _ _))
      ((hE _).trans (le_max_left _ _)) (abs_nonneg _) (le_max_right _ _)
  have hWp : ∀ᵐ p ∂(volume : Measure (Vec d)).prod Q.measure,
      W p = ∫ z, Ψ (p, z) ∂K p := by
    filter_upwards [hBp'] with p hp
    dsimp only [W, Ψ]
    rw [integral_const_mul, hp]
  exact Regeneration.integral_annealed_future_eq_uniformEndpointAverage hd Q lam h₀.le h₁
    P K hK.1 hK.2.1 hK.2.2.1 Δ hΔ δ R i hK.2.2.2.2.1
    hK.2.2.2.2.2.2.1 (m + k) G hG hbG Ψ hΨ hbΨ W hW hbW hWp

#print axioms coupling_scope_burn_success_killed_future

/-- Joint environment and finite-history tests on the actual Burn slice admit
successful endpoint disintegration for every bounded killed-future test. -/
theorem coupling_scope_joint_burn_success_killed_future {d : ℕ}
    (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1) (l δ : ℝ) (hl : 0 < l)
    (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K)
    (m J N k : ℕ)
    (H : FieldPair d × Regeneration.CoupledSample d → ℝ)
    (hH : @Measurable (FieldPair d × Regeneration.CoupledSample d) ℝ
      (MeasurableSpace.prod inferInstance
        (Regeneration.finiteHistorySigma (Regeneration.Renewal.regenDelta lam) (m + k)))
      inferInstance H) (hbH : Regeneration.BoundedRealTest H)
    (Φ : Regeneration.FutureState d (Regeneration.Renewal.forceCoord hd) (l / lam) → ℝ)
    (hΦ : Measurable Φ) (hbΦ : Regeneration.BoundedRealTest Φ) :
    let Δ := Regeneration.Renewal.regenDelta lam
    let R := l / lam
    let i := Regeneration.Renewal.forceCoord hd
    let A := couplingScopeTrialBurnPrebridge Δ lam R m i J N k
    ∃ B : Vec d × FieldPair d → ℝ, Measurable B ∧ Regeneration.BoundedRealTest B ∧
      (∀ᵐ p ∂(volume : Measure (Vec d)).prod Q.measure,
        B p = ∫ z, Regeneration.killedFutureTest R i Φ (p, z) ∂K p) ∧
      (∫ q, (H q * A.indicator (fun _ => (1 : ℝ)) q.2) *
        (if q.2.2 (m + k) = true then (1 : ℝ) else 0) *
        Regeneration.killedFutureTest R i Φ
          ((q.2.1 (((m + k + 1 : ℕ) : ℝ≥0) * Δ), q.1),
            Regeneration.sampleTimeShift Δ q.2 (((m + k + 1 : ℕ) : ℝ≥0) * Δ))
        ∂Regeneration.annealedCoupledLaw Q.measure K) =
      ∫ ω, δ * ∫ z, (H (ω, z) * A.indicator (fun _ => (1 : ℝ)) z) *
        Regeneration.endpointAverage i R (z.1 (((m + k : ℕ) : ℝ≥0) * Δ))
          (fun y => B (y, ω)) ∂K (0, ω) ∂Q.measure := by
  classical
  dsimp only
  let Δ := Regeneration.Renewal.regenDelta lam
  let R := l / lam
  let i := Regeneration.Renewal.forceCoord hd
  let A := couplingScopeTrialBurnPrebridge Δ lam R m i J N k
  have hΔ : 0 < Δ := Real.toNNReal_pos.mpr (inv_pos.mpr (sq_pos_of_pos h₀))
  have hR : 0 < R := div_pos hl h₀
  obtain ⟨C, _, B, hB, hbB, _, hBp⟩ :=
    Regeneration.exists_globally_bounded_measurable_killed_future_version
      Q.measure K hK.1 R i Φ hΦ hbΦ
  have hBp' : ∀ᵐ p ∂(volume : Measure (Vec d)).prod Q.measure,
      B p = ∫ z, Regeneration.killedFutureTest R i Φ (p, z) ∂K p := by
    filter_upwards [hBp] with p hp
    simpa only [Regeneration.killedFutureTest, Regeneration.spatialFutureRecord] using hp
  refine ⟨B, hB, ⟨C, hbB⟩, hBp', ?_⟩
  let G : FieldPair d × Regeneration.CoupledSample d → ℝ := fun q =>
    H q * A.indicator (fun _ => 1) q.2
  have hG : @Measurable (FieldPair d × Regeneration.CoupledSample d) ℝ
      (MeasurableSpace.prod inferInstance (Regeneration.finiteHistorySigma Δ (m + k)))
      inferInstance G := by
    have hA := coupling_scope_measurableSet_trial_burn_prebridge_finiteHistory
      Δ hΔ lam R h₀ hR m i J N k
    exact hH.mul ((measurable_const.indicator hA).comp measurable_snd)
  have hbG : Regeneration.BoundedRealTest G := by
    obtain ⟨D, hD⟩ := hbH
    refine ⟨max D 0, fun q => ?_⟩
    by_cases hq : q.2 ∈ A
    · simpa [G, Set.indicator_of_mem hq] using (hD q).trans (le_max_left D 0)
    · simpa [G, Set.indicator_of_notMem hq] using le_max_right D 0
  exact coupling_scope_joint_history_success_endpoint hd Q lam h₀.le h₁ P K
    hK.1 hK.2.1 hK.2.2.1 Δ hΔ δ R i hK.2.2.2.2.1
    hK.2.2.2.2.2.2.1 (m + k) G hG hbG
    (Regeneration.killedFutureTest R i Φ)
    (Regeneration.measurable_killedFutureTest R i Φ hΦ)
    (Regeneration.boundedRealTest_killedFutureTest R i Φ hbΦ) B hB ⟨C, hbB⟩ hBp'

#print axioms coupling_scope_joint_burn_success_killed_future

/-- One measurable killed-future kernel works simultaneously for all bounded
joint environment and finite-history tests on the actual Burn slice. -/
theorem coupling_scope_joint_burn_success_killed_future_uniform {d : ℕ}
    (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1) (l δ : ℝ) (hl : 0 < l)
    (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K)
    (m J N k : ℕ)
    (Φ : Regeneration.FutureState d (Regeneration.Renewal.forceCoord hd) (l / lam) → ℝ)
    (hΦ : Measurable Φ) (hbΦ : Regeneration.BoundedRealTest Φ) :
    let Δ := Regeneration.Renewal.regenDelta lam
    let R := l / lam
    let i := Regeneration.Renewal.forceCoord hd
    let A := couplingScopeTrialBurnPrebridge Δ lam R m i J N k
    ∃ B : Vec d × FieldPair d → ℝ, Measurable B ∧ Regeneration.BoundedRealTest B ∧
      (∀ᵐ p ∂(volume : Measure (Vec d)).prod Q.measure,
        B p = ∫ z, Regeneration.killedFutureTest R i Φ (p, z) ∂K p) ∧
      ∀ (H : FieldPair d × Regeneration.CoupledSample d → ℝ),
      @Measurable (FieldPair d × Regeneration.CoupledSample d) ℝ
        (MeasurableSpace.prod inferInstance (Regeneration.finiteHistorySigma Δ (m + k)))
        inferInstance H → Regeneration.BoundedRealTest H →
      (∫ q, (H q * A.indicator (fun _ => (1 : ℝ)) q.2) *
        (if q.2.2 (m + k) = true then (1 : ℝ) else 0) *
        Regeneration.killedFutureTest R i Φ
          ((q.2.1 (((m + k + 1 : ℕ) : ℝ≥0) * Δ), q.1),
            Regeneration.sampleTimeShift Δ q.2 (((m + k + 1 : ℕ) : ℝ≥0) * Δ))
        ∂Regeneration.annealedCoupledLaw Q.measure K) =
      ∫ ω, δ * ∫ z, (H (ω, z) * A.indicator (fun _ => (1 : ℝ)) z) *
        Regeneration.endpointAverage i R (z.1 (((m + k : ℕ) : ℝ≥0) * Δ))
          (fun y => B (y, ω)) ∂K (0, ω) ∂Q.measure := by
  classical
  dsimp only
  let Δ := Regeneration.Renewal.regenDelta lam
  let R := l / lam
  let i := Regeneration.Renewal.forceCoord hd
  let A := couplingScopeTrialBurnPrebridge Δ lam R m i J N k
  have hΔ : 0 < Δ := Real.toNNReal_pos.mpr (inv_pos.mpr (sq_pos_of_pos h₀))
  have hR : 0 < R := div_pos hl h₀
  obtain ⟨C, _, B, hB, hbB, _, hBp⟩ :=
    Regeneration.exists_globally_bounded_measurable_killed_future_version
      Q.measure K hK.1 R i Φ hΦ hbΦ
  have hBp' : ∀ᵐ p ∂(volume : Measure (Vec d)).prod Q.measure,
      B p = ∫ z, Regeneration.killedFutureTest R i Φ (p, z) ∂K p := by
    filter_upwards [hBp] with p hp
    simpa only [Regeneration.killedFutureTest, Regeneration.spatialFutureRecord] using hp
  refine ⟨B, hB, ⟨C, hbB⟩, hBp', ?_⟩
  intro H hH hbH
  let G : FieldPair d × Regeneration.CoupledSample d → ℝ := fun q =>
    H q * A.indicator (fun _ => 1) q.2
  have hG : @Measurable (FieldPair d × Regeneration.CoupledSample d) ℝ
      (MeasurableSpace.prod inferInstance (Regeneration.finiteHistorySigma Δ (m + k)))
      inferInstance G := by
    have hA := coupling_scope_measurableSet_trial_burn_prebridge_finiteHistory
      Δ hΔ lam R h₀ hR m i J N k
    exact hH.mul ((measurable_const.indicator hA).comp measurable_snd)
  have hbG : Regeneration.BoundedRealTest G := by
    obtain ⟨D, hD⟩ := hbH
    refine ⟨max D 0, fun q => ?_⟩
    by_cases hq : q.2 ∈ A
    · simpa [G, Set.indicator_of_mem hq] using (hD q).trans (le_max_left D 0)
    · simpa [G, Set.indicator_of_notMem hq] using le_max_right D 0
  exact coupling_scope_joint_history_success_endpoint hd Q lam h₀.le h₁ P K
    hK.1 hK.2.1 hK.2.2.1 Δ hΔ δ R i hK.2.2.2.2.1
    hK.2.2.2.2.2.2.1 (m + k) G hG hbG
    (Regeneration.killedFutureTest R i Φ)
    (Regeneration.measurable_killedFutureTest R i Φ hΦ)
    (Regeneration.boundedRealTest_killedFutureTest R i Φ hbΦ) B hB ⟨C, hbB⟩ hBp'

#print axioms coupling_scope_joint_burn_success_killed_future_uniform

/-- The endpoint kernel is measurable and integrable on the full annealed
space before it is conditioned on the sample history. -/
theorem coupling_scope_endpoint_kernel_integrable {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (K : Regeneration.CoupledQuenchedLaws d) (hK : Regeneration.HasProbabilityLaws Q K)
    (i : Fin d) (R : ℝ) (hR : 0 < R) (t : ℝ≥0) (δ : ℝ)
    (B : Vec d × FieldPair d → ℝ) (hB : Measurable B)
    (hbB : Regeneration.BoundedRealTest B) :
    let g : FieldPair d × Regeneration.CoupledSample d → ℝ := fun q =>
      δ * Regeneration.endpointAverage i R (q.2.1 t) (fun y => B (y, q.1))
    Measurable g ∧ Integrable g (Regeneration.annealedCoupledLaw Q K) := by
  dsimp only
  let X : FieldPair d × Regeneration.CoupledSample d → Vec d := fun q => q.2.1 t
  let B' : (FieldPair d × Regeneration.CoupledSample d) × Vec d → ℝ :=
    fun p => B (p.2, p.1.1)
  have hX : Measurable X :=
    (continuous_eval_const t).measurable.comp measurable_snd.fst
  have hB' : Measurable B' := hB.comp (measurable_snd.prodMk measurable_fst.fst)
  have hbB' : Regeneration.BoundedRealTest B' := by
    obtain ⟨C, hC⟩ := hbB
    exact ⟨C, fun p => hC (p.2, p.1.1)⟩
  have hm := Regeneration.measurable_endpointAverage i R X hX B' hB'
  obtain ⟨C, hC⟩ := Regeneration.boundedRealTest_endpointAverage i R hR X B' hbB'
  let : IsProbabilityMeasure (Regeneration.annealedCoupledLaw Q K) :=
    Regeneration.annealedCoupledLaw_isProbabilityMeasure Q K hK
  have hi : Integrable (fun q => Regeneration.endpointAverage i R (X q)
      (fun y => B' (q, y))) (Regeneration.annealedCoupledLaw Q K) :=
    Integrable.of_bound hm.aestronglyMeasurable C
      (Filter.Eventually.of_forall (fun q => by simpa only [Real.norm_eq_abs] using hC q))
  exact ⟨measurable_const.mul hm, hi.const_mul δ⟩

#print axioms coupling_scope_endpoint_kernel_integrable

/-- Disintegrate a bounded joint history test times the actual endpoint kernel. -/
theorem coupling_scope_integral_mul_endpoint_kernel {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (K : Regeneration.CoupledQuenchedLaws d) (hK : Regeneration.HasProbabilityLaws Q K)
    (i : Fin d) (R : ℝ) (hR : 0 < R) (t : ℝ≥0) (δ : ℝ)
    (B : Vec d × FieldPair d → ℝ) (hB : Measurable B)
    (hbB : Regeneration.BoundedRealTest B)
    (H : FieldPair d × Regeneration.CoupledSample d → ℝ) (hH : Measurable H)
    (hbH : Regeneration.BoundedRealTest H) :
    (∫ q, H q * (δ * Regeneration.endpointAverage i R (q.2.1 t)
        (fun y => B (y, q.1))) ∂Regeneration.annealedCoupledLaw Q K) =
      ∫ ω, δ * ∫ z, H (ω, z) * Regeneration.endpointAverage i R (z.1 t)
        (fun y => B (y, ω)) ∂K (0, ω) ∂Q := by
  let X : FieldPair d × Regeneration.CoupledSample d → Vec d := fun q => q.2.1 t
  let B' : (FieldPair d × Regeneration.CoupledSample d) × Vec d → ℝ :=
    fun p => B (p.2, p.1.1)
  have hX : Measurable X := (continuous_eval_const t).measurable.comp measurable_snd.fst
  have hB' : Measurable B' := hB.comp (measurable_snd.prodMk measurable_fst.fst)
  have hbB' : Regeneration.BoundedRealTest B' := by
    obtain ⟨C, hC⟩ := hbB
    exact ⟨C, fun p => hC (p.2, p.1.1)⟩
  have hm := Regeneration.measurable_endpointAverage i R X hX B' hB'
  obtain ⟨CB, hCB⟩ := Regeneration.boundedRealTest_endpointAverage i R hR X B' hbB'
  obtain ⟨CH, hCH⟩ := hbH
  let F : FieldPair d × Regeneration.CoupledSample d → ℝ := fun q =>
    H q * Regeneration.endpointAverage i R (X q) (fun y => B' (q, y))
  have hF : Measurable F := hH.mul hm
  have hbF : Regeneration.BoundedRealTest F := by
    refine ⟨max CH 0 * max CB 0, fun q => ?_⟩
    dsimp [F]
    rw [abs_mul]
    exact mul_le_mul ((hCH _).trans (le_max_left _ _))
      ((hCB _).trans (le_max_left _ _)) (abs_nonneg _) (le_max_right _ _)
  calc
    (∫ q, H q * (δ * Regeneration.endpointAverage i R (q.2.1 t)
        (fun y => B (y, q.1))) ∂Regeneration.annealedCoupledLaw Q K) =
      δ * ∫ q, F q ∂Regeneration.annealedCoupledLaw Q K := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun q => by dsimp [F, X, B']; ring)
    _ = δ * ∫ ω, ∫ z, F (ω, z) ∂K (0, ω) ∂Q := by
        rw [Regeneration.integral_annealedCoupledLaw Q K hK F hF hbF]
    _ = ∫ ω, δ * ∫ z, H (ω, z) * Regeneration.endpointAverage i R (z.1 t)
        (fun y => B (y, ω)) ∂K (0, ω) ∂Q := by
        rw [integral_const_mul]

#print axioms coupling_scope_integral_mul_endpoint_kernel

/-- On the selected Burn slice, every bounded joint-history test sees the
same annealed endpoint kernel for the killed full-future observable. -/
theorem coupling_scope_joint_burn_success_killed_future_annealed {d : ℕ}
    (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1) (l δ : ℝ) (hl : 0 < l)
    (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K)
    (m J N k : ℕ)
    (Φ : Regeneration.FutureState d (Regeneration.Renewal.forceCoord hd) (l / lam) → ℝ)
    (hΦ : Measurable Φ) (hbΦ : Regeneration.BoundedRealTest Φ) :
    let Δ := Regeneration.Renewal.regenDelta lam
    let R := l / lam
    let i := Regeneration.Renewal.forceCoord hd
    let A := couplingScopeTrialBurnPrebridge Δ lam R m i J N k
    ∃ B : Vec d × FieldPair d → ℝ, Measurable B ∧ Regeneration.BoundedRealTest B ∧
      (∀ᵐ p ∂(volume : Measure (Vec d)).prod Q.measure,
        B p = ∫ z, Regeneration.killedFutureTest R i Φ (p, z) ∂K p) ∧
      ∀ (H : FieldPair d × Regeneration.CoupledSample d → ℝ),
      @Measurable (FieldPair d × Regeneration.CoupledSample d) ℝ
        (MeasurableSpace.prod inferInstance (Regeneration.finiteHistorySigma Δ (m + k)))
        inferInstance H → Regeneration.BoundedRealTest H →
      (∫ q, (H q * A.indicator (fun _ => (1 : ℝ)) q.2) *
        (if q.2.2 (m + k) = true then (1 : ℝ) else 0) *
        Regeneration.killedFutureTest R i Φ
          ((q.2.1 (((m + k + 1 : ℕ) : ℝ≥0) * Δ), q.1),
            Regeneration.sampleTimeShift Δ q.2 (((m + k + 1 : ℕ) : ℝ≥0) * Δ))
        ∂Regeneration.annealedCoupledLaw Q.measure K) =
      ∫ q, (H q * A.indicator (fun _ => (1 : ℝ)) q.2) *
        (δ * Regeneration.endpointAverage i R (q.2.1 (((m + k : ℕ) : ℝ≥0) * Δ))
          (fun y => B (y, q.1))) ∂Regeneration.annealedCoupledLaw Q.measure K := by
  classical
  dsimp only
  let Δ := Regeneration.Renewal.regenDelta lam
  let R := l / lam
  let i := Regeneration.Renewal.forceCoord hd
  let A := couplingScopeTrialBurnPrebridge Δ lam R m i J N k
  have hΔ : 0 < Δ := Real.toNNReal_pos.mpr (inv_pos.mpr (sq_pos_of_pos h₀))
  have hR : 0 < R := div_pos hl h₀
  obtain ⟨B, hB, hbB, hBp, hdis⟩ :=
    coupling_scope_joint_burn_success_killed_future_uniform hd Q lam h₀ h₁ l δ hl P K hK
      m J N k Φ hΦ hbΦ
  refine ⟨B, hB, hbB, hBp, ?_⟩
  intro H hH hbH
  let G : FieldPair d × Regeneration.CoupledSample d → ℝ := fun q =>
    H q * A.indicator (fun _ => 1) q.2
  have hHfull : Measurable H := hH.mono (sup_le_sup le_rfl
    (MeasurableSpace.comap_mono (Probability.finiteHistorySigma_le Δ (m + k)))) le_rfl
  have hA := coupling_scope_measurableSet_trial_burn_prebridge_finiteHistory
    Δ hΔ lam R h₀ hR m i J N k
  have hAfull : MeasurableSet A := Probability.finiteHistorySigma_le Δ (m + k) A hA
  have hG : Measurable G := hHfull.mul ((measurable_const.indicator hAfull).comp measurable_snd)
  have hbG : Regeneration.BoundedRealTest G := by
    obtain ⟨D, hD⟩ := hbH
    refine ⟨max D 0, fun q => ?_⟩
    by_cases hq : q.2 ∈ A
    · simpa [G, Set.indicator_of_mem hq] using (hD q).trans (le_max_left D 0)
    · simpa [G, Set.indicator_of_notMem hq] using le_max_right D 0
  exact (hdis H hH hbH).trans
    (coupling_scope_integral_mul_endpoint_kernel Q.measure K hK.1 i R hR
      (((m + k : ℕ) : ℝ≥0) * Δ) δ B hB hbB G hG hbG).symm

#print axioms coupling_scope_joint_burn_success_killed_future_annealed

/-- The actual killed-future endpoint kernel agrees with the selected success
observable on every sample-history set intersected with Burn. -/
theorem coupling_scope_burn_future_setIntegral_kernel {d : ℕ}
    (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1) (l δ : ℝ) (hl : 0 < l)
    (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K)
    (m J N k : ℕ)
    (Φ : Regeneration.FutureState d (Regeneration.Renewal.forceCoord hd) (l / lam) → ℝ)
    (hΦ : Measurable Φ) (hbΦ : Regeneration.BoundedRealTest Φ) :
    let Δ := Regeneration.Renewal.regenDelta lam
    let R := l / lam
    let i := Regeneration.Renewal.forceCoord hd
    let A := couplingScopeTrialBurnPrebridge Δ lam R m i J N k
    ∃ B : Vec d × FieldPair d → ℝ, Measurable B ∧ Regeneration.BoundedRealTest B ∧
      (∀ᵐ p ∂(volume : Measure (Vec d)).prod Q.measure,
        B p = ∫ z, Regeneration.killedFutureTest R i Φ (p, z) ∂K p) ∧
      ∀ s : Set (FieldPair d × Regeneration.CoupledSample d),
      MeasurableSet[couplingScopeAnnealedHistory Δ (m + k)] s →
      (∫ q in s ∩ {q | q.2 ∈ A},
        (if q.2.2 (m + k) = true then (1 : ℝ) else 0) *
        Regeneration.killedFutureTest R i Φ
          ((q.2.1 (((m + k + 1 : ℕ) : ℝ≥0) * Δ), q.1),
            Regeneration.sampleTimeShift Δ q.2 (((m + k + 1 : ℕ) : ℝ≥0) * Δ))
        ∂Regeneration.annealedCoupledLaw Q.measure K) =
      ∫ q in s ∩ {q | q.2 ∈ A},
        δ * Regeneration.endpointAverage i R (q.2.1 (((m + k : ℕ) : ℝ≥0) * Δ))
          (fun y => B (y, q.1)) ∂Regeneration.annealedCoupledLaw Q.measure K := by
  classical
  dsimp only
  let Δ := Regeneration.Renewal.regenDelta lam
  let R := l / lam
  let i := Regeneration.Renewal.forceCoord hd
  let A := couplingScopeTrialBurnPrebridge Δ lam R m i J N k
  have hΔ : 0 < Δ := Real.toNNReal_pos.mpr (inv_pos.mpr (sq_pos_of_pos h₀))
  have hR : 0 < R := div_pos hl h₀
  obtain ⟨B, hB, hbB, hBp, hdis⟩ :=
    coupling_scope_joint_burn_success_killed_future_annealed hd Q lam h₀ h₁ l δ hl P K hK
      m J N k Φ hΦ hbΦ
  refine ⟨B, hB, hbB, hBp, ?_⟩
  intro s hs
  have hle : couplingScopeAnnealedHistory (d := d) Δ (m + k) ≤
      MeasurableSpace.prod inferInstance (Regeneration.finiteHistorySigma Δ (m + k)) :=
    measurable_snd.comap_le
  have hS : MeasurableSet s := coupling_scope_annealed_history_le Δ (m + k) s hs
  have hA := coupling_scope_measurableSet_trial_burn_prebridge_finiteHistory
    Δ hΔ lam R h₀ hR m i J N k
  have hAfull : MeasurableSet A := Probability.finiteHistorySigma_le Δ (m + k) A hA
  have hSA : MeasurableSet (s ∩ {q : FieldPair d × Regeneration.CoupledSample d | q.2 ∈ A}) :=
    hS.inter (hAfull.preimage measurable_snd)
  let H : FieldPair d × Regeneration.CoupledSample d → ℝ := s.indicator (fun _ => 1)
  have hH : @Measurable (FieldPair d × Regeneration.CoupledSample d) ℝ
      (MeasurableSpace.prod inferInstance (Regeneration.finiteHistorySigma Δ (m + k)))
      inferInstance H := measurable_const.indicator (hle s hs)
  have hbH : Regeneration.BoundedRealTest H := by
    refine ⟨1, fun q => ?_⟩
    by_cases hq : q ∈ s <;> simp [H, hq]
  have hh := hdis H hH hbH
  let f : FieldPair d × Regeneration.CoupledSample d → ℝ := fun q =>
    (if q.2.2 (m + k) = true then 1 else 0) *
      Regeneration.killedFutureTest R i Φ
        ((q.2.1 (((m + k + 1 : ℕ) : ℝ≥0) * Δ), q.1),
          Regeneration.sampleTimeShift Δ q.2 (((m + k + 1 : ℕ) : ℝ≥0) * Δ))
  let g : FieldPair d × Regeneration.CoupledSample d → ℝ := fun q =>
    δ * Regeneration.endpointAverage i R (q.2.1 (((m + k : ℕ) : ℝ≥0) * Δ))
      (fun y => B (y, q.1))
  have hL : (fun q => (H q * A.indicator (fun _ => (1 : ℝ)) q.2) * f q) =
      (s ∩ {q | q.2 ∈ A}).indicator f := by
    funext q
    by_cases hs' : q ∈ s <;> by_cases ha' : q.2 ∈ A <;>
      simp [H, hs', ha', Set.indicator_of_mem, Set.indicator_of_notMem]
  have hG : (fun q => (H q * A.indicator (fun _ => (1 : ℝ)) q.2) * g q) =
      (s ∩ {q | q.2 ∈ A}).indicator g := by
    funext q
    by_cases hs' : q ∈ s <;> by_cases ha' : q.2 ∈ A <;>
      simp [H, hs', ha', Set.indicator_of_mem, Set.indicator_of_notMem]
  have hh' : (∫ q, (H q * A.indicator (fun _ => (1 : ℝ)) q.2) * f q
      ∂Regeneration.annealedCoupledLaw Q.measure K) =
      ∫ q, (H q * A.indicator (fun _ => (1 : ℝ)) q.2) * g q
      ∂Regeneration.annealedCoupledLaw Q.measure K := by
    simpa only [f, g, mul_assoc] using hh
  rw [hL, hG, integral_indicator hSA, integral_indicator hSA] at hh'
  exact hh'

#print axioms coupling_scope_burn_future_setIntegral_kernel

/-- Conditioning the actual endpoint kernel on the sample history identifies
all bounded killed-future tests on the selected Burn event. -/
theorem coupling_scope_burn_future_condExp_kernel {d : ℕ}
    (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1) (l δ : ℝ) (hl : 0 < l)
    (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K)
    (m J N k : ℕ)
    (Φ : Regeneration.FutureState d (Regeneration.Renewal.forceCoord hd) (l / lam) → ℝ)
    (hΦ : Measurable Φ) (hbΦ : Regeneration.BoundedRealTest Φ) :
    let Δ := Regeneration.Renewal.regenDelta lam
    let R := l / lam
    let i := Regeneration.Renewal.forceCoord hd
    let A := couplingScopeTrialBurnPrebridge Δ lam R m i J N k
    let μ := Regeneration.annealedCoupledLaw Q.measure K
    ∃ B : Vec d × FieldPair d → ℝ, Measurable B ∧ Regeneration.BoundedRealTest B ∧
      (∀ᵐ p ∂(volume : Measure (Vec d)).prod Q.measure,
        B p = ∫ z, Regeneration.killedFutureTest R i Φ (p, z) ∂K p) ∧
      ∀ᵐ q ∂μ, q.2 ∈ A →
        (μ[fun q => (if q.2.2 (m + k) = true then (1 : ℝ) else 0) *
          Regeneration.killedFutureTest R i Φ
            ((q.2.1 (((m + k + 1 : ℕ) : ℝ≥0) * Δ), q.1),
              Regeneration.sampleTimeShift Δ q.2 (((m + k + 1 : ℕ) : ℝ≥0) * Δ)) | (couplingScopeAnnealedHistory (d := d) Δ (m + k))]) q =
        (μ[fun q => δ * Regeneration.endpointAverage i R
          (q.2.1 (((m + k : ℕ) : ℝ≥0) * Δ)) (fun y => B (y, q.1)) | (couplingScopeAnnealedHistory (d := d) Δ (m + k))]) q := by
  classical
  dsimp only
  let Δ := Regeneration.Renewal.regenDelta lam
  let R := l / lam
  let i := Regeneration.Renewal.forceCoord hd
  let μ := Regeneration.annealedCoupledLaw Q.measure K
  let A : Set (FieldPair d × Regeneration.CoupledSample d) :=
    {q | q.2 ∈ couplingScopeTrialBurnPrebridge Δ lam R m i J N k}
  let t : ℝ≥0 := (((m + k + 1 : ℕ) : ℝ≥0) * Δ)
  let f : FieldPair d × Regeneration.CoupledSample d → ℝ := fun q =>
    (if q.2.2 (m + k) = true then 1 else 0) *
      Regeneration.killedFutureTest R i Φ
        ((q.2.1 t, q.1), Regeneration.sampleTimeShift Δ q.2 t)
  have hΔ : 0 < Δ := Real.toNNReal_pos.mpr (inv_pos.mpr (sq_pos_of_pos h₀))
  have hR : 0 < R := div_pos hl h₀
  let : IsProbabilityMeasure μ :=
    Regeneration.annealedCoupledLaw_isProbabilityMeasure Q.measure K hK.1
  have hH := coupling_scope_annealed_history_le (d := d) Δ (m + k)
  have hA : MeasurableSet[(couplingScopeAnnealedHistory (d := d) Δ (m + k))] A :=
    (coupling_scope_measurableSet_trial_burn_prebridge_finiteHistory
      Δ hΔ lam R h₀ hR m i J N k).preimage (Measurable.of_comap_le le_rfl)
  have hA' : MeasurableSet A := hH A hA
  have hfm : Measurable f := by
    exact (Measurable.ite (((measurable_pi_apply (m + k)).comp measurable_snd.snd)
      (measurableSet_singleton true)) measurable_const measurable_const).mul
      ((Regeneration.measurable_killedFutureTest R i Φ hΦ).comp
        ((((continuous_eval_const t).measurable.comp measurable_snd.fst).prodMk measurable_fst).prodMk
          ((Regeneration.measurable_sampleTimeShift Δ).comp
            (measurable_const.prodMk measurable_snd))))
  obtain ⟨C, hC⟩ := Regeneration.boundedRealTest_killedFutureTest R i Φ hbΦ
  have hf : Integrable f μ := Integrable.of_bound hfm.aestronglyMeasurable (max C 0) (by
    filter_upwards with q
    by_cases hq : q.2.2 (m + k) = true
    · simpa [f, hq, Real.norm_eq_abs] using (hC _).trans (le_max_left C 0)
    · simp [f, hq, le_max_right C 0])
  obtain ⟨B, hB, hbB, hBp, hdis⟩ :=
    coupling_scope_burn_future_setIntegral_kernel hd Q lam h₀ h₁ l δ hl P K hK m J N k Φ hΦ hbΦ
  refine ⟨B, hB, hbB, hBp, ?_⟩
  let g : FieldPair d × Regeneration.CoupledSample d → ℝ := fun q =>
    δ * Regeneration.endpointAverage i R (q.2.1 (((m + k : ℕ) : ℝ≥0) * Δ))
      (fun y => B (y, q.1))
  have hg : Integrable g μ := (coupling_scope_endpoint_kernel_integrable Q.measure K hK.1
    i R hR (((m + k : ℕ) : ℝ≥0) * Δ) δ B hB hbB).2
  have heq : A.indicator (μ[g | (couplingScopeAnnealedHistory (d := d) Δ (m + k))]) =ᵐ[μ] μ[A.indicator f | (couplingScopeAnnealedHistory (d := d) Δ (m + k))] := by
    apply ae_eq_condExp_of_forall_setIntegral_eq hH (hf.indicator hA')
    · intro s hs hfin
      exact (integrable_condExp.indicator hA').integrableOn
    · intro s hs hfin
      rw [setIntegral_indicator hA', setIntegral_indicator hA']
      rw [setIntegral_condExp hH hg (hs.inter hA)]
      exact (hdis s hs).symm
    · have hm : StronglyMeasurable[couplingScopeAnnealedHistory Δ (m + k)]
          (μ[g | couplingScopeAnnealedHistory Δ (m + k)]) := stronglyMeasurable_condExp
      exact (hm.indicator hA).aestronglyMeasurable
  have hind := condExp_indicator hf hA
  filter_upwards [heq, hind] with q hq hi hqa
  have hqa' : q ∈ A := hqa
  have h := hq.trans hi
  simpa only [Set.indicator_of_mem hqa'] using h.symm

#print axioms coupling_scope_burn_future_condExp_kernel

/-- The actual selected success event has the conditional endpoint-kernel
probability on Burn, with the absolute trial coin index. -/
theorem coupling_scope_burn_success_condExp_endpoint_kernel {d : ℕ}
    (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1) (l δ : ℝ) (hl : 0 < l)
    (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K)
    (m J N k : ℕ) :
    let Δ := Regeneration.Renewal.regenDelta lam
    let R := l / lam
    let i := Regeneration.Renewal.forceCoord hd
    let A := couplingScopeTrialBurnPrebridge Δ lam R m i J N k
    let μ := Regeneration.annealedCoupledLaw Q.measure K
    ∃ B : Vec d × FieldPair d → ℝ, Measurable B ∧ Regeneration.BoundedRealTest B ∧
      (∀ᵐ p ∂(volume : Measure (Vec d)).prod Q.measure,
        B p = ∫ z, Regeneration.killedFutureTest R i (fun _ => 1) (p, z) ∂K p) ∧
      ∀ᵐ q ∂μ, q.2 ∈ A →
        (μ[({p : FieldPair d × Regeneration.CoupledSample d |
          p.2.2 (m + k) = true ∧ Regeneration.NoBacktracking R
            (Regeneration.pathTimeShift
              (Regeneration.sampleTimeShift Δ p.2 ((m : ℝ≥0) * Δ)).1
                (((k + 1 : ℕ) : ℝ≥0) * Δ)) i}).indicator (fun _ => (1 : ℝ)) |
            couplingScopeAnnealedHistory Δ (m + k)]) q =
        (μ[fun q => δ * Regeneration.endpointAverage i R
          (q.2.1 (((m + k : ℕ) : ℝ≥0) * Δ)) (fun y => B (y, q.1)) |
            couplingScopeAnnealedHistory Δ (m + k)]) q := by
  classical
  dsimp only
  let Δ := Regeneration.Renewal.regenDelta lam
  let R := l / lam
  let i := Regeneration.Renewal.forceCoord hd
  let μ := Regeneration.annealedCoupledLaw Q.measure K
  obtain ⟨B, hB, hbB, hBp, hcond⟩ :=
    coupling_scope_burn_future_condExp_kernel hd Q lam h₀ h₁ l δ hl P K hK m J N k
      (fun _ => 1) measurable_const ⟨1, fun _ => by simp⟩
  refine ⟨B, hB, hbB, hBp, ?_⟩
  have hpath (z : Regeneration.CoupledSample d) :
      Regeneration.pathTimeShift
        (Regeneration.sampleTimeShift Δ z ((m : ℝ≥0) * Δ)).1
          (((k + 1 : ℕ) : ℝ≥0) * Δ) =
      Regeneration.pathTimeShift z.1 (((m + k + 1 : ℕ) : ℝ≥0) * Δ) := by
    ext t j
    simp only [Regeneration.sampleTimeShift, Regeneration.pathTimeShift, ContinuousMap.coe_mk]
    push_cast
    ring
  have hf : (fun q : FieldPair d × Regeneration.CoupledSample d =>
      (if q.2.2 (m + k) = true then (1 : ℝ) else 0) *
      Regeneration.killedFutureTest R i (fun _ => 1)
        ((q.2.1 (((m + k + 1 : ℕ) : ℝ≥0) * Δ), q.1),
          Regeneration.sampleTimeShift Δ q.2 (((m + k + 1 : ℕ) : ℝ≥0) * Δ))) =
      ({p : FieldPair d × Regeneration.CoupledSample d |
        p.2.2 (m + k) = true ∧ Regeneration.NoBacktracking R
          (Regeneration.pathTimeShift
            (Regeneration.sampleTimeShift Δ p.2 ((m : ℝ≥0) * Δ)).1
              (((k + 1 : ℕ) : ℝ≥0) * Δ)) i}).indicator (fun _ => (1 : ℝ)) := by
    funext q
    rw [Regeneration.killedFutureTest_sampleTimeShift]
    simp only [hpath]
    by_cases hc : q.2.2 (m + k) = true <;>
      by_cases hn : Regeneration.NoBacktracking R
        (Regeneration.pathTimeShift q.2.1 (((m + k + 1 : ℕ) : ℝ≥0) * Δ)) i <;>
      simp only [Nat.cast_add, Nat.cast_one] at hn <;>
      simp [hc, hn, Set.indicator_of_mem, Set.indicator_of_notMem]
  rw [hf] at hcond
  exact hcond

#print axioms coupling_scope_burn_success_condExp_endpoint_kernel

/-- A disintegration identity only on selected Burn histories identifies the
conditional success probability on Burn. The candidate and the identity are
still producer obligations for the supplied coupling. -/
theorem coupling_scope_success_condExp_on_burn_of_setIntegral_kernel {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (K : Regeneration.CoupledQuenchedLaws d) (hK : Regeneration.HasProbabilityLaws Q K)
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (lam R : ℝ) (hlam : 0 < lam) (hR : 0 < R)
    (m : ℕ) (i : Fin d) (J N k : ℕ)
    (g : FieldPair d × Regeneration.CoupledSample d → ℝ)
    (hg : Integrable g (Regeneration.annealedCoupledLaw Q K))
    (hgm : AEStronglyMeasurable[couplingScopeAnnealedHistory Δ (m + k)] g
      (Regeneration.annealedCoupledLaw Q K))
    (hdis : ∀ s : Set (FieldPair d × Regeneration.CoupledSample d),
      MeasurableSet[couplingScopeAnnealedHistory Δ (m + k)] s →
      ∫ q in s ∩ {q | q.2 ∈ couplingScopeTrialBurnPrebridge Δ lam R m i J N k},
        g q ∂Regeneration.annealedCoupledLaw Q K =
      ∫ q in s ∩ {q | q.2 ∈ couplingScopeTrialBurnPrebridge Δ lam R m i J N k},
        ({p : FieldPair d × Regeneration.CoupledSample d |
          p.2.2 (m + k) = true ∧ Regeneration.NoBacktracking R
            (Regeneration.pathTimeShift
              (Regeneration.sampleTimeShift Δ p.2 ((m : ℝ≥0) * Δ)).1
                (((k + 1 : ℕ) : ℝ≥0) * Δ)) i}).indicator (fun _ => (1 : ℝ)) q
          ∂Regeneration.annealedCoupledLaw Q K) :
    ∀ᵐ q ∂Regeneration.annealedCoupledLaw Q K,
      q.2 ∈ couplingScopeTrialBurnPrebridge Δ lam R m i J N k →
      g q = ((Regeneration.annealedCoupledLaw Q K)[
        ({p : FieldPair d × Regeneration.CoupledSample d |
          p.2.2 (m + k) = true ∧ Regeneration.NoBacktracking R
            (Regeneration.pathTimeShift
              (Regeneration.sampleTimeShift Δ p.2 ((m : ℝ≥0) * Δ)).1
                (((k + 1 : ℕ) : ℝ≥0) * Δ)) i}).indicator (fun _ => (1 : ℝ)) |
          couplingScopeAnnealedHistory Δ (m + k)]) q := by
  let μ := Regeneration.annealedCoupledLaw Q K
  let A : Set (FieldPair d × Regeneration.CoupledSample d) :=
    {q | q.2 ∈ couplingScopeTrialBurnPrebridge Δ lam R m i J N k}
  let B : Set (FieldPair d × Regeneration.CoupledSample d) :=
    {p | p.2.2 (m + k) = true ∧ Regeneration.NoBacktracking R
      (Regeneration.pathTimeShift
        (Regeneration.sampleTimeShift Δ p.2 ((m : ℝ≥0) * Δ)).1
          (((k + 1 : ℕ) : ℝ≥0) * Δ)) i}
  let f := B.indicator (fun _ => (1 : ℝ))
  let : IsProbabilityMeasure μ := Regeneration.annealedCoupledLaw_isProbabilityMeasure Q K hK
  have hH := coupling_scope_annealed_history_le (d := d) Δ (m + k)
  have hA : MeasurableSet[couplingScopeAnnealedHistory Δ (m + k)] A :=
    (coupling_scope_measurableSet_trial_burn_prebridge_finiteHistory
      Δ hΔ lam R hlam hR m i J N k).preimage (Measurable.of_comap_le le_rfl)
  have hA' : MeasurableSet A := hH A hA
  have hw : Measurable (fun q : FieldPair d × Regeneration.CoupledSample d =>
      Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)) :=
    (Regeneration.measurable_sampleTimeShift Δ).comp (measurable_const.prodMk measurable_snd)
  have hB : MeasurableSet B :=
    (measurableSet_eq_fun ((measurable_pi_apply (m + k)).comp measurable_snd.snd)
      measurable_const).inter ((Regeneration.measurableSet_NoBacktracking R i).preimage
        (Probability.continuous_path_time_shift.measurable.comp
          (measurable_const.prodMk hw.fst)))
  have hf : Integrable f μ := (integrable_const 1).indicator hB
  have heq : A.indicator g =ᵐ[μ] μ[A.indicator f | couplingScopeAnnealedHistory Δ (m + k)] := by
    apply ae_eq_condExp_of_forall_setIntegral_eq hH (hf.indicator hA')
    · intro s hs hfin
      exact (hg.indicator hA').integrableOn
    · intro s hs hfin
      rw [setIntegral_indicator hA', setIntegral_indicator hA']
      exact hdis s hs
    · obtain ⟨g₀, hg₀, hgg₀⟩ := hgm
      refine ⟨A.indicator g₀, hg₀.indicator hA, ?_⟩
      filter_upwards [hgg₀] with q hq
      by_cases hqa : q ∈ A
      · simp only [Set.indicator_of_mem hqa, hq]
      · simp only [Set.indicator_of_notMem hqa]
  have hind : μ[A.indicator f | couplingScopeAnnealedHistory Δ (m + k)] =ᵐ[μ]
      A.indicator (μ[f | couplingScopeAnnealedHistory Δ (m + k)]) :=
    condExp_indicator hf hA
  filter_upwards [heq, hind] with q hq hi hqa
  have hqa' : q ∈ A := hqa
  have h := hq.trans hi
  simpa only [Set.indicator_of_mem hqa'] using h

/-- The conditional success identity on Burn extends to every integrable,
prebridge-history measurable signed multiplier. -/
theorem coupling_scope_success_integrable_history_on_burn {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (K : Regeneration.CoupledQuenchedLaws d) (hK : Regeneration.HasProbabilityLaws Q K)
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (lam R : ℝ) (hlam : 0 < lam) (hR : 0 < R)
    (m : ℕ) (i : Fin d) (J N k : ℕ)
    (g w : FieldPair d × Regeneration.CoupledSample d → ℝ)
    (hw : Integrable w (Regeneration.annealedCoupledLaw Q K))
    (hwm : AEStronglyMeasurable[couplingScopeAnnealedHistory Δ (m + k)] w
      (Regeneration.annealedCoupledLaw Q K))
    (hcond : ∀ᵐ q ∂Regeneration.annealedCoupledLaw Q K,
      q.2 ∈ couplingScopeTrialBurnPrebridge Δ lam R m i J N k →
      g q = ((Regeneration.annealedCoupledLaw Q K)[
        ({p : FieldPair d × Regeneration.CoupledSample d |
          p.2.2 (m + k) = true ∧ Regeneration.NoBacktracking R
            (Regeneration.pathTimeShift
              (Regeneration.sampleTimeShift Δ p.2 ((m : ℝ≥0) * Δ)).1
                (((k + 1 : ℕ) : ℝ≥0) * Δ)) i}).indicator (fun _ => (1 : ℝ)) |
          couplingScopeAnnealedHistory Δ (m + k)]) q) :
    ∫ q in {q | q.2 ∈ couplingScopeTrialBurnPrebridge Δ lam R m i J N k},
      w q * ({p : FieldPair d × Regeneration.CoupledSample d |
        p.2.2 (m + k) = true ∧ Regeneration.NoBacktracking R
          (Regeneration.pathTimeShift
            (Regeneration.sampleTimeShift Δ p.2 ((m : ℝ≥0) * Δ)).1
              (((k + 1 : ℕ) : ℝ≥0) * Δ)) i}).indicator (fun _ => (1 : ℝ)) q
        ∂Regeneration.annealedCoupledLaw Q K =
    ∫ q in {q | q.2 ∈ couplingScopeTrialBurnPrebridge Δ lam R m i J N k},
      w q * g q ∂Regeneration.annealedCoupledLaw Q K := by
  let μ := Regeneration.annealedCoupledLaw Q K
  let A : Set (FieldPair d × Regeneration.CoupledSample d) :=
    {q | q.2 ∈ couplingScopeTrialBurnPrebridge Δ lam R m i J N k}
  let B : Set (FieldPair d × Regeneration.CoupledSample d) :=
    {p | p.2.2 (m + k) = true ∧ Regeneration.NoBacktracking R
      (Regeneration.pathTimeShift
        (Regeneration.sampleTimeShift Δ p.2 ((m : ℝ≥0) * Δ)).1
          (((k + 1 : ℕ) : ℝ≥0) * Δ)) i}
  let f := B.indicator (fun _ => (1 : ℝ))
  let v := A.indicator w
  let : IsProbabilityMeasure μ := Regeneration.annealedCoupledLaw_isProbabilityMeasure Q K hK
  have hH := coupling_scope_annealed_history_le (d := d) Δ (m + k)
  have hA : MeasurableSet[couplingScopeAnnealedHistory Δ (m + k)] A :=
    (coupling_scope_measurableSet_trial_burn_prebridge_finiteHistory
      Δ hΔ lam R hlam hR m i J N k).preimage (Measurable.of_comap_le le_rfl)
  have hA' : MeasurableSet A := hH A hA
  have hshift : Measurable (fun q : FieldPair d × Regeneration.CoupledSample d =>
      Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)) :=
    (Regeneration.measurable_sampleTimeShift Δ).comp (measurable_const.prodMk measurable_snd)
  have hB : MeasurableSet B :=
    (measurableSet_eq_fun ((measurable_pi_apply (m + k)).comp measurable_snd.snd)
      measurable_const).inter ((Regeneration.measurableSet_NoBacktracking R i).preimage
        (Probability.continuous_path_time_shift.measurable.comp
          (measurable_const.prodMk hshift.fst)))
  have hf : Integrable f μ := (integrable_const 1).indicator hB
  have hv : Integrable v μ := hw.indicator hA'
  have hvm : AEStronglyMeasurable[couplingScopeAnnealedHistory Δ (m + k)] v μ := by
    obtain ⟨w₀, hw₀, hww₀⟩ := hwm
    refine ⟨A.indicator w₀, hw₀.indicator hA, ?_⟩
    filter_upwards [hww₀] with q hq
    by_cases hqa : q ∈ A
    · simp only [v, Set.indicator_of_mem hqa, hq]
    · simp only [v, Set.indicator_of_notMem hqa]
  have hfb : ∀ᵐ q ∂μ, ‖f q‖ ≤ (1 : ℝ) := by
    filter_upwards [] with q
    by_cases hq : q ∈ B <;> simp [f, hq]
  have hvf : Integrable (v * f) μ := hv.mul_bdd hf.aestronglyMeasurable hfb
  have hpull := condExp_mul_of_aestronglyMeasurable_left hvm hvf hf
  have heq : ∫ q, v q * f q ∂μ = ∫ q, v q * g q ∂μ := by
    calc
      ∫ q, v q * f q ∂μ = ∫ q, (μ[v * f | couplingScopeAnnealedHistory Δ (m + k)]) q ∂μ :=
        (integral_condExp hH).symm
      _ = ∫ q, v q * (μ[f | couplingScopeAnnealedHistory Δ (m + k)]) q ∂μ := integral_congr_ae hpull
      _ = ∫ q, v q * g q ∂μ := by
        apply integral_congr_ae
        filter_upwards [hcond] with q hq
        by_cases hqa : q ∈ A
        · have he : g q = (μ[f | couplingScopeAnnealedHistory Δ (m + k)]) q := hq hqa
          simp only [v, Set.indicator_of_mem hqa, ← he]
        · simp only [v, Set.indicator_of_notMem hqa, zero_mul]
  change ∫ q in A, w q * f q ∂μ = ∫ q in A, w q * g q ∂μ
  rw [← integral_indicator hA', ← integral_indicator hA']
  simpa only [v, Set.indicator_mul_left] using heq

/-- A single actual restarted endpoint kernel represents every signed,
integrable sample-history pairing with selected success on Burn. -/
theorem coupling_scope_burn_success_integrable_history_endpoint_kernel {d : ℕ}
    (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1) (l δ : ℝ) (hl : 0 < l)
    (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K)
    (m J N k : ℕ) :
    let Δ := Regeneration.Renewal.regenDelta lam
    let R := l / lam
    let i := Regeneration.Renewal.forceCoord hd
    let A := couplingScopeTrialBurnPrebridge Δ lam R m i J N k
    let μ := Regeneration.annealedCoupledLaw Q.measure K
    ∃ B : Vec d × FieldPair d → ℝ, Measurable B ∧ Regeneration.BoundedRealTest B ∧
      (∀ᵐ p ∂(volume : Measure (Vec d)).prod Q.measure,
        B p = ∫ z, Regeneration.killedFutureTest R i (fun _ => 1) (p, z) ∂K p) ∧
      ∀ w : FieldPair d × Regeneration.CoupledSample d → ℝ,
      Integrable w μ → AEStronglyMeasurable[couplingScopeAnnealedHistory Δ (m + k)] w μ →
      (∫ q in {q | q.2 ∈ A}, w q *
        ({p : FieldPair d × Regeneration.CoupledSample d |
          p.2.2 (m + k) = true ∧ Regeneration.NoBacktracking R
            (Regeneration.pathTimeShift
              (Regeneration.sampleTimeShift Δ p.2 ((m : ℝ≥0) * Δ)).1
                (((k + 1 : ℕ) : ℝ≥0) * Δ)) i}).indicator (fun _ => (1 : ℝ)) q ∂μ) =
      ∫ q in {q | q.2 ∈ A}, w q *
        (μ[fun q => δ * Regeneration.endpointAverage i R
          (q.2.1 (((m + k : ℕ) : ℝ≥0) * Δ)) (fun y => B (y, q.1)) |
            couplingScopeAnnealedHistory Δ (m + k)]) q ∂μ := by
  dsimp only
  let Δ := Regeneration.Renewal.regenDelta lam
  let R := l / lam
  let i := Regeneration.Renewal.forceCoord hd
  let μ := Regeneration.annealedCoupledLaw Q.measure K
  have hΔ : 0 < Δ := Real.toNNReal_pos.mpr (inv_pos.mpr (sq_pos_of_pos h₀))
  have hR : 0 < R := div_pos hl h₀
  obtain ⟨B, hB, hbB, hBp, hcond⟩ :=
    coupling_scope_burn_success_condExp_endpoint_kernel hd Q lam h₀ h₁ l δ hl P K hK m J N k
  refine ⟨B, hB, hbB, hBp, ?_⟩
  intro w hw hwm
  apply coupling_scope_success_integrable_history_on_burn Q.measure K hK.1 Δ hΔ lam R h₀ hR
    m i J N k _ w hw hwm
  filter_upwards [hcond] with q hq hqa
  exact (hq hqa).symm

#print axioms coupling_scope_burn_success_integrable_history_endpoint_kernel

/-- A lower bound on the actual restarted endpoint average on Burn yields the
same lower bound for the selected success probability conditioned on history. -/
theorem coupling_scope_burn_success_condExp_lower_of_endpoint_average {d : ℕ}
    (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1) (l δ : ℝ) (hl : 0 < l)
    (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K)
    (m J N k : ℕ) :
    let Δ := Regeneration.Renewal.regenDelta lam
    let R := l / lam
    let i := Regeneration.Renewal.forceCoord hd
    let A := {q : FieldPair d × Regeneration.CoupledSample d |
      q.2 ∈ couplingScopeTrialBurnPrebridge Δ lam R m i J N k}
    let μ := Regeneration.annealedCoupledLaw Q.measure K
    ∃ B : Vec d × FieldPair d → ℝ, Measurable B ∧ Regeneration.BoundedRealTest B ∧
      (∀ᵐ p ∂(volume : Measure (Vec d)).prod Q.measure,
        B p = ∫ z, Regeneration.killedFutureTest R i (fun _ => 1) (p, z) ∂K p) ∧
      ∀ ε : ℝ,
      (∀ᵐ q ∂μ, q ∈ A → ε ≤ δ * Regeneration.endpointAverage i R
        (q.2.1 (((m + k : ℕ) : ℝ≥0) * Δ)) (fun y => B (y, q.1))) →
      ∀ᵐ q ∂μ, q ∈ A → ε ≤
        (μ[({p : FieldPair d × Regeneration.CoupledSample d |
          p.2.2 (m + k) = true ∧ Regeneration.NoBacktracking R
            (Regeneration.pathTimeShift
              (Regeneration.sampleTimeShift Δ p.2 ((m : ℝ≥0) * Δ)).1
                (((k + 1 : ℕ) : ℝ≥0) * Δ)) i}).indicator (fun _ => (1 : ℝ)) |
            couplingScopeAnnealedHistory Δ (m + k)]) q := by
  classical
  dsimp only
  let Δ := Regeneration.Renewal.regenDelta lam
  let R := l / lam
  let i := Regeneration.Renewal.forceCoord hd
  let μ := Regeneration.annealedCoupledLaw Q.measure K
  let A : Set (FieldPair d × Regeneration.CoupledSample d) :=
    {q | q.2 ∈ couplingScopeTrialBurnPrebridge Δ lam R m i J N k}
  let H := couplingScopeAnnealedHistory (d := d) Δ (m + k)
  have hΔ : 0 < Δ := Real.toNNReal_pos.mpr (inv_pos.mpr (sq_pos_of_pos h₀))
  have hR : 0 < R := div_pos hl h₀
  let : IsProbabilityMeasure μ :=
    Regeneration.annealedCoupledLaw_isProbabilityMeasure Q.measure K hK.1
  have hH := coupling_scope_annealed_history_le (d := d) Δ (m + k)
  have hA : MeasurableSet[H] A :=
    (coupling_scope_measurableSet_trial_burn_prebridge_finiteHistory
      Δ hΔ lam R h₀ hR m i J N k).preimage (Measurable.of_comap_le le_rfl)
  have hA' := hH A hA
  obtain ⟨B, hB, hbB, hBp, hcond⟩ :=
    coupling_scope_burn_success_condExp_endpoint_kernel hd Q lam h₀ h₁ l δ hl P K hK m J N k
  refine ⟨B, hB, hbB, hBp, ?_⟩
  intro ε hlow
  let g : FieldPair d × Regeneration.CoupledSample d → ℝ := fun q =>
    δ * Regeneration.endpointAverage i R (q.2.1 (((m + k : ℕ) : ℝ≥0) * Δ))
      (fun y => B (y, q.1))
  have hg : Integrable g μ := (coupling_scope_endpoint_kernel_integrable Q.measure K hK.1
    i R hR (((m + k : ℕ) : ℝ≥0) * Δ) δ B hB hbB).2
  have hle : A.indicator (fun _ => ε) ≤ᵐ[μ] A.indicator g := by
    filter_upwards [hlow] with q hq
    by_cases ha : q ∈ A
    · simpa [Set.indicator_of_mem ha, g] using hq ha
    · simp [Set.indicator_of_notMem ha]
  have hmono := condExp_mono (μ := μ) (m := H) ((integrable_const ε).indicator hA')
    (hg.indicator hA') hle
  have hind := condExp_indicator hg hA
  have hconst := condExp_indicator (μ := μ) (integrable_const ε) hA
  filter_upwards [hmono, hind, hconst, hcond] with q hq hi hc hs ha
  change μ[A.indicator (fun _ => ε) | H] q = A.indicator (μ[fun _ => ε | H]) q at hc
  change μ[A.indicator g | H] q = A.indicator (μ[g | H]) q at hi
  rw [condExp_const hH, Set.indicator_of_mem (s := A) (show q ∈ A from ha)] at hc
  rw [Set.indicator_of_mem (s := A) (show q ∈ A from ha)] at hi
  rw [hc, hi] at hq
  exact le_trans hq (le_of_eq (hs ha).symm)

#print axioms coupling_scope_burn_success_condExp_lower_of_endpoint_average

/-- A Burn set-integral disintegration gives the signed integrable history
pairing. The set-integral identity is a separate supplied-law obligation. -/
theorem coupling_scope_success_integrable_history_on_burn_of_setIntegral_kernel {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (K : Regeneration.CoupledQuenchedLaws d) (hK : Regeneration.HasProbabilityLaws Q K)
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (lam R : ℝ) (hlam : 0 < lam) (hR : 0 < R)
    (m : ℕ) (i : Fin d) (J N k : ℕ)
    (g w : FieldPair d × Regeneration.CoupledSample d → ℝ)
    (hg : Integrable g (Regeneration.annealedCoupledLaw Q K))
    (hgm : AEStronglyMeasurable[couplingScopeAnnealedHistory Δ (m + k)] g
      (Regeneration.annealedCoupledLaw Q K))
    (hw : Integrable w (Regeneration.annealedCoupledLaw Q K))
    (hwm : AEStronglyMeasurable[couplingScopeAnnealedHistory Δ (m + k)] w
      (Regeneration.annealedCoupledLaw Q K))
    (hdis : ∀ s : Set (FieldPair d × Regeneration.CoupledSample d),
      MeasurableSet[couplingScopeAnnealedHistory Δ (m + k)] s →
      ∫ q in s ∩ {q | q.2 ∈ couplingScopeTrialBurnPrebridge Δ lam R m i J N k},
        g q ∂Regeneration.annealedCoupledLaw Q K =
      ∫ q in s ∩ {q | q.2 ∈ couplingScopeTrialBurnPrebridge Δ lam R m i J N k},
        ({p : FieldPair d × Regeneration.CoupledSample d |
          p.2.2 (m + k) = true ∧ Regeneration.NoBacktracking R
            (Regeneration.pathTimeShift
              (Regeneration.sampleTimeShift Δ p.2 ((m : ℝ≥0) * Δ)).1
                (((k + 1 : ℕ) : ℝ≥0) * Δ)) i}).indicator (fun _ => (1 : ℝ)) q
          ∂Regeneration.annealedCoupledLaw Q K) :
    ∫ q in {q | q.2 ∈ couplingScopeTrialBurnPrebridge Δ lam R m i J N k},
      w q * ({p : FieldPair d × Regeneration.CoupledSample d |
        p.2.2 (m + k) = true ∧ Regeneration.NoBacktracking R
          (Regeneration.pathTimeShift
            (Regeneration.sampleTimeShift Δ p.2 ((m : ℝ≥0) * Δ)).1
              (((k + 1 : ℕ) : ℝ≥0) * Δ)) i}).indicator (fun _ => (1 : ℝ)) q
        ∂Regeneration.annealedCoupledLaw Q K =
    ∫ q in {q | q.2 ∈ couplingScopeTrialBurnPrebridge Δ lam R m i J N k},
      w q * g q ∂Regeneration.annealedCoupledLaw Q K := by
  apply coupling_scope_success_integrable_history_on_burn Q K hK Δ hΔ lam R hlam hR
    m i J N k g w hw hwm
  exact coupling_scope_success_condExp_on_burn_of_setIntegral_kernel Q K hK Δ hΔ
    lam R hlam hR m i J N k g hg hgm hdis

#print axioms coupling_scope_success_integrable_history_on_burn_of_setIntegral_kernel

#print axioms coupling_scope_success_integrable_history_on_burn

#print axioms coupling_scope_success_condExp_on_burn_of_setIntegral_kernel

open EinsteinRelation.Regeneration ProbabilityTheory

/-- A uniform lower bound for a proposed restarted success kernel transfers
through the selected successful endpoint law. The endpoint ratio, restarted
kernel and its identification with no-backtracking remain separate obligations. -/
theorem coupling_scope_selected_subball_kernel_lower {d : ℕ}
    (Δ : ℝ≥0) (R ρ : ℝ) (i : Fin d)
    (L : CoupledQuenchedLaws d) (xω : Vec d × FieldPair d)
    [IsProbabilityMeasure (L xω)]
    (N : CoupledSample d → ℕ) (hN : Measurable N)
    (hsucc : L xω {q | q.2 (N q) = true} ≠ 0)
    (y : Vec d)
    (hratio : (∫ q, (endpointBall i ρ y).indicator (fun _ => (1 : ℝ))
      (q.1 ((N q : ℝ≥0) * Δ + Δ))
      ∂cond (L xω) {q | q.2 (N q) = true}) = (ρ / R) ^ d)
    (p : CoupledSample d → ℝ) (η : ℝ)
    (hp : Integrable p (cond (L xω) {q | q.2 (N q) = true}))
    (hp0 : ∀ᵐ q ∂cond (L xω) {q | q.2 (N q) = true}, 0 ≤ p q)
    (hplower : ∀ᵐ q ∂cond (L xω) {q | q.2 (N q) = true},
      q.1 ((N q : ℝ≥0) * Δ + Δ) ∈ endpointBall i ρ y → η ≤ p q) :
    η * (ρ / R) ^ d ≤ ∫ q, p q ∂cond (L xω) {q | q.2 (N q) = true} := by
  let μ := cond (L xω) {q | q.2 (N q) = true}
  let : IsProbabilityMeasure μ := cond_isProbabilityMeasure hsucc
  let S : Set (CoupledSample d) :=
    {q | q.1 ((N q : ℝ≥0) * Δ + Δ) ∈ endpointBall i ρ y}
  have hm : Measurable (fun q : CoupledSample d =>
      q.1 ((N q : ℝ≥0) * Δ + Δ)) := by
    exact (measurable_from_prod_countable_right
      (f := fun p : ℕ × CoupledSample d => p.2.1 ((p.1 : ℝ≥0) * Δ + Δ))
      (fun n => (continuous_eval_const ((n : ℝ≥0) * Δ + Δ)).measurable.comp
        (measurable_fst : Measurable (fun q : CoupledSample d => q.1)))).comp
        (hN.prodMk measurable_id)
  have hS : MeasurableSet S :=
    ((measurableSet_endpointBall_pair i ρ).preimage
      (measurable_const.prodMk measurable_id)).preimage hm
  have hbound : ∀ᵐ q ∂μ, S.indicator (fun _ => η) q ≤ p q := by
    filter_upwards [hp0, hplower] with q hq0 hq
    by_cases hqS : q ∈ S
    · simpa [Set.indicator_of_mem hqS] using hq hqS
    · simpa [Set.indicator_of_notMem hqS] using hq0
  calc
    η * (ρ / R) ^ d = ∫ q, S.indicator (fun _ => η) q ∂μ := by
      rw [← hratio, ← integral_const_mul]
      congr 1
      funext q
      by_cases hq : q.1 ((N q : ℝ≥0) * Δ + Δ) ∈ endpointBall i ρ y <;>
        simp [S, Set.indicator, hq]
    _ ≤ ∫ q, p q ∂μ := integral_mono_ae ((integrable_const η).indicator hS) hp hbound

#print axioms coupling_scope_selected_subball_kernel_lower

#print axioms coupling_scope_success_condExp_of_setIntegral_kernel

#print axioms coupling_scope_trial_lost_product_of_source_split_prebridge_condExp
#print axioms coupling_scope_both_laws_grid_record_of_burn_prebridge_condExp
#print axioms coupling_scope_trial_start_monotone
#print axioms coupling_scope_earlier_failure_finite_of_trial_start
#print axioms couplingScopeTrialBurnPrebridge
#print axioms coupling_scope_measurableSet_trial_burn_prebridge
#print axioms coupling_scope_mem_trial_burn_prebridge_of_prefix
#print axioms coupling_scope_measurableSet_trial_burn_prebridge_finiteHistory

#print axioms coupling_scope_both_laws_grid_record_of_burn_estimate

#print axioms coupling_scope_ae_all_grid_trial_entries_of_escape_and_guard_estimates
#print axioms coupling_scope_trial_burn_full_prefix
#print axioms coupling_scope_ae_all_cycles_finite_of_escape_and_burn_estimate

#print axioms coupling_scope_trial_start_le_failure
#print axioms coupling_scope_trial_start_add_two_step_le_succ
#print axioms coupling_scope_nat_two_step_le_trial_start
#print axioms coupling_scope_trial_prebridge_tendsto_atTop
#print axioms couplingScopeTrialBurn
#print axioms couplingScopeTrialLost
#print axioms coupling_scope_measurableSet_trial_burn
#print axioms coupling_scope_measurableSet_trial_lost
#print axioms coupling_scope_trial_lost_antitone
#print axioms coupling_scope_exists_trial_burn_of_escape
#print axioms coupling_scope_infinite_shifted_regeneration_mem_lost
#print axioms coupling_scope_ae_all_grid_first_regeneration_finite_of_burn_estimate

#print axioms coupling_scope_sample_restart_add
#print axioms couplingScopeSelectedRestartLevel
#print axioms coupling_scope_selected_restart_level_eq
#print axioms coupling_scope_measurable_selected_restart_level_finiteHistory
#print axioms coupling_scope_selected_restart_level_div_pos
#print axioms coupling_scope_selected_passage_eq
#print axioms coupling_scope_selected_even_guard_iff
#print axioms coupling_scope_selected_successful_candidate_eq
#print axioms coupling_scope_ae_all_grid_trial_entries_of_successful_candidates

#print axioms ConditionalTrialExhaustion.directional_escape_of_positive_velocity
#print axioms ConditionalTrialExhaustion.directional_escape_pathTimeShift
#print axioms ConditionalTrialExhaustion.firstHittingAbove_ne_top_of_escape
#print axioms ConditionalTrialExhaustion.crossing_at_firstHittingAbove_of_ne_top
#print axioms ConditionalTrialExhaustion.roundUp_ne_top
#print axioms ConditionalTrialExhaustion.passageSequence_ne_top_of_escape
#print axioms ConditionalTrialExhaustion.passageSequence_next_attained_of_escape
#print axioms ConditionalTrialExhaustion.shifted_passageSequence_ne_top_of_escape
#print axioms ConditionalTrialExhaustion.shifted_firstHittingAbove_attained_of_escape
#print axioms ConditionalTrialExhaustion.rounded_passage_lt_next_of_escape
#print axioms coupling_scope_ae_passages_finite_of_escape
#print axioms coupling_scope_ae_passages_finite_of_positive_velocity
#print axioms coupling_scope_ae_passages_finite_of_quenched_positive_velocity
#print axioms coupling_scope_gmp_physical_origin_passages_finite
#print axioms coupling_scope_ae_candidates_finite_of_escape_and_guard_estimates
#print axioms coupling_scope_ae_candidates_finite_of_quenched_velocity_and_guard_estimates

#print axioms ConditionalTrialExhaustion.finite_product_of_failure_step
#print axioms ConditionalTrialExhaustion.measure_inter_le_of_condExp
#print axioms ConditionalTrialExhaustion.finite_product_of_condExp
#print axioms ConditionalTrialExhaustion.measure_iInter_eq_zero_of_failure_step
#print axioms ConditionalTrialExhaustion.measure_sdiff_le_of_success_measure
#print axioms ConditionalTrialExhaustion.measure_iInter_eq_zero_of_condExp
#print axioms ConditionalTrialExhaustion.roundUp_add_step_le_of_lt
#print axioms ConditionalTrialExhaustion.passage_add_step_le_two_later
#print axioms couplingScopePassage
#print axioms couplingScopeEvenGuard
#print axioms couplingScopeEvenGuardFailure
#print axioms coupling_scope_even_passage_windows_separated
#print axioms coupling_scope_measurable_passage
#print axioms coupling_scope_measurableSet_even_guard
#print axioms coupling_scope_measurableSet_even_guard_failure
#print axioms coupling_scope_even_guard_failure_succ
#print axioms coupling_scope_even_guard_failure_product_of_estimate
#print axioms coupling_scope_first_candidate_finite_of_good
#print axioms coupling_scope_ae_first_candidate_finite_of_guard_estimate
#print axioms coupling_scope_path_restart_add
#print axioms coupling_scope_ae_candidates_finite_of_guard_estimates
#print axioms coupling_scope_passage_eq_of_prefix
#print axioms coupling_scope_even_guard_iff_of_prefix
#print axioms coupling_scope_measurableSet_rounded_passage_le_finiteHistory
#print axioms coupling_scope_measurableSet_even_guard_observed_finiteHistory
#print axioms coupling_scope_measurableSet_even_guard_failure_observed_finiteHistory
#print axioms couplingScopeEvenGuardHistoryFailure
#print axioms coupling_scope_even_guard_history_failure_eq
#print axioms coupling_scope_measurableSet_even_guard_history_failure_finiteHistory
#print axioms coupling_scope_measure_even_guard_history_failure_fresh_bit
#print axioms coupling_scope_rounded_passage_le_later
#print axioms coupling_scope_even_guard_history_failure_iff_of_next_le
#print axioms coupling_scope_measurableSet_even_guard_failure_next_le_finiteHistory
#print axioms ConditionalTrialExhaustion.roundUp_toNNReal_le_add
#print axioms ConditionalTrialExhaustion.isGoodPassage_of_euclidean_tube
#print axioms coupling_scope_even_guard_history_failure_restart
#print axioms couplingScopeRestartLevel
#print axioms coupling_scope_measurable_restart_level_finiteHistory
#print axioms coupling_scope_trial_reentry_finite
#print axioms coupling_scope_ae_successful_candidate_finite_of_guard_estimates
#print axioms coupling_scope_trial_entries_of_successful_candidates
#print axioms coupling_scope_ae_trial_entries_of_guard_estimates
#print axioms coupling_scope_first_regeneration_eq_top_iff_all_trials_finite
#print axioms coupling_scope_first_trial_slice_of_successful_candidate
#print axioms coupling_scope_first_regeneration_of_selected_bridge
#print axioms coupling_scope_trial_start_succ_finite_requires_failure
#print axioms coupling_scope_finite_trial_product_of_return_estimate
#print axioms coupling_scope_ae_first_regeneration_finite_of_return_estimate
#print axioms coupling_scope_trial_return_event_eq
#print axioms coupling_scope_ae_first_regeneration_finite_of_guard_and_return_estimates
#print axioms ConditionalTrialExhaustion.measure_inter_ge_of_condExp
#print axioms couplingScopeAnnealedHistory
#print axioms coupling_scope_annealed_history_le
#print axioms coupling_scope_measurableSet_trial_start_slice_annealedHistory
#print axioms coupling_scope_trial_entry_eq_iUnion_slices
#print axioms coupling_scope_trial_start_slices_pairwise_disjoint
#print axioms coupling_scope_trial_return_slice_eq
#print axioms coupling_scope_return_estimate_of_slice_estimates
#print axioms coupling_scope_measurableSet_trial_prebridge_annealedHistory
#print axioms coupling_scope_trial_slice_return_bound_of_prebridge_condExp
#print axioms coupling_scope_return_estimate_of_prebridge_condExp
#print axioms coupling_scope_ae_first_regeneration_finite_of_prebridge_condExp
#print axioms couplingScopeRetainedFailureCount
#print axioms coupling_scope_retained_count_le_iff
#print axioms coupling_scope_retained_count_tail_iff
#print axioms coupling_scope_retained_count_eq_zero_off_burn
#print axioms coupling_scope_retained_count_eq_top_iff
#print axioms coupling_scope_measurable_retained_count
#print axioms coupling_scope_retained_count_toENNReal_eq_tsum
#print axioms coupling_scope_measurable_retained_count_toENNReal
#print axioms coupling_scope_lintegral_retained_tail_finset
#print axioms coupling_scope_lintegral_retained_count_eq_tsum
#print axioms coupling_scope_retained_count_eq_natCast_iff
#print axioms coupling_scope_retained_count_finite_noBacktracking
#print axioms coupling_scope_lintegral_retained_count_le_of_geometric_tail
#print axioms coupling_scope_lintegral_retained_count_ne_top_of_geometric_tail
#print axioms coupling_scope_retained_count_integrable_of_lintegral_ne_top
#print axioms coupling_scope_hasSum_retained_tail_of_lintegral_ne_top
#print axioms coupling_scope_lintegral_conditioned_retained_count_eq_tsum
#print axioms coupling_scope_lintegral_conditioned_retained_count_le_of_geometric_tail
#print axioms coupling_scope_both_laws_retained_count_integrable_of_geometric_tail
#print axioms couplingScopeRetainedTrialCount
#print axioms coupling_scope_retained_trial_count_toENNReal_eq_add
#print axioms coupling_scope_retained_trial_count_toENNReal_eq_tsum
#print axioms coupling_scope_measurable_retained_trial_count_toENNReal
#print axioms coupling_scope_lintegral_retained_trial_count_eq_tsum
#print axioms coupling_scope_lintegral_retained_trial_count_le_of_geometric_tail
#print axioms coupling_scope_retained_trial_count_integrable_of_geometric_tail
#print axioms coupling_scope_retained_count_ae_zero_of_null_burn
#print axioms coupling_scope_both_laws_ae_all_grid_retained_count_finite_of_geometric_tails
#print axioms coupling_scope_lintegral_retained_count_le_of_prebridge_condExp
#print axioms coupling_scope_both_laws_grid_record_and_retained_counts_of_burn_estimate

#print axioms coupling_scope_retained_trial_count_ae_zero_of_null_burn
#print axioms coupling_scope_retained_count_ae_zero_of_geometric_tail_zero


#print axioms coupling_scope_tube_inter_subset_guard
#print axioms coupling_scope_guard_estimate_of_tube_estimate
#print axioms coupling_scope_ae_all_grid_trial_entries_of_escape_and_tube_estimates


/-- A deterministic stopped path is measurable from the history up to the stop. -/
theorem coupling_scope_measurable_stoppedPath_history {d : ℕ} (T : ℝ≥0) :
    @Measurable (Path d) (Path d)
      (MarkovProcess.ContinuousPath.canonicalFiltration (alpha := Vec d) T)
      (borel (Path d)) (MarkovProcess.ContinuousPath.stoppedPath T) := by
  letI : MeasurableSpace (Path d) :=
    MarkovProcess.ContinuousPath.canonicalFiltration (alpha := Vec d) T
  apply ContinuousMap.measurable_iff_eval.mpr
  intro t
  change Measurable (fun γ : Path d => γ (min t T))
  exact (MarkovProcess.ContinuousPath.measurable_coordinateProcess_canonicalFiltration
    (alpha := Vec d) (min t T)).mono
      (MarkovProcess.ContinuousPath.canonicalFiltration.mono (min_le_right t T)) le_rfl

/-- Each actual passage time is a stopping time for the canonical path filtration. -/
theorem coupling_scope_isStoppingTime_passageSequence {d : ℕ}
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (lam R a : ℝ) (hR : 0 < R)
    (i : Fin d) (n : ℕ) :
    IsStoppingTime (MarkovProcess.ContinuousPath.canonicalFiltration (alpha := Vec d))
      (fun γ : Path d => Regeneration.passageSequence Δ lam R a γ i n) := by
  intro T
  have heq : {γ : Path d | Regeneration.passageSequence Δ lam R a γ i n ≤
      (T : ℝ≥0∞)} =
      (MarkovProcess.ContinuousPath.stoppedPath T) ⁻¹'
        {γ : Path d | Regeneration.passageSequence Δ lam R a γ i n ≤ (T : ℝ≥0∞)} := by
    ext γ
    exact (Regeneration.passageSequence_prefix_determined Δ hΔ lam R a hR γ
      (MarkovProcess.ContinuousPath.stoppedPath T γ) i n T
      (fun t ht => (MarkovProcess.ContinuousPath.stoppedPath_apply_of_le T γ t ht.2).symm)).1
  change @MeasurableSet (Path d)
    (MarkovProcess.ContinuousPath.canonicalFiltration (alpha := Vec d) T)
    {γ : Path d | Regeneration.passageSequence Δ lam R a γ i n ≤ (T : ℝ≥0∞)}
  rw [heq]
  apply coupling_scope_measurable_stoppedPath_history T
  exact ((Regeneration.measurable_passageSequence_joint Δ lam R i n).comp
    (measurable_const.prodMk measurable_id)) measurableSet_Iic

/-- A rounded passage sublevel is measurable from the original path history. -/
theorem coupling_scope_measurableSet_rounded_passage_history {d : ℕ}
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (lam R a : ℝ) (hR : 0 < R)
    (i : Fin d) (n : ℕ) (T : ℝ≥0) :
    @MeasurableSet (Path d)
      (MarkovProcess.ContinuousPath.canonicalFiltration (alpha := Vec d) T)
      {γ : Path d | Regeneration.roundUp Δ
        (Regeneration.passageSequence Δ lam R a γ i n) ≤ (T : ℝ≥0∞)} := by
  let E : Set (Path d) := {γ | Regeneration.roundUp Δ
    (Regeneration.passageSequence Δ lam R a γ i n) ≤ (T : ℝ≥0∞)}
  have heq : E = (MarkovProcess.ContinuousPath.stoppedPath T) ⁻¹' E := by
    ext γ
    have hpre : ∀ t ∈ Set.Icc (0 : ℝ≥0) T,
        γ t = MarkovProcess.ContinuousPath.stoppedPath T γ t :=
      fun t ht => (MarkovProcess.ContinuousPath.stoppedPath_apply_of_le T γ t ht.2).symm
    constructor
    · intro h
      have hv := (Regeneration.le_roundUp Δ hΔ _).trans h
      have hpass := (Regeneration.passageSequence_prefix_determined Δ hΔ lam R a hR
        γ (MarkovProcess.ContinuousPath.stoppedPath T γ) i n T hpre).2 hv
      change Regeneration.roundUp Δ _ ≤ (T : ℝ≥0∞)
      rw [← hpass]
      exact h
    · intro h
      have hv := (Regeneration.le_roundUp Δ hΔ _).trans h
      have hpass := (Regeneration.passageSequence_prefix_determined Δ hΔ lam R a hR
        (MarkovProcess.ContinuousPath.stoppedPath T γ) γ i n T
        (fun t ht => (hpre t ht).symm)).2 hv
      change Regeneration.roundUp Δ _ ≤ (T : ℝ≥0∞)
      rw [← hpass]
      exact h
  change @MeasurableSet (Path d)
    (MarkovProcess.ContinuousPath.canonicalFiltration (alpha := Vec d) T) E
  rw [heq]
  apply coupling_scope_measurable_stoppedPath_history T
  exact ((Regeneration.measurable_roundUp Δ).comp
    ((Regeneration.measurable_passageSequence_joint Δ lam R i n).comp
      (measurable_const.prodMk measurable_id))) measurableSet_Iic

/-- A stopped deterministic restart depends measurably on the original history. -/
theorem coupling_scope_measurable_stopped_shiftedPath_history {d : ℕ} (s T : ℝ≥0) :
    @Measurable (Path d) (Path d)
      (MarkovProcess.ContinuousPath.canonicalFiltration (alpha := Vec d) (s + T))
      (borel (Path d))
      (fun γ => MarkovProcess.ContinuousPath.stoppedPath T
        (Regeneration.pathTimeShift γ s)) := by
  letI : MeasurableSpace (Path d) :=
    MarkovProcess.ContinuousPath.canonicalFiltration (alpha := Vec d) (s + T)
  apply ContinuousMap.measurable_iff_eval.mpr
  intro t
  change Measurable (fun γ : Path d => γ (s + min t T))
  exact (MarkovProcess.ContinuousPath.measurable_coordinateProcess_canonicalFiltration
    (alpha := Vec d) (s + min t T)).mono
      (MarkovProcess.ContinuousPath.canonicalFiltration.mono
        (add_le_add_right (min_le_right t T) s)) le_rfl

/-- Rounded passage after a deterministic restart is measurable in the original history. -/
theorem coupling_scope_measurableSet_rounded_shifted_passage_history {d : ℕ}
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (lam R a : ℝ) (hR : 0 < R)
    (i : Fin d) (n : ℕ) (s T : ℝ≥0) :
    @MeasurableSet (Path d)
      (MarkovProcess.ContinuousPath.canonicalFiltration (alpha := Vec d) (s + T))
      {γ : Path d | Regeneration.roundUp Δ
        (Regeneration.passageSequence Δ lam R a (Regeneration.pathTimeShift γ s) i n) ≤
          (T : ℝ≥0∞)} := by
  let E : Set (Path d) := {γ | Regeneration.roundUp Δ
    (Regeneration.passageSequence Δ lam R a γ i n) ≤ (T : ℝ≥0∞)}
  have heq : {γ : Path d | Regeneration.roundUp Δ
      (Regeneration.passageSequence Δ lam R a (Regeneration.pathTimeShift γ s) i n) ≤
        (T : ℝ≥0∞)} =
      (fun γ : Path d => MarkovProcess.ContinuousPath.stoppedPath T
        (Regeneration.pathTimeShift γ s)) ⁻¹' E := by
    ext γ
    have hpre : ∀ t ∈ Set.Icc (0 : ℝ≥0) T,
        Regeneration.pathTimeShift γ s t =
          MarkovProcess.ContinuousPath.stoppedPath T (Regeneration.pathTimeShift γ s) t :=
      fun t ht => (MarkovProcess.ContinuousPath.stoppedPath_apply_of_le T
        (Regeneration.pathTimeShift γ s) t ht.2).symm
    constructor
    · intro h
      have hv := (Regeneration.le_roundUp Δ hΔ _).trans h
      have hpass := (Regeneration.passageSequence_prefix_determined Δ hΔ lam R a hR
        (Regeneration.pathTimeShift γ s)
        (MarkovProcess.ContinuousPath.stoppedPath T (Regeneration.pathTimeShift γ s))
        i n T hpre).2 hv
      change Regeneration.roundUp Δ _ ≤ (T : ℝ≥0∞)
      rw [← hpass]
      exact h
    · intro h
      have hv := (Regeneration.le_roundUp Δ hΔ _).trans h
      have hpass := (Regeneration.passageSequence_prefix_determined Δ hΔ lam R a hR
        (MarkovProcess.ContinuousPath.stoppedPath T (Regeneration.pathTimeShift γ s))
        (Regeneration.pathTimeShift γ s) i n T
        (fun t ht => (hpre t ht).symm)).2 hv
      change Regeneration.roundUp Δ _ ≤ (T : ℝ≥0∞)
      rw [← hpass]
      exact h
  rw [heq]
  apply coupling_scope_measurable_stopped_shiftedPath_history s T
  exact ((Regeneration.measurable_roundUp Δ).comp
    ((Regeneration.measurable_passageSequence_joint Δ lam R i n).comp
      (measurable_const.prodMk measurable_id))) measurableSet_Iic

#print axioms coupling_scope_measurable_stopped_shiftedPath_history
#print axioms coupling_scope_measurableSet_rounded_shifted_passage_history
#print axioms coupling_scope_measurableSet_rounded_passage_history

#print axioms coupling_scope_measurable_stoppedPath_history
#print axioms coupling_scope_isStoppingTime_passageSequence

#lint

end EinsteinFull.Blueprint
