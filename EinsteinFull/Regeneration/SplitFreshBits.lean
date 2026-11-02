import EinsteinFull.Regeneration.SplitCoinLaw
import EinsteinRelation.Probability.FiniteHistoryStopping
import Mathlib.Probability.Independence.Integration

/-!
# Fresh coins against the actual closed path history

The closed path history through the next grid endpoint depends only on the
sampled segment prefix. The exact prefix/coin product law therefore gives the
blueprint's literal FreshBitsAt integral identity for the actual glued kernel.
Time zero uses only the original path law's starting-position property. Both
origin and product-a.e. clauses follow from this pointwise construction.
Whole-path marginal identification, deterministic restart and stopped locality
remain separate internal obligations.
-/

open MeasureTheory ProbabilityTheory Preorder
open scoped NNReal ENNReal
noncomputable section
namespace EinsteinFull.Regeneration
open EinsteinRelation EinsteinRelation.Regeneration EinsteinRelation.Probability

/-- Extend an actual finite segment prefix by its first state. -/
def extendSplitSegmentPrefix {d : ℕ} (n : ℕ)
    (u : (j : Finset.Iic n) → SplitSegmentState d) : ℕ → SplitSegmentState d :=
  fun k => if hk : k ≤ n then u ⟨k, Finset.mem_Iic.mpr hk⟩
    else u ⟨0, Finset.mem_Iic.mpr (Nat.zero_le n)⟩

/-- The literal finite-prefix extension is measurable into segment sequence space. -/
theorem measurable_extendSplitSegmentPrefix {d : ℕ} (n : ℕ) :
    Measurable (extendSplitSegmentPrefix (d := d) n) := by
  apply Measurable.of_eval
  intro k
  by_cases hk : k ≤ n <;> simp only [extendSplitSegmentPrefix, hk, dite_true, dite_false]
  all_goals exact measurable_pi_apply _

/-- Extending a restricted prefix preserves all its actual segment coordinates. -/
theorem extendSplitSegmentPrefix_restrict {d : ℕ} (n : ℕ) (s : ℕ → SplitSegmentState d)
    (k : ℕ) (hk : k ≤ n) :
    extendSplitSegmentPrefix n (frestrictLe n s) k = s k := by
  simp only [extendSplitSegmentPrefix, dif_pos hk, frestrictLe_apply]

/-- A closed grid past of the literal gluing uses only the corresponding segment prefix. -/
theorem stoppedHistory_gluedSplitSegmentSample_prefix {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ)
    (n : ℕ) (s : ℕ → SplitSegmentState d) :
    stoppedHistorySample Δ (n + 1) (gluedSplitSegmentSample Δ hΔ s) =
      stoppedHistorySample Δ (n + 1) (gluedSplitSegmentSample Δ hΔ
        (extendSplitSegmentPrefix n (frestrictLe n s))) := by
  apply Prod.ext
  · apply ContinuousMap.ext
    intro t
    change glueSplitSegments Δ hΔ (fun k => (s k).2.1) (min t ((n + 1 : ℕ) * Δ)) =
      glueSplitSegments Δ hΔ
        (fun k => (extendSplitSegmentPrefix n (frestrictLe n s) k).2.1)
          (min t ((n + 1 : ℕ) * Δ))
    rw [glueSplitSegments_eq_sum Δ hΔ _ (n + 1) _ (min_le_right _ _),
      glueSplitSegments_eq_sum Δ hΔ _ (n + 1) _ (min_le_right _ _),
      extendSplitSegmentPrefix_restrict n s 0 (Nat.zero_le n)]
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    rw [splitSegmentIncrement, splitSegmentIncrement,
      extendSplitSegmentPrefix_restrict n s k (Nat.le_of_lt_succ (Finset.mem_range.mp hk))]
  · funext k
    change (if k < n + 1 then (s k).2.2 else false) =
      if k < n + 1 then (extendSplitSegmentPrefix n (frestrictLe n s) k).2.2 else false
    split_ifs with hk
    · rw [extendSplitSegmentPrefix_restrict n s k (Nat.le_of_lt_succ hk)]
    · rfl

variable {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ) (δ R : ℝ) (i : Fin d)
  (hδ₀ : 0 < δ) (hδ₁ : δ < 1) (hR : 0 < R)
  (P : QuenchedPathLaws d) [IsMarkovKernel P]
  (hminor : ∀ ω : FieldPair d,
    EinsteinFull.External.Source.GMP.HasSourceMinorization
      (fun x => P (x, ω)) Δ δ R i)

/-- The success indicator of every actual sampled coin has mean `δ`. -/
theorem integral_splitSegmentSequenceKernel_coin (a : Vec d × FieldPair d) (n : ℕ) :
    (∫ s, (if (s n).2.2 = true then (1 : ℝ) else 0)
      ∂splitSegmentSequenceKernel Δ δ R i hδ₀ hδ₁ hR P hminor a) = δ := by
  let A : Set (ℕ → SplitSegmentState d) := {s | (s n).2.2 = true}
  have hA : MeasurableSet A := (measurable_pi_apply n).snd.snd (measurableSet_singleton true)
  have heq : (fun s : ℕ → SplitSegmentState d =>
      if (s n).2.2 = true then (1 : ℝ) else 0) = A.indicator 1 := by
    funext s
    simp only [Set.indicator, A, Set.mem_setOf_eq, Pi.one_apply]
  rw [heq, integral_indicator_one hA]
  have h := congrArg (fun κ => κ a {true})
    (map_splitSegmentSequenceKernel_coin Δ δ R i hδ₀ hδ₁ hR P hminor n)
  rw [Kernel.map_apply _ (by fun_prop), Kernel.const_apply,
    Measure.map_apply (by fun_prop) (measurableSet_singleton true),
    splitCoinLaw_singleton] at h
  have hmass : splitSegmentSequenceKernel Δ δ R i hδ₀ hδ₁ hR P hminor a A =
      ENNReal.ofReal δ := by
    simpa only [A, Set.preimage, Set.mem_singleton_iff, ite_true] using h
  change (splitSegmentSequenceKernel Δ δ R i hδ₀ hδ₁ hR P hminor a A).toReal = δ
  rw [hmass]
  exact ENNReal.toReal_ofReal hδ₀.le

/-- Every exact finite-past test of the glued sample is independent of the next coin. -/
theorem indepFun_gluedSplitSegmentSample_past_coin (a : Vec d × FieldPair d) (n : ℕ)
    (H : CoupledSample d → ℝ)
    (hH : @Measurable (CoupledSample d) ℝ (finiteHistorySigma Δ (n + 1)) inferInstance H) :
    IndepFun (fun s => H (gluedSplitSegmentSample Δ hΔ s))
      (fun s : ℕ → SplitSegmentState d => (s (n + 1)).2.2)
      (splitSegmentSequenceKernel Δ δ R i hδ₀ hδ₁ hR P hminor a) := by
  let F : ((j : Finset.Iic n) → SplitSegmentState d) → ℝ := fun u =>
    H (gluedSplitSegmentSample Δ hΔ (extendSplitSegmentPrefix n u))
  have hF : Measurable F :=
    (hH.mono (finiteHistorySigma_le Δ (n + 1)) le_rfl).comp
      ((measurable_gluedSplitSegmentSample Δ hΔ).comp
        (measurable_extendSplitSegmentPrefix n))
  have heq : (fun s => H (gluedSplitSegmentSample Δ hΔ s)) = F ∘ frestrictLe n := by
    funext s
    dsimp only [Function.comp_def, F]
    rw [← finiteHistory_test_stopped Δ (n + 1) H hH (gluedSplitSegmentSample Δ hΔ s),
      ← finiteHistory_test_stopped Δ (n + 1) H hH
        (gluedSplitSegmentSample Δ hΔ (extendSplitSegmentPrefix n (frestrictLe n s))),
      stoppedHistory_gluedSplitSegmentSample_prefix]
  rw [heq]
  exact (indepFun_splitSegmentSequenceKernel_prefix_coin
    Δ δ R i hδ₀ hδ₁ hR P hminor a n).comp hF measurable_id

/-- The actual glued kernel satisfies the literal finite-past fresh-bit identity.
The only path-law hypothesis used here is its actual starting position. -/
theorem freshBitsAt_splitContinuousCouplingKernel
    (hstart : ∀ a, ∀ᵐ γ ∂P a, γ 0 = a.1) (a : Vec d × FieldPair d) :
    FreshBitsAt Δ δ (splitContinuousCouplingKernel Δ hΔ δ R i hδ₀ hδ₁ hR P hminor) a := by
  intro n H hH _hb
  have hHm : Measurable H := hH.mono (finiteHistorySigma_le Δ n) le_rfl
  have hcoin : Measurable (fun b : Bool => if b = true then (1 : ℝ) else 0) :=
    measurable_of_countable _
  have hbit : Measurable (fun z : CoupledSample d =>
      if z.2 n = true then (1 : ℝ) else 0) :=
    hcoin.comp ((measurable_pi_apply n).comp measurable_snd)
  rw [splitContinuousCouplingKernel, Kernel.map_apply _
    (measurable_gluedSplitSegmentSample Δ hΔ)]
  rw [integral_map (measurable_gluedSplitSegmentSample Δ hΔ).aemeasurable
      (hHm.fun_mul hbit).aestronglyMeasurable,
    integral_map (measurable_gluedSplitSegmentSample Δ hΔ).aemeasurable
      hHm.aestronglyMeasurable]
  have hind : IndepFun (fun s => H (gluedSplitSegmentSample Δ hΔ s))
      (fun s : ℕ → SplitSegmentState d => (s n).2.2)
      (splitSegmentSequenceKernel Δ δ R i hδ₀ hδ₁ hR P hminor a) := by
    cases n with
    | zero =>
      let z₀ : CoupledSample d := (⟨fun _ => a.1, continuous_const⟩, fun _ => false)
      have hconst : (fun _ : ℕ → SplitSegmentState d => H z₀) =ᵐ[
          splitSegmentSequenceKernel Δ δ R i hδ₀ hδ₁ hR P hminor a]
          fun s => H (gluedSplitSegmentSample Δ hΔ s) := by
        filter_upwards [ae_splitSegmentSequenceKernel_endpoints Δ δ R i
          hδ₀ hδ₁ hR P hminor hstart a] with s hs
        rw [← finiteHistory_test_stopped Δ 0 H hH (gluedSplitSegmentSample Δ hΔ s)]
        congr 1
        apply Prod.ext
        · apply ContinuousMap.ext
          intro t
          simp only [z₀, stoppedHistorySample, gluedSplitSegmentSample, Nat.cast_zero,
            zero_mul, min_eq_right (zero_le (a := t)), ContinuousMap.coe_mk]
          rw [glueSplitSegments_eq_sum Δ hΔ _ 0 0 (by simp)]
          simpa only [Finset.range_zero, Finset.sum_empty, add_zero] using hs.1.symm
        · funext k
          simp only [z₀, stoppedHistorySample, Nat.not_lt_zero, if_false]
      exact (indepFun_const_left (H z₀)
        (fun s : ℕ → SplitSegmentState d => (s 0).2.2)).congr hconst Filter.EventuallyEq.rfl
    | succ n =>
      exact indepFun_gluedSplitSegmentSample_past_coin Δ hΔ δ R i hδ₀ hδ₁ hR P hminor a n H hH
  have hind' := hind.comp measurable_id hcoin
  have hfactor := hind'.integral_fun_mul_eq_mul_integral
    (hHm.comp (measurable_gluedSplitSegmentSample Δ hΔ)).aestronglyMeasurable
    (hcoin.comp (measurable_pi_apply n).snd.snd).aestronglyMeasurable
  dsimp only [Function.comp_def, id_eq] at hfactor
  change (∫ s, H (gluedSplitSegmentSample Δ hΔ s) *
      (if (s n).2.2 = true then (1 : ℝ) else 0) ∂_) = _ at hfactor ⊢
  rw [hfactor, integral_splitSegmentSequenceKernel_coin Δ δ R i hδ₀ hδ₁ hR P hminor a n,
    mul_comm]

/-- The pointwise construction supplies both origin and product-a.e. fresh-bit clauses. -/
theorem hasFreshBits_splitContinuousCouplingKernel (Q : Measure (FieldPair d))
    (hstart : ∀ a, ∀ᵐ γ ∂P a, γ 0 = a.1) :
    HasFreshBits Q Δ δ (splitContinuousCouplingKernel Δ hΔ δ R i hδ₀ hδ₁ hR P hminor) := by
  constructor
  · exact Filter.Eventually.of_forall (fun ω =>
      freshBitsAt_splitContinuousCouplingKernel Δ hΔ δ R i hδ₀ hδ₁ hR P hminor hstart (0, ω))
  · exact Filter.Eventually.of_forall (fun a =>
      freshBitsAt_splitContinuousCouplingKernel Δ hΔ δ R i hδ₀ hδ₁ hR P hminor hstart a)

end EinsteinFull.Regeneration
