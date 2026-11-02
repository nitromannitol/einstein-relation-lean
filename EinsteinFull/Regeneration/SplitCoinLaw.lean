import EinsteinFull.Regeneration.SplitContinuousKernel
import Mathlib.Probability.Independence.InfinitePi

/-!
# The actual split sequence has the Bernoulli product coin law

Every canonical segment transition has the same literal Bernoulli coin marginal.
The exact prefix/next-segment law therefore factors the next coin from all earlier
sampled segments. Finite-cylinder induction identifies the entire coin process
with the infinite product measure. Mapping to continuous paths preserves it.
These conclusions are conditional on the actual source minorization used to
construct the segment kernel; no process identification or locality is assumed.
-/

open MeasureTheory ProbabilityTheory Preorder
open scoped NNReal ENNReal
noncomputable section
namespace EinsteinFull.Regeneration
open EinsteinRelation EinsteinRelation.Regeneration

/-- The literal source Bernoulli law, with success mass `δ`. -/
def splitCoinLaw (δ : ℝ) : Measure Bool :=
  ENNReal.ofReal δ • Measure.dirac true + ENNReal.ofReal (1 - δ) • Measure.dirac false

theorem splitCoinLaw_singleton (δ : ℝ) (b : Bool) :
    splitCoinLaw δ {b} = ENNReal.ofReal (if b then δ else 1 - δ) := by
  cases b <;> simp [splitCoinLaw]

theorem isProbabilityMeasure_splitCoinLaw (δ : ℝ) (hδ₀ : 0 ≤ δ) (hδ₁ : δ ≤ 1) :
    IsProbabilityMeasure (splitCoinLaw δ) := by
  constructor
  simp only [splitCoinLaw, Measure.add_apply, Measure.smul_apply, measure_univ,
    smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add hδ₀ (sub_nonneg.mpr hδ₁), add_sub_cancel, ENNReal.ofReal_one]

variable {d : ℕ} (Δ : ℝ≥0) (δ R : ℝ) (i : Fin d)
  (hδ₀ : 0 < δ) (hδ₁ : δ < 1) (hR : 0 < R)
  (P : QuenchedPathLaws d) [IsMarkovKernel P]
  (hminor : ∀ ω : FieldPair d,
    EinsteinFull.External.Source.GMP.HasSourceMinorization
      (fun x => P (x, ω)) Δ δ R i)

include hδ₁

/-- The actual one-interval split coin has the literal Bernoulli law. -/
theorem map_oneIntervalSplitKernel_coin :
    (oneIntervalSplitKernel Δ δ R i hδ₀.le hR P hminor).map Prod.snd =
      Kernel.const (Vec d × FieldPair d) (splitCoinLaw δ) := by
  ext a : 1
  rw [Kernel.map_apply _ measurable_snd, Kernel.const_apply]
  apply Measure.ext_of_singleton
  intro b
  rw [Measure.map_apply measurable_snd (measurableSet_singleton b), splitCoinLaw_singleton]
  exact oneIntervalSplitKernel_coin Δ δ R i hδ₀ hδ₁ hR P hminor a b

/-- Retaining the environment does not alter the actual first coin law. -/
theorem map_splitInitialStateKernel_coin :
    (splitInitialStateKernel Δ δ R i hδ₀ hR P hminor).map (fun u => u.2.2) =
      Kernel.const (Vec d × FieldPair d) (splitCoinLaw δ) := by
  letI := isMarkovKernel_oneIntervalSplitKernel Δ δ R i hδ₀ hδ₁ hR P hminor
  change (splitInitialStateKernel Δ δ R i hδ₀ hR P hminor).map (Prod.snd ∘ Prod.snd) = _
  rw [Kernel.map_comp_right _ measurable_snd measurable_snd]
  rw [← Kernel.snd_eq (splitInitialStateKernel Δ δ R i hδ₀ hR P hminor),
    splitInitialStateKernel, Kernel.snd_prod,
    map_oneIntervalSplitKernel_coin Δ δ R i hδ₀ hδ₁ hR P hminor]

/-- The next coin has the same Bernoulli law at every actual sampled prefix. -/
theorem map_splitSegmentHistoryKernel_coin (n : ℕ) :
    (splitSegmentHistoryKernel Δ δ R i hδ₀ hR P hminor n).map (fun u => u.2.2) =
      Kernel.const ((j : Finset.Iic n) → SplitSegmentState d) (splitCoinLaw δ) := by
  ext u : 1
  rw [Kernel.map_apply _ (by fun_prop)]
  change (splitInitialStateKernel Δ δ R i hδ₀ hR P hminor
    ((u ⟨n, Finset.mem_Iic.mpr le_rfl⟩).2.1 Δ, (u ⟨n, Finset.mem_Iic.mpr le_rfl⟩).1)).map
      (fun u => u.2.2) = splitCoinLaw δ
  rw [← Kernel.map_apply _ (by fun_prop), map_splitInitialStateKernel_coin (hδ₁ := hδ₁)]
  rfl

/-- The actual prefix and next coin have their product joint law. -/
theorem splitSegmentSequenceKernel_prefix_coin (n : ℕ) :
    (splitSegmentSequenceKernel Δ δ R i hδ₀ hδ₁ hR P hminor).map
        (fun s => (frestrictLe n s, (s (n + 1)).2.2)) =
      (splitSegmentSequenceKernel Δ δ R i hδ₀ hδ₁ hR P hminor).map (frestrictLe n) ×ₖ
        Kernel.const (Vec d × FieldPair d) (splitCoinLaw δ) := by
  letI := isMarkovKernel_splitSegmentHistoryKernel Δ δ R i hδ₀ hδ₁ hR P hminor n
  letI := isProbabilityMeasure_splitCoinLaw δ hδ₀.le hδ₁.le
  have h := congrArg (fun κ => κ.map (Prod.map id (fun u : SplitSegmentState d => u.2.2)))
    (splitSegmentSequenceKernel_prefix_next Δ δ R i hδ₀ hδ₁ hR P hminor n)
  rw [← Kernel.map_comp_right _ (by fun_prop) (by fun_prop)] at h
  rw [Kernel.map_comp, ← Kernel.map_prod_map _ _ measurable_id (by fun_prop),
    Kernel.map_id, map_splitSegmentHistoryKernel_coin (hδ₁ := hδ₁),
    Kernel.prod_const_comp, Kernel.id_comp] at h
  exact h

/-- Every coin coordinate has the same literal Bernoulli marginal. -/
theorem map_splitSegmentSequenceKernel_coin (n : ℕ) :
    (splitSegmentSequenceKernel Δ δ R i hδ₀ hδ₁ hR P hminor).map
        (fun s => (s n).2.2) = Kernel.const (Vec d × FieldPair d) (splitCoinLaw δ) := by
  cases n with
  | zero =>
    change (splitSegmentSequenceKernel Δ δ R i hδ₀ hδ₁ hR P hminor).map
      ((fun u : SplitSegmentState d => u.2.2) ∘ (fun s => s 0)) = _
    rw [Kernel.map_comp_right _ (measurable_pi_apply 0) (by fun_prop),
      map_splitSegmentSequenceKernel_zero, map_splitInitialStateKernel_coin (hδ₁ := hδ₁)]
  | succ n =>
    letI := Kernel.IsMarkovKernel.map
      (splitSegmentSequenceKernel Δ δ R i hδ₀ hδ₁ hR P hminor)
      (measurable_frestrictLe n)
    letI := isProbabilityMeasure_splitCoinLaw δ hδ₀.le hδ₁.le
    have h := congrArg (fun κ => κ.map Prod.snd)
      (splitSegmentSequenceKernel_prefix_coin Δ δ R i hδ₀ hδ₁ hR P hminor n)
    rw [← Kernel.map_comp_right _ (by fun_prop) measurable_snd] at h
    rw [← Kernel.snd_eq ((splitSegmentSequenceKernel Δ δ R i hδ₀ hδ₁ hR P hminor).map
      (frestrictLe n) ×ₖ Kernel.const (Vec d × FieldPair d) (splitCoinLaw δ)),
      Kernel.snd_prod] at h
    exact h

/-- Each future coin is independent of the entire previously sampled segment prefix. -/
theorem indepFun_splitSegmentSequenceKernel_prefix_coin (a : Vec d × FieldPair d) (n : ℕ) :
    IndepFun (frestrictLe n) (fun s : ℕ → SplitSegmentState d => (s (n + 1)).2.2)
      (splitSegmentSequenceKernel Δ δ R i hδ₀ hδ₁ hR P hminor a) := by
  rw [indepFun_iff_map_prod_eq_prod_map_map
    (measurable_frestrictLe n).aemeasurable
      ((measurable_pi_apply (n + 1)).snd.snd.aemeasurable)]
  have h := congrArg (fun κ => κ a)
    (splitSegmentSequenceKernel_prefix_coin Δ δ R i hδ₀ hδ₁ hR P hminor n)
  rw [Kernel.map_apply _ (by fun_prop), Kernel.prod_apply,
    Kernel.map_apply _ (measurable_frestrictLe n), Kernel.const_apply] at h
  have hm := congrArg (fun κ => κ a)
    (map_splitSegmentSequenceKernel_coin Δ δ R i hδ₀ hδ₁ hR P hminor (n + 1))
  rw [Kernel.map_apply _ (by fun_prop), Kernel.const_apply] at hm
  rw [hm]
  exact h

/-- The probability of an arbitrary finite coin cylinder is its Bernoulli product. -/
theorem splitSegmentSequenceKernel_coin_cylinder (a : Vec d × FieldPair d)
    (S : Finset ℕ) (sets : ℕ → Set Bool) (hsets : ∀ n, MeasurableSet (sets n)) :
    splitSegmentSequenceKernel Δ δ R i hδ₀ hδ₁ hR P hminor a
      (⋂ k ∈ S, (fun s : ℕ → SplitSegmentState d => (s k).2.2) ⁻¹' sets k) = ∏ k ∈ S, splitCoinLaw δ (sets k) := by
  classical
  have hm (n : ℕ) :
      splitSegmentSequenceKernel Δ δ R i hδ₀ hδ₁ hR P hminor a
        ((fun s : ℕ → SplitSegmentState d => (s n).2.2) ⁻¹' sets n) = splitCoinLaw δ (sets n) := by
    have h := congrArg (fun κ => κ a (sets n))
      (map_splitSegmentSequenceKernel_coin Δ δ R i hδ₀ hδ₁ hR P hminor n)
    rw [Kernel.map_apply _ (by fun_prop), Kernel.const_apply,
      Measure.map_apply (by fun_prop) (hsets n)] at h
    exact h
  refine Finset.induction_on_max S (by simp) ?_
  intro k S hmax ih
  have hk : k ∉ S := fun hk => (lt_irrefl k) (hmax k hk)
  rw [Finset.prod_insert hk]
  cases k with
  | zero =>
    have hS : S = ∅ := Finset.eq_empty_iff_forall_notMem.mpr
      (fun k hk => Nat.not_lt_zero k (hmax k hk))
    simpa [hS] using hm 0
  | succ n =>
    let A : Set ((j : Finset.Iic n) → SplitSegmentState d) :=
      ⋂ k : S, {u | (u ⟨k, Finset.mem_Iic.mpr (Nat.le_of_lt_succ (hmax k k.2))⟩).2.2 ∈ sets k}
    have hA : MeasurableSet A := by
      exact MeasurableSet.iInter (fun k => (hsets k).preimage (by fun_prop))
    have hpre : (frestrictLe n : (ℕ → SplitSegmentState d) → _) ⁻¹' A = ⋂ k ∈ S, (fun s : ℕ → SplitSegmentState d => (s k).2.2) ⁻¹' sets k := by
      ext s
      simp [A]
    have hind := (indepFun_splitSegmentSequenceKernel_prefix_coin
      Δ δ R i hδ₀ hδ₁ hR P hminor a n).measure_inter_preimage_eq_mul A (sets (n + 1))
        hA (hsets (n + 1))
    rw [hpre, hm, ih] at hind
    simpa only [Finset.set_biInter_insert, Set.inter_comm, mul_comm] using hind

/-- All coin coordinates of the actual iterated split law are independent. -/
theorem iIndepFun_splitSegmentSequenceKernel_coins (a : Vec d × FieldPair d) :
    iIndepFun (fun n (s : ℕ → SplitSegmentState d) => (s n).2.2)
      (splitSegmentSequenceKernel Δ δ R i hδ₀ hδ₁ hR P hminor a) := by
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
  intro S sets hsets
  have hsets' : ∀ n, MeasurableSet (sets n) := fun _ => MeasurableSet.of_discrete
  rw [splitSegmentSequenceKernel_coin_cylinder Δ δ R i hδ₀ hδ₁ hR P hminor a S sets hsets']
  apply Finset.prod_congr rfl
  intro n hn
  have h := congrArg (fun κ => κ a (sets n))
    (map_splitSegmentSequenceKernel_coin Δ δ R i hδ₀ hδ₁ hR P hminor n)
  rw [Kernel.map_apply _ (by fun_prop), Kernel.const_apply,
    Measure.map_apply (by fun_prop) (hsets' n)] at h
  exact h.symm

/-- The entire actual coin sequence has the Bernoulli product law. -/
theorem map_splitSegmentSequenceKernel_coins :
    (splitSegmentSequenceKernel Δ δ R i hδ₀ hδ₁ hR P hminor).map
      (fun s n => (s n).2.2) =
      Kernel.const (Vec d × FieldPair d) (Measure.infinitePi (fun _ : ℕ => splitCoinLaw δ)) := by
  ext a : 1
  rw [Kernel.map_apply _ (by fun_prop), Kernel.const_apply,
    (iIndepFun_iff_map_fun_eq_infinitePi_map (by fun_prop)).mp
      (iIndepFun_splitSegmentSequenceKernel_coins Δ δ R i hδ₀ hδ₁ hR P hminor a)]
  congr 1
  funext n
  have h := congrArg (fun κ => κ a)
    (map_splitSegmentSequenceKernel_coin Δ δ R i hδ₀ hδ₁ hR P hminor n)
  rw [Kernel.map_apply _ (by fun_prop), Kernel.const_apply] at h
  exact h

/-- Gluing the sampled segments preserves the Bernoulli product law of the coins. -/
theorem map_splitContinuousCouplingKernel_coin_product (hΔ : 0 < Δ) :
    (splitContinuousCouplingKernel Δ hΔ δ R i hδ₀ hδ₁ hR P hminor).map Prod.snd =
      Kernel.const (Vec d × FieldPair d) (Measure.infinitePi (fun _ : ℕ => splitCoinLaw δ)) := by
  rw [map_splitContinuousCouplingKernel_coins, map_splitSegmentSequenceKernel_coins]

end EinsteinFull.Regeneration
