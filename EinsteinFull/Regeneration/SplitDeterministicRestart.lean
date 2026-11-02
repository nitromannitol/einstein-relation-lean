import EinsteinFull.Regeneration.SplitSequenceRestart
import EinsteinFull.Regeneration.SplitGluingShift
import EinsteinFull.Regeneration.SplitFreshBits
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

/-!
# Deterministic restart of the actual continuous split coupling

The complete finite history includes its closed endpoint and every earlier
coin. The future is the joint path and entire remaining coin sequence.
-/

open MeasureTheory ProbabilityTheory Preorder
open scoped NNReal ENNReal
noncomputable section
namespace EinsteinFull.Regeneration
open EinsteinRelation EinsteinRelation.Regeneration EinsteinRelation.Probability

variable {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ) (δ R : ℝ) (i : Fin d)
  (hδ₀ : 0 < δ) (hδ₁ : δ < 1) (hR : 0 < R)
  (P : QuenchedPathLaws d) [IsMarkovKernel P]
  (hminor : ∀ ω : FieldPair d,
    EinsteinFull.External.Source.GMP.HasSourceMinorization
      (fun x => P (x, ω)) Δ δ R i)

private theorem integral_splitSequence_prefix_future (a : Vec d × FieldPair d) (n : ℕ)
    (F : ((j : Finset.Iic n) → SplitSegmentState d) → ℝ)
    (Ψ : (ℕ → SplitSegmentState d) → ℝ)
    (hF : Measurable F) (hFb : BoundedRealTest F)
    (hΨ : Measurable Ψ) (hΨb : BoundedRealTest Ψ) :
    (∫ s, F (frestrictLe n s) * Ψ (sequenceShift (n + 1) s)
      ∂splitSegmentSequenceKernel Δ δ R i hδ₀ hδ₁ hR P hminor a) =
    ∫ s, F (frestrictLe n s) *
      (∫ s', Ψ s' ∂splitSegmentSequenceKernel Δ δ R i hδ₀ hδ₁ hR P hminor
        (splitPrefixEndpoint Δ n (frestrictLe n s)))
      ∂splitSegmentSequenceKernel Δ δ R i hδ₀ hδ₁ hR P hminor a := by
  let μ := splitSegmentSequenceKernel Δ δ R i hδ₀ hδ₁ hR P hminor a
  let L := (splitSegmentSequenceKernel Δ δ R i hδ₀ hδ₁ hR P hminor).comap
    (splitPrefixEndpoint Δ n) (measurable_splitPrefixEndpoint Δ n)
  have hjoint : μ.map (fun s => (frestrictLe n s, sequenceShift (n + 1) s)) =
      (μ.map (frestrictLe n)).compProd L := by
    have h := congrArg (fun κ => κ a)
      (splitSegmentSequenceKernel_prefix_future_joint Δ δ R i hδ₀ hδ₁ hR P hminor n)

    rw [Kernel.map_apply _ ((measurable_frestrictLe n).prodMk (measurable_sequenceShift _)), Kernel.comp_apply,
      Kernel.map_apply _ (measurable_frestrictLe _), ← Measure.compProd_eq_comp_prod] at h
    exact h
  have htest : Measurable (fun q : ((j : Finset.Iic n) → SplitSegmentState d) ×
      (ℕ → SplitSegmentState d) => F q.1 * Ψ q.2) :=
    (hF.comp measurable_fst).mul (hΨ.comp measurable_snd)
  obtain ⟨C, hC⟩ := hFb
  obtain ⟨D, hD⟩ := hΨb
  have hint : Integrable (fun q => F q.1 * Ψ q.2) ((μ.map (frestrictLe n)).compProd L) :=
    Integrable.of_bound htest.aestronglyMeasurable (|C| * |D|)
      (Filter.Eventually.of_forall fun q => by
        rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
        exact mul_le_mul ((hC _).trans (le_abs_self _)) ((hD _).trans (le_abs_self _))
          (abs_nonneg _) (abs_nonneg _))
  have h := congrArg (fun ν => ∫ q, F q.1 * Ψ q.2 ∂ν) hjoint

  rw [integral_map ((measurable_frestrictLe n).prodMk (measurable_sequenceShift _)).aemeasurable htest.aestronglyMeasurable,
    Measure.integral_compProd hint] at h
  simp only [integral_const_mul] at h
  have hinner : StronglyMeasurable (fun u => ∫ s', Ψ s' ∂L u) :=
    hΨ.stronglyMeasurable.integral_kernel
  rw [integral_map (measurable_frestrictLe n).aemeasurable
    (hF.stronglyMeasurable.mul hinner).aestronglyMeasurable] at h
  exact h

/-- Restart at a positive grid time retains the exact continuous past and coins. -/
theorem deterministicRestartAt_splitContinuousCouplingKernel_succ
    (hstart : ∀ a, ∀ᵐ γ ∂P a, γ 0 = a.1) (a : Vec d × FieldPair d) (n : ℕ)
    (H Φ : CoupledSample d → ℝ)
    (hH : @Measurable (CoupledSample d) ℝ (finiteHistorySigma Δ (n + 1)) inferInstance H)
    (hbH : BoundedRealTest H) (hΦ : Measurable Φ) (hbΦ : BoundedRealTest Φ) :
    (∫ z, H z * Φ (sampleTimeShift Δ z ((n + 1 : ℕ) * Δ))
      ∂splitContinuousCouplingKernel Δ hΔ δ R i hδ₀ hδ₁ hR P hminor a) =
      ∫ z, H z * (∫ z', Φ z'
        ∂splitContinuousCouplingKernel Δ hΔ δ R i hδ₀ hδ₁ hR P hminor
          (z.1 ((n + 1 : ℕ) * Δ), a.2))
        ∂splitContinuousCouplingKernel Δ hΔ δ R i hδ₀ hδ₁ hR P hminor a := by
  let F : ((j : Finset.Iic n) → SplitSegmentState d) → ℝ := fun u =>
    H (gluedSplitSegmentSample Δ hΔ (extendSplitSegmentPrefix n u))
  let Ψ : (ℕ → SplitSegmentState d) → ℝ := Φ ∘ gluedSplitSegmentSample Δ hΔ
  have hHm : Measurable H := hH.mono (finiteHistorySigma_le Δ (n + 1)) le_rfl
  have hF : Measurable F := hHm.comp ((measurable_gluedSplitSegmentSample Δ hΔ).comp
    (measurable_extendSplitSegmentPrefix n))
  have hΨ : Measurable Ψ := hΦ.comp (measurable_gluedSplitSegmentSample Δ hΔ)
  have hFb : BoundedRealTest F := ⟨hbH.choose, fun _ => hbH.choose_spec _⟩
  have hΨb : BoundedRealTest Ψ := ⟨hbΦ.choose, fun _ => hbΦ.choose_spec _⟩
  have hFpast (s : ℕ → SplitSegmentState d) :
      F (frestrictLe n s) = H (gluedSplitSegmentSample Δ hΔ s) := by
    dsimp only [F]
    calc
      H (gluedSplitSegmentSample Δ hΔ (extendSplitSegmentPrefix n (frestrictLe n s))) =
          H (stoppedHistorySample Δ (n + 1) (gluedSplitSegmentSample Δ hΔ
            (extendSplitSegmentPrefix n (frestrictLe n s)))) :=
        (finiteHistory_test_stopped Δ (n + 1) H hH _).symm
      _ = H (stoppedHistorySample Δ (n + 1) (gluedSplitSegmentSample Δ hΔ s)) :=
        congrArg H (stoppedHistory_gluedSplitSegmentSample_prefix Δ hΔ n s).symm
      _ = H (gluedSplitSegmentSample Δ hΔ s) := finiteHistory_test_stopped Δ (n + 1) H hH _
  have hinner : Measurable (fun a => ∫ z', Φ z'
      ∂splitContinuousCouplingKernel Δ hΔ δ R i hδ₀ hδ₁ hR P hminor a) :=
    hΦ.stronglyMeasurable.integral_kernel.measurable
  have hshift : Measurable (fun z : CoupledSample d =>
      sampleTimeShift Δ z ((n + 1 : ℕ) * Δ)) :=
    (measurable_sampleTimeShift Δ).comp (measurable_const.prodMk measurable_id)
  have hleft : Measurable (fun z : CoupledSample d =>
      H z * Φ (sampleTimeShift Δ z ((n + 1 : ℕ) * Δ))) := hHm.mul (hΦ.comp hshift)
  have hright : Measurable (fun z : CoupledSample d => H z * (∫ z', Φ z'
      ∂splitContinuousCouplingKernel Δ hΔ δ R i hδ₀ hδ₁ hR P hminor
        (z.1 ((n + 1 : ℕ) * Δ), a.2))) :=
    hHm.mul (hinner.comp (((continuous_eval_const _).measurable.comp measurable_fst).prodMk
      measurable_const))
  have hmap : splitContinuousCouplingKernel Δ hΔ δ R i hδ₀ hδ₁ hR P hminor a =
      (splitSegmentSequenceKernel Δ δ R i hδ₀ hδ₁ hR P hminor a).map
        (gluedSplitSegmentSample Δ hΔ) :=
    Kernel.map_apply _ (measurable_gluedSplitSegmentSample Δ hΔ) a
  rw [hmap]
  rw [integral_map (measurable_gluedSplitSegmentSample Δ hΔ).aemeasurable
      hleft.aestronglyMeasurable,
    integral_map (measurable_gluedSplitSegmentSample Δ hΔ).aemeasurable
      hright.aestronglyMeasurable]
  have h := integral_splitSequence_prefix_future Δ δ R i hδ₀ hδ₁ hR P hminor a n F Ψ
    hF hFb hΨ hΨb
  refine (integral_congr_ae ?_).trans (h.trans (integral_congr_ae ?_))
  · filter_upwards [ae_splitSegmentSequenceKernel_endpoints Δ δ R i hδ₀ hδ₁ hR P hminor
      hstart a] with s hs
    rw [hFpast, sampleTimeShift_gluedSplitSegmentSample Δ hΔ s hs.2]
    rfl
  · filter_upwards [ae_splitSegmentSequenceKernel_endpoints Δ δ R i hδ₀ hδ₁ hR P hminor
      hstart a, ae_splitSegmentSequenceKernel_environment Δ δ R i hδ₀ hδ₁ hR P hminor a]
      with s hs henv
    rw [hFpast]
    congr 1
    have hend : (gluedSplitSegmentSample Δ hΔ s).1 ((n + 1 : ℕ) * Δ) = (s n).2.1 Δ := by
      have ht : (n + 1 : ℕ) * Δ = n * Δ + Δ := by push_cast; ring
      rw [ht]
      exact glueSplitSegments_interval Δ hΔ (fun k => (s k).2.1) hs.2 n Δ le_rfl
    rw [hend]
    change (∫ s', Ψ s' ∂splitSegmentSequenceKernel Δ δ R i hδ₀ hδ₁ hR P hminor
      ((s n).2.1 Δ, (s n).1)) = _
    rw [henv n, splitContinuousCouplingKernel, Kernel.map_apply _
      (measurable_gluedSplitSegmentSample Δ hΔ),
      integral_map (measurable_gluedSplitSegmentSample Δ hΔ).aemeasurable hΦ.aestronglyMeasurable]
    rfl

/-- The same constructed joint kernel restarts at every deterministic grid time,
including time zero, against the literal closed finite-history sigma algebra. -/
theorem deterministicRestartAt_splitContinuousCouplingKernel
    (hstart : ∀ a, ∀ᵐ γ ∂P a, γ 0 = a.1) (a : Vec d × FieldPair d) :
    DeterministicRestartAt Δ
      (splitContinuousCouplingKernel Δ hΔ δ R i hδ₀ hδ₁ hR P hminor) a := by
  intro n H Φ hH hbH hΦ hbΦ
  cases n with
  | succ n =>
    exact deterministicRestartAt_splitContinuousCouplingKernel_succ Δ hΔ δ R i
      hδ₀ hδ₁ hR P hminor hstart a n H Φ hH hbH hΦ hbΦ
  | zero =>
    let K := splitContinuousCouplingKernel Δ hΔ δ R i hδ₀ hδ₁ hR P hminor
    let z₀ : CoupledSample d := (⟨fun _ => a.1, continuous_const⟩, fun _ => false)
    have hconst : ∀ᵐ z ∂K a, H z = H z₀ := by
      filter_upwards [ae_splitContinuousCouplingKernel_start Δ hΔ δ R i hδ₀ hδ₁ hR P hminor
        hstart a] with z hz
      rw [← finiteHistory_test_stopped Δ 0 H hH z,
        ← finiteHistory_test_stopped Δ 0 H hH z₀]
      congr 1
      apply Prod.ext
      · apply ContinuousMap.ext
        intro t
        simpa only [stoppedHistorySample, Nat.cast_zero, zero_mul, min_eq_right (zero_le (a := t)),
          z₀, ContinuousMap.coe_mk] using hz
      · funext k
        simp only [stoppedHistorySample, Nat.not_lt_zero, if_false]
    have hshift (z : CoupledSample d) : sampleTimeShift Δ z 0 = z := by
      apply Prod.ext
      · apply ContinuousMap.ext
        intro t
        simp only [sampleTimeShift, pathTimeShift, ContinuousMap.coe_mk, zero_add]
      · funext k
        simp only [sampleTimeShift, gridIndex, NNReal.coe_zero, zero_div, Nat.floor_zero, zero_add]
    simp only [Nat.cast_zero, zero_mul, hshift]
    change (∫ z, H z * Φ z ∂K a) =
      ∫ z, H z * (∫ z', Φ z' ∂K (z.1 0, a.2)) ∂K a
    calc
      (∫ z, H z * Φ z ∂K a) = ∫ z, H z₀ * Φ z ∂K a := by
        apply integral_congr_ae
        filter_upwards [hconst] with z hz
        rw [hz]
      _ = H z₀ * ∫ z, Φ z ∂K a := integral_const_mul _ _
      _ = ∫ z, H z₀ * (∫ z', Φ z' ∂K a) ∂K a := by simp
      _ = ∫ z, H z * (∫ z', Φ z' ∂K (z.1 0, a.2)) ∂K a := by
        apply integral_congr_ae
        filter_upwards [hconst, ae_splitContinuousCouplingKernel_start Δ hΔ δ R i
          hδ₀ hδ₁ hR P hminor hstart a] with z hz hpos
        rw [hz, hpos]

/-- Pointwise coupled restart supplies both the origin and product-a.e. clauses. -/
theorem hasDeterministicRestart_splitContinuousCouplingKernel
    (hstart : ∀ a, ∀ᵐ γ ∂P a, γ 0 = a.1) (Q : Measure (FieldPair d)) :
    HasDeterministicRestart Q Δ
      (splitContinuousCouplingKernel Δ hΔ δ R i hδ₀ hδ₁ hR P hminor) :=
  ⟨Filter.Eventually.of_forall (fun _ => deterministicRestartAt_splitContinuousCouplingKernel
    Δ hΔ δ R i hδ₀ hδ₁ hR P hminor hstart _),
   Filter.Eventually.of_forall (fun _ => deterministicRestartAt_splitContinuousCouplingKernel
    Δ hΔ δ R i hδ₀ hδ₁ hR P hminor hstart _)⟩

end EinsteinFull.Regeneration
