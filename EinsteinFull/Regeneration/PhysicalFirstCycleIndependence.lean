import EinsteinFull.Regeneration.PhysicalEndpointFactorization
import EinsteinFull.Regeneration.C1ConditionIterateSupport
import EinsteinFull.Regeneration.VelocityFromRecords
import EinsteinFull.PhysicalRegeneration.Blueprint.Foundation.node_app_u3A_factorization_u23_coupling_u2D_scope
import EinsteinRelation.Regeneration.NoBacktrackingPrefix

/-!
# Independence of the first cycle and the next record

GMP 2012, Theorem 5.6, and Shen 2003, Theorem 2.5: under the law conditioned on no return, the
duration and the displacement of the first regeneration cycle are independent of the record
at the first regeneration time. On a slice `τ₁ = (m + 1)λ⁻²` the cycle is a function of the
displacement up to `mλ⁻²` and of the displacement over the last bridge; the slice factorization
with the bridge displacement gives the product rule for these two displacements and the record,
and the slices cover the conditioned law.
-/

open MeasureTheory ProbabilityTheory EinsteinRelation EinsteinRelation.Regeneration
open scoped NNReal ENNReal

attribute [local instance 2000] EinsteinRelation.instMeasurableSpaceMat

namespace EinsteinFull.Blueprint

/-- The cycle of the record at time zero is the first regeneration time and the displacement of
the path at that time. -/
theorem recordCycle_iteratedRecord_zero {d : ℕ} (Δ : ℝ≥0) (lam R : ℝ) (i : Fin d)
    (q : FieldPair d × CoupledSample d) :
    EinsteinFull.Regeneration.recordCycle Δ lam R i (iteratedRecord Δ lam R i 0 q) =
      (((firstRegenerationTime Δ lam R q.2 i).toNNReal : ℝ),
        q.2.1 (firstRegenerationTime Δ lam R q.2 i).toNNReal - q.2.1 0) := by
  have h0 : Regeneration.regenerationTime Δ lam R q.2 i 0 = 0 := rfl
  have h1 : firstRegenerationTime Δ lam R
      (recordSample (iteratedRecord Δ lam R i 0 q)) i = firstRegenerationTime Δ lam R q.2 i := by
    rw [EinsteinFull.Regeneration.firstRegenerationTime_iteratedRecord, h0,
      ENNReal.toNNReal_zero, sampleTimeShift_zero]
  refine Prod.ext ?_ ?_
  · simp only [EinsteinFull.Regeneration.recordCycle,
      EinsteinFull.Regeneration.recordDuration, h1]
  · funext j
    simp only [EinsteinFull.Regeneration.recordCycle,
      EinsteinFull.Regeneration.recordDisplacement]
    rw [h1]
    simp only [iteratedRecord, futureRecord, h0, ENNReal.toNNReal_zero, zero_add,
      ContinuousMap.coe_mk, Pi.sub_apply, sub_self, sub_zero]

open Classical in
/-- The slice factorization with the last bridge displacement under the law conditioned on no
return: on the slice, no return is the no-return event of the history through `mλ⁻²`. -/
theorem physical_slice_factorization_endpoint_cond
    (hpast : node_app_u3A_factorization_u23_past_u2D_kernelStmt_phys)
    (hfuture : node_app_u3A_factorization_u23_future_u2D_kernelStmt_phys)
    (hslices : node_app_u3A_factorization_u23_slicesStmt_phys)
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1) (l δ : ℝ)
    (hl : 0 < l) (hsep : r₀ < 2 * l) (hδ₀ : 0 < δ) (hδ₁ : δ < 1)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : IsRegenerationCouplingPhys hd Q lam l δ h₀.le h₁ P K)
    (hD : annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam)) ≠ 0)
    (m : ℕ) (hm : 1 ≤ m) (H : CoupledSample d → ℝ)
    (hH : Measurable[finiteHistorySigma (Renewal.regenDelta lam) m] H)
    (hbH : BoundedRealTest H) (hH0 : ∀ z, 0 ≤ H z)
    (g : Vec d → ℝ) (hg : Measurable g) (hbg : BoundedRealTest g) (hg0 : ∀ y, 0 ≤ g y)
    (Φ : FutureState d (Renewal.forceCoord hd) (l / lam) → ℝ)
    (hΦ : Measurable Φ) (hbΦ : BoundedRealTest Φ) (hΦ0 : ∀ r, 0 ≤ Φ r) :
    (∫ q in {q : FieldPair d × CoupledSample d |
        firstRegenerationTime (Renewal.regenDelta lam) lam (l / lam) q.2 (Renewal.forceCoord hd) =
          ((((m + 1 : ℕ) : ℝ≥0) * Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)},
      H q.2 * g (q.2.1 (((m + 1 : ℕ) : ℝ≥0) * Renewal.regenDelta lam) -
        q.2.1 ((m : ℝ≥0) * Renewal.regenDelta lam)) *
        Φ (iteratedRecord (Renewal.regenDelta lam) lam (l / lam) (Renewal.forceCoord hd) 1 q)
        ∂regenerationConditionedLaw hd Q lam l K hK.1 hD) =
      (∫ q in {q : FieldPair d × CoupledSample d |
        firstRegenerationTime (Renewal.regenDelta lam) lam (l / lam) q.2 (Renewal.forceCoord hd) =
          ((((m + 1 : ℕ) : ℝ≥0) * Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)},
        H q.2 * g (q.2.1 (((m + 1 : ℕ) : ℝ≥0) * Renewal.regenDelta lam) -
          q.2.1 ((m : ℝ≥0) * Renewal.regenDelta lam))
          ∂regenerationConditionedLaw hd Q lam l K hK.1 hD) *
        ∫ q, Φ (regenerationRecord hd lam l 0 q)
          ∂regenerationConditionedLaw hd Q lam l K hK.1 hD := by
  let E : Set (CoupledSample d) :=
    {z | ∀ t : ℝ≥0, t ≤ (m : ℝ≥0) * Renewal.regenDelta lam →
      -(l / lam) < z.1 t (Renewal.forceCoord hd) - z.1 0 (Renewal.forceCoord hd)}
  have hEm : MeasurableSet[finiteHistorySigma (Renewal.regenDelta lam) m] E :=
    measurableSet_noBacktracking_prefix _ m _ _
  have hsm : MeasurableSet {q : FieldPair d × CoupledSample d |
      firstRegenerationTime (Renewal.regenDelta lam) lam (l / lam) q.2 (Renewal.forceCoord hd) =
        ((((m + 1 : ℕ) : ℝ≥0) * Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)} :=
    ((measurable_firstRegenerationTime _ lam _ _).comp measurable_snd)
      (measurableSet_singleton _)
  have hdm : MeasurableSet (regenerationNoReturn hd (l / lam)) :=
    (measurableSet_NoBacktracking _ _).preimage measurable_snd.fst
  have hΔ : 0 < Renewal.regenDelta lam := EinsteinRelation.regenDelta_pos h₀
  have hbar := ae_noBacktracking_iff_prefix_on_firstRegenerationSlice Q.measure K hK.1
    _ hΔ lam (l / lam) h₀ (div_pos hl h₀) (Renewal.forceCoord hd) m hK.2.2.2.2.2.1
  have hDE : ∀ᵐ q ∂(annealedCoupledLaw Q.measure K).restrict
      {q : FieldPair d × CoupledSample d |
        firstRegenerationTime (Renewal.regenDelta lam) lam (l / lam) q.2
          (Renewal.forceCoord hd) =
          ((((m + 1 : ℕ) : ℝ≥0) * Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)},
      q ∈ regenerationNoReturn hd (l / lam) ↔ q ∈ Prod.snd ⁻¹' E := by
    filter_upwards [ae_restrict_of_ae hbar, ae_restrict_mem hsm] with q hq ht
    exact hq ht
  have hbEH : BoundedRealTest (E.indicator H) := by
    obtain ⟨C, hC⟩ := hbH
    refine ⟨max C 0, fun z => ?_⟩
    by_cases hz : z ∈ E
    · simpa only [Set.indicator_of_mem hz] using (hC z).trans (le_max_left C 0)
    · simpa only [Set.indicator_of_notMem hz, abs_zero] using le_max_right C 0
  have hEH0 : ∀ z, 0 ≤ E.indicator H z := fun z => Set.indicator_nonneg (fun z _ => hH0 z) z
  have hfac := physical_slice_factorization_endpoint hpast hfuture hslices hd Q lam h₀ h₁
    l δ hl hsep hδ₀ hδ₁ P K hK hD m hm (E.indicator H) (hH.indicator hEm) hbEH hEH0
    g hg hbg hg0 Φ hΦ hbΦ hΦ0
  apply EinsteinFull.Regeneration.conditional_slice_of_indicator
    (annealedCoupledLaw Q.measure K) (regenerationNoReturn hd (l / lam)) _ (Prod.snd ⁻¹' E)
    hdm hsm hDE
  have heq (q : FieldPair d × CoupledSample d) :
      (Prod.snd ⁻¹' E).indicator (fun q : FieldPair d × CoupledSample d =>
        H q.2 * g (q.2.1 (((m + 1 : ℕ) : ℝ≥0) * Renewal.regenDelta lam) -
          q.2.1 ((m : ℝ≥0) * Renewal.regenDelta lam)) *
        Φ (iteratedRecord (Renewal.regenDelta lam) lam (l / lam) (Renewal.forceCoord hd) 1 q)) q =
      E.indicator H q.2 * g (q.2.1 (((m + 1 : ℕ) : ℝ≥0) * Renewal.regenDelta lam) -
          q.2.1 ((m : ℝ≥0) * Renewal.regenDelta lam)) *
        Φ (iteratedRecord (Renewal.regenDelta lam) lam (l / lam) (Renewal.forceCoord hd) 1 q) := by
    by_cases hq : q.2 ∈ E <;> simp [hq]
  have heq' (q : FieldPair d × CoupledSample d) :
      (Prod.snd ⁻¹' E).indicator (fun q : FieldPair d × CoupledSample d =>
        H q.2 * g (q.2.1 (((m + 1 : ℕ) : ℝ≥0) * Renewal.regenDelta lam) -
          q.2.1 ((m : ℝ≥0) * Renewal.regenDelta lam))) q =
      E.indicator H q.2 * g (q.2.1 (((m + 1 : ℕ) : ℝ≥0) * Renewal.regenDelta lam) -
          q.2.1 ((m : ℝ≥0) * Renewal.regenDelta lam)) := by
    by_cases hq : q.2 ∈ E <;> simp [hq]
  simp only [heq, heq']
  exact hfac

end EinsteinFull.Blueprint
