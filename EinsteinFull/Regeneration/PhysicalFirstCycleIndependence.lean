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

/-- The displacement up to `mλ⁻²` and the displacement over the bridge `[mλ⁻², (m + 1)λ⁻²]`. -/
def bridgeSplit {d : ℕ} (Δ : ℝ≥0) (m : ℕ) (q : FieldPair d × CoupledSample d) :
    Vec d × Vec d :=
  (q.2.1 ((m : ℝ≥0) * Δ) - q.2.1 0, q.2.1 (((m + 1 : ℕ) : ℝ≥0) * Δ) - q.2.1 ((m : ℝ≥0) * Δ))

theorem measurable_bridgeSplit {d : ℕ} (Δ : ℝ≥0) (m : ℕ) :
    Measurable (bridgeSplit (d := d) Δ m) := by
  have he : ∀ t : ℝ≥0, Measurable fun q : FieldPair d × CoupledSample d => q.2.1 t := fun t =>
    (continuous_eval_const t).measurable.comp measurable_snd.fst
  exact ((he _).sub (he _)).prodMk ((he _).sub (he _))

theorem setIntegral_indicator_one_eq_measureReal {α : Type*} [MeasurableSpace α]
    (ν : Measure α) [IsFiniteMeasure ν] (S T : Set α) (hT : MeasurableSet T)
    (f : α → ℝ) (hf : ∀ x, f x = T.indicator 1 x) :
    (∫ x in S, f x ∂ν) = ν.real (S ∩ T) := by
  rw [integral_congr_ae (ae_of_all _ hf), integral_indicator_one hT,
    measureReal_restrict_apply hT, Set.inter_comm]

open Classical in
/-- The slice product rule for the two displacements and the next record, for measurable sets
of the displacements. -/
theorem physical_slice_measure_factorization
    (hpast : node_app_u3A_factorization_u23_past_u2D_kernelStmt_phys)
    (hfuture : node_app_u3A_factorization_u23_future_u2D_kernelStmt_phys)
    (hslices : node_app_u3A_factorization_u23_slicesStmt_phys)
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1) (l δ : ℝ)
    (hl : 0 < l) (hsep : r₀ < 2 * l) (hδ₀ : 0 < δ) (hδ₁ : δ < 1)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : IsRegenerationCouplingPhys hd Q lam l δ h₀.le h₁ P K)
    (hD : annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam)) ≠ 0)
    (m : ℕ) (hm : 1 ≤ m) (A : Set (Vec d × Vec d)) (hA : MeasurableSet A)
    (B : Set (FutureState d (Renewal.forceCoord hd) (l / lam))) (hB : MeasurableSet B) :
    regenerationConditionedLaw hd Q lam l K hK.1 hD
        ({q : FieldPair d × CoupledSample d |
          firstRegenerationTime (Renewal.regenDelta lam) lam (l / lam) q.2
            (Renewal.forceCoord hd) =
            ((((m + 1 : ℕ) : ℝ≥0) * Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)} ∩
          bridgeSplit (Renewal.regenDelta lam) m ⁻¹' A ∩
          iteratedRecord (Renewal.regenDelta lam) lam (l / lam) (Renewal.forceCoord hd) 1 ⁻¹' B) =
      regenerationConditionedLaw hd Q lam l K hK.1 hD
        ({q : FieldPair d × CoupledSample d |
          firstRegenerationTime (Renewal.regenDelta lam) lam (l / lam) q.2
            (Renewal.forceCoord hd) =
            ((((m + 1 : ℕ) : ℝ≥0) * Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)} ∩
          bridgeSplit (Renewal.regenDelta lam) m ⁻¹' A) *
      regenerationConditionedLaw hd Q lam l K hK.1 hD
        (iteratedRecord (Renewal.regenDelta lam) lam (l / lam) (Renewal.forceCoord hd) 0 ⁻¹' B) := by
  set ν := regenerationConditionedLaw hd Q lam l K hK.1 hD with hνdef
  have : IsProbabilityMeasure (annealedCoupledLaw Q.measure K) :=
    annealedCoupledLaw_isProbabilityMeasure Q.measure K hK.1
  have : IsProbabilityMeasure ν := ProbabilityTheory.cond_isProbabilityMeasure hD
  set S := {q : FieldPair d × CoupledSample d |
    firstRegenerationTime (Renewal.regenDelta lam) lam (l / lam) q.2 (Renewal.forceCoord hd) =
      ((((m + 1 : ℕ) : ℝ≥0) * Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)} with hSdef
  set W := bridgeSplit (d := d) (Renewal.regenDelta lam) m with hWdef
  set Y1 := iteratedRecord (Renewal.regenDelta lam) lam (l / lam) (Renewal.forceCoord hd) 1
  set Y0 := iteratedRecord (Renewal.regenDelta lam) lam (l / lam) (Renewal.forceCoord hd) 0
  have hW : Measurable W := measurable_bridgeSplit _ m
  have hY1 : Measurable Y1 := measurable_iteratedRecord _ _ _ _ 1
  have hY0 : Measurable Y0 := measurable_iteratedRecord _ _ _ _ 0
  have hev : ∀ t : ℝ≥0, t ≤ (m : ℝ≥0) * Renewal.regenDelta lam →
      Measurable[finiteHistorySigma (Renewal.regenDelta lam) m] fun z : CoupledSample d => z.1 t :=
    fun t ht => EinsteinFull.Regeneration.measurable_path_finiteHistorySigma _ m t ht
  have hb1 : ∀ (s : Set (Vec d)) (x : Vec d), |s.indicator (fun _ => (1 : ℝ)) x| ≤ 1 := by
    intro s x
    by_cases hx : x ∈ s <;> simp [hx]
  have hrect : ∀ A₁ A₂ : Set (Vec d), MeasurableSet A₁ → MeasurableSet A₂ →
      ν (S ∩ W ⁻¹' (A₁ ×ˢ A₂) ∩ Y1 ⁻¹' B) = ν (S ∩ W ⁻¹' (A₁ ×ˢ A₂)) * ν (Y0 ⁻¹' B) := by
    intro A₁ A₂ hA₁ hA₂
    have hH : Measurable[finiteHistorySigma (Renewal.regenDelta lam) m]
        fun z : CoupledSample d => A₁.indicator (fun _ => (1 : ℝ))
          (z.1 ((m : ℝ≥0) * Renewal.regenDelta lam) - z.1 0) :=
      (measurable_const.indicator hA₁).comp ((hev _ le_rfl).sub (hev 0 (by positivity)))
    have hfac := physical_slice_factorization_endpoint_cond hpast hfuture hslices hd Q lam h₀ h₁
      l δ hl hsep hδ₀ hδ₁ P K hK hD m hm
      (fun z => A₁.indicator (fun _ => (1 : ℝ))
        (z.1 ((m : ℝ≥0) * Renewal.regenDelta lam) - z.1 0)) hH
      ⟨1, fun z => hb1 _ _⟩ (fun z => Set.indicator_nonneg (fun _ _ => zero_le_one) _)
      (A₂.indicator fun _ => (1 : ℝ)) (measurable_const.indicator hA₂) ⟨1, fun y => hb1 _ _⟩
      (fun y => Set.indicator_nonneg (fun _ _ => zero_le_one) _)
      (B.indicator fun _ => (1 : ℝ)) (measurable_const.indicator hB)
      ⟨1, fun r => by by_cases hr : r ∈ B <;> simp [hr]⟩
      (fun r => Set.indicator_nonneg (fun _ _ => zero_le_one) _)
    have hT3 : MeasurableSet (W ⁻¹' (A₁ ×ˢ A₂) ∩ Y1 ⁻¹' B) :=
      (hW (hA₁.prod hA₂)).inter (hY1 hB)
    rw [setIntegral_indicator_one_eq_measureReal ν S _ hT3 _ (fun q => by
        by_cases h1 : q.2.1 ((m : ℝ≥0) * Renewal.regenDelta lam) - q.2.1 0 ∈ A₁ <;>
        by_cases h3 : Y1 q ∈ B <;>
        simp [Set.indicator_apply, h1, h3, W, bridgeSplit, Y1]),
      setIntegral_indicator_one_eq_measureReal ν S _ (hW (hA₁.prod hA₂)) _ (fun q => by
        by_cases h1 : q.2.1 ((m : ℝ≥0) * Renewal.regenDelta lam) - q.2.1 0 ∈ A₁ <;>
        simp [Set.indicator_apply, h1, W, bridgeSplit])] at hfac
    have h3 : (∫ q, B.indicator (fun _ => (1 : ℝ)) (regenerationRecord hd lam l 0 q) ∂ν) =
        ν.real (Y0 ⁻¹' B) := by
      rw [← integral_indicator_one (hY0 hB)]
      exact integral_congr_ae (ae_of_all _ fun q => by
        change B.indicator (fun _ => (1 : ℝ)) (Y0 q) = (Y0 ⁻¹' B).indicator 1 q
        by_cases h : Y0 q ∈ B <;> simp [h])
    rw [h3, measureReal_def, measureReal_def, measureReal_def, ← ENNReal.toReal_mul,
      ← Set.inter_assoc] at hfac
    exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _)
      (ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _))).mp hfac
  have hC : ∀ s ∈ Set.image2 (· ×ˢ ·) {s : Set (Vec d) | MeasurableSet s}
      {t : Set (Vec d) | MeasurableSet t},
      (ν.restrict (S ∩ Y1 ⁻¹' B)).map W s = (ν (Y0 ⁻¹' B) • (ν.restrict S).map W) s := by
    rintro _ ⟨A₁, hA₁, A₂, hA₂, rfl⟩
    change MeasurableSet A₁ at hA₁
    change MeasurableSet A₂ at hA₂
    rw [Measure.smul_apply, Measure.map_apply hW (hA₁.prod hA₂),
      Measure.map_apply hW (hA₁.prod hA₂), Measure.restrict_apply (hW (hA₁.prod hA₂)),
      Measure.restrict_apply (hW (hA₁.prod hA₂)), smul_eq_mul, mul_comm,
      Set.inter_comm _ S, Set.inter_comm _ (S ∩ Y1 ⁻¹' B)]
    rw [show S ∩ Y1 ⁻¹' B ∩ W ⁻¹' (A₁ ×ˢ A₂) = S ∩ W ⁻¹' (A₁ ×ˢ A₂) ∩ Y1 ⁻¹' B by
      rw [Set.inter_assoc, Set.inter_comm (Y1 ⁻¹' B), ← Set.inter_assoc]]
    exact hrect A₁ A₂ hA₁ hA₂
  have hM : (ν.restrict (S ∩ Y1 ⁻¹' B)).map W = ν (Y0 ⁻¹' B) • (ν.restrict S).map W := by
    refine ext_of_generate_finite _ generateFrom_prod.symm isPiSystem_prod hC ?_
    rw [← Set.univ_prod_univ]
    exact hC _ ⟨Set.univ, Set.mem_ofPred_eq.mpr MeasurableSet.univ, Set.univ,
      Set.mem_ofPred_eq.mpr MeasurableSet.univ, rfl⟩
  have hMA := congrArg (fun M : Measure (Vec d × Vec d) => M A) hM
  simp only [Measure.smul_apply, Measure.map_apply hW hA, Measure.restrict_apply (hW hA),
    smul_eq_mul] at hMA
  rw [Set.inter_comm _ S, Set.inter_comm _ (S ∩ Y1 ⁻¹' B), mul_comm] at hMA
  rw [← hMA, Set.inter_assoc, Set.inter_comm (W ⁻¹' A), ← Set.inter_assoc]

/-- The duration and the displacement of the first cycle are independent of the record at the
first regeneration time under the law conditioned on no return (GMP 2012, Theorem 5.6; Shen
2003, Theorem 2.5). -/
theorem physical_first_cycle_indepFun
    (hpast : node_app_u3A_factorization_u23_past_u2D_kernelStmt_phys)
    (hfuture : node_app_u3A_factorization_u23_future_u2D_kernelStmt_phys)
    (hslices : node_app_u3A_factorization_u23_slicesStmt_phys)
    (hscope : node_app_u3A_factorization_u23_coupling_u2D_scopeStmt_phys)
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1) (l δ : ℝ)
    (hl : 0 < l) (hsep : r₀ < 2 * l) (hδ₀ : 0 < δ) (hδ₁ : δ < 1)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : IsRegenerationCouplingPhys hd Q lam l δ h₀.le h₁ P K)
    (hD : annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam)) ≠ 0)
    (hν1 : (regenerationConditionedLaw hd Q lam l K hK.1 hD).map
        (iteratedRecord (Renewal.regenDelta lam) lam (l / lam) (Renewal.forceCoord hd) 1) =
      (regenerationConditionedLaw hd Q lam l K hK.1 hD).map
        (iteratedRecord (Renewal.regenDelta lam) lam (l / lam) (Renewal.forceCoord hd) 0)) :
    (fun q => EinsteinFull.Regeneration.recordCycle (Renewal.regenDelta lam) lam (l / lam)
        (Renewal.forceCoord hd)
        (iteratedRecord (Renewal.regenDelta lam) lam (l / lam) (Renewal.forceCoord hd) 0 q))
      ⟂ᵢ[regenerationConditionedLaw hd Q lam l K hK.1 hD]
      iteratedRecord (Renewal.regenDelta lam) lam (l / lam) (Renewal.forceCoord hd) 1 := by
  set ν := regenerationConditionedLaw hd Q lam l K hK.1 hD with hνdef
  have : IsProbabilityMeasure (annealedCoupledLaw Q.measure K) :=
    annealedCoupledLaw_isProbabilityMeasure Q.measure K hK.1
  have : IsProbabilityMeasure ν := ProbabilityTheory.cond_isProbabilityMeasure hD
  set X := fun q => EinsteinFull.Regeneration.recordCycle (Renewal.regenDelta lam) lam (l / lam)
    (Renewal.forceCoord hd)
    (iteratedRecord (Renewal.regenDelta lam) lam (l / lam) (Renewal.forceCoord hd) 0 q) with hXdef
  have hX : Measurable X := (EinsteinFull.Regeneration.measurable_recordCycle _ _ _ _).comp
    (measurable_iteratedRecord _ _ _ _ 0)
  have hY1 : Measurable
      (iteratedRecord (Renewal.regenDelta lam) lam (l / lam) (Renewal.forceCoord hd) 1) :=
    measurable_iteratedRecord _ _ _ _ 1
  have hY0 : Measurable
      (iteratedRecord (Renewal.regenDelta lam) lam (l / lam) (Renewal.forceCoord hd) 0) :=
    measurable_iteratedRecord _ _ _ _ 0
  rw [indepFun_iff_measure_inter_preimage_eq_mul]
  intro A B hA hB
  let s : ℕ → Set (FieldPair d × CoupledSample d) := fun n =>
    {q | firstRegenerationTime (Renewal.regenDelta lam) lam (l / lam) q.2
      (Renewal.forceCoord hd) =
      ((((n + 1 + 1 : ℕ) : ℝ≥0) * Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)}
  have hs : ∀ n, MeasurableSet (s n) := fun n =>
    ((measurable_firstRegenerationTime _ lam _ _).comp measurable_snd)
      (measurableSet_singleton _)
  have hdis : Pairwise (fun m n => Disjoint (s m) (s n)) := by
    intro m n hmn
    refine Set.disjoint_left.mpr fun q hm hn => hmn ?_
    have he := ENNReal.coe_inj.mp (hm.symm.trans hn)
    have hc := mul_right_cancel₀ (EinsteinRelation.regenDelta_pos h₀).ne' he
    have hnat : m + 1 + 1 = n + 1 + 1 := by exact_mod_cast hc
    omega
  have hcover : ∀ᵐ q ∂ν, q ∈ ⋃ n, s n := by
    have hsc := (hscope d hd Λ₀ r₀ Q lam h₀ h₁ l δ hl hsep hδ₀ hδ₁ P K hK hD 1).2.2 ν
      (Set.mem_insert_of_mem _ rfl)
    filter_upwards [hsc] with q hq
    obtain ⟨n, hn, ht, _⟩ := hq
    refine Set.mem_iUnion.mpr ⟨n - 2, ?_⟩
    have hn₂ : n - 2 + 1 + 1 = n := by omega
    change firstRegenerationTime (Renewal.regenDelta lam) lam (l / lam) q.2
      (Renewal.forceCoord hd) =
      ((((n - 2 + 1 + 1 : ℕ) : ℝ≥0) * Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)
    rw [hn₂]
    simpa only [EinsteinFull.regenerationTime, regenerationTime_one] using ht
  have hsum : ∀ T, MeasurableSet T → ν T = ∑' n, ν (T ∩ s n) := by
    intro T hT
    have h1 : ν T = ν.restrict (⋃ n, s n) T := by
      rw [Measure.restrict_eq_self_of_ae_mem hcover]
    rw [h1, Measure.restrict_apply hT, Set.inter_iUnion, measure_iUnion]
    · intro m n hmn
      exact (hdis hmn).mono Set.inter_subset_right Set.inter_subset_right
    · exact fun n => hT.inter (hs n)
  have hXs : ∀ n q, q ∈ s n → X q =
      (((((n + 1 + 1 : ℕ) : ℝ≥0) * Renewal.regenDelta lam : ℝ≥0) : ℝ),
        (bridgeSplit (Renewal.regenDelta lam) (n + 1) q).1 +
          (bridgeSplit (Renewal.regenDelta lam) (n + 1) q).2) := by
    intro n q hq
    have hq' : firstRegenerationTime (Renewal.regenDelta lam) lam (l / lam) q.2
        (Renewal.forceCoord hd) =
        ((((n + 1 + 1 : ℕ) : ℝ≥0) * Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞) := hq
    simp only [hXdef]
    rw [recordCycle_iteratedRecord_zero, hq', ENNReal.toNNReal_coe]
    refine Prod.ext rfl ?_
    simp only [bridgeSplit]
    abel
  let A' : ℕ → Set (Vec d × Vec d) := fun n =>
    (fun p : Vec d × Vec d => (((((n + 1 + 1 : ℕ) : ℝ≥0) * Renewal.regenDelta lam : ℝ≥0) : ℝ),
      p.1 + p.2)) ⁻¹' A
  have hA' : ∀ n, MeasurableSet (A' n) := fun n =>
    (measurable_const.prodMk (measurable_fst.add measurable_snd)) hA
  have hset : ∀ n, X ⁻¹' A ∩
      iteratedRecord (Renewal.regenDelta lam) lam (l / lam) (Renewal.forceCoord hd) 1 ⁻¹' B ∩
        s n = s n ∩ bridgeSplit (Renewal.regenDelta lam) (n + 1) ⁻¹' A' n ∩
      iteratedRecord (Renewal.regenDelta lam) lam (l / lam) (Renewal.forceCoord hd) 1 ⁻¹' B := by
    intro n
    ext q
    constructor
    · rintro ⟨⟨hxa, hyb⟩, hq⟩
      refine ⟨⟨hq, ?_⟩, hyb⟩
      have hxa' : X q ∈ A := hxa
      rw [hXs n q hq] at hxa'
      exact hxa'
    · rintro ⟨⟨hq, ha⟩, hyb⟩
      refine ⟨⟨?_, hyb⟩, hq⟩
      change X q ∈ A
      rw [hXs n q hq]
      exact ha
  have hset' : ∀ n, X ⁻¹' A ∩ s n =
      s n ∩ bridgeSplit (Renewal.regenDelta lam) (n + 1) ⁻¹' A' n := by
    intro n
    ext q
    constructor
    · rintro ⟨hxa, hq⟩
      refine ⟨hq, ?_⟩
      have hxa' : X q ∈ A := hxa
      rw [hXs n q hq] at hxa'
      exact hxa'
    · rintro ⟨hq, ha⟩
      refine ⟨?_, hq⟩
      change X q ∈ A
      rw [hXs n q hq]
      exact ha
  calc ν (X ⁻¹' A ∩
        iteratedRecord (Renewal.regenDelta lam) lam (l / lam) (Renewal.forceCoord hd) 1 ⁻¹' B)
      = ∑' n, ν (X ⁻¹' A ∩
        iteratedRecord (Renewal.regenDelta lam) lam (l / lam) (Renewal.forceCoord hd) 1 ⁻¹' B ∩
          s n) := hsum _ ((hX hA).inter (hY1 hB))
    _ = ∑' n, ν (X ⁻¹' A ∩ s n) * ν
        (iteratedRecord (Renewal.regenDelta lam) lam (l / lam) (Renewal.forceCoord hd) 0 ⁻¹' B) := by
      congr 1
      funext n
      rw [hset n, hset' n]
      exact physical_slice_measure_factorization hpast hfuture hslices hd Q lam h₀ h₁ l δ hl hsep
        hδ₀ hδ₁ P K hK hD (n + 1) (by omega) (A' n) (hA' n) B hB
    _ = ν (X ⁻¹' A) * ν
        (iteratedRecord (Renewal.regenDelta lam) lam (l / lam) (Renewal.forceCoord hd) 1 ⁻¹' B) := by
      rw [ENNReal.tsum_mul_right, ← hsum _ (hX hA)]
      congr 1
      rw [← Measure.map_apply hY0 hB, ← Measure.map_apply hY1 hB, hν1]

end EinsteinFull.Blueprint
