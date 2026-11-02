import EinsteinFull.Blueprint.G1.node_app_u3A_factorization_u23_independence_v2
import EinsteinFull.Blueprint.G1.node_app_u3A_factorization_u23_endpoint_u2D_disintegration
import EinsteinFull.Blueprint.G1.node_app_u3A_factorization_u23_future_u2D_kernel
import EinsteinFull.Blueprint.Foundation.node_app_u3A_factorization_u23_past_u2D_kernel
import EinsteinFull.Blueprint.Foundation.node_app_u3A_factorization_u23_slices
import EinsteinFull.Blueprint.Foundation.node_app_u3A_factorization_u23_coupling_u2D_scope
import EinsteinRelation.Regeneration.FirstSlicePastLocality
import EinsteinRelation.Regeneration.KilledFutureConditionalMean
import EinsteinRelation.Regeneration.CorrectedHalfSpaceIndependence

/-! Support for the first-cycle independence reduction.

The supplied origin past-kernel statement gives the literal past factors.
Signed product-test extension, spatial integrability and volume normalization
support the slice calculation and assembly of the actual first marginal.
-/

open MeasureTheory Classical
open scoped NNReal ENNReal

noncomputable section

namespace EinsteinFull.Blueprint

open EinsteinRelation EinsteinRelation.Regeneration

/-- The physical radius preserves the strict finite-range gap for every
admissible positive force. -/
theorem sbxS5_radius_gap {r₀ l lam : ℝ} (hl : 0 < l) (h₀ : 0 < lam)
    (h₁ : lam ≤ 1) (hsep : r₀ < 2 * l) : r₀ < 2 * (l / lam) := by
  have hlR : l ≤ l / lam := by
    rw [le_div_iff₀ h₀]
    exact mul_le_of_le_one_right hl.le h₁
  linarith

section Setup

variable {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1) (l δ : ℝ)
    (hl : 0 < l) (hsep : r₀ < 2 * l) (hδ₀ : 0 < δ) (hδ₁ : δ < 1)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K)

include hK hl hsep hδ₀ hδ₁

/-- Apply the supplied origin locality statement to the literal forced-event
and endpoint-ball test. The version observes the joint field below `y_i-4R`. -/
theorem sbxS5_firstSlicePast_local
    (hpast : node_app_u3A_factorization_u23_past_u2D_kernelStmt)
    (m : ℕ) (H : CoupledSample d → ℝ)
    (hH : Measurable[finiteHistorySigma (Renewal.regenDelta lam) m] H)
    (hbH : BoundedRealTest H) (y : Vec d) :
    ∃ A' : FieldPair d → ℝ,
      Measurable[localSigma {x : Vec d |
        x (Renewal.forceCoord hd) ≤ y (Renewal.forceCoord hd) - 4 * (l / lam)}] A' ∧
      (fun ω => firstSlicePastIntegral (Renewal.regenDelta lam) lam (l / lam)
        (Renewal.forceCoord hd) m K H (y, ω)) =ᵐ[Q.measure] A' := by
  classical
  let Δ := Renewal.regenDelta lam
  let R := l / lam
  let i := Renewal.forceCoord hd
  have hΔ : 0 < Δ := EinsteinRelation.regenDelta_pos h₀
  have hR : 0 < R := div_pos hl h₀
  let Γ := forcedBitTrialEvent Δ lam R i m
  let E : Set (CoupledSample d) := {z | y ∈ endpointBall i R (z.1 ((m : ℝ≥0) * Δ))}
  let J := E.indicator (Γ.indicator H)
  have hJ : Measurable[finiteHistorySigma Δ m] J :=
    (hH.indicator (measurableSet_forcedBitTrialEvent_finiteHistory Δ hΔ lam R hR i m)).indicator
      (measurableSet_endpointBall_past Δ R i m y)
  have hbJ : BoundedRealTest J := by
    obtain ⟨C, hC⟩ := hbH
    refine ⟨max C 0, fun z => ?_⟩
    by_cases hz : z ∈ E
    · by_cases hΓ : z ∈ Γ
      · simpa only [J, Set.indicator_of_mem hz, Set.indicator_of_mem hΓ] using
          (hC z).trans (le_max_left C 0)
      · simpa only [J, Set.indicator_of_mem hz, Set.indicator_of_notMem hΓ, abs_zero] using
          (le_max_right C 0)
    · simpa only [J, Set.indicator_of_notMem hz, abs_zero] using (le_max_right C 0)
  have hbar : ∀ z, (¬ ∀ t : ℝ≥0, t ≤ (m : ℝ≥0) * Δ → z.1 t i ≤ y i - 7 * R) →
      J z = 0 := by
    intro z hz
    by_cases he : z ∈ E
    · by_cases hΓ : z ∈ Γ
      · exact (hz (forcedBitTrialEvent_endpoint_past_barrier Δ hΔ lam R h₀ hR i m z
          hΓ y he)).elim
      · simp only [J, Set.indicator_of_mem he, Set.indicator_of_notMem hΓ]
    · exact Set.indicator_of_notMem he _
  obtain ⟨A', hA', heq⟩ := hpast d hd Λ₀ r₀ Q lam h₀ h₁ l δ hl hsep hδ₀ hδ₁
    P K hK m (y i - 7 * R) J hJ hbJ hbar
  have hv : y i - 7 * R + 3 * R = y i - 4 * R := by ring
  rw [hv] at hA'
  refine ⟨A', hA', ?_⟩
  have hident : (fun ω => firstSlicePastIntegral Δ lam R i m K H (y, ω)) =ᵐ[Q.measure]
      (fun ω => ∫ z, J z ∂K (0, ω)) := by
    apply Filter.Eventually.of_forall
    intro ω
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro z
    by_cases he : z ∈ E
    · change y ∈ endpointBall i R (z.1 ((m : ℝ≥0) * Δ)) at he
      simp only [J, E, Γ, Set.indicator, Set.mem_ofPred_eq, he, ite_true, mul_one]
    · change y ∉ endpointBall i R (z.1 ((m : ℝ≥0) * Δ)) at he
      simp only [J, E, Set.indicator, Set.mem_ofPred_eq, he, ite_false, mul_zero]
  exact hident.trans heq

/-- The actual quenched past factor vanishes below the endpoint threshold.
The starting-point exceptional set comes from the actual GMP path marginal. -/
theorem sbxS5_firstSlicePast_zero
    (hslices : node_app_u3A_factorization_u23_slicesStmt)
    (n : ℕ) (hn : 2 ≤ n) (H : CoupledSample d → ℝ) (y : Vec d)
    (hy : y (Renewal.forceCoord hd) < 10 * (l / lam)) :
    (fun ω => firstSlicePastIntegral (Renewal.regenDelta lam) lam (l / lam)
      (Renewal.forceCoord hd) (n - 1) K H (y, ω)) =ᵐ[Q.measure] 0 := by
  classical
  have hstart := ae_origin_start_of_isGMPReducedKernel hd Q lam h₀.le h₁ P K
    hK.1 hK.2.1 hK.2.2.1
  have hstartK := ae_quenched_of_annealed Q.measure K hK.1 hstart
  have hgeom := (hslices d hd Λ₀ r₀ Q lam h₀ h₁ l δ hl hsep hδ₀ hδ₁ P K hK n hn).2.2
  filter_upwards [hstartK] with ω hω
  apply integral_eq_zero_of_ae
  filter_upwards [hω] with z hz
  by_cases hΓ : z ∈ forcedBitTrialEvent (Renewal.regenDelta lam) lam (l / lam)
      (Renewal.forceCoord hd) (n - 1)
  · have hb : y ∉ endpointBall (Renewal.forceCoord hd) (l / lam)
        (z.1 (((n - 1 : ℕ) : ℝ≥0) * Renewal.regenDelta lam)) := by
      intro hb
      exact (not_le.mpr hy) ((hgeom z hz hΓ).2.2 y hb).1
    simp only [Set.indicator_of_mem hΓ, ite_eq_right hb, mul_zero, Pi.zero_apply]
  · simp only [Set.indicator_of_notMem hΓ, zero_mul, Pi.zero_apply]

/-- On the nonzero endpoint range the original field test belongs to the
same past half-space as the first-slice kernel. -/
theorem sbxS5_pastFactor_local
    (hpast : node_app_u3A_factorization_u23_past_u2D_kernelStmt)
    (F : FieldPair d → ℝ)
    (hF : Measurable[localSigma {x : Vec d | euclideanNorm x < l / lam}] F)
    (m : ℕ) (H : CoupledSample d → ℝ)
    (hH : Measurable[finiteHistorySigma (Renewal.regenDelta lam) m] H)
    (hbH : BoundedRealTest H) (y : Vec d)
    (hy : 10 * (l / lam) ≤ y (Renewal.forceCoord hd)) :
    ∃ A' : FieldPair d → ℝ,
      Measurable[localSigma {x : Vec d |
        x (Renewal.forceCoord hd) ≤ y (Renewal.forceCoord hd) - 4 * (l / lam)}] A' ∧
      (fun ω => F ω * firstSlicePastIntegral (Renewal.regenDelta lam) lam (l / lam)
        (Renewal.forceCoord hd) m K H (y, ω)) =ᵐ[Q.measure] A' := by
  obtain ⟨A', hA', heq⟩ := sbxS5_firstSlicePast_local hd Q lam h₀ h₁ l δ hl hsep hδ₀ hδ₁
    P K hK hpast m H hH hbH y
  have hFlocal : Measurable[localSigma {x : Vec d |
      x (Renewal.forceCoord hd) ≤ y (Renewal.forceCoord hd) - 4 * (l / lam)}] F := by
    apply hF.mono (Probability.localSigma_mono ?_) le_rfl
    intro x hx
    have hcoord := (le_abs_self (x (Renewal.forceCoord hd))).trans
      (coordinate_abs_le_euclideanNorm x (Renewal.forceCoord hd))
    have hR := div_pos hl h₀
    change euclideanNorm x < l / lam at hx
    change x (Renewal.forceCoord hd) ≤ y (Renewal.forceCoord hd) - 4 * (l / lam)
    linarith
  exact ⟨fun ω => F ω * A' ω, hFlocal.mul hA', (Filter.EventuallyEq.rfl).mul heq⟩

omit hl hsep hδ₀ hδ₁ in
/-- The origin future mean has the literal no-return normalization. This
identity uses the actual path marginal, independently of spatial transport. -/
theorem sbxS5_killedFuture_origin_mean
    (hD : annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam)) ≠ 0)
    (Φ : FutureState d (Renewal.forceCoord hd) (l / lam) → ℝ)
    (hΦ : Measurable Φ) (hbΦ : BoundedRealTest Φ) :
    (∫ ω, ∫ z, killedFutureTest (l / lam) (Renewal.forceCoord hd) Φ ((0, ω), z)
      ∂K (0, ω) ∂Q.measure) =
      (annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam))).toReal *
        ∫ q, Φ (regenerationRecord hd lam l 0 q)
          ∂regenerationConditionedLaw hd Q lam l K hK.1 hD := by
  exact integral_killed_future_origin_eq_condIntegral Q.measure K hK.1
    (ae_origin_start_of_isGMPReducedKernel hd Q lam h₀.le h₁ P K
      hK.1 hK.2.1 hK.2.2.1)
    (Renewal.regenDelta lam) lam (l / lam) (Renewal.forceCoord hd) hD Φ hΦ hbΦ
    (fun yω => ∫ z, killedFutureTest (l / lam) (Renewal.forceCoord hd) Φ (yω, z) ∂K yω)
    (Filter.Eventually.of_forall fun _ => rfl)

/-- Sum the literal finite first-cycle slices. The supplied scope gives
coverage at indices at least two, including at every admissible scale. -/
theorem sbxS5_firstMarginal_of_sliceIdentity
    (hscope : node_app_u3A_factorization_u23_coupling_u2D_scopeStmt)
    (hD : annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam)) ≠ 0)
    (Φ : FutureState d (Renewal.forceCoord hd) (l / lam) → ℝ)
    (hΦ : Measurable Φ) (hbΦ : BoundedRealTest Φ)
    (hslice : ∀ n : ℕ, 2 ≤ n →
      (∫ q in {q | regenerationTime hd lam l 1 q.2 =
          (((n : ℝ≥0) * Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)},
        Φ (regenerationRecord hd lam l 1 q) ∂annealedCoupledLaw Q.measure K) =
      (∫ q in {q | regenerationTime hd lam l 1 q.2 =
          (((n : ℝ≥0) * Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)},
        (1 : ℝ) ∂annealedCoupledLaw Q.measure K) *
        ∫ q, Φ (regenerationRecord hd lam l 0 q)
          ∂regenerationConditionedLaw hd Q lam l K hK.1 hD) :
    (∫ q, Φ (regenerationRecord hd lam l 1 q) ∂annealedCoupledLaw Q.measure K) =
      ∫ q, Φ (regenerationRecord hd lam l 0 q)
        ∂regenerationConditionedLaw hd Q lam l K hK.1 hD := by
  let μ := annealedCoupledLaw Q.measure K
  haveI : IsProbabilityMeasure μ := annealedCoupledLaw_isProbabilityMeasure Q.measure K hK.1
  have hsc := hscope d hd Λ₀ r₀ Q lam h₀ h₁ l δ hl hsep hδ₀ hδ₁ P K hK hD 1
  have hgrid := hsc.2.2 μ (by simp [μ])
  let s : ℕ → Set (FieldPair d × CoupledSample d) := fun n =>
    {q | regenerationTime hd lam l 1 q.2 =
      ((((n + 2 : ℕ) : ℝ≥0) * Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)}
  have hs (n : ℕ) : MeasurableSet (s n) :=
    (hsc.1.comp measurable_snd) (measurableSet_singleton _)
  have hdis : Pairwise (fun m n => Disjoint (s m) (s n)) := by
    intro m n hmn
    apply Set.disjoint_left.mpr
    intro q hm hn
    have he := ENNReal.coe_inj.mp (hm.symm.trans hn)
    have hc := mul_right_cancel₀ (EinsteinRelation.regenDelta_pos h₀).ne' he
    have hnat : m + 2 = n + 2 := by exact_mod_cast hc
    exact hmn (Nat.add_right_cancel hnat)
  have hcover : ∀ᵐ q ∂μ, q ∈ ⋃ n, s n := by
    filter_upwards [hgrid] with q hq
    obtain ⟨n, hn, ht, _⟩ := hq
    have hn₂ : n - 2 + 2 = n := by omega
    refine Set.mem_iUnion.mpr ⟨n - 2, ?_⟩
    change regenerationTime hd lam l 1 q.2 =
      ((((n - 2 + 2 : ℕ) : ℝ≥0) * Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)
    simpa only [hn₂] using ht
  have hseries (f : FieldPair d × CoupledSample d → ℝ) (hf : Integrable f μ) :
      HasSum (fun n => ∫ q in s n, f q ∂μ) (∫ q, f q ∂μ) := by
    have h := hasSum_integral_iUnion hs hdis hf.integrableOn
    rw [Measure.restrict_eq_self_of_ae_mem hcover] at h
    exact h
  have hb : Integrable (fun q => Φ (regenerationRecord hd lam l 1 q)) μ := by
    obtain ⟨C, hC⟩ := hbΦ
    exact Integrable.of_bound (hΦ.comp hsc.2.1).aestronglyMeasurable C
      (Filter.Eventually.of_forall fun q => by simpa only [Real.norm_eq_abs] using hC _)
  have hleft := hseries _ hb
  let c := ∫ q, Φ (regenerationRecord hd lam l 0 q)
    ∂regenerationConditionedLaw hd Q lam l K hK.1 hD
  have hright := (hseries (fun _ => (1 : ℝ)) (integrable_const 1)).mul_right c
  have heq : (fun n => ∫ q in s n, Φ (regenerationRecord hd lam l 1 q) ∂μ) =
      (fun n => (∫ q in s n, (1 : ℝ) ∂μ) * c) := by
    funext n
    exact hslice (n + 2) (by omega)
  rw [heq] at hleft
  simpa only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one,
    smul_eq_mul, one_mul] using
    hleft.unique hright

end Setup

/-- Product tests of the path-and-coins pair and the entire future field
determine a finite law on the full future triple. -/
theorem sbxS5_futureMeasure_eq_of_productTests {d : ℕ} (i : Fin d) (R : ℝ)
    (μ ν : Measure (FutureState d i R)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (htest : ∀ (f : Path d × BernoulliSequence → ℝ), Measurable f → BoundedRealTest f →
      ∀ (g : (FutureHalfSpace d i R → Mat d × ℝ) → ℝ), Measurable g → BoundedRealTest g →
        (∫ r, f (r.1, r.2.1) * g r.2.2 ∂μ) =
          ∫ r, f (r.1, r.2.1) * g r.2.2 ∂ν) : μ = ν := by
  classical
  apply Measure.ext_prod₃
  intro s t u hs ht hu
  let f : Path d × BernoulliSequence → ℝ := (s ×ˢ t).indicator (fun _ => 1)
  let g : (FutureHalfSpace d i R → Mat d × ℝ) → ℝ := u.indicator (fun _ => 1)
  have hf : Measurable f := measurable_const.indicator (hs.prod ht)
  have hg : Measurable g := measurable_const.indicator hu
  have hbf : BoundedRealTest f := by
    refine ⟨1, fun x => ?_⟩
    by_cases hx : x ∈ s ×ˢ t <;> simp [f, hx]
  have hbg : BoundedRealTest g := by
    refine ⟨1, fun x => ?_⟩
    by_cases hx : x ∈ u <;> simp [g, hx]
  have hind : (fun r : FutureState d i R => f (r.1, r.2.1) * g r.2.2) =
      (s ×ˢ t ×ˢ u).indicator (fun _ => (1 : ℝ)) := by
    funext r
    by_cases h₁ : r.1 ∈ s <;> by_cases h₂ : r.2.1 ∈ t <;>
      by_cases h₃ : r.2.2 ∈ u <;> simp [f, g, h₁, h₂, h₃]
  have heq := htest f hf hbf g hg hbg
  rw [hind] at heq
  simp only [integral_indicator (hs.prod (ht.prod hu)), setIntegral_const,
    smul_eq_mul, mul_one, measureReal_def] at heq
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top μ _) (measure_ne_top ν _)).mp heq


/-- An integrable signed weight has a finite positive-density measure. -/
theorem sbxS5_isFiniteMeasure_positiveWeight {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (w : α → ℝ) (hw : Integrable w μ) :
    IsFiniteMeasure (μ.withDensity (fun x => ENNReal.ofReal (w x))) := by
  apply isFiniteMeasure_withDensity
  exact ((lintegral_ofReal_le_lintegral_enorm w).trans_lt hw.2).ne

/-- The difference of the positive and negative weighted record laws integrates
an arbitrary bounded record test against the original signed weight. -/
theorem sbxS5_signedWeight_record_integral {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (w : α → ℝ) (hw : Measurable w) (hiw : Integrable w μ)
    (T : α → β) (hT : Measurable T) (Φ : β → ℝ)
    (hΦ : Measurable Φ) (hbΦ : BoundedRealTest Φ) :
    (∫ r, Φ r ∂((μ.withDensity (fun x => ENNReal.ofReal (w x))).map T)) -
      (∫ r, Φ r ∂((μ.withDensity (fun x => ENNReal.ofReal (-w x))).map T)) =
        ∫ x, w x * Φ (T x) ∂μ := by
  obtain ⟨C, hC⟩ := hbΦ
  have hcomp : Measurable (fun x => Φ (T x)) := hΦ.comp hT
  have hbound : ∀ᵐ x ∂μ, ‖Φ (T x)‖ ≤ C :=
    Filter.Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hC (T x)
  have hip := hiw.pos_part.mul_bdd hcomp.aestronglyMeasurable hbound
  have hin := hiw.neg_part.mul_bdd hcomp.aestronglyMeasurable hbound
  rw [integral_map hT.aemeasurable hΦ.aestronglyMeasurable,
    integral_map hT.aemeasurable hΦ.aestronglyMeasurable,
    integral_withDensity_eq_integral_toReal_smul hw.ennreal_ofReal
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top),
    integral_withDensity_eq_integral_toReal_smul
      (f := fun x => ENNReal.ofReal (-w x)) hw.neg.ennreal_ofReal
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal', smul_eq_mul]
  rw [← integral_sub hip hin]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  by_cases hx : 0 ≤ w x
  · simp only [max_eq_left hx, max_eq_right (neg_nonpos.mpr hx), zero_mul, sub_zero]
  · simp only [max_eq_right (le_of_not_ge hx),
      max_eq_left (neg_nonneg.mpr (le_of_not_ge hx))]
    ring

/-- Equality against product future tests extends to every bounded measurable
full future-record test, even for integrable signed weights on different sample spaces. -/
theorem sbxS5_signedWeighted_futureTests {d : ℕ} (i : Fin d) (R : ℝ)
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β)
    (w : α → ℝ) (v : β → ℝ) (hw : Measurable w) (hv : Measurable v)
    (hiw : Integrable w μ) (hiv : Integrable v ν)
    (T : α → FutureState d i R) (S : β → FutureState d i R)
    (hT : Measurable T) (hS : Measurable S)
    (htest : ∀ (f : Path d × BernoulliSequence → ℝ), Measurable f → BoundedRealTest f →
      ∀ (g : (FutureHalfSpace d i R → Mat d × ℝ) → ℝ), Measurable g → BoundedRealTest g →
        (∫ x, w x * (f ((T x).1, (T x).2.1) * g (T x).2.2) ∂μ) =
          ∫ x, v x * (f ((S x).1, (S x).2.1) * g (S x).2.2) ∂ν)
    (Φ : FutureState d i R → ℝ) (hΦ : Measurable Φ) (hbΦ : BoundedRealTest Φ) :
    (∫ x, w x * Φ (T x) ∂μ) = ∫ x, v x * Φ (S x) ∂ν := by
  let μp := (μ.withDensity (fun x => ENNReal.ofReal (w x))).map T
  let μn := (μ.withDensity (fun x => ENNReal.ofReal (-w x))).map T
  let νp := (ν.withDensity (fun x => ENNReal.ofReal (v x))).map S
  let νn := (ν.withDensity (fun x => ENNReal.ofReal (-v x))).map S
  letI := sbxS5_isFiniteMeasure_positiveWeight μ w hiw
  letI := sbxS5_isFiniteMeasure_positiveWeight μ (fun x => -w x) hiw.neg
  letI := sbxS5_isFiniteMeasure_positiveWeight ν v hiv
  letI := sbxS5_isFiniteMeasure_positiveWeight ν (fun x => -v x) hiv.neg
  have hbounded : ∀ (ρ : Measure (FutureState d i R)) [IsFiniteMeasure ρ]
      (ψ : FutureState d i R → ℝ), Measurable ψ → BoundedRealTest ψ → Integrable ψ ρ := by
    intro ρ hρ ψ hψ hbψ
    obtain ⟨C, hC⟩ := hbψ
    exact Integrable.of_bound hψ.aestronglyMeasurable C
      (Filter.Eventually.of_forall fun r => by simpa only [Real.norm_eq_abs] using hC r)
  have hbalance : μp + νn = μn + νp := by
    apply sbxS5_futureMeasure_eq_of_productTests i R
    intro f hf hbf g hg hbg
    let ψ : FutureState d i R → ℝ := fun r => f (r.1, r.2.1) * g r.2.2
    have hψ : Measurable ψ :=
      (hf.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))).mul
        (hg.comp (measurable_snd.comp measurable_snd))
    have hbψ : BoundedRealTest ψ := by
      obtain ⟨C, hC⟩ := hbf
      obtain ⟨D, hD⟩ := hbg
      refine ⟨|C| * |D|, fun r => ?_⟩
      exact (abs_mul _ _).trans_le (mul_le_mul
        ((hC _).trans (le_abs_self C)) ((hD _).trans (le_abs_self D))
        (abs_nonneg _) (abs_nonneg _))
    have hμ := sbxS5_signedWeight_record_integral μ w hw hiw T hT ψ hψ hbψ
    have hν := sbxS5_signedWeight_record_integral ν v hv hiv S hS ψ hψ hbψ
    have ht := htest f hf hbf g hg hbg
    change (∫ r, ψ r ∂(μp + νn)) = ∫ r, ψ r ∂(μn + νp)
    rw [integral_add_measure (hbounded μp ψ hψ hbψ) (hbounded νn ψ hψ hbψ),
      integral_add_measure (hbounded μn ψ hψ hbψ) (hbounded νp ψ hψ hbψ)]
    change (∫ r, ψ r ∂μp) - (∫ r, ψ r ∂μn) = _ at hμ
    change (∫ r, ψ r ∂νp) - (∫ r, ψ r ∂νn) = _ at hν
    dsimp only [ψ] at hμ hν
    linarith
  have hμ := sbxS5_signedWeight_record_integral μ w hw hiw T hT Φ hΦ hbΦ
  have hν := sbxS5_signedWeight_record_integral ν v hv hiv S hS Φ hΦ hbΦ
  have heq : (∫ r, Φ r ∂(μp + νn)) = ∫ r, Φ r ∂(μn + νp) := by rw [hbalance]
  rw [integral_add_measure (hbounded μp Φ hΦ hbΦ) (hbounded νn Φ hΦ hbΦ),
    integral_add_measure (hbounded μn Φ hΦ hbΦ) (hbounded νp Φ hΦ hbΦ)] at heq
  change (∫ r, Φ r ∂μp) - (∫ r, Φ r ∂μn) = _ at hμ
  change (∫ r, Φ r ∂νp) - (∫ r, Φ r ∂νn) = _ at hν
  linarith


/-- The actual first-cycle slice factorization for product future tests implies
the same factorization for every bounded full future-record test. -/
theorem sbxS5_firstSliceIdentity_of_productTests
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1) (l δ : ℝ)
    (hl : 0 < l) (hsep : r₀ < 2 * l) (hδ₀ : 0 < δ) (hδ₁ : δ < 1)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K)
    (hscope : node_app_u3A_factorization_u23_coupling_u2D_scopeStmt)
    (hD : annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam)) ≠ 0)
    (n : ℕ) (W : FieldPair d × CoupledSample d → ℝ)
    (hW : Measurable W) (hbW : BoundedRealTest W)
    (htest : ∀ (f : Path d × BernoulliSequence → ℝ), Measurable f → BoundedRealTest f →
      ∀ (g : (FutureHalfSpace d (Renewal.forceCoord hd) (l / lam) → Mat d × ℝ) → ℝ),
        Measurable g → BoundedRealTest g →
      (∫ q in {q | regenerationTime hd lam l 1 q.2 =
          (((n : ℝ≥0) * Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)},
        W q * (f ((regenerationRecord hd lam l 1 q).1,
          (regenerationRecord hd lam l 1 q).2.1) *
            g (regenerationRecord hd lam l 1 q).2.2) ∂annealedCoupledLaw Q.measure K) =
      (∫ q in {q | regenerationTime hd lam l 1 q.2 =
          (((n : ℝ≥0) * Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)},
        W q ∂annealedCoupledLaw Q.measure K) *
      ∫ q, f ((regenerationRecord hd lam l 0 q).1,
        (regenerationRecord hd lam l 0 q).2.1) * g (regenerationRecord hd lam l 0 q).2.2
        ∂regenerationConditionedLaw hd Q lam l K hK.1 hD)
    (Φ : FutureState d (Renewal.forceCoord hd) (l / lam) → ℝ)
    (hΦ : Measurable Φ) (hbΦ : BoundedRealTest Φ) :
    (∫ q in {q | regenerationTime hd lam l 1 q.2 =
        (((n : ℝ≥0) * Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)},
      W q * Φ (regenerationRecord hd lam l 1 q) ∂annealedCoupledLaw Q.measure K) =
    (∫ q in {q | regenerationTime hd lam l 1 q.2 =
        (((n : ℝ≥0) * Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)},
      W q ∂annealedCoupledLaw Q.measure K) *
      ∫ q, Φ (regenerationRecord hd lam l 0 q)
        ∂regenerationConditionedLaw hd Q lam l K hK.1 hD := by
  let μ := annealedCoupledLaw Q.measure K
  let ν := regenerationConditionedLaw hd Q lam l K hK.1 hD
  let ρ := μ.restrict {q | regenerationTime hd lam l 1 q.2 =
    (((n : ℝ≥0) * Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)}
  haveI : IsProbabilityMeasure μ := annealedCoupledLaw_isProbabilityMeasure Q.measure K hK.1
  haveI : IsProbabilityMeasure ν := ProbabilityTheory.cond_isProbabilityMeasure hD
  obtain ⟨C, hC⟩ := hbW
  have hiW : Integrable W ρ := Integrable.of_bound hW.aestronglyMeasurable C
    (Filter.Eventually.of_forall fun q => by simpa only [Real.norm_eq_abs] using hC q)
  have hsc₀ := hscope d hd Λ₀ r₀ Q lam h₀ h₁ l δ hl hsep hδ₀ hδ₁ P K hK hD 0
  have hsc₁ := hscope d hd Λ₀ r₀ Q lam h₀ h₁ l δ hl hsep hδ₀ hδ₁ P K hK hD 1
  have hprod : ∀ (f : Path d × BernoulliSequence → ℝ), Measurable f → BoundedRealTest f →
      ∀ (g : (FutureHalfSpace d (Renewal.forceCoord hd) (l / lam) → Mat d × ℝ) → ℝ),
        Measurable g → BoundedRealTest g →
        (∫ q, W q * (f ((regenerationRecord hd lam l 1 q).1,
          (regenerationRecord hd lam l 1 q).2.1) *
            g (regenerationRecord hd lam l 1 q).2.2) ∂ρ) =
        ∫ q, (∫ x, W x ∂ρ) * (f ((regenerationRecord hd lam l 0 q).1,
          (regenerationRecord hd lam l 0 q).2.1) *
            g (regenerationRecord hd lam l 0 q).2.2) ∂ν := by
    intro f hf hbf g hg hbg
    simpa only [integral_const_mul] using htest f hf hbf g hg hbg
  have ht := sbxS5_signedWeighted_futureTests (Renewal.forceCoord hd) (l / lam)
    ρ ν W (fun _ => ∫ x, W x ∂ρ) hW measurable_const hiW (integrable_const _)
    (regenerationRecord hd lam l 1) (regenerationRecord hd lam l 0)
    hsc₁.2.1 hsc₀.2.1 hprod Φ hΦ hbΦ
  simpa only [integral_const_mul] using ht

/-- Spatial endpoint averaging of a bounded signed joint observation is
integrable, even when the original kernel is only almost everywhere a
probability kernel. -/
theorem sbxS5_integrable_spatial_kernel_average {d : ℕ} {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) [IsProbabilityMeasure μ] (κ : ProbabilityTheory.Kernel α β)
    (hκ : ∀ᵐ a ∂μ, IsProbabilityMeasure (κ a))
    (i : Fin d) (R : ℝ) (hR : 0 < R) (X : β → Vec d) (hX : Measurable X)
    (G : α × β → ℝ) (hG : Measurable G) (hbG : BoundedRealTest G) :
    Integrable (fun p : Vec d × α => ∫ b, G (p.2, b) *
      (if p.1 ∈ endpointBall i R (X b) then 1 else 0) ∂κ p.2)
      (volume.prod μ) := by
  classical
  let κ' := Probability.probabilityPart κ
  let ρ := μ.compProd κ'
  haveI : IsProbabilityMeasure ρ :=
    Probability.isProbabilityMeasure_compProd_probabilityPart μ κ hκ
  let J : (α × β) × Vec d → ℝ := fun q =>
    (endpointBall i R (X q.1.2)).indicator (fun _ => G q.1) q.2
  have hJ : Measurable J := by
    apply (hG.comp measurable_fst).indicator
    exact (measurableSet_endpointBall_pair i R).preimage
      ((hX.comp measurable_fst.snd).prodMk measurable_snd)
  have hiJ : Integrable J (ρ.prod volume) :=
    integrable_endpointBall_indicator ρ i R hR (fun q => X q.2)
      (hX.comp measurable_snd) (fun q => G q.1) (hG.comp measurable_fst)
      (by obtain ⟨C, hC⟩ := hbG; exact ⟨C, fun q => hC q.1⟩)
  obtain ⟨C, hC⟩ := hbG
  have hbJ : ∀ q, ‖J q‖ ≤ max C 0 := by
    intro q
    by_cases hq : q.2 ∈ endpointBall i R (X q.1.2)
    · simpa only [J, Set.indicator_of_mem hq, Real.norm_eq_abs] using
        (hC q.1).trans (le_max_left C 0)
    · simpa only [J, Set.indicator_of_notMem hq, norm_zero] using le_max_right C 0
  let A : Vec d × α → ℝ := fun p => ∫ b, J ((p.2, b), p.1) ∂κ' p.2
  have hA : StronglyMeasurable A := by
    exact (hJ.stronglyMeasurable.comp_measurable
      ((measurable_fst.snd.prodMk measurable_snd).prodMk measurable_fst.fst)).integral_kernel_prod_right'
        (κ := κ'.comap Prod.snd measurable_snd)
  have hiJy : ∀ y, Integrable (fun q : α × β => J (q, y)) ρ := fun y =>
    Integrable.of_bound (hJ.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
      (max C 0) (Filter.Eventually.of_forall fun q => hbJ (q, y))
  have hiNy : ∀ y, Integrable (fun a => ∫ b, ‖J ((a, b), y)‖ ∂κ' a) μ :=
    fun y => ((Measure.integrable_compProd_iff (hiJy y).aestronglyMeasurable).mp (hiJy y)).2
  have hiAy : ∀ y, Integrable (fun a => A (y, a)) μ := by
    intro y
    apply (hiNy y).mono' (hA.comp_measurable measurable_prodMk_left).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun a => norm_integral_le_integral_norm _
  have hiA : Integrable A (volume.prod μ) := by
    apply (integrable_prod_iff hA.aestronglyMeasurable).mpr
    refine ⟨Filter.Eventually.of_forall hiAy, ?_⟩
    apply hiJ.norm.integral_prod_right.mono'
      hA.norm.integral_prod_right'.aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro y
    rw [Real.norm_of_nonneg (integral_nonneg (fun a => norm_nonneg (A (y, a)))),
      Measure.integral_compProd (hiJy y).norm]
    exact integral_mono (hiAy y).norm (hiNy y)
      (fun a => norm_integral_le_integral_norm _)
  apply hiA.congr
  have hae := (Measure.quasiMeasurePreserving_snd (μ := (volume : Measure (Vec d))) (ν := μ)).ae
    (Probability.probabilityPart_ae_eq μ κ hκ)
  filter_upwards [hae] with p hp
  change (∫ b, J ((p.2, b), p.1) ∂κ' p.2) = _
  rw [show κ' p.2 = κ p.2 from hp]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun b => by
    by_cases hb : p.1 ∈ endpointBall i R (X b) <;> simp [J, hb]

/-- The literal signed past factor has a joint spatial integrability
premise for Fubini; no pointwise probability condition is imposed on `K`. -/
theorem sbxS5_integrable_firstSlicePastFactor {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q] (K : CoupledQuenchedLaws d)
    (hK : HasProbabilityLaws Q K) (Δ : ℝ≥0) (lam R : ℝ) (i : Fin d)
    (hR : 0 < R) (m : ℕ) (F : FieldPair d → ℝ)
    (hF : Measurable F) (hbF : BoundedRealTest F)
    (H : CoupledSample d → ℝ) (hH : Measurable H) (hbH : BoundedRealTest H) :
    Integrable (fun p : Vec d × FieldPair d =>
      F p.2 * firstSlicePastIntegral Δ lam R i m K H p) (volume.prod Q) := by
  classical
  let Γ := forcedBitTrialEvent Δ lam R i m
  let G : FieldPair d × CoupledSample d → ℝ := fun q => F q.1 * Γ.indicator H q.2
  have hG : Measurable G := (hF.comp measurable_fst).mul
    ((hH.indicator (measurableSet_forcedBitTrialEvent Δ lam R i m)).comp measurable_snd)
  have hbG : BoundedRealTest G := by
    obtain ⟨CF, hCF⟩ := hbF
    obtain ⟨CH, hCH⟩ := hbH
    refine ⟨max CF 0 * max CH 0, fun q => ?_⟩
    by_cases hq : q.2 ∈ Γ
    · simp only [G, Set.indicator_of_mem hq, abs_mul]
      exact mul_le_mul ((hCF _).trans (le_max_left _ _))
        ((hCH _).trans (le_max_left _ _)) (abs_nonneg _) (le_max_right _ _)
    · simpa only [G, Set.indicator_of_notMem hq, mul_zero, abs_zero] using
        mul_nonneg (le_max_right CF 0) (le_max_right CH 0)
  have hi := sbxS5_integrable_spatial_kernel_average Q (originCoupledLaw K) hK.1
    i R hR (fun z => z.1 ((m : ℝ≥0) * Δ))
    ((continuous_eval_const _).measurable.comp measurable_fst) G hG hbG
  convert hi using 1
  funext p
  dsimp only [firstSlicePastIntegral, originCoupledLaw, ProbabilityTheory.Kernel.comap_apply, G]
  rw [← integral_const_mul]
  congr 1
  funext z
  exact (mul_assoc _ _ _).symm

/-- The two actual endpoint factors have an integrable joint product.
The bounded future version is used only to establish integrability and is
then replaced by the original off-origin expectation almost everywhere. -/
theorem sbxS5_integrable_firstSlicePast_killedFuture {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q] (K : CoupledQuenchedLaws d)
    (hK : HasProbabilityLaws Q K) (Δ : ℝ≥0) (lam R : ℝ) (i : Fin d)
    (hR : 0 < R) (m : ℕ) (F : FieldPair d → ℝ)
    (hF : Measurable F) (hbF : BoundedRealTest F)
    (H : CoupledSample d → ℝ) (hH : Measurable H) (hbH : BoundedRealTest H)
    (Φ : FutureState d i R → ℝ) (hΦ : Measurable Φ) (hbΦ : BoundedRealTest Φ) :
    Integrable (fun p : Vec d × FieldPair d =>
      (F p.2 * firstSlicePastIntegral Δ lam R i m K H p) *
        ∫ z, killedFutureTest R i Φ (p, z) ∂K p) (volume.prod Q) := by
  obtain ⟨C, _, B, hB, hbB, _, heq⟩ :=
    exists_globally_bounded_measurable_killed_future_version Q K hK R i Φ hΦ hbΦ
  have hi := (sbxS5_integrable_firstSlicePastFactor Q K hK Δ lam R i hR m
    F hF hbF H hH hbH).mul_bdd hB.aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => by simpa only [Real.norm_eq_abs] using hbB p)
  apply hi.congr
  filter_upwards [heq] with p hp
  exact congrArg (fun b => (F p.2 * firstSlicePastIntegral Δ lam R i m K H p) * b) hp

/-- Spatial and environment integration commute for the literal signed
endpoint factors, including the original off-origin kernel. -/
theorem sbxS5_firstSlicePast_killedFuture_fubini {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q] (K : CoupledQuenchedLaws d)
    (hK : HasProbabilityLaws Q K) (Δ : ℝ≥0) (lam R : ℝ) (i : Fin d)
    (hR : 0 < R) (m : ℕ) (F : FieldPair d → ℝ)
    (hF : Measurable F) (hbF : BoundedRealTest F)
    (H : CoupledSample d → ℝ) (hH : Measurable H) (hbH : BoundedRealTest H)
    (Φ : FutureState d i R → ℝ) (hΦ : Measurable Φ) (hbΦ : BoundedRealTest Φ) :
    (∫ y, ∫ ω, (F ω * firstSlicePastIntegral Δ lam R i m K H (y, ω)) *
      (∫ z, killedFutureTest R i Φ ((y, ω), z) ∂K (y, ω)) ∂Q) =
    ∫ ω, ∫ y, (F ω * firstSlicePastIntegral Δ lam R i m K H (y, ω)) *
      (∫ z, killedFutureTest R i Φ ((y, ω), z) ∂K (y, ω)) ∂volume ∂Q := by
  exact integral_integral_swap (sbxS5_integrable_firstSlicePast_killedFuture Q K hK
    Δ lam R i hR m F hF hbF H hH hbH Φ hΦ hbΦ)


/-- Integrating the moving endpoint ball produces its translation-invariant
volume times the original joint observation, with the actual kernel retained. -/
theorem sbxS5_spatial_kernel_average_integral {d : ℕ} {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) [IsProbabilityMeasure μ] (κ : ProbabilityTheory.Kernel α β)
    (hκ : ∀ᵐ a ∂μ, IsProbabilityMeasure (κ a))
    (i : Fin d) (R : ℝ) (hR : 0 < R) (X : β → Vec d) (hX : Measurable X)
    (G : α × β → ℝ) (hG : Measurable G) (hbG : BoundedRealTest G) :
    (∫ y, ∫ a, ∫ b, G (a, b) *
      (if y ∈ endpointBall i R (X b) then 1 else 0) ∂κ a ∂μ) =
      (volume (endpointBall i R 0)).toReal * ∫ a, ∫ b, G (a, b) ∂κ a ∂μ := by
  classical
  let ρ := μ.compProd (Probability.probabilityPart κ)
  have : IsProbabilityMeasure ρ :=
    Probability.isProbabilityMeasure_compProd_probabilityPart μ κ hκ
  let J : (α × β) × Vec d → ℝ := fun q =>
    (endpointBall i R (X q.1.2)).indicator (fun _ => G q.1) q.2
  have hJ : Measurable J := by
    apply (hG.comp measurable_fst).indicator
    exact (measurableSet_endpointBall_pair i R).preimage
      ((hX.comp measurable_fst.snd).prodMk measurable_snd)
  have hiJ : Integrable J (ρ.prod volume) :=
    integrable_endpointBall_indicator ρ i R hR (fun q => X q.2)
      (hX.comp measurable_snd) (fun q => G q.1) (hG.comp measurable_fst)
      (by obtain ⟨C, hC⟩ := hbG; exact ⟨C, fun q => hC q.1⟩)
  obtain ⟨C, hC⟩ := hbG
  have hbJ : ∀ y, BoundedRealTest (fun q : α × β => J (q, y)) := by
    intro y
    refine ⟨max C 0, fun q => ?_⟩
    by_cases hq : y ∈ endpointBall i R (X q.2)
    · simpa only [J, Set.indicator_of_mem hq] using
        (hC q).trans (le_max_left C 0)
    · simpa only [J, Set.indicator_of_notMem hq, abs_zero] using le_max_right C 0
  have hiter : ∀ y, (∫ q, J (q, y) ∂ρ) =
      ∫ a, ∫ b, G (a, b) *
        (if y ∈ endpointBall i R (X b) then 1 else 0) ∂κ a ∂μ := by
    intro y
    calc
      _ = ∫ a, ∫ b, J ((a, b), y) ∂κ a ∂μ :=
        Probability.integral_compProd_probabilityPart μ κ hκ (fun q => J (q, y))
          (hJ.comp (measurable_id.prodMk measurable_const)) (hbJ y)
      _ = _ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun a => integral_congr_ae
          (Filter.Eventually.of_forall fun b => by
            by_cases hb : y ∈ endpointBall i R (X b) <;> simp [J, hb])
  calc
    _ = ∫ y, ∫ q, J (q, y) ∂ρ := integral_congr_ae
      (Filter.Eventually.of_forall fun y => (hiter y).symm)
    _ = ∫ q, ∫ y, J (q, y) ∂volume ∂ρ := (integral_integral_swap hiJ).symm
    _ = ∫ q, (volume (endpointBall i R 0)).toReal * G q ∂ρ := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro q
      have hball : MeasurableSet (endpointBall i R (X q.2)) :=
        (measurableSet_endpointBall_pair i R).preimage
          (measurable_const.prodMk measurable_id)
      simp only [J, integral_indicator hball, integral_const, smul_eq_mul,
        Measure.real, Measure.restrict_apply_univ, endpointBall_volume_eq]
    _ = (volume (endpointBall i R 0)).toReal * ∫ q, G q ∂ρ := integral_const_mul _ _
    _ = _ := by
      rw [Probability.integral_compProd_probabilityPart μ κ hκ G hG ⟨C, hC⟩]

/-- The spatial integral of the actual signed past factor has exactly the
endpoint-ball volume normalization and the actual forced-event annealed law. -/
theorem sbxS5_firstSlicePastFactor_spatial_integral {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q] (K : CoupledQuenchedLaws d)
    (hK : HasProbabilityLaws Q K) (Δ : ℝ≥0) (lam R : ℝ) (i : Fin d)
    (hR : 0 < R) (m : ℕ) (F : FieldPair d → ℝ)
    (hF : Measurable F) (hbF : BoundedRealTest F)
    (H : CoupledSample d → ℝ) (hH : Measurable H) (hbH : BoundedRealTest H) :
    (∫ y, ∫ ω, F ω * firstSlicePastIntegral Δ lam R i m K H (y, ω) ∂Q) =
      (volume (endpointBall i R 0)).toReal *
        ∫ q, F q.1 * ((forcedBitTrialEvent Δ lam R i m).indicator H) q.2
          ∂annealedCoupledLaw Q K := by
  classical
  let Γ := forcedBitTrialEvent Δ lam R i m
  let G : FieldPair d × CoupledSample d → ℝ := fun q => F q.1 * Γ.indicator H q.2
  have hG : Measurable G := (hF.comp measurable_fst).mul
    ((hH.indicator (measurableSet_forcedBitTrialEvent Δ lam R i m)).comp measurable_snd)
  have hbG : BoundedRealTest G := by
    obtain ⟨CF, hCF⟩ := hbF
    obtain ⟨CH, hCH⟩ := hbH
    refine ⟨max CF 0 * max CH 0, fun q => ?_⟩
    by_cases hq : q.2 ∈ Γ
    · simp only [G, Set.indicator_of_mem hq, abs_mul]
      exact mul_le_mul ((hCF _).trans (le_max_left _ _))
        ((hCH _).trans (le_max_left _ _)) (abs_nonneg _) (le_max_right _ _)
    · simpa only [G, Set.indicator_of_notMem hq, mul_zero, abs_zero] using
        mul_nonneg (le_max_right CF 0) (le_max_right CH 0)
  rw [integral_annealedCoupledLaw Q K hK G hG hbG]
  have hi := sbxS5_spatial_kernel_average_integral Q (originCoupledLaw K) hK.1
    i R hR (fun z => z.1 ((m : ℝ≥0) * Δ))
    ((continuous_eval_const _).measurable.comp measurable_fst) G hG hbG
  convert hi using 1
  · congr 1
    funext y
    congr 1
    funext ω
    dsimp only [firstSlicePastIntegral, originCoupledLaw, ProbabilityTheory.Kernel.comap_apply, G]
    rw [← integral_const_mul]
    congr 1
    funext z
    exact (mul_assoc _ _ _).symm
  · rfl


/-- The same normalization holds on the nonzero endpoint half-space. The
excluded endpoints contribute zero by the supplied actual slice geometry. -/
theorem sbxS5_firstSlicePastFactor_spatial_integral_above {d : ℕ}
    (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1) (l δ : ℝ)
    (hl : 0 < l) (hsep : r₀ < 2 * l) (hδ₀ : 0 < δ) (hδ₁ : δ < 1)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K)
    (hslices : node_app_u3A_factorization_u23_slicesStmt)
    (F : FieldPair d → ℝ)
    (hF : Measurable[localSigma {x : Vec d | euclideanNorm x < l / lam}] F)
    (hbF : BoundedRealTest F) (n : ℕ) (hn : 2 ≤ n) (H : CoupledSample d → ℝ)
    (hH : Measurable[finiteHistorySigma (Renewal.regenDelta lam) (n - 1)] H)
    (hbH : BoundedRealTest H) :
    (∫ y in {y : Vec d | 10 * (l / lam) ≤ y (Renewal.forceCoord hd)},
      ∫ ω, F ω * firstSlicePastIntegral (Renewal.regenDelta lam) lam (l / lam)
        (Renewal.forceCoord hd) (n - 1) K H (y, ω) ∂Q.measure) =
      (volume (endpointBall (Renewal.forceCoord hd) (l / lam) 0)).toReal *
        ∫ q, F q.1 * ((forcedBitTrialEvent (Renewal.regenDelta lam) lam (l / lam)
          (Renewal.forceCoord hd) (n - 1)).indicator H) q.2
            ∂annealedCoupledLaw Q.measure K := by
  let A : Vec d → ℝ := fun y => ∫ ω, F ω *
    firstSlicePastIntegral (Renewal.regenDelta lam) lam (l / lam)
      (Renewal.forceCoord hd) (n - 1) K H (y, ω) ∂Q.measure
  have hz : ∀ y, y (Renewal.forceCoord hd) < 10 * (l / lam) → A y = 0 := by
    intro y hy
    apply integral_eq_zero_of_ae
    filter_upwards [sbxS5_firstSlicePast_zero hd Q lam h₀ h₁ l δ hl hsep hδ₀ hδ₁
      P K hK hslices n hn H y hy] with ω hω
    simp only [Pi.zero_apply] at hω
    simp only [hω, mul_zero, Pi.zero_apply]
  have hhalf : MeasurableSet {y : Vec d | 10 * (l / lam) ≤ y (Renewal.forceCoord hd)} :=
    measurableSet_le measurable_const (measurable_pi_apply _)
  calc
    _ = ∫ y, A y := by
      rw [← integral_indicator hhalf]
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro y
      change ({y : Vec d | 10 * (l / lam) ≤ y (Renewal.forceCoord hd)}).indicator A y = A y
      by_cases hy : y ∈ {y : Vec d | 10 * (l / lam) ≤ y (Renewal.forceCoord hd)}
      · exact Set.indicator_of_mem hy A
      · rw [Set.indicator_of_notMem hy, hz y (lt_of_not_ge hy)]
    _ = _ := sbxS5_firstSlicePastFactor_spatial_integral Q.measure K hK.1
      (Renewal.regenDelta lam) lam (l / lam) (Renewal.forceCoord hd) (div_pos hl h₀)
      (n - 1) F (hF.mono (Probability.localSigma_le_borel _) le_rfl) hbF H
      (hH.mono (Probability.finiteHistorySigma_le _ _) le_rfl) hbH


section ShiftedOrigin

variable {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1) (l δ : ℝ)
    (hl : 0 < l) (hsep : r₀ < 2 * l) (hδ₀ : 0 < δ) (hδ₁ : δ < 1)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K)

include hK hl hsep hδ₀ hδ₁

/-- The supplied origin future version translates to the corrected future
half-space and retains its mean by stationarity. This statement concerns the
translated origin law explicitly; identifying it with the off-origin law
requires the separate covariance producer. -/
theorem sbxS5_shiftedOriginFuture_local_mean
    (hfuture : node_app_u3A_factorization_u23_future_u2D_kernelStmt)
    (Φ : FutureState d (Renewal.forceCoord hd) (l / lam) → ℝ)
    (hΦ : Measurable Φ) (hbΦ : BoundedRealTest Φ) (y : Vec d) :
    ∃ B' : FieldPair d → ℝ,
      Measurable[localSigma {x : Vec d |
        y (Renewal.forceCoord hd) - 2 * (l / lam) ≤ x (Renewal.forceCoord hd)}] B' ∧
      (fun ω => ∫ z, killedFutureTest (l / lam) (Renewal.forceCoord hd) Φ
        ((0, translate y ω), z) ∂K (0, translate y ω)) =ᵐ[Q.measure] B' ∧
      (∫ ω, ∫ z, killedFutureTest (l / lam) (Renewal.forceCoord hd) Φ
        ((0, translate y ω), z) ∂K (0, translate y ω) ∂Q.measure) =
        ∫ ω, ∫ z, killedFutureTest (l / lam) (Renewal.forceCoord hd) Φ
          ((0, ω), z) ∂K (0, ω) ∂Q.measure := by
  obtain ⟨B, hB, hBo⟩ :=
    hfuture d hd Λ₀ r₀ Q lam h₀ h₁ l δ hl hsep hδ₀ hδ₁ P K hK Φ hΦ hbΦ
  have hmap : ∀ᵐ ω ∂Measure.map (translate y) Q.measure,
      (∫ z, killedFutureTest (l / lam) (Renewal.forceCoord hd) Φ
        ((0, ω), z) ∂K (0, ω)) = B ω := by
    rw [Q.stationary y]
    exact hBo
  have ht := ae_of_ae_map (Probability.measurable_translate y).aemeasurable hmap
  refine ⟨fun ω => B (translate y ω), ?_, ht, ?_⟩
  · apply (hB.comp (Probability.measurable_translate_local y _)).mono
      (Probability.localSigma_mono ?_) le_rfl
    rintro x ⟨z, hz, rfl⟩
    change -2 * (l / lam) ≤ z (Renewal.forceCoord hd) at hz
    change y (Renewal.forceCoord hd) - 2 * (l / lam) ≤ (y + z) (Renewal.forceCoord hd)
    simp only [Pi.add_apply]
    linarith
  · have hBg : Measurable B := hB.mono (Probability.localSigma_le_borel _) le_rfl
    rw [integral_congr_ae ht,
      ← integral_map (Probability.measurable_translate y).aemeasurable hBg.aestronglyMeasurable,
      Q.stationary y]
    exact integral_congr_ae hBo.symm

/-- Actual past factors are independent of the translated origin future
expectation under the genuine joint finite-range law. The normalization uses
the actual no-return probability and conditioned origin record. -/
theorem sbxS5_firstSlicePast_shiftedOriginFuture_factorization
    (hpast : node_app_u3A_factorization_u23_past_u2D_kernelStmt)
    (hfuture : node_app_u3A_factorization_u23_future_u2D_kernelStmt)
    (hD : annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam)) ≠ 0)
    (Φ : FutureState d (Renewal.forceCoord hd) (l / lam) → ℝ)
    (hΦ : Measurable Φ) (hbΦ : BoundedRealTest Φ)
    (F : FieldPair d → ℝ)
    (hF : Measurable[localSigma {x : Vec d | euclideanNorm x < l / lam}] F)
    (m : ℕ) (H : CoupledSample d → ℝ)
    (hH : Measurable[finiteHistorySigma (Renewal.regenDelta lam) m] H)
    (hbH : BoundedRealTest H) (y : Vec d)
    (hy : 10 * (l / lam) ≤ y (Renewal.forceCoord hd)) :
    (∫ ω, (F ω * firstSlicePastIntegral (Renewal.regenDelta lam) lam (l / lam)
      (Renewal.forceCoord hd) m K H (y, ω)) *
      (∫ z, killedFutureTest (l / lam) (Renewal.forceCoord hd) Φ
        ((0, translate y ω), z) ∂K (0, translate y ω)) ∂Q.measure) =
      (∫ ω, F ω * firstSlicePastIntegral (Renewal.regenDelta lam) lam (l / lam)
        (Renewal.forceCoord hd) m K H (y, ω) ∂Q.measure) *
      ((annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam))).toReal *
        ∫ q, Φ (regenerationRecord hd lam l 0 q)
          ∂regenerationConditionedLaw hd Q lam l K hK.1 hD) := by
  obtain ⟨A', hA', hAe⟩ := sbxS5_pastFactor_local hd Q lam h₀ h₁ l δ hl hsep hδ₀ hδ₁
    P K hK hpast F hF m H hH hbH y hy
  obtain ⟨B', hB', hBe, hmean⟩ := sbxS5_shiftedOriginFuture_local_mean
    hd Q lam h₀ h₁ l δ hl hsep hδ₀ hδ₁ P K hK hfuture Φ hΦ hbΦ y
  rw [integral_mul_eq_of_corrected_halfSpace_versions Q (Renewal.forceCoord hd)
    (y (Renewal.forceCoord hd)) (l / lam) (sbxS5_radius_gap hl h₀ h₁ hsep)
    _ _ A' B' hA' hB' hAe hBe, hmean,
    sbxS5_killedFuture_origin_mean hd Q lam h₀ h₁ l δ P K hK hD Φ hΦ hbΦ]


/-- Spatial integration of the actual past factor against the translated
origin future expectation gives the literal volume and no-return factors.
The off-origin coupled law does not occur in this comparison formula. -/
theorem sbxS5_firstSlicePast_shiftedOriginFuture_spatial_integral
    (hpast : node_app_u3A_factorization_u23_past_u2D_kernelStmt)
    (hfuture : node_app_u3A_factorization_u23_future_u2D_kernelStmt)
    (hslices : node_app_u3A_factorization_u23_slicesStmt)
    (hD : annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam)) ≠ 0)
    (Φ : FutureState d (Renewal.forceCoord hd) (l / lam) → ℝ)
    (hΦ : Measurable Φ) (hbΦ : BoundedRealTest Φ)
    (F : FieldPair d → ℝ)
    (hF : Measurable[localSigma {x : Vec d | euclideanNorm x < l / lam}] F)
    (hbF : BoundedRealTest F) (n : ℕ) (hn : 2 ≤ n) (H : CoupledSample d → ℝ)
    (hH : Measurable[finiteHistorySigma (Renewal.regenDelta lam) (n - 1)] H)
    (hbH : BoundedRealTest H) :
    (∫ y, ∫ ω, (F ω * firstSlicePastIntegral (Renewal.regenDelta lam) lam (l / lam)
      (Renewal.forceCoord hd) (n - 1) K H (y, ω)) *
      (∫ z, killedFutureTest (l / lam) (Renewal.forceCoord hd) Φ
        ((0, translate y ω), z) ∂K (0, translate y ω)) ∂Q.measure) =
      ((volume (endpointBall (Renewal.forceCoord hd) (l / lam) 0)).toReal *
        ∫ q, F q.1 * ((forcedBitTrialEvent (Renewal.regenDelta lam) lam (l / lam)
          (Renewal.forceCoord hd) (n - 1)).indicator H) q.2
            ∂annealedCoupledLaw Q.measure K) *
      ((annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam))).toReal *
        ∫ q, Φ (regenerationRecord hd lam l 0 q)
          ∂regenerationConditionedLaw hd Q lam l K hK.1 hD) := by
  let A : Vec d → FieldPair d → ℝ := fun y ω => F ω *
    firstSlicePastIntegral (Renewal.regenDelta lam) lam (l / lam)
      (Renewal.forceCoord hd) (n - 1) K H (y, ω)
  let B : Vec d → FieldPair d → ℝ := fun y ω =>
    ∫ z, killedFutureTest (l / lam) (Renewal.forceCoord hd) Φ
      ((0, translate y ω), z) ∂K (0, translate y ω)
  let c := (annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam))).toReal *
    ∫ q, Φ (regenerationRecord hd lam l 0 q)
      ∂regenerationConditionedLaw hd Q lam l K hK.1 hD
  have heq : ∀ y, (∫ ω, A y ω * B y ω ∂Q.measure) =
      (∫ ω, A y ω ∂Q.measure) * c := by
    intro y
    by_cases hy : 10 * (l / lam) ≤ y (Renewal.forceCoord hd)
    · exact sbxS5_firstSlicePast_shiftedOriginFuture_factorization
        hd Q lam h₀ h₁ l δ hl hsep hδ₀ hδ₁ P K hK hpast hfuture hD
        Φ hΦ hbΦ F hF (n - 1) H hH hbH y hy
    · have hAz : A y =ᵐ[Q.measure] 0 := by
        filter_upwards [sbxS5_firstSlicePast_zero hd Q lam h₀ h₁ l δ hl hsep hδ₀ hδ₁
          P K hK hslices n hn H y (lt_of_not_ge hy)] with ω hω
        simp only [Pi.zero_apply] at hω ⊢
        change F ω * _ = 0
        rw [hω, mul_zero]
      have hA0 : (∫ ω, A y ω ∂Q.measure) = 0 := integral_eq_zero_of_ae hAz
      have hAB0 : (∫ ω, A y ω * B y ω ∂Q.measure) = 0 := by
        apply integral_eq_zero_of_ae
        filter_upwards [hAz] with ω hω
        simp only [Pi.zero_apply] at hω ⊢
        rw [hω, zero_mul]
      rw [hA0, hAB0, zero_mul]
  calc
    _ = ∫ y, (∫ ω, A y ω ∂Q.measure) * c := integral_congr_ae
      (Filter.Eventually.of_forall heq)
    _ = (∫ y, ∫ ω, A y ω ∂Q.measure) * c := integral_mul_const _ _
    _ = _ := congrArg (fun t => t * c)
      (sbxS5_firstSlicePastFactor_spatial_integral Q.measure K hK.1
        (Renewal.regenDelta lam) lam (l / lam) (Renewal.forceCoord hd) (div_pos hl h₀)
        (n - 1) F (hF.mono (Probability.localSigma_le_borel _) le_rfl) hbF H
        (hH.mono (Probability.finiteHistorySigma_le _ _) le_rfl) hbH)

end ShiftedOrigin

/-- The translated-origin comparison term is jointly integrable. Stationarity
transports the separate origin version; no off-origin covariance is used. -/
theorem sbxS5_integrable_firstSlicePast_shiftedOriginFuture {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q] (hQ : IsStationary Q)
    (K : CoupledQuenchedLaws d) (hK : HasProbabilityLaws Q K)
    (Δ : ℝ≥0) (lam R : ℝ) (i : Fin d) (hR : 0 < R) (m : ℕ)
    (F : FieldPair d → ℝ) (hF : Measurable F) (hbF : BoundedRealTest F)
    (H : CoupledSample d → ℝ) (hH : Measurable H) (hbH : BoundedRealTest H)
    (Φ : FutureState d i R → ℝ) (hΦ : Measurable Φ) (hbΦ : BoundedRealTest Φ) :
    Integrable (fun p : Vec d × FieldPair d =>
      (F p.2 * firstSlicePastIntegral Δ lam R i m K H p) *
        ∫ z, killedFutureTest R i Φ ((0, translate p.1 p.2), z)
          ∂K (0, translate p.1 p.2)) (volume.prod Q) := by
  obtain ⟨C, _, B, hB, hbB, hBo, _⟩ :=
    exists_globally_bounded_measurable_killed_future_version Q K hK R i Φ hΦ hbΦ
  have htrans : Measure.QuasiMeasurePreserving
      (fun p : Vec d × FieldPair d => translate p.1 p.2) (volume.prod Q) Q :=
    MeasureTheory.QuasiMeasurePreserving.prod_of_right Probability.continuous_translate.measurable
      (Filter.Eventually.of_forall fun y =>
        (measurePreserving_translate Q hQ y).quasiMeasurePreserving)
  have ht := htrans.ae hBo
  have hm : Measurable (fun p : Vec d × FieldPair d => B (0, translate p.1 p.2)) :=
    hB.comp (measurable_const.prodMk Probability.continuous_translate.measurable)
  have hi := (sbxS5_integrable_firstSlicePastFactor Q K hK Δ lam R i hR m
    F hF hbF H hH hbH).mul_bdd hm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => by
        simpa only [Real.norm_eq_abs] using hbB (0, translate p.1 p.2))
  apply hi.congr
  filter_upwards [ht] with p hp
  exact congrArg (fun b => (F p.2 * firstSlicePastIntegral Δ lam R i m K H p) * b) hp

section EndpointDifference

variable {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1) (l δ : ℝ)
    (hl : 0 < l) (hsep : r₀ < 2 * l) (hδ₀ : 0 < δ) (hδ₁ : δ < 1)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K)

include hK hl hsep hδ₀ hδ₁

/-- The actual spatial endpoint integral splits into the normalized
translated-origin term and an integrable, literal off-origin difference.
No equality between these two kernel versions is assumed. -/
theorem sbxS5_firstSlicePast_killedFuture_spatial_difference
    (hpast : node_app_u3A_factorization_u23_past_u2D_kernelStmt)
    (hfuture : node_app_u3A_factorization_u23_future_u2D_kernelStmt)
    (hslices : node_app_u3A_factorization_u23_slicesStmt)
    (hD : annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam)) ≠ 0)
    (Φ : FutureState d (Renewal.forceCoord hd) (l / lam) → ℝ)
    (hΦ : Measurable Φ) (hbΦ : BoundedRealTest Φ)
    (F : FieldPair d → ℝ)
    (hF : Measurable[localSigma {x : Vec d | euclideanNorm x < l / lam}] F)
    (hbF : BoundedRealTest F) (n : ℕ) (hn : 2 ≤ n) (H : CoupledSample d → ℝ)
    (hH : Measurable[finiteHistorySigma (Renewal.regenDelta lam) (n - 1)] H)
    (hbH : BoundedRealTest H) :
    let A := fun (y : Vec d) (ω : FieldPair d) => F ω *
      firstSlicePastIntegral (Renewal.regenDelta lam) lam (l / lam)
        (Renewal.forceCoord hd) (n - 1) K H (y, ω)
    let B := fun (y : Vec d) (ω : FieldPair d) =>
      ∫ z, killedFutureTest (l / lam) (Renewal.forceCoord hd) Φ ((y, ω), z) ∂K (y, ω)
    let B₀ := fun (y : Vec d) (ω : FieldPair d) =>
      ∫ z, killedFutureTest (l / lam) (Renewal.forceCoord hd) Φ
        ((0, translate y ω), z) ∂K (0, translate y ω)
    (∫ y, ∫ ω, A y ω * B y ω ∂Q.measure) =
      ((volume (endpointBall (Renewal.forceCoord hd) (l / lam) 0)).toReal *
        ∫ q, F q.1 * ((forcedBitTrialEvent (Renewal.regenDelta lam) lam (l / lam)
          (Renewal.forceCoord hd) (n - 1)).indicator H) q.2
            ∂annealedCoupledLaw Q.measure K) *
      ((annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam))).toReal *
        ∫ q, Φ (regenerationRecord hd lam l 0 q)
          ∂regenerationConditionedLaw hd Q lam l K hK.1 hD) +
      ∫ y, ∫ ω, A y ω * (B y ω - B₀ y ω) ∂Q.measure := by
  intro A B B₀
  have hFg : Measurable F := hF.mono (Probability.localSigma_le_borel _) le_rfl
  have hHg : Measurable H := hH.mono (Probability.finiteHistorySigma_le _ _) le_rfl
  have hi := sbxS5_integrable_firstSlicePast_killedFuture Q.measure K hK.1
    (Renewal.regenDelta lam) lam (l / lam) (Renewal.forceCoord hd) (div_pos hl h₀)
    (n - 1) F hFg hbF H hHg hbH Φ hΦ hbΦ
  have hi₀ := sbxS5_integrable_firstSlicePast_shiftedOriginFuture Q.measure Q.stationary
    K hK.1 (Renewal.regenDelta lam) lam (l / lam) (Renewal.forceCoord hd) (div_pos hl h₀)
    (n - 1) F hFg hbF H hHg hbH Φ hΦ hbΦ
  have hdiff : (∫ y, ∫ ω, A y ω * (B y ω - B₀ y ω) ∂Q.measure) =
      (∫ y, ∫ ω, A y ω * B y ω ∂Q.measure) -
      ∫ y, ∫ ω, A y ω * B₀ y ω ∂Q.measure := by
    simpa only [mul_sub] using integral_integral_sub hi hi₀
  calc
    _ = (∫ y, ∫ ω, A y ω * B₀ y ω ∂Q.measure) +
        ∫ y, ∫ ω, A y ω * (B y ω - B₀ y ω) ∂Q.measure := by rw [hdiff]; ring
    _ = _ := by
      rw [sbxS5_firstSlicePast_shiftedOriginFuture_spatial_integral
        hd Q lam h₀ h₁ l δ hl hsep hδ₀ hδ₁ P K hK hpast hfuture hslices hD
        Φ hΦ hbΦ F hF hbF n hn H hH hbH]

/-- Endpoint disintegration and joint finite-range independence give the
actual product-test slice integral with an explicit off-origin remainder.
The coefficient is the literal successful-coin probability divided by the
positive Euclidean ball volume. -/
theorem sbxS5_productSlice_endpoint_difference
    (hendpoint : node_app_u3A_factorization_u23_endpoint_u2D_disintegrationStmt)
    (hpast : node_app_u3A_factorization_u23_past_u2D_kernelStmt)
    (hfuture : node_app_u3A_factorization_u23_future_u2D_kernelStmt)
    (hslices : node_app_u3A_factorization_u23_slicesStmt)
    (hD : annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam)) ≠ 0)
    (F : FieldPair d → ℝ)
    (hF : Measurable[localSigma {x : Vec d | euclideanNorm x < l / lam}] F)
    (hbF : BoundedRealTest F) (n : ℕ) (hn : 2 ≤ n) (H : CoupledSample d → ℝ)
    (hH : Measurable[finiteHistorySigma (Renewal.regenDelta lam) (n - 1)] H)
    (hbH : BoundedRealTest H)
    (f : Path d × BernoulliSequence → ℝ) (hf : Measurable f) (hbf : BoundedRealTest f)
    (g : (FutureHalfSpace d (Renewal.forceCoord hd) (l / lam) → Mat d × ℝ) → ℝ)
    (hg : Measurable g) (hbg : BoundedRealTest g) :
    let Φ := fun r : FutureState d (Renewal.forceCoord hd) (l / lam) =>
      f (r.1, r.2.1) * g r.2.2
    let A := fun (y : Vec d) (ω : FieldPair d) => F ω *
      firstSlicePastIntegral (Renewal.regenDelta lam) lam (l / lam)
        (Renewal.forceCoord hd) (n - 1) K H (y, ω)
    let B := fun (y : Vec d) (ω : FieldPair d) =>
      ∫ z, killedFutureTest (l / lam) (Renewal.forceCoord hd) Φ ((y, ω), z) ∂K (y, ω)
    let B₀ := fun (y : Vec d) (ω : FieldPair d) =>
      ∫ z, killedFutureTest (l / lam) (Renewal.forceCoord hd) Φ
        ((0, translate y ω), z) ∂K (0, translate y ω)
    (∫ q in {q | regenerationTime hd lam l 1 q.2 =
        (((n : ℝ≥0) * Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)},
      F q.1 * H q.2 * Φ (regenerationRecord hd lam l 1 q)
        ∂annealedCoupledLaw Q.measure K) =
      δ * (∫ q, F q.1 * ((forcedBitTrialEvent (Renewal.regenDelta lam) lam (l / lam)
          (Renewal.forceCoord hd) (n - 1)).indicator H) q.2
            ∂annealedCoupledLaw Q.measure K) *
        ((annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam))).toReal *
          ∫ q, Φ (regenerationRecord hd lam l 0 q)
            ∂regenerationConditionedLaw hd Q lam l K hK.1 hD) +
      (δ / (volume (endpointBall (Renewal.forceCoord hd) (l / lam) 0)).toReal) *
        ∫ y, ∫ ω, A y ω * (B y ω - B₀ y ω) ∂Q.measure := by
  intro Φ A B B₀
  have hΦ : Measurable Φ :=
    (hf.comp (measurable_fst.prodMk measurable_snd.fst)).mul
      (hg.comp measurable_snd.snd)
  have hbΦ : BoundedRealTest Φ := by
    obtain ⟨Cf, hCf⟩ := hbf
    obtain ⟨Cg, hCg⟩ := hbg
    refine ⟨max Cf 0 * max Cg 0, fun r => ?_⟩
    simp only [Φ, abs_mul]
    exact mul_le_mul ((hCf _).trans (le_max_left _ _))
      ((hCg _).trans (le_max_left _ _)) (abs_nonneg _) (le_max_right _ _)
  have hV : (volume (endpointBall (Renewal.forceCoord hd) (l / lam) (0 : Vec d))).toReal ≠ 0 :=
    ENNReal.toReal_ne_zero.mpr
      ⟨(endpointBall_volume_pos _ _ (div_pos hl h₀) _).ne',
        endpointBall_volume_ne_top _ _ (div_pos hl h₀) _⟩
  rw [hendpoint d hd Λ₀ r₀ Q lam h₀ h₁ l δ hl hsep hδ₀ hδ₁ P K hK
    F hF hbF n hn H hH hbH f hf hbf g hg hbg]
  rw [sbxS5_firstSlicePast_killedFuture_spatial_difference
    hd Q lam h₀ h₁ l δ hl hsep hδ₀ hδ₁ P K hK hpast hfuture hslices hD
    Φ hΦ hbΦ F hF hbF n hn H hH hbH]
  field_simp
  <;> ring

end EndpointDifference

/-- An integrable signed spatial weight remains integrable after adjoining
an almost-everywhere probability kernel. Exceptional fibres are normalized
only in the integration measure. -/
theorem sbxS5_integrable_kernelLift {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) [SFinite μ] (κ : ProbabilityTheory.Kernel α β)
    (hκ : ∀ᵐ a ∂μ, IsProbabilityMeasure (κ a))
    (w : α → ℝ) (hw : Measurable w) (hiw : Integrable w μ) :
    Integrable (fun p : α × β => w p.1)
      (μ.compProd (Probability.probabilityPart κ)) := by
  apply (Measure.integrable_compProd_iff
    (hw.comp measurable_fst).aestronglyMeasurable).mpr
  refine ⟨Filter.Eventually.of_forall (fun a => ?_), ?_⟩
  · exact integrable_const (μ := Probability.probabilityPart κ a) (w a)
  · apply hiw.norm.congr
    filter_upwards [hκ, Probability.probabilityPart_ae_eq μ κ hκ] with a ha heq
    letI := ha
    rw [heq]
    change ‖w a‖ = ∫ b, ‖w a‖ ∂κ a
    simp only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]

/-- Integration against the normalized joint kernel law recovers the
literal quenched integral for an integrable signed weight and a bounded
measurable joint observation. -/
theorem sbxS5_signedWeight_kernel_integral {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) [SFinite μ] (κ : ProbabilityTheory.Kernel α β)
    (hκ : ∀ᵐ a ∂μ, IsProbabilityMeasure (κ a))
    (w : α → ℝ) (hw : Measurable w) (hiw : Integrable w μ)
    (G : α × β → ℝ) (hG : Measurable G) (hbG : BoundedRealTest G) :
    (∫ p, w p.1 * G p ∂μ.compProd (Probability.probabilityPart κ)) =
      ∫ a, w a * (∫ b, G (a, b) ∂κ a) ∂μ := by
  obtain ⟨C, hC⟩ := hbG
  have hi := (sbxS5_integrable_kernelLift μ κ hκ w hw hiw).mul_bdd
    hG.aestronglyMeasurable
    (Filter.Eventually.of_forall fun p => by simpa only [Real.norm_eq_abs] using hC p)
  rw [Measure.integral_compProd hi]
  apply integral_congr_ae
  filter_upwards [Probability.probabilityPart_ae_eq μ κ hκ] with a ha
  rw [ha, integral_const_mul]

/-- Endpoint disintegration extends from product tests to every bounded
measurable test of the entire future record, retaining the actual off-origin
kernel and its spatial integral. -/
theorem sbxS5_endpointDisintegration_fullFuture
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1) (l δ : ℝ)
    (hl : 0 < l) (hsep : r₀ < 2 * l) (hδ₀ : 0 < δ) (hδ₁ : δ < 1)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K)
    (hendpoint : node_app_u3A_factorization_u23_endpoint_u2D_disintegrationStmt)
    (hscope : node_app_u3A_factorization_u23_coupling_u2D_scopeStmt)
    (hD : annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam)) ≠ 0)
    (F : FieldPair d → ℝ)
    (hF : Measurable[localSigma {x : Vec d | euclideanNorm x < l / lam}] F)
    (hbF : BoundedRealTest F) (n : ℕ) (hn : 2 ≤ n) (H : CoupledSample d → ℝ)
    (hH : Measurable[finiteHistorySigma (Renewal.regenDelta lam) (n - 1)] H)
    (hbH : BoundedRealTest H)
    (Φ : FutureState d (Renewal.forceCoord hd) (l / lam) → ℝ)
    (hΦ : Measurable Φ) (hbΦ : BoundedRealTest Φ) :
    (∫ q in {q | regenerationTime hd lam l 1 q.2 =
        (((n : ℝ≥0) * Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)},
      F q.1 * H q.2 * Φ (regenerationRecord hd lam l 1 q)
        ∂annealedCoupledLaw Q.measure K) =
      (δ / (volume (endpointBall (Renewal.forceCoord hd) (l / lam) 0)).toReal) *
        ∫ y, ∫ ω, (F ω * firstSlicePastIntegral (Renewal.regenDelta lam) lam (l / lam)
          (Renewal.forceCoord hd) (n - 1) K H (y, ω)) *
            (∫ z, killedFutureTest (l / lam) (Renewal.forceCoord hd) Φ
              ((y, ω), z) ∂K (y, ω)) ∂Q.measure := by
  classical
  let R := l / lam
  let i := Renewal.forceCoord hd
  let c := δ / (volume (endpointBall i R (0 : Vec d))).toReal
  let μ := annealedCoupledLaw Q.measure K
  let ρ := μ.restrict {q | regenerationTime hd lam l 1 q.2 =
    (((n : ℝ≥0) * Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)}
  let σ := (volume : Measure (Vec d)).prod Q.measure
  let η := σ.compProd (Probability.probabilityPart K)
  let A := fun p : Vec d × FieldPair d => F p.2 *
    firstSlicePastIntegral (Renewal.regenDelta lam) lam R i (n - 1) K H p
  have hFg : Measurable F := hF.mono (Probability.localSigma_le_borel _) le_rfl
  have hHg : Measurable H := hH.mono (Probability.finiteHistorySigma_le _ _) le_rfl
  have hiA : Integrable A σ := sbxS5_integrable_firstSlicePastFactor Q.measure K hK.1
    (Renewal.regenDelta lam) lam R i (div_pos hl h₀) (n - 1) F hFg hbF H hHg hbH
  let A' := hiA.aestronglyMeasurable.mk A
  have hA' : Measurable A' := hiA.aestronglyMeasurable.measurable_mk
  have heqA : A =ᵐ[σ] A' := hiA.aestronglyMeasurable.ae_eq_mk
  have hiA' : Integrable A' σ := hiA.congr heqA
  let T := fun p : (Vec d × FieldPair d) × CoupledSample d =>
    spatialFutureRecord R i p.1 p.2
  have hT : Measurable T := measurable_spatial_future_triple R i
  let v := fun p : (Vec d × FieldPair d) × CoupledSample d =>
    (c * A' p.1) * killedFutureTest R i (fun _ => 1) p
  have hv : Measurable v :=
    (measurable_const.mul (hA'.comp measurable_fst)).mul
      (measurable_killedFutureTest R i (fun _ => 1) measurable_const)
  have hiv : Integrable v η := by
    apply ((sbxS5_integrable_kernelLift σ K hK.1.2 A' hA' hiA').const_mul c).mul_bdd (c := 1)
      (measurable_killedFutureTest R i (fun _ => 1) measurable_const).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun p => by
      dsimp only [killedFutureTest]
      split_ifs <;> norm_num
  have hspatial : ∀ (ψ : FutureState d i R → ℝ), Measurable ψ → BoundedRealTest ψ →
      (∫ p, v p * ψ (T p) ∂η) =
        c * ∫ y, ∫ ω, A (y, ω) * (∫ z, killedFutureTest R i ψ ((y, ω), z)
          ∂K (y, ω)) ∂Q.measure := by
    intro ψ hψ hbψ
    calc
      (∫ p, v p * ψ (T p) ∂η) =
          c * ∫ p, A' p.1 * killedFutureTest R i ψ p ∂η := by
        rw [← integral_const_mul]
        congr 1
        funext p
        dsimp only [v, T, killedFutureTest]
        split_ifs <;> ring
      _ = c * ∫ p, A' p * (∫ z, killedFutureTest R i ψ (p, z) ∂K p) ∂σ := by
        rw [sbxS5_signedWeight_kernel_integral σ K hK.1.2 A' hA' hiA'
          (killedFutureTest R i ψ) (measurable_killedFutureTest R i ψ hψ)
          (boundedRealTest_killedFutureTest R i ψ hbψ)]
      _ = c * ∫ p, A p * (∫ z, killedFutureTest R i ψ (p, z) ∂K p) ∂σ := by
        congr 1
        apply integral_congr_ae
        filter_upwards [heqA] with p hp
        rw [hp]
      _ = _ := by
        dsimp only [σ, A]
        rw [integral_prod _ (sbxS5_integrable_firstSlicePast_killedFuture Q.measure K hK.1
          (Renewal.regenDelta lam) lam R i (div_pos hl h₀) (n - 1)
          F hFg hbF H hHg hbH ψ hψ hbψ)]
  haveI : IsProbabilityMeasure μ := annealedCoupledLaw_isProbabilityMeasure Q.measure K hK.1
  let W := fun q : FieldPair d × CoupledSample d => F q.1 * H q.2
  have hW : Measurable W := (hFg.comp measurable_fst).mul (hHg.comp measurable_snd)
  have hiW : Integrable W ρ := by
    obtain ⟨CF, hCF⟩ := hbF
    obtain ⟨CH, hCH⟩ := hbH
    apply Integrable.of_bound hW.aestronglyMeasurable (max CF 0 * max CH 0)
    exact Filter.Eventually.of_forall fun q => by
      simp only [W, Real.norm_eq_abs, abs_mul]
      exact mul_le_mul ((hCF _).trans (le_max_left _ _))
        ((hCH _).trans (le_max_left _ _)) (abs_nonneg _) (le_max_right _ _)
  have hrecord := (hscope d hd Λ₀ r₀ Q lam h₀ h₁ l δ hl hsep hδ₀ hδ₁ P K hK hD 1).2.1
  have htest : ∀ (f : Path d × BernoulliSequence → ℝ), Measurable f → BoundedRealTest f →
      ∀ (g : (FutureHalfSpace d i R → Mat d × ℝ) → ℝ), Measurable g → BoundedRealTest g →
      (∫ q, W q * (f ((regenerationRecord hd lam l 1 q).1,
        (regenerationRecord hd lam l 1 q).2.1) * g (regenerationRecord hd lam l 1 q).2.2) ∂ρ) =
      ∫ p, v p * (f ((T p).1, (T p).2.1) * g (T p).2.2) ∂η := by
    intro f hf hbf g hg hbg
    let ψ : FutureState d i R → ℝ := fun r => f (r.1, r.2.1) * g r.2.2
    have hψ : Measurable ψ :=
      (hf.comp (measurable_fst.prodMk measurable_snd.fst)).mul
        (hg.comp measurable_snd.snd)
    have hbψ : BoundedRealTest ψ := by
      obtain ⟨Cf, hCf⟩ := hbf
      obtain ⟨Cg, hCg⟩ := hbg
      refine ⟨max Cf 0 * max Cg 0, fun r => ?_⟩
      simp only [ψ, abs_mul]
      exact mul_le_mul ((hCf _).trans (le_max_left _ _))
        ((hCg _).trans (le_max_left _ _)) (abs_nonneg _) (le_max_right _ _)
    change (∫ q, W q * ψ (regenerationRecord hd lam l 1 q) ∂ρ) = ∫ p, v p * ψ (T p) ∂η
    rw [hspatial ψ hψ hbψ]
    exact hendpoint d hd Λ₀ r₀ Q lam h₀ h₁ l δ hl hsep hδ₀ hδ₁ P K hK
      F hF hbF n hn H hH hbH f hf hbf g hg hbg
  have ht := sbxS5_signedWeighted_futureTests i R ρ η W v hW hv hiW hiv
    (regenerationRecord hd lam l 1) T hrecord hT htest Φ hΦ hbΦ
  rw [hspatial Φ hΦ hbΦ] at ht
  exact ht

section CenteredEndpointDifference

variable {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1) (l δ : ℝ)
    (hl : 0 < l) (hsep : r₀ < 2 * l) (hδ₀ : 0 < δ) (hδ₁ : δ < 1)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K)

include hK hl hsep hδ₀ hδ₁

/-- The full future-triple endpoint identity retains the exact off-origin
remainder after factoring the translated-origin term by joint finite range. -/
theorem sbxS5_fullSlice_endpoint_difference
    (hendpoint : node_app_u3A_factorization_u23_endpoint_u2D_disintegrationStmt)
    (hpast : node_app_u3A_factorization_u23_past_u2D_kernelStmt)
    (hfuture : node_app_u3A_factorization_u23_future_u2D_kernelStmt)
    (hslices : node_app_u3A_factorization_u23_slicesStmt)
    (hscope : node_app_u3A_factorization_u23_coupling_u2D_scopeStmt)
    (hD : annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam)) ≠ 0)
    (F : FieldPair d → ℝ)
    (hF : Measurable[localSigma {x : Vec d | euclideanNorm x < l / lam}] F)
    (hbF : BoundedRealTest F) (n : ℕ) (hn : 2 ≤ n) (H : CoupledSample d → ℝ)
    (hH : Measurable[finiteHistorySigma (Renewal.regenDelta lam) (n - 1)] H)
    (hbH : BoundedRealTest H)
    (Φ : FutureState d (Renewal.forceCoord hd) (l / lam) → ℝ)
    (hΦ : Measurable Φ) (hbΦ : BoundedRealTest Φ) :
    let A := fun (y : Vec d) (ω : FieldPair d) => F ω *
      firstSlicePastIntegral (Renewal.regenDelta lam) lam (l / lam)
        (Renewal.forceCoord hd) (n - 1) K H (y, ω)
    let B := fun (y : Vec d) (ω : FieldPair d) =>
      ∫ z, killedFutureTest (l / lam) (Renewal.forceCoord hd) Φ ((y, ω), z) ∂K (y, ω)
    let B₀ := fun (y : Vec d) (ω : FieldPair d) =>
      ∫ z, killedFutureTest (l / lam) (Renewal.forceCoord hd) Φ
        ((0, translate y ω), z) ∂K (0, translate y ω)
    (∫ q in {q | regenerationTime hd lam l 1 q.2 =
        (((n : ℝ≥0) * Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)},
      F q.1 * H q.2 * Φ (regenerationRecord hd lam l 1 q)
        ∂annealedCoupledLaw Q.measure K) =
      δ * (∫ q, F q.1 * ((forcedBitTrialEvent (Renewal.regenDelta lam) lam (l / lam)
          (Renewal.forceCoord hd) (n - 1)).indicator H) q.2
            ∂annealedCoupledLaw Q.measure K) *
        ((annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam))).toReal *
          ∫ q, Φ (regenerationRecord hd lam l 0 q)
            ∂regenerationConditionedLaw hd Q lam l K hK.1 hD) +
      (δ / (volume (endpointBall (Renewal.forceCoord hd) (l / lam) 0)).toReal) *
        ∫ y, ∫ ω, A y ω * (B y ω - B₀ y ω) ∂Q.measure := by
  intro A B B₀
  have hV : (volume (endpointBall (Renewal.forceCoord hd) (l / lam) (0 : Vec d))).toReal ≠ 0 :=
    ENNReal.toReal_ne_zero.mpr
      ⟨(endpointBall_volume_pos _ _ (div_pos hl h₀) _).ne',
        endpointBall_volume_ne_top _ _ (div_pos hl h₀) _⟩
  rw [sbxS5_endpointDisintegration_fullFuture hd Q lam h₀ h₁ l δ hl hsep hδ₀ hδ₁
    P K hK hendpoint hscope hD F hF hbF n hn H hH hbH Φ hΦ hbΦ]
  rw [sbxS5_firstSlicePast_killedFuture_spatial_difference
    hd Q lam h₀ h₁ l δ hl hsep hδ₀ hδ₁ P K hK hpast hfuture hslices hD
    Φ hΦ hbΦ F hF hbF n hn H hH hbH]
  field_simp
  <;> ring

/-- Centering the entire future test by its actual conditioned mean removes
the normalization term. The remaining expression is precisely the defect in
slice independence, still evaluated with the literal spatial coupling. -/
theorem sbxS5_sliceIndependence_centered_remainder
    (hendpoint : node_app_u3A_factorization_u23_endpoint_u2D_disintegrationStmt)
    (hpast : node_app_u3A_factorization_u23_past_u2D_kernelStmt)
    (hfuture : node_app_u3A_factorization_u23_future_u2D_kernelStmt)
    (hslices : node_app_u3A_factorization_u23_slicesStmt)
    (hscope : node_app_u3A_factorization_u23_coupling_u2D_scopeStmt)
    (hD : annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam)) ≠ 0)
    (F : FieldPair d → ℝ)
    (hF : Measurable[localSigma {x : Vec d | euclideanNorm x < l / lam}] F)
    (hbF : BoundedRealTest F) (n : ℕ) (hn : 2 ≤ n) (H : CoupledSample d → ℝ)
    (hH : Measurable[finiteHistorySigma (Renewal.regenDelta lam) (n - 1)] H)
    (hbH : BoundedRealTest H)
    (Φ : FutureState d (Renewal.forceCoord hd) (l / lam) → ℝ)
    (hΦ : Measurable Φ) (hbΦ : BoundedRealTest Φ) :
    let μ := annealedCoupledLaw Q.measure K
    let ν := regenerationConditionedLaw hd Q lam l K hK.1 hD
    let m := ∫ q, Φ (regenerationRecord hd lam l 0 q) ∂ν
    let Ψ := fun r => Φ r - m
    let A := fun (y : Vec d) (ω : FieldPair d) => F ω *
      firstSlicePastIntegral (Renewal.regenDelta lam) lam (l / lam)
        (Renewal.forceCoord hd) (n - 1) K H (y, ω)
    let B := fun (y : Vec d) (ω : FieldPair d) =>
      ∫ z, killedFutureTest (l / lam) (Renewal.forceCoord hd) Ψ ((y, ω), z) ∂K (y, ω)
    let B₀ := fun (y : Vec d) (ω : FieldPair d) =>
      ∫ z, killedFutureTest (l / lam) (Renewal.forceCoord hd) Ψ
        ((0, translate y ω), z) ∂K (0, translate y ω)
    (∫ q in {q | regenerationTime hd lam l 1 q.2 =
        (((n : ℝ≥0) * Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)},
      F q.1 * H q.2 * Φ (regenerationRecord hd lam l 1 q) ∂μ) -
      (∫ q in {q | regenerationTime hd lam l 1 q.2 =
        (((n : ℝ≥0) * Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)},
        F q.1 * H q.2 ∂μ) * m =
      (δ / (volume (endpointBall (Renewal.forceCoord hd) (l / lam) 0)).toReal) *
        ∫ y, ∫ ω, A y ω * (B y ω - B₀ y ω) ∂Q.measure := by
  intro μ ν m Ψ A B B₀
  haveI : IsProbabilityMeasure μ := annealedCoupledLaw_isProbabilityMeasure Q.measure K hK.1
  haveI : IsProbabilityMeasure ν := ProbabilityTheory.cond_isProbabilityMeasure hD
  have hΨ : Measurable Ψ := hΦ.sub measurable_const
  obtain ⟨C, hC⟩ := hbΦ
  have hbΨ : BoundedRealTest Ψ :=
    ⟨C + |m|, fun r => (abs_sub (Φ r) m).trans (by linarith only [hC r])⟩
  have hrecord₀ := (hscope d hd Λ₀ r₀ Q lam h₀ h₁ l δ hl hsep hδ₀ hδ₁ P K hK hD 0).2.1
  have hiΦ₀ : Integrable (fun q => Φ (regenerationRecord hd lam l 0 q)) ν :=
    Integrable.of_bound (hΦ.comp hrecord₀).aestronglyMeasurable C
      (Filter.Eventually.of_forall fun q => by simpa only [Real.norm_eq_abs] using hC _)
  have hmean : (∫ q, Ψ (regenerationRecord hd lam l 0 q) ∂ν) = 0 := by
    rw [show (fun q => Ψ (regenerationRecord hd lam l 0 q)) =
      (fun q => Φ (regenerationRecord hd lam l 0 q) - m) from rfl]
    rw [integral_sub hiΦ₀ (integrable_const m)]
    simp only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one,
      smul_eq_mul, one_mul, m, sub_self]
  let ρ := μ.restrict {q | regenerationTime hd lam l 1 q.2 =
    (((n : ℝ≥0) * Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)}
  let W := fun q : FieldPair d × CoupledSample d => F q.1 * H q.2
  have hFg : Measurable F := hF.mono (Probability.localSigma_le_borel _) le_rfl
  have hHg : Measurable H := hH.mono (Probability.finiteHistorySigma_le _ _) le_rfl
  have hW : Measurable W := (hFg.comp measurable_fst).mul (hHg.comp measurable_snd)
  obtain ⟨CF, hCF⟩ := hbF
  obtain ⟨CH, hCH⟩ := hbH
  have hiW : Integrable W ρ := by
    apply Integrable.of_bound hW.aestronglyMeasurable (max CF 0 * max CH 0)
    exact Filter.Eventually.of_forall fun q => by
      simp only [W, Real.norm_eq_abs, abs_mul]
      exact mul_le_mul ((hCF _).trans (le_max_left _ _))
        ((hCH _).trans (le_max_left _ _)) (abs_nonneg _) (le_max_right _ _)
  have hrecord₁ := (hscope d hd Λ₀ r₀ Q lam h₀ h₁ l δ hl hsep hδ₀ hδ₁ P K hK hD 1).2.1
  have hiWΦ : Integrable (fun q => W q * Φ (regenerationRecord hd lam l 1 q)) ρ :=
    hiW.mul_bdd (hΦ.comp hrecord₁).aestronglyMeasurable
      (Filter.Eventually.of_forall fun q => by simpa only [Real.norm_eq_abs] using hC _)
  have hcenter : (∫ q, W q * Ψ (regenerationRecord hd lam l 1 q) ∂ρ) =
      (∫ q, W q * Φ (regenerationRecord hd lam l 1 q) ∂ρ) -
        (∫ q, W q ∂ρ) * m := by
    simp only [Ψ, mul_sub]
    rw [integral_sub hiWΦ (hiW.mul_const m), integral_mul_const]
  have heq := sbxS5_fullSlice_endpoint_difference hd Q lam h₀ h₁ l δ hl hsep hδ₀ hδ₁
    P K hK hendpoint hpast hfuture hslices hscope hD F hF ⟨CF, hCF⟩ n hn H hH
    ⟨CH, hCH⟩ Ψ hΨ hbΨ
  rw [hmean] at heq
  change (∫ q, W q * Φ (regenerationRecord hd lam l 1 q) ∂ρ) -
    (∫ q, W q ∂ρ) * m = _
  rw [← hcenter]
  simpa only [mul_zero, zero_add] using heq

end CenteredEndpointDifference

/-- The literal difference between the off-origin and translated-origin
future factors is integrable against the signed past weight. In particular,
its spatial restriction is an ordinary integrable remainder. -/
theorem sbxS5_integrable_firstSlicePast_future_difference {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q] (hQ : IsStationary Q)
    (K : CoupledQuenchedLaws d) (hK : HasProbabilityLaws Q K)
    (Δ : ℝ≥0) (lam R : ℝ) (i : Fin d) (hR : 0 < R) (m : ℕ)
    (F : FieldPair d → ℝ) (hF : Measurable F) (hbF : BoundedRealTest F)
    (H : CoupledSample d → ℝ) (hH : Measurable H) (hbH : BoundedRealTest H)
    (Φ : FutureState d i R → ℝ) (hΦ : Measurable Φ) (hbΦ : BoundedRealTest Φ) :
    Integrable (fun p : Vec d × FieldPair d =>
      (F p.2 * firstSlicePastIntegral Δ lam R i m K H p) *
        ((∫ z, killedFutureTest R i Φ (p, z) ∂K p) -
          ∫ z, killedFutureTest R i Φ ((0, translate p.1 p.2), z)
            ∂K (0, translate p.1 p.2))) (volume.prod Q) := by
  have hi :=
    (sbxS5_integrable_firstSlicePast_killedFuture Q K hK Δ lam R i hR m
      F hF hbF H hH hbH Φ hΦ hbΦ).sub
        (sbxS5_integrable_firstSlicePast_shiftedOriginFuture Q hQ K hK Δ lam R i hR m
          F hF hbF H hH hbH Φ hΦ hbΦ)
  apply hi.congr
  exact Filter.Eventually.of_forall (fun p => (mul_sub _ _ _).symm)

/-- Slice geometry removes every spatial endpoint below `10R`, even after
multiplication by an arbitrary real future factor. This applies directly to
the actual off-origin discrepancy, without a covariance identification. -/
theorem sbxS5_firstSlicePast_weighted_spatial_integral_above
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1) (l δ : ℝ)
    (hl : 0 < l) (hsep : r₀ < 2 * l) (hδ₀ : 0 < δ) (hδ₁ : δ < 1)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K)
    (hslices : node_app_u3A_factorization_u23_slicesStmt)
    (F : FieldPair d → ℝ) (n : ℕ) (hn : 2 ≤ n) (H : CoupledSample d → ℝ)
    (C : Vec d × FieldPair d → ℝ) :
    (∫ y in {y : Vec d | 10 * (l / lam) ≤ y (Renewal.forceCoord hd)},
      ∫ ω, (F ω * firstSlicePastIntegral (Renewal.regenDelta lam) lam (l / lam)
        (Renewal.forceCoord hd) (n - 1) K H (y, ω)) * C (y, ω) ∂Q.measure) =
      ∫ y, ∫ ω, (F ω * firstSlicePastIntegral (Renewal.regenDelta lam) lam (l / lam)
        (Renewal.forceCoord hd) (n - 1) K H (y, ω)) * C (y, ω) ∂Q.measure := by
  let J := fun y : Vec d => ∫ ω, (F ω *
    firstSlicePastIntegral (Renewal.regenDelta lam) lam (l / lam)
      (Renewal.forceCoord hd) (n - 1) K H (y, ω)) * C (y, ω) ∂Q.measure
  have hz : ∀ y, y (Renewal.forceCoord hd) < 10 * (l / lam) → J y = 0 := by
    intro y hy
    apply integral_eq_zero_of_ae
    filter_upwards [sbxS5_firstSlicePast_zero hd Q lam h₀ h₁ l δ hl hsep hδ₀ hδ₁
      P K hK hslices n hn H y hy] with ω hω
    simp only [Pi.zero_apply] at hω
    simp only [hω, mul_zero, zero_mul, Pi.zero_apply]
  have hhalf : MeasurableSet {y : Vec d | 10 * (l / lam) ≤ y (Renewal.forceCoord hd)} :=
    measurableSet_le measurable_const (measurable_pi_apply _)
  change (∫ y in {y : Vec d | 10 * (l / lam) ≤ y (Renewal.forceCoord hd)}, J y) = ∫ y, J y
  rw [← integral_indicator hhalf]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro y
  by_cases hy : y ∈ {y : Vec d | 10 * (l / lam) ≤ y (Renewal.forceCoord hd)}
  · exact Set.indicator_of_mem hy J
  · rw [Set.indicator_of_notMem hy, hz y (lt_of_not_ge hy)]

section FirstCycleRemainderSeries

variable {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1) (l δ : ℝ)
    (hl : 0 < l) (hsep : r₀ < 2 * l) (hδ₀ : 0 < δ) (hδ₁ : δ < 1)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K)

include hK hl hsep hδ₀ hδ₁

/-- The actual first-cycle grid partitions the whole annealed law, so every
integrable observation has a convergent series of its literal slice integrals.
The supplied coupling scope covers every admissible scale. -/
theorem sbxS5_firstCycle_hasSum_integral
    (hscope : node_app_u3A_factorization_u23_coupling_u2D_scopeStmt)
    (hD : annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam)) ≠ 0)
    (f : FieldPair d × CoupledSample d → ℝ)
    (hf : Integrable f (annealedCoupledLaw Q.measure K)) :
    HasSum (fun n : ℕ =>
      ∫ q in {q | regenerationTime hd lam l 1 q.2 =
        ((((n + 2 : ℕ) : ℝ≥0) * Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)},
        f q ∂annealedCoupledLaw Q.measure K)
      (∫ q, f q ∂annealedCoupledLaw Q.measure K) := by
  let μ := annealedCoupledLaw Q.measure K
  have hsc := hscope d hd Λ₀ r₀ Q lam h₀ h₁ l δ hl hsep hδ₀ hδ₁ P K hK hD 1
  have hgrid := hsc.2.2 μ (by simp [μ])
  let s : ℕ → Set (FieldPair d × CoupledSample d) := fun n =>
    {q | regenerationTime hd lam l 1 q.2 =
      ((((n + 2 : ℕ) : ℝ≥0) * Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)}
  have hs (n : ℕ) : MeasurableSet (s n) :=
    (hsc.1.comp measurable_snd) (measurableSet_singleton _)
  have hdis : Pairwise (fun m n => Disjoint (s m) (s n)) := by
    intro m n hmn
    apply Set.disjoint_left.mpr
    intro q hm hn
    have he := ENNReal.coe_inj.mp (hm.symm.trans hn)
    have hc := mul_right_cancel₀ (EinsteinRelation.regenDelta_pos h₀).ne' he
    have hnat : m + 2 = n + 2 := by exact_mod_cast hc
    exact hmn (Nat.add_right_cancel hnat)
  have hcover : ∀ᵐ q ∂μ, q ∈ ⋃ n, s n := by
    filter_upwards [hgrid] with q hq
    obtain ⟨n, hn, ht, _⟩ := hq
    have hn₂ : n - 2 + 2 = n := by omega
    refine Set.mem_iUnion.mpr ⟨n - 2, ?_⟩
    change regenerationTime hd lam l 1 q.2 =
      ((((n - 2 + 2 : ℕ) : ℝ≥0) * Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)
    simpa only [hn₂] using ht
  have h := hasSum_integral_iUnion hs hdis hf.integrableOn
  rw [Measure.restrict_eq_self_of_ae_mem hcover] at h
  exact h

/-- The full first-marginal defect is the convergent sum of the literal
centered off-origin discrepancies. This uses the five supplied factorization
inputs and retains the actual coupling on every spatial fiber. -/
theorem sbxS5_firstMarginal_centered_remainders_hasSum
    (hendpoint : node_app_u3A_factorization_u23_endpoint_u2D_disintegrationStmt)
    (hpast : node_app_u3A_factorization_u23_past_u2D_kernelStmt)
    (hfuture : node_app_u3A_factorization_u23_future_u2D_kernelStmt)
    (hslices : node_app_u3A_factorization_u23_slicesStmt)
    (hscope : node_app_u3A_factorization_u23_coupling_u2D_scopeStmt)
    (hD : annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam)) ≠ 0)
    (Φ : FutureState d (Renewal.forceCoord hd) (l / lam) → ℝ)
    (hΦ : Measurable Φ) (hbΦ : BoundedRealTest Φ) :
    let μ := annealedCoupledLaw Q.measure K
    let ν := regenerationConditionedLaw hd Q lam l K hK.1 hD
    let m := ∫ q, Φ (regenerationRecord hd lam l 0 q) ∂ν
    let Ψ := fun r => Φ r - m
    let A := fun (n : ℕ) (y : Vec d) (ω : FieldPair d) =>
      firstSlicePastIntegral (Renewal.regenDelta lam) lam (l / lam)
        (Renewal.forceCoord hd) (n + 2 - 1) K (fun _ => 1) (y, ω)
    let B := fun (y : Vec d) (ω : FieldPair d) =>
      ∫ z, killedFutureTest (l / lam) (Renewal.forceCoord hd) Ψ ((y, ω), z) ∂K (y, ω)
    let B₀ := fun (y : Vec d) (ω : FieldPair d) =>
      ∫ z, killedFutureTest (l / lam) (Renewal.forceCoord hd) Ψ
        ((0, translate y ω), z) ∂K (0, translate y ω)
    HasSum (fun n : ℕ =>
      (δ / (volume (endpointBall (Renewal.forceCoord hd) (l / lam) 0)).toReal) *
        ∫ y, ∫ ω, A n y ω * (B y ω - B₀ y ω) ∂Q.measure)
      ((∫ q, Φ (regenerationRecord hd lam l 1 q) ∂μ) - m) := by
  intro μ ν m Ψ A B B₀
  haveI : IsProbabilityMeasure μ := annealedCoupledLaw_isProbabilityMeasure Q.measure K hK.1
  have hrecord := (hscope d hd Λ₀ r₀ Q lam h₀ h₁ l δ hl hsep hδ₀ hδ₁
    P K hK hD 1).2.1
  obtain ⟨C, hC⟩ := hbΦ
  have hiΦ : Integrable (fun q => Φ (regenerationRecord hd lam l 1 q)) μ :=
    Integrable.of_bound (hΦ.comp hrecord).aestronglyMeasurable C
      (Filter.Eventually.of_forall fun q => by simpa only [Real.norm_eq_abs] using hC _)
  let s : ℕ → Set (FieldPair d × CoupledSample d) := fun n =>
    {q | regenerationTime hd lam l 1 q.2 =
      ((((n + 2 : ℕ) : ℝ≥0) * Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)}
  have hleft := sbxS5_firstCycle_hasSum_integral hd Q lam h₀ h₁ l δ hl hsep hδ₀ hδ₁
    P K hK hscope hD _ hiΦ
  have hmass := sbxS5_firstCycle_hasSum_integral hd Q lam h₀ h₁ l δ hl hsep hδ₀ hδ₁
    P K hK hscope hD (fun _ => (1 : ℝ)) (integrable_const 1)
  have hsum : HasSum (fun n => (∫ q in s n, Φ (regenerationRecord hd lam l 1 q) ∂μ) -
      (∫ q in s n, (1 : ℝ) ∂μ) * m)
      ((∫ q, Φ (regenerationRecord hd lam l 1 q) ∂μ) - m) := by
    have h : HasSum (fun n => (∫ q in s n, Φ (regenerationRecord hd lam l 1 q) ∂μ) -
        (∫ q in s n, (1 : ℝ) ∂μ) * m)
        ((∫ q, Φ (regenerationRecord hd lam l 1 q) ∂μ) - (∫ _q, (1 : ℝ) ∂μ) * m) :=
      hleft.sub (hmass.mul_right m)
    simpa only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one,
      smul_eq_mul, one_mul] using h
  have hb1 {α : Type} : BoundedRealTest (fun _ : α => (1 : ℝ)) :=
    ⟨1, fun _ => by norm_num⟩
  have heq : (fun n : ℕ =>
      (δ / (volume (endpointBall (Renewal.forceCoord hd) (l / lam) 0)).toReal) *
        ∫ y, ∫ ω, A n y ω * (B y ω - B₀ y ω) ∂Q.measure) =
      (fun n => (∫ q in s n, Φ (regenerationRecord hd lam l 1 q) ∂μ) -
        (∫ q in s n, (1 : ℝ) ∂μ) * m) := by
    funext n
    have h := sbxS5_sliceIndependence_centered_remainder hd Q lam h₀ h₁ l δ
      hl hsep hδ₀ hδ₁ P K hK hendpoint hpast hfuture hslices hscope hD
      (fun _ => 1) measurable_const hb1 (n + 2) (by omega)
      (fun _ => 1) measurable_const hb1 Φ hΦ ⟨C, hC⟩
    simpa only [one_mul] using h.symm
  rw [heq]
  exact hsum

/-- The literal first-cycle slice integrals are absolutely summable, with
their total variation controlled by the annealed integral of the absolute
observation. No covariance or cancellation between slices is used. -/
theorem sbxS5_firstCycle_summable_abs_integrals
    (hscope : node_app_u3A_factorization_u23_coupling_u2D_scopeStmt)
    (hD : annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam)) ≠ 0)
    (f : FieldPair d × CoupledSample d → ℝ)
    (hf : Integrable f (annealedCoupledLaw Q.measure K)) :
    let μ := annealedCoupledLaw Q.measure K
    let a := fun n : ℕ =>
      ∫ q in {q | regenerationTime hd lam l 1 q.2 =
        ((((n + 2 : ℕ) : ℝ≥0) * Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)}, f q ∂μ
    Summable (fun n => |a n|) ∧ (∑' n, |a n|) ≤ ∫ q, |f q| ∂μ := by
  intro μ a
  let b := fun n : ℕ =>
    ∫ q in {q | regenerationTime hd lam l 1 q.2 =
      ((((n + 2 : ℕ) : ℝ≥0) * Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)}, |f q| ∂μ
  have hb : HasSum b (∫ q, |f q| ∂μ) := by
    simpa only [Real.norm_eq_abs] using
      sbxS5_firstCycle_hasSum_integral hd Q lam h₀ h₁ l δ hl hsep hδ₀ hδ₁
        P K hK hscope hD (fun q => ‖f q‖) hf.norm
  have hle (n : ℕ) : |a n| ≤ b n := by
    simpa only [Real.norm_eq_abs] using
      norm_integral_le_integral_norm (f := f)
        (μ := μ.restrict {q | regenerationTime hd lam l 1 q.2 =
          ((((n + 2 : ℕ) : ℝ≥0) * Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)})
  have ha : Summable (fun n => |a n|) :=
    Summable.of_nonneg_of_le (fun _ => abs_nonneg _) hle hb.summable
  refine ⟨ha, ?_⟩
  exact (ha.tsum_le_tsum hle hb.summable).trans_eq hb.tsum_eq

/-- The centered off-origin spatial remainders form an absolutely summable
series. Their total variation is bounded by the actual first-record centered
observation, rather than by cancellation in the series. -/
theorem sbxS5_firstMarginal_centered_remainders_absSummable
    (hendpoint : node_app_u3A_factorization_u23_endpoint_u2D_disintegrationStmt)
    (hpast : node_app_u3A_factorization_u23_past_u2D_kernelStmt)
    (hfuture : node_app_u3A_factorization_u23_future_u2D_kernelStmt)
    (hslices : node_app_u3A_factorization_u23_slicesStmt)
    (hscope : node_app_u3A_factorization_u23_coupling_u2D_scopeStmt)
    (hD : annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam)) ≠ 0)
    (Φ : FutureState d (Renewal.forceCoord hd) (l / lam) → ℝ)
    (hΦ : Measurable Φ) (hbΦ : BoundedRealTest Φ) :
    let μ := annealedCoupledLaw Q.measure K
    let ν := regenerationConditionedLaw hd Q lam l K hK.1 hD
    let m := ∫ q, Φ (regenerationRecord hd lam l 0 q) ∂ν
    let Ψ := fun r => Φ r - m
    let A := fun (n : ℕ) (y : Vec d) (ω : FieldPair d) =>
      firstSlicePastIntegral (Renewal.regenDelta lam) lam (l / lam)
        (Renewal.forceCoord hd) (n + 2 - 1) K (fun _ => 1) (y, ω)
    let B := fun (y : Vec d) (ω : FieldPair d) =>
      ∫ z, killedFutureTest (l / lam) (Renewal.forceCoord hd) Ψ ((y, ω), z) ∂K (y, ω)
    let B₀ := fun (y : Vec d) (ω : FieldPair d) =>
      ∫ z, killedFutureTest (l / lam) (Renewal.forceCoord hd) Ψ
        ((0, translate y ω), z) ∂K (0, translate y ω)
    let a := fun n : ℕ =>
      (δ / (volume (endpointBall (Renewal.forceCoord hd) (l / lam) 0)).toReal) *
        ∫ y, ∫ ω, A n y ω * (B y ω - B₀ y ω) ∂Q.measure
    Summable (fun n => |a n|) ∧
      |(∫ q, Φ (regenerationRecord hd lam l 1 q) ∂μ) - m| ≤ (∑' n, |a n|) ∧
      (∑' n, |a n|) ≤ ∫ q, |Φ (regenerationRecord hd lam l 1 q) - m| ∂μ := by
  intro μ ν m Ψ A B B₀ a
  haveI : IsProbabilityMeasure μ := annealedCoupledLaw_isProbabilityMeasure Q.measure K hK.1
  have hrecord := (hscope d hd Λ₀ r₀ Q lam h₀ h₁ l δ hl hsep hδ₀ hδ₁
    P K hK hD 1).2.1
  obtain ⟨C, hC⟩ := hbΦ
  have hiΦ : Integrable (fun q => Φ (regenerationRecord hd lam l 1 q)) μ :=
    Integrable.of_bound (hΦ.comp hrecord).aestronglyMeasurable C
      (Filter.Eventually.of_forall fun q => by simpa only [Real.norm_eq_abs] using hC _)
  have hi := hiΦ.sub (integrable_const m)
  have habs := sbxS5_firstCycle_summable_abs_integrals hd Q lam h₀ h₁ l δ hl hsep hδ₀ hδ₁
    P K hK hscope hD (fun q => Φ (regenerationRecord hd lam l 1 q) - m) hi
  have hb1 {α : Type} : BoundedRealTest (fun _ : α => (1 : ℝ)) :=
    ⟨1, fun _ => by norm_num⟩
  have heq : a = fun n : ℕ =>
      ∫ q in {q | regenerationTime hd lam l 1 q.2 =
        ((((n + 2 : ℕ) : ℝ≥0) * Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)},
        (Φ (regenerationRecord hd lam l 1 q) - m) ∂μ := by
    funext n
    have h := sbxS5_sliceIndependence_centered_remainder hd Q lam h₀ h₁ l δ
      hl hsep hδ₀ hδ₁ P K hK hendpoint hpast hfuture hslices hscope hD
      (fun _ => 1) measurable_const hb1 (n + 2) (by omega)
      (fun _ => 1) measurable_const hb1 Φ hΦ ⟨C, hC⟩
    calc
      a n = (∫ q in {q | regenerationTime hd lam l 1 q.2 =
          ((((n + 2 : ℕ) : ℝ≥0) * Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)},
          Φ (regenerationRecord hd lam l 1 q) ∂μ) -
        (∫ q in {q | regenerationTime hd lam l 1 q.2 =
          ((((n + 2 : ℕ) : ℝ≥0) * Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)},
          (1 : ℝ) ∂μ) * m := by simpa only [one_mul] using h.symm
      _ = _ := by
        rw [integral_sub hiΦ.integrableOn (integrable_const m)]
        simp only [setIntegral_const, smul_eq_mul, mul_one]
  have ha : Summable (fun n => |a n|) := by
    rw [heq]
    exact habs.1
  have hsum : HasSum a ((∫ q, Φ (regenerationRecord hd lam l 1 q) ∂μ) - m) :=
    sbxS5_firstMarginal_centered_remainders_hasSum hd Q lam h₀ h₁ l δ hl hsep hδ₀ hδ₁
      P K hK hendpoint hpast hfuture hslices hscope hD Φ hΦ ⟨C, hC⟩
  refine ⟨ha, ?_, ?_⟩
  · rw [← hsum.tsum_eq]
    simpa only [Real.norm_eq_abs] using
      (norm_tsum_le_tsum_norm (f := a) (by simpa only [Real.norm_eq_abs] using ha))
  · rw [heq]
    exact habs.2

end FirstCycleRemainderSeries

end EinsteinFull.Blueprint
