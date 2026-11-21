import EinsteinFull.Blueprint.G1.Proofs.SbxS6ConditionIterate
import EinsteinFull.Regeneration.PhysicalKernelPredicate
import EinsteinFull.PhysicalRegeneration.Blueprint.Foundation.node_app_u3A_factorization_u23_slices
import EinsteinFull.PhysicalRegeneration.Blueprint.Foundation.node_app_u3A_regen_u2D_tails
import EinsteinFull.PhysicalRegeneration.Blueprint.G1.Proofs.C1ConditionIterate
import EinsteinFull.PhysicalRegeneration.Blueprint.G1.node_app_u3A_factorization_u23_condition_u2D_iterate
import EinsteinFull.PhysicalRegeneration.Blueprint.G1.node_app_u3A_factorization_u23_independence_v2
import EinsteinFull.PhysicalRegeneration.Frozen.RegenerationCoupling
import EinsteinFull.PhysicalRegeneration.Vendor.Diffusion.GMPFamilyAPI
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.AnnealedUniformEndpointRestart
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.DeterministicEndpointNullSets
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.FirstRegenerationSliceFubini
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.KilledFutureConditionalMean
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.RenewalCarriers

/-!
# Physical-kernel version of
`EinsteinFull.Blueprint.G1.Proofs.SbxS6ConditionIterate`

The declarations of that module that concern the reduced quenched kernel, stated and
proved for the physical quenched kernel of GMP Section 7: the zero-potential pair
`(exp(-2V) a₀, 0)` is replaced by the physical pair `ω = (a₀, V)`, regular at the same
bound `sourceReducedBound Λ₀` (`IsGMPPhysicalKernelReducedBound`).
-/


open MeasureTheory
open scoped NNReal ENNReal
namespace EinsteinFull.Blueprint
open EinsteinRelation Regeneration
/-- The physical-kernel version of `EinsteinFull.Blueprint.sbx_s6_conditioned_slice_factor_v2`. -/
theorem sbx_s6_conditioned_slice_factor_v2_phys
    (hindep : node_app_u3A_factorization_u23_independenceStmtV2_phys)
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
    (l δ : ℝ) (hl : 0 < l) (hsep : r₀ < 2 * l) (hδ : 0 < δ) (hδ₁ : δ < 1)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : IsRegenerationCouplingPhys hd Q lam l δ h₀.le h₁ P K)
    (hD : annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam)) ≠ 0)
    (Φ : FutureState d (Renewal.forceCoord hd) (l / lam) → ℝ)
    (hΦ : Measurable Φ) (hbΦ : BoundedRealTest Φ)
    (F : FieldPair d → ℝ)
    (hF : Measurable[localSigma {x : Vec d | euclideanNorm x < l / lam}] F)
    (hbF : BoundedRealTest F) (n : ℕ) (hn : 2 ≤ n)
    (H : CoupledSample d → ℝ)
    (hH : Measurable[finiteHistorySigma (Renewal.regenDelta lam) (n - 1)] H)
    (hbH : BoundedRealTest H) :
    let ν := regenerationConditionedLaw hd Q lam l K hK.1 hD
    (∫ q in {q | regenerationTime hd lam l 1 q.2 =
      (((n : ℝ≥0) * Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)},
      F q.1 * H q.2 * Φ (regenerationRecord hd lam l 1 q) ∂ν) =
    (∫ q in {q | regenerationTime hd lam l 1 q.2 =
      (((n : ℝ≥0) * Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)},
      F q.1 * H q.2 ∂ν) * ∫ q, Φ (regenerationRecord hd lam l 0 q) ∂ν := by
  classical
  let Δ := Renewal.regenDelta lam
  let R := l / lam
  let i := Renewal.forceCoord hd
  let μ := annealedCoupledLaw Q.measure K
  let S : Set (FieldPair d × CoupledSample d) :=
    {q | regenerationTime hd lam l 1 q.2 = (((n : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞)}
  let E : Set (CoupledSample d) :=
    {z | ∀ t : ℝ≥0, t ≤ (n - 1 : ℕ) * Δ → -R < z.1 t i - z.1 0 i}
  have hEm : MeasurableSet[finiteHistorySigma Δ (n - 1)] E :=
    measurableSet_noBacktracking_prefix Δ (n - 1) R i
  have hsm : MeasurableSet S := measurableSet_eq_fun
    ((Regeneration.measurable_regenerationTime Δ lam R i 1).comp measurable_snd) measurable_const
  have hdm : MeasurableSet (regenerationNoReturn hd R) :=
    (measurableSet_NoBacktracking R i).preimage measurable_snd.fst
  have hΔ : 0 < Δ := Real.toNNReal_pos.mpr (inv_pos.mpr (sq_pos_of_pos h₀))
  have hbar := ae_noBacktracking_iff_prefix_on_firstRegenerationSlice Q.measure K hK.1
    Δ hΔ lam R h₀ (div_pos hl h₀) i (n - 1) hK.2.2.2.2.2.1
  have hDE : ∀ᵐ q ∂μ.restrict S, q ∈ regenerationNoReturn hd R ↔ q.2 ∈ E := by
    filter_upwards [ae_restrict_of_ae hbar, ae_restrict_mem hsm] with q hq ht
    apply hq
    simpa only [S, Set.mem_ofPred_eq, EinsteinFull.regenerationTime,
      regenerationTime_one, Nat.sub_add_cancel (by omega : 1 ≤ n)] using ht
  have hbEH : BoundedRealTest (E.indicator H) := by
    obtain ⟨C, hC⟩ := hbH
    refine ⟨max C 0, fun z => ?_⟩
    by_cases hz : z ∈ E
    · simpa only [Set.indicator_of_mem hz] using (hC z).trans (le_max_left C 0)
    · simpa only [Set.indicator_of_notMem hz, abs_zero] using le_max_right C 0
  have hfactor := ((hindep d hd Λ₀ r₀ Q lam h₀ h₁ l δ hl hsep hδ hδ₁ P K hK hD
    Φ hΦ hbΦ).1 F hF hbF n hn (E.indicator H) (hH.indicator hEm) hbEH).2.2.2.2
  dsimp only
  apply EinsteinFull.Regeneration.conditional_slice_of_indicator μ
    (regenerationNoReturn hd R) S (Prod.snd ⁻¹' E) hdm hsm hDE
  have heq (q : FieldPair d × CoupledSample d) :
      (Prod.snd ⁻¹' E).indicator (fun q => F q.1 * H q.2 *
        Φ (regenerationRecord hd lam l 1 q)) q =
      F q.1 * E.indicator H q.2 * Φ (regenerationRecord hd lam l 1 q) := by
    by_cases hq : q.2 ∈ E <;> simp [hq]
  have heq' (q : FieldPair d × CoupledSample d) :
      (Prod.snd ⁻¹' E).indicator (fun q => F q.1 * H q.2) q =
      F q.1 * E.indicator H q.2 := by
    by_cases hq : q.2 ∈ E <;> simp [hq]
  simp only [heq, heq']
  exact hfactor

section AllScale
variable (hindep : node_app_u3A_factorization_u23_independenceStmtV2_phys)
  {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
  (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
  (l δ : ℝ) (hl : 0 < l) (hsep : r₀ < 2 * l) (hδ : 0 < δ) (hδ₁ : δ < 1)
  (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
  (hK : IsRegenerationCouplingPhys hd Q lam l δ h₀.le h₁ P K)
  (hD : annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam)) ≠ 0)
include hindep h₀ h₁ hl hsep hδ hδ₁ hK hD
/-- The physical-kernel version of `EinsteinFull.Blueprint.sbx_s6_slice_factor_both`. -/
theorem sbx_s6_slice_factor_both_phys
    (Φ : FutureState d (Renewal.forceCoord hd) (l / lam) → ℝ)
    (hΦ : Measurable Φ) (hbΦ : BoundedRealTest Φ)
    (F : FieldPair d → ℝ)
    (hF : Measurable[localSigma {x : Vec d | euclideanNorm x < l / lam}] F)
    (hbF : BoundedRealTest F) (n : ℕ) (hn : 2 ≤ n)
    (H : CoupledSample d → ℝ)
    (hH : Measurable[finiteHistorySigma (Renewal.regenDelta lam) (n - 1)] H)
    (hbH : BoundedRealTest H) :
    let μ := annealedCoupledLaw Q.measure K
    let ν := regenerationConditionedLaw hd Q lam l K hK.1 hD
    ∀ ρ ∈ ({μ, ν} : Set (Measure (FieldPair d × CoupledSample d))),
    (∫ q in {q | regenerationTime hd lam l 1 q.2 =
      (((n : ℝ≥0) * Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)},
      F q.1 * H q.2 * Φ (regenerationRecord hd lam l 1 q) ∂ρ) =
    (∫ q in {q | regenerationTime hd lam l 1 q.2 =
      (((n : ℝ≥0) * Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)},
      F q.1 * H q.2 ∂ρ) *
      ∫ q, Φ (regenerationRecord hd lam l 0 q)
        ∂regenerationConditionedLaw hd Q lam l K hK.1 hD := by
  dsimp only
  intro ρ hρ
  rcases Set.mem_insert_iff.mp hρ with rfl | hρ
  · exact ((hindep d hd Λ₀ r₀ Q lam h₀ h₁ l δ hl hsep hδ hδ₁ P K hK hD
      Φ hΦ hbΦ).1 F hF hbF n hn H hH hbH).2.2.2.2
  · obtain rfl := Set.mem_singleton_iff.mp hρ
    exact sbx_s6_conditioned_slice_factor_v2_phys hindep hd Q lam h₀ h₁ l δ hl hsep
      hδ hδ₁ P K hK hD Φ hΦ hbΦ F hF hbF n hn H hH hbH

/-- The physical-kernel version of `EinsteinFull.Blueprint.sbx_s6_annealed_first_marginal`. -/
theorem sbx_s6_annealed_first_marginal_phys
    (Φ : FutureState d (Renewal.forceCoord hd) (l / lam) → ℝ)
    (hΦ : Measurable Φ) (hbΦ : BoundedRealTest Φ) :
    (∫ q, Φ (regenerationRecord hd lam l 1 q) ∂annealedCoupledLaw Q.measure K) =
      ∫ q, Φ (regenerationRecord hd lam l 0 q)
        ∂regenerationConditionedLaw hd Q lam l K hK.1 hD :=
  (hindep d hd Λ₀ r₀ Q lam h₀ h₁ l δ hl hsep hδ hδ₁ P K hK hD Φ hΦ hbΦ).2

/-- The physical-kernel version of `EinsteinFull.Blueprint.sbx_s6_annealed_first_law`. -/
theorem sbx_s6_annealed_first_law_phys :
    (annealedCoupledLaw Q.measure K).map (regenerationRecord hd lam l 1) =
      (regenerationConditionedLaw hd Q lam l K hK.1 hD).map
        (regenerationRecord hd lam l 0) := by
  have := annealedCoupledLaw_isProbabilityMeasure Q.measure K hK.1
  have := EinsteinFull.regenerationConditionedLaw_probability hd Q lam l K hK.1 hD
  apply measure_eq_of_bounded_real_tests
  intro Φ hΦ hbΦ
  rw [integral_map (EinsteinFull.measurable_regenerationRecord hd lam l 1).aemeasurable
      hΦ.aestronglyMeasurable,
    integral_map (EinsteinFull.measurable_regenerationRecord hd lam l 0).aemeasurable
      hΦ.aestronglyMeasurable]
  exact sbx_s6_annealed_first_marginal_phys hindep hd Q lam h₀ h₁ l δ hl hsep hδ hδ₁ P K hK hD
    Φ hΦ hbΦ

/-- The physical-kernel version of `EinsteinFull.Blueprint.sbx_s6_infinity_implies_no_return`. -/
theorem sbx_s6_infinity_implies_no_return_phys :
    ∀ᵐ q ∂annealedCoupledLaw Q.measure K,
      firstRegenerationTime (Renewal.regenDelta lam) lam (l / lam) q.2
        (Renewal.forceCoord hd) = ⊤ → q ∈ regenerationNoReturn hd (l / lam) := by
  let μ := annealedCoupledLaw Q.measure K
  let ν := regenerationConditionedLaw hd Q lam l K hK.1 hD
  let B : Set (FutureState d (Renewal.forceCoord hd) (l / lam)) :=
    {y | NoBacktracking (l / lam) y.1 (Renewal.forceCoord hd)}
  have hBm : MeasurableSet B :=
    (measurableSet_NoBacktracking _ _).preimage measurable_fst
  have hν : ∀ᵐ q ∂ν, regenerationRecord hd lam l 0 q ∈ B := by
    have hmem : ∀ᵐ q ∂ν, q ∈ regenerationNoReturn hd (l / lam) :=
      ProbabilityTheory.ae_cond_mem (EinsteinFull.measurableSet_regenerationNoReturn hd _)
    filter_upwards [hmem] with q hq
    exact (sbx_s6_zero_record_no_return_iff hd lam l q).mpr hq
  have hmap : ∀ᵐ y ∂ν.map (regenerationRecord hd lam l 0), y ∈ B :=
    (ae_map_iff (EinsteinFull.measurable_regenerationRecord hd lam l 0).aemeasurable hBm).mpr hν
  rw [← sbx_s6_annealed_first_law_phys hindep hd Q lam h₀ h₁ l δ hl hsep hδ hδ₁ P K hK hD] at hmap
  have hμ := ae_of_ae_map
    (EinsteinFull.measurable_regenerationRecord hd lam l 1).aemeasurable hmap
  filter_upwards [hμ] with q hq htop
  rw [sbx_s6_record_first_eq_zero_of_infinite hd lam l q htop] at hq
  exact (sbx_s6_zero_record_no_return_iff hd lam l q).mp hq

/-- The physical-kernel version of `EinsteinFull.Blueprint.sbx_s6_centered_residual_both`. -/
theorem sbx_s6_centered_residual_both_phys
    (Φ : FutureState d (Renewal.forceCoord hd) (l / lam) → ℝ)
    (hΦ : Measurable Φ) (hbΦ : BoundedRealTest Φ) :
    let μ := annealedCoupledLaw Q.measure K
    let ν := regenerationConditionedLaw hd Q lam l K hK.1 hD
    let a := ∫ q, Φ (regenerationRecord hd lam l 0 q) ∂ν
    ∀ ρ ∈ ({μ, ν} : Set (Measure (FieldPair d × CoupledSample d))),
      (∫ q, (Φ (regenerationRecord hd lam l 1 q) - a) ∂ρ) =
        ∫ q in {q | firstRegenerationTime (Renewal.regenDelta lam) lam (l / lam)
          q.2 (Renewal.forceCoord hd) = ⊤},
          (Φ (regenerationRecord hd lam l 1 q) - a) ∂ρ := by
  dsimp only
  intro ρ hρ
  have := annealedCoupledLaw_isProbabilityMeasure Q.measure K hK.1
  have := EinsteinFull.regenerationConditionedLaw_probability hd Q lam l K hK.1 hD
  have : IsProbabilityMeasure ρ := by
    rcases Set.mem_insert_iff.mp hρ with rfl | hρ
    · infer_instance
    · obtain rfl := Set.mem_singleton_iff.mp hρ
      infer_instance
  let a := ∫ q, Φ (regenerationRecord hd lam l 0 q)
    ∂regenerationConditionedLaw hd Q lam l K hK.1 hD
  have hf : Integrable (fun q => Φ (regenerationRecord hd lam l 1 q)) ρ := by
    obtain ⟨C, hC⟩ := hbΦ
    apply Integrable.of_bound
      (hΦ.comp (EinsteinFull.measurable_regenerationRecord hd lam l 1)).aestronglyMeasurable C
    exact Filter.Eventually.of_forall fun q => by
      rw [Real.norm_eq_abs]
      exact hC _
  have hΔ : 0 < Renewal.regenDelta lam :=
    Real.toNNReal_pos.mpr (inv_pos.mpr (sq_pos_of_pos h₀))
  apply sbx_s6_integral_eq_infinity_of_slice_zero _ hΔ _ _ _ ρ _ (hf.sub (integrable_const a))
  intro m
  by_cases hm : m = 0
  · subst m
    have hempty : {q : FieldPair d × CoupledSample d |
        firstRegenerationTime (Renewal.regenDelta lam) lam (l / lam) q.2 (Renewal.forceCoord hd) =
          ((((0 + 1 : ℕ) : ℝ≥0) * Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro q hq
      have ht := ((firstRegenerationTime_eq_iff_forcedBitTrialEvent _ hΔ _ _ _ _ 0).mp hq).1
      rw [forcedBitTrialEvent_zero_eq_empty _ hΔ _ _ h₀ (div_pos hl h₀) _] at ht
      exact ht
    rw [hempty, setIntegral_empty]
  · have hfactor := sbx_s6_slice_factor_both_phys hindep hd Q lam h₀ h₁ l δ hl hsep hδ hδ₁ P K hK hD
      Φ hΦ hbΦ (fun _ => 1) measurable_const ⟨1, fun _ => by norm_num⟩
      (m + 1) (by omega) (fun _ => 1) measurable_const ⟨1, fun _ => by norm_num⟩ ρ hρ
    simp only [one_mul, EinsteinFull.regenerationTime, regenerationTime_one] at hfactor
    simp only [Pi.sub_apply]
    rw [integral_sub hf.integrableOn (integrable_const a), hfactor]
    simp only [integral_const, smul_eq_mul, measureReal_def, mul_one, a, sub_self]

/-- The physical-kernel version of `EinsteinFull.Blueprint.sbx_s6_conditional_first_integral`. -/
theorem sbx_s6_conditional_first_integral_phys
    (Φ : FutureState d (Renewal.forceCoord hd) (l / lam) → ℝ)
    (hΦ : Measurable Φ) (hbΦ : BoundedRealTest Φ) :
    (∫ q, Φ (regenerationRecord hd lam l 1 q)
      ∂regenerationConditionedLaw hd Q lam l K hK.1 hD) =
    ∫ q, Φ (regenerationRecord hd lam l 0 q)
      ∂regenerationConditionedLaw hd Q lam l K hK.1 hD := by
  let μ := annealedCoupledLaw Q.measure K
  let ν := regenerationConditionedLaw hd Q lam l K hK.1 hD
  let E : Set (FieldPair d × CoupledSample d) :=
    {q | firstRegenerationTime (Renewal.regenDelta lam) lam (l / lam) q.2
      (Renewal.forceCoord hd) = ⊤}
  let D := regenerationNoReturn hd (l / lam)
  let a := ∫ q, Φ (regenerationRecord hd lam l 0 q) ∂ν
  let f := fun q => Φ (regenerationRecord hd lam l 1 q) - a
  have := annealedCoupledLaw_isProbabilityMeasure Q.measure K hK.1
  have := EinsteinFull.regenerationConditionedLaw_probability hd Q lam l K hK.1 hD
  have hf (ρ : Measure (FieldPair d × CoupledSample d)) [IsFiniteMeasure ρ] :
      Integrable (fun q => Φ (regenerationRecord hd lam l 1 q)) ρ := by
    obtain ⟨C, hC⟩ := hbΦ
    apply Integrable.of_bound
      (hΦ.comp (EinsteinFull.measurable_regenerationRecord hd lam l 1)).aestronglyMeasurable C
    exact Filter.Eventually.of_forall fun q => by rw [Real.norm_eq_abs]; exact hC _
  have hcenter (ρ : Measure (FieldPair d × CoupledSample d)) [IsProbabilityMeasure ρ] :
      (∫ q, f q ∂ρ) = (∫ q, Φ (regenerationRecord hd lam l 1 q) ∂ρ) - a := by
    rw [integral_sub (hf ρ) (integrable_const a)]
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  have hres := sbx_s6_centered_residual_both_phys hindep hd Q lam h₀ h₁ l δ hl hsep hδ hδ₁ P K hK hD
    Φ hΦ hbΦ
  have hzero : (∫ q in E, f q ∂μ) = 0 := by
    rw [← hres μ (by exact Or.inl rfl), hcenter μ,
      sbx_s6_annealed_first_marginal_phys hindep hd Q lam h₀ h₁ l δ hl hsep hδ hδ₁ P K hK hD
        Φ hΦ hbΦ]
    exact sub_self a
  have hEm : MeasurableSet E := measurableSet_eq_fun
    ((measurable_firstRegenerationTime _ _ _ _).comp measurable_snd) measurable_const
  have hED : E ∩ D =ᵐ[μ] E := by
    filter_upwards [sbx_s6_infinity_implies_no_return_phys hindep hd Q lam h₀ h₁ l δ hl hsep
      hδ hδ₁ P K hK hD] with q hq
    exact propext ⟨fun h => h.1, fun h => ⟨h, hq h⟩⟩
  have hrestrict : ν.restrict E = (μ D)⁻¹ • μ.restrict E := by
    change (ProbabilityTheory.cond μ D).restrict E = _
    rw [ProbabilityTheory.cond, Measure.restrict_smul, Measure.restrict_restrict hEm,
      Measure.restrict_congr_set hED]
  have hzeroν : (∫ q, f q ∂ν) = 0 := by
    rw [hres ν (by exact Or.inr rfl), hrestrict, integral_smul_measure, hzero, smul_zero]
  have heq := hcenter ν
  rw [hzeroν] at heq
  exact sub_eq_zero.mp heq.symm

/-- The physical-kernel version of `EinsteinFull.Blueprint.sbx_s6_conditional_first_law`. -/
theorem sbx_s6_conditional_first_law_phys :
    (regenerationConditionedLaw hd Q lam l K hK.1 hD).map (regenerationRecord hd lam l 1) =
      (regenerationConditionedLaw hd Q lam l K hK.1 hD).map (regenerationRecord hd lam l 0) := by
  have := EinsteinFull.regenerationConditionedLaw_probability hd Q lam l K hK.1 hD
  apply measure_eq_of_bounded_real_tests
  intro Φ hΦ hbΦ
  rw [integral_map (EinsteinFull.measurable_regenerationRecord hd lam l 1).aemeasurable
      hΦ.aestronglyMeasurable,
    integral_map (EinsteinFull.measurable_regenerationRecord hd lam l 0).aemeasurable
      hΦ.aestronglyMeasurable]
  exact sbx_s6_conditional_first_integral_phys hindep hd Q lam h₀ h₁ l δ hl hsep hδ hδ₁ P K hK hD
    Φ hΦ hbΦ

/-- The physical-kernel version of `EinsteinFull.Blueprint.sbx_s6_infinity_record_law`. -/
theorem sbx_s6_infinity_record_law_phys :
    let μ := annealedCoupledLaw Q.measure K
    let ν := regenerationConditionedLaw hd Q lam l K hK.1 hD
    let E := {q : FieldPair d × CoupledSample d |
      firstRegenerationTime (Renewal.regenDelta lam) lam (l / lam) q.2
        (Renewal.forceCoord hd) = ⊤}
    (μ.restrict E).map (regenerationRecord hd lam l 0) =
      (μ E) • ν.map (regenerationRecord hd lam l 0) := by
  let μ := annealedCoupledLaw Q.measure K
  let ν := regenerationConditionedLaw hd Q lam l K hK.1 hD
  let E : Set (FieldPair d × CoupledSample d) :=
    {q | firstRegenerationTime (Renewal.regenDelta lam) lam (l / lam) q.2
      (Renewal.forceCoord hd) = ⊤}
  have := annealedCoupledLaw_isProbabilityMeasure Q.measure K hK.1
  have := EinsteinFull.regenerationConditionedLaw_probability hd Q lam l K hK.1 hD
  have := Measure.smul_finite (ν.map (regenerationRecord hd lam l 0)) (measure_ne_top μ E)
  have hEm : MeasurableSet E := measurableSet_eq_fun
    ((measurable_firstRegenerationTime _ _ _ _).comp measurable_snd) measurable_const
  apply measure_eq_of_bounded_real_tests
  intro Φ hΦ hbΦ
  rw [integral_map (EinsteinFull.measurable_regenerationRecord hd lam l 0).aemeasurable
      hΦ.aestronglyMeasurable,
    integral_smul_measure,
    integral_map (EinsteinFull.measurable_regenerationRecord hd lam l 0).aemeasurable
      hΦ.aestronglyMeasurable]
  let a := ∫ q, Φ (regenerationRecord hd lam l 0 q) ∂ν
  have hf : Integrable (fun q => Φ (regenerationRecord hd lam l 1 q)) μ := by
    obtain ⟨C, hC⟩ := hbΦ
    apply Integrable.of_bound
      (hΦ.comp (EinsteinFull.measurable_regenerationRecord hd lam l 1)).aestronglyMeasurable C
    exact Filter.Eventually.of_forall fun q => by rw [Real.norm_eq_abs]; exact hC _
  have hres := sbx_s6_centered_residual_both_phys hindep hd Q lam h₀ h₁ l δ hl hsep hδ hδ₁ P K hK hD
    Φ hΦ hbΦ
  have hzero : (∫ q in E, (Φ (regenerationRecord hd lam l 1 q) - a) ∂μ) = 0 := by
    rw [← hres μ (by exact Or.inl rfl), integral_sub hf (integrable_const a),
      sbx_s6_annealed_first_marginal_phys hindep hd Q lam h₀ h₁ l δ hl hsep hδ hδ₁ P K hK hD
        Φ hΦ hbΦ]
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
    exact sub_self a
  have hrecords : (∫ q in E, Φ (regenerationRecord hd lam l 1 q) ∂μ) =
      ∫ q in E, Φ (regenerationRecord hd lam l 0 q) ∂μ := by
    apply setIntegral_congr_fun hEm
    intro q hq
    exact congrArg Φ (sbx_s6_record_first_eq_zero_of_infinite hd lam l q hq)
  rw [integral_sub hf.integrableOn (integrable_const a), hrecords] at hzero
  simpa only [integral_const, smul_eq_mul, measureReal_def,
    Measure.restrict_apply_univ, a] using sub_eq_zero.mp hzero

/-- The physical-kernel version of
`EinsteinFull.Blueprint.sbx_s6_conditioned_first_time_dichotomy`. -/
theorem sbx_s6_conditioned_first_time_dichotomy_phys :
    (∀ᵐ q ∂annealedCoupledLaw Q.measure K,
      firstRegenerationTime (Renewal.regenDelta lam) lam (l / lam) q.2
        (Renewal.forceCoord hd) ≠ ⊤) ∨
    (∀ᵐ q ∂regenerationConditionedLaw hd Q lam l K hK.1 hD,
      firstRegenerationTime (Renewal.regenDelta lam) lam (l / lam) q.2
        (Renewal.forceCoord hd) = ⊤) := by
  let μ := annealedCoupledLaw Q.measure K
  let ν := regenerationConditionedLaw hd Q lam l K hK.1 hD
  let E : Set (FieldPair d × CoupledSample d) :=
    {q | firstRegenerationTime (Renewal.regenDelta lam) lam (l / lam) q.2
      (Renewal.forceCoord hd) = ⊤}
  let A : Set (FutureState d (Renewal.forceCoord hd) (l / lam)) :=
    {y | firstRegenerationTime (Renewal.regenDelta lam) lam (l / lam) (recordSample y)
      (Renewal.forceCoord hd) = ⊤}
  have := annealedCoupledLaw_isProbabilityMeasure Q.measure K hK.1
  have := EinsteinFull.regenerationConditionedLaw_probability hd Q lam l K hK.1 hD
  have hEm : MeasurableSet E := measurableSet_eq_fun
    ((measurable_firstRegenerationTime _ _ _ _).comp measurable_snd) measurable_const
  have hAm : MeasurableSet A := measurableSet_eq_fun
    ((measurable_firstRegenerationTime _ _ _ _).comp (measurable_recordSample _ _))
    measurable_const
  have hpre : (regenerationRecord hd lam l 0) ⁻¹' A = E := by
    ext q
    change (_ = ⊤) ↔ (_ = ⊤)
    rw [sbx_s6_zero_record_first_time hd lam l q]
  have hlaw := sbx_s6_infinity_record_law_phys hindep hd Q lam h₀ h₁ l δ hl hsep hδ hδ₁ P K hK hD
  have hmass := congrArg (fun ρ : Measure (FutureState d (Renewal.forceCoord hd) (l / lam)) =>
    ρ A) hlaw
  rw [Measure.map_apply (EinsteinFull.measurable_regenerationRecord hd lam l 0) hAm,
    hpre, Measure.restrict_apply hEm, Set.inter_self, Measure.smul_apply, smul_eq_mul,
    Measure.map_apply (EinsteinFull.measurable_regenerationRecord hd lam l 0) hAm, hpre] at hmass
  by_cases hz : μ E = 0
  · exact Or.inl ((measure_eq_zero_iff_ae_notMem).mp hz)
  · right
    have hνE : ν E = 1 := (ENNReal.mul_eq_left hz (measure_ne_top μ E)).mp hmass.symm
    exact (mem_ae_iff_prob_eq_one hEm).mpr hνE

/-- The physical-kernel version of
`EinsteinFull.Blueprint.sbx_s6_first_finite_iff_conditioned_positive`. -/
theorem sbx_s6_first_finite_iff_conditioned_positive_phys :
    (∀ᵐ q ∂annealedCoupledLaw Q.measure K,
      firstRegenerationTime (Renewal.regenDelta lam) lam (l / lam) q.2
        (Renewal.forceCoord hd) ≠ ⊤) ↔
    (regenerationConditionedLaw hd Q lam l K hK.1 hD)
      {q | firstRegenerationTime (Renewal.regenDelta lam) lam (l / lam) q.2
        (Renewal.forceCoord hd) ≠ ⊤} ≠ 0 := by
  let μ := annealedCoupledLaw Q.measure K
  let ν := regenerationConditionedLaw hd Q lam l K hK.1 hD
  let A : Set (FieldPair d × CoupledSample d) :=
    {q | firstRegenerationTime (Renewal.regenDelta lam) lam (l / lam) q.2
      (Renewal.forceCoord hd) ≠ ⊤}
  have hνμ : ν ≪ μ :=
    EinsteinFull.regenerationConditionedLaw_absolutelyContinuous hd Q lam l K hK.1 hD
  have := EinsteinFull.regenerationConditionedLaw_probability hd Q lam l K hK.1 hD
  have hAm : MeasurableSet A := (measurableSet_eq_fun
    ((measurable_firstRegenerationTime _ _ _ _).comp measurable_snd) measurable_const).compl
  constructor
  · intro hfin
    have hmass : ν A = 1 := (mem_ae_iff_prob_eq_one hAm).mp (hνμ.ae_le hfin)
    exact hmass.trans_ne one_ne_zero
  · intro hpos
    rcases sbx_s6_conditioned_first_time_dichotomy_phys hindep hd Q lam h₀ h₁ l δ hl hsep hδ hδ₁
      P K hK hD with hfin | hinf
    · exact hfin
    · have hzero : ν A = 0 := (measure_eq_zero_iff_ae_notMem).mpr
        (hinf.mono fun _ hq hneq => hneq hq)
      exact (hpos hzero).elim

/-- The physical-kernel version of `EinsteinFull.Blueprint.sbx_s6_conditional_all_record_laws`. -/
theorem sbx_s6_conditional_all_record_laws_phys (k : ℕ) :
    (regenerationConditionedLaw hd Q lam l K hK.1 hD).map (regenerationRecord hd lam l k) =
      (regenerationConditionedLaw hd Q lam l K hK.1 hD).map (regenerationRecord hd lam l 0) := by
  let μ := annealedCoupledLaw Q.measure K
  let ν := regenerationConditionedLaw hd Q lam l K hK.1 hD
  let Δ := Renewal.regenDelta lam
  let R := l / lam
  let i := Renewal.forceCoord hd
  have hΔ : 0 < Δ := Real.toNNReal_pos.mpr (inv_pos.mpr (sq_pos_of_pos h₀))
  have hνμ : ν ≪ μ :=
    EinsteinFull.regenerationConditionedLaw_absolutelyContinuous hd Q lam l K hK.1 hD
  rcases sbx_s6_conditioned_first_time_dichotomy_phys hindep hd Q lam h₀ h₁ l δ hl hsep hδ hδ₁
    P K hK hD with hfin | hinf
  · have hfwd := ae_firstRegenerationTime_forward Q.measure K hK.1 Δ hΔ lam R h₀
      (div_pos hl h₀) i hK.2.2.2.2.2.1
    have hgood : ∀ᵐ q ∂ν, RecordCanShift Δ lam R i (iteratedRecord Δ lam R i 0 q) := by
      filter_upwards [hνμ.ae_le hfin, hνμ.ae_le hfwd] with q hq hforward
      change RecordCanShift Δ lam R i (futureRecord Δ R q.1 q.2 i 0)
      rw [recordCanShift_futureRecord_iff, sampleTimeShift_zero, zero_add]
      exact ⟨hq, hforward hq⟩
    have hcond := sbx_s6_conditional_first_law_phys hindep hd Q lam h₀ h₁ l δ hl hsep hδ hδ₁ P K hK hD
    have hcond' : ν.map (iteratedRecord Δ lam R i 1) =
        ν.map (iteratedRecord Δ lam R i 0) := hcond
    cases k with
    | zero => rfl
    | succ j =>
        exact (iteratedRecord_law_of_first_and_conditional_law Δ hΔ lam R i ν ν
          Measure.AbsolutelyContinuous.rfl hgood hcond' hcond' j).2
  · apply Measure.map_congr
    filter_upwards [hinf] with q hq
    exact sbx_s6_all_records_eq_zero_of_infinite hd lam l q hq k

end AllScale
end EinsteinFull.Blueprint

#lint
