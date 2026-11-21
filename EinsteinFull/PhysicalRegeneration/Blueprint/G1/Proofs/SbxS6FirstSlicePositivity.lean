import EinsteinFull.Blueprint.G1.Proofs.SbxS6FirstSlicePositivity
import EinsteinFull.Regeneration.PhysicalKernelPredicate
import EinsteinFull.PhysicalRegeneration.Blueprint.Foundation.node_app_u3A_factorization_u23_past_u2D_kernel
import EinsteinFull.PhysicalRegeneration.Blueprint.Foundation.node_app_u3A_factorization_u23_slices
import EinsteinFull.PhysicalRegeneration.Blueprint.Foundation.node_app_u3A_regen_u2D_tails
import EinsteinFull.PhysicalRegeneration.Blueprint.G1.Proofs.C1ConditionIterate
import EinsteinFull.PhysicalRegeneration.Blueprint.G1.Proofs.SbxS6ConditionIterate
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
`EinsteinFull.Blueprint.G1.Proofs.SbxS6FirstSlicePositivity`

The declarations of that module that concern the reduced quenched kernel, stated and
proved for the physical quenched kernel of GMP Section 7: the zero-potential pair
`(exp(-2V) a₀, 0)` is replaced by the physical pair `ω = (a₀, V)`, regular at the same
bound `sourceReducedBound Λ₀` (`IsGMPPhysicalKernelReducedBound`).
-/


open Filter MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal InnerProductSpace
namespace EinsteinFull.Blueprint.FirstSlicePositivity
attribute [local instance 2000] EinsteinRelation.instMeasurableSpaceMat
open EinsteinRelation
open EinsteinRelation.External.GantertSection7Support
noncomputable section
section GMPBounds
variable {d : ℕ} {hd : 2 ≤ d} {L : ℝ} {hL : 1 ≤ L} {ω : FieldPair d}
  {hω : IsRegular L ω} {lam : ℝ} {h₀ : 0 ≤ lam} {h₁ : lam ≤ 1}
  (G : GantertFixedEnvironmentRealization hd L hL ω hω lam h₀ h₁)
end GMPBounds
section EndpointMass
open Regeneration
variable (hindep : node_app_u3A_factorization_u23_independenceStmtV2_phys)
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
    (l δ : ℝ) (hl : 0 < l) (hsep : r₀ < 2 * l) (hδ : 0 < δ) (hδ₁ : δ < 1)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : IsRegenerationCouplingPhys hd Q lam l δ h₀.le h₁ P K)
    (hD : annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam)) ≠ 0)
include hindep h₀ h₁ hl hsep hδ hδ₁ hK hD in
/-- The physical-kernel version of
`EinsteinFull.Blueprint.FirstSlicePositivity.firstSlice_spatial_mass_factorization`. -/
theorem firstSlice_spatial_mass_factorization_phys (n : ℕ) (hn : 2 ≤ n)
    (H : CoupledSample d → ℝ)
    (hH : Measurable[finiteHistorySigma (Renewal.regenDelta lam) (n - 1)] H)
    (hbH : BoundedRealTest H) :
    (∫ y, ∫ ω,
      firstSlicePastIntegral (Renewal.regenDelta lam) lam (l / lam)
          (Renewal.forceCoord hd) (n - 1) K H (y, ω) *
        (∫ z, killedFutureTest (l / lam) (Renewal.forceCoord hd)
          (fun _ => (1 : ℝ)) ((y, ω), z) ∂K (y, ω)) ∂Q.measure) =
      (∫ y, ∫ ω, firstSlicePastIntegral (Renewal.regenDelta lam) lam (l / lam)
          (Renewal.forceCoord hd) (n - 1) K H (y, ω) ∂Q.measure) *
        (annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam))).toReal := by
  have hdata := ((hindep d hd Λ₀ r₀ Q lam h₀ h₁ l δ hl hsep hδ hδ₁ P K hK hD
    (fun _ => (1 : ℝ)) measurable_const ⟨1, by simp⟩).1
      (fun _ => (1 : ℝ)) measurable_const ⟨1, by simp⟩ n hn H hH hbH)
  obtain ⟨_, hzero, hprod, hmean, _⟩ := hdata
  simp only [one_mul] at hzero hprod
  have hfactor : ∀ᵐ y ∂(volume : Measure (Vec d)),
      (∫ ω,
        firstSlicePastIntegral (Renewal.regenDelta lam) lam (l / lam)
            (Renewal.forceCoord hd) (n - 1) K H (y, ω) *
          (∫ z, killedFutureTest (l / lam) (Renewal.forceCoord hd)
            (fun _ => (1 : ℝ)) ((y, ω), z) ∂K (y, ω)) ∂Q.measure) =
        (∫ ω, firstSlicePastIntegral (Renewal.regenDelta lam) lam (l / lam)
            (Renewal.forceCoord hd) (n - 1) K H (y, ω) ∂Q.measure) *
          (annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam))).toReal := by
    filter_upwards [hzero, hprod, hmean] with y hz hp hm
    have hm' : (∫ ω, (∫ z, killedFutureTest (l / lam) (Renewal.forceCoord hd)
        (fun _ => (1 : ℝ)) ((y, ω), z) ∂K (y, ω)) ∂Q.measure) =
        (annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam))).toReal := by
      simpa only [integral_const, smul_eq_mul, mul_one, measureReal_def,
        Measure.restrict_apply_univ] using hm
    by_cases hy : y (Renewal.forceCoord hd) < 10 * (l / lam)
    · have hz' := hz hy
      have hleft := integral_congr_ae (hz'.mono fun ω hω =>
        congrArg (fun a : ℝ => a * (∫ z, killedFutureTest (l / lam)
          (Renewal.forceCoord hd) (fun _ => (1 : ℝ)) ((y, ω), z) ∂K (y, ω))) hω)
      rw [hleft, integral_congr_ae hz']
      simp only [Pi.zero_apply, zero_mul, integral_zero]
    · rw [(hp (le_of_not_gt hy)).2, hm']
  rw [integral_congr_ae hfactor, integral_mul_const]

include hindep h₀ h₁ hl hsep hδ hδ₁ hK hD in
/-- The physical-kernel version of
`EinsteinFull.Blueprint.FirstSlicePositivity.firstSlice_past_mass_factorization`. -/
theorem firstSlice_past_mass_factorization_phys (n : ℕ) (hn : 2 ≤ n)
    (H : CoupledSample d → ℝ)
    (hH : Measurable[finiteHistorySigma (Renewal.regenDelta lam) (n - 1)] H)
    (hbH : BoundedRealTest H) :
    (∫ q in {q : FieldPair d × CoupledSample d |
        firstRegenerationTime (Renewal.regenDelta lam) lam (l / lam) q.2
          (Renewal.forceCoord hd) =
            (((n : ℝ≥0) * Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)},
      H q.2 ∂annealedCoupledLaw Q.measure K) =
      δ * (∫ q, ((forcedBitTrialEvent (Renewal.regenDelta lam) lam (l / lam)
          (Renewal.forceCoord hd) (n - 1)).indicator H) q.2
        ∂annealedCoupledLaw Q.measure K) *
        (annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam))).toReal := by
  have hR : 0 < l / lam := div_pos hl h₀
  have hΔ : 0 < Renewal.regenDelta lam :=
    Real.toNNReal_pos.mpr (inv_pos.mpr (sq_pos_of_pos h₀))
  obtain ⟨C, _, B, hB, hbB, _, hBp⟩ :=
    exists_globally_bounded_measurable_killed_future_version Q.measure K hK.1
      (l / lam) (Renewal.forceCoord hd) (fun _ => (1 : ℝ)) measurable_const ⟨1, by simp⟩
  have hBp' : ∀ᵐ yω ∂(volume : Measure (Vec d)).prod Q.measure,
      B yω = ∫ z, killedFutureTest (l / lam) (Renewal.forceCoord hd)
        (fun _ => (1 : ℝ)) (yω, z) ∂K yω := hBp
  have hs := firstRegeneration_slice_integral_eq_phys hd Q lam h₀.le h₁ P K
    hK.1 hK.2.1 hK.2.2.1 (Renewal.regenDelta lam) hΔ
    δ (l / lam) hR (Renewal.forceCoord hd) hK.2.2.2.2.1 hK.2.2.2.2.2.2.1
    (fun _ => (1 : ℝ)) measurable_const ⟨1, by simp⟩ B hB ⟨C, hbB⟩ hBp'
    (n - 1) H hH hbH
  have hn' : n - 1 + 1 = n := Nat.sub_add_cancel (by omega)
  simp only [mul_one, hn'] at hs
  rw [hs]
  have hreplace :
      (∫ y, ∫ ω, firstSlicePastIntegral (Renewal.regenDelta lam) lam (l / lam)
          (Renewal.forceCoord hd) (n - 1) K H (y, ω) * B (y, ω) ∂Q.measure) =
      ∫ y, ∫ ω, firstSlicePastIntegral (Renewal.regenDelta lam) lam (l / lam)
          (Renewal.forceCoord hd) (n - 1) K H (y, ω) *
        (∫ z, killedFutureTest (l / lam) (Renewal.forceCoord hd)
          (fun _ => (1 : ℝ)) ((y, ω), z) ∂K (y, ω)) ∂Q.measure := by
    apply integral_congr_ae
    filter_upwards [MeasureTheory.Measure.ae_ae_of_ae_prod hBp'] with y hy
    exact integral_congr_ae (hy.mono fun ω hω => congrArg
      (fun b : ℝ => firstSlicePastIntegral (Renewal.regenDelta lam) lam (l / lam)
        (Renewal.forceCoord hd) (n - 1) K H (y, ω) * b) hω)
  rw [hreplace, firstSlice_spatial_mass_factorization_phys hindep hd Q lam h₀ h₁ l δ
    hl hsep hδ hδ₁ P K hK hD n hn H hH hbH]
  rw [div_eq_mul_inv, ← mul_assoc, mul_assoc δ]
  rw [spatial_past_mass_eq Q.measure K hK.1 (Renewal.regenDelta lam)
    hΔ lam (l / lam) hR (Renewal.forceCoord hd)
    (n - 1) H hH hbH]

/-- The physical-kernel version of `EinsteinFull.Blueprint.FirstSlicePositivity.firstTubeSlice`. -/
def firstTubeSlice_phys {d : ℕ} (hd : 2 ≤ d) (lam l : ℝ) :
    Set (FieldPair d × CoupledSample d) :=
  {q | q.2.1 ∈ tubeEvent (Renewal.forceCoord hd) lam l ∧
    firstRegenerationTime (Renewal.regenDelta lam) lam (l / lam) q.2
      (Renewal.forceCoord hd) = ((2 * Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)}

/-- The physical-kernel version of
`EinsteinFull.Blueprint.FirstSlicePositivity.measurableSet_firstTubeSlice`. -/
theorem measurableSet_firstTubeSlice_phys {d : ℕ} (hd : 2 ≤ d) (lam l : ℝ) :
    MeasurableSet (firstTubeSlice_phys hd lam l) :=
  ((measurableSet_tubeEvent (Renewal.forceCoord hd) lam l).preimage
      measurable_snd.fst).inter
    (measurableSet_eq_fun ((measurable_firstRegenerationTime _ _ _ _).comp
      measurable_snd) measurable_const)

include hindep h₀ h₁ hl hsep hδ hδ₁ hK hD in
/-- The physical-kernel version of
`EinsteinFull.Blueprint.FirstSlicePositivity.firstTubeSlice_mass`. -/
theorem firstTubeSlice_mass_phys :
    annealedCoupledLaw Q.measure K (firstTubeSlice_phys hd lam l) =
      ENNReal.ofReal δ * annealedCoupledLaw Q.measure K
        {q | q.2.1 ∈ tubeEvent (Renewal.forceCoord hd) lam l} *
      annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam)) := by
  let μ := annealedCoupledLaw Q.measure K
  have : IsProbabilityMeasure μ := annealedCoupledLaw_isProbabilityMeasure Q.measure K hK.1
  let A : Set (CoupledSample d) := {z | z.1 ∈ tubeEvent (Renewal.forceCoord hd) lam l}
  let T : Set (FieldPair d × CoupledSample d) := {q | q.2 ∈ A}
  let H : CoupledSample d → ℝ := A.indicator (fun _ => (1 : ℝ))
  have hA := measurableSet_tubeEvent_history (Renewal.forceCoord hd) lam l
  have hH : Measurable[finiteHistorySigma (Renewal.regenDelta lam) (2 - 1)] H := by
    exact measurable_const.indicator hA
  have hbH : BoundedRealTest H := by
    refine ⟨1, fun z => ?_⟩
    by_cases hz : z ∈ A <;> simp [H, hz]
  have hT : MeasurableSet T :=
    ((measurableSet_tubeEvent (Renewal.forceCoord hd) lam l).preimage measurable_fst).preimage
      measurable_snd
  have hstart := ae_origin_start_of_isGMPReducedKernel_phys hd Q lam h₀.le h₁ P K
    hK.1 hK.2.1 hK.2.2.1
  have hforced :
      (∫ q, ((forcedBitTrialEvent (Renewal.regenDelta lam) lam (l / lam)
          (Renewal.forceCoord hd) 1).indicator H) q.2 ∂μ) = (μ T).toReal := by
    calc
      _ = ∫ q, H q.2 ∂μ := by
        apply integral_congr_ae
        filter_upwards [hstart] with q hq
        by_cases ht : q.2 ∈ A
        · exact Set.indicator_of_mem (tubeEvent_mem_forcedBitTrialEvent hd h₀ h₁ hl
            q.2 hq ht) H
        · by_cases hf : q.2 ∈ forcedBitTrialEvent (Renewal.regenDelta lam) lam
              (l / lam) (Renewal.forceCoord hd) 1 <;> simp [hf, H, ht]
      _ = _ := by
        change (∫ q, T.indicator (fun _ => (1 : ℝ)) q ∂μ) = _
        rw [integral_indicator hT]
        simp only [integral_const, smul_eq_mul, mul_one, measureReal_def,
          Measure.restrict_apply_univ]
  have hraw := firstSlice_past_mass_factorization_phys hindep hd Q lam h₀ h₁ l δ
    hl hsep hδ hδ₁ P K hK hD 2 (by omega) H hH hbH
  simp only [Nat.reduceSub, Nat.cast_ofNat] at hraw
  rw [hforced] at hraw
  have hleft : (∫ q in {q : FieldPair d × CoupledSample d |
      firstRegenerationTime (Renewal.regenDelta lam) lam (l / lam) q.2
        (Renewal.forceCoord hd) = ((2 * Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)},
      H q.2 ∂μ) = (μ (firstTubeSlice_phys hd lam l)).toReal := by
    change (∫ q in _, T.indicator (fun _ => (1 : ℝ)) q ∂μ) = _
    rw [integral_indicator hT]
    simp only [integral_const, smul_eq_mul, mul_one, measureReal_def,
      Measure.restrict_apply_univ, Measure.restrict_apply hT]
    rfl
  rw [hleft] at hraw
  change μ (firstTubeSlice_phys hd lam l) = ENNReal.ofReal δ * μ T * _
  calc
    _ = ENNReal.ofReal (μ (firstTubeSlice_phys hd lam l)).toReal :=
      (ENNReal.ofReal_toReal (measure_ne_top μ _)).symm
    _ = ENNReal.ofReal (δ * (μ T).toReal *
        (μ (regenerationNoReturn hd (l / lam))).toReal) := congrArg ENNReal.ofReal hraw
    _ = _ := by
      rw [ENNReal.ofReal_mul (mul_nonneg hδ.le ENNReal.toReal_nonneg),
        ENNReal.ofReal_mul hδ.le, ENNReal.ofReal_toReal (measure_ne_top μ T),
        ENNReal.ofReal_toReal (measure_ne_top μ _)]

include h₀ h₁ hl hK in
/-- The physical-kernel version of
`EinsteinFull.Blueprint.FirstSlicePositivity.firstTubeSlice_noReturn_ae`. -/
theorem firstTubeSlice_noReturn_ae_phys :
    ∀ᵐ q ∂annealedCoupledLaw Q.measure K,
      q ∈ firstTubeSlice_phys hd lam l → q ∈ regenerationNoReturn hd (l / lam) := by
  have hstart := ae_origin_start_of_isGMPReducedKernel_phys hd Q lam h₀.le h₁ P K
    hK.1 hK.2.1 hK.2.2.1
  have hbar := c1_prebridge_survival_phys hd Q lam h₀ h₁ l δ hl P K hK 2 (by omega)
  filter_upwards [hstart, hbar] with q hq0 hq
  intro ht
  have hgeo := node_rt_u3A_renewal_u23_tube_u2D_geometry_of_deps d hd l hl lam h₀ h₁
    2 (Or.inl rfl) q.2.1 hq0 (by
      intro u hu
      have hu' : (u : ℝ) ≤ 1 := by norm_num at hu; exact hu
      simpa only [tubeCurve, ite_true] using ht.1 u hu')
  apply (hq (by
    simpa only [EinsteinFull.regenerationTime, regenerationTime_one, Nat.cast_ofNat]
      using ht.2)).2
  exact hgeo.2.2.2.2

include hindep h₀ h₁ hl hsep hδ hδ₁ hK hD in
/-- The physical-kernel version of
`EinsteinFull.Blueprint.FirstSlicePositivity.conditioned_firstTubeSlice_mass`. -/
theorem conditioned_firstTubeSlice_mass_phys :
    (regenerationConditionedLaw hd Q lam l K hK.1 hD) (firstTubeSlice_phys hd lam l) =
      ENNReal.ofReal δ * annealedCoupledLaw Q.measure K
        {q | q.2.1 ∈ tubeEvent (Renewal.forceCoord hd) lam l} := by
  let μ := annealedCoupledLaw Q.measure K
  have : IsProbabilityMeasure μ := annealedCoupledLaw_isProbabilityMeasure Q.measure K hK.1
  have hinter : μ (regenerationNoReturn hd (l / lam) ∩ firstTubeSlice_phys hd lam l) =
      μ (firstTubeSlice_phys hd lam l) := by
    apply measure_congr
    filter_upwards [firstTubeSlice_noReturn_ae_phys hd Q lam h₀ h₁ l δ hl P K hK] with q hq
    exact propext (and_iff_right_of_imp hq)
  rw [EinsteinFull.regenerationConditionedLaw_eq_cond,
    ProbabilityTheory.cond_apply' (measurableSet_firstTubeSlice_phys hd lam l)]
  change (μ (regenerationNoReturn hd (l / lam)))⁻¹ *
    μ (regenerationNoReturn hd (l / lam) ∩ firstTubeSlice_phys hd lam l) = _
  rw [hinter, firstTubeSlice_mass_phys hindep hd Q lam h₀ h₁ l δ hl hsep hδ hδ₁ P K hK hD]
  change (μ (regenerationNoReturn hd (l / lam)))⁻¹ *
    (ENNReal.ofReal δ * μ _ * μ (regenerationNoReturn hd (l / lam))) = _
  calc
    _ = (μ (regenerationNoReturn hd (l / lam)))⁻¹ *
        μ (regenerationNoReturn hd (l / lam)) * (ENNReal.ofReal δ * μ _) := by ac_rfl
    _ = _ := by rw [ENNReal.inv_mul_cancel hD (measure_ne_top μ _), one_mul]

include hindep h₀ h₁ hl hsep hδ hδ₁ hK hD in
/-- The physical-kernel version of
`EinsteinFull.Blueprint.FirstSlicePositivity.all_record_iteration_of_first_finite`. -/
theorem all_record_iteration_of_first_finite_phys
    (hfin : ∀ᵐ q ∂annealedCoupledLaw Q.measure K,
      firstRegenerationTime (Renewal.regenDelta lam) lam (l / lam) q.2
        (Renewal.forceCoord hd) ≠ ⊤) :
    let μ := annealedCoupledLaw Q.measure K
    let ν := regenerationConditionedLaw hd Q lam l K hK.1 hD
    (∀ ρ ∈ ({μ, ν} : Set (Measure (FieldPair d × CoupledSample d))),
      ∀ k : ℕ, ∀ᵐ q ∂ρ, EinsteinFull.regenerationTime hd lam l k q.2 ≠ ⊤) ∧
    (∀ ρ ∈ ({μ, ν} : Set (Measure (FieldPair d × CoupledSample d))),
      ∀ k : ℕ, 1 ≤ k →
        ρ.map (regenerationRecord hd lam l k) = ν.map (regenerationRecord hd lam l 0)) ∧
    ∃ Θ : FutureState d (Renewal.forceCoord hd) (l / lam) →
        FutureState d (Renewal.forceCoord hd) (l / lam),
      Measurable Θ ∧
      (∀ ρ ∈ ({μ, ν} : Set (Measure (FieldPair d × CoupledSample d))),
        ∀ k : ℕ, ∀ᵐ q ∂ρ,
          Θ (regenerationRecord hd lam l k q) = regenerationRecord hd lam l (k + 1) q) ∧
      (ν.map (regenerationRecord hd lam l 0)).map Θ =
        ν.map (regenerationRecord hd lam l 0) := by
  let μ := annealedCoupledLaw Q.measure K
  let ν := regenerationConditionedLaw hd Q lam l K hK.1 hD
  let Δ := Renewal.regenDelta lam
  let R := l / lam
  let i := Renewal.forceCoord hd
  have hΔ : 0 < Δ := Real.toNNReal_pos.mpr (inv_pos.mpr (sq_pos_of_pos h₀))
  have hνμ : ν ≪ μ :=
    EinsteinFull.regenerationConditionedLaw_absolutelyContinuous hd Q lam l K hK.1 hD
  have hfwd := ae_firstRegenerationTime_forward Q.measure K hK.1 Δ hΔ lam R h₀
    (div_pos hl h₀) i hK.2.2.2.2.2.1
  have hgood : ∀ᵐ q ∂μ, RecordCanShift Δ lam R i (iteratedRecord Δ lam R i 0 q) := by
    filter_upwards [hfin, hfwd] with q hq hforward
    change RecordCanShift Δ lam R i (futureRecord Δ R q.1 q.2 i 0)
    rw [recordCanShift_futureRecord_iff, sampleTimeShift_zero, zero_add]
    exact ⟨hq, hforward hq⟩
  have hfirst : μ.map (iteratedRecord Δ lam R i 1) = ν.map (iteratedRecord Δ lam R i 0) :=
    sbx_s6_annealed_first_law_phys hindep hd Q lam h₀ h₁ l δ hl hsep hδ hδ₁ P K hK hD
  have hcond : ν.map (iteratedRecord Δ lam R i 1) = ν.map (iteratedRecord Δ lam R i 0) :=
    sbx_s6_conditional_first_law_phys hindep hd Q lam h₀ h₁ l δ hl hsep hδ hδ₁ P K hK hD
  have hiter := iteratedRecord_law_of_first_and_conditional_law Δ hΔ lam R i μ ν
    hνμ hgood hfirst hcond
  have hfiniteall : ∀ ρ ∈ ({μ, ν} : Set (Measure (FieldPair d × CoupledSample d))),
      ∀ k : ℕ, ∀ᵐ q ∂ρ, EinsteinFull.regenerationTime hd lam l k q.2 ≠ ⊤ := by
    have hall : ∀ k : ℕ, ∀ᵐ q ∂μ, EinsteinFull.regenerationTime hd lam l k q.2 ≠ ⊤ := by
      intro k
      cases k with
      | zero => exact Filter.Eventually.of_forall fun _ => ENNReal.zero_ne_top
      | succ j => exact (hiter j).1
    intro ρ hρ k
    rcases Set.mem_insert_iff.mp hρ with rfl | hρ
    · exact hall k
    · obtain rfl := Set.mem_singleton_iff.mp hρ
      exact hνμ.ae_le (hall k)
  have hlaws : ∀ ρ ∈ ({μ, ν} : Set (Measure (FieldPair d × CoupledSample d))),
      ∀ k : ℕ, 1 ≤ k →
        ρ.map (regenerationRecord hd lam l k) = ν.map (regenerationRecord hd lam l 0) := by
    intro ρ hρ k hk
    rcases Set.mem_insert_iff.mp hρ with rfl | hρ
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
      exact (hiter j).2
    · obtain rfl := Set.mem_singleton_iff.mp hρ
      exact sbx_s6_conditional_all_record_laws_phys hindep hd Q lam h₀ h₁ l δ hl hsep hδ hδ₁ P K hK hD k
  obtain ⟨D, hDm, hdecode⟩ := Probability.exists_future_halfSpace_decoder i R
  let Θ := shiftRestrictedRecord Δ lam R i D
  have hΘ : Measurable Θ := measurable_shiftRestrictedRecord Δ lam R i D hDm
  have hσgood : ∀ᵐ y ∂ν.map (iteratedRecord Δ lam R i 0), RecordCanShift Δ lam R i y :=
    (ae_map_iff (measurable_iteratedRecord Δ lam R i 0).aemeasurable
      (measurableSet_recordCanShift Δ lam R i)).mpr (hνμ.ae_le hgood)
  have hcompose : ∀ k : ℕ, ∀ᵐ q ∂μ,
      Θ (regenerationRecord hd lam l k q) = regenerationRecord hd lam l (k + 1) q := by
    intro k
    have hkgood : ∀ᵐ q ∂μ, RecordCanShift Δ lam R i (iteratedRecord Δ lam R i k q) := by
      cases k with
      | zero => exact hgood
      | succ j =>
          rw [← (hiter j).2] at hσgood
          exact ae_of_ae_map (measurable_iteratedRecord Δ lam R i (j + 1)).aemeasurable hσgood
    have hkfin : ∀ᵐ q ∂μ, Regeneration.regenerationTime Δ lam R q.2 i k ≠ ⊤ := by
      cases k with
      | zero => exact Filter.Eventually.of_forall fun _ => ENNReal.zero_ne_top
      | succ j => exact (hiter j).1
    filter_upwards [hkgood, hkfin] with q hq hqfin
    exact (iteratedRecord_succ_of_canShift Δ hΔ lam R i D hdecode q k hqfin hq).2.symm
  refine ⟨hfiniteall, hlaws, Θ, hΘ, ?_, ?_⟩
  · intro ρ hρ k
    rcases Set.mem_insert_iff.mp hρ with rfl | hρ
    · exact hcompose k
    · obtain rfl := Set.mem_singleton_iff.mp hρ
      exact hνμ.ae_le (hcompose k)
  · rw [Measure.map_map hΘ (EinsteinFull.measurable_regenerationRecord hd lam l 0)]
    exact (Measure.map_congr (hνμ.ae_le (hcompose 0))).trans hcond

include hindep h₀ h₁ hl hsep hδ hδ₁ hK hD in
/-- The physical-kernel version of
`EinsteinFull.Blueprint.FirstSlicePositivity.condition_iterate_of_first_finite`. -/
theorem condition_iterate_of_first_finite_phys
    (hfin : ∀ᵐ q ∂annealedCoupledLaw Q.measure K,
      firstRegenerationTime (Renewal.regenDelta lam) lam (l / lam) q.2
        (Renewal.forceCoord hd) ≠ ⊤) :
    let R := l / lam
    let i := Regeneration.Renewal.forceCoord hd
    let Δ := Regeneration.Renewal.regenDelta lam
    let μ := Regeneration.annealedCoupledLaw Q.measure K
    let ν := regenerationConditionedLaw hd Q lam l K
      hK.1 hD
    (∀ n : ℕ, 2 ≤ n → ∀ᵐ q ∂μ,
      EinsteinFull.regenerationTime hd lam l 1 q.2 =
        (((n : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞) →
      (q ∈ regenerationNoReturn hd R ↔
        ∀ s : ℝ≥0, s ≤ (n - 1 : ℕ) * Δ → -R < q.2.1 s i)) ∧
    (∃ Θ : Regeneration.FutureState d i R → Regeneration.FutureState d i R,
      Measurable Θ ∧
      (∀ ρ ∈ ({μ, ν} : Set (Measure (FieldPair d × Regeneration.CoupledSample d))),
        ∀ k : ℕ, ∀ᵐ q ∂ρ,
          Θ (regenerationRecord hd lam l k q) = regenerationRecord hd lam l (k + 1) q) ∧
      Measure.map Θ (Measure.map (regenerationRecord hd lam l 0) ν) =
        Measure.map (regenerationRecord hd lam l 0) ν) ∧
    (∀ (Φ : Regeneration.FutureState d i R → ℝ),
      Measurable Φ → Regeneration.BoundedRealTest Φ →
      ∀ ρ ∈ ({μ, ν} : Set (Measure (FieldPair d × Regeneration.CoupledSample d))),
      (∀ k : ℕ, 1 ≤ k →
        (∫ q, Φ (regenerationRecord hd lam l k q) ∂ρ) =
          ∫ q, Φ (regenerationRecord hd lam l 0 q) ∂ν) ∧
      (∀ (F : FieldPair d → ℝ),
        Measurable[localSigma {x : Vec d | euclideanNorm x < R}] F →
        Regeneration.BoundedRealTest F →
        ∀ (n : ℕ), 2 ≤ n → ∀ (H : Regeneration.CoupledSample d → ℝ),
        Measurable[Regeneration.finiteHistorySigma Δ (n - 1)] H →
        Regeneration.BoundedRealTest H →
        (∫ q in {q | EinsteinFull.regenerationTime hd lam l 1 q.2 =
          (((n : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞)},
          F q.1 * H q.2 * Φ (regenerationRecord hd lam l 1 q) ∂ρ) =
        (∫ q in {q | EinsteinFull.regenerationTime hd lam l 1 q.2 =
          (((n : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞)}, F q.1 * H q.2 ∂ρ) *
          ∫ q, Φ (regenerationRecord hd lam l 0 q) ∂ν)) := by
  obtain ⟨_, hlaws, hshift⟩ := all_record_iteration_of_first_finite_phys hindep hd Q lam
    h₀ h₁ l δ hl hsep hδ hδ₁ P K hK hD hfin
  dsimp only
  refine ⟨?_, hshift, ?_⟩
  · intro n hn
    exact c1_prebridge_survival_phys hd Q lam h₀ h₁ l δ hl P K hK n hn
  · intro Φ hΦ hbΦ ρ hρ
    refine ⟨?_, ?_⟩
    · intro k hk
      have hmap := hlaws ρ hρ k hk
      calc
        _ = ∫ y, Φ y ∂ρ.map (regenerationRecord hd lam l k) :=
          (integral_map (EinsteinFull.measurable_regenerationRecord hd lam l k).aemeasurable
            hΦ.aestronglyMeasurable).symm
        _ = ∫ y, Φ y ∂(regenerationConditionedLaw hd Q lam l K hK.1 hD).map
            (regenerationRecord hd lam l 0) := by rw [hmap]
        _ = _ := integral_map
          (EinsteinFull.measurable_regenerationRecord hd lam l 0).aemeasurable
          hΦ.aestronglyMeasurable
    · intro F hF hbF n hn H hH hbH
      exact sbx_s6_slice_factor_both_phys hindep hd Q lam h₀ h₁ l δ hl hsep hδ hδ₁ P K hK hD
        Φ hΦ hbΦ F hF hbF n hn H hH hbH ρ hρ

end EndpointMass
open Regeneration
end
end EinsteinFull.Blueprint.FirstSlicePositivity
