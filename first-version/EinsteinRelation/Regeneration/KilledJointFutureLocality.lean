import EinsteinRelation.Probability.LocalKernelVersion
import EinsteinRelation.Regeneration.FirstRegenerationEndpointFormula
import EinsteinRelation.Environment.FieldMeasurability

/-!
# Extending killed path/bit locality to the full future record

Source `paper/main.tex:383–387,413`. The environment restriction in the
future record is measurable for the future half-space. A local version
of the killed path/bit kernel therefore integrates every joint record
test locally. This extension uses no additional literature hypothesis.
-/

open MeasureTheory ProbabilityTheory

noncomputable section
attribute [local instance] Classical.propDecidable

namespace EinsteinRelation.Regeneration

/-- The origin future record uses only the path, bits and the physical
environment restricted to the source future half-space. -/
theorem measurable_origin_futureRecord_local {d : ℕ} (R : ℝ) (i : Fin d) :
    @Measurable (FieldPair d × CoupledSample d) (FutureState d i R)
      ((localSigma {x : Vec d | -2 * R ≤ x i}).prod inferInstance) inferInstance
      (fun p => spatialFutureRecord R i (0, p.1) p.2) := by
  letI : MeasurableSpace (FieldPair d × CoupledSample d) :=
    (localSigma {x : Vec d | -2 * R ≤ x i}).prod inferInstance
  have hpath : @Measurable (FieldPair d × CoupledSample d) (Path d)
      ((localSigma {x : Vec d | -2 * R ≤ x i}).prod inferInstance) inferInstance
      (fun p => (recenterSample (0 : Vec d) p.2).1) :=
    Probability.continuous_path_recenter.measurable.comp
      (measurable_const.prodMk measurable_snd.fst)
  have hbits : @Measurable (FieldPair d × CoupledSample d) BernoulliSequence
      ((localSigma {x : Vec d | -2 * R ≤ x i}).prod inferInstance) inferInstance
      (fun p => p.2.2) := measurable_snd.snd
  refine hpath.prodMk (hbits.prodMk ?_)
  apply measurable_pi_iff.mpr
  intro x
  have heval : Measurable[localSigma {x : Vec d | -2 * R ≤ x i}]
      (fun ω : FieldPair d => (ω.1 (x : Vec d), ω.2 (x : Vec d))) := by
    apply Measurable.of_comap_le
    exact le_iSup_of_le x le_rfl
  have hred := heval.comp (Probability.measurable_reduce_local {x : Vec d | -2 * R ≤ x i})
  have hf : @Measurable (FieldPair d × CoupledSample d) (FieldPair d)
      ((localSigma {x : Vec d | -2 * R ≤ x i}).prod inferInstance)
      (localSigma {x : Vec d | -2 * R ≤ x i}) Prod.fst := measurable_fst
  simpa [translate] using hred.comp hf

/-- Killed path/bit locality implies the origin local version of every
bounded joint future-record test. The premise is the existing internal
coupled-kernel locality target, not a new external input. -/
theorem killedJointFutureLocality_of_killedPathBitVersions {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (K : CoupledQuenchedLaws d) (hK : HasProbabilityLaws Q K) (R : ℝ) (i : Fin d)
    (hkilled : HasKilledPathBitFutureVersions Q i R K)
    (Φ : FutureState d i R → ℝ) (hΦ : Measurable Φ) (_hb : BoundedRealTest Φ) :
    ∃ A : FieldPair d → ℝ,
      Measurable[localSigma {x : Vec d | -2 * R ≤ x i}] A ∧
      ∀ᵐ ω ∂Q, A ω = ∫ z, killedFutureTest R i Φ ((0, ω), z) ∂K (0, ω) := by
  letI : PolishSpace (CoefficientField d) := Localization.coefficientField_polish d
  letI : PolishSpace (FieldPair d) := inferInstance
  letI : StandardBorelSpace (FieldPair d) := inferInstance
  let D : Set (CoupledSample d) := {z | NoBacktracking R z.1 i}
  have hDm : MeasurableSet D := (measurableSet_NoBacktracking R i).preimage measurable_fst
  let κ := (Probability.probabilityPart (originCoupledLaw K)).restrict hDm
  have hlocal : ∀ F : CoupledSample d → ℝ, Measurable F → BoundedRealTest F →
      ∃ A : FieldPair d → ℝ,
        Measurable[localSigma {x : Vec d | -2 * R ≤ x i}] A ∧
        A =ᵐ[Q] fun ω => ∫ z, F z ∂κ ω := by
    intro F hF hbF
    obtain ⟨A, hA, hAe⟩ := hkilled F hF hbF
    refine ⟨A, hA, ?_⟩
    filter_upwards [hAe, hK.1] with ω hω hp
    haveI : IsProbabilityMeasure (originCoupledLaw K ω) := hp
    rw [hω]
    simp only [κ, Kernel.restrict_apply,
      Probability.probabilityPart_eq_of_isProbabilityMeasure (originCoupledLaw K) ω]
    rw [← integral_indicator hDm]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun z => by
      by_cases hz : z ∈ D <;> simp [D] at hz ⊢ <;> simp [hz]
  obtain ⟨η, hηfinite, hη⟩ := Probability.exists_local_kernel_of_local_integral_versions
    Q κ (localSigma {x : Vec d | -2 * R ≤ x i})
    (Probability.localSigma_le_borel _) hlocal
  haveI := hηfinite
  refine ⟨fun ω => ∫ z, Φ (spatialFutureRecord R i (0, ω) z) ∂η ω,
    (hΦ.comp (measurable_origin_futureRecord_local R i)).stronglyMeasurable.integral_kernel_prod_right'
      |>.measurable, ?_⟩
  filter_upwards [hη, hK.1] with ω hω hp
  haveI : IsProbabilityMeasure (originCoupledLaw K ω) := hp
  rw [← hω]
  simp only [κ, Kernel.restrict_apply,
    Probability.probabilityPart_eq_of_isProbabilityMeasure (originCoupledLaw K) ω]
  rw [← integral_indicator hDm]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun z => by
    by_cases hz : z ∈ D <;> simp [D] at hz ⊢ <;> simp [killedFutureTest, hz]


end EinsteinRelation.Regeneration
