import EinsteinFull.Regeneration.UniformReturnAtGrid
import EinsteinFull.Regeneration.PhysicalKernelPredicate
import EinsteinFull.PhysicalRegeneration.Blueprint.Foundation.Proofs.SbxS7ConditionalTrialExhaustion
import EinsteinFull.PhysicalRegeneration.Blueprint.Foundation.node_app_u3A_factorization_u23_coupling_u2D_scope
import EinsteinFull.PhysicalRegeneration.Blueprint.Foundation.node_app_u3A_factorization_u23_past_u2D_kernel
import EinsteinFull.PhysicalRegeneration.Blueprint.Foundation.node_app_u3A_factorization_u23_slices
import EinsteinFull.PhysicalRegeneration.Blueprint.Foundation.node_app_u3A_regen_u2D_tails
import EinsteinFull.PhysicalRegeneration.Blueprint.G1.Proofs.W2Queue0440
import EinsteinFull.PhysicalRegeneration.Blueprint.G1.node_app_u3A_factorization_u23_independence_v2
import EinsteinFull.PhysicalRegeneration.Calculus.C10S3StoppedTubeProducer
import EinsteinFull.PhysicalRegeneration.Calculus.C1S3HistoryParameterIntegral
import EinsteinFull.PhysicalRegeneration.Calculus.SbxAGlobalReducedKernelR04
import EinsteinFull.PhysicalRegeneration.Calculus.SbxBCenteredLocalReturnClosureR15
import EinsteinFull.PhysicalRegeneration.Calculus.SbxBCenteredLocalReturnR13
import EinsteinFull.PhysicalRegeneration.Calculus.SbxBCenteredSurvivalR12
import EinsteinFull.PhysicalRegeneration.Calculus.SbxBCenteredTubeChainR03
import EinsteinFull.PhysicalRegeneration.Calculus.SbxS3JointReducedKernelR01
import EinsteinFull.PhysicalRegeneration.Calculus.SbxS6SuppliedKernelUniquenessR01
import EinsteinFull.PhysicalRegeneration.Frozen.RegenerationCoupling
import EinsteinFull.PhysicalRegeneration.Regeneration.GuardEstimate
import EinsteinFull.PhysicalRegeneration.Regeneration.ReducedCenteredSurvival
import EinsteinFull.PhysicalRegeneration.Vendor.Diffusion.GMPFamilyAPI
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.AnnealedUniformEndpointRestart
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.DeterministicEndpointNullSets
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.FirstRegenerationSliceFubini
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.KilledFutureConditionalMean
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.RenewalCarriers

/-!
# Physical-kernel version of
`EinsteinFull.Regeneration.UniformReturnAtGrid`

The declarations of that module that concern the reduced quenched kernel, stated and
proved for the physical quenched kernel of GMP Section 7: the zero-potential pair
`(exp(-2V) a₀, 0)` is replaced by the physical pair `ω = (a₀, V)`, regular at the same
bound `sourceReducedBound Λ₀` (`IsGMPPhysicalKernelReducedBound`).
-/


open MeasureTheory ProbabilityTheory EinsteinRelation EinsteinRelation.Regeneration
open EinsteinFull.Blueprint
open scoped NNReal ENNReal
namespace EinsteinFull.Regeneration
/-- The physical-kernel version of `EinsteinFull.Regeneration.grid_history_path_event_lower`. -/
theorem grid_history_path_event_lower_phys {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1)
    (l δ : ℝ) (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : IsRegenerationCouplingPhys hd Q lam l δ h0.le h1 P K)
    (m : ℕ) (S : Set (CoupledSample d))
    (hS : @MeasurableSet (CoupledSample d) (finiteHistorySigma (Renewal.regenDelta lam) m) S)
    (D : Set (Path d)) (hD : MeasurableSet D) (η : ℝ) (hη : 0 ≤ η)
    (hbound : ∀ᵐ ω ∂Q.measure, ∀ x, ENNReal.ofReal η ≤ P (x, ω) D) :
    let μ := annealedCoupledLaw Q.measure K
    η * μ.real {q | q.2 ∈ S} ≤ μ.real {q | q.2 ∈ S ∧
      (sampleTimeShift (Renewal.regenDelta lam) q.2
        ((m : ℝ≥0) * Renewal.regenDelta lam)).1 ∈ D} := by
  classical
  dsimp only
  let Δ := Renewal.regenDelta lam
  let μ := annealedCoupledLaw Q.measure K
  let : IsProbabilityMeasure Q.measure := Q.probability
  let : IsProbabilityMeasure μ := annealedCoupledLaw_isProbabilityMeasure Q.measure K hK.1
  have hSg : MeasurableSet S := EinsteinRelation.Probability.finiteHistorySigma_le Δ m S hS
  let A : CoupledSample d → ℝ := S.indicator (fun _ => 1)
  have hA : Measurable[finiteHistorySigma Δ m] A := measurable_const.indicator hS
  have hAg : Measurable A := hA.mono (EinsteinRelation.Probability.finiteHistorySigma_le Δ m) le_rfl
  let U : Set (ℝ × CoupledSample d) := {p | p.1 = 1 ∧ p.2.1 ∈ D}
  have hU : MeasurableSet U := (measurableSet_eq_fun measurable_fst measurable_const).inter
    (hD.preimage measurable_snd.fst)
  let F : ℝ × CoupledSample d → ℝ := U.indicator (fun _ => 1)
  have hF : Measurable F := measurable_const.indicator hU
  have hbF : BoundedRealTest F := by
    refine ⟨1, fun p => ?_⟩
    by_cases hp : p ∈ U <;> simp [F, hp]
  have hr := c10_s3_history_level_restart_phys hd Q lam h0 h1 l δ P K hK m A hA F hF hbF
  have hi := c10_s3_history_level_conditional_integrable_phys hd Q lam h0 h1 l δ P K hK m A hAg F hF hbF
  let E : Set (FieldPair d × CoupledSample d) := {q | q.2 ∈ S}
  let G : Set (FieldPair d × CoupledSample d) := {q | q.2 ∈ S ∧
    (sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)).1 ∈ D}
  have hE : MeasurableSet E := hSg.preimage measurable_snd
  have hG : MeasurableSet G := hE.inter (hD.preimage
    (((measurable_sampleTimeShift Δ).comp (measurable_const.prodMk measurable_snd)).fst))
  have hout : (∫ q, F (A q.2, sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)) ∂μ) = μ.real G := by
    rw [← integral_indicator_one hG]
    apply integral_congr_ae
    filter_upwards [] with q
    by_cases hs : q.2 ∈ S <;>
      by_cases hdmem : (sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)).1 ∈ D <;>
      simp [F, U, A, G, hs, hdmem]
  have hqmp : Measure.QuasiMeasurePreserving
      (Prod.fst : FieldPair d × CoupledSample d → FieldPair d) μ Q.measure := by
    refine ⟨measurable_fst, ?_⟩
    rw [c10_s3_annealed_environment_map Q K hK.1]
  have hinner : ∀ᵐ q ∂μ,
      η * E.indicator (fun _ => (1 : ℝ)) q ≤
        ∫ w, F (A q.2, w) ∂K (q.2.1 ((m : ℝ≥0) * Δ), q.1) := by
    filter_upwards [hqmp.ae hbound,
      c10_s3_grid_endpoint_path_marginal_phys hd Q lam h0 h1 l δ P K hK m,
      c10_s3_grid_endpoint_probability_phys hd Q lam h0 h1 l δ P K hK m] with q hb hm hp
    let ν := K (q.2.1 ((m : ℝ≥0) * Δ), q.1)
    let : IsProbabilityMeasure ν := hp
    by_cases hs : q.2 ∈ S
    · have hpD : ENNReal.ofReal η ≤ ν (Prod.fst ⁻¹' D) := by
        rw [← Measure.map_apply measurable_fst hD, hm]
        exact hb _
      have hpR : η ≤ ν.real (Prod.fst ⁻¹' D) := by
        have := ENNReal.toReal_mono (measure_ne_top ν _) hpD
        simpa only [ENNReal.toReal_ofReal hη, measureReal_def] using this
      have heq : (∫ w, F (A q.2, w) ∂ν) = ν.real (Prod.fst ⁻¹' D) := by
        rw [← integral_indicator_one (hD.preimage measurable_fst)]
        apply integral_congr_ae
        filter_upwards [] with w
        by_cases hw : w.1 ∈ D <;> simp [F, U, A, hs, hw]
      change η * E.indicator (fun _ => (1 : ℝ)) q ≤ ∫ w, F (A q.2, w) ∂ν
      rw [heq]
      simpa [E, hs] using hpR
    · simp [E, F, U, A, hs]
  have hEint : Integrable (E.indicator (fun _ => (1 : ℝ))) μ :=
    Integrable.of_bound (measurable_const.indicator hE).aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun q => by by_cases hq : q ∈ E <;> simp [hq])
  have h := integral_mono_ae (hEint.const_mul η) hi hinner
  rw [integral_const_mul, ← hr, hout] at h
  have he : (∫ q, E.indicator (fun _ => (1 : ℝ)) q ∂μ) = μ.real E := by
    change (∫ q, E.indicator (1 : (FieldPair d × CoupledSample d) → ℝ) q ∂μ) = μ.real E
    exact integral_indicator_one hE
  rw [he] at h
  exact h

/-- The physical-kernel version of
`EinsteinFull.Regeneration.trial_return_estimate_of_uniform_no_backtracking`. -/
theorem trial_return_estimate_of_uniform_no_backtracking_phys {d : ℕ} (hd : 2 ≤ d)
    {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1)
    (l δ : ℝ) (hl : 0 < l) (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : IsRegenerationCouplingPhys hd Q lam l δ h0.le h1 P K)
    (η : ℝ) (hη : 0 ≤ η)
    (hbound : ∀ᵐ ω ∂Q.measure, ∀ x, ENNReal.ofReal η ≤
      P (x, ω) {γ | NoBacktracking (l / lam) γ (Renewal.forceCoord hd)}) :
    ∀ n : ℕ,
      let μ := annealedCoupledLaw Q.measure K
      let Δ := Renewal.regenDelta lam
      let R := l / lam
      let i := Renewal.forceCoord hd
      let E := {q : FieldPair d × CoupledSample d | trialStartSequence Δ lam R q.2 i n ≠ ⊤}
      η * μ.real E ≤ μ.real (E ∩ {q | NoBacktracking R
        (pathTimeShift q.2.1 (trialStartSequence Δ lam R q.2 i n).toNNReal) i}) := by
  let : IsProbabilityMeasure Q.measure := Q.probability
  let μ := annealedCoupledLaw Q.measure K
  let : IsProbabilityMeasure μ := annealedCoupledLaw_isProbabilityMeasure Q.measure K hK.1
  let Δ := Renewal.regenDelta lam
  let R := l / lam
  let i := Renewal.forceCoord hd
  have hΔ : 0 < Δ := EinsteinRelation.regenDelta_pos h0
  have hR : 0 < R := div_pos hl h0
  have hslice : ∀ n m : ℕ,
      let S := {q : FieldPair d × CoupledSample d |
        trialStartSequence Δ lam R q.2 i n = ((((m + 1 : ℕ) : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞)}
      ENNReal.ofReal η * μ S ≤ μ (S ∩ {q | trialFailureTime Δ R q.2 i
        (trialStartSequence Δ lam R q.2 i n) = ⊤}) := by
    intro n m
    let S : Set (CoupledSample d) := {z | trialStartSequence Δ lam R z i n =
      ((((m + 1 : ℕ) : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞)}
    have hS : @MeasurableSet (CoupledSample d) (finiteHistorySigma Δ (m + 1)) S := by
      have hj := coupling_scope_measurableSet_trial_start_slice_annealedHistory Δ hΔ lam R hR i n m
      have hf : @Measurable (CoupledSample d) (FieldPair d × CoupledSample d)
          (finiteHistorySigma Δ (m + 1)) (couplingScopeAnnealedHistory Δ (m + 1))
          (fun z => (0, z)) := by
        apply Measurable.of_comap_le
        simp only [couplingScopeAnnealedHistory, MeasurableSpace.comap_comp, Function.comp_def]
        change MeasurableSpace.comap id (finiteHistorySigma Δ (m + 1)) ≤ _
        rw [MeasurableSpace.comap_id]
      exact hj.preimage hf
    let D : Set (Path d) := {γ | NoBacktracking R γ i}
    have hD : MeasurableSet D := measurableSet_NoBacktracking R i
    have hr := grid_history_path_event_lower_phys hd Q lam h0 h1 l δ P K hK (m + 1) S hS D hD η hη hbound
    have hreal : η * μ.real {q | q.2 ∈ S} ≤
        μ.real ({q | q.2 ∈ S} ∩ {q | NoBacktracking R
          (pathTimeShift q.2.1 (((m + 1 : ℕ) : ℝ≥0) * Δ)) i}) := by
      simpa only [Set.ofPred_and, sampleTimeShift, D, Δ, Set.mem_ofPred_eq] using hr
    have hENN := ENNReal.ofReal_le_ofReal hreal
    rw [ENNReal.ofReal_mul hη] at hENN
    simp only [measureReal_def] at hENN
    rw [ENNReal.ofReal_toReal (measure_ne_top μ _),
      ENNReal.ofReal_toReal (measure_ne_top μ _)] at hENN
    change ENNReal.ofReal η * μ {q | q.2 ∈ S} ≤ _
    rw [coupling_scope_trial_return_slice_eq Δ lam R i n m]
    exact hENN
  have hr := coupling_scope_return_estimate_of_slice_estimates μ Δ hΔ lam R i η hη hslice
  intro n
  have h := hr n
  dsimp only at h ⊢
  rw [coupling_scope_trial_return_event_eq Δ lam R i n] at h
  exact h

end EinsteinFull.Regeneration
