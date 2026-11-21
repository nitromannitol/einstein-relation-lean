import EinsteinFull.Calculus.C1S3HistoryParameterIntegral
import EinsteinFull.Calculus.C11SourceAssociationVelocity

/-! # Finite trial entries from the foundation consumers

The positive reduced velocity given by the GMP velocity law under the source association makes
the coupled path escape along the force; with the even-guard estimate this gives finite trial
entries after every grid restart.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation Regeneration EinsteinRelation.External.GantertSection7Support

@[nolint unusedArguments]
private theorem c1_s3_escape_of_foundation_consumers
    (physical_mp_ae_unique : ∀ (d : ℕ) (_hd : 2 ≤ d) (Λ₀ r₀ : ℝ)
      (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (lam : ℝ) (PX PX' : QuenchedPathLaws d)
      (_hX : ∀ᵐ ω ∂Q.measure, SolvesMartingaleProblem (physicalGenerator i ω lam) 0 (PX (0, ω)))
      (_hX' : ∀ᵐ ω ∂Q.measure, SolvesMartingaleProblem (physicalGenerator i ω lam) 0 (PX' (0, ω))),
      ∀ᵐ ω ∂Q.measure, PX (0, ω) = PX' (0, ω))
    (requested_s3_pathwise_foundation : node_eq_u2E_reduced_u2D_generator_u23_pathwiseStmt)
    (requested_s3_supplied_reduced_mp : ∀ {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
      (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
      (P : QuenchedPathLaws d), IsGMPReducedKernel hd Q.ellipticity_parameter Q lam h0 h1 P →
      ∀ᵐ ω ∂Q.measure, SolvesMartingaleProblem
        (reducedGenerator (Regeneration.Renewal.forceCoord hd) ω lam) 0 (P (0, ω))) :
    ∀ (_htails : node_app_u3A_regen_u2D_tailsStmt) {d : ℕ} (hd : 2 ≤ d)
      {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h0 : 0 < lam)
      (h1 : lam ≤ 1) (l δ : ℝ) (_hl : 0 < l) (_hsep : r₀ < 2 * l)
      (_hδ0 : 0 < δ) (_hδ1 : δ < 1) (P : QuenchedPathLaws d)
      (K : Regeneration.CoupledQuenchedLaws d)
      (_hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K)
      (_hD : Regeneration.annealedCoupledLaw Q.measure K
        (regenerationNoReturn hd (l / lam)) ≠ 0),
      ∀ᵐ q ∂ Regeneration.annealedCoupledLaw Q.measure K,
        Filter.Tendsto (fun t : ℝ≥0 => q.2.1 t (Regeneration.Renewal.forceCoord hd))
          Filter.atTop Filter.atTop := by
  intro _htails d hd Λ₀ r₀ Q lam h0 h1 l δ _hl _hsep _hδ0 _hδ1 P K hK _hD
  have hassoc : ∀ (d : ℕ) (hd : 2 ≤ d) (L R : ℝ) (Q : EnvironmentLaw d L R)
      (mu : ℝ) (hmu0 : 0 < mu) (hmu1 : mu ≤ 1)
      (P : ProbabilityTheory.Kernel (FieldPair d) (Path d)),
      (∀ᵐ ω ∂Q.measure, SolvesMartingaleProblem
        (physicalGenerator (firstCoordinateIndex hd) ω mu) 0 (P ω)) →
      IsGMPPhysicalOriginLaw hd Q.ellipticity_parameter Q mu hmu0.le hmu1 P := by
    intro d hd L R Q mu hmu0 hmu1 P hP
    obtain ⟨K, _, hsource, hKmp⟩ := u6_foundation_regular_signed_origin_law_and_mp
      hd Q.ellipticity_parameter Q mu hmu0.le hmu1
    exact physical_origin_law_of_source_mp physical_mp_ae_unique hd Q hmu0.le hmu1
      K P hsource hKmp hP
  have hY := requested_s3_supplied_reduced_mp hd Q lam h0.le h1 P hK.2.2.1
  obtain ⟨v, hv, hvpos⟩ := forced_reduced_signed_velocity_of_source_association
    hassoc requested_s3_pathwise_foundation d hd Λ₀ r₀ Q lam h0.ne' P hY
  have hpos : 0 < v (Regeneration.Renewal.forceCoord hd) :=
    (mul_pos_iff_of_pos_left h0).mp hvpos
  have hmeas : MeasurableSet {q : FieldPair d × Regeneration.CoupledSample d |
      HasPathVelocity q.2.1 v} :=
    measurableSet_joint_path_velocity.preimage
      ((measurable_fst.comp measurable_snd).prodMk measurable_const)
  have hvel : ∀ᵐ q ∂ Regeneration.annealedCoupledLaw Q.measure K,
      HasPathVelocity q.2.1 v := by
    apply Measure.ae_compProd_of_ae_ae hmeas
    filter_upwards [hK.1.1, hK.2.1.1, hv] with ω hprob hmap hvel
    let : IsProbabilityMeasure (Regeneration.originCoupledLaw K ω) := hprob
    rw [Probability.probabilityPart_eq_of_isProbabilityMeasure
      (Regeneration.originCoupledLaw K) ω]
    have hm : ∀ᵐ γ ∂(K (0, ω)).map Prod.fst, HasPathVelocity γ v := by
      rw [hmap]
      exact hvel
    exact ae_of_ae_map measurable_fst.aemeasurable hm
  filter_upwards [hvel] with q hq
  exact ConditionalTrialExhaustion.directional_escape_of_positive_velocity
    q.2.1 v (Regeneration.Renewal.forceCoord hd) hq hpos

theorem c1_s3_actual_entries_of_foundation_guard (physical_mp_ae_unique : ∀ (d : ℕ) (_hd : 2 ≤ d) (Λ₀ r₀ : ℝ) (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (lam : ℝ) (PX PX' : QuenchedPathLaws d) (_hX : ∀ᵐ ω ∂Q.measure, SolvesMartingaleProblem (physicalGenerator i ω lam) 0 (PX (0, ω))) (_hX' : ∀ᵐ ω ∂Q.measure, SolvesMartingaleProblem (physicalGenerator i ω lam) 0 (PX' (0, ω))), ∀ᵐ ω ∂Q.measure, PX (0, ω) = PX' (0, ω)) (requested_s3_pathwise_foundation : node_eq_u2E_reduced_u2D_generator_u23_pathwiseStmt) (requested_s3_supplied_reduced_mp : ∀ {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1) (P : QuenchedPathLaws d), IsGMPReducedKernel hd Q.ellipticity_parameter Q lam h0 h1 P → ∀ᵐ ω ∂Q.measure, SolvesMartingaleProblem (reducedGenerator (Regeneration.Renewal.forceCoord hd) ω lam) 0 (P (0, ω))) (hGuard : ∀ (_htails : node_app_u3A_regen_u2D_tailsStmt) {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ) (_hl : 0 < l) (_hsep : r₀ < 2 * l) (_hδ0 : 0 < δ) (_hδ1 : δ < 1) (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d) (_hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K) (_hD : Regeneration.annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam)) ≠ 0), let Δ := Regeneration.Renewal.regenDelta lam; let R := l / lam; let i := Regeneration.Renewal.forceCoord hd; ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ∀ (m : ℕ) (A : Regeneration.CoupledSample d → ℝ), @Measurable (Regeneration.CoupledSample d) ℝ (Regeneration.finiteHistorySigma Δ m) inferInstance A → ∀ N : ℕ, let E := couplingScopeEvenGuardFailure Δ lam R A m i Set.univ N ∩ {q | couplingScopePassage Δ lam R A m i (2 * N) q.2 ≠ ⊤}; ε * (Regeneration.annealedCoupledLaw Q.measure K).real E ≤ (Regeneration.annealedCoupledLaw Q.measure K).real (E ∩ {q | q.2 ∈ couplingScopeEvenGuard Δ lam R A m i N})) (htails : node_app_u3A_regen_u2D_tailsStmt) {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ) (hl : 0 < l) (hsep : r₀ < 2 * l) (hδ0 : 0 < δ) (hδ1 : δ < 1) (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d) (hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K) (hD : Regeneration.annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam)) ≠ 0) : let Δ := Regeneration.Renewal.regenDelta lam; let R := l / lam; let i := Regeneration.Renewal.forceCoord hd; ∀ᵐ q ∂ Regeneration.annealedCoupledLaw Q.measure K, ∀ m : ℕ, let w := Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ); Regeneration.trialStartSequence Δ lam R w i 0 ≠ ⊤ ∧ ∀ n : ℕ, Regeneration.trialFailureTime Δ R w i (Regeneration.trialStartSequence Δ lam R w i n) ≠ ⊤ → Regeneration.trialStartSequence Δ lam R w i (n + 1) ≠ ⊤ := by
  exact c1_s3_actual_entries_of_escape_guard
    (c1_s3_escape_of_foundation_consumers physical_mp_ae_unique
      requested_s3_pathwise_foundation requested_s3_supplied_reduced_mp)
    hGuard htails hd Q lam h0 h1 l δ hl hsep hδ0 hδ1 P K hK hD

theorem c1_s3_entries_of_foundation_guard_reduced_mp_discharged (physical_mp_ae_unique : ∀ (d : ℕ) (_hd : 2 ≤ d) (Λ₀ r₀ : ℝ) (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (lam : ℝ) (PX PX' : QuenchedPathLaws d) (_hX : ∀ᵐ ω ∂Q.measure, SolvesMartingaleProblem (physicalGenerator i ω lam) 0 (PX (0, ω))) (_hX' : ∀ᵐ ω ∂Q.measure, SolvesMartingaleProblem (physicalGenerator i ω lam) 0 (PX' (0, ω))), ∀ᵐ ω ∂Q.measure, PX (0, ω) = PX' (0, ω)) (requested_s3_pathwise_foundation : node_eq_u2E_reduced_u2D_generator_u23_pathwiseStmt) (hGuard : ∀ (_htails : node_app_u3A_regen_u2D_tailsStmt) {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ) (_hl : 0 < l) (_hsep : r₀ < 2 * l) (_hδ0 : 0 < δ) (_hδ1 : δ < 1) (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d) (_hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K) (_hD : Regeneration.annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam)) ≠ 0), let Δ := Regeneration.Renewal.regenDelta lam; let R := l / lam; let i := Regeneration.Renewal.forceCoord hd; ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ∀ (m : ℕ) (A : Regeneration.CoupledSample d → ℝ), @Measurable (Regeneration.CoupledSample d) ℝ (Regeneration.finiteHistorySigma Δ m) inferInstance A → ∀ N : ℕ, let E := couplingScopeEvenGuardFailure Δ lam R A m i Set.univ N ∩ {q | couplingScopePassage Δ lam R A m i (2 * N) q.2 ≠ ⊤}; ε * (Regeneration.annealedCoupledLaw Q.measure K).real E ≤ (Regeneration.annealedCoupledLaw Q.measure K).real (E ∩ {q | q.2 ∈ couplingScopeEvenGuard Δ lam R A m i N})) (htails : node_app_u3A_regen_u2D_tailsStmt) {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ) (hl : 0 < l) (hsep : r₀ < 2 * l) (hδ0 : 0 < δ) (hδ1 : δ < 1) (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d) (hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K) (hD : Regeneration.annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam)) ≠ 0) : let Δ := Regeneration.Renewal.regenDelta lam; let R := l / lam; let i := Regeneration.Renewal.forceCoord hd; ∀ᵐ q ∂ Regeneration.annealedCoupledLaw Q.measure K, ∀ m : ℕ, let w := Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ); Regeneration.trialStartSequence Δ lam R w i 0 ≠ ⊤ ∧ ∀ n : ℕ, Regeneration.trialFailureTime Δ R w i (Regeneration.trialStartSequence Δ lam R w i n) ≠ ⊤ → Regeneration.trialStartSequence Δ lam R w i (n + 1) ≠ ⊤ := by
  exact c1_s3_actual_entries_of_foundation_guard physical_mp_ae_unique
    requested_s3_pathwise_foundation EinsteinFull.u2_arbitrary_supplied_reduced_kernel_MP
    hGuard htails hd Q lam h0 h1 l δ hl hsep hδ0 hδ1 P K hK hD

end EinsteinFull.Blueprint
