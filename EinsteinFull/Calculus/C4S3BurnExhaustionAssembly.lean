import EinsteinFull.Blueprint.Foundation.Proofs.SbxS7ConditionalTrialExhaustion

open EinsteinRelation Regeneration MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace EinsteinFull.Blueprint

/-- Entry and burn hypotheses, together with contraction of the lost events,
ensure finite first regeneration at every grid start almost surely. -/
theorem c4_s3_all_grid_finite_of_burn_and_entries
    {d : ℕ} (μ : Measure (FieldPair d × CoupledSample d)) [IsProbabilityMeasure μ]
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (lam R : ℝ) (i : Fin d)
    (hentry : ∀ᵐ q ∂μ, ∀ m : ℕ,
      let w := sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)
      trialStartSequence Δ lam R w i 0 ≠ ⊤ ∧
        ∀ n, trialFailureTime Δ R w i (trialStartSequence Δ lam R w i n) ≠ ⊤ →
          trialStartSequence Δ lam R w i (n + 1) ≠ ⊤)
    (hburn : ∀ᵐ q ∂μ, ∀ m : ℕ,
      (∀ n, trialStartSequence Δ lam R (sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)) i n ≠ ⊤) →
      ∃ J, q ∈ couplingScopeTrialBurn Δ lam R m i J)
    (η : ℝ) (hη : 0 < η)
    (hstep : ∀ m J N, μ (couplingScopeTrialLost Δ lam R m i J (N + 1)) ≤
      ENNReal.ofReal (1 - η) * μ (couplingScopeTrialLost Δ lam R m i J N)) :
    ∀ᵐ q ∂μ, ∀ m : ℕ,
      firstRegenerationTime Δ lam R (sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)) i ≠ ⊤ := by
  have hnull (m : ℕ) : μ (⋃ J, ⋂ N, couplingScopeTrialLost Δ lam R m i J N) = 0 := by
    apply measure_iUnion_null
    intro J
    exact ConditionalTrialExhaustion.measure_iInter_eq_zero_of_failure_step μ _
      (fun N => coupling_scope_measurableSet_trial_lost Δ lam R m i J N)
      (coupling_scope_trial_lost_antitone Δ lam R m i J) _
      (ENNReal.ofReal_lt_one.mpr (by linarith)) (hstep m J)
  have havoid : ∀ᵐ q ∂μ, ∀ m : ℕ,
      q ∉ ⋃ J, ⋂ N, couplingScopeTrialLost Δ lam R m i J N := by
    apply ae_all_iff.mpr
    intro m
    rw [ae_iff]
    simpa only [not_not, Set.ofPred_mem_eq] using hnull m
  filter_upwards [hentry, hburn, havoid] with q he hb hn m htop
  let w := sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)
  have hfinite := (coupling_scope_first_regeneration_eq_top_iff_all_trials_finite
    Δ hΔ lam R w i (he m).1 (he m).2).mp htop
  obtain ⟨J, hJ⟩ := hb m hfinite
  apply hn m
  refine Set.mem_iUnion.mpr ⟨J, Set.mem_iInter.mpr ?_⟩
  intro N
  change (q ∈ couplingScopeTrialBurn Δ lam R m i J) ∧
    ∀ r < N, trialFailureTime Δ R w i
      (trialStartSequence Δ lam R w i (J + r)) ≠ ⊤
  refine ⟨hJ, ?_⟩
  intro r _hr hfail
  have htrial : IsRegenerationTrial Δ lam R w i (J + r) :=
    ⟨hfinite (J + r), hfail⟩
  have hle : firstRegenerationTime Δ lam R w i ≤
      trialStartSequence Δ lam R w i (J + r) :=
    iInf_le_of_le (J + r) (iInf_le_of_le htrial le_rfl)
  exact hfinite (J + r) (top_le_iff.mp (htop ▸ hle))

end EinsteinFull.Blueprint
