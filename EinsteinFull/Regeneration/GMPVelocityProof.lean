import EinsteinFull.External.Draft.GMPVelocity
import EinsteinFull.Regeneration.PhysicalFactorization
import EinsteinFull.Regeneration.PhysicalCoupling
import EinsteinFull.Regeneration.PhysicalRecordLaws
import EinsteinFull.Regeneration.PhysicalFirstCycleIndependence
import EinsteinFull.Regeneration.PhysicalCycleMoments
import EinsteinFull.Regeneration.PhysicalWindowMaximum

/-!
# The positive quenched velocity of the physical diffusion

GMP 2012, Theorem 5.6 and Proposition 5.9, for the physical diffusion of Section 7 itself:
the physical kernel carries the split coupling of Proposition 5.4; under the law conditioned on
no return the regeneration records have one law, the first cycle is independent of the next
record, the first regeneration time and the maximal displacement of the first cycle are
integrable (Lemma 5.8), and the renewal argument gives the quenched velocity, whose
coordinate along the force is positive.
-/

open MeasureTheory ProbabilityTheory EinsteinRelation EinsteinRelation.Regeneration
open scoped NNReal ENNReal

attribute [local instance 2000] EinsteinRelation.instMeasurableSpaceMat

namespace EinsteinFull.External

/-- GMP 2012, the positive quenched velocity of the physical origin process
(`Draft.gmpVelocityStmt`), proved by regenerating the physical process. -/
theorem gmp_velocity_holds : EinsteinFull.External.Draft.gmpVelocityStmt := by
  intro d hd L R Q _ lam h₀ h₁ P₀ hP₀
  have : IsProbabilityMeasure Q.measure := Q.probability
  obtain ⟨l₀, hl₀, hr₀, htails⟩ := Blueprint.node_app_u3A_regen_u2D_tails_phys d hd L R
  set l := max l₀ 1 with hldef
  have hl1 : 1 ≤ l := le_max_right _ _
  have hll₀ : l₀ ≤ l := le_max_left _ _
  have hl : 0 < l := lt_of_lt_of_le one_pos hl1
  have hsep : R < 2 * l := lt_of_lt_of_le hr₀ (by linarith)
  obtain ⟨δ, hδ₀, hδ₁, hcoup⟩ :=
    EinsteinFull.Regeneration.exists_physical_regeneration_coupling d hd L R l hl1
  obtain ⟨c, C, a, M, hc, hC, ha, _, _, hT⟩ := htails l hll₀ δ hδ₀ hδ₁
  obtain ⟨b, Cw, hb, hCw, hwinall⟩ :=
    EinsteinFull.Regeneration.uniform_physical_window_absolute_maximum_moment hd L R
  obtain ⟨P, hPk, -, -, -⟩ :=
    EinsteinFull.Regeneration.global_physical_kernel_exists hd Q lam h₀.le h₁
  obtain ⟨P', K, hPP', hK⟩ := hcoup Q lam h₀ h₁ P hPk
  obtain ⟨hD, -, htau, -, hmD⟩ := hT Q lam h₀ h₁ P' K hK
  obtain ⟨Θ, hΘm, hΘμ, hΘν, hμ, hν⟩ := EinsteinFull.Regeneration.physical_record_laws
    Blueprint.node_app_u3A_factorization_u23_condition_u2D_iterate_phys d hd L R Q lam h₀ h₁
    l δ hl hsep hδ₀ hδ₁ P' K hK hD
  have : IsProbabilityMeasure (Regeneration.annealedCoupledLaw Q.measure K) :=
    annealedCoupledLaw_isProbabilityMeasure Q.measure K hK.1
  have : IsProbabilityMeasure (regenerationConditionedLaw hd Q lam l K hK.1 hD) :=
    ProbabilityTheory.cond_isProbabilityMeasure hD
  have hΔ : 0 < Renewal.regenDelta lam := EinsteinRelation.regenDelta_pos h₀
  have hR : 0 < l / lam := div_pos hl h₀
  have htail' : HasFirstRegenerationTail Q.measure (Renewal.regenDelta lam) lam (l / lam) c C
      (Renewal.forceCoord hd) K := by
    intro t ht
    simpa only [EinsteinFull.regenerationTime, regenerationTime_one] using htau t ht
  have h1μ := firstRegenerationTime_ne_top_ae_of_tail Q.measure K (Renewal.regenDelta lam) lam
    (l / lam) c C hc h₀ (Renewal.forceCoord hd) htail'
  have h1ν : ∀ᵐ q ∂regenerationConditionedLaw hd Q lam l K hK.1 hD,
      firstRegenerationTime (Renewal.regenDelta lam) lam (l / lam) q.2
        (Renewal.forceCoord hd) ≠ ⊤ :=
    ProbabilityTheory.cond_absolutelyContinuous.ae_le h1μ
  have hfinite := EinsteinFull.Regeneration.ae_regenerationTime_ne_top_of_record_laws
    (Renewal.regenDelta lam) lam (l / lam) (Renewal.forceCoord hd) _ _ hμ h1μ h1ν
  have hfac := Blueprint.physical_first_cycle_indepFun
    Blueprint.node_app_u3A_factorization_u23_past_u2D_kernel_phys
    Blueprint.node_app_u3A_factorization_u23_future_u2D_kernel_phys
    Blueprint.node_app_u3A_factorization_u23_slices_phys
    Blueprint.node_app_u3A_factorization_u23_coupling_u2D_scope_phys
    hd Q lam h₀ h₁ l δ hl hsep hδ₀ hδ₁ P' K hK hD (hν 1 le_rfl)
  have hdur := EinsteinFull.Regeneration.physical_record_duration_integrable hd Q lam h₀ l K hK.1
    hD a M ha hmD
  have hmax := fun j => EinsteinFull.Regeneration.physical_record_maximum_integrable hd Q lam
    h₀ h₁ l δ hl hsep hδ₀ hδ₁ P' K hK hD c C hc hC htau b Cw hb hCw
    (hwinall Q lam h₀ h₁ P' hK.2.2.1) j
  obtain ⟨v, hv, hvpos⟩ := EinsteinFull.Regeneration.quenched_velocity_of_record_factorization
    Q.measure P' K hK.1 hK.2.1 (Renewal.regenDelta lam) hΔ lam (l / lam) h₀ hR
    (Renewal.forceCoord hd) hK.2.2.2.2.2.1 (regenerationConditionedLaw hd Q lam l K hK.1 hD)
    hfinite Θ hΘm hΘμ hΘν hμ hν hfac hdur hmax
  refine ⟨v, ?_, hvpos⟩
  have horigin := EinsteinFull.Regeneration.ae_originLaw_eq_of_isGMPPhysicalKernel hd Q lam
    h₀.le h₁ P₀ P hP₀ hPk
  filter_upwards [hv, horigin, hPP'] with ω hω hω₀ hω'
  rw [hω₀, ← hω' 0]
  simpa only [originLaw_apply] using hω

end EinsteinFull.External
