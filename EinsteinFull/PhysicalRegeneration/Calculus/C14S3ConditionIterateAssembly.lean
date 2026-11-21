import EinsteinFull.Calculus.C14S3ConditionIterateAssembly
import EinsteinFull.Regeneration.PhysicalKernelPredicate
import EinsteinFull.PhysicalRegeneration.Blueprint.Foundation.node_app_u3A_factorization_u23_past_u2D_kernel
import EinsteinFull.PhysicalRegeneration.Blueprint.Foundation.node_app_u3A_factorization_u23_slices
import EinsteinFull.PhysicalRegeneration.Blueprint.Foundation.node_app_u3A_regen_u2D_tails
import EinsteinFull.PhysicalRegeneration.Blueprint.G1.Proofs.C1ConditionIterate
import EinsteinFull.PhysicalRegeneration.Blueprint.G1.Proofs.SbxS6ConditionIterate
import EinsteinFull.PhysicalRegeneration.Blueprint.G1.Proofs.SbxS6FirstSlicePositivity
import EinsteinFull.PhysicalRegeneration.Blueprint.G1.node_app_u3A_factorization_u23_condition_u2D_iterate
import EinsteinFull.PhysicalRegeneration.Blueprint.G1.node_app_u3A_factorization_u23_independence_v2
import EinsteinFull.PhysicalRegeneration.Calculus.C10S3ConditionedFinitePositive
import EinsteinFull.PhysicalRegeneration.Frozen.RegenerationCoupling
import EinsteinFull.PhysicalRegeneration.Vendor.Diffusion.GMPFamilyAPI
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.AnnealedUniformEndpointRestart
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.DeterministicEndpointNullSets
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.FirstRegenerationSliceFubini
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.KilledFutureConditionalMean
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.RenewalCarriers

/-!
# Physical-kernel version of
`EinsteinFull.Calculus.C14S3ConditionIterateAssembly`

The declarations of that module that concern the reduced quenched kernel, stated and
proved for the physical quenched kernel of GMP Section 7: the zero-potential pair
`(exp(-2V) a₀, 0)` is replaced by the physical pair `ω = (a₀, V)`, regular at the same
bound `sourceReducedBound Λ₀` (`IsGMPPhysicalKernelReducedBound`).
-/

open MeasureTheory
open scoped NNReal ENNReal InnerProductSpace
namespace EinsteinFull.Blueprint
open EinsteinRelation Regeneration
open EinsteinRelation.External.GantertSection7Support
/-- The physical-kernel version of
`EinsteinFull.Blueprint.c14_condition_iterate_of_conditioned_first_finite_positive`. -/
theorem c14_condition_iterate_of_conditioned_first_finite_positive_phys
    (hindep : node_app_u3A_factorization_u23_independenceStmtV2_phys)
    (hpositive : ∀ {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
      (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
      (l δ : ℝ) (_hl : 0 < l) (_hsep : r₀ < 2 * l) (_hδ : 0 < δ) (_hδ₁ : δ < 1)
      (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
      (hK : IsRegenerationCouplingPhys hd Q lam l δ h₀.le h₁ P K)
      (hD : annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam)) ≠ 0),
      (regenerationConditionedLaw hd Q lam l K hK.1 hD)
        {q | firstRegenerationTime (Renewal.regenDelta lam) lam (l / lam) q.2
          (Renewal.forceCoord hd) ≠ ⊤} ≠ 0) :
    node_app_u3A_factorization_u23_condition_u2D_iterateStmt_phys := by
  intro d hd Λ₀ r₀ Q lam h₀ h₁ l δ hl hsep hδ hδ₁ P K hK hD
  have hfin := (sbx_s6_first_finite_iff_conditioned_positive_phys hindep hd Q lam h₀ h₁
    l δ hl hsep hδ hδ₁ P K hK hD).2
    (hpositive hd Q lam h₀ h₁ l δ hl hsep hδ hδ₁ P K hK hD)
  exact FirstSlicePositivity.condition_iterate_of_first_finite_phys hindep hd Q lam h₀ h₁
    l δ hl hsep hδ hδ₁ P K hK hD hfin

/-- The physical-kernel version of
`EinsteinFull.Blueprint.c14_s3_condition_iterate_of_annealed_tube_positive`. -/
theorem c14_s3_condition_iterate_of_annealed_tube_positive_phys
    (h1 : node_app_u3A_factorization_u23_independenceStmtV2_phys)
    (h2 : node_app_u3A_factorization_u23_slicesStmt_phys)
    (h3 : node_app_u3A_regen_u2D_tailsStmt_phys)
    (c10_s3_actual_annealed_tube_positive : ∀
      (_hindep : node_app_u3A_factorization_u23_independenceStmtV2_phys)
      (_hslices : node_app_u3A_factorization_u23_slicesStmt_phys)
      (_htails : node_app_u3A_regen_u2D_tailsStmt_phys)
      {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
      (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ)
      (_hl : 0 < l) (_hsep : r₀ < 2 * l) (_hδ0 : 0 < δ) (_hδ1 : δ < 1)
      (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
      (_hK : IsRegenerationCouplingPhys hd Q lam l δ h0.le h1 P K)
      (_hD : Regeneration.annealedCoupledLaw Q.measure K
        (regenerationNoReturn hd (l / lam)) ≠ 0),
      Regeneration.annealedCoupledLaw Q.measure K
        {q | q.2.1 ∈ FirstSlicePositivity.tubeEvent (Regeneration.Renewal.forceCoord hd) lam l} ≠ 0) :
    node_app_u3A_factorization_u23_condition_u2D_iterateStmt_phys := by
  apply c14_condition_iterate_of_conditioned_first_finite_positive_phys h1
  intro d hd Λ₀ r₀ Q lam h0 hlam l δ hl hsep hδ0 hδ1 P K hK hD
  have hmass := c10_s3_first_finite_mass_lower_phys h1 hd Q lam h0 hlam l δ hl hsep
    hδ0 hδ1 P K hK hD
  have hnonzero : ENNReal.ofReal δ * Regeneration.annealedCoupledLaw Q.measure K
      {q | q.2.1 ∈ FirstSlicePositivity.tubeEvent (Regeneration.Renewal.forceCoord hd) lam l} ≠ 0 :=
    mul_ne_zero (ne_of_gt (ENNReal.ofReal_pos.mpr hδ0))
      (c10_s3_actual_annealed_tube_positive h1 h2 h3 hd Q lam h0 hlam l δ hl hsep
        hδ0 hδ1 P K hK hD)
  intro hzero
  rw [hzero] at hmass
  exact hnonzero (le_antisymm hmass bot_le)

/-- The physical-kernel version of
`EinsteinFull.Blueprint.c14_s3_condition_iterate_of_requested_killed_analytic`. -/
theorem c14_s3_condition_iterate_of_requested_killed_analytic_phys
    (requested_s3_killed_orbit_analytic : ∀ {d : ℕ} (hd : 2 ≤ d) (L : ℝ)
      (hL : 1 ≤ L) (ω : FieldPair d) (hω : IsRegular L ω) (lam : ℝ)
      (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
      (G : GantertFixedEnvironmentRealization hd L hL ω hω lam h0 h1)
      (U : Set (Vec d)) (hU : IsOpen U)
      (g v : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)),
      AnalyticOnNhd ℝ (fun r : ℝ => inner ℝ v
        (gmpKilledL2Operator G U hU r.toNNReal g)) (Set.Ioi 0))
    (h1 : node_app_u3A_factorization_u23_independenceStmtV2_phys)
    (h2 : node_app_u3A_factorization_u23_slicesStmt_phys)
    (h3 : node_app_u3A_regen_u2D_tailsStmt_phys) :
    node_app_u3A_factorization_u23_condition_u2D_iterateStmt_phys := by
  exact c14_s3_condition_iterate_of_annealed_tube_positive_phys h1 h2 h3
    (fun _ _ _ {d} hd {Λ₀ r₀} Q lam h0 hlam l δ hl _ _ _ P K hK _ =>
      c10_s3_annealed_tube_of_killed_analytic_minimal_phys
        requested_s3_killed_orbit_analytic hd Q lam h0 hlam l δ hl P K hK)

end EinsteinFull.Blueprint
