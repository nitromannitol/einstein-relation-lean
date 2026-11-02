import EinsteinFull.Blueprint.G1.Proofs.SbxS6FirstSlicePositivity
import EinsteinFull.Blueprint.G1.node_app_u3A_factorization_u23_condition_u2D_iterate
import EinsteinFull.Blueprint.Foundation.node_app_u3A_factorization_u23_slices
import EinsteinFull.Calculus.C10S3ConditionedFinitePositive

open MeasureTheory
open scoped NNReal ENNReal InnerProductSpace

namespace EinsteinFull.Blueprint

open EinsteinRelation Regeneration
open EinsteinRelation.External.GantertSection7Support

/-- Support only: the exact condition-iterate conclusion follows from the
original-scale conditioned finite-first-time positivity producer. The extra
producer argument is not a graph dependency. -/
theorem c14_condition_iterate_of_conditioned_first_finite_positive
    (hindep : node_app_u3A_factorization_u23_independenceStmtV2)
    (hpositive : ∀ {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
      (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
      (l δ : ℝ) (hl : 0 < l) (hsep : r₀ < 2 * l) (hδ : 0 < δ) (hδ₁ : δ < 1)
      (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
      (hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K)
      (hD : annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam)) ≠ 0),
      (regenerationConditionedLaw hd Q lam l K hK.1 hD)
        {q | firstRegenerationTime (Renewal.regenDelta lam) lam (l / lam) q.2
          (Renewal.forceCoord hd) ≠ ⊤} ≠ 0) :
    node_app_u3A_factorization_u23_condition_u2D_iterateStmt := by
  intro d hd Λ₀ r₀ Q lam h₀ h₁ l δ hl hsep hδ hδ₁ P K hK hD
  have hfin := (sbx_s6_first_finite_iff_conditioned_positive hindep hd Q lam h₀ h₁
    l δ hl hsep hδ hδ₁ P K hK hD).2
    (hpositive hd Q lam h₀ h₁ l δ hl hsep hδ hδ₁ P K hK hD)
  exact FirstSlicePositivity.condition_iterate_of_first_finite hindep hd Q lam h₀ h₁
    l δ hl hsep hδ hδ₁ P K hK hD hfin

/-- The condition-iterate conclusion follows from positivity of the actual
annealed first tube at the original scale. -/
theorem c14_s3_condition_iterate_of_annealed_tube_positive
    (h1 : node_app_u3A_factorization_u23_independenceStmtV2)
    (h2 : node_app_u3A_factorization_u23_slicesStmt)
    (h3 : node_app_u3A_regen_u2D_tailsStmt)
    (c10_s3_actual_annealed_tube_positive : ∀
      (hindep : node_app_u3A_factorization_u23_independenceStmtV2)
      (hslices : node_app_u3A_factorization_u23_slicesStmt)
      (htails : node_app_u3A_regen_u2D_tailsStmt)
      {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
      (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ)
      (hl : 0 < l) (hsep : r₀ < 2 * l) (hδ0 : 0 < δ) (hδ1 : δ < 1)
      (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
      (hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K)
      (hD : Regeneration.annealedCoupledLaw Q.measure K
        (regenerationNoReturn hd (l / lam)) ≠ 0),
      Regeneration.annealedCoupledLaw Q.measure K
        {q | q.2.1 ∈ FirstSlicePositivity.tubeEvent (Regeneration.Renewal.forceCoord hd) lam l} ≠ 0) :
    node_app_u3A_factorization_u23_condition_u2D_iterateStmt := by
  apply c14_condition_iterate_of_conditioned_first_finite_positive h1
  intro d hd Λ₀ r₀ Q lam h0 hlam l δ hl hsep hδ0 hδ1 P K hK hD
  have hmass := c10_s3_first_finite_mass_lower h1 hd Q lam h0 hlam l δ hl hsep
    hδ0 hδ1 P K hK hD
  have hnonzero : ENNReal.ofReal δ * Regeneration.annealedCoupledLaw Q.measure K
      {q | q.2.1 ∈ FirstSlicePositivity.tubeEvent (Regeneration.Renewal.forceCoord hd) lam l} ≠ 0 :=
    mul_ne_zero (ne_of_gt (ENNReal.ofReal_pos.mpr hδ0))
      (c10_s3_actual_annealed_tube_positive h1 h2 h3 hd Q lam h0 hlam l δ hl hsep
        hδ0 hδ1 P K hK hD)
  intro hzero
  rw [hzero] at hmass
  exact hnonzero (le_antisymm hmass bot_le)

/-- The requested killed-orbit analyticity supplies the condition-iterate
conclusion through positivity of the actual annealed tube. -/
theorem c14_s3_condition_iterate_of_requested_killed_analytic
    (requested_s3_killed_orbit_analytic : ∀ {d : ℕ} (hd : 2 ≤ d) (L : ℝ)
      (hL : 1 ≤ L) (ω : FieldPair d) (hω : IsRegular L ω) (lam : ℝ)
      (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
      (G : GantertFixedEnvironmentRealization hd L hL ω hω lam h0 h1)
      (U : Set (Vec d)) (hU : IsOpen U)
      (g v : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)),
      AnalyticOnNhd ℝ (fun r : ℝ => inner ℝ v
        (gmpKilledL2Operator G U hU r.toNNReal g)) (Set.Ioi 0))
    (h1 : node_app_u3A_factorization_u23_independenceStmtV2)
    (h2 : node_app_u3A_factorization_u23_slicesStmt)
    (h3 : node_app_u3A_regen_u2D_tailsStmt) :
    node_app_u3A_factorization_u23_condition_u2D_iterateStmt := by
  exact c14_s3_condition_iterate_of_annealed_tube_positive h1 h2 h3
    (fun _ _ _ {d} hd {Λ₀ r₀} Q lam h0 hlam l δ hl _ _ _ P K hK _ =>
      c10_s3_annealed_tube_of_killed_analytic_minimal
        requested_s3_killed_orbit_analytic hd Q lam h0 hlam l δ hl P K hK)

end EinsteinFull.Blueprint
