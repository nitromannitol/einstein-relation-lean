import EinsteinFull.Blueprint.G1.Proofs.SbxS6FirstSlicePositivity

open Filter MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal InnerProductSpace

namespace EinsteinFull.Blueprint

open EinsteinRelation
open EinsteinRelation.External.GantertSection7Support
open Regeneration

noncomputable section

/-- The conditioned probability of a finite first regeneration time dominates
the quantitative mass of the literal first tube slice. -/
theorem c10_s3_first_finite_mass_lower
    (hindep : node_app_u3A_factorization_u23_independenceStmtV2)
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ)
    (hl : 0 < l) (hsep : r₀ < 2 * l) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K)
    (hD : Regeneration.annealedCoupledLaw Q.measure K
      (regenerationNoReturn hd (l / lam)) ≠ 0) :
    ENNReal.ofReal δ * Regeneration.annealedCoupledLaw Q.measure K
      {q | q.2.1 ∈ FirstSlicePositivity.tubeEvent (Regeneration.Renewal.forceCoord hd) lam l} ≤
    (regenerationConditionedLaw hd Q lam l K hK.1 hD)
      {q | Regeneration.firstRegenerationTime (Regeneration.Renewal.regenDelta lam)
        lam (l / lam) q.2 (Regeneration.Renewal.forceCoord hd) ≠ ⊤} := by
  rw [← FirstSlicePositivity.conditioned_firstTubeSlice_mass hindep hd Q lam h0 h1
    l δ hl hsep hδ0 hδ1 P K hK hD]
  apply measure_mono
  intro q hq
  change firstRegenerationTime (Renewal.regenDelta lam) lam (l / lam) q.2
    (Renewal.forceCoord hd) ≠ ⊤
  rw [hq.2]
  exact ENNReal.coe_ne_top

private theorem annealed_tube_of_killed_analytic
    (requested_s3_killed_orbit_analytic : ∀ {d : ℕ} (hd : 2 ≤ d) (L : ℝ)
      (hL : 1 ≤ L) (ω : FieldPair d) (hω : IsRegular L ω) (lam : ℝ)
      (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
      (G : GantertFixedEnvironmentRealization hd L hL ω hω lam h0 h1)
      (U : Set (Vec d)) (hU : IsOpen U)
      (g v : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)),
      AnalyticOnNhd ℝ (fun r : ℝ => inner ℝ v
        (gmpKilledL2Operator G U hU r.toNNReal g)) (Set.Ioi 0)) :
    ∀ {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
      (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ)
      (hl : 0 < l)
      (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
      (hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K),
      Regeneration.annealedCoupledLaw Q.measure K
        {q | q.2.1 ∈ FirstSlicePositivity.tubeEvent (Regeneration.Renewal.forceCoord hd) lam l} ≠ 0 := by
  intro d hd Λ₀ r₀ Q lam h0 h1 l δ hl P K hK
  have hpath : ∀ᵐ ω ∂Q.measure, 0 < P (0, ω)
      (FirstSlicePositivity.tubeEvent (Renewal.forceCoord hd) lam l) := by
    filter_upwards [hK.2.2.1] with ω hω
    obtain ⟨hreg, G, hG⟩ := hω
    rw [hG 0]
    apply FirstSlicePositivity.tubeEvent_mass_pos_of_mesh_indicator_self G
      (Renewal.forceCoord hd) l hl h0
    intro k hk t ht htime
    apply FirstSlicePositivity.killedL2_positive_time_support_invariant_of_analytic G _ _ t ht
    · filter_upwards [indicatorConstLp_coeFn (p := 2)
        (hs := (FirstSlicePositivity.isOpen_meshBall lam ((l / 32) / 16)
          (FirstSlicePositivity.tubeCenters (Renewal.forceCoord hd) l (k + 1))).measurableSet)
        (hμs := FirstSlicePositivity.physicalReversibleMeasure_meshBall_ne_top
          (ω := zeroPotentialReducedPair ω) (hd := hd) h0 (by positivity)
          (FirstSlicePositivity.tubeCenters (Renewal.forceCoord hd) l (k + 1)))
        (c := (1 : ℝ))] with x hx
      rw [hx]
      by_cases hx : x ∈ FirstSlicePositivity.meshBall lam ((l / 32) / 16)
          (FirstSlicePositivity.tubeCenters (Renewal.forceCoord hd) l (k + 1)) <;> simp [hx]
    · intro v
      exact requested_s3_killed_orbit_analytic hd (sourceReducedBound Λ₀)
        (one_le_sourceReducedBound Q.ellipticity_parameter) (zeroPotentialReducedPair ω) hreg
        lam h0.le h1 G _ _ _ v
  exact (FirstSlicePositivity.annealed_tubeEvent_mass_pos Q.measure K P hK.1 hK.2.1
    (Renewal.forceCoord hd) lam l hpath).ne'


/-- Killed-orbit analyticity yields positivity for the actual annealed tube. -/
theorem c10_s3_annealed_tube_of_killed_analytic_minimal
    (requested_s3_killed_orbit_analytic : ∀ {d : ℕ} (hd : 2 ≤ d) (L : ℝ)
      (hL : 1 ≤ L) (ω : FieldPair d) (hω : IsRegular L ω) (lam : ℝ)
      (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
      (G : GantertFixedEnvironmentRealization hd L hL ω hω lam h0 h1)
      (U : Set (Vec d)) (hU : IsOpen U)
      (g v : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)),
      AnalyticOnNhd ℝ (fun r : ℝ => inner ℝ v
        (gmpKilledL2Operator G U hU r.toNNReal g)) (Set.Ioi 0)) :
    ∀ {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
      (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ)
      (hl : 0 < l)
      (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
      (hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K),
      Regeneration.annealedCoupledLaw Q.measure K
        {q | q.2.1 ∈ FirstSlicePositivity.tubeEvent (Regeneration.Renewal.forceCoord hd) lam l} ≠ 0 := by
  exact annealed_tube_of_killed_analytic requested_s3_killed_orbit_analytic


/-- The requested killed-orbit analyticity implies positivity of the actual
annealed tube. This is a conditional consumer, not an analyticity assertion. -/
theorem c10_s3_annealed_tube_of_requested_killed_analytic
    (requested_s3_killed_orbit_analytic : ∀ {d : ℕ} (hd : 2 ≤ d) (L : ℝ)
      (hL : 1 ≤ L) (ω : FieldPair d) (hω : IsRegular L ω) (lam : ℝ)
      (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
      (G : GantertFixedEnvironmentRealization hd L hL ω hω lam h0 h1)
      (U : Set (Vec d)) (hU : IsOpen U)
      (g v : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)),
      AnalyticOnNhd ℝ (fun r : ℝ => inner ℝ v
        (gmpKilledL2Operator G U hU r.toNNReal g)) (Set.Ioi 0)) :
    ∀ {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
      (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ)
      (hl : 0 < l)
      (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
      (hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K),
      Regeneration.annealedCoupledLaw Q.measure K
        {q | q.2.1 ∈ FirstSlicePositivity.tubeEvent (Regeneration.Renewal.forceCoord hd) lam l} ≠ 0 := by
  exact annealed_tube_of_killed_analytic requested_s3_killed_orbit_analytic


end

end EinsteinFull.Blueprint
