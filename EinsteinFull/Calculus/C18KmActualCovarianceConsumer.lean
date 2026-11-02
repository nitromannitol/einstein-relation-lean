import EinsteinFull.Calculus.C18KmDensePairingExtension

/-! Bilinear covariance for the actual coupled endpoint under a bounded-test action. -/

open MeasureTheory
open scoped NNReal ENNReal Topology
noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation

/-- The dense canonical action identifies the supplied coupled covariance. -/
theorem c18_km_actual_covariance_of_dense_action
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (q : ℝ≥0∞) (hq : 2 ≤ q) (hqfin : q ≠ ∞)
    (lam : ℝ) (t : ℝ≥0) :
    letI := reducedLaw_probability Q
    letI : Fact (1 ≤ q) := ⟨le_trans (by norm_num) hq⟩
    ∀ (T : Lp ℂ q (reducedLaw Q) →L[ℂ] Lp ℂ 2 Q.measure)
    (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
    (l δ : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (hK : IsRegenerationCoupling hd Q lam l δ h0 h1 P K)
    (hrep : ∀ H, T H =ᵐ[Q.measure]
      fun ω => ∫ γ : Path d, H (translate (γ t) (reduce ω)) ∂P (0, ω))
    (hbounded : ∀ f : BoundedContinuousFunction (FieldPair d) ℂ,
      T (BoundedContinuousFunction.toLp q (reducedLaw Q) ℂ f) =ᵐ[Q.measure]
        fun ω => forcedComplexEvolution Q (Regeneration.Renewal.forceCoord hd) (lam : ℂ) t
          (BoundedContinuousFunction.toLp 2 (reducedLaw Q) ℂ f) (reduce ω))
    (F G : Lp ℂ 2 (reducedLaw Q))
    (hGq : MemLp (G : FieldPair d → ℂ) q (reducedLaw Q))
    (hend : MemLp (fun w => G (sbxS4CoupledEndpoint t w)) 2
      (Regeneration.annealedCoupledLaw Q.measure K)),
    (∫ ω, F ω * forcedComplexEvolution Q (Regeneration.Renewal.forceCoord hd)
      (lam : ℂ) t G ω ∂reducedLaw Q) =
      ∫ w, F (reduce w.1) * G (sbxS4CoupledEndpoint t w)
        ∂Regeneration.annealedCoupledLaw Q.measure K := by
  let _ := reducedLaw_probability Q
  let _ : Fact (1 ≤ q) := ⟨le_trans (by norm_num) hq⟩
  intro T P K l δ h0 h1 hK hrep hbounded F G hGq hend
  let H := hGq.toLp (G : FieldPair d → ℂ)
  have he : (fun w => H (sbxS4CoupledEndpoint t w)) =ᵐ[
      Regeneration.annealedCoupledLaw Q.measure K]
      (fun w => G (sbxS4CoupledEndpoint t w)) :=
    sbxS4_ae_eq_coupledEndpoint_of_ae_eq hd Q lam l δ h0 h1 P K hK t hGq.coeFn_toLp
  have hHend : MemLp (fun w => H (sbxS4CoupledEndpoint t w)) 2
      (Regeneration.annealedCoupledLaw Q.measure K) := (memLp_congr_ae he).2 hend
  have hp := (sbxS4_L2_pairing_eq_supplied hd Q lam l δ h0 h1 P K hK t
    (Lp.memLp F) (Lp.stronglyMeasurable H).measurable hHend).2
  have haction := c18_km_extend_canonical_action_from_bounded hd Q q hq hqfin lam t
    T hbounded G hGq
  have hmean : (fun ω => ∫ γ : Path d, H (translate (γ t) (reduce ω)) ∂P (0, ω)) =ᵐ[Q.measure]
      fun ω => forcedComplexEvolution Q (Regeneration.Renewal.forceCoord hd) (lam : ℂ) t G (reduce ω) :=
    (hrep H).symm.trans haction
  calc
    _ = ∫ ω, F (reduce ω) * forcedComplexEvolution Q
        (Regeneration.Renewal.forceCoord hd) (lam : ℂ) t G (reduce ω) ∂Q.measure := by
      exact integral_map Probability.measurable_reduce.aemeasurable
        ((Lp.stronglyMeasurable F).aestronglyMeasurable.mul
          (Lp.stronglyMeasurable _).aestronglyMeasurable)
    _ = ∫ ω, F (reduce ω) * (∫ γ : Path d, H (translate (γ t) (reduce ω)) ∂P (0, ω)) ∂Q.measure := by
      apply integral_congr_ae
      filter_upwards [hmean] with ω hω
      rw [hω]
    _ = ∫ w, F (reduce w.1) * H (sbxS4CoupledEndpoint t w)
        ∂Regeneration.annealedCoupledLaw Q.measure K := hp.symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [he] with w hw
      rw [hw]

end EinsteinFull.Blueprint
