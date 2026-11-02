import EinsteinRelation.Regeneration.OneIntervalLocality
import EinsteinFull.Work.W1.StoppedKernelLocalitySupport

open MeasureTheory
open scoped NNReal ENNReal

noncomputable section

namespace EinsteinFull.Blueprint

open EinsteinRelation

/-- Conditional transport of both one-interval integrals from equality of the
actual exit-stopped path laws. -/
theorem c4_future_integral_pair_of_stopped_map_eq
    {d : ℕ} (Δ : ℝ≥0) (R : ℝ) (hR : 0 < R) (i : Fin d)
    (P : QuenchedPathLaws d) (y : Vec d) (ω ω' : FieldPair d)
    (hy : -R ≤ y i)
    (hstop : (P (y, ω)).map (Diffusion.localityStoppedPath {x : Vec d | -2 * R < x i}) =
      (P (y, ω')).map (Diffusion.localityStoppedPath {x : Vec d | -2 * R < x i}))
    (F : Path d → ℝ) (hF : Measurable F)
    (hsegment : ∀ γ γ' : Path d, (∀ t : ℝ≥0, t ≤ Δ → γ t = γ' t) → F γ = F γ')
    (hsupport : ∀ γ, F γ ≠ 0 → ∀ t : ℝ≥0, t ≤ Δ → -R ≤ γ t i) :
    ((∫ γ, F γ ∂P (y, ω)) = ∫ γ, F γ ∂P (y, ω')) ∧
      ((∫ γ, F γ ∂Regeneration.Renewal.killedBridgeMixture Δ R i P y ω) =
        ∫ γ, F γ ∂Regeneration.Renewal.killedBridgeMixture Δ R i P y ω') := by
  let U : Set (Vec d) := {x | -2 * R < x i}
  have hU : IsOpen U := isOpen_lt continuous_const (continuous_apply i)
  have hm := EinsteinFull.measurable_localityStoppedPath U hU
  have hball : Regeneration.couplingRegion i R y ⊆ U :=
    Regeneration.couplingRegion_subset_future_halfSpace i R y hy
  have hkill : (Regeneration.Renewal.killedSegmentLaw Δ R i P y ω).map
      (Diffusion.stopPathAt Δ) =
      (Regeneration.Renewal.killedSegmentLaw Δ R i P y ω').map
        (Diffusion.stopPathAt Δ) := by
    exact Diffusion.map_restrict_stopPathAt_eq_of_stoppedLaw_eq U _ hU
      (Regeneration.isOpen_couplingRegion i R y) hball Δ _ _ hm hstop
  have hbridge := Regeneration.map_endpoint_reweighted_eq_of_map_stopPathAt_eq Δ _ _
    (ProbabilityTheory.cond (volume : Measure (Vec d)) (Regeneration.endpointBall i R y)) hkill
  refine ⟨Regeneration.integral_supported_segment_eq_of_stoppedLaw_eq U hU Δ _ _ hm hstop
    F hF hsegment ?_, ?_⟩
  · intro γ hγ t ht
    have h := hsupport γ hγ t ht
    change -2 * R < γ t i
    linarith
  · exact Regeneration.integral_eq_of_map_stopPathAt_eq Δ _ _ hbridge F hF hsegment

end EinsteinFull.Blueprint
