import EinsteinRelation.Correctors.StationarySpatialGradientApproximation
import EinsteinRelation.Correctors.CenteredPotentialLimit
import EinsteinRelation.Calculus.WeakRepresentativeOperations
import EinsteinRelation.Regeneration.HalfSpaces

/-!
# Scalar spatial weak potentials of closed stationary gradients

Source: `paper/main.tex:693-698,727-729`. Rapid scalar H¹ approximations
converge locally in the samplewise spatial L² gradient norm. Centering
and Poincaré give actual scalar weak potentials on every positive ball.
-/

open MeasureTheory Filter Topology
noncomputable section
namespace EinsteinRelation.Correctors
open External.AKM External.GilbargTrudinger StationarySpatialRealization

/-- The Euclidean ball is contained in a compact ball of the coordinate
carrier. This comparison does not replace the Euclidean norm in estimates. -/
theorem euclideanBall_subset_coordinateClosedBall {d : ℕ} (R : ℝ) (hR : 0 ≤ R) :
    ball (0 : Vec d) R ⊆ Metric.closedBall (0 : Vec d) R := by
  intro x hx
  have hx' : euclideanNorm x < R := by simpa [ball, sub_zero] using hx
  rw [Metric.mem_closedBall, dist_pi_le_iff hR]
  intro i
  simpa only [Real.dist_eq, Pi.zero_apply, sub_zero] using
    (Regeneration.coordinate_abs_le_euclideanNorm x i).trans hx'.le

/-- Every actual closed-domain stationary gradient has scalar weak
potentials on all positive Euclidean balls on one common full-measure event.
The only source input is the existing explicit GT Poincaré proposition. -/
theorem ae_exists_spatial_weakPotential_of_closed_gradient
    (hP : BallPoincareEstimate) {d : ℕ} [Fact (2 ≤ d)]
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q] (hQ : IsStationary Q)
    (G : Lp (EuclideanSpace ℝ (Fin d)) 2 Q)
    (hG : G ∈ stationaryPotentialGradientSubmodule Q hQ) :
    ∀ᵐ ω ∂Q, ∀ R : ℝ, 0 < R → ∃ u : Vec d → ℝ,
      MemLp u 2 (volume.restrict (ball 0 R)) ∧
      HasWeakGradient (ball 0 R) u (fun x => (G (translate x ω)).ofLp) := by
  obtain ⟨f, _, hf⟩ := exists_samplewise_scalar_gradient_approximation Q hQ G hG
  let D := fun n => horizontalEuclideanGradient Q hQ (f n)
  filter_upwards [hf,
    ae_all_iff.mpr (fun n => ae_spatialRealization_memLp_on_all_compacts hQ (D n)),
    ae_spatialRealization_memLp_on_all_compacts hQ G] with ω hω hD hGG
  intro R hR
  let K := Metric.closedBall (0 : Vec d) R
  have hK : IsCompact K := isCompact_closedBall _ _
  have hsub : ball (0 : Vec d) R ⊆ K :=
    euclideanBall_subset_coordinateClosedBall R hR.le
  have hrestrict := Measure.restrict_mono_set volume hsub
  apply exists_weakPotential_of_spatial_gradient_approximation hP (Fact.out : 2 ≤ d)
    R hR (fun n x => (f n : Lp ℝ 2 Q) (translate x ω))
    (fun n x => D n (translate x ω)) (fun x => G (translate x ω))
  · exact fun n => (hω.2.1 n K hK).mono_measure hrestrict
  · exact fun n => (hD n K hK).mono_measure hrestrict
  · exact (hGG K hK).mono_measure hrestrict
  · intro n i
    exact HasWeakPartialDerivative.restrict_subset (Set.subset_univ _) MeasurableSet.univ
      (hω.1 n i)
  · apply squeeze_zero (fun n => integral_nonneg fun _ => sq_nonneg _) ?_ (hω.2.2 K hK)
    intro n
    have hm := (hD n K hK).sub (hGG K hK)
    exact setIntegral_mono_set
      ((memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mp hm)
      (ae_of_all _ fun _ => sq_nonneg _)
      (ae_of_all _ fun _ hx => hsub hx)

end EinsteinRelation.Correctors
