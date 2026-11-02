import EinsteinRelation.Correctors.AKMScalarApproximation
import EinsteinRelation.Correctors.GlobalSpatialWeakPotential
import EinsteinRelation.Correctors.CenteredPotentialLimit
import EinsteinRelation.Correctors.StationarySpatialWeakPotentials

/-!
# Global weak potentials on the actual AKM law

Source: `paper/main.tex:693-702`. Measurable scalar approximations are
transferred before completing their gradients. Poincaré completion and
normalized gluing therefore take place directly on the raw coefficient law.
-/

open MeasureTheory Filter Topology
noncomputable section
namespace EinsteinRelation.Correctors
open External.AKM External.GilbargTrudinger Environment.AKMTestIntegralSupport ReductionImageV3

/-- Actual locally convergent scalar Sobolev approximations determine a
global scalar weak potential with zero unit-ball integral. -/
theorem exists_global_weakPotential_of_local_scalar_approximation
    (hP : BallPoincareEstimate) {d : ℕ} (hd : 2 ≤ d)
    (u : ℕ → Vec d → ℝ) (g : ℕ → Vec d → EuclideanSpace ℝ (Fin d))
    (G : Vec d → EuclideanSpace ℝ (Fin d))
    (hw : ∀ n, HasWeakGradient Set.univ (u n) (fun x => (g n x).ofLp))
    (hlocal : ∀ n (K : Set (Vec d)), IsCompact K →
      MemLp (u n) 2 (volume.restrict K) ∧ MemLp (g n) 2 (volume.restrict K))
    (hG : ∀ K : Set (Vec d), IsCompact K → MemLp G 2 (volume.restrict K))
    (hlim : ∀ K : Set (Vec d), IsCompact K → Tendsto
      (fun n => ∫ x in K, ‖g n x - G x‖ ^ 2) atTop (𝓝 0)) :
    ∃ v : Vec d → ℝ, HasWeakGradient Set.univ v (fun x => (G x).ofLp) ∧
      (∀ R : ℝ, 0 < R → MemLp v 2 (volume.restrict (ball 0 R))) ∧
      (∫ x in ball (0 : Vec d) 1, v x) = 0 := by
  let J := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).toContinuousLinearMap
  apply exists_global_weakPotential_of_ball_potentials hP hd (fun x => (G x).ofLp)
  · intro R hR
    exact J.comp_memLp' ((hG _ (isCompact_closedBall (0 : Vec d) R)).mono_measure
      (Measure.restrict_mono_set volume (euclideanBall_subset_coordinateClosedBall R hR.le)))
  · intro R hR
    let K := Metric.closedBall (0 : Vec d) R
    have hK : IsCompact K := isCompact_closedBall _ _
    have hs : ball (0 : Vec d) R ⊆ K := euclideanBall_subset_coordinateClosedBall R hR.le
    have hμ := Measure.restrict_mono_set volume hs
    apply exists_weakPotential_of_spatial_gradient_approximation hP hd R hR u g G
    · exact fun n => (hlocal n K hK).1.mono_measure hμ
    · exact fun n => (hlocal n K hK).2.mono_measure hμ
    · exact (hG K hK).mono_measure hμ
    · exact fun n j => HasWeakPartialDerivative.restrict_subset (Set.subset_univ _)
        MeasurableSet.univ (hw n j)
    · apply squeeze_zero (fun n => integral_nonneg fun _ => sq_nonneg _) ?_ (hlim K hK)
      intro n
      have hm := (hlocal n K hK).2.sub (hG K hK)
      exact setIntegral_mono_set
        ((memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mp hm)
        (ae_of_all _ fun _ => sq_nonneg _) (ae_of_all _ fun _ hx => hs hx)

/-- A jointly measurable raw gradient, canonically identified on the
physical law, has a global normalized scalar weak potential under the raw
AKM law. Sublinearity is a separate property. -/
theorem exists_akm_canonical_global_weakPotential
    (hP : BallPoincareEstimate) {d : ℕ} [Fact (2 ≤ d)] {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) (i : Fin d) :
    ∃ G : Coefficient d (AKMUpperEllipticity L) → Vec d → EuclideanSpace ℝ (Fin d),
      Measurable (fun p : Coefficient d (AKMUpperEllipticity L) × Vec d => G p.1 p.2) ∧
      (∀ᵐ a ∂actualCoefficientLaw Q,
        (∀ R : ℝ, 0 < R → MemLp (G a) 2 (volume.restrict (ball 0 R))) ∧
        ∃ v : Vec d → ℝ, HasWeakGradient Set.univ v (fun x => (G a x).ofLp) ∧
          (∀ R : ℝ, 0 < R → MemLp v 2 (volume.restrict (ball 0 R))) ∧
          (∫ x in ball (0 : Vec d) 1, v x) = 0) ∧
      ∀ᵐ ω ∂physicalReferenceLaw Q, ∀ᵐ x ∂(volume : Measure (Vec d)),
        G (project (r₀ := r₀) Q.ellipticity_parameter ω) x =
          (canonicalCorrectorGradient Q i :
            Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
              (translate x (reduce ω.1)) := by
  obtain ⟨u, g, G, _, hG, ha, hid⟩ := exists_akm_scalar_gradient_approximation Q i
  refine ⟨G, hG, ?_, hid⟩
  filter_upwards [ha] with a ha
  refine ⟨fun R hR => (ha.2.2.1 _ (isCompact_closedBall (0 : Vec d) R)).mono_measure
    (Measure.restrict_mono_set volume (euclideanBall_subset_coordinateClosedBall R hR.le)), ?_⟩
  exact exists_global_weakPotential_of_local_scalar_approximation hP (Fact.out : 2 ≤ d)
    (fun n => u n a) (fun n => g n a) (G a) ha.1 ha.2.1 ha.2.2.1 ha.2.2.2

end EinsteinRelation.Correctors
