import EinsteinRelation.Correctors.SpecifiedFlowBoundedGradientDecay
import EinsteinRelation.Correctors.FlowSpatialReindexing
import EinsteinRelation.Correctors.FlowMomentReindexing

open MeasureTheory
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

/-- Spatial invariance transports the prescribed-time estimate to every
center while retaining the same gradient field. Source:
`paper/main.tex:798–806,850–852`. -/
theorem specifiedSemigroupFlow_bounded_gradient_decay_all_centers
    (hreg : ParabolicLargeScale) (d : ℕ) (hd : 2 ≤ d)
    (K s : ℝ) (hK : 1 < K) (hs : 0 < s) (hs2 : s < 2) :
    ∃ J : ℝ → ℝ, (∀ m : ℝ, 2 ≤ m → 0 < J m) ∧
      ∀ P : Measure (Coefficient d K), IsAdmissibleLaw P →
      (∀ v : Vec d, MeasurePreserving (translateCoefficient v) P P) →
      ∀ (g : Coefficient d K → Vec d → Vec d)
        (u : Coefficient d K → ℝ × Vec d → ℝ)
        (H : Coefficient d K → ℝ × Vec d → Vec d),
        Measurable (fun z : Coefficient d K × (ℝ × Vec d) => u z.1 z.2) →
        Measurable (fun z : Coefficient d K × (ℝ × Vec d) => H z.1 z.2) →
        (∀ᵐ A ∂P, IsSemigroupSolution A (g A) (u A) (H A)) →
        (∀ᵐ A ∂P, ∀ t : ℝ, 0 < t → HasWeakGradient Set.univ
          (fun x => u A (t,x)) (fun x => H A (t,x))) →
        ∀ B : ℝ, 0 ≤ B →
        (∀ᵐ A ∂P, ∀ t : ℝ, 0 < t → ∀ x : Vec d, |u A (t,x)| ≤ B) →
        ∀ F : ℝ → ℝ, (∀ m : ℝ, 0 < m → 0 < F m) →
        (∀ m : ℝ, 0 < m → ∀ t : ℝ, 1 ≤ t → ∀ x : Vec d,
          MemLp (fun A => u A (t,x)) (ENNReal.ofReal m) P ∧
          eLpNorm (fun A => u A (t,x)) (ENNReal.ofReal m) P ≤
            ENNReal.ofReal (F m*t^(-(1 : ℝ)/2-(d : ℝ)/4))) →
        ∀ (v : Vec d) (m t : ℝ), 2 ≤ m → 1 ≤ t →
          MemLp (fun A => vectorRms volume (originBall d 1) (fun x => H A (t,v+x)))
            (ENNReal.ofReal m) P ∧
          eLpNorm (fun A => vectorRms volume (originBall d 1) (fun x => H A (t,v+x)))
            (ENNReal.ofReal m) P ≤ ENNReal.ofReal
              ((J m*(B+F (2*m)))*t^(-(1 : ℝ)-(d : ℝ)/4)) := by
  obtain ⟨J,hJ,hgradient⟩ := specifiedSemigroupFlow_bounded_prescribed_gradient_decay
    hreg d hd K s hK hs hs2
  refine ⟨J,hJ,?_⟩
  intro P hP htrans g u H hum hHm hsol hHw B hB hub F hF hval v m t hm ht
  have hρ := htrans (-v)
  have hub' : ∀ᵐ A ∂P, ∀ t : ℝ, 0 < t → ∀ x : Vec d,
      |u (translateCoefficient (-v) A) (t,v+x)| ≤ B := by
    filter_upwards [hρ.quasiMeasurePreserving.ae hub] with A hA
    intro t ht x
    exact hA t ht (v+x)
  apply (semigroupFlow_gradient_moments_reindex_iff hρ H hHm v t (ENNReal.ofReal m)
    (ENNReal.ofReal ((J m*(B+F (2*m)))*t^(-(1 : ℝ)-(d : ℝ)/4)))).mp
  exact hgradient P hP
    (fun A x => g (translateCoefficient (-v) A) (v+x))
    (fun A z => u (translateCoefficient (-v) A) (z.1,v+z.2))
    (fun A z => H (translateCoefficient (-v) A) (z.1,v+z.2))
    (measurable_semigroupFlow_spatial_reindex u hum v)
    (measurable_semigroupFlow_spatial_reindex H hHm v)
    (semigroupFlow_spatial_reindex_solution P v hρ g u H hsol)
    (semigroupFlow_spatial_reindex_gradient P v hρ u H hHw)
    B hB hub' F hF (semigroupFlow_scalar_moments_reindex hρ v u F hval) m t hm ht

end EinsteinRelation.Correctors
