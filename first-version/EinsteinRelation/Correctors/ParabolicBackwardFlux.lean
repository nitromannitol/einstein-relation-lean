import EinsteinRelation.Correctors.ParabolicFluxSolution
import EinsteinRelation.Correctors.ParabolicTimeReflection
import EinsteinRelation.Correctors.ParabolicTimeReverseEquation

open MeasureTheory
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

/-- A forward solution reflected in time solves the flux equation with
negative actual coefficient flux. Source: `paper/main.tex:787–792,850`. -/
theorem parabolicFluxSolution_of_backward_parabolicSolution {d : ℕ} {K : ℝ}
    (hK : 0 < K) {A : Coefficient d K} {a b T : ℝ} {U : Set (Vec d)}
    {v : ℝ × Vec d → ℝ} {H : ℝ × Vec d → Vec d}
    (hv : IsParabolicSolution A (Set.Ioo (T-b) (T-a)) U v H) :
    IsParabolicFluxSolution (Set.Ioo a b) U
      (fun z => v (T-z.1,z.2)) (fun z => H (T-z.1,z.2))
      (fun z => -((A z.2).mulVec (H (T-z.1,z.2)))) := by
  have htr := akm_time_reflection_cylinder_measurePreserving d T a b U
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa only [Function.comp_def] using hv.1.comp_measurePreserving htr
  · intro j
    simpa only [Function.comp_def] using
      (parabolicSolution_gradient_coordinate_memLp hv j).comp_measurePreserving htr
  · exact (akm_time_reflection_interval_measurePreserving T a b).quasiMeasurePreserving.ae hv.2.2.2.1
  · intro j
    simpa only [Function.comp_def, Pi.neg_apply] using
      ((parabolicSolution_flux_coordinate_memLp hK A hv j).comp_measurePreserving htr).neg
  · intro ψ hψ hψc hψs
    have hs : tsupport ψ ⊆ Set.Ioo a b ×ˢ U :=
      hψs.trans (Set.prod_mono interior_subset Set.Subset.rfl)
    have hb := (parabolicSolution_time_reverse_weak hK hv hψ hψc hs).2
    have heq (z : ℝ × Vec d) :
        -(v (T-z.1,z.2)) * fderiv ℝ ψ z (1,0) +
          dot (-((A z.2).mulVec (H (T-z.1,z.2))))
            (fun j => fderiv ℝ ψ z (0,unitVector j)) =
        -(v (T-z.1,z.2) * fderiv ℝ ψ z (1,0) +
          dot ((A z.2).mulVec (H (T-z.1,z.2)))
            (fun j => fderiv ℝ ψ z (0,unitVector j))) := by
      simp only [dot, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]
      ring
    simp_rw [heq, integral_neg, hb, neg_zero]

end EinsteinRelation.Correctors
