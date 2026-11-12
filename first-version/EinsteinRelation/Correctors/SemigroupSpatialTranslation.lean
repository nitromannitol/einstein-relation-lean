import EinsteinRelation.Correctors.ParabolicSpatialTranslation
import EinsteinRelation.Calculus.WeakGradientTranslation
import Mathlib.MeasureTheory.Group.Integral

open MeasureTheory
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

/-- Spatial translation preserves the actual semigroup equation and its
weak-divergence initial trace. Source: `paper/main.tex:787–792,850`. -/
theorem semigroupSolution_spatial_translation {d : ℕ} {K : ℝ}
    {A : Coefficient d K} {g : Vec d → Vec d}
    {u : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    (hsol : IsSemigroupSolution A g u G) (v : Vec d) :
    IsSemigroupSolution (translateCoefficient v A) (fun x => g (v+x))
      (fun z => u (z.1,v+z.2)) (fun z => G (z.1,v+z.2)) := by
  refine ⟨?_, ?_, ?_⟩
  · -- ContinuousOn condition: u is continuous on Ioi 0 ×ˢ Set.univ, and
    have h_cont_map : Continuous (fun (z : ℝ × Vec d) => (z.1, v + z.2)) :=
      Continuous.prodMk continuous_fst (continuous_const.add continuous_snd)
    have h_maps : Set.MapsTo (fun (z : ℝ × Vec d) => (z.1, v + z.2))
        (Set.Ioi 0 ×ˢ Set.univ) (Set.Ioi 0 ×ˢ Set.univ) := by
      intro z hz
      exact ⟨hz.1, Set.mem_univ _⟩
    exact hsol.1.comp h_cont_map.continuousOn h_maps
  · -- IsParabolicSolution condition: use the existing spatial translation lemma
    exact parabolicFamily_translate_space hsol.2.1 v
  · -- Initial trace condition: apply the hypothesis to ψ(· - v) and use change of variables
    intro ψ hψ
    have hψ_trans : IsSpatialTest Set.univ (fun x => ψ (x - v)) := by
      refine ⟨?_, ?_, Set.subset_univ _⟩
      · -- smoothness: x ↦ x - v is ContDiff
        exact hψ.1.comp (contDiff_id.sub contDiff_const)
      · -- compact support: translation preserves compact support
        exact hψ.2.1.comp_homeomorph (Homeomorph.addRight (-v))
    have h := hsol.2.2 (fun x => ψ (x - v)) hψ_trans
    have h_grad (x : Vec d) : gradient (fun x => ψ (x - v)) x = gradient ψ (x - v) := by
      ext i
      simp [gradient, coordinateDerivative, fderiv_comp_add_right, sub_eq_add_neg]
    have h_integral (t : ℝ) : (∫ x : Vec d, u (t, v + x) * ψ x) =
        (∫ x : Vec d, u (t, x) * ψ (x - v)) := by
      calc
        (∫ x : Vec d, u (t, v + x) * ψ x) = (∫ x : Vec d, u (t, x + v) * ψ x) := by simp [add_comm]
        _ = (∫ x : Vec d, u (t, x) * ψ (x - v)) := by
          rw [← integral_add_right_eq_self (fun x => u (t, x) * ψ (x - v)) v]
          simp
    have h_dot : (∫ x : Vec d, dot (g (v + x)) (gradient ψ x)) =
        (∫ x : Vec d, dot (g x) (gradient ψ (x - v))) := by
      calc
        (∫ x : Vec d, dot (g (v + x)) (gradient ψ x)) =
            (∫ x : Vec d, dot (g (x + v)) (gradient ψ x)) := by simp [add_comm]
        _ = (∫ x : Vec d, dot (g x) (gradient ψ (x - v))) := by
          rw [← integral_add_right_eq_self (fun x => dot (g x) (gradient ψ (x - v))) v]
          simp
    simpa [h_integral, h_dot, h_grad] using h

end EinsteinRelation.Correctors
