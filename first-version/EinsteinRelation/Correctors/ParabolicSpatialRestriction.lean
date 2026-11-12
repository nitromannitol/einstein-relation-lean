import EinsteinRelation.Correctors.SpatialWeakLocalization
import EinsteinRelation.External.AKMLocalCorrectors

open MeasureTheory
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

/-- Restriction to a smaller spatial domain preserves the actual parabolic
energy solution and weak equation. Source: `paper/main.tex:787–806,850`. -/
theorem parabolicSolution_restrict_space {d : ℕ} {K : ℝ}
    {A : Coefficient d K} {I : Set ℝ} {U V : Set (Vec d)} (hVU : V ⊆ U)
    {u : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    (hsol : IsParabolicSolution A I U u G) :
    IsParabolicSolution A I V u G := by
  have hm := Measure.restrict_mono_set volume (Set.prod_mono (Set.Subset.refl I) hVU)
  refine ⟨hsol.1.mono_measure hm,hsol.2.1.mono_measure hm,
    hsol.2.2.1.mono_measure hm,?_,?_⟩
  · filter_upwards [hsol.2.2.2.1] with t ht
    exact hasWeakGradient_mono hVU ht
  · intro ψ hψ hψc hψs
    let F : ℝ × Vec d → ℝ := fun z =>
      -(u z)*fderiv ℝ ψ z (1,0) +
        dot ((A z.2).mulVec (G z)) (fun j => fderiv ℝ ψ z (0,unitVector j))
    have hz (z : ℝ × Vec d) (h : z ∉ tsupport ψ) : F z = 0 := by
      simp only [F,fderiv_of_notMem_tsupport (𝕜 := ℝ) h,
        ContinuousLinearMap.zero_apply,mul_zero,dot,Finset.sum_const_zero,zero_add]
    have heV : (∫ z in I ×ˢ V, F z) = ∫ z, F z := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro z hzV
      apply hz
      intro hmem
      have hh := hψs hmem
      exact hzV ⟨interior_subset hh.1,hh.2⟩
    have heU : (∫ z in I ×ˢ U, F z) = ∫ z, F z := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro z hzU
      apply hz
      intro hmem
      have hh := hψs hmem
      exact hzU ⟨interior_subset hh.1,hVU hh.2⟩
    have hh := hsol.2.2.2.2 ψ hψ hψc
      (hψs.trans (Set.prod_mono (Set.Subset.refl _) hVU))
    change (∫ z in I ×ˢ V, F z) = 0
    rw [heV,← heU]
    exact hh

end EinsteinRelation.Correctors
