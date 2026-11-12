import EinsteinRelation.Correctors.PairedPDESmoothRegularization

/-! # Global spatial energy of the compact cutoff field

Source: `paper/main.tex:832–840`. Both terms of the actual product-rule
gradient vanish outside the support of the cutoff. Its local L² estimate
therefore gives the global L² field used in convolution approximation.
-/

open MeasureTheory

namespace EinsteinRelation.Correctors

open External.AKM Environment.AKMTestIntegralSupport

/-- The actual weak spatial derivative of the cutoff solution is globally
square integrable. Source: `paper/main.tex:832–840`. -/
theorem parabolicSolution_cutoff_gradient_memLp_global {d : ℕ} {K : ℝ}
    {A : Coefficient d K} {I : Set ℝ} {U : Set (Vec d)}
    (hI : MeasurableSet I) (hU : IsOpen U)
    {u : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    (hsol : IsParabolicSolution A I U u G)
    {ζ : ℝ × Vec d → ℝ} (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ)
    (hζc : HasCompactSupport ζ) (hζsupp : tsupport ζ ⊆ I ×ˢ U)
    (j : Fin d) :
    MemLp (fun z => ζ z * G z j + u z * fderiv ℝ ζ z (0, unitVector j))
      2 volume := by
  have hm := (parabolicSolution_cutoff_energy_class hU hsol hζ hζc).2.1 j
  let H := fun z => ζ z * G z j + u z * fderiv ℝ ζ z (0, unitVector j)
  have heq : (I ×ˢ U).indicator H = H := by
    funext z
    by_cases hz : z ∈ I ×ˢ U
    · exact Set.indicator_of_mem hz _
    · rw [Set.indicator_of_notMem hz]
      have hn : z ∉ tsupport ζ := fun hx => hz (hζsupp hx)
      simp only [H, image_eq_zero_of_notMem_tsupport hn,
        fderiv_of_notMem_tsupport ℝ hn, ContinuousLinearMap.zero_apply,
        zero_mul, mul_zero, add_zero]
  change MemLp H 2 volume
  rw [← heq]
  exact (memLp_indicator_iff_restrict (hI.prod hU.measurableSet)).mpr hm

end EinsteinRelation.Correctors
