import EinsteinRelation.External.AKMLocalCorrectors
import EinsteinRelation.Correctors.SpatialWeakLocalization

/-! # Spatial restriction of the actual weak parabolic equation

Source: `paper/main.tex:816–832`. The test and its full derivative vanish
outside the smaller spatial cylinder, so both weak equations use the same
whole-space test integral.
-/

open MeasureTheory
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

/-- Restriction to a smaller spatial set preserves the actual weak PDE
and energy class. Source: `paper/main.tex:816–832`. -/
theorem parabolicSolution_spatial_restrict {d : ℕ} {K : ℝ}
    {A : Coefficient d K} {I : Set ℝ} {U V : Set (Vec d)}
    (_hI : MeasurableSet I) (_hU : MeasurableSet U) (_hV : MeasurableSet V)
    (hVU : V ⊆ U) {u : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    (hsol : IsParabolicSolution A I U u G) :
    IsParabolicSolution A I V u G := by
  have hm : volume.restrict (I ×ˢ V) ≤ volume.restrict (I ×ˢ U) :=
    Measure.restrict_mono_set volume (Set.prod_mono_right hVU)
  refine ⟨hsol.1.mono_measure hm, hsol.2.1.mono_measure hm,
    hsol.2.2.1.mono_measure hm, ?_, ?_⟩
  · filter_upwards [hsol.2.2.2.1] with t ht
    exact hasWeakGradient_mono hVU ht
  · intro ψ hψ hψc hsupp
    let F := fun z : ℝ × Vec d => -(u z) * fderiv ℝ ψ z (1, 0) +
      dot ((A z.2).mulVec (G z)) (fun j => fderiv ℝ ψ z (0, unitVector j))
    have hs : tsupport ψ ⊆ I ×ˢ V :=
      hsupp.trans (Set.prod_mono_left interior_subset)
    have hz (z : ℝ × Vec d) (hnot : z ∉ tsupport ψ) : F z = 0 := by
      simp [F, fderiv_of_notMem_tsupport (𝕜 := ℝ) hnot, dot]
    have hv : (∫ z in I ×ˢ V, F z) = ∫ z, F z :=
      setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hzV =>
        hz z (fun h => hzV (hs h)))
    have hu : (∫ z in I ×ˢ U, F z) = ∫ z, F z :=
      setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hzU =>
        hz z (fun h => hzU ((Set.prod_mono_right hVU) (hs h))))
    change (∫ z in I ×ˢ V, F z) = 0
    rw [hv, ← hu]
    exact hsol.2.2.2.2 ψ hψ hψc (hsupp.trans (Set.prod_mono_right hVU))

end EinsteinRelation.Correctors
