import EinsteinRelation.Correctors.AKMHeatKernelSpatialExhaustion
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! # Localization of spatially supported space-time integrals

Source: `paper/main.tex:787–792,850`; compact testing in the proof of
AKM Proposition E.1. A spatial support inclusion suffices to extend a
cylinder integral to a whole-space strip.
-/

open MeasureTheory
namespace EinsteinRelation.Correctors

/-- An integrand vanishing outside the spatial test support has the same
integral on the containing cylinder and the whole-space time strip.
Source: `paper/main.tex:787–792,850`. -/
theorem akm_spatially_supported_strip_integral {d : ℕ}
    {I : Set ℝ} (hI : MeasurableSet I) {U : Set (Vec d)}
    {χ : Vec d → ℝ} (hχ : tsupport χ ⊆ U)
    {f : ℝ × Vec d → ℝ} (hf : ∀ z, χ z.2 = 0 → f z = 0) :
    (∫ z in I ×ˢ Set.univ, f z) = ∫ z in I ×ˢ U, f z := by
  apply setIntegral_eq_of_subset_of_forall_diff_eq_zero
    (hI.prod MeasurableSet.univ) (Set.prod_mono Set.Subset.rfl (Set.subset_univ U))
  intro z hz
  apply hf
  apply image_eq_zero_of_notMem_tsupport
  intro hx
  exact hz.2 ⟨hz.1.1, hχ hx⟩

end EinsteinRelation.Correctors
