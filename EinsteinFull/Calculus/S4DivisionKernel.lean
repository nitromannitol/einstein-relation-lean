import Mathlib.MeasureTheory.Integral.Indicator
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import EinsteinFull.Frozen.KernelProfileRemainder
import EinsteinFull.Frozen.GaussianProfile
import EinsteinFull.Frozen.ComplexGaussianProfile

/-!
# The zeroth coefficient of the integrated kernel

At force zero the profile-subtracted correlation integrates to the plain correlation integral:
`∫₀^∞ (J(t) - 1_{t ≥ 1} t^{-1-d/2} c) dt + 2c/d = ∫₀^∞ J(t) dt`.
-/

open MeasureTheory Set

namespace EinsteinFull

theorem integral_remainder_add {d : ℕ} (hd : 1 ≤ d) {J : ℝ → ℝ} (c : ℝ)
    (hJ : IntegrableOn J (Ici (0 : ℝ))) :
    (∫ t in Ici (0 : ℝ), (J t - if 1 ≤ t then t ^ (-1 - (d : ℝ) / 2) * c else 0)) +
        2 * c / (d : ℝ) = ∫ t in Ici (0 : ℝ), J t := by
  set r : ℝ := -1 - (d : ℝ) / 2 with hrdef
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hr : r < -1 := by rw [hrdef]; linarith
  set g : ℝ → ℝ := fun t => if 1 ≤ t then t ^ r * c else 0 with hg
  have hgeq : g = Set.indicator (Ici (1 : ℝ)) (fun t => t ^ r * c) := by
    funext t
    simp only [hg, Set.indicator, Set.mem_Ici]
  have h0 : IntegrableOn (fun t : ℝ => t ^ r) (Ici (1 : ℝ)) :=
    Iff.mpr (integrableOn_Ici_iff_integrableOn_Ioi (f := fun t : ℝ => t ^ r)
      (by simp)) (integrableOn_Ioi_rpow_of_lt hr one_pos)
  have h1 : IntegrableOn (fun t : ℝ => t ^ r * c) (Ici (1 : ℝ)) := h0.mul_const c
  have hgint : IntegrableOn g (Ici (0 : ℝ)) := by
    rw [hgeq, IntegrableOn, integrable_indicator_iff measurableSet_Ici, IntegrableOn,
      Measure.restrict_restrict measurableSet_Ici]
    exact h1.mono_set Set.inter_subset_left
  have hgval : ∫ t in Ici (0 : ℝ), g t = 2 * c / d := by
    rw [hgeq, setIntegral_indicator measurableSet_Ici]
    have : Ici (0 : ℝ) ∩ Ici 1 = Ici 1 := by
      ext x; simp only [Set.mem_inter_iff, Set.mem_Ici]
      constructor
      · exact fun h => h.2
      · exact fun h => ⟨by linarith, h⟩
    rw [this, integral_Ici_eq_integral_Ioi, integral_mul_const, integral_Ioi_rpow_of_lt hr one_pos]
    have h2 : r + 1 = -(d : ℝ) / 2 := by rw [hrdef]; ring
    rw [h2, Real.one_rpow]
    field_simp
  rw [integral_sub hJ hgint, hgval]
  ring

end EinsteinFull
