import EinsteinRelation.Correctors.ParabolicDualityCutoffFlux
import Mathlib.MeasureTheory.Integral.DominatedConvergence

open MeasureTheory Filter
open scoped Topology
namespace EinsteinRelation.Correctors

/-- Removing expanding cutoffs in an integrable weak duality identity.
Source: `paper/main.tex:787–792,850`; AKM Proposition E.1 proof. -/
theorem akm_global_duality_cutoff_removal {d : ℕ} {a b : ℝ}
    {f : ℝ × Vec d → ℝ} {F : ℝ × Vec d → Vec d}
    (hf : Integrable f (volume.restrict (Set.Ioo a b ×ˢ Set.univ)))
    (hF : ∀ j : Fin d, Integrable (fun z => F z j)
      (volume.restrict (Set.Ioo a b ×ˢ Set.univ)))
    {η : ℝ → ℝ} (hη : Continuous η) (hηc : HasCompactSupport η)
    (hid : ∀ χ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ → HasCompactSupport χ →
      (∫ z in Set.Ioo a b ×ˢ Set.univ, f z * χ z.2 ^ 2) =
        2 * ∫ z in Set.Ioo a b ×ˢ Set.univ,
          η z.1 * χ z.2 * dot (F z) (gradient χ z.2)) :
    (∫ z in Set.Ioo a b ×ˢ Set.univ, f z) = 0 := by
  obtain ⟨χ, B, hB, hχ, hχb, hχlim, hχD⟩ := akm_exists_scaled_cutoffs d
  have hχabs (n : ℕ) (x : Vec d) : |χ n x| ≤ 1 := by
    rw [abs_of_nonneg (hχb n x).1]
    exact (hχb n x).2
  have hflux := akm_cutoff_flux_tendsto_zero hF hη hηc hB
    (fun n => (hχ n).1) hχabs hχD
  have hL : Tendsto (fun n => ∫ z in Set.Ioo a b ×ˢ Set.univ, f z * χ n z.2 ^ 2)
      atTop (𝓝 (∫ z in Set.Ioo a b ×ˢ Set.univ, f z)) := by
    apply tendsto_integral_of_dominated_convergence (fun z => ‖f z‖)
    · intro n
      exact hf.aestronglyMeasurable.mul
        (((hχ n).1.continuous.comp continuous_snd).pow 2).aestronglyMeasurable
    · exact hf.norm
    · intro n
      exact Filter.Eventually.of_forall fun z => by
        simp only [norm_mul, norm_pow, Real.norm_eq_abs]
        exact mul_le_of_le_one_right (abs_nonneg (f z)) (by nlinarith [hχabs n z.2, abs_nonneg (χ n z.2)])
    · exact Filter.Eventually.of_forall fun z => by
        simpa using ((hχlim z.2).pow 2).const_mul (f z)
  have hR := hflux.const_mul 2
  have heq (n : ℕ) := hid (χ n) (hχ n).1 (hχ n).2
  exact tendsto_nhds_unique hL (by simpa using hR.congr (fun n => (heq n).symm))

end EinsteinRelation.Correctors
