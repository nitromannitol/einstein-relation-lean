import EinsteinRelation.Correctors.SymmetricEnergyDerivative
import EinsteinRelation.Correctors.EnergyEndpointAverage

open MeasureTheory
namespace EinsteinRelation.Correctors

/-- Integrate the actual localized coefficient energy along a differentiable
L² curve. Source: `paper/main.tex:798–806`; AKM Lemma 8.2. -/
theorem bilinear_energy_curve_endpoint_le {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B : E →L[ℝ] E →L[ℝ] ℝ) (hsym : ∀ f g, B f g = B g f)
    {g g' : ℝ → E} (hg : ∀ t, HasDerivAt g (g' t) t)
    {a b K D : ℝ} (hab : a < b) (hD : 0 ≤ D)
    (hupper : ∀ t ∈ Set.Icc a b, B (g t) (g t) ≤ K * ‖g t‖^2)
    (hder : ∀ t ∈ Set.Ioo a b, 2 * B (g t) (g' t) ≤ D * ‖g t‖^2) :
    B (g b) (g b) ≤ (K / (b-a) + D) * (∫ t in a..b, ‖g t‖^2) := by
  have hc : Continuous g := continuous_iff_continuousAt.mpr fun t => (hg t).continuousAt
  have he : Continuous (fun t => B (g t) (g t)) := (B.continuous.comp hc).clm_apply hc
  have hn : Continuous (fun t => ‖g t‖^2) := hc.norm.pow 2
  have hF : Continuous (fun t => D * ‖g t‖^2) := continuous_const.mul hn
  have hd t := hasDerivAt_symmetric_bilinear_energy B hsym (hg t)
  have h := energy_endpoint_le_average_add_error hab he.continuousOn hF.continuousOn
    (fun t _ => mul_nonneg hD (sq_nonneg _))
    (fun t _ => by rw [(hd t).deriv]; exact hd t)
    (fun t ht => by rw [(hd t).deriv]; exact hder t ht)
  have hu : (∫ t in a..b, B (g t) (g t)) ≤ K * (∫ t in a..b, ‖g t‖^2) := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_mono_on hab.le
      (he.intervalIntegrable a b) ((continuous_const.mul hn).intervalIntegrable a b) hupper
  rw [intervalIntegral.integral_const_mul] at h
  calc
    _ ≤ (b-a)⁻¹ * (∫ t in a..b, B (g t) (g t)) +
        D * (∫ t in a..b, ‖g t‖^2) := h
    _ ≤ (b-a)⁻¹ * (K * (∫ t in a..b, ‖g t‖^2)) +
        D * (∫ t in a..b, ‖g t‖^2) :=
      add_le_add (mul_le_mul_of_nonneg_left hu (inv_nonneg.mpr (sub_pos.mpr hab).le)) (le_refl _)
    _ = _ := by ring

end EinsteinRelation.Correctors
