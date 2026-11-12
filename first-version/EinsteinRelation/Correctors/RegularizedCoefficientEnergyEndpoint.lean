import EinsteinRelation.Correctors.CoefficientEnergyForm
import EinsteinRelation.Correctors.BilinearEnergyEndpoint

open MeasureTheory
namespace EinsteinRelation.Correctors
open Environment.AKMTestIntegralSupport

/-- The actual temporally regularized gradient has a uniform endpoint energy
bound from the autonomous symmetric weak equation. Source:
`paper/main.tex:798–806`; AKM Lemma 8.2, printed pp. 305–307. -/
theorem regularized_coefficient_gradient_endpoint_le {d : ℕ} {K a b : ℝ}
    (hK : 0 < K) (hab : a < b) (A : Coefficient d K)
    {U : Set (Vec d)} (hU : IsOpen U) {χ : Vec d → ℝ}
    (hχ : IsSpatialTest U χ) (hχb : ∀ x, |χ x| ≤ 1)
    {L : ℝ} (hL : 0 ≤ L) (hχD : ∀ x, euclideanNorm (gradient χ x) ≤ L)
    (g g' : ℝ → Lp (EuclideanSpace ℝ (Fin d)) 2 (volume.restrict U))
    (hg : ∀ t, HasDerivAt g (g' t) t) (v : ℝ → Vec d → ℝ)
    (hv : ∀ t ∈ Set.Ioo a b, MemLp (v t) 2 (volume.restrict U))
    (hw : ∀ t ∈ Set.Ioo a b, HasWeakGradient U (v t) (fun x => (g' t x).ofLp))
    (hdiv : ∀ t ∈ Set.Ioo a b,
      HasWeakDivergence U (fun x => (A x).mulVec (g t x).ofLp) (v t)) :
    (∫ x in U, χ x^2 * euclideanSq (g b x).ofLp) ≤
      (K/(b-a) + 2*K^2*L^2) * (∫ t in a..b, ‖g t‖^2) := by
  obtain ⟨B,hBs,hBr⟩ := exists_coefficient_cutoff_energy_form hK.le A hχ
  have hupper t : B (g t) (g t) ≤ K * ‖g t‖^2 := by
    rw [hBr]
    exact (coefficient_cutoff_energy_bounds hK.le A hχ hχb (g t)).2
  have hder t (ht : t ∈ Set.Ioo a b) :
      2 * B (g t) (g' t) ≤ (2*K^2*L^2) * ‖g t‖^2 := by
    have he := regularized_gradient_energy_derivative_le hU (fun x => A x)
      hχ B hBs hBr (hg t) (hv t ht) (hw t ht)
      (coefficient_mulVec_memLp hK.le A U (g t)) (hdiv t ht)
    rw [(hasDerivAt_symmetric_bilinear_energy B hBs (hg t)).deriv] at he
    have hb := coefficient_cutoff_flux_error_le hK A hχ hL hχD (g t)
    calc
      _ ≤ 2 * (∫ x in U,
          (dot ((A x).mulVec (g t x).ofLp) (gradient χ x))^2) := he
      _ ≤ 2 * (K^2*L^2*‖g t‖^2) := mul_le_mul_of_nonneg_left hb (by norm_num)
      _ = _ := by ring
  have he := bilinear_energy_curve_endpoint_le B hBs hg hab (by positivity : 0 ≤ 2*K^2*L^2)
    (fun t _ => hupper t) hder
  apply le_trans _ he
  rw [hBr]
  exact (coefficient_cutoff_energy_bounds hK.le A hχ hχb (g b)).1

end EinsteinRelation.Correctors
