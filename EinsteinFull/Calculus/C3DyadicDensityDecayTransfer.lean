import EinsteinFull.Calculus.C6DyadicDensityFluxBridge

open MeasureTheory
open scoped NNReal ENNReal Topology
noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation

theorem c3_actual_flux_decay_of_density_bound
    {d : ℕ} {D : StructuralData d}
    {Q : EnvironmentLaw d D.ellipticity D.dependenceRange} {hQ : HasSmoothBounds D Q}
    {β : Fin d → Lp ℂ 2 (reducedLaw Q)} (hβ : IsReducedDriftObservation Q hQ β)
    {i : Fin d} {ζ : ℂ}
    {P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (hPd : IsComplexTransposeSemigroup Q P Pdag) (s u : ℝ≥0) (hsu : s ≤ u) (C : ℝ) :
    let := reducedLaw_probability Q
    ‖Pdag u (Lp.const 2 (reducedLaw Q) 1) -
      Pdag s (Lp.const 2 (reducedLaw Q) 1)‖ ≤ C * (s : ℝ) ^ (-(d : ℝ)/4) →
    Real.sqrt (∑ j : Fin d,
      ‖(-2 * ζ) • complexCoefficientMul Q j i
        (∫ t in Set.Icc (s : ℝ) (u : ℝ),
          transposeEndpoint Q i Pdag β t.toNNReal)‖ ^ 2) ≤
      ((d : ℝ) * (Real.exp (2 * D.ellipticity) * D.ellipticity)) *
        (C * (s : ℝ) ^ (-(d : ℝ)/4)) := by
  dsimp only
  let := reducedLaw_probability Q
  intro hbound
  exact (c6_density_increment_controls_actual_flux_remainder hβ hP hPd s u hsu).trans
    (mul_le_mul_of_nonneg_left hbound
      (mul_nonneg (Nat.cast_nonneg d)
        (mul_nonneg (Real.exp_pos _).le (le_trans zero_le_one D.one_le_ellipticity))))

end EinsteinFull.Blueprint
