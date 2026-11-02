import EinsteinFull.Calculus.C8DyadicTransposeFluxSize

open MeasureTheory Set
open scoped NNReal ENNReal Topology
noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation

theorem c6_density_increment_controls_actual_flux_remainder
    {d : ℕ} {D : StructuralData d}
    {Q : EnvironmentLaw d D.ellipticity D.dependenceRange} {hQ : HasSmoothBounds D Q}
    {β : Fin d → Lp ℂ 2 (reducedLaw Q)} (hβ : IsReducedDriftObservation Q hQ β)
    {i : Fin d} {ζ : ℂ}
    {P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (hPd : IsComplexTransposeSemigroup Q P Pdag) (s u : ℝ≥0) (hsu : s ≤ u) :
    let := reducedLaw_probability Q
    Real.sqrt (∑ j : Fin d,
      ‖(-2 * ζ) • complexCoefficientMul Q j i
        (∫ t in Set.Icc (s : ℝ) (u : ℝ),
          transposeEndpoint Q i Pdag β t.toNNReal)‖ ^ 2) ≤
      ((d : ℝ) * (Real.exp (2 * D.ellipticity) * D.ellipticity)) *
        ‖Pdag u (Lp.const 2 (reducedLaw Q) 1) -
          Pdag s (Lp.const 2 (reducedLaw Q) 1)‖ := by
  let := reducedLaw_probability Q
  let H := ∫ t in Set.Icc (s : ℝ) (u : ℝ),
    transposeEndpoint Q i Pdag β t.toNNReal
  let X := Pdag u (Lp.const 2 (reducedLaw Q) 1) -
    Pdag s (Lp.const 2 (reducedLaw Q) 1)
  have hX : (-2 * ζ) • H = X :=
    dyadic_transpose_primitive_const_increment hβ hP hPd s u hsu
  have hcoord (j : Fin d) :
      ‖(-2 * ζ) • complexCoefficientMul Q j i H‖ ≤
        (Real.exp (2 * D.ellipticity) * D.ellipticity) * ‖X‖ := by
    rw [← map_smul, hX]
    exact ((complexCoefficientMul Q j i).le_opNorm X).trans
      (mul_le_mul_of_nonneg_right (norm_complexCoefficientMul_le Q j i) (norm_nonneg X))
  calc
    _ ≤ ∑ j : Fin d, ‖(-2 * ζ) • complexCoefficientMul Q j i H‖ := by
      apply Real.sqrt_le_iff.mpr
      exact ⟨Finset.sum_nonneg (fun j _ => norm_nonneg _),
        Finset.sum_sq_le_sq_sum_of_nonneg (fun j _ => norm_nonneg _)⟩
    _ ≤ ∑ _j : Fin d, (Real.exp (2 * D.ellipticity) * D.ellipticity) * ‖X‖ :=
      Finset.sum_le_sum fun j _ => hcoord j
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

end EinsteinFull.Blueprint
