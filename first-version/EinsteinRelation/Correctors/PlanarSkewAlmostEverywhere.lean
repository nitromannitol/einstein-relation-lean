import EinsteinRelation.Correctors.PlanarSkewWeakCalculus
import EinsteinRelation.Correctors.SpatialWeakCongruence
/-! # Planar skew weak calculus with almost-everywhere identities

Source: `paper/main.tex:869–872`. Distributional equations depend on
spatial equivalence classes, so the source almost-everywhere skewness
suffices without changing any prescribed value of the skew field.
-/

open MeasureTheory
namespace EinsteinRelation.Correctors

/-- Almost-everywhere skewness suffices for the planar weak equation;
paper/main.tex:869–872. -/
theorem hasWeakGradient_planar_skew_entry_of_ae {U : Set (Vec 2)}
    (_hU : IsOpen U) (S : Vec 2 → Mat 2) (q : Vec 2 → Vec 2)
    (hS : ∀ᵐ x ∂volume.restrict U, (S x).transpose = -(S x))
    (hdiv : HasWeakRowDivergence U S q) :
    HasWeakGradient U (fun x => S x 0 1) (fun x => ![-q x 1, q x 0]) := by
  have hdiv0 := hdiv 0
  have hdiv1 := hdiv 1
  have hloc_S01 : LocallyIntegrableOn (fun x => S x 0 1) U volume :=
    hdiv0.1 1
  have hloc_q0 : LocallyIntegrableOn (fun x => q x 0) U volume :=
    hdiv0.2.1
  have hloc_q1 : LocallyIntegrableOn (fun x => q x 1) U volume :=
    hdiv1.2.1
  have hloc_negq1 : LocallyIntegrableOn (fun x => -q x 1) U volume :=
    hloc_q1.neg
  have hS_skew_ae : ∀ᵐ x ∂volume.restrict U,
      S x 1 0 = -(S x 0 1) ∧ S x 0 0 = 0 ∧ S x 1 1 = 0 := by
    filter_upwards [hS] with x hx
    have h_entry (i j : Fin 2) : S x j i = -(S x i j) := by
      have h := congr_fun (congr_fun hx i) j
      simpa [Matrix.transpose_apply, Pi.neg_apply] using h
    have h00 : S x 0 0 = 0 := by
      have h := h_entry 0 0
      linarith
    have h11 : S x 1 1 = 0 := by
      have h := h_entry 1 1
      linarith
    have h10 : S x 1 0 = -(S x 0 1) := h_entry 0 1
    exact ⟨h10, h00, h11⟩
  have h0 : HasWeakPartialDerivative U 0 (fun x => S x 0 1) (fun x => -q x 1) := by
    refine ⟨hloc_S01, hloc_negq1, ?_⟩
    intro ψ hψ
    have heq := hdiv1.2.2 ψ hψ
    have h_integral_eq : (∫ x in U, dot (fun k => S x 1 k) (gradient ψ x)) =
        (∫ x in U, -(S x 0 1 * coordinateDerivative 0 ψ x)) := by
      refine integral_congr_ae ?_
      filter_upwards [hS_skew_ae] with x ⟨h10, h00, h11⟩
      simp [dot, gradient, h11, h10, Fin.sum_univ_two]
    rw [h_integral_eq] at heq
    have h_simp : (∫ x in U, -(S x 0 1 * coordinateDerivative 0 ψ x)) =
        -(∫ x in U, S x 0 1 * coordinateDerivative 0 ψ x) := integral_neg _
    rw [h_simp] at heq
    have h_cancel : (∫ x in U, S x 0 1 * coordinateDerivative 0 ψ x) =
        (∫ x in U, q x 1 * ψ x) := by
      linarith
    calc
      (∫ x in U, S x 0 1 * coordinateDerivative 0 ψ x) =
          (∫ x in U, q x 1 * ψ x) := h_cancel
      _ = -(∫ x in U, (-q x 1) * ψ x) := by
        simp [integral_neg]
  have h1 : HasWeakPartialDerivative U 1 (fun x => S x 0 1) (fun x => q x 0) := by
    refine ⟨hloc_S01, hloc_q0, ?_⟩
    intro ψ hψ
    have heq := hdiv0.2.2 ψ hψ
    have h_integral_eq : (∫ x in U, dot (fun k => S x 0 k) (gradient ψ x)) =
        (∫ x in U, S x 0 1 * coordinateDerivative 1 ψ x) := by
      refine integral_congr_ae ?_
      filter_upwards [hS_skew_ae] with x ⟨h10, h00, h11⟩
      simp [dot, gradient, h00, Fin.sum_univ_two]
    rw [h_integral_eq] at heq
    simpa using heq
  intro i
  fin_cases i <;> assumption
end EinsteinRelation.Correctors
