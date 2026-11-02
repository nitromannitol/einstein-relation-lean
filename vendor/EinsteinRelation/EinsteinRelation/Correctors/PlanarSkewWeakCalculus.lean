import EinsteinRelation.Correctors.SpatialWeakLocalization
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-! # Planar skew fluxes and rotated weak gradients

Source: `paper/main.tex:864–873`.
-/

open MeasureTheory

namespace EinsteinRelation.Correctors

/-- Source: `paper/main.tex:864–873`. A planar skew flux equation is
a scalar weak-gradient equation, with the manuscript's row-divergence signs. -/
theorem hasWeakGradient_planar_skew_entry {U : Set (Vec 2)}
    (S : Vec 2 → Mat 2) (q : Vec 2 → Vec 2)
    (hS : ∀ x, (S x).transpose = -(S x))
    (hdiv : HasWeakRowDivergence U S q) :
    HasWeakGradient U (fun x => S x 0 1) (fun x => ![-q x 1, q x 0]) := by
  have hS_entry (x : Vec 2) (i j : Fin 2) : S x j i = -(S x i j) := by
    have h := congr_fun (congr_fun (hS x) i) j
    simpa [Matrix.transpose_apply, Pi.neg_apply] using h
  have hS_zero_diag (x : Vec 2) (i : Fin 2) : S x i i = 0 := by
    have h := hS_entry x i i
    linarith
  have hS_skew (x : Vec 2) : S x 1 0 = -(S x 0 1) := hS_entry x 0 1
  have hdiv0 := hdiv 0
  have hdiv1 := hdiv 1
  have hloc_S01 : LocallyIntegrableOn (fun x => S x 0 1) U volume := by
    have := hdiv0.1 1
    simpa using this
  have hloc_q0 : LocallyIntegrableOn (fun x => q x 0) U volume := hdiv0.2.1
  have hloc_q1 : LocallyIntegrableOn (fun x => q x 1) U volume := hdiv1.2.1
  have hloc_negq1 : LocallyIntegrableOn (fun x => -q x 1) U volume :=
    hloc_q1.neg
  have h0 : HasWeakPartialDerivative U 0 (fun x => S x 0 1) (fun x => -q x 1) := by
    refine ⟨hloc_S01, hloc_negq1, ?_⟩
    intro ψ hψ
    have heq := hdiv1.2.2 ψ hψ
    have hdot_eq : (fun x => dot (fun k => S x 1 k) (gradient ψ x))
        = (fun x => -(S x 0 1) * coordinateDerivative 0 ψ x) := by
      ext x
      simp [dot, gradient, hS_zero_diag x 1, hS_skew x, Fin.sum_univ_two]
    rw [hdot_eq] at heq
    have h_simp : (∫ x in U, -(S x 0 1) * coordinateDerivative 0 ψ x) =
        -(∫ x in U, S x 0 1 * coordinateDerivative 0 ψ x) := by
      calc
        (∫ x in U, -(S x 0 1) * coordinateDerivative 0 ψ x) =
            (∫ x in U, -(S x 0 1 * coordinateDerivative 0 ψ x)) := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
          ring
        _ = -(∫ x in U, S x 0 1 * coordinateDerivative 0 ψ x) := integral_neg _
    rw [h_simp] at heq
    rw [neg_inj] at heq
    simpa [neg_mul, integral_neg, Pi.neg_apply, neg_neg] using heq
  have h1 : HasWeakPartialDerivative U 1 (fun x => S x 0 1) (fun x => q x 0) := by
    refine ⟨hloc_S01, hloc_q0, ?_⟩
    intro ψ hψ
    have heq := hdiv0.2.2 ψ hψ
    have hdot_eq : (fun x => dot (fun k => S x 0 k) (gradient ψ x))
        = (fun x => S x 0 1 * coordinateDerivative 1 ψ x) := by
      ext x
      simp [dot, gradient, hS_zero_diag x 0, Fin.sum_univ_two]
    rw [hdot_eq] at heq
    simpa using heq
  intro i
  fin_cases i <;> assumption

/-- Source: `paper/main.tex:867–870`. The divergence of the ninety-degree
rotation of a weak gradient vanishes, by commutation of the smooth test's
mixed derivatives. -/
theorem hasWeakDivergence_planar_rotated_gradient {U : Set (Vec 2)}
    (f : Vec 2 → ℝ) (G : Vec 2 → Vec 2)
    (hf : HasWeakGradient U f G) :
    HasWeakDivergence U (fun x => ![-G x 1, G x 0]) (fun _ => 0) := by
  have hloc_rot0 : LocallyIntegrableOn (fun x => -G x 1) U volume := by
    have hG := hf 1
    exact hG.2.1.neg
  have hloc_rot1 : LocallyIntegrableOn (fun x => G x 0) U volume :=
    (hf 0).2.1
  have hloc_zero : LocallyIntegrableOn (fun _ => (0 : ℝ)) U volume :=
    locallyIntegrableOn_zero
  refine ⟨?_, hloc_zero, ?_⟩
  · intro i
    fin_cases i
    · exact hloc_rot0
    · exact hloc_rot1
  · intro ψ hψ
    have hψ_smooth : ContDiff ℝ (⊤ : ℕ∞) ψ := hψ.1
    have htest_deriv0 : IsSpatialTest U (coordinateDerivative 0 ψ) :=
      isSpatialTest_coordinateDerivative hψ 0
    have htest_deriv1 : IsSpatialTest U (coordinateDerivative 1 ψ) :=
      isSpatialTest_coordinateDerivative hψ 1
    have h0_deriv1 := (hf 0).2.2 (coordinateDerivative 1 ψ) htest_deriv1
    have h1_deriv0 := (hf 1).2.2 (coordinateDerivative 0 ψ) htest_deriv0
    have hinner : (2 : ℕ∞) ≤ (⊤ : ℕ∞) := le_top
    have hn : minSmoothness ℝ 2 ≤ (↑(⊤ : ℕ∞) : WithTop ℕ∞) := by
      rw [minSmoothness_of_isRCLikeNormedField]
      change (↑(2 : ℕ∞) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞)
      exact_mod_cast hinner
    have hcomm (x : Vec 2) : coordinateDerivative 0 (coordinateDerivative 1 ψ) x =
        coordinateDerivative 1 (coordinateDerivative 0 ψ) x := by
      have hsymm := ContDiffAt.isSymmSndFDerivAt (hψ_smooth.contDiffAt (x := x)) hn
      have hswap := hsymm.iteratedFDeriv_cons (v := unitVector 0) (w := unitVector 1)
      have hd : DifferentiableAt ℝ (fun y => fderiv ℝ ψ y) x := by
        have hbound : (1 : WithTop ℕ∞) + 1 ≤ (↑(⊤ : ℕ∞) : WithTop ℕ∞) := by
          change (↑(2 : ℕ∞) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞)
          exact_mod_cast hinner
        exact ((hψ_smooth.contDiffAt (x := x)).fderiv_right hbound).differentiableAt
          (by norm_num)
      have happly (v w : Vec 2) :
          fderiv ℝ (fun y => fderiv ℝ ψ y v) x w =
            (fderiv ℝ (fderiv ℝ ψ) x w) v := by
        have heq := fderiv_clm_apply hd (differentiableAt_const (x := x) v)
        simpa using congrArg (fun L : Vec 2 →L[ℝ] ℝ => L w) heq
      change fderiv ℝ (coordinateDerivative 1 ψ) x (unitVector 0) =
        fderiv ℝ (coordinateDerivative 0 ψ) x (unitVector 1)
      rw [show coordinateDerivative 1 ψ = fun y => fderiv ℝ ψ y (unitVector 1) by rfl,
        show coordinateDerivative 0 ψ = fun y => fderiv ℝ ψ y (unitVector 0) by rfl,
        happly (unitVector 1) (unitVector 0), happly (unitVector 0) (unitVector 1)]
      simpa [iteratedFDeriv_two_apply] using hswap
    have hLHS_eq : (∫ x in U, f x * coordinateDerivative 0 (coordinateDerivative 1 ψ) x) =
        (∫ x in U, f x * coordinateDerivative 1 (coordinateDerivative 0 ψ) x) := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      dsimp only
      rw [hcomm x]
    rw [hLHS_eq] at h0_deriv1
    rw [h1_deriv0] at h0_deriv1
    have h_eq : (∫ x in U, G x 0 * coordinateDerivative 1 ψ x) =
        (∫ x in U, G x 1 * coordinateDerivative 0 ψ x) := by
      linarith
    have hint0 : IntegrableOn (fun x => (-G x 1) * coordinateDerivative 0 ψ x) U volume :=
      integrableOn_mul_spatialTest hloc_rot0 htest_deriv0
    have hint1 : IntegrableOn (fun x => (G x 0) * coordinateDerivative 1 ψ x) U volume :=
      integrableOn_mul_spatialTest hloc_rot1 htest_deriv1
    calc
      (∫ x in U, dot (fun j => ![-G x 1, G x 0] j) (gradient ψ x)) =
          (∫ x in U, (-G x 1) * coordinateDerivative 0 ψ x + (G x 0) * coordinateDerivative 1 ψ x) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        simp [dot, gradient, Fin.sum_univ_two]
      _ = (∫ x in U, (-G x 1) * coordinateDerivative 0 ψ x) +
          (∫ x in U, (G x 0) * coordinateDerivative 1 ψ x) :=
        integral_add hint0 hint1
      _ = (-(∫ x in U, G x 1 * coordinateDerivative 0 ψ x)) +
          (∫ x in U, G x 0 * coordinateDerivative 1 ψ x) := by
        have h_first : (∫ x in U, (-G x 1) * coordinateDerivative 0 ψ x) =
            (-(∫ x in U, G x 1 * coordinateDerivative 0 ψ x)) := by
          calc
            (∫ x in U, (-G x 1) * coordinateDerivative 0 ψ x) =
                (∫ x in U, -(G x 1 * coordinateDerivative 0 ψ x)) := by
              refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
              ring
            _ = -(∫ x in U, G x 1 * coordinateDerivative 0 ψ x) := integral_neg _
        rw [h_first]
      _ = (-(∫ x in U, G x 1 * coordinateDerivative 0 ψ x)) +
          (∫ x in U, G x 1 * coordinateDerivative 0 ψ x) := by rw [h_eq]
      _ = 0 := by ring
      _ = -(∫ x in U, (0 : ℝ) * ψ x) := by simp

end EinsteinRelation.Correctors
