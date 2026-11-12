import EinsteinRelation.Correctors.KernelDerivativeScaling
import EinsteinRelation.Correctors.HeatTransferIdentity

/-! # Derivatives under the homogenized coordinate change

Source: `paper/main.tex:1003–1018`. Coordinate chain rules for the actual
spatial kernels used to pass from radial to anisotropic Poisson equations.
-/

noncomputable section

namespace EinsteinRelation.Correctors.KernelCalculus

variable {d : ℕ}

private theorem linearFunctional_eq_sum (L : Vec d →L[ℝ] ℝ) (x : Vec d) :
    L x = ∑ j, x j * L (unitVector j) := by
  have hx : x = ∑ j, x j • unitVector j := by
    funext k
    simp [unitVector, Pi.single_apply, mul_ite]
  conv_lhs => rw [hx]
  simp only [map_sum, map_smul, smul_eq_mul]

/-- The coordinate chain rule for a continuous linear change of variables
(`paper/main.tex:1003–1018`). -/
theorem coordinateDerivative_comp_linear {K : Vec d → ℝ}
    (hK : ContDiff ℝ 1 K) (B : Vec d →L[ℝ] Vec d) (i : Fin d) (x : Vec d) :
    coordinateDerivative i (fun y => K (B y)) x =
      ∑ j, (B (unitVector i)) j * coordinateDerivative j K (B x) := by
  unfold coordinateDerivative
  change (fderiv ℝ (K ∘ B) x) (unitVector i) = _
  rw [((hK.differentiable le_rfl (B x)).hasFDerivAt.comp x B.hasFDerivAt).fderiv]
  exact linearFunctional_eq_sum (fderiv ℝ K (B x)) (B (unitVector i))

private theorem coordinateDerivative_sum {ι : Type*} [Fintype ι]
    {F : ι → Vec d → ℝ} (hF : ∀ j, ContDiff ℝ 1 (F j)) (i : Fin d) (x : Vec d) :
    coordinateDerivative i (fun y => ∑ j, F j y) x =
      ∑ j, coordinateDerivative i (F j) x := by
  unfold coordinateDerivative
  have hsum : (fun y => ∑ j, F j y) = ∑ j, F j := by
    funext y
    simp only [Finset.sum_apply]
  rw [hsum]
  rw [fderiv_sum (fun j _ => (hF j).differentiable le_rfl x)]
  simp only [ContinuousLinearMap.sum_apply]

private theorem coordinateDerivative_const_mul {K : Vec d → ℝ}
    (hK : ContDiff ℝ 1 K) (c : ℝ) (i : Fin d) (x : Vec d) :
    coordinateDerivative i (fun y => c * K y) x = c * coordinateDerivative i K x := by
  unfold coordinateDerivative
  rw [fderiv_const_mul (hK.differentiable le_rfl x) c]
  rfl

/-- The second coordinate chain rule for an arbitrary linear change
(`paper/main.tex:1003–1018`). -/
theorem coordinateIterate_two_comp_linear {K : Vec d → ℝ}
    (hK : ContDiff ℝ (⊤ : ℕ∞) K) (B : Vec d →L[ℝ] Vec d)
    (i j : Fin d) (x : Vec d) :
    coordinateIterate [i, j] (fun y => K (B y)) x =
      ∑ a, ∑ b, (B (unitVector j)) a * (B (unitVector i)) b *
        coordinateIterate [b, a] K (B x) := by
  have hK1 : ContDiff ℝ 1 K := hK.of_le (by norm_cast)
  have hD (a : Fin d) : ContDiff ℝ 1 (fun y => coordinateDerivative a K (B y)) :=
    ((contDiff_coordinateIterate hK [a]).comp B.contDiff).of_le (by norm_cast)
  have hfirst : (fun y => coordinateDerivative j (fun z => K (B z)) y) =
      fun y => ∑ a, (B (unitVector j)) a * coordinateDerivative a K (B y) :=
    funext fun y => coordinateDerivative_comp_linear hK1 B j y
  change coordinateDerivative i (fun y => coordinateDerivative j (fun z => K (B z)) y) x = _
  rw [hfirst, coordinateDerivative_sum (fun a => contDiff_const.mul (hD a))]
  apply Finset.sum_congr rfl
  intro a _
  rw [coordinateDerivative_const_mul (hD a)]
  rw [coordinateDerivative_comp_linear (K := coordinateDerivative a K)
    ((contDiff_coordinateIterate hK [a]).of_le (by norm_cast)) B i x]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun b _ => by
    simp only [coordinateIterate]
    ring

end EinsteinRelation.Correctors.KernelCalculus
