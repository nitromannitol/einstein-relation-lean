import EinsteinRelation.Correctors.LinearKernelCalculus
import EinsteinRelation.Correctors.KernelDerivativeConstants

/-! # All-order coordinate chain rule

Source: `paper/main.tex:1015–1018`. The full finite expansion exposes
uniform coefficients for the homogenized change of coordinates.
-/

noncomputable section
namespace EinsteinRelation.Correctors.KernelCalculus

private theorem coordinateDerivative_fintype_sum {d : ℕ} {ι : Type*} [Fintype ι]
    {F : ι → Vec d → ℝ} (hF : ∀ j, ContDiff ℝ 1 (F j)) (i : Fin d) (x : Vec d) :
    coordinateDerivative i (fun y => ∑ j, F j y) x = ∑ j, coordinateDerivative i (F j) x := by
  unfold coordinateDerivative
  have he : (fun y => ∑ j, F j y) = ∑ j, F j := by ext y; simp
  rw [he, fderiv_sum (fun j _ => (hF j).differentiable le_rfl x)]
  simp only [ContinuousLinearMap.sum_apply]

/-- Every iterated derivative of a linearly transformed smooth kernel has
a finite coordinate expansion (`paper/main.tex:1015–1018`). -/
theorem coordinateIterate_comp_linear_expansion {d : ℕ} {K : Vec d → ℝ}
    (hK : ContDiff ℝ (⊤ : ℕ∞) K) (B : Vec d →L[ℝ] Vec d)
    (cs : List (Fin d)) (x : Vec d) :
    coordinateIterate cs (fun y => K (B y)) x =
      ∑ σ : Fin cs.length → Fin d,
        (∏ i : Fin cs.length, (B (unitVector (cs.get i))) (σ i)) *
        coordinateIterate (List.ofFn σ) K (B x) := by
  classical
  induction cs generalizing x with
  | nil => simp [coordinateIterate]
  | cons i rest ih =>
    let a : (Fin rest.length → Fin d) → ℝ := fun σ =>
      ∏ k : Fin rest.length, (B (unitVector (rest.get k))) (σ k)
    have hs (σ : Fin rest.length → Fin d) :
        ContDiff ℝ (⊤ : ℕ∞) (fun y => coordinateIterate (List.ofFn σ) K (B y)) :=
      (contDiff_coordinateIterate hK _).comp B.contDiff
    have he : coordinateIterate rest (fun y => K (B y)) =
        fun y => ∑ σ : Fin rest.length → Fin d, a σ * coordinateIterate (List.ofFn σ) K (B y) :=
      funext ih
    change coordinateDerivative i (coordinateIterate rest (fun y => K (B y))) x = _
    rw [he, coordinateDerivative_fintype_sum (fun σ =>
      (contDiff_const.mul (hs σ)).of_le (by norm_cast))]
    have hd (σ : Fin rest.length → Fin d) :
        coordinateDerivative i (fun y => a σ * coordinateIterate (List.ofFn σ) K (B y)) x =
        ∑ j, a σ * ((B (unitVector i)) j * coordinateIterate (j :: List.ofFn σ) K (B x)) := by
      have h := congrFun (coordinateIterate_const_mul (hs σ) [i] (a σ)) x
      change coordinateDerivative i (fun y => a σ * coordinateIterate (List.ofFn σ) K (B y)) x =
        a σ * coordinateDerivative i (fun y => coordinateIterate (List.ofFn σ) K (B y)) x at h
      rw [h, coordinateDerivative_comp_linear
        ((contDiff_coordinateIterate hK _).of_le (by norm_cast)) B i x, Finset.mul_sum]
      rfl
    simp_rw [hd]
    rw [Finset.sum_comm]
    let e : (Fin d × (Fin rest.length → Fin d)) ≃ (Fin (rest.length + 1) → Fin d) :=
      Fin.consEquiv (fun _ => Fin d)
    have hp := Fintype.sum_prod_type (fun q : Fin d × (Fin rest.length → Fin d) =>
      a q.2 * ((B (unitVector i)) q.1 * coordinateIterate (q.1 :: List.ofFn q.2) K (B x)))
    rw [← hp]
    change (∑ q : Fin d × (Fin rest.length → Fin d),
      a q.2 * ((B (unitVector i)) q.1 * coordinateIterate (q.1 :: List.ofFn q.2) K (B x))) =
      ∑ σ : Fin (rest.length + 1) → Fin d,
        (∏ k : Fin (rest.length + 1), (B (unitVector ((i :: rest).get k))) (σ k)) *
          coordinateIterate (List.ofFn σ) K (B x)
    apply Fintype.sum_equiv e
    intro q
    change a q.2 * ((B (unitVector i)) q.1 * coordinateIterate (q.1 :: List.ofFn q.2) K (B x)) =
      (∏ k : Fin (rest.length + 1), (B (unitVector ((i :: rest).get k)))
        ((Fin.cons q.1 q.2 : Fin (rest.length + 1) → Fin d) k)) *
        coordinateIterate (List.ofFn (Fin.cons q.1 q.2)) K (B x)
    simp [Fin.prod_univ_succ, a, mul_assoc, mul_left_comm]

end EinsteinRelation.Correctors.KernelCalculus
