import EinsteinRelation.Correctors.IteratedLinearKernelCalculus
import EinsteinRelation.Correctors.LinearKernelIntegration
import EinsteinRelation.Correctors.KernelDerivativeOrderBounds

/-! # Uniform derivative masses under elliptic coordinate changes

Source: `paper/main.tex:1015–1018`. Entry bounds on the actual coordinate
map control all derivatives without choosing a constant after the law.
-/

open MeasureTheory
noncomputable section
namespace EinsteinRelation.Correctors.KernelCalculus

/-- A bounded linear change costs at most `(d*b)^k` in the mass of a
`k`th derivative (`paper/main.tex:1015–1018`). -/
theorem integral_abs_coordinateIterate_comp_linear_bound {d : ℕ}
    (B : Vec d ≃L[ℝ] Vec d) {b C : ℝ} (hb : 0 ≤ b)
    (hB : ∀ i j : Fin d, |(B (unitVector i)) j| ≤ b)
    {K : Vec d → ℝ} (hK : ContDiff ℝ (⊤ : ℕ∞) K) (hKc : HasCompactSupport K)
    (cs : List (Fin d))
    (hmass : ∀ ds : List (Fin d), ds.length = cs.length →
      (∫ x : Vec d, |coordinateIterate ds K x|) ≤ C) :
    |B.toContinuousLinearMap.det| *
      (∫ x : Vec d, |coordinateIterate cs (fun y => K (B y)) x|) ≤
      ((d : ℝ) * b) ^ cs.length * C := by
  classical
  let a : (Fin cs.length → Fin d) → ℝ := fun σ =>
    ∏ i : Fin cs.length, (B (unitVector (cs.get i))) (σ i)
  let F : Vec d → ℝ := fun x =>
    ∑ σ : Fin cs.length → Fin d, |a σ| * |coordinateIterate (List.ofFn σ) K x|
  have hi (σ : Fin cs.length → Fin d) : Integrable
      (fun x : Vec d => |a σ| * |coordinateIterate (List.ofFn σ) K x|) volume :=
    (integrable_coordinateIterate hK hKc _).abs.const_mul _
  have hiB (σ : Fin cs.length → Fin d) : Integrable
      (fun x : Vec d => |a σ| * |coordinateIterate (List.ofFn σ) K (B x)|) volume := by
    apply Integrable.const_mul
    apply Integrable.abs
    exact ((contDiff_coordinateIterate hK _).continuous.comp B.continuous).integrable_of_hasCompactSupport
      ((hasCompactSupport_coordinateIterate hKc _).comp_homeomorph B.toHomeomorph)
  have hleft := (integrable_coordinateIterate (hK.comp B.contDiff)
    (hKc.comp_homeomorph B.toHomeomorph) cs).abs
  have hright : Integrable (fun x : Vec d => F (B x)) volume :=
    integrable_finset_sum _ fun σ _ => hiB σ
  have hab (σ : Fin cs.length → Fin d) : |a σ| ≤ b ^ cs.length := by
    dsimp only [a]
    rw [Finset.abs_prod]
    calc
      _ ≤ ∏ _i : Fin cs.length, b := Finset.prod_le_prod
        (fun _ _ => abs_nonneg _) (fun i _ => hB (cs.get i) (σ i))
      _ = _ := by simp
  calc
    _ = ∫ x : Vec d, |B.toContinuousLinearMap.det| *
        |coordinateIterate cs (fun y => K (B y)) x| := (integral_const_mul _ _).symm
    _ ≤ ∫ x : Vec d, |B.toContinuousLinearMap.det| * F (B x) := by
      apply integral_mono (hleft.const_mul _) (hright.const_mul _)
      intro x
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      have he := coordinateIterate_comp_linear_expansion hK B.toContinuousLinearMap cs x
      change coordinateIterate cs (fun y => K (B y)) x =
        ∑ σ : Fin cs.length → Fin d, a σ * coordinateIterate (List.ofFn σ) K (B x) at he
      change |coordinateIterate cs (fun y => K (B y)) x| ≤ F (B x)
      rw [he]
      exact (Finset.abs_sum_le_sum_abs _ _).trans_eq (by
        simp only [F, a, abs_mul])
    _ = ∫ x : Vec d, F x := integral_normalized_linear B F
    _ = ∑ σ : Fin cs.length → Fin d,
        |a σ| * (∫ x : Vec d, |coordinateIterate (List.ofFn σ) K x|) := by
      rw [show F = fun x => ∑ σ : Fin cs.length → Fin d,
        |a σ| * |coordinateIterate (List.ofFn σ) K x| from rfl,
        integral_finset_sum _ fun σ _ => hi σ]
      simp_rw [integral_const_mul]
    _ ≤ ∑ _σ : Fin cs.length → Fin d, b ^ cs.length * C := by
      apply Finset.sum_le_sum
      intro σ _
      exact mul_le_mul (hab σ) (hmass _ List.length_ofFn)
        (integral_nonneg fun _ => abs_nonneg _) (pow_nonneg hb _)
    _ = _ := by simp [mul_pow, mul_assoc]

end EinsteinRelation.Correctors.KernelCalculus
