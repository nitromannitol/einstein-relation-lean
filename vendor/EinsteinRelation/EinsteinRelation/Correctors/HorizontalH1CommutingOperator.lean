import EinsteinRelation.Calculus.HorizontalSobolev

/-! # Operators commuting with stationary translations

Source: `paper/main.tex:240–248,693–698`.
-/

open MeasureTheory
namespace EinsteinRelation.Correctors

/-- An operator commuting with translations preserves the actual H¹ domain
and its coordinate generators; source `paper/main.tex:240-248,693-698`. -/
theorem horizontalH1_of_commuting_operator {d : ℕ}
    (Q : Measure (FieldPair d)) (hQ : IsStationary Q)
    (P : Lp ℝ 2 Q →L[ℝ] Lp ℝ 2 Q)
    (hP : ∀ (x : Vec d) (f : Lp ℝ 2 Q),
      P (translationLp Q hQ x f) = translationLp Q hQ x (P f))
    (f : horizontalH1 Q hQ) :
    ∃ g : horizontalH1 Q hQ, (g : Lp ℝ 2 Q) = P f ∧
      ∀ i, horizontalH1Gradient Q hQ g i = P (horizontalH1Gradient Q hQ f i) := by
  let g_grad : Fin d → Lp ℝ 2 Q := fun i => P (horizontalH1Gradient Q hQ f i)
  have hg_grad : ∀ i, HasHorizontalLpDerivative Q hQ i (P f) (g_grad i) := by
    intro i
    have hderiv := hasHorizontalLpDerivative_horizontalH1Gradient Q hQ f i
    unfold HasHorizontalLpDerivative at hderiv ⊢
    have h_eq : (fun t : ℝ => t⁻¹ • (translationLp Q hQ (t • unitVector i) (P f) - P f)) =
        (fun t : ℝ => P (t⁻¹ • (translationLp Q hQ (t • unitVector i) f - f))) := by
      funext t
      apply Lp.ext
      filter_upwards [coeFn_translationLp Q hQ (t • unitVector i) f] with ω
      simp [hP (t • unitVector i) f, P.map_sub, P.map_smul, smul_sub]
    rw [h_eq]
    exact Filter.Tendsto.comp P.continuous.continuousAt hderiv
  let g : horizontalH1 Q hQ := ⟨P f, g_grad, hg_grad⟩
  refine ⟨g, rfl, fun i => ?_⟩
  have h_eq_grad := horizontalH1Gradient_eq_of_hasHorizontalLpDerivative Q hQ g g_grad hg_grad
  rw [h_eq_grad]

end EinsteinRelation.Correctors
