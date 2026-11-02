import EinsteinRelation.Calculus.Weak
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-! Source: `paper/main.tex:693-702`. The smooth tests used in changes of spatial scale. -/
namespace EinsteinRelation.Correctors

/-- Inverse dilation preserves spatial tests and gives the coordinate chain rule. -/
theorem isSpatialTest_inv_dilation {d : ℕ} (ψ : Vec d → ℝ)
    (hψ : IsSpatialTest Set.univ ψ) (r : ℝ) (hr : 0 < r) :
    IsSpatialTest Set.univ (fun x => ψ (r⁻¹ • x)) ∧
    ∀ x : Vec d, ∀ j : Fin d,
      coordinateDerivative j (fun z => ψ (r⁻¹ • z)) (r • x) =
        r⁻¹ * coordinateDerivative j ψ x := by
  refine ⟨⟨hψ.1.comp (contDiff_id.const_smul _),
    hψ.2.1.comp_homeomorph (Homeomorph.smul (Units.mk0 r⁻¹ (inv_ne_zero hr.ne'))),
    Set.subset_univ _⟩, ?_⟩
  intro x j
  have hd := (hψ.1.differentiable (by simp) (r⁻¹ • (r • x))).hasFDerivAt.comp
    (r • x) ((hasFDerivAt_id (r • x)).const_smul r⁻¹)
  unfold coordinateDerivative
  rw [show fderiv ℝ (fun z => ψ (r⁻¹ • z)) (r • x) =
    (fderiv ℝ ψ (r⁻¹ • (r • x))).comp (r⁻¹ • ContinuousLinearMap.id ℝ (Vec d)) from hd.fderiv]
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
    map_smul, smul_eq_mul, smul_smul, inv_mul_cancel₀ hr.ne', one_smul]

end EinsteinRelation.Correctors
