import EinsteinRelation.Correctors.AKMHeatKernelGradientIntegrability
import EinsteinRelation.Correctors.AKMHeatKernelCanonicalRepresentation
import EinsteinRelation.Correctors.AKMHeatKernelBoundedSemigroup

open MeasureTheory
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

/-- A specified E.1 kernel constructs the canonical energy flow of bounded
weak-divergence data. All-time absolute convergence and the vector formula
are proved from E.1, rather than assumed. Source: AKM (9.2), p. 347;
`paper/main.tex:787–806,850–852`. -/
theorem akm_heatKernel_bounded_divergence_canonical_semigroup
    {d : ℕ} {K : ℝ} (hK : 0 < K) {A : Coefficient d K}
    {P : ℝ → Vec d → Vec d → ℝ}
    {X Y : ℝ → Vec d → Vec d → Vec d}
    {H : ℝ → Vec d → Vec d → Mat d} {C : ℝ → ℝ}
    (hC : ∀ α, 0 < α → α < K⁻¹ → 0 < C α)
    (hP : HeatKernelProperties A P X Y H C)
    {g : Vec d → Vec d} {f : Vec d → ℝ}
    (hdiv : HasWeakDivergence Set.univ g f)
    (hg : AEStronglyMeasurable g volume) (hf : Measurable f)
    {B D : ℝ} (hgb : ∀ᵐ y ∂volume, ‖g y‖ ≤ B)
    (hD : 0 ≤ D) (hfb : ∀ y, |f y| ≤ D) :
    ∃ G : ℝ × Vec d → Vec d, Measurable G ∧
      IsSemigroupSolution A g (fun z => ∫ y, P z.1 z.2 y*f y ∂volume) G ∧
      HasCanonicalKernelRepresentation A g (fun z => ∫ y, P z.1 z.2 y*f y ∂volume) ∧
      ∀ t : ℝ, 0 < t → ∀ x : Vec d,
        |∫ y, P t x y*f y ∂volume| ≤ D := by
  obtain ⟨Z,hZm,hZsol,hZw⟩ := akm_heatKernel_exists_measurable_prescribed_gradient hK hP
  have hZi := akm_heatKernel_prescribed_gradient_integrable hK hP hZm hZsol hZw
  obtain ⟨G,hGm,hsol,hbound⟩ := akm_heatKernel_bounded_divergence_semigroup hK hP hdiv hf hD hfb
  exact ⟨G,hGm,hsol,
    akm_heatKernel_canonical_representation_of_prescribed_integrable_gradient
      hC hP hZsol hZw hZi hdiv hg hf.aestronglyMeasurable hgb
        (Filter.Eventually.of_forall hfb),hbound⟩

end EinsteinRelation.Correctors
