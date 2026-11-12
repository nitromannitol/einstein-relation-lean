import EinsteinRelation.Correctors.AKMHeatKernelPrescribedProperties
import EinsteinRelation.Correctors.AKMHeatKernelWeakIdentification
import EinsteinRelation.External.AKMKernelSemigroup

open MeasureTheory
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

/-- For a prescribed integrable kernel gradient, bounded weak-divergence
data give the canonical vector representation of the scalar evolution.
Source: AKM (9.2), p. 347; `paper/main.tex:787–792,850`. -/
theorem akm_heatKernel_canonical_representation_of_prescribed_integrable_gradient
    {d : ℕ} {K : ℝ} {A : Coefficient d K}
    {P : ℝ → Vec d → Vec d → ℝ}
    {X Y Z : ℝ → Vec d → Vec d → Vec d}
    {H : ℝ → Vec d → Vec d → Mat d} {C : ℝ → ℝ}
    (hC : ∀ α, 0 < α → α < K⁻¹ → 0 < C α)
    (hP : HeatKernelProperties A P X Y H C)
    (hZsol : ∀ y, IsFundamentalSolution A y
      (fun z => P z.1 z.2 y) (fun z => Z z.1 z.2 y))
    (hZw : ∀ y t, 0 < t → HasWeakGradient Set.univ
      (fun x => P t x y) (fun x => Z t x y))
    (hZi : ∀ y t, 0 < t → Integrable (fun x => Z t x y) volume)
    {g : Vec d → Vec d} {f : Vec d → ℝ}
    (hdiv : HasWeakDivergence Set.univ g f)
    (hg : AEStronglyMeasurable g volume) (hf : AEStronglyMeasurable f volume)
    {B D : ℝ} (hgb : ∀ᵐ y ∂volume, ‖g y‖ ≤ B)
    (hfb : ∀ᵐ y ∂volume, |f y| ≤ D) :
    HasCanonicalKernelRepresentation A g (fun z => ∫ y, P z.1 z.2 y*f y ∂volume) := by
  refine ⟨C,P,Z,(fun t x y => Z t y x),H,hC,
    akm_heatKernel_prescribed_properties hP hZsol,?_⟩
  intro t ht x
  have hi (j : Fin d) : Integrable (fun y => g y j * Z t y x j) volume := by
    have hz : Integrable (fun y => Z t y x j) volume :=
      (hZi x t ht).norm.mono'
        ((continuous_apply j).comp_aestronglyMeasurable (hZi x t ht).aestronglyMeasurable)
        (Filter.Eventually.of_forall fun y => norm_le_pi_norm (Z t y x) j)
    apply hz.bdd_mul ((continuous_apply j).comp_aestronglyMeasurable hg)
    filter_upwards [hgb] with y hy
    exact (norm_le_pi_norm (g y) j).trans hy
  have hint : Integrable (fun y => dot (g y) (Z t y x)) volume :=
    integrable_finset_sum _ (fun j _ => hi j)
  refine ⟨hint,?_⟩
  have hp : Continuous (fun y => P t y x) := by
    apply continuousOn_univ.mp
    exact hP.1.comp (continuous_const.prodMk (continuous_id.prodMk continuous_const)).continuousOn
      (fun y _ => ⟨ht,Set.mem_univ _⟩)
  have hid := akm_weak_kernel_integration_by_parts hdiv (hZw x t ht) hp
    (hP.2.2.2.2.2.1 t ht x).2.2.1 hg hf hgb hfb hint
  rw [hid]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun y => by
    change P t x y*f y = P t y x*f y
    rw [hP.2.2.2.2.1 t ht x y]

end EinsteinRelation.Correctors
