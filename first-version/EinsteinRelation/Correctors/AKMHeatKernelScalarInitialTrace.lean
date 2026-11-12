import EinsteinRelation.Correctors.AKMHeatKernelJointContinuity
import EinsteinRelation.Correctors.AKMCanonicalKernelTrace

open MeasureTheory Filter
open scoped Topology
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

/-- The scalar evolution defined directly by an E.1 kernel has the compact-test
initial trace of its bounded scalar datum. Source: AKM Proposition E.1,
(E.3), (E.11), pp. 499–501; `paper/main.tex:787–792,850`. -/
theorem akm_heatKernel_scalar_average_test_trace
    {d : ℕ} {K : ℝ} {A : Coefficient d K}
    {P : ℝ → Vec d → Vec d → ℝ}
    {X Y : ℝ → Vec d → Vec d → Vec d}
    {H : ℝ → Vec d → Vec d → Mat d} {C : ℝ → ℝ}
    (hP : HeatKernelProperties A P X Y H C)
    {f : Vec d → ℝ} (hf : AEStronglyMeasurable f volume)
    {B : ℝ} (hB : ∀ᵐ y ∂volume, |f y| ≤ B)
    (ψ : Vec d → ℝ) (hψ : IsSpatialTest Set.univ ψ) :
    Tendsto (fun t => ∫ x, (∫ y, P t x y*f y ∂volume)*ψ x ∂volume)
      (nhdsWithin 0 (Set.Ioi 0)) (𝓝 (∫ x, f x*ψ x ∂volume)) := by
  have hu := akm_heatKernel_scalar_average_joint_continuousOn hP hf hB
  have huc (t : ℝ) (ht : 0 < t) :
      Continuous (fun x => ∫ y, P t x y*f y ∂volume) :=
    hu.comp_continuous (continuous_const.prodMk continuous_id)
      (fun x => ⟨ht,Set.mem_univ _⟩)
  have hi : Integrable ψ volume := hψ.1.continuous.integrable_of_hasCompactSupport hψ.2.1
  have hb (t : ℝ) (ht : 0 < t) (x : Vec d) :
      |∫ y, P t x y*f y ∂volume| ≤ |B| := by
    obtain ⟨hpi,hpp,hpm⟩ := akm_heatKernel_mass hP t ht x
    exact (paired_kernel_average_bound hpi hpp hpm hf hB).2.trans (le_abs_self B)
  apply tendsto_integral_filter_of_dominated_convergence (fun x => |B| * |ψ x|)
  · filter_upwards [self_mem_nhdsWithin] with t ht
    exact (huc t ht).aestronglyMeasurable.mul hψ.1.continuous.aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with t ht
    exact Filter.Eventually.of_forall fun x => by
      simpa only [norm_mul,Real.norm_eq_abs] using
        mul_le_mul_of_nonneg_right (hb t ht x) (abs_nonneg (ψ x))
  · exact hi.abs.const_mul |B|
  · filter_upwards [akm_heatKernel_initial_of_bounded hP hf hB] with x hx
    exact hx.mul_const (ψ x)
end EinsteinRelation.Correctors
