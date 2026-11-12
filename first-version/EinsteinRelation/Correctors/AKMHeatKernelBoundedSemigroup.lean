import EinsteinRelation.Correctors.AKMHeatKernelBoundedEvolution

open MeasureTheory Filter
open scoped Topology
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

/-- A bounded weak-divergence datum generates an actual continuous energy
flow through the specified E.1 kernel, including its distributional initial
condition and uniform initial-layer bound. Source:
AKM E.1 (E.1), (E.4), (E.11); `paper/main.tex:787–792,850–852`. -/
theorem akm_heatKernel_bounded_divergence_semigroup
    {d : ℕ} {K : ℝ} (hK : 0 < K) {A : Coefficient d K}
    {P : ℝ → Vec d → Vec d → ℝ}
    {X Y : ℝ → Vec d → Vec d → Vec d}
    {H : ℝ → Vec d → Vec d → Mat d} {C : ℝ → ℝ}
    (hP : HeatKernelProperties A P X Y H C)
    {g : Vec d → Vec d} {f : Vec d → ℝ}
    (hdiv : HasWeakDivergence Set.univ g f)
    (hf : Measurable f) {B : ℝ} (hB : 0 ≤ B) (hfb : ∀ y, |f y| ≤ B) :
    ∃ G : ℝ × Vec d → Vec d, Measurable G ∧
      IsSemigroupSolution A g (fun z => ∫ y, P z.1 z.2 y*f y ∂volume) G ∧
      ∀ t : ℝ, 0 < t → ∀ x : Vec d,
        |∫ y, P t x y*f y ∂volume| ≤ B := by
  obtain ⟨G,hGm,hsol⟩ := akm_heatKernel_bounded_data_parabolic_evolution hK hP hf hB hfb
  have hfa : AEStronglyMeasurable f volume := hf.aestronglyMeasurable
  have hba : ∀ᵐ y ∂volume, |f y| ≤ B := Filter.Eventually.of_forall hfb
  refine ⟨G,hGm,⟨akm_heatKernel_scalar_average_joint_continuousOn hP hfa hba,hsol,?_⟩,?_⟩
  · intro ψ hψ
    have hi := akm_heatKernel_scalar_average_test_trace hP hfa hba ψ hψ
    have he := hdiv.2.2 ψ hψ
    simp only [Measure.restrict_univ] at he
    convert hi using 1
    congr 1
    linarith only [he]
  · intro t ht x
    obtain ⟨hi,hp,hm⟩ := akm_heatKernel_mass hP t ht x
    exact (paired_kernel_average_bound hi hp hm hfa hba).2

end EinsteinRelation.Correctors
