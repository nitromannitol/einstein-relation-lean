import EinsteinRelation.External.AKMKernelSemigroup
import EinsteinRelation.Correctors.AKMHeatKernelConsequences
import EinsteinRelation.Correctors.AKMHeatKernelBoundedData
import EinsteinRelation.Correctors.AKMHeatKernelTimeContinuity
import EinsteinRelation.Correctors.AKMHeatKernelEnergySlices
import EinsteinRelation.Correctors.AKMHeatKernelWeakIdentification
import EinsteinRelation.Correctors.PairedPDEGreenTrace

/-! # Strong initial trace of the source-defined AKM flow

Source: `paper/main.tex:787–792,821–838,850`; AKM (9.2), p. 347,
Proposition E.1, (E.4), (E.10)–(E.11), pp. 499–501. The only kernel
premise identifies the actual canonical flow. Scalar representation,
almost-everywhere initial limits, and strong paired trace are proved
internally from the bounded weak divergence datum.
-/

open MeasureTheory Filter
open scoped Topology

namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

/-- Integration by parts identifies the canonical vector-datum evolution
with the scalar-datum kernel average. The energy-class slices suffice;
continuity then gives the identity at every positive time.
Source: AKM (9.2), p. 347; `paper/main.tex:787–792,850`. -/
theorem akm_canonical_kernel_package_of_bounded_divergence
    {d : ℕ} {K : ℝ} {A : Coefficient d K}
    {g : Vec d → Vec d} {u : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    (hsol : IsSemigroupSolution A g u G)
    (hcanonical : HasCanonicalKernelRepresentation A g u)
    {a : Vec d → ℝ} (hdiv : HasWeakDivergence Set.univ g a)
    (hg : AEStronglyMeasurable g volume) {B : ℝ}
    (hgb : ∀ᵐ x ∂volume, euclideanNorm (g x) ≤ B)
    (ha : AEStronglyMeasurable a volume) {D : ℝ}
    (hab : ∀ᵐ x ∂volume, |a x| ≤ D) :
    ∃ P : ℝ → Vec d → Vec d → ℝ,
      (∀ t : ℝ, 0 < t → ∀ x : Vec d,
        Integrable (P t x) volume ∧ (∀ᵐ y ∂volume, 0 ≤ P t x y) ∧
          (∫ y, P t x y ∂volume) = 1) ∧
      (∀ t : ℝ, 0 < t → ∀ x : Vec d,
        u (t,x) = ∫ y, P t x y * a y ∂volume) ∧
      (∀ᵐ x ∂volume, Tendsto (fun t => ∫ y, P t x y * a y ∂volume)
        (nhdsWithin 0 (Set.Ioi 0)) (𝓝 (a x))) := by
  obtain ⟨C, P, X, Y, H, _hC, hP, hrep⟩ := hcanonical
  refine ⟨P, fun t ht x => akm_heatKernel_mass hP t ht x, ?_,
    akm_heatKernel_initial_of_bounded hP ha hab⟩
  have hgs : ∀ᵐ x ∂volume, ‖g x‖ ≤ B := by
    filter_upwards [hgb] with x hx
    apply le_trans ?_ hx
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr fun j => ?_
    rw [Real.norm_eq_abs]
    apply Real.abs_le_sqrt
    change (g x j)^2 ≤ ∑ i, g x i * g x i
    simpa only [pow_two] using
      (Finset.single_le_sum (fun i (_ : i ∈ Finset.univ) => mul_self_nonneg (g x i))
        (Finset.mem_univ j))
  intro t ht x
  have hu : ContinuousOn (fun s => u (s,x)) (Set.Ioi 0) :=
    hsol.1.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun _ hs => ⟨hs, Set.mem_univ _⟩)
  have hv : ContinuousOn (fun s => ∫ y, P s x y * a y ∂volume) (Set.Ioi 0) := by
    apply akm_mass_one_kernel_average_continuousOn ?_ ?_ ?_ ?_ ha hab
    · intro y
      exact hP.1.comp (show Continuous (fun s : ℝ => (s, (x,y))) from
        continuous_id.prodMk continuous_const).continuousOn
        (fun _ hs => ⟨hs, Set.mem_univ _⟩)
    · intro s hs
      exact (akm_heatKernel_mass hP s hs x).1
    · intro s hs y
      exact hP.2.1 s hs x y
    · intro s hs
      exact (akm_heatKernel_mass hP s hs x).2.2
  apply akm_kernel_representation_of_ae_time hu hv ?_ t ht
  filter_upwards [ae_restrict_mem measurableSet_Ioi,
    akm_fundamental_energy_slices (hP.2.2.2.1 x).1] with s hspos hs
  rw [(hrep s hspos x).2]
  have hpc : Continuous (P s x) := by
    exact hP.1.comp_continuous (continuous_const.prodMk
      (continuous_const.prodMk continuous_id)) (fun y => ⟨hspos, Set.mem_univ _⟩)
  exact akm_weak_kernel_integration_by_parts hdiv hs.1 hpc
    (akm_heatKernel_mass hP s hspos x).1 hg ha hgs hab (hrep s hspos x).1

/-- The actual paired canonical flows have a strong zero local L² trace.
Kernel representation and scalar initial limits are consequences, rather
than hypotheses. Source: `paper/main.tex:821–838,850`. -/
theorem paired_canonicalSemigroup_exists_zero_L2_extension
    {d : ℕ} {K : ℝ} {A₁ A₂ : Coefficient d K}
    {g₁ g₂ : Vec d → Vec d} {u₁ u₂ : ℝ × Vec d → ℝ}
    {G₁ G₂ : ℝ × Vec d → Vec d}
    (h₁ : IsSemigroupSolution A₁ g₁ u₁ G₁)
    (h₂ : IsSemigroupSolution A₂ g₂ u₂ G₂)
    (hc₁ : HasCanonicalKernelRepresentation A₁ g₁ u₁)
    (hc₂ : HasCanonicalKernelRepresentation A₂ g₂ u₂)
    {a₁ a₂ : Vec d → ℝ}
    (hd₁ : HasWeakDivergence Set.univ g₁ a₁)
    (hd₂ : HasWeakDivergence Set.univ g₂ a₂)
    (hg₁ : AEStronglyMeasurable g₁ volume)
    (hg₂ : AEStronglyMeasurable g₂ volume)
    {B₁ B₂ : ℝ}
    (hb₁ : ∀ᵐ x ∂volume, euclideanNorm (g₁ x) ≤ B₁)
    (hb₂ : ∀ᵐ x ∂volume, euclideanNorm (g₂ x) ≤ B₂)
    (ha₁ : AEStronglyMeasurable a₁ volume)
    (ha₂ : AEStronglyMeasurable a₂ volume)
    {D₁ D₂ : ℝ} (hD₁ : 0 ≤ D₁) (hD₂ : 0 ≤ D₂)
    (hab₁ : ∀ᵐ x ∂volume, |a₁ x| ≤ D₁)
    (hab₂ : ∀ᵐ x ∂volume, |a₂ x| ≤ D₂)
    {U : Set (Vec d)} (hU : IsOpen U)
    [IsFiniteMeasure (volume.restrict U)] (hEq : Set.EqOn g₁ g₂ U) :
    ∃ v : ℝ → Lp ℝ 2 (volume.restrict U),
      ContinuousWithinAt v (Set.Ici 0) 0 ∧ v 0 = 0 ∧
      (∀ t : ℝ, 0 < t →
        (v t : Vec d → ℝ) =ᵐ[volume.restrict U] fun x => u₁ (t,x) - u₂ (t,x)) ∧
      Tendsto (fun t => ∫ x in U, (u₁ (t,x) - u₂ (t,x))^2 ∂volume)
        (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0) := by
  obtain ⟨P₁, hP₁, hrep₁, hinit₁⟩ :=
    akm_canonical_kernel_package_of_bounded_divergence h₁ hc₁ hd₁ hg₁ hb₁ ha₁ hab₁
  obtain ⟨P₂, hP₂, hrep₂, hinit₂⟩ :=
    akm_canonical_kernel_package_of_bounded_divergence h₂ hc₂ hd₂ hg₂ hb₂ ha₂ hab₂
  exact paired_semigroupSolution_exists_zero_L2_extension_of_kernels h₁ h₂ hU hEq
    P₁ P₂ a₁ a₂ ha₁ ha₂ hD₁ hD₂ hab₁ hab₂
    hP₁ hP₂ hrep₁ hrep₂ hinit₁ hinit₂

end EinsteinRelation.Correctors
