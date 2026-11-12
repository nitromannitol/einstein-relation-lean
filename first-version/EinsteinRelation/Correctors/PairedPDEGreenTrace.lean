import EinsteinRelation.Correctors.PairedPDEBoundedTrace
import EinsteinRelation.Correctors.PairedPDEKernelBound

/-! # Initial trace along the Green-function route

Source: `paper/main.tex:787–792,821–838,850`; AKM (9.2), printed p. 347,
and Proposition E.1, (E.4), (E.11), printed pp. 499–501.

For specified kernel representations, positivity, unit mass and the scalar
almost-everywhere initial limit imply the strong paired trace. No kernel
existence, formula (9.2), or scalar initial-limit theorem is assumed by the
existing `IsSemigroupSolution` predicate; those facts are explicit arguments
of the theorem below, not a new external input or a strengthened predicate.
-/

open MeasureTheory Filter
open scoped Topology

namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

/-- The Green-function route to the zero strong paired trace. The two scalar
initial limits need not be assumed equal: agreement of the vector data and
the distributional initial condition identify the paired limit as zero.
The kernel representation and the almost-everywhere initial limit are the
precise source facts still needed from AKM's canonical construction.
Source: `paper/main.tex:787–792,821–838,850`. -/
theorem paired_semigroupSolution_exists_zero_L2_extension_of_kernels
    {d : ℕ} {K : ℝ} {A₁ A₂ : Coefficient d K} {g₁ g₂ : Vec d → Vec d}
    {u₁ u₂ : ℝ × Vec d → ℝ} {G₁ G₂ : ℝ × Vec d → Vec d}
    (h₁ : IsSemigroupSolution A₁ g₁ u₁ G₁)
    (h₂ : IsSemigroupSolution A₂ g₂ u₂ G₂)
    {U : Set (Vec d)} (hU : IsOpen U)
    [IsFiniteMeasure (volume.restrict U)] (hg : Set.EqOn g₁ g₂ U)
    (P₁ P₂ : ℝ → Vec d → Vec d → ℝ) (a₁ a₂ : Vec d → ℝ)
    (ha₁ : AEStronglyMeasurable a₁ volume)
    (ha₂ : AEStronglyMeasurable a₂ volume)
    {B₁ B₂ : ℝ} (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (ha₁b : ∀ᵐ x ∂volume, |a₁ x| ≤ B₁)
    (ha₂b : ∀ᵐ x ∂volume, |a₂ x| ≤ B₂)
    (hP₁ : ∀ t : ℝ, 0 < t → ∀ x : Vec d,
      Integrable (P₁ t x) volume ∧ (∀ᵐ y ∂volume, 0 ≤ P₁ t x y) ∧
        (∫ y, P₁ t x y ∂volume) = 1)
    (hP₂ : ∀ t : ℝ, 0 < t → ∀ x : Vec d,
      Integrable (P₂ t x) volume ∧ (∀ᵐ y ∂volume, 0 ≤ P₂ t x y) ∧
        (∫ y, P₂ t x y ∂volume) = 1)
    (hrep₁ : ∀ t : ℝ, 0 < t → ∀ x : Vec d,
      u₁ (t, x) = ∫ y, P₁ t x y * a₁ y ∂volume)
    (hrep₂ : ∀ t : ℝ, 0 < t → ∀ x : Vec d,
      u₂ (t, x) = ∫ y, P₂ t x y * a₂ y ∂volume)
    (hinit₁ : ∀ᵐ x ∂volume, Tendsto (fun t => ∫ y, P₁ t x y * a₁ y ∂volume)
      (nhdsWithin 0 (Set.Ioi 0)) (𝓝 (a₁ x)))
    (hinit₂ : ∀ᵐ x ∂volume, Tendsto (fun t => ∫ y, P₂ t x y * a₂ y ∂volume)
      (nhdsWithin 0 (Set.Ioi 0)) (𝓝 (a₂ x))) :
    ∃ v : ℝ → Lp ℝ 2 (volume.restrict U),
      ContinuousWithinAt v (Set.Ici 0) 0 ∧ v 0 = 0 ∧
      (∀ t : ℝ, 0 < t →
        (v t : Vec d → ℝ) =ᵐ[volume.restrict U] fun x => u₁ (t, x) - u₂ (t, x)) ∧
      Tendsto (fun t => ∫ x in U, (u₁ (t, x) - u₂ (t, x))^2 ∂volume)
        (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0) := by
  apply paired_semigroupSolution_exists_zero_L2_extension_of_scalar_limits
    h₁ h₂ hU hg (ha₁.mono_measure Measure.restrict_le_self)
    (ha₂.mono_measure Measure.restrict_le_self) hB₁ hB₂ ?_ ?_
    (ae_restrict_of_ae ha₁b) (ae_restrict_of_ae ha₂b) ?_ ?_
  · intro t ht
    apply Filter.Eventually.of_forall
    intro x
    rw [hrep₁ t ht x]
    obtain ⟨hi, hp, hm⟩ := hP₁ t ht x
    exact (paired_kernel_average_bound hi hp hm ha₁ ha₁b).2
  · intro t ht
    apply Filter.Eventually.of_forall
    intro x
    rw [hrep₂ t ht x]
    obtain ⟨hi, hp, hm⟩ := hP₂ t ht x
    exact (paired_kernel_average_bound hi hp hm ha₂ ha₂b).2
  · apply ae_restrict_of_ae
    filter_upwards [hinit₁] with x hx
    apply hx.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (hrep₁ t ht x).symm
  · apply ae_restrict_of_ae
    filter_upwards [hinit₂] with x hx
    apply hx.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (hrep₂ t ht x).symm

end EinsteinRelation.Correctors
