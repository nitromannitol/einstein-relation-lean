import EinsteinRelation.Correctors.AKMCanonicalKernelTrace
import EinsteinRelation.Correctors.ParabolicWeightedEnergyContinuity

/-! # Continuous weighted energy for the canonical source flow

Source: `paper/main.tex:821–850`; AKM (9.2), p. 347, and Proposition E.1,
pp. 499–501. The canonical vector-datum formula supplies the strong paired
initial trace through the internal kernel integration-by-parts package.
The scalar representation, initial limit and continuous endpoint energy
are all conclusions. No uniqueness of arbitrary weak solutions is used.
-/

open MeasureTheory
open scoped Topology ENNReal

namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

/-- The same actual canonical flows have continuous weighted energy through
time zero wherever their initial vector data agree. The canonical formula
is explicit data; this theorem does not assume a candidate literature Prop.
Source: `paper/main.tex:821–850`. -/
theorem paired_canonicalSemigroup_continuous_weighted_energy
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
    {U : Set (Vec d)} (hU : IsOpen U) (hUc : IsCompact (closure U))
    [IsFiniteMeasure (volume.restrict U)] (hEq : Set.EqOn g₁ g₂ U)
    {χ : Vec d → ℝ} (hχ : MemLp χ ∞ (volume.restrict U)) :
    ∃ F : ℝ → ℝ, ContinuousOn F (Set.Ici 0) ∧ F 0 = 0 ∧
      (∀ t, 0 ≤ F t) ∧ ∀ t : ℝ, 0 < t →
        F t = ∫ x in U, χ x^2 * (u₁ (t,x) - u₂ (t,x))^2 := by
  obtain ⟨v, hv, hv₀, hrep, _⟩ :=
    paired_canonicalSemigroup_exists_zero_L2_extension h₁ h₂ hc₁ hc₂
      hd₁ hd₂ hg₁ hg₂ hb₁ hb₂ ha₁ ha₂ hD₁ hD₂ hab₁ hab₂ hU hEq
  exact paired_weighted_energy_continuous_of_local_L2_trace h₁ h₂ hUc v hv hv₀ hrep hχ

end EinsteinRelation.Correctors
