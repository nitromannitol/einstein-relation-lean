import EinsteinRelation.Correctors.AKMCanonicalFlowWeightedEnergy
import EinsteinRelation.Correctors.PairedPowerEnergyPrimitive

/-! # Canonical paired flow: zero trace and the actual energy primitive

Source: `paper/main.tex:813–840`. The canonical representation produces
one continuous energy, with zero initial value, whose positive-time
increments equal the integrals of the literal power-cutoff flux. The
local PDEs and canonical representation remain explicit data.
-/

open MeasureTheory
open scoped ENNReal
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

/-- The canonical paired weighted energy has its actual zero trace and
positive-time endpoint identity, with the same scalar and gradient fields.
Source: `paper/main.tex:813–840`. -/
theorem paired_canonicalSemigroup_power_energy_dynamics
    {d : ℕ} {K : ℝ} (hK : 0 < K) {A₁ A₂ : Coefficient d K}
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
    (hA : Set.EqOn A₁ A₂ U)
    (hl₁ : ∀ a b : ℝ, 0 < a → a < b → IsParabolicSolution A₁ (Set.Ioo a b) U u₁ G₁)
    (hl₂ : ∀ a b : ℝ, 0 < a → a < b → IsParabolicSolution A₂ (Set.Ioo a b) U u₂ G₂)
    {χ : Vec d → ℝ} (hχ : IsSpatialTest U χ) (n : ℕ) (hn : 1 ≤ n) :
    ∃ F : ℝ → ℝ, ContinuousOn F (Set.Ici 0) ∧ F 0 = 0 ∧
      (∀ t, 0 ≤ F t) ∧
      (∀ t : ℝ, 0 < t → F t = ∫ x in U, χ x^(2*n) * (u₁ (t,x) - u₂ (t,x))^2) ∧
      ∀ a b : ℝ, 0 < a → a < b →
        (∫ t in a..b,
          -2 * ∫ x in U, dot ((A₁ x).mulVec (G₁ (t,x) - G₂ (t,x))) (fun j =>
            χ x^(2*n) * (G₁ (t,x) - G₂ (t,x)) j +
              2 * (n : ℝ) * χ x^(2*n-1) * (u₁ (t,x) - u₂ (t,x)) * coordinateDerivative j χ x)) =
            F b - F a := by
  have hp := spatial_test_pow hχ n hn
  obtain ⟨F, hF, hF₀, hFn, hrep⟩ :=
    paired_canonicalSemigroup_continuous_weighted_energy h₁ h₂ hc₁ hc₂ hd₁ hd₂
      hg₁ hg₂ hb₁ hb₂ ha₁ ha₂ hD₁ hD₂ hab₁ hab₂ hU hUc hEq
      (hp.1.continuous.memLp_top_of_hasCompactSupport hp.2.1 _)
  have hrep' (t : ℝ) (ht : 0 < t) :
      F t = ∫ x in U, χ x^(2*n) * (u₁ (t,x) - u₂ (t,x))^2 := by
    simpa only [← pow_mul, Nat.mul_comm n 2] using hrep t ht
  refine ⟨F, hF, hF₀, hFn, hrep', ?_⟩
  intro a b ha hab
  rw [hrep' b (ha.trans hab), hrep' a ha]
  exact paired_semigroupSolutions_power_energy_integral_eq_sub hK ha hab
    h₁ h₂ hU hUc hA (hl₁ a b ha hab) (hl₂ a b ha hab) hχ n hn

end EinsteinRelation.Correctors
