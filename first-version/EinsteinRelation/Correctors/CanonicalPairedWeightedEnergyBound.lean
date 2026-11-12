import EinsteinRelation.Correctors.CanonicalPairedPowerEnergy
import EinsteinRelation.Correctors.PairedWeightedEnergyBound
import EinsteinRelation.Correctors.EnergyRootIntegrability

/-! # Weighted energy bound of the actual canonical paired flow

Source: `paper/main.tex:813–840`. The canonical formula supplies the zero
trace. The weak PDE supplies the time equation, coercivity and spatial
interpolation. The resulting bound concerns the literal scalar and
Euclidean gradient fields, without an assumed energy derivative or trace.
-/

open MeasureTheory
open scoped ENNReal
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

/-- The actual canonical paired flow satisfies the manuscript's weighted
energy and integrated dissipation bounds. Kernel representations and the
bounded divergence data remain explicit. The scalar source integral
is proved from the canonical continuous trace.
Source: `paper/main.tex:813–840`. -/
theorem paired_canonicalSemigroup_weighted_energy_bound
    {d : ℕ} {K : ℝ} (hK : 0 < K) {T : ℝ} (hT : 0 < T) {A₁ A₂ : Coefficient d K}
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
    {χ : Vec d → ℝ} (hχ : IsSpatialTest U χ)
    (hχb : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1)
    {L : ℝ} (hD : ∀ x, euclideanSq (gradient χ x) ≤ L^2)
    (n : ℕ) (hn : 2 ≤ n) :
    let E := fun t => ∫ x in U, χ x^(2*n) * euclideanSq (G₁ (t,x) - G₂ (t,x))
    let B := (4 * (n : ℝ)^2 * K^2 * L^2) * ∫ t in (0 : ℝ)..T,
      (∫ x in U, (u₁ (t,x) - u₂ (t,x))^2)^((n : ℝ)⁻¹)
    IntegrableOn E (Set.Icc 0 T) ∧
      (∀ t ∈ Set.Ioc 0 T, (∫ x in U, χ x^(2*n) * (u₁ (t,x) - u₂ (t,x))^2) ≤ B^n) ∧
      (∫ t in (0 : ℝ)..T, E t) ≤ B^n := by
  have hp := spatial_test_pow hχ n (by omega)
  obtain ⟨F, hF, hF₀, hFn, hrep⟩ :=
    paired_canonicalSemigroup_continuous_weighted_energy h₁ h₂ hc₁ hc₂ hd₁ hd₂
      hg₁ hg₂ hb₁ hb₂ ha₁ ha₂ hD₁ hD₂ hab₁ hab₂ hU hUc hEq
      (hp.1.continuous.memLp_top_of_hasCompactSupport hp.2.1 _)
  have hrep' (t : ℝ) (ht : 0 < t) :
      F t = ∫ x in U, χ x^(2*n) * (u₁ (t,x) - u₂ (t,x))^2 := by
    simpa only [← pow_mul, Nat.mul_comm n 2] using hrep t ht
  obtain ⟨S, hS, _, _, hSrep⟩ :=
    paired_canonicalSemigroup_continuous_weighted_energy h₁ h₂ hc₁ hc₂ hd₁ hd₂
      hg₁ hg₂ hb₁ hb₂ ha₁ ha₂ hD₁ hD₂ hab₁ hab₂ hU hUc hEq
      (memLp_const (1 : ℝ))
  have hsource : IntegrableOn (fun t =>
      (∫ x in U, (u₁ (t,x) - u₂ (t,x))^2)^((n : ℝ)⁻¹)) (Set.Icc 0 T) := by
    apply energy_root_integrable_of_continuous_extension n
      (hS.mono (fun _ ht => ht.1))
    intro t ht _
    simpa only [one_pow, one_mul] using hSrep t ht
  obtain ⟨hEi, hbound, hdiss⟩ := paired_semigroupSolutions_weighted_energy_bound hK hT
    h₁ h₂ hU hUc hA hχ hχb hD n hn F
        (hF.mono (fun _ ht => ht.1)) hF₀ (fun t _ => hFn t)
          (fun t ht _ => hrep' t ht) hsource
  refine ⟨hEi, ?_, hdiss⟩
  intro t ht
  rw [← hrep' t ht.1]
  exact hbound t ⟨ht.1.le, ht.2⟩

end EinsteinRelation.Correctors
