import EinsteinRelation.Correctors.PhysicalCouplingWeightedEnergy
import EinsteinRelation.Correctors.NormalizedPairedEnergy

/-! # Normalized dissipation on the actual coefficient coupling

Source: `paper/main.tex:834–851`. The bounded initial trace and weighted
energy are already derived from the actual coefficient regularity. Spatial
normalization cancels from the nonlinear right-hand side.
-/

open MeasureTheory Set
open scoped Topology

namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport ReductionImageV3

/-- Actual coefficient regularity discharges all initial divergence and
trace premises in the normalized paired dissipation bound.
Source: `paper/main.tex:834–851`. -/
theorem physicalCoupling_paired_canonical_normalized_dissipation_le
    {d : ℕ} {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀) (i : Fin d)
    (u : Coefficient d (AKMUpperEllipticity L) → ℝ × Vec d → ℝ)
    (G : Coefficient d (AKMUpperEllipticity L) → ℝ × Vec d → Vec d)
    (hflow : ∀ᵐ A ∂actualCoefficientLaw Q,
      IsSemigroupSolution A (fun x => (A x).mulVec (unitVector i)) (u A) (G A) ∧
      HasCanonicalKernelRepresentation A (fun x => (A x).mulVec (unitVector i)) (u A))
    (μ : Measure (PhysicalField d L × PhysicalField d L))
    (hfst : MeasurePreserving Prod.fst μ (physicalReferenceLaw Q))
    (hsnd : MeasurePreserving Prod.snd μ (physicalReferenceLaw Q))
    {U : Set (Vec d)} (hU : IsOpen U) (hUc : IsCompact (closure U))
    [IsFiniteMeasure (volume.restrict U)] (hUpos : 0 < volume.real U)
    (hEq : ∀ᵐ A ∂μ, Set.EqOn (project (r₀ := r₀) Q.ellipticity_parameter A.1) (project (r₀ := r₀) Q.ellipticity_parameter A.2) U)
    {T : ℝ} (hT : 0 < T) {χ : Vec d → ℝ} (hχ : IsSpatialTest U χ)
    (hχb : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1)
    {M : ℝ} (hD : ∀ x, euclideanSq (gradient χ x) ≤ M^2)
    (n : ℕ) (hn : 2 ≤ n) :
    ∀ᵐ A ∂μ,
      (∫ t in (0 : ℝ)..T, ⨍ x in U,
        χ x^(2*n) * euclideanSq (G (project (r₀ := r₀) Q.ellipticity_parameter A.1) (t,x) - G (project (r₀ := r₀) Q.ellipticity_parameter A.2) (t,x))) ≤
      ((4 * (n : ℝ)^2 * (AKMUpperEllipticity L)^2 * M^2) * ∫ t in (0 : ℝ)..T,
        (⨍ x in U, (u (project (r₀ := r₀) Q.ellipticity_parameter A.1) (t,x) - u (project (r₀ := r₀) Q.ellipticity_parameter A.2) (t,x))^2)^((n : ℝ)⁻¹))^n := by
  filter_upwards [physicalCoupling_paired_canonical_weighted_energy_bound Q i u G
    hflow μ hfst hsnd hU hUc hEq hT hχ hχb hD n hn] with A hA
  have hraw := hA.2.2
  simp only [intervalIntegral.integral_of_le hT.le, ← integral_Icc_eq_integral_Ioc] at hraw ⊢
  exact setAverage_power_energy_le (volume.restrict (Icc 0 T)) volume U n
    (by omega) hUpos _ (fun t x => u (project (r₀ := r₀) Q.ellipticity_parameter A.1) (t,x) - u (project (r₀ := r₀) Q.ellipticity_parameter A.2) (t,x))
      (fun t x => χ x^(2*n) * euclideanSq (G (project (r₀ := r₀) Q.ellipticity_parameter A.1) (t,x) - G (project (r₀ := r₀) Q.ellipticity_parameter A.2) (t,x))) hraw

end EinsteinRelation.Correctors
