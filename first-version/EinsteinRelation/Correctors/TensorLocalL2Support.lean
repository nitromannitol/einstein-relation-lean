import EinsteinRelation.Correctors.FrobeniusDilation
import EinsteinRelation.Correctors.CoordinateMomentProjections
import Mathlib.MeasureTheory.Function.L2Space

/-! Source: `paper/main.tex:733-745`. Local Frobenius L² data control
every scalar tensor component in the canonical Poisson estimate. -/
open MeasureTheory
namespace EinsteinRelation.Correctors

/-- Entrywise L² membership gives integrability of the squared Frobenius norm. -/
theorem integrable_frobeniusNorm_sq_of_memLp
    {X : Type*} [MeasurableSpace X] {μ : Measure X} {d : ℕ}
    (S : X → Mat d) (hS : ∀ j k, MemLp (fun x => S x j k) 2 μ) :
    Integrable (fun x => frobeniusNorm (S x) ^ 2) μ := by
  simp only [frobeniusNorm_sq_eq_sum]
  exact integrable_finset_sum _ fun j _ => integrable_finset_sum _ fun k _ =>
    (hS j k).integrable_sq

/-- The root-integral norm of each entry is bounded by the tensor norm. -/
theorem sqrt_integral_entry_sq_le_frobenius
    {X : Type*} [MeasurableSpace X] {μ : Measure X} {d : ℕ}
    (S : X → Mat d) (hS : ∀ j k, MemLp (fun x => S x j k) 2 μ)
    (j k : Fin d) :
    Real.sqrt (∫ x, |S x j k| ^ 2 ∂μ) ≤
      Real.sqrt (∫ x, frobeniusNorm (S x) ^ 2 ∂μ) := by
  apply Real.sqrt_le_sqrt
  apply integral_mono
    (by simpa only [sq_abs] using (hS j k).integrable_sq)
    (integrable_frobeniusNorm_sq_of_memLp S hS)
  intro x
  exact pow_le_pow_left₀ (abs_nonneg _) (abs_entry_le_frobeniusNorm (S x) j k) 2
end EinsteinRelation.Correctors
