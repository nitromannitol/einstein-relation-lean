import EinsteinFull.Homogenization.SourceLimitingDualMatrix
import Mathlib.Topology.Instances.Matrix

/-!
# Convergence of minimizing fluxes

The minimizing fluxes for the expected responses in Armstrong, Kuusi and
Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Chapter 2, converge to the inverse limiting dual matrix applied to the loading.
-/

open MeasureTheory Filter Topology
open _root_.Homogenization

namespace EinsteinFull.Homogenization

open EinsteinRelation.Environment.AKMTestIntegralSupport

/-- The inverse annealed dual matrices converge to the inverse limiting matrix. -/
theorem tendsto_inv_annealedDualMatrix {d : ℕ} [NeZero d] {K : ℝ}
    (P : Measure (Coefficient d K)) [IsProbabilityMeasure P]
    (hstat : ∀ z : LatticeIndex d, Measure.map (translateCoefficient (latticeShift z)) P = P)
    (k : ℕ) (hk : K ≤ (k : ℝ) + 1) :
    Tendsto (fun n : ℕ => (annealedDualMatrix P n k hk)⁻¹) atTop
      (𝓝 (limitingAnnealedDualMatrix P)⁻¹) := by
  have hM : Tendsto (fun n : ℕ => annealedDualMatrix P n k hk) atTop
      (𝓝 (limitingAnnealedDualMatrix P)) := by
    apply tendsto_pi_nhds.mpr
    intro i
    apply tendsto_pi_nhds.mpr
    intro j
    exact tendsto_annealedDualMatrix_entry P hstat k hk i j
  have hdet : (limitingAnnealedDualMatrix P).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det (A := limitingAnnealedDualMatrix P)).mp
      (limitingAnnealedDualMatrix_posDef P hstat).isUnit).ne_zero
  have hinv : ContinuousAt (Ring.inverse : ℝ → ℝ) (limitingAnnealedDualMatrix P).det := by
    rw [Ring.inverse_eq_inv']
    exact continuousAt_inv₀ hdet
  exact (continuousAt_matrix_inv _ hinv).tendsto.comp hM

/-- The flux minimizing expected response converges for every fixed loading. -/
theorem tendsto_annealedResponse_minimizingFlux {d : ℕ} [NeZero d] {K : ℝ}
    (P : Measure (Coefficient d K)) [IsProbabilityMeasure P]
    (hstat : ∀ z : LatticeIndex d, Measure.map (translateCoefficient (latticeShift z)) P = P)
    (k : ℕ) (hk : K ≤ (k : ℝ) + 1) (p : Vec d) :
    Tendsto (fun n : ℕ => matVecMul (annealedDualMatrix P n k hk)⁻¹ p) atTop
      (𝓝 (matVecMul (limitingAnnealedDualMatrix P)⁻¹ p)) := by
  apply tendsto_pi_nhds.mpr
  intro i
  have h := tendsto_inv_annealedDualMatrix P hstat k hk
  have hi := (tendsto_pi_nhds.mp h) i
  change Tendsto (fun n => ∑ j : Fin d, (annealedDualMatrix P n k hk)⁻¹ i j * p j)
    atTop (𝓝 (∑ j : Fin d, (limitingAnnealedDualMatrix P)⁻¹ i j * p j))
  exact tendsto_finsetSum _ fun j _ => ((tendsto_pi_nhds.mp hi) j).mul_const (p j)

end EinsteinFull.Homogenization
