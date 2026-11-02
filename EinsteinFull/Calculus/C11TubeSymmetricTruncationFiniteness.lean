import EinsteinFull.Calculus.C20TubeWeightedNonlinearEnergyLimit
import EllipticRegularity.Parabolic.LocalMax.PowerFamily

open MeasureTheory PDE.Parabolic.LocalMax

namespace EinsteinFull.Calculus

/-- A fixed symmetric truncation has finite energy for every square-integrable function. -/
theorem c11_symmetric_truncation_integrable_of_memLp_two
    {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    (u : X → ℝ) (hu : MemLp u 2 μ)
    (p ε : ℝ) (hp : 2 ≤ p) (hε : 0 < ε) (n : ℕ) :
    Integrable (fun x => PDE.Parabolic.LocalMax.powF p ε (n : ℝ) (u x) +
      PDE.Parabolic.LocalMax.powF p ε (n : ℝ) (-u x)) μ := by
  have hN : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  obtain ⟨C, hC⟩ := exists_powF2_bound (p := p) (N := (n : ℝ)) (by linarith) hε hN
  have hF := powF_contDiff (p := p) hε hN
  have hpos : Integrable (fun x => powF p ε (n : ℝ) (u x)) μ :=
    c20_nonlinear_comp_integrable u hu _ hF C C.coe_nonneg hC
  have hneg : Integrable (fun x => powF p ε (n : ℝ) (-u x)) μ :=
    c20_nonlinear_comp_integrable (fun x => -u x) hu.neg _ hF C C.coe_nonneg hC
  exact hpos.add hneg

end EinsteinFull.Calculus

