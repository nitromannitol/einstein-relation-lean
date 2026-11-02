import EinsteinFull.Calculus.C20TubeNegativePowerGradientIntegrability
import EinsteinFull.Calculus.FellerRegularSet

open EinsteinRelation MeasureTheory Filter EinsteinFull.External.Source.GMP
open PDE hiding Vec Mat

namespace EinsteinFull.Calculus

/-- The half-negative-power gradient has finite spacetime quadratic energy. -/
theorem c20_negative_half_power_gradient_memLp
    {X : Type*} [MeasurableSpace X] (μ : Measure X) {d : ℕ}
    (u : X → ℝ) (hu : AEStronglyMeasurable u μ)
    (G : X → Vec d) (hG : AEStronglyMeasurable G μ)
    (hG2 : MemLp (fun x => euclideanNorm (G x)) 2 μ)
    (ε p : ℝ) (hε : 0 < ε) (hp : 0 < p)
    (hpos : ∀ᵐ x ∂μ, ε ≤ u x) :
    MemLp (fun x => euclideanNorm ((-p/2 * Real.rpow (u x) (-p/2-1)) • G x)) 2 μ := by
  have hm : AEStronglyMeasurable
      (fun x => euclideanNorm ((-p/2 * Real.rpow (u x) (-p/2-1)) • G x)) μ := by
    have hg := ((hu.aemeasurable.pow_const (-p/2-1)).aestronglyMeasurable.const_mul (-p/2)).smul hG
    exact (Feller.continuous_euclideanNorm d).comp_aestronglyMeasurable hg
  apply (memLp_two_iff_integrable_sq hm).2
  have hi := (c20_negative_power_gradient_energy_integrable μ u hu G hG2 ε p hε hp hpos).const_mul ((-p/2)^2)
  apply hi.congr
  filter_upwards [hpos] with x hx
  have hr : Real.rpow (u x) (-p/2-1) ^ 2 = Real.rpow (u x) (-p-2) := by
    change (u x ^ (-p/2-1 : ℝ)) ^ (2 : ℕ) = u x ^ (-p-2 : ℝ)
    rw [← Real.rpow_mul_natCast (le_trans hε.le hx)]
    congr 1
    ring
  have hn : euclideanNorm (G x) ^ 2 = euclideanSq (G x) := by
    apply Real.sq_sqrt
    unfold euclideanSq dot
    exact Finset.sum_nonneg fun i _ => mul_self_nonneg (G x i)
  rw [TimeChange.euclideanNorm_smul, mul_pow, sq_abs, mul_pow, hr, hn]
  ring

/-- The same estimate for the full finite-cylinder caloric gradient. -/
theorem c20_weighted_caloric_negative_half_power_gradient_memLp
    {d : ℕ} {I : Set ℝ} {U : Set (Vec d)}
    (ρ : Vec d → ℝ) (α : Vec d → Mat d)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hcal : IsWeightedCaloric ρ α I U u G)
    (ε p : ℝ) (hε : 0 < ε) (hp : 0 < p)
    (hpos : ∀ᵐ z ∂volume.restrict (I ×ˢ U), ε ≤ u z) :
    MemLp (fun z => euclideanNorm ((-p/2 * Real.rpow (u z) (-p/2-1)) • G z))
      2 (volume.restrict (I ×ˢ U)) :=
  c20_negative_half_power_gradient_memLp _ u hcal.1.aestronglyMeasurable G hcal.2.1
    hcal.2.2.1 ε p hε hp hpos

end EinsteinFull.Calculus
