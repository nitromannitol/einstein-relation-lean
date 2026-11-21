import EinsteinFull.External.DFGW.Trajectory

/-! # Correlations of a reversible process

Time reflection exchanges the two endpoints of a trajectory interval. Consequently the
correlation of two observables is symmetric in the observables.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S]
variable {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- Time reversal interchanges the endpoints of a two-time correlation. -/
theorem integral_mul_eval_comm (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (f g : S → ℝ) (t : ℝ)
    (hfg : Integrable (fun η : C(ℝ, S) => f (η 0) * g (η t)) P) :
    (∫ η : C(ℝ, S), f (η 0) * g (η t) ∂P) =
      ∫ η : C(ℝ, S), g (η 0) * f (η t) ∂P := by
  have hmap := integral_map (μ := P) (measurable_refl (S := S) (t / 2)).aemeasurable
    (f := fun η : C(ℝ, S) => f (η 0) * g (η t)) (by
      rw [hP.reversible]
      exact hfg.aestronglyMeasurable)
  rw [hP.reversible] at hmap
  calc
    (∫ η : C(ℝ, S), f (η 0) * g (η t) ∂P) =
        ∫ η : C(ℝ, S), f (Draft.dfgwRefl (t / 2) η 0) *
          g (Draft.dfgwRefl (t / 2) η t) ∂P := hmap
    _ = ∫ η : C(ℝ, S), g (η 0) * f (η t) ∂P := by
      congr 1
      funext η
      have h₀ : Draft.dfgwRefl (t / 2) η 0 = η t := by
        change η (2 * (t / 2) - 0) = η t
        congr 1
        ring
      have h₁ : Draft.dfgwRefl (t / 2) η t = η 0 := by
        change η (2 * (t / 2) - t) = η 0
        congr 1
        ring
      rw [h₀, h₁, mul_comm]

end EinsteinFull.External.DFGW
