import Ch5NashStatements.LocalHarnack
import EllipticRegularity.DeGiorgi.Assembly.EssContinuous

/-!
# Pointwise Harnack bounds for stationary parabolic solutions

The parabolic Harnack inequality gives pointwise spatial comparison for a
continuous solution that is constant in time, in every positive dimension.
-/

open MeasureTheory Set
open scoped ENNReal

namespace EinsteinFull.Regeneration

/-- Continuous stationary solutions inherit pointwise comparison from parabolic Harnack. -/
theorem stationary_pointwise_harnack (d : ℕ) (hd : 0 < d) (Λ : ℝ) (hΛ : 1 ≤ Λ) :
    ∃ H : ℝ, 2 ≤ H ∧ ∀ (a : PDE.ParCoeffField d) (τ θ : ℝ), 0 < θ →
      ∀ z z' : PDE.Vec d, PDE.euclideanSqDist z z' ≤ θ / 4 →
      PDE.IsParabolicCoeff 1 Λ a
        (PDE.euclideanBall ((1 / 2 : ℝ) • (z + z')) (Real.sqrt (2 * θ)))
        (Ioc (τ - 3 * θ / 2) (τ + 5 * θ / 4)) →
      ∀ u : PDE.ParH1Function
        (PDE.euclideanBall ((1 / 2 : ℝ) • (z + z')) (Real.sqrt (2 * θ)))
        (Ioc (τ - 3 * θ / 2) (τ + 5 * θ / 4)),
      PDE.IsParabolicWeakSolution a _ _ u →
      ∀ v : PDE.Vec d → ℝ, Continuous v → (∀ x, 0 ≤ v x) →
        (∀ x t, u.toFun (x, t) = v x) → v z ≤ H * v z' := by
  obtain ⟨H, hH, hharnack⟩ := PDE.parabLocalHarnack d hd Λ hΛ
  refine ⟨H, hH, ?_⟩
  intro a τ θ hθ z z' hdist hcoeff u hsol v hv hv0 hstatic
  have hnonneg : ∀ᵐ w ∂(volume.restrict
      (PDE.euclideanBall ((1 / 2 : ℝ) • (z + z')) (Real.sqrt (2 * θ)) ×ˢ
        Ioc (τ - 3 * θ / 2) (τ + 5 * θ / 4))), 0 ≤ u.toFun w := by
    exact Filter.Eventually.of_forall fun w => by rw [hstatic]; exact hv0 w.1
  have hh := hharnack a τ θ hθ z z' hdist hcoeff u hsol hnonneg
  simp_rw [hstatic] at hh
  have hr : 0 < Real.sqrt θ / 4 := div_pos (Real.sqrt_pos.2 hθ) (by norm_num)
  have hcont : Continuous (fun x => ENNReal.ofReal (v x)) :=
    ENNReal.continuous_ofReal.comp hv
  have hleft := PDE.DGNMAssembly.le_essSup_of_continuousOn
    (PDE.isOpen_euclideanBall z (Real.sqrt θ / 4)) hcont.continuousOn
    (PDE.center_mem_euclideanBall z hr)
  have hright := PDE.DGNMAssembly.essInf_le_of_continuousOn
    (PDE.isOpen_euclideanBall z' (Real.sqrt θ / 4)) hcont.continuousOn
    (PDE.center_mem_euclideanBall z' hr)
  have hcomp : ENNReal.ofReal (v z) ≤ ENNReal.ofReal (H * v z') := by
    calc
      _ ≤ _ := hleft
      _ ≤ _ := hh
      _ ≤ ENNReal.ofReal H * ENNReal.ofReal (v z') := by simpa only [mul_comm] using mul_le_mul_left hright (ENNReal.ofReal H)
      _ = _ := (ENNReal.ofReal_mul (by linarith : 0 ≤ H)).symm
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (by linarith) (hv0 z'))).mp hcomp

end EinsteinFull.Regeneration
