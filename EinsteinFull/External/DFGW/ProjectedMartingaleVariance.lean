import EinsteinFull.External.DFGW.VarianceAdditivity

/-! # Variance of projected stationary martingales

The second moment of any linear projection of the compensated martingale is additive in time.
-/

open MeasureTheory ProbabilityTheory EinsteinRelation
open scoped NNReal

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {d : ℕ} {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}
variable {X : ℝ → ℝ → C(ℝ, S) → Vec d} {Y : C(ℝ, S) → Path d}

/-- The second moment of a projected compensated martingale is additive in time. -/
theorem integral_projected_compensated_sq_add
    (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (hX : Draft.IsDFGWTrajectoryFamily P X Y) (φ : S → Vec d) (hφ : Integrable φ μ)
    (hL2 : ∀ t, MemLp (compensated X φ t) 2 P)
    (hM : Martingale (compensated X φ) Draft.dfgwPast P)
    (L : Vec d →L[ℝ] ℝ) (s t : ℝ≥0) :
    (∫ η, (L (compensated X φ (s + t) η)) ^ 2 ∂P) =
      (∫ η, (L (compensated X φ s η)) ^ 2 ∂P) +
        ∫ η, (L (compensated X φ t η)) ^ 2 ∂P := by
  let : IsProbabilityMeasure P := hP.probability
  have hMc : Martingale (fun t η => L (compensated X φ t η)) Draft.dfgwPast P :=
    martingale_continuousLinearMap hM L
  have hs := integral_martingale_increment_sq hMc (show s ≤ s + t by simp)
    ((hL2 s).continuousLinearMap_comp L) ((hL2 (s + t)).continuousLinearMap_comp L)
  let Z : C(ℝ, S) → Vec d := compensated X φ t
  have hZ : Integrable (fun η => (L (Z η)) ^ 2) P :=
    ((hL2 t).continuousLinearMap_comp L).integrable_sq
  have hm : AEStronglyMeasurable (fun η => (L (Z η)) ^ 2) (P.map (Draft.dfgwShift s)) := by
    rw [hP.stationary]
    exact hZ.aestronglyMeasurable
  have he := compensated_increment_eq_shift_of_integrable hP hX φ hφ
    (a := (s : ℝ)) (b := ((s + t : ℝ≥0) : ℝ)) s.coe_nonneg
    (by exact_mod_cast (show s ≤ s + t by simp))
  have hstat : (∫ η, (L (compensated X φ (s + t) η) - L (compensated X φ s η)) ^ 2 ∂P) =
      ∫ η, (L (compensated X φ t η)) ^ 2 ∂P := by
    calc
      _ = ∫ η, (L (Z (Draft.dfgwShift s η))) ^ 2 ∂P := by
        apply integral_congr_ae
        filter_upwards [he] with η hη
        simp only [NNReal.coe_add, add_sub_cancel_left] at hη
        change compensated X φ (s + t) η - compensated X φ s η =
          compensated X φ t (Draft.dfgwShift s η) at hη
        rw [← map_sub L, hη]
      _ = ∫ η, (L (Z η)) ^ 2 ∂P.map (Draft.dfgwShift s) :=
        (integral_map (measurable_shift _).aemeasurable hm).symm
      _ = _ := by rw [hP.stationary]
  rw [hstat] at hs
  linarith

end EinsteinFull.External.DFGW
