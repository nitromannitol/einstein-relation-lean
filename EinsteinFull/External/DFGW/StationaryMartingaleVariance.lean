import EinsteinFull.External.DFGW.AdditiveVariance

/-! # Variance of stationary-increment martingales

The variance of a square-integrable martingale with stationary increments grows linearly in
time.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace EinsteinFull.External.DFGW

variable {Ω : Type*} {m : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
variable {ℱ : Filtration ℝ≥0 m} {M : ℝ≥0 → Ω → ℝ} {θ : ℝ≥0 → Ω → Ω}

/-- The initial increment of a square-integrable stationary-increment martingale has variance
linear in time. -/
theorem integral_stationary_martingale_increment_sq_eq_mul
    (hM : Martingale M ℱ P) (hL2 : ∀ t, MemLp (M t) 2 P)
    (hθ : ∀ s, MeasurePreserving (θ s) P P)
    (hstat : ∀ s t, (fun ω => M (s + t) ω - M s ω) =ᵐ[P]
      fun ω => M t (θ s ω) - M 0 (θ s ω)) (t : ℝ≥0) :
    (∫ ω, (M t ω - M 0 ω) ^ 2 ∂P) =
      (t : ℝ) * ∫ ω, (M 1 ω - M 0 ω) ^ 2 ∂P := by
  let V : ℝ≥0 → ℝ := fun t => ∫ ω, (M t ω - M 0 ω) ^ 2 ∂P
  have hadd (s t : ℝ≥0) : V (s + t) = V s + V t := by
    have h1 := integral_martingale_increment_sq hM (show (0 : ℝ≥0) ≤ s + t by simp)
      (hL2 0) (hL2 (s + t))
    have h2 := integral_martingale_increment_sq hM (show (0 : ℝ≥0) ≤ s by simp)
      (hL2 0) (hL2 s)
    have h3 := integral_martingale_increment_sq hM (show s ≤ s + t by simp)
      (hL2 s) (hL2 (s + t))
    let G : Ω → ℝ := fun ω => (M t ω - M 0 ω) ^ 2
    have hG : Integrable G P := ((hL2 t).sub (hL2 0)).integrable_sq
    have hm : AEStronglyMeasurable G (P.map (θ s)) := by
      rw [(hθ s).map_eq]
      exact hG.aestronglyMeasurable
    have hstat' : (∫ ω, (M (s + t) ω - M s ω) ^ 2 ∂P) = V t := by
      calc
        _ = ∫ ω, G (θ s ω) ∂P := by
          apply integral_congr_ae
          filter_upwards [hstat s t] with ω hω
          exact congrArg (fun x : ℝ => x ^ 2) hω
        _ = ∫ ω, G ω ∂P.map (θ s) := (integral_map (hθ s).measurable.aemeasurable hm).symm
        _ = _ := by rw [(hθ s).map_eq]
    change V (s + t) = V s + V t
    dsimp only [V]
    linarith
  exact nonnegative_additive_eq_mul V hadd (fun t => integral_nonneg fun _ => sq_nonneg _) t

end EinsteinFull.External.DFGW
