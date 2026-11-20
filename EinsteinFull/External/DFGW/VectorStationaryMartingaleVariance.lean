import EinsteinFull.External.DFGW.StationaryMartingaleVariance
import EinsteinFull.External.DFGW.MartingaleProjection
import EinsteinFull.External.DFGW.Trajectory
import EinsteinFull.External.DFGW.MartingaleCovariance

/-! # Variance of vector stationary-increment martingales

Every projection of a square-integrable vector martingale with stationary increments has
variance proportional to time.
-/

open MeasureTheory ProbabilityTheory EinsteinRelation
open scoped NNReal BigOperators

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {d : ℕ} {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- Every projection of a stationary-increment vector martingale has variance linear in time. -/
theorem integral_dot_stationary_martingale_sq (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (N : ℝ≥0 → C(ℝ, S) → Vec d) (hN : Martingale N Draft.dfgwPast P)
    (hN2 : ∀ t, MemLp (N t) 2 P)
    (hstat : ∀ s t, (fun η => N (s + t) η - N s η) =ᵐ[P]
      fun η => N t (Draft.dfgwShift s η)) (e : Vec d) (t : ℝ≥0) :
    (∫ η, dot e (N t η) ^ 2 ∂P) = (t : ℝ) * ∫ η, dot e (N 1 η) ^ 2 ∂P := by
  let : IsProbabilityMeasure P := hP.probability
  let L : Vec d →L[ℝ] ℝ := ∑ i : Fin d, (e i) • ContinuousLinearMap.proj i
  have hL (v : Vec d) : L v = dot e v := by
    simp only [L, sum_apply, smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul, dot]
  let B : ℝ≥0 → C(ℝ, S) → ℝ := fun t η => dot e (N t η)
  have hB2 (u : ℝ≥0) : MemLp (B u) 2 P := by
    simpa only [Function.comp_apply, hL, B] using (hN2 u).continuousLinearMap_comp L
  have hB : Martingale B Draft.dfgwPast P := by
    simpa only [hL, B] using martingale_continuousLinearMap hN L
  have hzero : N 0 =ᵐ[P] 0 := by
    have hshift (η : C(ℝ, S)) : Draft.dfgwShift 0 η = η := by
      ext u
      simp [Draft.dfgwShift]
    filter_upwards [hstat 0 0] with η hη
    simp only [zero_add, NNReal.coe_zero, hshift, Pi.zero_apply] at hη ⊢
    have hη' : N 0 η - N 0 η = N 0 η := hη
    simpa only [sub_self] using hη'.symm
  have hBzero : B 0 =ᵐ[P] 0 := by
    filter_upwards [hzero] with η hη
    change dot e (N 0 η) = 0
    rw [hη]
    simp [dot]
  have hθ (s : ℝ≥0) : MeasurePreserving (Draft.dfgwShift (S := S) s) P P :=
    ⟨measurable_shift s, hP.stationary s⟩
  have hBstat (s u : ℝ≥0) : (fun η => B (s + u) η - B s η) =ᵐ[P]
      fun η => B u (Draft.dfgwShift s η) - B 0 (Draft.dfgwShift s η) := by
    have hz := (hθ s).quasiMeasurePreserving.ae hBzero
    filter_upwards [hstat s u, hz] with η hs h0
    have hs' := congrArg L hs
    change L (N (s + u) η - N s η) = L (N u (Draft.dfgwShift s η)) at hs'
    rw [map_sub, hL, hL, hL] at hs'
    simp only [Pi.zero_apply] at h0
    change dot e (N (s + u) η) - dot e (N s η) =
      dot e (N u (Draft.dfgwShift s η)) - B 0 (Draft.dfgwShift s η)
    rw [h0, sub_zero]
    exact hs'
  have h := integral_stationary_martingale_increment_sq_eq_mul hB hB2 hθ hBstat t
  have he (u : ℝ≥0) : (∫ η, (B u η - B 0 η) ^ 2 ∂P) = ∫ η, B u η ^ 2 ∂P := by
    apply integral_congr_ae
    filter_upwards [hBzero] with η hη
    simp only [Pi.zero_apply] at hη
    rw [hη, sub_zero]
  rw [he t, he 1] at h
  exact h

end EinsteinFull.External.DFGW
