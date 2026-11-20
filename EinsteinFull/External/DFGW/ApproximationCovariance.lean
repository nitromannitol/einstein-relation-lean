import EinsteinFull.External.DFGW.VectorRemainderProjection
import EinsteinFull.External.DFGW.StationaryMartingaleVariance
import EinsteinFull.External.DFGW.VarianceApproximation
import EinsteinFull.External.DFGW.DiffusionVarianceLimit

/-! # Covariance of the vector martingale approximation

A stationary-increment vector martingale approximating the original increments in mean square
has the same diffusion quadratic form as the increments.
-/

open MeasureTheory ProbabilityTheory Filter EinsteinRelation
open scoped NNReal Topology BigOperators

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {d : ℕ} {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}
variable {X : ℝ → ℝ → C(ℝ, S) → Vec d} {Y : C(ℝ, S) → Path d}

/-- The variance rate of a projected vector martingale approximation equals the normalized
variance limit of the original increment. -/
theorem projected_martingale_variance_eq_limit
    (hP : Draft.IsDFGWTrajectoryProcess P μ T) (φ : S → Vec d) (hφ : MemLp φ 2 μ)
    (hL2 : ∀ t, MemLp (compensated X φ t) 2 P)
    (N : ℝ≥0 → C(ℝ, S) → Vec d) (hN : Martingale N Draft.dfgwPast P)
    (hN2 : ∀ t, MemLp (N t) 2 P)
    (hstat : ∀ s t, (fun η => N (s + t) η - N s η) =ᵐ[P]
      fun η => N t (Draft.dfgwShift s η))
    (hcoord : ∀ i : Fin d, Tendsto (fun t : ℝ≥0 => (t : ℝ)⁻¹ *
      ∫ η, (X 0 t η i - N t η i) ^ 2 ∂P) atTop (𝓝 0))
    (e : Vec d) (q : ℝ)
    (hXvar : Tendsto (fun t : ℝ => t⁻¹ * ∫ η, dot e (X 0 t η) ^ 2 ∂P) atTop (𝓝 q)) :
    (∫ η, dot e (N 1 η) ^ 2 ∂P) = q := by
  let : IsProbabilityMeasure P := hP.probability
  let L : Vec d →L[ℝ] ℝ := ∑ i : Fin d, (e i) • ContinuousLinearMap.proj i
  have hL (v : Vec d) : L v = dot e v := by
    simp only [L, sum_apply, smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul, dot]
  let A : ℝ≥0 → C(ℝ, S) → ℝ := fun t η => dot e (X 0 t η)
  let B : ℝ≥0 → C(ℝ, S) → ℝ := fun t η => dot e (N t η)
  have hA2 (t : ℝ≥0) : MemLp (A t) 2 P := increment_dot_memLp hP φ hφ t (hL2 t) e
  have hB2 (t : ℝ≥0) : MemLp (B t) 2 P := by
    simpa only [Function.comp_apply, hL, B] using (hN2 t).continuousLinearMap_comp L
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
  have hBstat (s t : ℝ≥0) : (fun η => B (s + t) η - B s η) =ᵐ[P]
      fun η => B t (Draft.dfgwShift s η) - B 0 (Draft.dfgwShift s η) := by
    have hz := (hθ s).quasiMeasurePreserving.ae hBzero
    filter_upwards [hstat s t, hz] with η hs h0
    have hs' := congrArg L hs
    change L (N (s + t) η - N s η) = L (N t (Draft.dfgwShift s η)) at hs'
    rw [map_sub, hL, hL, hL] at hs'
    simp only [Pi.zero_apply] at h0
    change dot e (N (s + t) η) - dot e (N s η) =
      dot e (N t (Draft.dfgwShift s η)) - B 0 (Draft.dfgwShift s η)
    rw [h0, sub_zero]
    exact hs'
  let c : ℝ := ∫ η, B 1 η ^ 2 ∂P
  have hc : 0 ≤ c := integral_nonneg fun _ => sq_nonneg _
  have hBvar (t : ℝ≥0) : (∫ η, B t η ^ 2 ∂P) = (t : ℝ) * c := by
    have h := integral_stationary_martingale_increment_sq_eq_mul hB hB2 hθ hBstat t
    have he (u : ℝ≥0) : (∫ η, (B u η - B 0 η) ^ 2 ∂P) = ∫ η, B u η ^ 2 ∂P := by
      apply integral_congr_ae
      filter_upwards [hBzero] with η hη
      simp only [Pi.zero_apply] at hη
      rw [hη, sub_zero]
    rw [he t, he 1] at h
    exact h
  have hrem := tendsto_projected_remainder_of_coordinates hP φ hφ hL2 N hN2 hcoord e
  have hlimit := tendsto_variance_of_sublinear_approximation A B hA2 hB2 c hc hBvar hrem
  have hcoerce : Tendsto (fun t : ℝ≥0 => (t : ℝ)) atTop atTop :=
    NNReal.tendsto_coe_atTop.mpr tendsto_id
  have hlimitX := hXvar.comp hcoerce
  change Tendsto (fun t : ℝ≥0 => (t : ℝ)⁻¹ * ∫ η, A t η ^ 2 ∂P) atTop (𝓝 q) at hlimitX
  exact tendsto_nhds_unique hlimit hlimitX

end EinsteinFull.External.DFGW
