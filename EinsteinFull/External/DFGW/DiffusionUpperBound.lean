import EinsteinFull.External.DFGW.DiffusionVarianceLimit

/-! # Upper bound on the diffusion matrix

The integrated drift variance is nonnegative, so the limiting diffusion matrix is bounded
above by the martingale second-moment matrix in quadratic form.
-/

open MeasureTheory ProbabilityTheory Filter EinsteinRelation
open scoped NNReal Topology

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {d : ℕ} {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}
variable {X : ℝ → ℝ → C(ℝ, S) → Vec d} {Y : C(ℝ, S) → Path d}

/-- The limiting diffusion quadratic form is bounded above by the compensated-martingale
second-moment quadratic form. -/
theorem diffusion_quadratic_le_martingale_covariance
    (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (hX : Draft.IsDFGWTrajectoryFamily P X Y) (φ : S → Vec d) (hφ : MemLp φ 2 μ)
    (hL2 : ∀ t, MemLp (compensated X φ t) 2 P)
    (hM : Martingale (compensated X φ) Draft.dfgwPast P) (D : Mat d) (e : Vec d)
    (hlimit : Tendsto (fun t : ℝ => t⁻¹ * ∫ η : C(ℝ, S), dot e (X 0 t η) ^ 2 ∂P)
      atTop (𝓝 (dot e (D.mulVec e)))) :
    dot e (D.mulVec e) ≤ dot e ((secondMomentMatrix P (compensated X φ 1)).mulVec e) := by
  apply le_of_tendsto_of_tendsto hlimit (tendsto_const_nhds (x :=
    dot e ((secondMomentMatrix P (compensated X φ 1)).mulVec e)))
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  have hfinite := integral_dot_increment_sq_eq_martingale_sub_drift hP hX φ hφ hL2 hM t.toNNReal e
  rw [Real.coe_toNNReal _ ht.le] at hfinite
  have hnonneg : 0 ≤ ∫ η : C(ℝ, S), (∫ u in (0 : ℝ)..t, dot e (φ (η u))) ^ 2 ∂P :=
    integral_nonneg fun _ => sq_nonneg _
  have hbound : (∫ η : C(ℝ, S), dot e (X 0 t η) ^ 2 ∂P) ≤
      t * dot e ((secondMomentMatrix P (compensated X φ 1)).mulVec e) := by linarith
  calc
    _ ≤ t⁻¹ * (t * dot e ((secondMomentMatrix P (compensated X φ 1)).mulVec e)) :=
      mul_le_mul_of_nonneg_left hbound (inv_nonneg.mpr ht.le)
    _ = _ := by field_simp

end EinsteinFull.External.DFGW
