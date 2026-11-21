import EinsteinFull.External.DFGW.VelocityMartingaleApproximation
import EinsteinFull.External.DFGW.TimeIntegrability
import EinsteinFull.External.DFGW.MartingaleProjection

/-! # Martingale approximation of projected increments

Adding the compensated increment martingale to the velocity martingale gives a stationary
increment martingale approximating each projection of the original increment family.
-/

open MeasureTheory ProbabilityTheory Filter EinsteinRelation
open scoped NNReal Topology BigOperators

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {d : ℕ} {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}
variable {X : ℝ → ℝ → C(ℝ, S) → Vec d} {Y : C(ℝ, S) → Path d}

/-- Every scalar projection of the increment family has a stationary-increment `L²` martingale
approximation with a sublinear mean-square remainder. -/
theorem exists_projected_increment_martingale_approximation
    (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (hcoord : Draft.dfgwCoordSigma (S := S) Set.univ =
      Draft.dfgwTrajectoryMeasurableSpace (S := S))
    (hX : Draft.IsDFGWTrajectoryFamily P X Y) (φ : S → Vec d) (hφ : MemLp φ 2 μ)
    (hlim : Tendsto (fun δ : ℝ =>
      ∫ η, ‖δ⁻¹ • (P[X 0 δ | Draft.dfgwCoordSigma (Set.Iic 0)]) η - φ (η 0)‖ ∂P)
      (𝓝[>] 0) (𝓝 0))
    (hL2 : ∀ t, MemLp (compensated X φ t) 2 P)
    (hM : Martingale (compensated X φ) Draft.dfgwPast P) (e : Vec d) :
    ∃ N : ℝ≥0 → C(ℝ, S) → ℝ,
      Martingale N Draft.dfgwPast P ∧
      (∀ t, MemLp (N t) 2 P) ∧
      (∀ s t, (fun η => N (s + t) η - N s η) =ᵐ[P]
        fun η => N t (Draft.dfgwShift s η)) ∧
      Tendsto (fun t : ℝ≥0 => (t : ℝ)⁻¹ *
        ∫ η, (dot e (X 0 t η) - N t η) ^ 2 ∂P) atTop (𝓝 0) := by
  let : IsProbabilityMeasure P := hP.probability
  let : IsProbabilityMeasure μ := hP.invariant_probability
  let L : Vec d →L[ℝ] ℝ := ∑ i : Fin d, (e i) • ContinuousLinearMap.proj i
  have hL (v : Vec d) : L v = dot e v := by
    simp only [L, sum_apply, smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul, dot]
  obtain ⟨M, hMv, hMv2, hMstat, _, hrem⟩ :=
    exists_projected_velocity_martingale_approximation hP hcoord hX φ hφ hlim hL2 hM e
  let A : ℝ≥0 → C(ℝ, S) → ℝ := fun t η => L (compensated X φ t η)
  let N : ℝ≥0 → C(ℝ, S) → ℝ := fun t η => A t η + M t η
  have hA : Martingale A Draft.dfgwPast P := martingale_continuousLinearMap hM L
  have hN : Martingale N Draft.dfgwPast P := hA.add hMv
  have hN2 (t : ℝ≥0) : MemLp (N t) 2 P := ((hL2 t).continuousLinearMap_comp L).add (hMv2 t)
  have hAstat (s t : ℝ≥0) : (fun η => A (s + t) η - A s η) =ᵐ[P]
      fun η => A t (Draft.dfgwShift s η) := by
    have he := compensated_increment_eq_shift_of_integrable hP hX φ (hφ.integrable one_le_two)
      (a := (s : ℝ)) (b := ((s + t : ℝ≥0) : ℝ)) s.coe_nonneg
      (by exact_mod_cast (show s ≤ s + t by simp))
    filter_upwards [he] with η hη
    simp only [NNReal.coe_add, add_sub_cancel_left] at hη
    change compensated X φ (s + t) η - compensated X φ s η =
      compensated X φ t (Draft.dfgwShift s η) at hη
    change L (compensated X φ (s + t) η) - L (compensated X φ s η) = _
    rw [← map_sub, hη]
  have hstat (s t : ℝ≥0) : (fun η => N (s + t) η - N s η) =ᵐ[P]
      fun η => N t (Draft.dfgwShift s η) := by
    filter_upwards [hAstat s t, hMstat s t] with η ha hm
    dsimp only [N]
    linarith
  have heq (t : ℝ≥0) : (∫ η, (dot e (X 0 t η) - N t η) ^ 2 ∂P) =
      ∫ η, ((∫ u in (0 : ℝ)..t, dot e (φ (η u))) - M t η) ^ 2 ∂P := by
    have hi := ae_intervalIntegrable_observable hP φ (hφ.integrable one_le_two) t.coe_nonneg
    apply integral_congr_ae
    filter_upwards [hi] with η hη
    have hproj := L.intervalIntegral_comp_comm hη
    have hproj' : dot e (∫ u in (0 : ℝ)..t, φ (η u)) =
        ∫ u in (0 : ℝ)..t, dot e (φ (η u)) := by
      simpa only [hL] using hproj.symm
    have hAeq : A t η = dot e (X 0 t η) - dot e (∫ u in (0 : ℝ)..t, φ (η u)) := by
      change L (X 0 t η - ∫ u in (0 : ℝ)..t, φ (η u)) = _
      rw [map_sub, hL, hL]
    dsimp only [N]
    rw [hAeq, hproj']
    ring
  exact ⟨N, hN, hN2, hstat, by simpa only [heq] using hrem⟩

end EinsteinFull.External.DFGW
