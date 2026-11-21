import EinsteinFull.External.DFGW.KipnisVaradhan
import EinsteinFull.External.DFGW.VelocityResolventEnergy
import EinsteinFull.External.DFGW.TimeIntegralCongruence

/-! # Martingale approximation of projected forward velocity

Every scalar projection of the forward velocity satisfies the square-integrable
stationary-increment martingale approximation.
-/

open MeasureTheory ProbabilityTheory Filter EinsteinRelation
open scoped NNReal Topology

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {d : ℕ} {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}
variable {X : ℝ → ℝ → C(ℝ, S) → Vec d} {Y : C(ℝ, S) → Path d}

/-- Each projected forward velocity has a stationary-increment martingale approximation whose
mean-square remainder is sublinear in time. -/
theorem exists_projected_velocity_martingale_approximation
    (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (hcoord : Draft.dfgwCoordSigma (S := S) Set.univ =
      Draft.dfgwTrajectoryMeasurableSpace (S := S))
    (hX : Draft.IsDFGWTrajectoryFamily P X Y) (φ : S → Vec d) (hφ : MemLp φ 2 μ)
    (hlim : Tendsto (fun δ : ℝ =>
      ∫ η, ‖δ⁻¹ • (P[X 0 δ | Draft.dfgwCoordSigma (Set.Iic 0)]) η - φ (η 0)‖ ∂P)
      (𝓝[>] 0) (𝓝 0))
    (hL2 : ∀ t, MemLp (compensated X φ t) 2 P)
    (hM : Martingale (compensated X φ) Draft.dfgwPast P) (e : Vec d) :
    ∃ M : ℝ≥0 → C(ℝ, S) → ℝ,
      Martingale M Draft.dfgwPast P ∧
      (∀ t, MemLp (M t) 2 P) ∧
      (∀ s t, (fun η => M (s + t) η - M s η) =ᵐ[P]
        fun η => M t (Draft.dfgwShift s η)) ∧
      (∀ t, (∫ η, (M t η) ^ 2 ∂P) = (t : ℝ) * (2 *
        ∫ u in Set.Ioi (0 : ℝ), ∫ x, dot e (φ x) *
          ∫ y, dot e (φ y) ∂T u.toNNReal x ∂μ)) ∧
      Tendsto (fun t : ℝ≥0 => (t : ℝ)⁻¹ *
        ∫ η, ((∫ u in (0 : ℝ)..t, dot e (φ (η u))) - M t η) ^ 2 ∂P) atTop (𝓝 0) := by
  have hg : MemLp (fun x => dot e (φ x)) 2 μ := by
    unfold dot
    apply memLp_finsetSum
    intro i hi
    exact (hφ.eval i).const_mul (e i)
  let g : Lp ℝ 2 μ := hg.toLp (fun x => dot e (φ x))
  have hint := integrableOn_projected_velocity_autocorrelation hP hX φ hφ hlim hL2 hM e hg
  obtain ⟨M, hmart, hmem, hstationary, hvar, hrem⟩ :=
    exists_martingale_approximation hP hcoord g hint
  refine ⟨M, hmart, hmem, hstationary, ?_, ?_⟩
  · intro t
    rw [hvar t]
    congr 2
    apply integral_congr_ae
    filter_upwards with u
    exact (integral_mul_kernel_eq_inner hP u.toNNReal _ _ hg hg).symm
  · have heq (t : ℝ≥0) : (∫ η, ((∫ u in (0 : ℝ)..t, g (η u)) - M t η) ^ 2 ∂P) =
        ∫ η, ((∫ u in (0 : ℝ)..t, dot e (φ (η u))) - M t η) ^ 2 ∂P := by
      have ha := ae_time_integral_congr hP (MemLp.coeFn_toLp hg) t.coe_nonneg
      apply integral_congr_ae
      filter_upwards [ha] with η hη
      rw [hη]
    simpa only [heq] using hrem

end EinsteinFull.External.DFGW
