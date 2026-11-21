import EinsteinFull.External.DFGW.ResolventVanishing
import EinsteinFull.External.DFGW.ProjectedVelocityCorrelation

/-! # Vanishing resolvents of the forward velocity

The mean forward velocity satisfies the normalized resolvent estimate needed for the
martingale approximation.
-/

open MeasureTheory ProbabilityTheory Filter EinsteinRelation
open scoped NNReal Topology

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {d : ℕ} {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}
variable {X : ℝ → ℝ → C(ℝ, S) → Vec d} {Y : C(ℝ, S) → Path d}

/-- The normalized resolvent norm vanishes for every projection of the mean forward velocity. -/
theorem tendsto_projected_velocity_resolvent_norm_sq
    (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (hX : Draft.IsDFGWTrajectoryFamily P X Y) (φ : S → Vec d) (hφ : MemLp φ 2 μ)
    (hlim : Tendsto (fun δ : ℝ =>
      ∫ η, ‖δ⁻¹ • (P[X 0 δ | Draft.dfgwCoordSigma (Set.Iic 0)]) η - φ (η 0)‖ ∂P)
      (𝓝[>] 0) (𝓝 0))
    (hL2 : ∀ t, MemLp (compensated X φ t) 2 P)
    (hM : Martingale (compensated X φ) Draft.dfgwPast P) (e : Vec d)
    (hg : MemLp (fun x => dot e (φ x)) 2 μ) :
    Tendsto (fun n : ℕ => (reciprocalShift n : ℝ) *
      ‖transitionResolvent hP (reciprocalShift n) (hg.toLp (fun x => dot e (φ x)))‖ ^ 2)
      atTop (𝓝 0) := by
  apply tendsto_reciprocalShift_mul_resolvent_norm_sq hP
  exact integrableOn_projected_velocity_autocorrelation hP hX φ hφ hlim hL2 hM e hg

end EinsteinFull.External.DFGW
