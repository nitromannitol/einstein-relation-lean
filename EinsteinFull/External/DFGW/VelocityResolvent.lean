import EinsteinFull.External.DFGW.FullGeneratorEnergy

/-! # Resolvent bound for the mean velocity

The generator-energy inequality gives a uniform bound for the velocity resolvent pairing.
-/

open MeasureTheory ProbabilityTheory Filter EinsteinRelation
open scoped NNReal Topology

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {d : ℕ} {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}
variable {X : ℝ → ℝ → C(ℝ, S) → Vec d} {Y : C(ℝ, S) → Path d}

/-- The mean-velocity resolvent pairing is uniformly bounded by martingale variance. -/
theorem inner_velocity_transitionResolvent_le
    (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (hX : Draft.IsDFGWTrajectoryFamily P X Y) (φ : S → Vec d) (hφ : MemLp φ 2 μ)
    (hlim : Tendsto (fun δ : ℝ =>
      ∫ η, ‖δ⁻¹ • (P[X 0 δ | Draft.dfgwCoordSigma (Set.Iic 0)]) η - φ (η 0)‖ ∂P)
      (𝓝[>] 0) (𝓝 0))
    (hL2 : ∀ t, MemLp (compensated X φ t) 2 P)
    (hM : Martingale (compensated X φ) Draft.dfgwPast P) (i : Fin d)
    (lam : MarkovProcess.Semigroup.PositiveShift) :
    inner ℝ ((hφ.eval i).toLp (fun x => φ x i))
        (transitionResolvent hP lam ((hφ.eval i).toLp (fun x => φ x i))) ≤
      ∫ η, (compensated X φ 1 η i) ^ 2 ∂P := by
  apply inner_transitionResolvent_le_of_energy_bound hP
  · exact integral_nonneg fun _ => sq_nonneg _
  · intro F
    exact inner_velocity_sq_le_full_generator_energy hP hX φ hφ hlim hL2 hM i F

end EinsteinFull.External.DFGW
