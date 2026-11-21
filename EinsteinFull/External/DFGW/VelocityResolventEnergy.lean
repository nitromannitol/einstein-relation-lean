import EinsteinFull.External.DFGW.ResolventEnergyCauchy
import EinsteinFull.External.DFGW.ResolventGeneratorLimit
import EinsteinFull.External.DFGW.ProjectedVelocityCorrelation

/-! # Energy convergence for projected velocity resolvents

The forward velocity has resolvent approximations that are Cauchy in generator energy.
-/

open MeasureTheory ProbabilityTheory Filter EinsteinRelation
open scoped NNReal Topology

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {d : ℕ} {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}
variable {X : ℝ → ℝ → C(ℝ, S) → Vec d} {Y : C(ℝ, S) → Path d}

/-- Resolvents of each projected mean velocity are Cauchy in generator energy. -/
theorem projected_velocity_resolvent_energy_cauchy
    (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (hX : Draft.IsDFGWTrajectoryFamily P X Y) (φ : S → Vec d) (hφ : MemLp φ 2 μ)
    (hlim : Tendsto (fun δ : ℝ =>
      ∫ η, ‖δ⁻¹ • (P[X 0 δ | Draft.dfgwCoordSigma (Set.Iic 0)]) η - φ (η 0)‖ ∂P)
      (𝓝[>] 0) (𝓝 0))
    (hL2 : ∀ t, MemLp (compensated X φ t) 2 P)
    (hM : Martingale (compensated X φ) Draft.dfgwPast P) (e : Vec d)
    (hg : MemLp (fun x => dot e (φ x)) 2 μ) :
    ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ m ≥ N,
      let F := transitionResolventDomain hP (reciprocalShift n) (hg.toLp (fun x => dot e (φ x))) -
        transitionResolventDomain hP (reciprocalShift m) (hg.toLp (fun x => dot e (φ x)));
      -inner ℝ (F : Lp ℝ 2 μ) ((transitionSemigroup hP).generator F) < ε := by
  apply resolvent_energy_cauchy hP
  exact integrableOn_projected_velocity_autocorrelation hP hX φ hφ hlim hL2 hM e hg

/-- The generators of projected-velocity resolvents converge to the negative velocity. -/
theorem tendsto_generator_projected_velocity_resolvent
    (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (hX : Draft.IsDFGWTrajectoryFamily P X Y) (φ : S → Vec d) (hφ : MemLp φ 2 μ)
    (hlim : Tendsto (fun δ : ℝ =>
      ∫ η, ‖δ⁻¹ • (P[X 0 δ | Draft.dfgwCoordSigma (Set.Iic 0)]) η - φ (η 0)‖ ∂P)
      (𝓝[>] 0) (𝓝 0))
    (hL2 : ∀ t, MemLp (compensated X φ t) 2 P)
    (hM : Martingale (compensated X φ) Draft.dfgwPast P) (e : Vec d)
    (hg : MemLp (fun x => dot e (φ x)) 2 μ) :
    Tendsto (fun n : ℕ => (transitionSemigroup hP).generator
      (transitionResolventDomain hP (reciprocalShift n) (hg.toLp (fun x => dot e (φ x)))))
      atTop (𝓝 (-(hg.toLp (fun x => dot e (φ x))))) := by
  apply tendsto_generator_reciprocalShift_resolvent hP
  exact integrableOn_projected_velocity_autocorrelation hP hX φ hφ hlim hL2 hM e hg

end EinsteinFull.External.DFGW
