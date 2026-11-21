import EinsteinFull.External.DFGW.FiniteTimeEnergy
import EinsteinFull.External.DFGW.VelocityPairing
import Mathlib.Analysis.SpecificLimits.Basic

/-! # Mean forward velocity and semigroup energy

Passing the finite-time estimate to zero bounds the mean forward velocity pairing by the
limiting semigroup energy.
-/

open MeasureTheory ProbabilityTheory Filter EinsteinRelation
open scoped NNReal Topology

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {d : ℕ} {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}
variable {X : ℝ → ℝ → C(ℝ, S) → Vec d} {Y : C(ℝ, S) → Path d}

/-- The velocity pairing is bounded by the limiting finite-time semigroup energy. -/
theorem velocity_pairing_sq_le_energy (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (hX : Draft.IsDFGWTrajectoryFamily P X Y) (φ : S → Vec d) (hφ : MemLp φ 2 μ)
    (hlim : Tendsto (fun δ : ℝ =>
      ∫ η, ‖δ⁻¹ • (P[X 0 δ | Draft.dfgwCoordSigma (Set.Iic 0)]) η - φ (η 0)‖ ∂P)
      (𝓝[>] 0) (𝓝 0))
    (hL2 : ∀ t, MemLp (compensated X φ t) 2 P)
    (hM : Martingale (compensated X φ) Draft.dfgwPast P) (i : Fin d)
    (f : S → ℝ) (hf : Measurable f) (hfb : ∃ C, ∀ x, |f x| ≤ C)
    (hfL2 : MemLp f 2 μ) (energy : ℝ)
    (henergy : Tendsto (fun n : ℕ => (n : ℝ) * (‖hfL2.toLp f‖ ^ 2 -
      inner ℝ (hfL2.toLp f) (transitionOperator hP ((n : ℝ≥0)⁻¹) (hfL2.toLp f))))
      atTop (𝓝 energy)) :
    (∫ x, φ x i * f x ∂μ) ^ 2 ≤
      (∫ η, (compensated X φ 1 η i) ^ 2 ∂P) * energy := by
  have hseq : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨tendsto_inv_atTop_nhds_zero_nat, ?_⟩
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    change 0 < (n : ℝ)⁻¹
    exact inv_pos.mpr (by exact_mod_cast hn)
  have hp := (tendsto_increment_observable_difference hP hX φ hφ hlim i f hf hfb).comp hseq
  have hp' : Tendsto (fun n : ℕ => (n : ℝ) * ∫ η, X 0 ((n : ℝ)⁻¹) η i *
      (f (η ((n : ℝ)⁻¹)) - f (η 0)) ∂P) atTop
      (𝓝 (-2 * ∫ x, φ x i * f x ∂μ)) := by
    change Tendsto (fun n : ℕ => ((n : ℝ)⁻¹)⁻¹ * ∫ η, X 0 ((n : ℝ)⁻¹) η i *
      (f (η ((n : ℝ)⁻¹)) - f (η 0)) ∂P) atTop _ at hp
    simpa only [inv_inv] using hp
  have hcoef : Tendsto (fun n : ℕ => 4 * ((∫ η, (compensated X φ 1 η i) ^ 2 ∂P) +
      (n : ℝ)⁻¹ * ∫ x, φ x i ^ 2 ∂μ)) atTop
      (𝓝 (4 * ∫ η, (compensated X φ 1 η i) ^ 2 ∂P)) := by
    have h := (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).mul_const
      (∫ x, φ x i ^ 2 ∂μ)
    simpa only [zero_mul, add_zero] using (tendsto_const_nhds.add h).const_mul 4
  have hb : ∀ᶠ n : ℕ in atTop,
      ((n : ℝ) * ∫ η, X 0 ((n : ℝ)⁻¹) η i *
        (f (η ((n : ℝ)⁻¹)) - f (η 0)) ∂P) ^ 2 ≤
      4 * ((∫ η, (compensated X φ 1 η i) ^ 2 ∂P) +
        (n : ℝ)⁻¹ * ∫ x, φ x i ^ 2 ∂μ) *
      ((n : ℝ) * (‖hfL2.toLp f‖ ^ 2 - inner ℝ (hfL2.toLp f)
        (transitionOperator hP ((n : ℝ≥0)⁻¹) (hfL2.toLp f)))) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    exact normalized_increment_pairing_sq_le hP hX φ hφ hL2 hM i f hf hfb hfL2 n hn
  have h := le_of_tendsto_of_tendsto (hp'.pow 2) (hcoef.mul henergy) hb
  nlinarith

end EinsteinFull.External.DFGW
