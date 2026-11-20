import EinsteinFull.Regeneration.TrialEndpointMoment

/-!
# Trial-moment recurrence

A one-step contraction of the actual weighted trial-start moments gives
their geometric bound and hence the first-regeneration endpoint moment.
-/

open MeasureTheory EinsteinRelation EinsteinRelation.Regeneration
open scoped NNReal ENNReal

namespace EinsteinFull.Regeneration

/-- A one-step weighted trial contraction yields the endpoint moment. -/
theorem first_regeneration_endpoint_moment_of_trial_contraction {d : ℕ}
    (μ : Measure (FieldPair d × CoupledSample d)) (Δ : ℝ≥0) (hΔ : 0 < Δ)
    (lam R a : ℝ) (i : Fin d) (B q : ℝ) (hB : 0 ≤ B) (hq : 0 ≤ q) (hq1 : q < 1)
    (hfinite : ∀ᵐ z ∂μ, firstRegenerationTime Δ lam R z.2 i ≠ ⊤)
    (hfirst :
      (∫⁻ z, {z : FieldPair d × CoupledSample d |
        trialStartSequence Δ lam R z.2 i 0 ≠ ⊤}.indicator
        (fun z => ENNReal.ofReal (Real.exp (a *
          (lam * (z.2.1 (trialStartSequence Δ lam R z.2 i 0).toNNReal i - z.2.1 0 i))))) z ∂μ)
        ≤ ENNReal.ofReal B)
    (hstep : ∀ n : ℕ,
      let M := fun j : ℕ => ∫⁻ z, {z : FieldPair d × CoupledSample d |
        trialStartSequence Δ lam R z.2 i j ≠ ⊤}.indicator
        (fun z => ENNReal.ofReal (Real.exp (a *
          (lam * (z.2.1 (trialStartSequence Δ lam R z.2 i j).toNNReal i - z.2.1 0 i))))) z ∂μ
      M (n + 1) ≤ ENNReal.ofReal q * M n) :
    Integrable (fun z : FieldPair d × CoupledSample d => Real.exp (a *
      (lam * (z.2.1 (firstRegenerationTime Δ lam R z.2 i).toNNReal i - z.2.1 0 i)))) μ ∧
    (∫ z : FieldPair d × CoupledSample d, Real.exp (a *
      (lam * (z.2.1 (firstRegenerationTime Δ lam R z.2 i).toNNReal i - z.2.1 0 i))) ∂μ)
      ≤ B / (1 - q) := by
  apply first_regeneration_endpoint_moment_of_trial_bounds μ Δ hΔ lam R a i B q hB hq hq1 hfinite
  intro n
  induction n with
  | zero => simpa using hfirst
  | succ n ih =>
      calc
        _ ≤ ENNReal.ofReal q * ENNReal.ofReal (B * q ^ n) :=
          (hstep n).trans (by simpa only [mul_comm] using mul_le_mul_left ih (ENNReal.ofReal q))
        _ = ENNReal.ofReal (B * q ^ (n + 1)) := by
          rw [← ENNReal.ofReal_mul hq]
          congr 1
          ring

end EinsteinFull.Regeneration
