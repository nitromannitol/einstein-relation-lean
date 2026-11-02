import EinsteinFull.Calculus.C10LocalTimeStationaryAverage

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators
noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation EinsteinFull

theorem local_time_moment_of_stationary_square_energy
    {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (κ : Measure (Vec d)) [IsProbabilityMeasure κ]
    (p M C : ℝ) (hp : 2 ≤ p) (hM : 0 ≤ M) (hC : 0 ≤ C)
    (F : ℝ × FieldPair d → ℂ) (hF : Measurable F)
    (hbound : ∀ᵐ s ∂ν,
      MemLp (fun ω => F (s, ω)) (ENNReal.ofReal p) (reducedLaw Q) ∧
      (eLpNorm (fun ω => F (s, ω)) (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤ M)
    (V : FieldPair d → ℂ) (hV : AEStronglyMeasurable V (reducedLaw Q))
    (henergy : ∀ᵐ ω ∂reducedLaw Q,
      ‖V ω‖ ^ 2 ≤ C * (∫ s, ∫ y, ‖F (s, translate y ω)‖ ^ 2 ∂κ ∂ν)) :
    MemLp V (ENNReal.ofReal p) (reducedLaw Q) ∧
      (eLpNorm V (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤ Real.sqrt C * M := by
  let A := fun ω : FieldPair d => Real.sqrt
    (∫ s, ∫ y, ‖F (s, translate y ω)‖ ^ 2 ∂κ ∂ν)
  obtain ⟨hA, hAnorm⟩ :=
    local_time_stationary_square_average_memLp Q ν κ p M hp hM F hF hbound
  have hdom : ∀ᵐ ω ∂reducedLaw Q, ‖V ω‖ ≤ Real.sqrt C * A ω := by
    filter_upwards [henergy] with ω hω
    have hs := Real.sqrt_le_sqrt hω
    rw [Real.sqrt_sq (norm_nonneg _), Real.sqrt_mul hC] at hs
    exact hs
  have hscaled := hA.const_mul (Real.sqrt C)
  refine ⟨hscaled.mono' hV hdom, ?_⟩
  have hnorm := eLpNorm_mono_ae_real (p := ENNReal.ofReal p) hV hdom
  have hscalar : eLpNorm (fun ω => Real.sqrt C * A ω)
      (ENNReal.ofReal p) (reducedLaw Q) =
      ENNReal.ofReal (Real.sqrt C) * eLpNorm A (ENNReal.ofReal p) (reducedLaw Q) := by
    change eLpNorm (Real.sqrt C • A) (ENNReal.ofReal p) (reducedLaw Q) = _
    simpa only [Real.enorm_eq_ofReal_abs,
      abs_of_nonneg (Real.sqrt_nonneg C)] using
      (eLpNorm_const_smul (c := Real.sqrt C) (f := A)
        (p := ENNReal.ofReal p) (μ := reducedLaw Q))
  calc
    (eLpNorm V (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤
        (eLpNorm (fun ω => Real.sqrt C * A ω)
          (ENNReal.ofReal p) (reducedLaw Q)).toReal :=
      ENNReal.toReal_mono hscaled.ne_top hnorm
    _ = Real.sqrt C * (eLpNorm A (ENNReal.ofReal p) (reducedLaw Q)).toReal := by
      rw [hscalar, ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.sqrt_nonneg C)]
    _ ≤ Real.sqrt C * M := mul_le_mul_of_nonneg_left hAnorm (Real.sqrt_nonneg C)

end EinsteinFull.Blueprint

#print axioms EinsteinFull.Blueprint.local_time_moment_of_stationary_square_energy

#lint
