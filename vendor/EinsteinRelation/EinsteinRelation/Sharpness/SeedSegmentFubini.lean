import EinsteinRelation.External.WhiteNoise
import EinsteinRelation.Sharpness.SeedFieldDerivatives
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! # Segment Fubini for the derivatives of the canonical seed

Source: `paper/main.tex`, proof of Proposition 7.1, Step 1, lines 1212–1218, and the stationary
centering of the derivatives of `h` in lines 1261–1265. The seed is `seedField d W`. Along the
segment `t ↦ t • unitVector i`, its coordinate derivative is jointly measurable in the actual sample
`W` and the time `t`, and it is bounded uniformly in both by the deterministic constant of
`exists_uniform_seedField_derivative_bound`. The product of the probability law `P` with the finite
interval measure `volume.restrict (Ioc 0 5)` therefore dominates the squared derivative, and
finite-measure Fubini exchanges the two integrals. No extra integrability hypothesis is used, and no
differentiation under the expectation is needed.
-/

open MeasureTheory

namespace EinsteinRelation.Sharpness

/-- Source: `paper/main.tex`, proof of Proposition 7.1, Step 1, lines 1212–1218, and the
centering in lines 1261–1265. For a white-noise law `P` and a coordinate `i`, the squared
coordinate derivative of the canonical seed along the segment `t • unitVector i`, for
`t ∈ (0, 5]`, is integrable on the product `P ⊗ volume|_(0,5]`, and the expectation of its time
integral equals the time integral of its expectation. -/
theorem integrable_and_integral_seedField_segment_derivative_sq_swap
    {d : ℕ} {P : Measure (NoiseSample d)} (hP : External.IsWhiteNoiseLaw P) (i : Fin d) :
    Integrable (fun p : NoiseSample d × ℝ =>
      (coordinateDerivative i (seedField d p.1) (p.2 • unitVector i))^2)
      (P.prod (volume.restrict (Set.Ioc (0 : ℝ) 5))) ∧
    (∫ W : NoiseSample d, (∫ t : ℝ in (0)..5,
      (coordinateDerivative i (seedField d W) (t • unitVector i))^2) ∂P) =
    ∫ t : ℝ in (0)..5, (∫ W : NoiseSample d,
      (coordinateDerivative i (seedField d W) (t • unitVector i))^2 ∂P) := by
  letI : IsProbabilityMeasure P := hP.1
  -- Deterministic bound on the first coordinate derivative, uniform in the sample and the point.
  obtain ⟨C, -, hC⟩ := exists_uniform_seedField_derivative_bound d [i]
  have hC' : ∀ (W : NoiseSample d) (x : Vec d), |coordinateDerivative i (seedField d W) x| ≤ C :=
    fun W x => hC W x
  -- The squared derivative is bounded by `C ^ 2` at every sample and every time.
  have hsq : ∀ (W : NoiseSample d) (t : ℝ),
      ‖(coordinateDerivative i (seedField d W) (t • unitVector i))^2‖ ≤ C ^ 2 := by
    intro W t
    have hab := abs_le.mp (hC' W (t • unitVector i))
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact sq_le_sq' hab.1 hab.2
  -- Joint measurability of `(W, x) ↦ ∂ᵢ seedField W x`, from the producer with `is = [i]`.
  have hG : Measurable (fun p : NoiseSample d × Vec d =>
      coordinateDerivative i (seedField d p.1) p.2) :=
    measurable_seedField_iteratedCoordinateDerivative_uncurry d [i]
  -- The map `(W, t) ↦ (W, t • unitVector i)` is measurable.
  have hshift : Measurable (fun p : NoiseSample d × ℝ => (p.1, p.2 • unitVector i)) :=
    measurable_fst.prodMk (measurable_snd.smul_const (unitVector i))
  have hF : Measurable (fun p : NoiseSample d × ℝ =>
      (coordinateDerivative i (seedField d p.1) (p.2 • unitVector i))^2) :=
    Measurable.fun_comp (g := fun p : NoiseSample d × Vec d =>
      (coordinateDerivative i (seedField d p.1) p.2)^2)
      (f := fun p : NoiseSample d × ℝ => (p.1, p.2 • unitVector i))
      (hG.pow_const 2) hshift
  -- `P` is a probability measure and `volume.restrict (Ioc 0 5)` is finite, so the product is
  -- finite and the bounded measurable integrand is integrable.
  have hInt : Integrable (fun p : NoiseSample d × ℝ =>
      (coordinateDerivative i (seedField d p.1) (p.2 • unitVector i))^2)
      (P.prod (volume.restrict (Set.Ioc (0 : ℝ) 5))) :=
    Integrable.of_bound hF.aestronglyMeasurable (C ^ 2) (ae_of_all _ fun p => hsq p.1 p.2)
  refine ⟨hInt, ?_⟩
  -- Replace the interval integrals over `0..5` by integrals over `Ioc 0 5`, then exchange them.
  have h05 : (0 : ℝ) ≤ 5 := by norm_num
  simp only [intervalIntegral.integral_of_le h05]
  exact integral_integral_swap (f := fun (W : NoiseSample d) (t : ℝ) =>
    (coordinateDerivative i (seedField d W) (t • unitVector i))^2) hInt

end EinsteinRelation.Sharpness
