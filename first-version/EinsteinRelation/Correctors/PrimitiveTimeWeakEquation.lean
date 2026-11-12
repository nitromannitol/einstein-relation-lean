import EinsteinRelation.Correctors.WeightedPrimitiveFubini
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

open MeasureTheory
namespace EinsteinRelation.Correctors

/-- Source: `paper/main.tex:808–816,833–848`. The time primitive of an
integrable right-hand side satisfies its actual weak equation. -/
theorem intervalPrimitive_weak_equation {a b : ℝ} (hab : a < b)
    (V : ℝ → ℝ) (hV : IntervalIntegrable V volume a b)
    (η : ℝ → ℝ) (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hηc : HasCompactSupport η) (hηs : tsupport η ⊆ Set.Ioo a b) :
    (∫ t in a..b, (∫ s in a..t, V s) * deriv η t) =
      -(∫ t in a..b, V t * η t) := by
  have hη1 : ContDiff ℝ (1 : ℕ∞) η :=
    hη.of_le (WithTop.coe_le_coe.mpr (le_top (a := (1 : ℕ∞))))
  have hd : Continuous (deriv η) := hη1.continuous_deriv le_rfl
  have hdiff : Differentiable ℝ η := hη1.differentiable le_rfl
  have hb : η b = 0 := by
    by_contra h
    have hbmem : b ∈ tsupport η := subset_tsupport η (Function.mem_support.mpr h)
    exact (lt_irrefl b) (hηs hbmem).2
  rw [integral_primitive_mul_eq_integral_mul_tail hab.le V (deriv η) hV hd.continuousOn]
  have htail (s : ℝ) : (∫ t in s..b, deriv η t) = -η s := by
    rw [intervalIntegral.integral_deriv_eq_sub (fun x _ => hdiff x)
      (hd.intervalIntegrable s b), hb, zero_sub]
  simp_rw [htail, mul_neg]
  exact intervalIntegral.integral_neg

end EinsteinRelation.Correctors
