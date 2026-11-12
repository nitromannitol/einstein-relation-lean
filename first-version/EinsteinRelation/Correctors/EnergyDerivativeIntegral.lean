import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Convex.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Order.Interval.Set.UnorderedInterval
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.Order.OrderClosed

/-! # Integrated form of a one-sided derivative bound

Auxiliary scalar estimate for the energy step of the paired-corrector argument
(`paper/main.tex:832–848`). If `f` is continuous on `[0, T]`, differentiable on `(0, T)`,
and its derivative there is bounded by a continuous `g`, then the increment `f T - f 0` is
at most `∫₀ᵀ g`. The derivative of `f` is neither assumed continuous nor integrable.
-/

open MeasureTheory

namespace EinsteinRelation.Correctors

/-- The increment of `f` over `[0, T]` is bounded by the integral of a function `g` that
dominates the derivative of `f` on `(0, T)`. -/
theorem energy_derivative_integral_le
    {f g : ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hf : ContinuousOn f (Set.Icc 0 T))
    (hg : ContinuousOn g (Set.Icc 0 T))
    (hd : ∀ t ∈ Set.Ioo 0 T, HasDerivAt f (deriv f t) t)
    (hbound : ∀ t ∈ Set.Ioo 0 T, deriv f t ≤ g t) :
    f T - f 0 ≤ ∫ t in (0 : ℝ)..T, g t := by
  -- The primitive of `g` is continuous on `[0, T]` and has derivative `g t` on `(0, T)`.
  have hGc : ContinuousOn (fun u => ∫ x in (0 : ℝ)..u, g x) (Set.Icc 0 T) := by
    have hgI : IntegrableOn g (Set.uIcc (0 : ℝ) T) := by
      rw [Set.uIcc_of_le hT]
      exact hg.integrableOn_Icc
    have hc := intervalIntegral.continuousOn_primitive_interval hgI
    rw [Set.uIcc_of_le hT] at hc
    exact hc
  have hGd : ∀ t ∈ Set.Ioo 0 T,
      HasDerivAt (fun u => ∫ x in (0 : ℝ)..u, g x) (g t) t := by
    intro t ht
    have hint : IntervalIntegrable g volume 0 t :=
      ContinuousOn.intervalIntegrable_of_Icc ht.1.le
        (hg.mono (Set.Icc_subset_Icc (le_refl (0 : ℝ)) ht.2.le))
    have hmeas : StronglyMeasurableAtFilter g (nhds t) :=
      ContinuousOn.stronglyMeasurableAtFilter (s := Set.Ioo 0 T) isOpen_Ioo
        (hg.mono Set.Ioo_subset_Icc_self) t ht
    have hcont : ContinuousAt g t :=
      hg.continuousAt (Icc_mem_nhds ht.1 ht.2)
    exact intervalIntegral.integral_hasDerivAt_right hint hmeas hcont
  -- Subtracting the primitive leaves a function with nonpositive derivative on `(0, T)`.
  have hh : ∀ t ∈ Set.Ioo 0 T,
      HasDerivAt (fun u => f u - ∫ x in (0 : ℝ)..u, g x) (deriv f t - g t) t :=
    fun t ht => (hd t ht).sub (hGd t ht)
  have hanti : AntitoneOn (fun u => f u - ∫ x in (0 : ℝ)..u, g x) (Set.Icc 0 T) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc (0 : ℝ) T)
    · exact hf.sub hGc
    · rw [interior_Icc]
      intro t ht
      exact (hh t ht).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      intro t ht
      rw [(hh t ht).deriv]
      linarith [hbound t ht]
  have key : f T - (∫ x in (0 : ℝ)..T, g x) ≤ f 0 - (∫ x in (0 : ℝ)..0, g x) :=
    hanti (Set.left_mem_Icc.mpr hT) (Set.right_mem_Icc.mpr hT) hT
  have hzero : ∫ x in (0 : ℝ)..0, g x = 0 := intervalIntegral.integral_same
  linarith

end EinsteinRelation.Correctors
