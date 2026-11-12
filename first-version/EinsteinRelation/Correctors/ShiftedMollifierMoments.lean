import EinsteinRelation.Correctors.ShiftedMollifierMeans
import EinsteinRelation.Correctors.NormedIntegralMoment

/-! # Moments of shifted smooth averages

Source: `paper/main.tex:948–955`. The segment identity for weak gradients
and Minkowski's inequality turn uniform tested-gradient bounds along the
segment into the same bound on a difference of smooth averages. The test
bounds themselves must come from the identified AKM corrector and rescaled
mollifier; they are not additional literature inputs.
-/

open MeasureTheory
open scoped Convolution

namespace EinsteinRelation.Correctors

/-- Joint measurability of the directional gradient average along a
translation segment. Source: `paper/main.tex:948–955`. -/
theorem measurable_convolution_gradient_segment {Ω : Type*} [MeasurableSpace Ω]
    {d : ℕ} (G : Ω → Vec d → Vec d)
    (hG : Measurable (fun z : Ω × Vec d => G z.1 z.2))
    {ζ : Vec d → ℝ} (hζ : Continuous ζ) (y : Vec d) :
    Measurable (fun z : ℝ × Ω => ∑ j : Fin d,
      y j * ((fun x => G z.2 x j) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ζ) (z.1 • y)) := by
  apply Finset.measurable_fun_sum
  intro j _
  apply measurable_const.mul
  have hm : Measurable (fun z : (ℝ × Ω) × Vec d =>
      G z.1.2 z.2 j * ζ (z.1.1 • y - z.2)) := by
    apply Measurable.mul
    · exact (measurable_pi_apply j).comp
        (hG.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
    · exact hζ.measurable.comp
        (((measurable_fst.comp measurable_fst).smul measurable_const).sub measurable_snd)
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

/-- A uniform moment bound for tested gradients along the unit segment
bounds the shifted mean, also for merely weakly differentiable correctors.
The constant and norm are unchanged. Source: `paper/main.tex:948–955`. -/
theorem convolution_shift_moment_le {Ω : Type*} [MeasurableSpace Ω]
    {d : ℕ} (Q : Measure Ω) [IsProbabilityMeasure Q] {p B : ℝ}
    (hp : 1 ≤ p) (hB : 0 ≤ B)
    (f : Ω → Vec d → ℝ) (G : Ω → Vec d → Vec d)
    (hGm : Measurable (fun z : Ω × Vec d => G z.1 z.2))
    (hloc : ∀ᵐ ω ∂Q, LocallyIntegrable (f ω) volume)
    (hweak : ∀ᵐ ω ∂Q, HasWeakGradient Set.univ (f ω) (G ω))
    {ζ : Vec d → ℝ} (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hζc : HasCompactSupport ζ)
    (y : Vec d)
    (hbound : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      MemLp (fun ω => ∑ j : Fin d,
          y j * ((fun x => G ω x j) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ζ) (t • y))
        (ENNReal.ofReal p) Q ∧
      eLpNorm (fun ω => ∑ j : Fin d,
          y j * ((fun x => G ω x j) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ζ) (t • y))
        (ENNReal.ofReal p) Q ≤ ENNReal.ofReal B) :
    MemLp (fun ω => (f ω ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ζ) y -
        (f ω ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ζ) 0) (ENNReal.ofReal p) Q ∧
      eLpNorm (fun ω => (f ω ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ζ) y -
        (f ω ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ζ) 0)
        (ENNReal.ofReal p) Q ≤ ENNReal.ofReal B := by
  let D : ℝ × Ω → ℝ := fun z => ∑ j : Fin d,
    y j * ((fun x => G z.2 x j) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ζ) (z.1 • y)
  let V : ℝ × Ω → ℝ := fun z => if z.1 ∈ Set.Icc (0 : ℝ) 1 then D z else 0
  have hDm : Measurable D := measurable_convolution_gradient_segment G hGm hζ.continuous y
  have hVm : Measurable V := hDm.ite
    (measurableSet_Icc.preimage measurable_fst) measurable_const
  have hVB (t : ℝ) : MemLp (fun ω => V (t, ω)) (ENNReal.ofReal p) Q ∧
      eLpNorm (fun ω => V (t, ω)) (ENNReal.ofReal p) Q ≤ ENNReal.ofReal B := by
    by_cases ht : t ∈ Set.Icc (0 : ℝ) 1
    · simpa only [V, if_pos ht, D] using hbound t ht
    · simp only [V, if_neg ht]
      exact ⟨MemLp.zero', by simp only [eLpNorm_zero']; exact zero_le _⟩
  obtain ⟨_, hmem, hnorm⟩ := normed_integral_moment_le Q
    (volume.restrict (Set.Ioc (0 : ℝ) 1)) hp (fun _ => B) measurable_const
    (fun _ => hB) (integrable_const B) V hVm hVB
  have heq : (fun ω => ∫ t in Set.Ioc (0 : ℝ) 1, V (t, ω)) =ᵐ[Q]
      (fun ω => (f ω ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ζ) y -
        (f ω ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ζ) 0) := by
    filter_upwards [hloc, hweak] with ω hω hω'
    rw [convolution_shift_sub_eq_integral_weakGradient hω hω' hζ hζc y,
      intervalIntegral.integral_of_le zero_le_one]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact if_pos ⟨ht.1.le, ht.2⟩
  refine ⟨(memLp_congr_ae heq).mp hmem, ?_⟩
  rw [← eLpNorm_congr_ae heq]
  simpa only [integral_const, measureReal_def, Measure.restrict_apply_univ, Real.volume_Ioc,
    sub_zero, ENNReal.ofReal_one, ENNReal.toReal_one, one_smul] using hnorm

end EinsteinRelation.Correctors
