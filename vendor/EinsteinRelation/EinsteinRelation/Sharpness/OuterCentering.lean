import EinsteinRelation.Sharpness.NoiseKernel
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.OuterMeasure.AE

/-! # Outer centering of a bounded centered field

Source: `paper/main.tex`, proof of Proposition 7.1, Step 1, lines 1212–1216. The field
`h ≔ ζ * tanh(K * W)` is an outer convolution of the compactly supported `ζ` with a bounded
field. This file shows that the outer convolution of a jointly measurable, bounded, centered
field is integrable on the probability space and has mean zero.

The field `H` is an arbitrary parameter. The statement uses only its joint measurability,
the bound `|H| ≤ 1`, and centering of its one-point marginals. It is an analytic helper, not a
sharpness assumption or a field-existence claim. Integrability is derived by Fubini, and no
product-integrability hypothesis is assumed.
-/

open MeasureTheory

namespace EinsteinRelation.Sharpness

/-- Source: `paper/main.tex`, Proposition 7.1, Step 1, lines 1212–1216. For a continuous
compactly supported `ζ` and a jointly measurable field `H` with `|H| ≤ 1` and centered
one-point marginals, the outer convolution `ω ↦ ∫ ζ(y) H(ω, x - y) dy` is `P`-integrable
and has mean zero. No positivity or mass condition on `ζ` is required. -/
theorem integrable_and_integral_outer_field_eq_zero {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ}
    (ζ : Vec d → ℝ) (H : Ω → Vec d → ℝ)
    (hζ : Continuous ζ) (hζc : HasCompactSupport ζ)
    (hH : Measurable (fun p : Ω × Vec d => H p.1 p.2))
    (hb : ∀ ω y, |H ω y| ≤ 1) (hmean : ∀ y, (∫ ω, H ω y ∂P) = 0)
    (x : Vec d) :
    Integrable (fun ω => ∫ y : Vec d, ζ y * H ω (x-y)) P ∧
      (∫ ω, (∫ y : Vec d, ζ y * H ω (x-y)) ∂P) = 0 := by
  -- Joint measurability of `(ω, y) ↦ ζ y * H ω (x - y)`, from the measurable field `H`.
  have hsub : Continuous (fun y : Vec d => x - y) := continuous_const.sub continuous_id
  have hpair : Measurable (fun p : Ω × Vec d => (p.1, x - p.2)) :=
    measurable_fst.prodMk (hsub.measurable.comp measurable_snd)
  have hmeas : Measurable (fun p : Ω × Vec d => ζ p.2 * H p.1 (x - p.2)) :=
    (hζ.measurable.comp measurable_snd).mul (hH.comp hpair)
  -- The dominator `|ζ y|` is integrable on `P ⊗ volume`, because `P` is finite.
  have hζi : Integrable ζ volume := hζ.integrable_of_hasCompactSupport hζc
  have hdom : Integrable (fun p : Ω × Vec d => |ζ p.2|) (P.prod volume) :=
    hζi.abs.comp_snd P
  -- The pointwise bound `|ζ y * H ω (x - y)| ≤ |ζ y|` comes from `|H| ≤ 1`.
  have hpt : ∀ p : Ω × Vec d, ‖ζ p.2 * H p.1 (x - p.2)‖ ≤ |ζ p.2| := fun p => by
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (hb _ _)
  have hint : Integrable (fun p : Ω × Vec d => ζ p.2 * H p.1 (x - p.2)) (P.prod volume) :=
    hdom.mono' hmeas.aestronglyMeasurable (ae_of_all _ hpt)
  -- For each fixed `y`, the `ω`-integral vanishes by the centering hypothesis.
  have hinner : ∀ y : Vec d, (∫ ω, ζ y * H ω (x - y) ∂P) = 0 := fun y => by
    rw [integral_const_mul, hmean (x - y), mul_zero]
  -- Fubini swaps the two integrals, and every `y`-slice is zero.
  have hswap : (∫ ω, (∫ y : Vec d, ζ y * H ω (x - y)) ∂P) =
      ∫ y : Vec d, (∫ ω, ζ y * H ω (x - y) ∂P) :=
    integral_integral_swap (f := fun ω y => ζ y * H ω (x - y)) hint
  refine ⟨hint.integral_prod_left, ?_⟩
  rw [hswap]
  simp only [hinner, integral_zero]

end EinsteinRelation.Sharpness
