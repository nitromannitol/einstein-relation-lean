import EinsteinRelation.Correctors.IntegralMoment
import EinsteinRelation.Correctors.NonnegativePowerMoments

/-! # Probability moments of roots of time integrals

Source: `paper/main.tex:844–849`. Minkowski is applied at exponent `p/q`
to the `q`-th power of a nonnegative scalar field, then the result is
raised to the reciprocal power. No independence of the samples is used.
-/

open MeasureTheory
open scoped ENNReal
namespace EinsteinRelation.Correctors

/-- The probability Minkowski step for the weighted energy source.
Source: `paper/main.tex:844–849`. -/
theorem root_integral_moment_le {Ω X : Type*} [MeasurableSpace Ω]
    [MeasurableSpace X] (Q : Measure Ω) [IsProbabilityMeasure Q]
    (ν : Measure X) [SigmaFinite ν] {p q : ℝ}
    (hp : 1 ≤ p) (hq : 0 < q) (hq1 : q ≤ 1)
    (H : X → ℝ) (hHm : Measurable H) (hH : ∀ x, 0 ≤ H x)
    (hHi : Integrable (fun x => (H x)^q) ν)
    (a : X × Ω → ℝ) (ha : Measurable a) (han : ∀ z, 0 ≤ a z)
    (hmom : ∀ x, MemLp (fun ω => a (x,ω)) (ENNReal.ofReal p) Q ∧
      eLpNorm (fun ω => a (x,ω)) (ENNReal.ofReal p) Q ≤ ENNReal.ofReal (H x)) :
    (∀ᵐ ω ∂Q, Integrable (fun x => (a (x,ω))^q) ν) ∧
    MemLp (fun ω => (∫ x, (a (x,ω))^q ∂ν)^(1/q)) (ENNReal.ofReal p) Q ∧
    eLpNorm (fun ω => (∫ x, (a (x,ω))^q ∂ν)^(1/q)) (ENNReal.ofReal p) Q ≤
      ENNReal.ofReal ((∫ x, (H x)^q ∂ν)^(1/q)) := by
  have hp0 : 0 < p := zero_lt_one.trans_le hp
  have hpq : 1 ≤ p / q := (le_div_iff₀ hq).mpr (by simpa using hq1.trans hp)
  have hpowm : Measurable (fun z => (a z)^q) := ha.pow_const q
  obtain ⟨hsec, hmem, hnorm⟩ := integral_moment_le Q ν hpq
    (fun x => (H x)^q) (hHm.pow_const q)
    (fun x => Real.rpow_nonneg (hH x) _) hHi
    (fun z => (a z)^q) hpowm (fun x =>
      nonnegative_rpow_moment Q hp0 hq (hH x)
        (ha.comp measurable_prodMk_left) (fun ω => han (x,ω))
        (hmom x).1 (hmom x).2)
  have hJm : Measurable (fun ω => ∫ x, (a (x,ω))^q ∂ν) :=
    (hpowm.comp measurable_swap).stronglyMeasurable.integral_prod_right'.measurable
  have hJn (ω : Ω) : 0 ≤ ∫ x, (a (x,ω))^q ∂ν :=
    integral_nonneg fun x => Real.rpow_nonneg (han (x,ω)) _
  have hr := nonnegative_rpow_moment Q (div_pos hp0 hq) (one_div_pos.mpr hq)
    (integral_nonneg fun x => Real.rpow_nonneg (hH x) _) hJm hJn hmem hnorm
  have he : p / q / (1 / q) = p := by field_simp
  rw [he] at hr
  exact ⟨hsec, hr⟩

end EinsteinRelation.Correctors
