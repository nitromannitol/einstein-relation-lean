import EinsteinRelation.Calculus.L2IntegralRepresentatives
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! # Literal representatives of L2 interval primitives

Source: `paper/main.tex:1021–1029`. The representative identity respects
the orientation of both positive and negative coordinate segments.
-/

open MeasureTheory
noncomputable section
namespace EinsteinRelation

/-- The oriented `L²` interval integral has the literal orbit integral
as an almost-everywhere representative (`paper/main.tex:1021–1029`). -/
theorem ae_coe_L2_intervalIntegral {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {a b : ℝ}
    {G : ℝ → Lp ℝ 2 μ} (hG : IntervalIntegrable G volume a b)
    {F : ℝ × Ω → ℝ}
    (hF : Integrable F ((volume.restrict (Set.uIoc a b)).prod μ))
    (heq : ∀ᵐ t ∂volume.restrict (Set.uIoc a b),
      (G t : Ω → ℝ) =ᵐ[μ] fun ω => F (t, ω)) :
    (fun ω => (∫ t in a..b, G t : Lp ℝ 2 μ) ω) =ᵐ[μ]
      fun ω => ∫ t in a..b, F (t, ω) := by
  have h := ae_coe_L2_integral hG.def' hF heq
  rcases le_total a b with hab | hba
  · simpa only [intervalIntegral.integral_of_le hab, Set.uIoc_of_le hab] using h
  · have hn := Lp.coeFn_neg (∫ t in Set.uIoc a b, G t : Lp ℝ 2 μ)
    filter_upwards [h, hn] with ω hω hnω
    simpa only [intervalIntegral.integral_of_ge hba, Set.uIoc_of_ge hba] using
      hnω.trans (congrArg Neg.neg hω)

end EinsteinRelation
