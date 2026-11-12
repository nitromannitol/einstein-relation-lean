import EinsteinRelation.Correctors.ConditionalCopyProperties
import EinsteinRelation.Correctors.AKMRandomRadiusTail
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

/-! Marginal transport of moments and random-radius tails under the literal
conditional-product coupling, `paper/main.tex:852–886`. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace EinsteinRelation.Correctors
open External.AKM

/-- The two-copy difference has every moment available for the original
observable, without independence assumptions; `paper/main.tex:852–886`. -/
theorem conditionalCopy_difference_moment_le
    {A B V : Type} [MeasurableSpace A] [StandardBorelSpace A] [Nonempty A]
    [MeasurableSpace B] [NormedAddCommGroup V]
    (Q : Measure A) [IsProbabilityMeasure Q] (X : A → B) (hX : Measurable X)
    {p : ℝ≥0∞} (hp : 1 ≤ p) {f : A → V} (hf : MemLp f p Q) :
    let P := (Q.map X) ⊗ₘ (condDistrib (id : A → A) X Q ×ₖ condDistrib (id : A → A) X Q)
    MemLp (fun z : B × (A × A) => f z.2.1 - f z.2.2) p P ∧
      eLpNorm (fun z : B × (A × A) => f z.2.1 - f z.2.2) p P ≤ 2*eLpNorm f p Q := by
  dsimp only
  obtain ⟨h1,h2⟩ := conditionalCopy_marginals Q X hX
  have hm1 : MeasurePreserving (fun z : B × (A × A) => z.2.1)
      ((Q.map X) ⊗ₘ (condDistrib (id : A → A) X Q ×ₖ condDistrib (id : A → A) X Q)) Q :=
    ⟨measurable_snd.fst, h1⟩
  have hm2 : MeasurePreserving (fun z : B × (A × A) => z.2.2)
      ((Q.map X) ⊗ₘ (condDistrib (id : A → A) X Q ×ₖ condDistrib (id : A → A) X Q)) Q :=
    ⟨measurable_snd.snd, h2⟩
  have hf1 := hf.comp_measurePreserving hm1
  have hf2 := hf.comp_measurePreserving hm2
  refine ⟨hf1.sub hf2, ?_⟩
  calc
    _ ≤ eLpNorm (fun z : B × (A × A) => f z.2.1) p _ +
        eLpNorm (fun z : B × (A × A) => f z.2.2) p _ := eLpNorm_sub_le hf1.1 hf2.1 hp
    _ = _ := (congrArg₂ (· + ·) (eLpNorm_comp_measurePreserving hf.1 hm1)
      (eLpNorm_comp_measurePreserving hf.1 hm2)).trans (two_mul _).symm

/-- A stretched-exponential bound transports along a measurable map having
the specified marginal. This applies to either conditional copy, and adds
no stochastic assumption; `paper/main.tex:852–886`. -/
theorem stretchedExponential_comp_of_map_eq
    {A Ω : Type*} [MeasurableSpace A] [MeasurableSpace Ω]
    {P : Measure Ω} {Q : Measure A} {π : Ω → A} (hπ : Measurable π)
    (hmap : P.map π = Q) {X : A → ℝ} (hX : Measurable X) {s θ : ℝ}
    (htail : StretchedExponentialBound Q s θ X) :
    StretchedExponentialBound P s θ (X ∘ π) := by
  unfold StretchedExponentialBound at *
  rw [← hmap, lintegral_map] at htail
  · exact htail
  · exact (((hX.max measurable_const).div_const θ).pow_const s).exp.ennreal_ofReal
  · exact hπ

end EinsteinRelation.Correctors
