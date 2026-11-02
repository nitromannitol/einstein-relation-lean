import EinsteinFull.Frozen.LocalSpatialEnergy
import EinsteinRelation.Probability.LocalSigma
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Average

/-! # Measurability of the local spatial energy

The v4.35 `MeasureTheory.eLpNorm` is `∞` off `AEStronglyMeasurable` functions. The frozen
estimates in `EinsteinFull.Frozen.ForcedLocalEstimates` apply `eLpNorm` to
`localSpatialEnergy`, so this file proves that this function is AE strongly measurable for the
reduced law, for every choice of its own arguments. Consequently `eLpNorm` agrees with the
classical `eLpNorm'` formula at every exponent `0 < p < ∞`.
-/

open MeasureTheory
open scoped ENNReal NNReal

namespace EinsteinFull

open EinsteinRelation

/-- The local spatial energy is AE strongly measurable for the reduced law. The `Lp`
representatives are strongly measurable, translation is jointly continuous, and the ball
average is a parametric Bochner integral. -/
theorem localSpatialEnergy_aestronglyMeasurable {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (t : ℝ≥0) (ρ : ℝ) (hρ : 0 < ρ) (x : Vec d)
    (G : Fin d → Lp ℂ 2 (reducedLaw Q)) (V : Lp ℂ 2 (reducedLaw Q)) :
    AEStronglyMeasurable (localSpatialEnergy Q t ρ hρ x G V) (reducedLaw Q) := by
  have hT : Measurable (fun p : FieldPair d × Vec d => translate p.2 p.1) :=
    Probability.continuous_translate.measurable.comp (measurable_snd.prodMk measurable_fst)
  have hG : ∀ j : Fin d, Measurable
      (fun p : FieldPair d × Vec d => ‖G j (translate p.2 p.1)‖ ^ 2) := fun j =>
    (((Lp.stronglyMeasurable (G j)).measurable.comp hT).norm).pow_const 2
  have hV : Measurable (fun p : FieldPair d × Vec d => ‖V (translate p.2 p.1)‖ ^ 2) :=
    (((Lp.stronglyMeasurable V).measurable.comp hT).norm).pow_const 2
  have hF : Measurable (Function.uncurry fun (ω : FieldPair d) (y : Vec d) =>
      (∑ j : Fin d, ‖G j (translate y ω)‖ ^ 2) + (t : ℝ) * ‖V (translate y ω)‖ ^ 2) :=
    (Finset.measurable_fun_sum _ fun j _ => hG j).add (hV.const_mul (t : ℝ))
  have hI := hF.stronglyMeasurable.integral_prod_right
    (ν := volume.restrict {y : Vec d | euclideanNorm (y - x) < ρ})
  have hm : Measurable (fun ω : FieldPair d =>
      ⨍ y in {y : Vec d | euclideanNorm (y - x) < ρ},
        (∑ j : Fin d, ‖G j (translate y ω)‖ ^ 2) + (t : ℝ) * ‖V (translate y ω)‖ ^ 2) := by
    simp only [setAverage_eq]
    exact hI.measurable.const_smul
      ((volume : Measure (Vec d)).real {y : Vec d | euclideanNorm (y - x) < ρ})⁻¹
  exact (Real.continuous_sqrt.measurable.comp hm).aestronglyMeasurable

/-- At every exponent `0 < p < ∞`, `eLpNorm` of the local spatial energy is the classical
`eLpNorm'` formula, so the frozen estimates mean what they meant before `eLpNorm` was
redefined to be `∞` off AE strongly measurable functions. -/
theorem eLpNorm_localSpatialEnergy_eq_eLpNorm' {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (t : ℝ≥0) (ρ : ℝ) (hρ : 0 < ρ) (x : Vec d)
    (G : Fin d → Lp ℂ 2 (reducedLaw Q)) (V : Lp ℂ 2 (reducedLaw Q))
    {p : ℝ≥0∞} (hp0 : p ≠ 0) (hptop : p ≠ ∞) :
    eLpNorm (localSpatialEnergy Q t ρ hρ x G V) p (reducedLaw Q) =
      eLpNorm' (localSpatialEnergy Q t ρ hρ x G V) p.toReal (reducedLaw Q) :=
  eLpNorm_eq_eLpNorm' hp0 hptop (localSpatialEnergy_aestronglyMeasurable Q t ρ hρ x G V)

end EinsteinFull
