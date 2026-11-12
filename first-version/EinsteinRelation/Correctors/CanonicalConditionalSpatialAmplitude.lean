import EinsteinRelation.Correctors.CanonicalConditionalAmplitudeBound
import EinsteinRelation.Correctors.ConditionalSpatialMollifierMoment

/-! # Spatial source moments control the common conditional fields

Source: `paper/main.tex:942–947`. The literal conditional averages inherit
product-space source moments against the scaled mollifier probability measure.
-/

open MeasureTheory
open EinsteinRelation.Carriers (reducedCoefficientObservationSigma)
namespace EinsteinRelation.Correctors

/-- Scalar and entrywise source amplitudes control the actual common scalar
and Frobenius skew average. Source: `paper/main.tex:942–947`. -/
theorem canonicalConditionalMollifierFields_amplitude_bound_of_spatial_moments
    {d : ℕ} {L r₀ R p C : ℝ} (Q : EnvironmentLaw d L r₀) (i : Fin d)
    (hR : 0 < R) (hp : 1 ≤ p) (hC : 0 ≤ C)
    (u : FieldPair d → Vec d → ℝ) (S : FieldPair d → Vec d → Mat d)
    (hum : StronglyMeasurable (Function.uncurry u))
    (hSm : ∀ j k, StronglyMeasurable (fun z : FieldPair d × Vec d => S z.1 z.2 j k))
    (hu : MemLp (fun z : FieldPair d × Vec d => u z.1 (-z.2))
      (ENNReal.ofReal p) ((reducedEnvironmentLaw Q).prod (mollifierCenterMeasure d R)))
    (hS : ∀ j k, MemLp (fun z : FieldPair d × Vec d => S z.1 (-z.2) j k)
      (ENNReal.ofReal p) ((reducedEnvironmentLaw Q).prod (mollifierCenterMeasure d R)))
    (hub : eLpNorm (fun z : FieldPair d × Vec d => u z.1 (-z.2))
      (ENNReal.ofReal p) ((reducedEnvironmentLaw Q).prod (mollifierCenterMeasure d R)) ≤
        ENNReal.ofReal C)
    (hSb : ∀ j k, eLpNorm (fun z : FieldPair d × Vec d => S z.1 (-z.2) j k)
      (ENNReal.ofReal p) ((reducedEnvironmentLaw Q).prod (mollifierCenterMeasure d R)) ≤
        ENNReal.ofReal C) :
    let f := canonicalConditionalMollifierFields Q i R u S
    eLpNorm f.scalar (ENNReal.ofReal p) (reducedEnvironmentLaw Q) +
      eLpNorm (fun ω => frobeniusNorm (f.skew ω))
        (ENNReal.ofReal p) (reducedEnvironmentLaw Q) ≤
          ENNReal.ofReal ((1 + (d : ℝ) * d) * C) := by
  let f := canonicalConditionalMollifierFields Q i R u S
  have hφ := (eLpNorm_centered_conditional_mollifier_le_spatial_moment
    Q hR (ENNReal.one_le_ofReal.mpr hp) ENNReal.ofReal_ne_top u hum hu).trans hub
  have hentry (j k : Fin d) : eLpNorm (fun ω => f.skew ω j k)
      (ENNReal.ofReal p) (reducedEnvironmentLaw Q) ≤ ENNReal.ofReal C :=
    (eLpNorm_centered_conditional_mollifier_le_spatial_moment
      Q hR (ENNReal.one_le_ofReal.mpr hp) ENNReal.ofReal_ne_top
      (fun a x => S a x j k) (hSm j k) (hS j k)).trans (hSb j k)
  have hm : Measurable f.skew := by
    have hobs : reducedCoefficientObservationSigma
        {x : Vec d | euclideanNorm x < 33 * R} ≤ borel (FieldPair d) := by
      rw [reducedCoefficientObservationSigma_eq_comap_evaluation]
      exact (measurable_pi_lambda _ fun x : {x : Vec d | euclideanNorm x < 33 * R} =>
        ((continuous_eval_const (x : Vec d)).comp continuous_fst).measurable).comap_le
    exact (measurable_canonicalConditionalMollifierFields Q i hR u S hum hSm).2.1.mono
      hobs le_rfl
  have hskew : eLpNorm (fun ω => frobeniusNorm (f.skew ω))
      (ENNReal.ofReal p) (reducedEnvironmentLaw Q) ≤
        ENNReal.ofReal ((d : ℝ) * d * C) := by
    calc
      _ ≤ ∑ j : Fin d, ∑ k : Fin d, eLpNorm (fun ω => f.skew ω j k)
          (ENNReal.ofReal p) (reducedEnvironmentLaw Q) :=
        eLpNorm_frobeniusNorm_le_sum_entries (ENNReal.one_le_ofReal.mpr hp) f.skew hm
      _ ≤ ∑ _j : Fin d, ∑ _k : Fin d, ENNReal.ofReal C :=
        Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ => hentry j k
      _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ d),
          ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ d)]
        congr 1
        ring
  calc
    _ ≤ ENNReal.ofReal C + ENNReal.ofReal ((d : ℝ) * d * C) := add_le_add hφ hskew
    _ = _ := by
      rw [← ENNReal.ofReal_add hC (by positivity)]
      congr 1
      ring

end EinsteinRelation.Correctors
