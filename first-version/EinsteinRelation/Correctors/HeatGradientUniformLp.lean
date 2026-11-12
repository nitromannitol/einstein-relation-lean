import EinsteinRelation.Correctors.HeatGradientStationaryLp

/-! Source: `paper/main.tex:722,756`. The stationary Gaussian Hessian
estimate gives a uniform `C/t` bound for the literal heat integral. -/
open MeasureTheory
open scoped ENNReal
namespace EinsteinRelation.Correctors
open HeatSelectedSkewMeaning

/-- Coordinate moment bounds and mixed-Hessian masses give a quantitative
positive-time bound, before any cutoff limit is taken. -/
theorem eLpNorm_heatGradientSpaceIntegral_le_div {d : ℕ}
    {Q : Measure (FieldPair d)} [IsProbabilityMeasure Q] (hQ : IsStationary Q)
    (F : FieldPair d → Vec d) (hF : Measurable F)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ∞)
    (A C : ℝ) (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hFnorm : ∀ i, eLpNorm (fun ρ => F ρ i) p Q ≤ ENNReal.ofReal A)
    (t : ℝ) (ht : 0 < t) (j k l : Fin d)
    (hK : ∀ i, Integrable (coordinateDerivative l (coordinateDerivative i
      (euclideanHeatKernel (d := d) t))) volume ∧
      (∫ y, |coordinateDerivative l (coordinateDerivative i
        (euclideanHeatKernel (d := d) t)) y|) ≤ C / t) :
    eLpNorm (fun ρ => akmHeatGradientSpaceIntegral
      (fun y => F (translate y ρ)) t j k l 0) p Q ≤
      ENNReal.ofReal (2 * C * A / t) := by
  have hi (i : Fin d) : Integrable (fun ρ => F ρ i) Q := by
    have hmem : MemLp (fun ρ => F ρ i) p Q :=
      ⟨((measurable_pi_apply i).comp hF).aestronglyMeasurable,
        (hFnorm i).trans_lt ENNReal.ofReal_lt_top⟩
    exact hmem.integrable hp
  apply (eLpNorm_heatGradientSpaceIntegral_le hQ F hF hp hpt t ht j k l
    (hK j).1 (hK k).1 (hi j) (hi k)).trans
  calc
    _ ≤ ENNReal.ofReal (C / t) * ENNReal.ofReal A +
        ENNReal.ofReal (C / t) * ENNReal.ofReal A :=
      add_le_add (mul_le_mul (ENNReal.ofReal_le_ofReal (hK j).2) (hFnorm k)
        (zero_le _) (zero_le _))
        (mul_le_mul (ENNReal.ofReal_le_ofReal (hK k).2) (hFnorm j)
          (zero_le _) (zero_le _))
    _ = ENNReal.ofReal (2 * C * A / t) := by
      rw [← ENNReal.ofReal_mul (div_nonneg hC ht.le),
        ← ENNReal.ofReal_add (mul_nonneg (div_nonneg hC ht.le) hA)
          (mul_nonneg (div_nonneg hC ht.le) hA)]
      congr 1
      ring

end EinsteinRelation.Correctors
