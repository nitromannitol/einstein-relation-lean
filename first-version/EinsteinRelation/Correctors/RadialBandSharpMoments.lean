import EinsteinRelation.Correctors.StationaryHeatTransfer

/-! # Sharp radial-band moments from scalar averaging

Source: `paper/main.tex:1033–1041`. The heat-transfer identity is proved
for the actual stationary field, so the derivative bounds here have no
remaining heat-transfer premise. The homogenized coordinate change is a
separate obligation.
-/

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace EinsteinRelation.Correctors

variable {d : ℕ}

/-- The scalar averaging assumption implies integrability of the initial
field (`paper/main.tex:1028–1030`). -/
theorem integrable_of_heatSmoothed_bound {Q : Measure (FieldPair d)} [IsProbabilityMeasure Q]
    {p : ℝ≥0∞} (hp : 1 ≤ p) {M R : ℝ} {f : FieldPair d → ℝ} (hf : Measurable f)
    (hheat : ∀ t : ℝ, 0 ≤ t → eLpNorm (heatSmoothed t f) p Q ≤
      ENNReal.ofReal (M * ((Real.sqrt (1 + t))⁻¹ + R⁻¹))) :
    Integrable f Q := by
  have h0 : heatSmoothed 0 f = f := by
    funext ω
    simp [heatSmoothed]
  have hb : eLpNorm f p Q ≤ ENNReal.ofReal (M * (1 + R⁻¹)) := by
    simpa only [h0, add_zero, Real.sqrt_one, inv_one] using hheat 0 le_rfl
  exact (show MemLp f p Q from
    ⟨hf.aestronglyMeasurable, hb.trans_lt ENNReal.ofReal_lt_top⟩).integrable hp

/-- Every coordinate derivative of the actual radial Poisson band has the
sharp scale `r^(1-k)` under scalar averaging (`paper/main.tex:1033–1041`).
The constant precedes the environment law and the moment order. -/
theorem eLpNorm_radialBand_le (hd : 2 ≤ d) (cs : List (Fin d)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q],
      IsStationary Q → ∀ (p : ℝ≥0∞), 1 ≤ p → p ≠ ∞ →
      ∀ (M r R : ℝ), 0 < M → 0 < r → 0 < R → r ≤ R →
      ∀ (f : FieldPair d → ℝ), Measurable f →
      (∀ t : ℝ, 0 ≤ t → eLpNorm (heatSmoothed t f) p Q ≤
        ENNReal.ofReal (M * ((Real.sqrt (1 + t))⁻¹ + R⁻¹))) →
      eLpNorm (horizontalMollify (coordinateIterate cs (radialBandKernel d r)) f) p Q ≤
        ENNReal.ofReal (C * M * (r / r ^ cs.length)) := by
  obtain ⟨C, hC, hbound⟩ := eLpNorm_radialBand_le_of_heatTransfer hd cs
  refine ⟨C, hC, fun Q _ hQ p hp hpt M r R hM hr hR hrR f hf hheat => ?_⟩
  apply hbound Q hQ p hp hpt M r R hM hr hR hrR f hf hheat
  exact horizontalMollify_heatTransfer_ae hQ
    (KernelCalculus.contDiff_coordinateIterate (radialBandKernel_contDiff hd hr) cs)
    (KernelCalculus.hasCompactSupport_coordinateIterate
      (radialBandKernel_hasCompactSupport hd hr) cs)
    hf (integrable_of_heatSmoothed_bound hp hf hheat) (sq_pos_of_pos hr)

end EinsteinRelation.Correctors
