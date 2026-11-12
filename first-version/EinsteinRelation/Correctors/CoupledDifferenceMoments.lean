import EinsteinRelation.Correctors.CoupledTailTriangle

/-! Marginal moment control for a coupled difference, as used in
`paper/main.tex:856–862`. No independence is required. -/

open MeasureTheory
open scoped ENNReal

namespace EinsteinRelation.Correctors

/-- Any coupling with the prescribed marginals has at most twice the
single-field moment. Source: `paper/main.tex:856–862`. -/
theorem coupledDifference_moment_le
    {Ω Z E : Type*} [MeasurableSpace Ω] [MeasurableSpace Z]
    [NormedAddCommGroup E] {μ : Measure Ω} {ν : Measure Z}
    {π₁ π₂ : Z → Ω} (h₁ : MeasurePreserving π₁ ν μ)
    (h₂ : MeasurePreserving π₂ ν μ) {p : ℝ≥0∞} (hp : 1 ≤ p)
    {f : Ω → E} (hf : AEStronglyMeasurable f μ)
    {B : ℝ} (hB : 0 ≤ B) (hb : eLpNorm f p μ ≤ ENNReal.ofReal B) :
    MemLp (fun z => ‖f (π₁ z) - f (π₂ z)‖) p ν ∧
      eLpNorm (fun z => ‖f (π₁ z) - f (π₂ z)‖) p ν ≤ ENNReal.ofReal (2*B) := by
  have hLp : MemLp f p μ := ⟨hf, hb.trans_lt ENNReal.ofReal_lt_top⟩
  have hnorm₁ : eLpNorm (f ∘ π₁) p ν = eLpNorm f p μ :=
    eLpNorm_comp_measurePreserving hf h₁
  have hnorm₂ : eLpNorm (f ∘ π₂) p ν = eLpNorm f p μ :=
    eLpNorm_comp_measurePreserving hf h₂
  have hLp₁ := hLp.comp_measurePreserving h₁
  have hLp₂ := hLp.comp_measurePreserving h₂
  refine ⟨(hLp₁.sub hLp₂).norm, ?_⟩
  rw [eLpNorm_norm]
  calc
    _ ≤ eLpNorm (f ∘ π₁) p ν + eLpNorm (f ∘ π₂) p ν :=
      eLpNorm_sub_le hLp₁.1 hLp₂.1 hp
    _ = eLpNorm f p μ + eLpNorm f p μ := by rw [hnorm₁, hnorm₂]
    _ ≤ ENNReal.ofReal B + ENNReal.ofReal B := add_le_add hb hb
    _ = ENNReal.ofReal (2*B) := by rw [← ENNReal.ofReal_add hB hB, ← two_mul]

end EinsteinRelation.Correctors
