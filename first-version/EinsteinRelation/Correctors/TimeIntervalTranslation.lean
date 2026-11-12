import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open MeasureTheory
open Set

namespace EinsteinRelation.Correctors

/-- Translate a time-slice statement without dropping its null-set qualifier.
Source: `paper/main.tex:798–806`; the backward-cylinder time convention. -/
theorem ae_restrict_Ioo_add_right_iff {a b c : ℝ} {p : ℝ → Prop} :
    (∀ᵐ t ∂volume.restrict (Set.Ioo a b), p (t+c)) ↔
      ∀ᵐ t ∂volume.restrict (Set.Ioo (a+c) (b+c)), p t := by
  have hpre : (fun t : ℝ => t + c) ⁻¹' Set.Ioo (a + c) (b + c) = Set.Ioo a b := by
    ext t
    simp only [mem_preimage, mem_Ioo]
    constructor <;> rintro ⟨hl, hr⟩ <;> constructor <;> linarith
  have hφ : MeasurePreserving (MeasurableEquiv.addRight c)
      (volume.restrict (Set.Ioo a b)) (volume.restrict (Set.Ioo (a + c) (b + c))) := by
    simpa [hpre] using (measurePreserving_add_right volume c).restrict_preimage_emb
      (MeasurableEquiv.addRight c).measurableEmbedding (Set.Ioo (a + c) (b + c))
  constructor
  · intro h
    have := hφ.symm.quasiMeasurePreserving.ae (p := fun t => p (t + c)) h
    simpa [sub_add_cancel] using this
  · intro h
    have := hφ.quasiMeasurePreserving.ae h
    simpa using this

end EinsteinRelation.Correctors
