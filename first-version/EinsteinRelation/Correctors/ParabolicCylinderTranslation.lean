import EinsteinRelation.Correctors.ParabolicTimeTranslation

/-! # Translation of normalized cylinder energy

Source: `paper/main.tex:798–806`. Lebesgue time translation preserves both
the energy integral and its volume normalization. A terminal time slice
does not affect these space-time norms.
-/

open MeasureTheory

namespace EinsteinRelation.Correctors
open External.AKM

/-- Translating the actual space-time field preserves its normalized energy.
Source: `paper/main.tex:798–806`. -/
theorem vectorRms_time_translate {d : ℕ} (a b c : ℝ) (U : Set (Vec d))
    (G : ℝ × Vec d → Vec d) :
    vectorRms volume (Set.Ioo (a-c) (b-c) ×ˢ U) (fun z => G (z.1+c,z.2)) =
      vectorRms volume (Set.Ioo a b ×ˢ U) G := by
  letI : Measure.IsAddHaarMeasure (volume : Measure (ℝ × Vec d)) :=
    Measure.prod.instIsAddHaarMeasure volume volume
  let T : ℝ × Vec d → ℝ × Vec d := fun z => z + (c,0)
  have hT (z : ℝ × Vec d) : T z = (z.1+c,z.2) := by
    ext <;> simp only [T, Prod.fst_add, Prod.snd_add, add_zero]
  have hTe : MeasurableEmbedding T :=
    (MeasurableEquiv.addRight (c,(0 : Vec d))).measurableEmbedding
  have hTp : MeasurePreserving T volume volume := measurePreserving_add_right volume (c,0)
  have hpre : T ⁻¹' (Set.Ioo a b ×ˢ U) = Set.Ioo (a-c) (b-c) ×ˢ U := by
    ext z
    simp only [Set.mem_preimage, hT, Set.mem_prod, Set.mem_Ioo]
    constructor <;> rintro ⟨⟨hl,hr⟩,hx⟩ <;> exact ⟨⟨by linarith, by linarith⟩,hx⟩
  have hp : MeasurePreserving T
      (volume.restrict (Set.Ioo (a-c) (b-c) ×ˢ U))
      (volume.restrict (Set.Ioo a b ×ˢ U)) := by
    simpa only [hpre] using hTp.restrict_preimage_emb hTe (Set.Ioo a b ×ˢ U)
  have hmass : volume.real (Set.Ioo (a-c) (b-c) ×ˢ U) =
      volume.real (Set.Ioo a b ×ˢ U) := by
    have h := hp.measure_preimage MeasurableSet.univ
    simp only [Set.preimage_univ, Measure.restrict_apply_univ] at h
    exact congrArg ENNReal.toReal h
  have hi := hp.integral_comp hTe (fun z => euclideanSq (G z))
  simp only [hT] at hi
  simp only [vectorRms, average_eq, measureReal_restrict_apply_univ, smul_eq_mul]
  rw [hmass, hi]

/-- The backward-cylinder energy at time `3r²` is exactly the positive-time
energy controlled by the constructed cutoff. Source: `paper/main.tex:798–806`. -/
theorem vectorRms_diffusive_backward_shift {d : ℕ} (r : ℝ)
    (G : ℝ × Vec d → Vec d) :
    vectorRms volume (cylinder d r) (fun z => G (z.1+3*r^2,z.2)) =
      vectorRms volume (Set.Ioo (2*r^2) (3*r^2) ×ˢ originBall d r) G := by
  have ht : (volume : Measure ℝ).restrict (Set.Ioc (-(r^2)) 0) =
      volume.restrict (Set.Ioo (-(r^2)) 0) := restrict_Ioo_eq_restrict_Ioc.symm
  have hp : (volume : Measure (ℝ × Vec d)).restrict (cylinder d r) =
      volume.restrict (Set.Ioo (-(r^2)) 0 ×ˢ originBall d r) := by
    rw [cylinder, Measure.volume_eq_prod, ← Measure.prod_restrict,
      ← Measure.prod_restrict, ht]
  have h := vectorRms_time_translate (2*r^2) (3*r^2) (3*r^2) (originBall d r) G
  simp only [show 2*r^2-3*r^2 = -(r^2) by ring, sub_self] at h
  unfold vectorRms at h ⊢
  rw [hp]
  exact h

end EinsteinRelation.Correctors
