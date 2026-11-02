import EinsteinRelation.Correctors.AKMParabolicIntegrability
import EinsteinRelation.Correctors.ParabolicTimeEndpoints
import Mathlib.MeasureTheory.Group.Prod

/-! # Time translation of weak parabolic solutions

Source: `paper/main.tex:788–796`. Positive-time flow cylinders are transported
to the backward cylinders of AKM without changing the energy class or weak PDE.
-/

open MeasureTheory
open scoped Topology

namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

/-- Translating time preserves the genuine weak equation, its spatial
gradient and joint measurability. Source: `paper/main.tex:788–796`. -/
theorem parabolicSolution_time_shift {d : ℕ} {K a b : ℝ}
    {A : Coefficient d K} {U : Set (Vec d)}
    {u : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    (hsol : IsParabolicSolution A (Set.Ioo a b) U u G) (c : ℝ) :
    IsParabolicSolution A (Set.Ioo (a-c) (b-c)) U
      (fun z => u (z.1+c,z.2)) (fun z => G (z.1+c,z.2)) := by
  letI : Measure.IsAddHaarMeasure (volume : Measure (ℝ × Vec d)) :=
    Measure.prod.instIsAddHaarMeasure volume volume
  let T : ℝ × Vec d → ℝ × Vec d := fun z => z + (c, 0)
  have hT (z : ℝ × Vec d) : T z = (z.1+c,z.2) := by
    ext <;> simp [T]
  have hTp : MeasurePreserving T volume volume := measurePreserving_add_right volume (c, 0)
  have hTe : MeasurableEmbedding T := (MeasurableEquiv.addRight (c, (0 : Vec d))).measurableEmbedding
  have hpre : T ⁻¹' (Set.Ioo a b ×ˢ U) = Set.Ioo (a-c) (b-c) ×ˢ U := by
    ext z
    simp only [T, Set.mem_preimage, Set.mem_prod, Set.mem_Ioo, Prod.fst_add,
      Prod.snd_add, add_zero]
    constructor <;> rintro ⟨⟨hl, hr⟩, hx⟩ <;> exact ⟨⟨by linarith, by linarith⟩, hx⟩
  have hTr : MeasurePreserving T (volume.restrict (Set.Ioo (a-c) (b-c) ×ˢ U))
      (volume.restrict (Set.Ioo a b ×ˢ U)) := by
    simpa only [hpre] using hTp.restrict_preimage_emb hTe (Set.Ioo a b ×ˢ U)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa only [Function.comp_def, hT] using
      hsol.1.comp_measurePreserving hTr
  · simpa only [Function.comp_def, hT] using
      hsol.2.1.comp_measurePreserving hTr
  · simpa only [Function.comp_def, hT] using
      hsol.2.2.1.comp_measurePreserving hTr
  · have hpre₁ : (fun t : ℝ => t+c) ⁻¹' Set.Ioo a b = Set.Ioo (a-c) (b-c) := by
      ext t
      simp only [Set.mem_preimage, Set.mem_Ioo]
      constructor <;> rintro ⟨hl, hr⟩ <;> exact ⟨by linarith, by linarith⟩
    have htime : MeasurePreserving (fun t : ℝ => t+c)
        (volume.restrict (Set.Ioo (a-c) (b-c))) (volume.restrict (Set.Ioo a b)) := by
      simpa only [hpre₁] using (measurePreserving_add_right volume c).restrict_preimage_emb
        (MeasurableEquiv.addRight c).measurableEmbedding (Set.Ioo a b)
    exact htime.quasiMeasurePreserving.ae hsol.2.2.2.1
  · intro ψ hψ hψc hψsupp
    let φ : ℝ × Vec d → ℝ := fun z => ψ (z + (-c, 0))
    have hφ : ContDiff ℝ (⊤ : ℕ∞) φ := hψ.comp (contDiff_id.add contDiff_const)
    have hφc : HasCompactSupport φ := hψc.comp_homeomorph (Homeomorph.addRight (-c, 0))
    have hφsupp : tsupport φ ⊆ interior (Set.Ioo a b) ×ˢ U := by
      have hs : tsupport φ ⊆ (fun z : ℝ × Vec d => z + (-c, 0)) ⁻¹' tsupport ψ := by
        apply closure_minimal ?_ ((isClosed_tsupport ψ).preimage (continuous_id.add continuous_const))
        intro z hz
        exact subset_tsupport ψ hz
      intro z hz
      obtain ⟨ht, hx⟩ := hψsupp (hs hz)
      simp only [interior_Ioo, Set.mem_Ioo, Prod.fst_add, Prod.snd_add, add_zero] at ht hx ⊢
      exact ⟨⟨by linarith [ht.1], by linarith [ht.2]⟩, hx⟩
    have hD (z v : ℝ × Vec d) : fderiv ℝ φ (T z) v = fderiv ℝ ψ z v := by
      dsimp only [φ]
      rw [fderiv_comp_add_right]
      have hc : T z + (-c, 0) = z := by
        ext <;> simp [T, add_assoc]
      rw [hc]
    have hid := hTr.integral_comp hTe
      (fun z => -(u z) * fderiv ℝ φ z (1, 0) +
        dot ((A z.2).mulVec (G z)) (fun j => fderiv ℝ φ z (0, unitVector j)))
    have heq := hsol.2.2.2.2 φ hφ hφc hφsupp
    rw [← hid] at heq
    have hD' (z v : ℝ × Vec d) :
        fderiv ℝ φ (z.1+c,z.2) v = fderiv ℝ ψ z v := by
      rw [← hT z]
      exact hD z v
    simpa only [hT, hD'] using heq

/-- A positive-time source cylinder has the exact final-time convention
used in AKM Theorem 8.7. Source: `paper/main.tex:788–796`. -/
theorem semigroupSolution_backward_cylinder {d : ℕ} {K : ℝ}
    {A : Coefficient d K} {g : Vec d → Vec d}
    {u : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    (hsol : IsSemigroupSolution A g u G) {t R : ℝ} (hR : 0 < R)
    (ht : R^2 < t) :
    IsParabolicSolution A (Set.Ioc (-(R^2)) 0) (originBall d R)
      (fun z => u (z.1+t,z.2)) (fun z => G (z.1+t,z.2)) := by
  apply parabolicSolution_Ioc_of_Ioo
  have h := parabolicSolution_time_shift
    (hsol.2.1 (t-R^2) t R (by linarith) (by nlinarith) hR) t
  simpa only [sub_self, sub_sub_cancel_left] using h

end EinsteinRelation.Correctors
