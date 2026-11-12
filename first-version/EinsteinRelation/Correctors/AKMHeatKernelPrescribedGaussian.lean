import EinsteinRelation.Correctors.AKMHeatKernelTranslatedGaussian
import EinsteinRelation.Correctors.ParabolicSpatialTranslation
import EinsteinRelation.Correctors.ParabolicPrescribedScalarEnergy

open MeasureTheory
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

/-- At every positive time the actual weak kernel gradient has Gaussian
local energy, uniformly over spatial centers and initial points. Source:
AKM E.1 (E.7), local energy estimate; `paper/main.tex:787–806,850`. -/
theorem akm_heatKernel_prescribed_translated_gradient_energy
    {d : ℕ} {K : ℝ} (hK : 0 < K) {A : Coefficient d K}
    {P : ℝ → Vec d → Vec d → ℝ}
    {X Y Z : ℝ → Vec d → Vec d → Vec d}
    {H : ℝ → Vec d → Vec d → Mat d} {C : ℝ → ℝ}
    (hP : HeatKernelProperties A P X Y H C)
    (hZsol : ∀ y, IsFundamentalSolution A y
      (fun z => P z.1 z.2 y) (fun z => Z z.1 z.2 y))
    (hZw : ∀ y t, 0 < t → HasWeakGradient Set.univ
      (fun x => P t x y) (fun x => Z t x y))
    {t R : ℝ} (ht : 0 < t) (hR : 0 < R) :
    ∃ D κ : ℝ, 0 ≤ D ∧ 0 < κ ∧ ∀ v y : Vec d,
      MemLp (fun x => euclideanNorm (Z t (v+x) y)) 2
        (volume.restrict (originBall d R)) ∧
      (∫ x in originBall d R, euclideanNorm (Z t (v+x) y)^2) ≤
        D * Real.exp (-(2*κ) * euclideanSq (y-v)) := by
  obtain ⟨E,hE,henergy⟩ := parabolicFamily_prescribed_local_scalar_energy hK ht hR
  obtain ⟨D,κ,hD,hκ,hscalar⟩ := akm_heatKernel_translated_scalar_gaussian_energy hK hP
    (by positivity : 0 < t/4) (by linarith : t/4 < 5*t/4) (by positivity : 0 < 4*R)
  refine ⟨E*D,κ,mul_nonneg hE hD,hκ,?_⟩
  intro v y
  have hc : ContinuousOn (fun z : ℝ × Vec d => P z.1 (v+z.2) y)
      (Set.Ioi 0 ×ˢ Set.univ) :=
    hP.1.comp ((continuous_fst.prodMk
      ((continuous_const.add continuous_snd).prodMk continuous_const)).continuousOn)
      (fun z hz => ⟨hz.1,Set.mem_univ _⟩)
  have hu : MemLp (fun x => P t (v+x) y) 2 (volume.restrict (originBall d R)) :=
    ((akm_heatKernel_slice_memLp hK hP ht y).comp_measurePreserving
      (measurePreserving_add_left volume v)).mono_measure Measure.restrict_le_self
  have hw : HasWeakGradient Set.univ (fun x => P t (v+x) y) (fun x => Z t (v+x) y) := by
    simpa only [Set.preimage_univ] using HasWeakGradient.translated (hZw y t ht) v
  obtain ⟨hL,hb⟩ := henergy (translateCoefficient v A)
    (fun z => P z.1 (v+z.2) y) (fun z => Z z.1 (v+z.2) y)
    (fun x => Z t (v+x) y) hc (parabolicFamily_translate_space (hZsol y).1 v) hu hw
  exact ⟨hL,hb.trans (by simpa only [mul_assoc] using
    mul_le_mul_of_nonneg_left (hscalar v y) hE)⟩

end EinsteinRelation.Correctors
