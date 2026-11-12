import EinsteinRelation.Correctors.ParabolicSliceAverage
import EinsteinRelation.Correctors.AKMRandomRadiusCylinderMoments

/-! # The good-radius comparison on a unit time cylinder

Source: `paper/main.tex:798–806`. Averaging the corrected Remark 8.8
conclusion over a unit interval keeps its random-radius factor and avoids
prescribed-time evaluation of the weak gradient.
-/

open MeasureTheory

namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

/-- The actual shifted unit cylinder remains in strictly positive time.
Source: `paper/main.tex:798–806`. -/
theorem semigroupSolution_shifted_unit_cylinder
    {d : ℕ} {K : ℝ} {A : Coefficient d K} {g : Vec d → Vec d}
    {u : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    (hsol : IsSemigroupSolution A g u G) {r : ℝ} (hr : 1 ≤ r) :
    IsParabolicSolution A (Set.Ioo (2 : ℝ) 3) (originBall d 1)
      (fun z => u (z.1+(3*r^2-3),z.2))
      (fun z => G (z.1+(3*r^2-3),z.2)) := by
  have hr21 : 1 ≤ r^2 := by nlinarith
  have h := parabolicSolution_time_shift
    (hsol.2.1 (2+(3*r^2-3)) (3+(3*r^2-3)) 1
      (by nlinarith only [hr21]) (by linarith) zero_lt_one) (3*r^2-3)
  simpa only [add_sub_cancel_right] using h

/-- The a.e. time-slice comparison controls the unit-cylinder gradient of
the same actual flow. No value of the gradient at a single time is used.
Source: `paper/main.tex:798–806`. -/
theorem semigroupSolution_good_radius_unit_cylinder_le
    {d : ℕ} {K : ℝ} {A : Coefficient d K} {g : Vec d → Vec d}
    {u : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    (hsol : IsSemigroupSolution A g u G) {r X L : ℝ}
    (hr : 1 ≤ r) (hX : 1 ≤ X) (hL : 0 ≤ L)
    (hcomp : ∀ᵐ τ ∂volume.restrict (Set.Ioo (-((2*X)^2)/4) 0),
      vectorRms volume (originBall d 1) (fun x => G (τ+3*r^2,x)) ≤
        L * X^((d : ℝ)/2) * vectorRms volume
          (Set.Ioo (2*r^2) (3*r^2) ×ˢ originBall d r) G) :
    vectorRms volume (Set.Ioo (2 : ℝ) 3 ×ˢ originBall d 1)
      (fun z => G (z.1+(3*r^2-3),z.2)) ≤
        L * X^((d : ℝ)/2) * vectorRms volume
          (Set.Ioo (2*r^2) (3*r^2) ×ˢ originBall d r) G := by
  have hsub : Set.Ioo (-1 : ℝ) 0 ⊆ Set.Ioo (-((2*X)^2)/4) 0 := by
    intro t ht
    exact ⟨by nlinarith only [ht.1,hX,sq_nonneg (X-1)],ht.2⟩
  have hc := ae_restrict_of_ae_restrict_of_subset hsub hcomp
  have hpre : (fun t : ℝ => t+(-3)) ⁻¹' Set.Ioo (-1 : ℝ) 0 = Set.Ioo (2 : ℝ) 3 := by
    ext t
    simp only [Set.mem_preimage,Set.mem_Ioo]
    constructor <;> rintro ⟨hl,hu⟩ <;> exact ⟨by linarith,by linarith⟩
  have htime : MeasurePreserving (fun t : ℝ => t+(-3))
      (volume.restrict (Set.Ioo (2 : ℝ) 3))
      (volume.restrict (Set.Ioo (-1 : ℝ) 0)) := by
    simpa only [hpre] using (measurePreserving_add_right volume (-3 : ℝ)).restrict_preimage_emb
      (MeasurableEquiv.addRight (-3 : ℝ)).measurableEmbedding (Set.Ioo (-1 : ℝ) 0)
  have hc' := htime.quasiMeasurePreserving.ae hc
  have ht (t : ℝ) : t+(-3)+3*r^2 = t+(3*r^2-3) := by ring
  apply unit_cylinder_vectorRms_le_of_slices _
    (semigroupSolution_shifted_unit_cylinder hsol hr).2.2.1
    (mul_nonneg (mul_nonneg hL (Real.rpow_nonneg (zero_le_one.trans hX) _))
      (Real.sqrt_nonneg _))
  simpa only [ht] using hc'

end EinsteinRelation.Correctors
