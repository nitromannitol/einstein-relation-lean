import EinsteinRelation.Correctors.ParabolicCylinderEnergy
import Mathlib.MeasureTheory.Integral.Prod

/-! # Averaging a gradient estimate over time

Source: `paper/main.tex:798–806`. An a.e. time-slice RMS bound gives
the same bound on its normalized cylinder. This uses the actual integrable
energy and does not select a pointwise gradient representative.
-/

open MeasureTheory

namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

/-- A uniform a.e. time-slice bound passes to the product energy RMS.
The time measure is normalized to mass one.
Source: `paper/main.tex:798–806`. -/
theorem vectorRms_prod_le_of_slice_bounds
    {T X : Type*} [MeasurableSpace T] [MeasurableSpace X]
    (μ : Measure T) [IsProbabilityMeasure μ] (ν : Measure X) [SFinite ν]
    {d : ℕ} (G : T × X → Vec d)
    (hint : Integrable (fun z => euclideanSq (G z)) (μ.prod ν))
    {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ᵐ t ∂μ, vectorRms ν Set.univ (fun x => G (t,x)) ≤ B) :
    vectorRms (μ.prod ν) Set.univ G ≤ B := by
  have hmass : (μ.prod ν).real Set.univ = ν.real Set.univ := by
    simp only [Measure.real, ← Set.univ_prod_univ, Measure.prod_prod, measure_univ, one_mul]
  have hmean : (⨍ z, euclideanSq (G z) ∂μ.prod ν) =
      ∫ t, ⨍ x, euclideanSq (G (t,x)) ∂ν ∂μ := by
    rw [average_eq,hmass,smul_eq_mul,integral_prod _ hint]
    simp only [average_eq,smul_eq_mul]
    rw [integral_const_mul]
  have havg : ∀ᵐ t ∂μ, (⨍ x, euclideanSq (G (t,x)) ∂ν) ≤ B^2 := by
    filter_upwards [hb] with t ht
    apply (Real.sqrt_le_iff.mp ?_).2
    simpa only [vectorRms,Measure.restrict_univ] using ht
  have hI : Integrable (fun t => ⨍ x, euclideanSq (G (t,x)) ∂ν) μ := by
    simpa only [average_eq,smul_eq_mul] using
      hint.integral_prod_left.const_mul ((ν.real Set.univ)⁻¹)
  have hle := integral_mono_ae hI (integrable_const (B^2)) havg
  change Real.sqrt (⨍ z, euclideanSq (G z) ∂(μ.prod ν).restrict Set.univ) ≤ B
  rw [Measure.restrict_univ,hmean]
  apply Real.sqrt_le_iff.mpr
  exact ⟨hB,by simpa using hle⟩

/-- Averaging the actual unit-ball slices costs no volume factor because
the time interval has length one. Source: `paper/main.tex:798–806`. -/
theorem unit_cylinder_vectorRms_le_of_slices
    {d : ℕ} (G : ℝ × Vec d → Vec d)
    (hG : MemLp (fun z => euclideanNorm (G z)) 2
      (volume.restrict (Set.Ioo (2 : ℝ) 3 ×ˢ originBall d 1)))
    {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ᵐ t ∂volume.restrict (Set.Ioo (2 : ℝ) 3),
      vectorRms volume (originBall d 1) (fun x => G (t,x)) ≤ B) :
    vectorRms volume (Set.Ioo (2 : ℝ) 3 ×ˢ originBall d 1) G ≤ B := by
  let μ : Measure ℝ := volume.restrict (Set.Ioo 2 3)
  let ν : Measure (Vec d) := volume.restrict (originBall d 1)
  letI : IsProbabilityMeasure μ := ⟨by norm_num [μ,Measure.restrict_apply_univ,Real.volume_Ioo]⟩
  have hint : Integrable (fun z => euclideanSq (G z)) (μ.prod ν) := by
    simpa only [μ,ν,Measure.prod_restrict,TimeChange.euclideanSq_eq_sq_euclideanNorm]
      using hG.integrable_sq
  have h := vectorRms_prod_le_of_slice_bounds μ ν G hint hB (by
    simpa only [μ,ν,vectorRms,Measure.restrict_univ] using hb)
  simpa only [μ,ν,Measure.prod_restrict,vectorRms,Measure.restrict_univ] using h

end EinsteinRelation.Correctors
