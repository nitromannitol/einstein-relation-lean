import EinsteinRelation.Correctors.TemporalL2Contraction
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Haar.Unique

open MeasureTheory
namespace EinsteinRelation.Correctors

/-- Extending by zero in time and convolving by a probability density bounds
the literal finite-interval temporal average. Source: `paper/main.tex:798–806`. -/
theorem finite_temporal_convolution_L2_contraction {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [SFinite ν] {a b : ℝ} {f : ℝ × X → ℝ}
    (hf : MemLp f 2 ((volume.restrict (Set.Ioo a b)).prod ν))
    {ρ : ℝ → ℝ} (hρ : Continuous ρ) (hρc : HasCompactSupport ρ)
    (hρ0 : ∀ s, 0 ≤ ρ s) (hρ1 : (∫ s, ρ s) = 1) :
    MemLp (fun z : ℝ × X => ∫ s in Set.Ioo a b, ρ (z.1-s) * f (s,z.2)) 2 (volume.prod ν) ∧
      eLpNorm (fun z : ℝ × X => ∫ s in Set.Ioo a b, ρ (z.1-s) * f (s,z.2)) 2 (volume.prod ν) ≤
        eLpNorm f 2 ((volume.restrict (Set.Ioo a b)).prod ν) := by
  let I := Set.Ioo a b
  let S : Set (ℝ × X) := I ×ˢ Set.univ
  let F : ℝ × X → ℝ := S.indicator f
  have hSm : MeasurableSet S := measurableSet_Ioo.prod MeasurableSet.univ
  have hp : (volume.prod ν).restrict S = (volume.restrict I).prod ν := by
    simp only [S,← Measure.prod_restrict,Measure.restrict_univ]
  have hF : MemLp F 2 (volume.prod ν) := by
    apply (memLp_indicator_iff_restrict hSm).mpr
    rwa [hp]
  have hFn : eLpNorm F 2 (volume.prod ν) = eLpNorm f 2 ((volume.restrict I).prod ν) := by
    rw [eLpNorm_indicator_eq_eLpNorm_restrict hSm,hp]
  have heq (z : ℝ × X) : (∫ s, ρ s * F (z.1-s,z.2)) =
      ∫ s in I, ρ (z.1-s) * f (s,z.2) := by
    calc
      _ = ∫ s, ρ (z.1-s) * F (s,z.2) := by
        have he := integral_sub_left_eq_self (fun s => ρ s * F (z.1-s,z.2)) volume z.1
        simpa only [sub_sub_cancel] using he.symm
      _ = ∫ s, I.indicator (fun s => ρ (z.1-s) * f (s,z.2)) s := by
        apply integral_congr_ae
        filter_upwards with s
        by_cases hs : s ∈ I
        · have hp : (s,z.2) ∈ S := ⟨hs,Set.mem_univ _⟩
          simp only [F,Set.indicator_of_mem hp,Set.indicator_of_mem hs]
        · have hp : (s,z.2) ∉ S := fun h => hs h.1
          simp only [F,Set.indicator_of_notMem hp,Set.indicator_of_notMem hs,mul_zero]
      _ = _ := integral_indicator measurableSet_Ioo
  obtain ⟨hm,hn⟩ := temporal_convolution_L2_contraction ν hF hρ hρc hρ0 hρ1
  simpa only [heq,hFn] using And.intro hm hn

end EinsteinRelation.Correctors
