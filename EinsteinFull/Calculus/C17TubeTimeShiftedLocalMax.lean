import EinsteinFull.Calculus.C17TubeScaledLocalMax
import EinsteinFull.Calculus.C18TubeCaloricTimeTranslation

open EinsteinRelation MeasureTheory Filter EinsteinFull.External.Source.GMP
open scoped Topology

namespace EinsteinFull.Calculus

/-- A centered local maximum estimate holds at an arbitrary time origin. -/
theorem c17_time_shifted_scaled_local_max_of_unit_bound
 (d : ℕ) (hd : 2 ≤ d) (κ C : ℝ) (hκ : 0 < κ) (hC : 0 < C)
 (hunit : ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
   IsUniformlyElliptic κ ρ α →
   ∀ (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d),
   IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1) u G →
   essSup (fun z => ENNReal.ofReal |u z|)
    (volume.restrict (Set.Ioo (-1/4:ℝ) (1/4) ×ˢ sourceBall 0 (1/2))) ≤
   ENNReal.ofReal (C * Real.sqrt
    (∫ z in Set.Ioo (-1:ℝ) 1 ×ˢ sourceBall 0 1, |u z|^2)))
 (t0 : ℝ) (y : Vec d) (r : ℝ) (hr : 0 < r)
 (ρ : Vec d → ℝ) (α : Vec d → Mat d)
 (hell : IsUniformlyElliptic κ ρ α)
 (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
 (hcal : IsWeightedCaloric ρ α (Set.Ioo (t0-r^2) (t0+r^2)) (sourceBall y r) u G) :
 essSup (fun z => ENNReal.ofReal |u z|)
  (volume.restrict (Set.Ioo (t0-(r^2)/4) (t0+r^2/4) ×ˢ sourceBall y (r/2))) ≤
 ENNReal.ofReal (C * Real.sqrt
  ((r^(d+2))⁻¹ * ∫ z in Set.Ioo (t0-r^2) (t0+r^2) ×ˢ sourceBall y r, |u z|^2)) := by
  have hc := c18_weighted_caloric_time_translate ρ α (-r^2) (r^2) t0
    (sourceBall y r) u G (by simpa only [← sub_eq_add_neg] using hcal)
  have h := c17_scaled_local_max_of_unit_bound d hd κ C hκ hC hunit y r hr ρ α hell _ _ hc
  have hi := c18_shifted_cylinder_integral t0 (-r^2) (r^2) (sourceBall y r)
    (fun z => |u z|^2)
  simp only [← sub_eq_add_neg] at hi
  rw [hi] at h
  have he : MeasurableEmbedding (fun z : ℝ × Vec d => (z.1+t0, z.2)) := by
    convert (Homeomorph.addRight (t0, (0 : Vec d))).measurableEmbedding using 1
    funext z
    rcases z with ⟨t, x⟩
    simp
  have hm := c13_time_translation_measurePreserving (d := d) t0
    (t0-(r^2)/4) (t0+r^2/4) (sourceBall y (r/2))
  have hs := he.essSup_map_measure (g := fun z => ENNReal.ofReal |u z|)
    (μ := volume.restrict (Set.Ioo (-(r^2)/4) (r^2/4) ×ˢ sourceBall y (r/2)))
  have hm' : Measure.map (fun z : ℝ × Vec d => (z.1+t0, z.2))
      (volume.restrict (Set.Ioo (-(r^2)/4) (r^2/4) ×ˢ sourceBall y (r/2))) =
      volume.restrict (Set.Ioo (t0-(r^2)/4) (t0+r^2/4) ×ˢ sourceBall y (r/2)) := by
    convert hm.map_eq using 1 <;> congr 3 <;> ring
  rw [hm'] at hs
  have hf : ((fun z => ENNReal.ofReal |u z|) ∘
      (fun z : ℝ × Vec d => (z.1+t0, z.2))) =
      (fun z => ENNReal.ofReal |u (t0+z.1, z.2)|) := by
    funext z
    simp only [Function.comp_apply, add_comm]
  rw [hf] at hs
  exact hs.trans_le h

end EinsteinFull.Calculus
