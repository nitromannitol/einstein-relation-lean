import EinsteinFull.Calculus.C13TubeWeightedEnergyTrace

open EinsteinRelation MeasureTheory EinsteinFull.External.Source.GMP
open scoped Topology

namespace EinsteinFull.Calculus

/-- A weighted caloric field remains caloric when its time coordinate is centered. -/
theorem c18_weighted_caloric_time_translate {d : ℕ}
    (ρ : Vec d → ℝ) (α : Vec d → Mat d)
    (a b t0 : ℝ) (U : Set (Vec d))
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hcal : IsWeightedCaloric ρ α (Set.Ioo (t0+a) (t0+b)) U u G) :
    IsWeightedCaloric ρ α (Set.Ioo a b) U
      (fun z => u (t0+z.1,z.2)) (fun z => G (t0+z.1,z.2)) := by
  have h := c13_weighted_caloric_time_translation t0 (t0+a) (t0+b) U ρ α u G hcal
  simpa only [add_sub_cancel_left, add_sub_cancel_right, add_comm] using h

/-- Centering time is reversible for the weighted caloric predicate. -/
theorem c18_weighted_caloric_time_translate_iff {d : ℕ}
    (ρ : Vec d → ℝ) (α : Vec d → Mat d)
    (a b t0 : ℝ) (U : Set (Vec d))
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d) :
    IsWeightedCaloric ρ α (Set.Ioo (t0+a) (t0+b)) U u G ↔
    IsWeightedCaloric ρ α (Set.Ioo a b) U
      (fun z => u (t0+z.1,z.2)) (fun z => G (t0+z.1,z.2)) := by
  constructor
  · exact c18_weighted_caloric_time_translate ρ α a b t0 U u G
  · intro h
    have h' := c13_weighted_caloric_time_translation (-t0) a b U ρ α
      (fun z => u (t0+z.1,z.2)) (fun z => G (t0+z.1,z.2)) h
    simpa only [sub_neg_eq_add, add_comm, add_neg_cancel_comm_assoc] using h'

/-- The same centering applies to a source-ball cylinder. -/
theorem c18_weighted_caloric_sourceBall_time_translate {d : ℕ}
    (ρ : Vec d → ℝ) (α : Vec d → Mat d)
    (a b t0 : ℝ) (y : Vec d) (R : ℝ)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hcal : IsWeightedCaloric ρ α (Set.Ioo (t0+a) (t0+b)) (sourceBall y R) u G) :
    IsWeightedCaloric ρ α (Set.Ioo a b) (sourceBall y R)
      (fun z => u (t0+z.1,z.2)) (fun z => G (t0+z.1,z.2)) :=
  c18_weighted_caloric_time_translate ρ α a b t0 (sourceBall y R) u G hcal

/-- Translation of the literal Lebesgue integral on a time-space cylinder. -/
theorem c18_shifted_cylinder_integral {d : ℕ} (t0 a b : ℝ)
    (U : Set (Vec d)) (f : ℝ × Vec d → ℝ) :
    (∫ z in Set.Ioo a b ×ˢ U, f (t0 + z.1, z.2)) =
      ∫ z in Set.Ioo (t0+a) (t0+b) ×ˢ U, f z := by
  have hm := c13_time_translation_measurePreserving t0 (t0+a) (t0+b) U
  have he : MeasurableEmbedding (fun z : ℝ × Vec d => (z.1+t0, z.2)) := by
    convert (Homeomorph.addRight (t0, (0 : Vec d))).measurableEmbedding using 1
    funext z
    rcases z with ⟨t, x⟩
    simp
  have hi := hm.integral_comp he f
  simpa only [add_sub_cancel_left, add_sub_cancel_right, add_comm] using hi

end EinsteinFull.Calculus
