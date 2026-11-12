import EinsteinRelation.Regeneration.SpatialRecenterEquiv

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
noncomputable section
namespace EinsteinRelation.Regeneration

/-- Source `paper/main.tex:406–408`: translating actual paths preserves the deterministic restart identity. -/
theorem deterministicRestartAt_conjugate_spatial {d : ℕ}
    (Δ : ℝ≥0) (K : CoupledQuenchedLaws d) (a x : Vec d) (ω : FieldPair d)
    (hr : DeterministicRestartAt Δ K (a + x, ω)) :
    DeterministicRestartAt Δ
      ((K.comap (fun p : Vec d × FieldPair d => (a + p.1, p.2))
        ((measurable_const.add measurable_fst).prodMk measurable_snd)).map
          (recenterSampleEquiv a)) (x, ω) := by
  let e := recenterSampleEquiv a
  intro n H Φ hH hbH hΦ hbΦ
  obtain ⟨B, hB⟩ := hbH
  obtain ⟨C, hC⟩ := hbΦ
  have h := hr n (fun z => H (e z)) (fun z => Φ (e z))
    (measurable_finiteHistory_comp_recenter Δ n a H hH) ⟨B, fun z => hB _⟩
    (hΦ.comp e.measurable) ⟨C, fun z => hC _⟩
  dsimp only [e] at h
  simp only [Kernel.map_apply _ (recenterSampleEquiv a).measurable,
    Kernel.comap_apply, integral_map_equiv]
  convert h using 1
  apply integral_congr_ae
  filter_upwards [] with z
  have hz : a + ((recenterSampleEquiv a) z).1 ((n : ℝ≥0) * Δ) =
      z.1 ((n : ℝ≥0) * Δ) := by
    change a + (z.1 ((n : ℝ≥0) * Δ) - a) = _
    abel
  simp only [hz]

end EinsteinRelation.Regeneration
