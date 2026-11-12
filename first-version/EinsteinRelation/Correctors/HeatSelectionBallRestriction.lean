import EinsteinRelation.External.AKMCorrectorOscillation

/-! Source: `paper/main.tex:722,756`. Restrict the existing heat-selection
predicate to the manuscript's Euclidean balls. -/
open MeasureTheory Filter Topology
namespace EinsteinRelation.Correctors
open External.AKM HeatSelectedSkewMeaning

/-- The canonical heat-selection predicate on ambient coordinate balls
implies the source predicate on Euclidean balls by restriction. -/
theorem isHeatSelectedFluxGradient_of_iterated {d : ℕ}
    (g : Vec d → Vec d) (ω : FieldPair d)
    (F : FieldPair d → Fin d → Fin d → Fin d → ℝ)
    (h : IsIteratedAKMHeatGradientAt g ω F) :
    IsHeatSelectedFluxGradient g (fun j k x l => F (translate x ω) j k l) := by
  intro j k l R
  have hsub : ball (0 : Vec d) ((R : ℝ) + 1) ⊆
      Metric.ball (0 : Vec d) ((R : ℝ) + 1) := by
    intro x hx
    have hnorm : ‖x‖ ≤ euclideanNorm x := by
      refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr fun i => ?_
      rw [Real.norm_eq_abs]
      have hsq : x i ^ 2 ≤ euclideanSq x := by
        unfold euclideanSq dot
        rw [sq]
        exact Finset.single_le_sum (fun j _ => mul_self_nonneg (x j)) (Finset.mem_univ i)
      exact Real.abs_le_sqrt hsq
    rw [Metric.mem_ball, dist_zero_right]
    exact hnorm.trans_lt (by simpa only [ball, Set.mem_setOf_eq, sub_zero] using hx)
  have hm := Measure.restrict_mono_set (volume : Measure (Vec d)) hsub
  have hsrc := h j k l R
  simp only [Nat.cast_add, Nat.cast_one] at hsrc
  refine ⟨fun m n => ae_mono hm (hsrc.1 m n),
    fun m n => (hsrc.2.1 m n).mono_measure hm,
    hsrc.2.2.1.mono_measure hm, ?_⟩
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsrc.2.2.2
    (fun _ => zero_le _) ?_
  intro mn
  exact eLpNorm_mono_measure _ hm

end EinsteinRelation.Correctors
