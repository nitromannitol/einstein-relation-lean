import EinsteinRelation.Correctors.IntervalPrimitiveSupport

/-! Auxiliary integral and moment estimates; source `paper/main.tex:699–753,808–848`. -/
open MeasureTheory Filter Topology
namespace EinsteinRelation.Correctors

theorem intervalPrimitive_zero_left_enclosure {a c e t : ℝ}
    (hac : a < c) {η : ℝ → ℝ} (hη : Continuous η)
    (hs : Function.support η ⊆ Set.Icc c e) (ht : t ≤ c) :
    (∫ s in a..t, η s) = 0 := by
  -- support in [c, e] kills η strictly left of c
  have hlt : ∀ x, x < c → η x = 0 := by
    intro x hx
    by_contra h
    have hxI : x ∈ Set.Icc c e := hs (Function.mem_support.mpr h)
    exact absurd hxI.1 (not_le.mpr hx)
  -- continuity transfers this vanishing to the point c itself
  have hc : η c = 0 := by
    have h1 : Tendsto η (𝓝[<] c) (𝓝 (η c)) :=
      (hη.tendsto c).mono_left nhdsWithin_le_nhds
    have h2 : Tendsto η (𝓝[<] c) (𝓝 0) := by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with x hx
      exact (hlt x hx).symm
    exact tendsto_nhds_unique h1 h2
  have hle : ∀ x, x ≤ c → η x = 0 := by
    intro x hx
    rcases hx.lt_or_eq with h | h
    · exact hlt x h
    · rw [h]
      exact hc
  -- the integrand vanishes on the whole interval between a and t, since both sit left of c
  have h0 : (∫ s in a..t, η s) = ∫ s in a..t, (0 : ℝ) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rcases le_total a t with hat | hta
    · rw [Set.uIcc_of_le hat] at hx
      exact hle x (hx.2.trans ht)
    · rw [Set.uIcc_of_ge hta] at hx
      exact hle x (hx.2.trans hac.le)
  rw [h0]
  simp

end EinsteinRelation.Correctors
