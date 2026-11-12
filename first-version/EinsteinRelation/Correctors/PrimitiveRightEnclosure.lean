import EinsteinRelation.Correctors.IntervalPrimitiveSupport

/-! Auxiliary integral and moment estimates; source `paper/main.tex:699–753,808–848`. -/
open MeasureTheory Filter Topology
namespace EinsteinRelation.Correctors

theorem intervalPrimitive_zero_right_enclosure {a c e t : ℝ}
    (hac : a < c) (hce : c ≤ e) {η : ℝ → ℝ} (hη : Continuous η)
    (hc : HasCompactSupport η) (hs : Function.support η ⊆ Set.Icc c e)
    (hz : (∫ s : ℝ, η s) = 0) (ht : e ≤ t) :
    (∫ s in a..t, η s) = 0 :=
  intervalPrimitive_eq_zero_of_ge_right (hac.le.trans hce) hη hc
    (hs.trans (Set.Icc_subset_Icc hac.le le_rfl)) hz ht

end EinsteinRelation.Correctors
