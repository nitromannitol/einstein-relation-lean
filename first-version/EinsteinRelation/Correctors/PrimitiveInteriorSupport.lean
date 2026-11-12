import EinsteinRelation.Correctors.PrimitiveLeftEnclosure
import EinsteinRelation.Correctors.PrimitiveRightEnclosure
import EinsteinRelation.Correctors.CompactIntervalEnclosure

/-! Compact interior support of a zero-mean primitive; source `paper/main.tex:808–816,833–848`. -/
open MeasureTheory
namespace EinsteinRelation.Correctors

theorem intervalPrimitive_tsupport_subset_interior {a b : ℝ} (hab : a < b)
    {η : ℝ → ℝ} (hη : Continuous η) (hc : HasCompactSupport η)
    (hs : tsupport η ⊆ Set.Ioo a b) (hz : (∫ t : ℝ, η t) = 0) :
    tsupport (fun t => ∫ s in a..t, η s) ⊆ Set.Ioo a b ∧
      HasCompactSupport (fun t => ∫ s in a..t, η s) := by
  obtain ⟨c, e, hac, hce, heb, hsupport⟩ := compact_subset_inner_Icc hab hc hs
  have hs' : Function.support η ⊆ Set.Icc c e := (subset_tsupport η).trans hsupport
  have hp : tsupport (fun t => ∫ s in a..t, η s) ⊆ Set.Icc c e := by
    apply closure_minimal ?_ isClosed_Icc
    intro t ht
    constructor
    · by_contra h
      exact ht (intervalPrimitive_zero_left_enclosure hac hη hs' (le_of_not_ge h))
    · by_contra h
      exact ht (intervalPrimitive_zero_right_enclosure hac hce hη hc hs' hz
        (le_of_not_ge h))
  exact ⟨hp.trans (fun _ h => ⟨hac.trans_le h.1, h.2.trans_lt heb⟩),
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) hp⟩

end EinsteinRelation.Correctors
