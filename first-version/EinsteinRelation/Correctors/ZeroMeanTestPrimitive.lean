import EinsteinRelation.Correctors.PrimitiveInteriorSupport
import EinsteinRelation.Correctors.SmoothIntervalPrimitive

open MeasureTheory
namespace EinsteinRelation.Correctors

/-- Source: `paper/main.tex:808–816,833–848`. A compact smooth scalar test of
zero integral has a compact smooth primitive in the same interval. -/
theorem exists_compact_primitive_of_integral_eq_zero {a b : ℝ} (hab : a < b)
    {η : ℝ → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (hηs : tsupport η ⊆ Set.Ioo a b) (hηzero : (∫ t : ℝ, η t) = 0) :
    ∃ ζ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ζ ∧ HasCompactSupport ζ ∧
      tsupport ζ ⊆ Set.Ioo a b ∧ ∀ t, deriv ζ t = η t := by
  obtain ⟨hs, hc⟩ := intervalPrimitive_tsupport_subset_interior hab hη.continuous hηc hηs hηzero
  exact ⟨fun t => ∫ s in a..t, η s, intervalPrimitive_contDiff hη a, hc, hs,
    deriv_intervalPrimitive hη.continuous a⟩

end EinsteinRelation.Correctors
