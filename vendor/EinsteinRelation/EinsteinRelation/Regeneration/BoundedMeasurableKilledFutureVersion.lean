import EinsteinRelation.Regeneration.KilledFutureKernel
import EinsteinRelation.Regeneration.BoundedKilledFutureExpectation

/-! # Globally bounded measurable killed future version

Source `paper/main.tex:377–403`, with the killed future expectation `B_Φ` at lines 387–390.
`exists_measurable_killed_future_expectation` gives a jointly measurable representative `B₀`
that equals the actual kernel integral at the origin for `Q`-a.e. `ω` and for product-a.e.
`(y, ω)`. `bounded_killed_future_expectation` gives one constant `C` bounding those actual
integrals on the same two a.e. sets. Clipping `B₀` to `[-C, C]` yields an everywhere bounded
measurable representative. A value already in `[-C, C]` is unchanged by the clip, so both
identities survive. No product-a.e. statement is transferred to the origin, and no external
premise is added.
-/

open MeasureTheory
open scoped NNReal ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable

namespace EinsteinRelation.Regeneration

/-- Clipping to `[-C, C]` leaves a real value that already lies in `[-C, C]` unchanged. -/
private lemma clipToBound_eq_of_abs_le (x C : ℝ) (hx : |x| ≤ C) :
    max (-C) (min x C) = x := by
  obtain ⟨hlo, hhi⟩ := abs_le.mp hx
  rw [min_eq_left hhi, max_eq_right hlo]

/-- Clipping to `[-C, C]` produces a value bounded by `C` whenever `0 ≤ C`. -/
private lemma abs_clipToBound_le (x C : ℝ) (hC : 0 ≤ C) :
    |max (-C) (min x C)| ≤ C := by
  rw [abs_le]
  exact ⟨le_max_left _ _, max_le (by linarith) (min_le_right _ _)⟩

/-- Source `paper/main.tex:377–403`: the killed future expectation of a bounded future
functional has a representative that is measurable and bounded everywhere by one constant
`C`. The representative equals the actual kernel integral at the origin for `Q`-a.e. `ω`,
and for `volume.prod Q`-a.e. `(y, ω)`. -/
theorem exists_globally_bounded_measurable_killed_future_version {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q] (K : CoupledQuenchedLaws d)
    (hK : HasProbabilityLaws Q K) (R : ℝ) (i : Fin d)
    (Φ : FutureState d i R → ℝ) (hΦ : Measurable Φ) (hb : BoundedRealTest Φ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ B : Vec d × FieldPair d → ℝ, Measurable B ∧
    (∀ p, |B p| ≤ C) ∧
    (∀ᵐ ω ∂Q, B (0,ω) = ∫ z, (if NoBacktracking R z.1 i then
      Φ ((recenterSample (0 : Vec d) z).1,z.2,fun y : FutureHalfSpace d i R =>
        ((translate (0 : Vec d) (reduce ω)).1 y,(translate (0 : Vec d) (reduce ω)).2 y)) else 0)
        ∂K (0,ω)) ∧
    B =ᵐ[((volume : Measure (Vec d)).prod Q)] (fun p => ∫ z, (if NoBacktracking R z.1 i then
      Φ ((recenterSample p.1 z).1,z.2,fun y : FutureHalfSpace d i R =>
        ((translate p.1 (reduce p.2)).1 y,(translate p.1 (reduce p.2)).2 y)) else 0) ∂K p) := by
  obtain ⟨B0, hB0m, hB0o, hB0p⟩ :=
    exists_measurable_killed_future_expectation Q K hK R i Φ hΦ hb
  obtain ⟨C, hC0, hCo, hCp⟩ := bounded_killed_future_expectation Q K hK R i Φ hΦ hb
  refine ⟨C, hC0, fun p => max (-C) (min (B0 p) C),
    measurable_const.max (hB0m.min measurable_const), ?_, ?_, ?_⟩
  · intro p
    exact abs_clipToBound_le (B0 p) C hC0
  · filter_upwards [hB0o, hCo] with ω hω hCω
    show max (-C) (min (B0 (0, ω)) C) = _
    rw [hω]
    exact clipToBound_eq_of_abs_le _ C hCω
  · filter_upwards [hB0p, hCp] with xω hω hCω
    show max (-C) (min (B0 xω) C) = _
    rw [hω]
    exact clipToBound_eq_of_abs_le _ C hCω

end EinsteinRelation.Regeneration
