import EinsteinRelation.Regeneration.Coupling

/-! # Bounded killed future expectation

Source `paper/main.tex:377-403` (Step 2 and the Fubini factorization in Step 3).
The killed future integrand is the no-backtracking indicator times a bounded
future functional. Its integral over each probability fibre of the coupled
kernel is bounded by the bound of that functional. The bound holds at the actual
origin for `Q`-a.e. environment and for product-a.e. starting pair, with one
common constant. Only the bounded-test hypothesis and the probability
qualifiers of `HasProbabilityLaws` are used. No measurability or future
locality of the expectation is asserted here.
-/

open MeasureTheory
noncomputable section
attribute [local instance] Classical.propDecidable
namespace EinsteinRelation.Regeneration

/-- A bounded integrand over a probability measure has integral bounded by the
same constant; no measurability of the integrand is needed. -/
private lemma abs_integral_le_of_bounded_prob_measure {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (f : α → ℝ) {C : ℝ}
    (hf : ∀ x, |f x| ≤ C) : |∫ x, f x ∂μ| ≤ C := by
  have hf' : ∀ᵐ x ∂μ, ‖f x‖ ≤ C :=
    Filter.Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hf x
  have h := norm_integral_le_of_norm_le_const hf'
  rw [probReal_univ, mul_one, Real.norm_eq_abs] at h
  exact h

/-- Zeroing a real value off an event keeps any bound that holds for the value. -/
private lemma abs_ite_zero_le_of_abs_le {p : Prop} [Decidable p] {y C : ℝ}
    (hC : 0 ≤ C) (hy : |y| ≤ C) : |if p then y else 0| ≤ C := by
  split_ifs
  · exact hy
  · rw [abs_zero]
    exact hC

/-- Source `paper/main.tex:377-403`: the killed future expectation of a bounded
future functional is bounded by one constant `C`, at the actual origin for
`Q`-a.e. environment and at product-a.e. spatial starts. -/
theorem bounded_killed_future_expectation {d : ℕ} (Q : Measure (FieldPair d))
    [IsProbabilityMeasure Q]
    (K : CoupledQuenchedLaws d) (hK : HasProbabilityLaws Q K) (R : ℝ) (i : Fin d)
    (Φ : FutureState d i R → ℝ) (hΦ : Measurable Φ) (hb : BoundedRealTest Φ) :
    ∃ C : ℝ, 0 ≤ C ∧
    (∀ᵐ ω ∂Q, |∫ z, (if NoBacktracking R z.1 i then
      Φ ((recenterSample (0 : Vec d) z).1,z.2,
        fun x : FutureHalfSpace d i R => ((translate (0 : Vec d) (reduce ω)).1 x,
          (translate (0 : Vec d) (reduce ω)).2 x)) else 0) ∂K (0,ω)| ≤ C) ∧
    (∀ᵐ xω ∂((volume : Measure (Vec d)).prod Q), |∫ z, (if NoBacktracking R z.1 i then
      Φ ((recenterSample xω.1 z).1,z.2,
        fun x : FutureHalfSpace d i R => ((translate xω.1 (reduce xω.2)).1 x,
          (translate xω.1 (reduce xω.2)).2 x)) else 0) ∂K xω| ≤ C) := by
  -- Measurability of `Φ` is not needed for the bound.
  have hResult :
      ∃ C : ℝ, 0 ≤ C ∧
      (∀ᵐ ω ∂Q, |∫ z, (if NoBacktracking R z.1 i then
        Φ ((recenterSample (0 : Vec d) z).1,z.2,
          fun x : FutureHalfSpace d i R => ((translate (0 : Vec d) (reduce ω)).1 x,
            (translate (0 : Vec d) (reduce ω)).2 x)) else 0) ∂K (0,ω)| ≤ C) ∧
      (∀ᵐ xω ∂((volume : Measure (Vec d)).prod Q), |∫ z, (if NoBacktracking R z.1 i then
        Φ ((recenterSample xω.1 z).1,z.2,
          fun x : FutureHalfSpace d i R => ((translate xω.1 (reduce xω.2)).1 x,
            (translate xω.1 (reduce xω.2)).2 x)) else 0) ∂K xω| ≤ C) := by
    obtain ⟨C0, hC0⟩ := hb
    refine ⟨|C0|, abs_nonneg C0, ?_, ?_⟩
    · filter_upwards [hK.1] with ω hω
      apply abs_integral_le_of_bounded_prob_measure
      intro z
      exact abs_ite_zero_le_of_abs_le (abs_nonneg C0) (le_trans (hC0 _) (le_abs_self C0))
    · filter_upwards [hK.2] with xω hxω
      apply abs_integral_le_of_bounded_prob_measure
      intro z
      exact abs_ite_zero_le_of_abs_le (abs_nonneg C0) (le_trans (hC0 _) (le_abs_self C0))
  -- Keep the frozen measurability binder in the API; the uniform bound uses `hb` only.
  exact (fun (_ : Measurable Φ) => hResult) hΦ

end EinsteinRelation.Regeneration
