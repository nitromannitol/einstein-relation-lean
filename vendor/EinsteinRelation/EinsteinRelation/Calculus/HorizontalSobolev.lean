import EinsteinRelation.Correctors.HorizontalCoreDifferenceQuotient

/-! # The actual horizontal H1 generator domain

Source `paper/main.tex:240–248`. Membership means that every coordinate
translation difference quotient has an L2 limit. Uniqueness is proved before
selecting the gradient; its complete characterization and choice independence
are exported. The real bounded-core consumer identifies this gradient with the
literal spatial orbit derivatives. No density, weak spatial identification,
closed-generator theorem or paper estimate is asserted by the definition.
-/

open MeasureTheory Filter
open scoped Topology

namespace EinsteinRelation

/-- Source main.tex240–246: the infinitesimal generator of the actual L2 translation group
in coordinate i, defined by its two-sided strong difference quotient. -/
def HasHorizontalLpDerivative {d : ℕ} (Q : Measure (FieldPair d)) (hQ : IsStationary Q)
    (i : Fin d) (f g : Lp ℝ 2 Q) : Prop :=
  Filter.Tendsto (fun t : ℝ => t⁻¹ • (translationLp Q hQ (t • unitVector i) f - f))
    (𝓝[≠] (0 : ℝ)) (nhds g)

theorem HasHorizontalLpDerivative.unique {d : ℕ} {Q : Measure (FieldPair d)}
    {hQ : IsStationary Q} {i : Fin d} {f g h : Lp ℝ 2 Q}
    (hg : HasHorizontalLpDerivative Q hQ i f g)
    (hh : HasHorizontalLpDerivative Q hQ i f h) : g = h :=
  tendsto_nhds_unique hg hh

theorem HasHorizontalLpDerivative.zero {d : ℕ} (Q : Measure (FieldPair d))
    (hQ : IsStationary Q) (i : Fin d) : HasHorizontalLpDerivative Q hQ i 0 0 := by
  unfold HasHorizontalLpDerivative
  simp only [map_zero, sub_self, smul_zero]
  exact tendsto_const_nhds

theorem HasHorizontalLpDerivative.add {d : ℕ} {Q : Measure (FieldPair d)}
    {hQ : IsStationary Q} {i : Fin d} {f g f' g' : Lp ℝ 2 Q}
    (hf : HasHorizontalLpDerivative Q hQ i f f')
    (hg : HasHorizontalLpDerivative Q hQ i g g') :
    HasHorizontalLpDerivative Q hQ i (f+g) (f'+g') := by
  unfold HasHorizontalLpDerivative at *
  simpa only [map_add, add_sub_add_comm, smul_add] using hf.add hg

theorem HasHorizontalLpDerivative.smul {d : ℕ} {Q : Measure (FieldPair d)}
    {hQ : IsStationary Q} {i : Fin d} {f g : Lp ℝ 2 Q}
    (hf : HasHorizontalLpDerivative Q hQ i f g) (c : ℝ) :
    HasHorizontalLpDerivative Q hQ i (c • f) (c • g) := by
  unfold HasHorizontalLpDerivative at *
  have heq : (fun t : ℝ => t⁻¹ •
      (translationLp Q hQ (t • unitVector i) (c • f) - c • f)) =
      (fun t : ℝ => c • (t⁻¹ • (translationLp Q hQ (t • unitVector i) f - f))) := by
    funext t
    rw [map_smul, ← smul_sub, smul_comm t⁻¹ c]
  rw [heq]
  exact hf.const_smul c

/-- The source horizontal H1 domain as an actual subspace of L2: every coordinate has the
strong L2 generator derivative. No estimate or paper conclusion is part of membership. -/
def horizontalH1 {d : ℕ} (Q : Measure (FieldPair d)) (hQ : IsStationary Q) :
    Submodule ℝ (Lp ℝ 2 Q) where
  carrier := {f | ∃ g : Fin d → Lp ℝ 2 Q, ∀ i, HasHorizontalLpDerivative Q hQ i f (g i)}
  zero_mem' := ⟨fun _ => 0, HasHorizontalLpDerivative.zero Q hQ⟩
  add_mem' := by
    rintro f g ⟨df, hf⟩ ⟨dg, hg⟩
    exact ⟨fun i => df i + dg i, fun i => (hf i).add (hg i)⟩
  smul_mem' := by
    rintro c f ⟨df,hf⟩
    exact ⟨fun i => c • df i, fun i => (hf i).smul c⟩

theorem existsUnique_horizontalH1_gradient {d : ℕ} (Q : Measure (FieldPair d))
    (hQ : IsStationary Q) (f : horizontalH1 Q hQ) :
    ∃! g : Fin d → Lp ℝ 2 Q, ∀ i, HasHorizontalLpDerivative Q hQ i f (g i) := by
  obtain ⟨g, hg⟩ := f.property
  exact ⟨g, hg, fun k hk => funext fun i => (hk i).unique (hg i)⟩

noncomputable def horizontalH1Gradient {d : ℕ} (Q : Measure (FieldPair d))
    (hQ : IsStationary Q) (f : horizontalH1 Q hQ) : Fin d → Lp ℝ 2 Q :=
  Classical.choose (existsUnique_horizontalH1_gradient Q hQ f)

theorem hasHorizontalLpDerivative_horizontalH1Gradient {d : ℕ} (Q : Measure (FieldPair d))
    (hQ : IsStationary Q) (f : horizontalH1 Q hQ) (i : Fin d) :
    HasHorizontalLpDerivative Q hQ i f (horizontalH1Gradient Q hQ f i) :=
  (Classical.choose_spec (existsUnique_horizontalH1_gradient Q hQ f)).1 i

theorem horizontalH1Gradient_eq_of_hasHorizontalLpDerivative {d : ℕ}
    (Q : Measure (FieldPair d)) (hQ : IsStationary Q) (f : horizontalH1 Q hQ)
    (g : Fin d → Lp ℝ 2 Q) (hg : ∀ i, HasHorizontalLpDerivative Q hQ i f (g i)) :
    horizontalH1Gradient Q hQ f = g :=
  funext fun i => (hasHorizontalLpDerivative_horizontalH1Gradient Q hQ f i).unique (hg i)

/-- Real consumer: the actual bounded orbit-smooth core belongs to the source generator domain,
and its coordinate derivatives are the literal spatial orbit derivatives. -/
theorem IsHorizontalTest.mem_horizontalH1 {d : ℕ} (Q : Measure (FieldPair d))
    [IsProbabilityMeasure Q] (hQ : IsStationary Q) {F : FieldPair d → ℝ}
    (hF : IsHorizontalTest F) :
    (hF.memLp Q 2).toLp F ∈ horizontalH1 Q hQ := by
  refine ⟨fun i => (hF.memLp_derivative Q 2 i).toLp (horizontalDerivative i F), ?_⟩
  intro i
  exact Correctors.tendsto_horizontalCore_differenceQuotient Q hQ hF i

/-- Full characterization on the actual core, including the uniquely chosen gradient. -/
theorem IsHorizontalTest.horizontalH1Gradient_eq {d : ℕ} (Q : Measure (FieldPair d))
    [IsProbabilityMeasure Q] (hQ : IsStationary Q) {F : FieldPair d → ℝ}
    (hF : IsHorizontalTest F) :
    horizontalH1Gradient Q hQ ⟨(hF.memLp Q 2).toLp F, hF.mem_horizontalH1 Q hQ⟩ =
      fun i => (hF.memLp_derivative Q 2 i).toLp (horizontalDerivative i F) := by
  apply horizontalH1Gradient_eq_of_hasHorizontalLpDerivative
  intro i
  exact Correctors.tendsto_horizontalCore_differenceQuotient Q hQ hF i

end EinsteinRelation
