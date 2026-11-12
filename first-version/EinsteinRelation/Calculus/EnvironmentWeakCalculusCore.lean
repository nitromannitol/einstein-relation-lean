import EinsteinRelation.Calculus.EnvironmentWeakCalculus

/-! # Orbit-core tests are horizontally smooth

Source `paper/main.tex:240–248`. Every bounded smooth orbit-core test (`IsHorizontalTest`) is a
horizontally smooth test in the L²(Q) generator sense. Coordinate derivatives of an orbit-core
test are again orbit-core tests, with orbit `x ↦ ∂ᵢ(orbit F ω) x`. Their iterates therefore have
the literal spatial orbit derivatives as L² generators, and the required bounds are inherited
from the bounded iterates of the original test.
-/

open MeasureTheory

noncomputable section
namespace EinsteinRelation

/-- A coordinate derivative of a smooth function is smooth. -/
private theorem contDiff_coordinateDerivative_orbit {d : ℕ} {f : Vec d → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (i : Fin d) :
    ContDiff ℝ (⊤ : ℕ∞) (coordinateDerivative i f) := by
  show ContDiff ℝ (⊤ : ℕ∞) (fun x => fderiv ℝ f x (unitVector i))
  exact ((contDiff_infty_iff_fderiv.mp hf).2).clm_apply contDiff_const

/-- Appending a coordinate to a coordinate list differentiates along it first. The head
coordinate of `coordinateIterate` is applied last, so the appended coordinate sits innermost. -/
theorem coordinateIterate_append_single {d : ℕ} (coords : List (Fin d)) (i : Fin d)
    (f : Vec d → ℝ) :
    coordinateIterate (coords ++ [i]) f = coordinateIterate coords (coordinateDerivative i f) := by
  induction coords with
  | nil => rfl
  | cons j rest ih => simp only [List.cons_append, coordinateIterate, ih]

/-- The orbit of a horizontal derivative is the spatial coordinate derivative of the orbit. -/
theorem orbit_horizontalDerivative {d : ℕ} (i : Fin d) (F : FieldPair d → ℝ)
    (ω : FieldPair d) :
    orbit (horizontalDerivative i F) ω = coordinateDerivative i (orbit F ω) := by
  funext x
  exact horizontalDerivative_translate i F ω x

/-- The horizontal coordinate derivative of an orbit-core test is an orbit-core test. -/
theorem IsHorizontalTest.horizontalDerivative {d : ℕ} {F : FieldPair d → ℝ}
    (hF : IsHorizontalTest F) (i : Fin d) : IsHorizontalTest (horizontalDerivative i F) := by
  refine ⟨hF.measurable_derivative i, fun ω => ?_, fun coords => ?_⟩
  · rw [orbit_horizontalDerivative i F ω]
    exact contDiff_coordinateDerivative_orbit (hF.2.1 ω) i
  · obtain ⟨M, hM⟩ := hF.2.2 (coords ++ [i])
    refine ⟨M, fun ω x => ?_⟩
    have h := hM ω x
    rw [coordinateIterate_append_single] at h
    rw [orbit_horizontalDerivative i F ω]
    exact h

/-- Iterated horizontal derivative along a coordinate list. The empty list is the identity, and
the head coordinate is applied last, as in `HasIteratedHorizontalLpDerivative`. -/
def iteratedHorizontalDerivative {d : ℕ} : List (Fin d) → (FieldPair d → ℝ) → FieldPair d → ℝ
  | [], F => F
  | i :: rest, F => horizontalDerivative i (iteratedHorizontalDerivative rest F)

/-- Every iterated horizontal derivative of an orbit-core test is an orbit-core test. -/
theorem IsHorizontalTest.iterated {d : ℕ} {F : FieldPair d → ℝ} (hF : IsHorizontalTest F)
    (coords : List (Fin d)) : IsHorizontalTest (iteratedHorizontalDerivative coords F) := by
  induction coords with
  | nil => exact hF
  | cons i rest ih => exact ih.horizontalDerivative i

/-- One coordinate step of an orbit-core test is the source generator identity: the strong L²(Q)
difference quotient converges to the literal spatial orbit derivative. -/
theorem IsHorizontalTest.hasHorizontalLpDerivative_toLp {d : ℕ} {F : FieldPair d → ℝ}
    (hF : IsHorizontalTest F) (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (hQ : IsStationary Q) (i : Fin d) :
    HasHorizontalLpDerivative Q hQ i ((hF.memLp Q 2).toLp F)
      ((hF.memLp_derivative Q 2 i).toLp (EinsteinRelation.horizontalDerivative i F)) := by
  exact Correctors.tendsto_horizontalCore_differenceQuotient Q hQ hF i

/-- Every coordinate list gives the iterated L²(Q) generator chain of an orbit-core test, with
the literal iterated orbit derivative as the final element. -/
theorem IsHorizontalTest.hasIteratedHorizontalLpDerivative {d : ℕ} {F : FieldPair d → ℝ}
    (hF : IsHorizontalTest F) (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (hQ : IsStationary Q) (coords : List (Fin d)) :
    HasIteratedHorizontalLpDerivative Q hQ coords ((hF.memLp Q 2).toLp F)
      (((hF.iterated coords).memLp Q 2).toLp (iteratedHorizontalDerivative coords F)) := by
  induction coords with
  | nil => exact rfl
  | cons i rest ih =>
    refine ⟨((hF.iterated rest).memLp Q 2).toLp (iteratedHorizontalDerivative rest F), ih, ?_⟩
    exact (hF.iterated rest).hasHorizontalLpDerivative_toLp Q hQ i

/-- Every orbit-core test is a horizontally smooth test in the L²(Q) generator sense. Its
iterated generators are the literal orbit derivatives, which are bounded by the bounds of the
core, and the boundedness of the coercion of each one follows from `coeFn_toLp`. -/
theorem IsHorizontalTest.isHorizontallySmoothTest {d : ℕ} {F : FieldPair d → ℝ}
    (hF : IsHorizontalTest F) (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (hQ : IsStationary Q) : IsHorizontallySmoothTest Q hQ ((hF.memLp Q 2).toLp F) := by
  intro coords
  refine ⟨((hF.iterated coords).memLp Q 2).toLp (iteratedHorizontalDerivative coords F),
    hF.hasIteratedHorizontalLpDerivative Q hQ coords, ?_⟩
  obtain ⟨M, _, hM⟩ := (hF.iterated coords).bound_orbit
  refine ⟨M, ?_⟩
  filter_upwards [((hF.iterated coords).memLp Q 2).coeFn_toLp] with ω hω
  rw [hω]
  simpa only [orbit_zero] using hM ω 0

end EinsteinRelation
