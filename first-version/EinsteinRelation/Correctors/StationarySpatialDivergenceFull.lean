import EinsteinRelation.Correctors.StationarySpatialDivergence
import EinsteinRelation.Correctors.HorizontalCoreDivergence

/-! # Full horizontal divergence of stationary spatial fields

Source: `paper/main.tex:926–938`. The stationary spatial weak equation
is transferred to all generator-domain tests in the paper's horizontal
divergence predicate. The row version retains the manuscript's convention.
-/

open MeasureTheory

namespace EinsteinRelation.Correctors

/-- A genuine samplewise spatial divergence equation for stationary L²
observables gives the full horizontal weak divergence.
Source: `paper/main.tex:926–938`. -/
theorem weakHorizontalDivergence_of_spatial {d : ℕ} (Q : Measure (FieldPair d))
    [IsProbabilityMeasure Q] (hQ : IsStationary Q)
    {W : FieldPair d → Vec d} {h : FieldPair d → ℝ}
    (hWm : Measurable W) (hhm : Measurable h)
    (hW : ∀ i, MemLp (fun ω => W ω i) 2 Q) (hh : MemLp h 2 Q)
    (hweak : ∀ᵐ ω ∂Q, HasWeakDivergence Set.univ
      (fun x => W (translate x ω)) (orbit h ω)) :
    HasWeakHorizontalDivergence Q hQ W h := by
  exact weakHorizontalDivergence_of_core Q hQ hW hh fun _ hH =>
    stationarySpatialDivergence_integral_test Q hQ hWm hhm hW hh hweak hH

/-- The row-wise transfer needed for the local skew flux corrector.
Source: `paper/main.tex:926–938`. -/
theorem weakHorizontalRowDivergence_of_spatial {d : ℕ} (Q : Measure (FieldPair d))
    [IsProbabilityMeasure Q] (hQ : IsStationary Q)
    {S : FieldPair d → Mat d} {g : FieldPair d → Vec d}
    (hSm : Measurable S) (hgm : Measurable g)
    (hS : ∀ i j, MemLp (fun ω => S ω i j) 2 Q)
    (hg : ∀ i, MemLp (fun ω => g ω i) 2 Q)
    (hweak : ∀ᵐ ω ∂Q, HasWeakRowDivergence Set.univ
      (fun x => S (translate x ω)) (fun x => g (translate x ω))) :
    ∀ i, HasWeakHorizontalDivergence Q hQ
      (fun ω j => S ω i j) (fun ω => g ω i) := by
  intro i
  have hrow : Continuous (fun a : Mat d => fun j => a i j) :=
    continuous_pi fun j => (continuous_apply j).comp (continuous_apply i)
  exact weakHorizontalDivergence_of_spatial Q hQ (hrow.measurable.comp hSm)
    ((measurable_pi_apply i).comp hgm) (hS i) (hg i)
    (hweak.mono fun _ hω => hω i)

end EinsteinRelation.Correctors
