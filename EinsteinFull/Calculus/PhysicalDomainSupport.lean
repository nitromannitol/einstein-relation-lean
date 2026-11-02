import EinsteinFull.Frozen.PhysicalBilinearForm
import EinsteinFull.Calculus.PhysicalMeasureSupport
import EinsteinFull.Calculus.PhysicalH1CongruenceSupport
import EinsteinFull.Calculus.PhysicalFormIntegralSupport

open scoped ENNReal
open MeasureTheory
namespace EinsteinFull
open EinsteinRelation

/-- Both integrals in the exported form exist for every public argument. -/
theorem physicalBilinearForm_integrable {d : ℕ} (m : Measure (Vec d))
    (a : Vec d → Mat d)
    (ha : ∀ j k : Fin d, MemLp (fun x => (a x j k : ℂ)) ∞ m)
    (i : Fin d) (ζ : ℂ) (u v : Lp ℂ 2 m)
    (G H : Fin d → Lp ℂ 2 m) :
    Integrable (fun x => u x * v x) m ∧
      Integrable (fun x => ∑ j : Fin d, ∑ k : Fin d,
        (G j x - ζ * (unitVector i j : ℂ) * u x) * (a x j k : ℂ) *
        (H k x - ζ * (unitVector i k : ℂ) * v x)) m := by
  exact ⟨(Lp.memLp u).integrable_mul (Lp.memLp v),
    integrable_shiftedGradientForm_of_memLp m d (fun j k x => (a x j k : ℂ)) ha
      u v (fun j => G j) (fun j => H j) (Lp.memLp u) (Lp.memLp v)
      (fun j => Lp.memLp (G j)) (fun j => Lp.memLp (H j))
      (fun j => ζ * (unitVector i j : ℂ))⟩

/-- Conjugation on L2 agrees with pointwise conjugation almost everywhere. -/
theorem physicalBilinearForm_star_representative {d : ℕ} (m : Measure (Vec d))
    (u : Lp ℂ 2 m) : (star u : Lp ℂ 2 m) =ᵐ[m] (fun x => star (u x)) :=
  Lp.coeFn_star u

/-- The exported H1 graph describes any representatives of its L2 classes. -/
theorem isPhysicalH1Graph_iff_representatives {d : ℕ} (m : Measure (Vec d))
    (hm : m = volume ∨ ∃ (i : Fin d) (lam : ℝ), m = physicalForceMeasure i lam)
    (u : Lp ℂ 2 m) (G : Fin d → Lp ℂ 2 m)
    (f : Vec d → ℂ) (g : Fin d → Vec d → ℂ)
    (hf : (fun x => u x) =ᵐ[m] f) (hg : ∀ j, (fun x => G j x) =ᵐ[m] g j) :
    IsPhysicalH1Graph m hm u G ↔
      (∀ j : Fin d, HasWeakPartialDerivative Set.univ j
        (fun x => (f x).re) (fun x => (g j x).re)) ∧
      (∀ j : Fin d, HasWeakPartialDerivative Set.univ j
        (fun x => (f x).im) (fun x => (g j x).im)) := by
  have hv : (volume : Measure (Vec d)) ≪ m := by
    rcases hm with rfl | ⟨i, lam, rfl⟩
    · exact Measure.AbsolutelyContinuous.rfl
    · exact volume_absolutelyContinuous_physicalForceMeasure i lam
  unfold IsPhysicalH1Graph
  apply and_congr
  · apply forall_congr'
    intro j
    exact hasWeakPartialDerivative_congr_of_absolutelyContinuous m hv j
      (hf.mono fun x hx => congrArg Complex.re hx)
      ((hg j).mono fun x hx => congrArg Complex.re hx)
  · apply forall_congr'
    intro j
    exact hasWeakPartialDerivative_congr_of_absolutelyContinuous m hv j
      (hf.mono fun x hx => congrArg Complex.im hx)
      ((hg j).mono fun x hx => congrArg Complex.im hx)

end EinsteinFull
