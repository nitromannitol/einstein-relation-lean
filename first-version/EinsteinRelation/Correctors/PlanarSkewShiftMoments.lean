import EinsteinRelation.Correctors.MollifierShiftFromCoordinateMoments
import EinsteinRelation.Correctors.HeatSelectedSkewEquations

/-! # Shifted means of the independent planar skew entry

Source: `paper/main.tex:948–955`. The actual row-divergence equation
identifies the weak gradient of the independent skew entry with the
rotated centered flux. Its coordinate mollifier bounds therefore imply
the same uniform shifted-mean estimate as for the scalar corrector.
-/

open MeasureTheory
open scoped Convolution

namespace EinsteinRelation.Correctors

/-- The planar skew shifted-mean estimate follows from coordinate bounds
on its actual row divergence. The weak-gradient equation is derived.
Source: `paper/main.tex:948–955`. -/
theorem planar_skew_shift_moment_le_of_flux_bounds
    {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q] {p C R : ℝ}
    (hp : 1 ≤ p) (hC : 0 ≤ C) (hR : 0 < R)
    (S : Ω → Vec 2 → Mat 2) (q : Ω → Vec 2 → Vec 2)
    (hqm : Measurable (fun z : Ω × Vec 2 => q z.1 z.2))
    (hskew : ∀ᵐ ω ∂Q, ∀ᵐ x ∂volume, (S ω x).transpose = -(S ω x))
    (hdiv : ∀ᵐ ω ∂Q, HasWeakRowDivergence Set.univ (S ω) (q ω))
    (hbound : ∀ x : Vec 2, euclideanNorm x ≤ R → ∀ j : Fin 2,
      eLpNorm (fun ω => ((fun z => q ω z j)
        ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
          Calculus.unitMassScaledMollifier 2 R) x) (ENNReal.ofReal p) Q ≤
        ENNReal.ofReal (C * R⁻¹))
    (y : Vec 2) (hy : euclideanNorm y ≤ R) :
    MemLp (fun ω => ((fun x => S ω x 0 1)
        ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
          Calculus.unitMassScaledMollifier 2 R) y -
      ((fun x => S ω x 0 1) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
        Calculus.unitMassScaledMollifier 2 R) 0) (ENNReal.ofReal p) Q ∧
      eLpNorm (fun ω => ((fun x => S ω x 0 1)
          ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
            Calculus.unitMassScaledMollifier 2 R) y -
        ((fun x => S ω x 0 1) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
          Calculus.unitMassScaledMollifier 2 R) 0) (ENNReal.ofReal p) Q ≤
        ENNReal.ofReal (2 * C) := by
  let H : Ω → Vec 2 → Vec 2 := fun ω x => ![-q ω x 1, q ω x 0]
  have hHm : Measurable (fun z : Ω × Vec 2 => H z.1 z.2) := by
    apply measurable_pi_lambda
    intro j
    fin_cases j
    · exact ((measurable_pi_apply 1).comp hqm).neg
    · exact (measurable_pi_apply 0).comp hqm
  have hweak : ∀ᵐ ω ∂Q, HasWeakGradient Set.univ (fun x => S ω x 0 1) (H ω) := by
    filter_upwards [hskew, hdiv] with ω hω hω'
    exact hasWeakGradient_planar_skew_entry_of_ae isOpen_univ (S ω) (q ω)
      (by simpa only [Measure.restrict_univ] using hω) hω'
  have hloc : ∀ᵐ ω ∂Q, LocallyIntegrable (fun x => S ω x 0 1) volume :=
    hweak.mono fun _ hω => locallyIntegrableOn_univ.mp (hω 0).1
  apply convolution_shift_moment_le_of_coordinate_bounds Q hp hC hR
    (fun ω x => S ω x 0 1) H hHm hloc hweak ?_ y hy
  intro x hx j
  fin_cases j
  · have heq : (fun ω => ((fun z => H ω z 0)
        ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
          Calculus.unitMassScaledMollifier 2 R) x) =
        -(fun ω => ((fun z => q ω z 1)
          ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
            Calculus.unitMassScaledMollifier 2 R) x) := by
      funext ω
      simp only [H, Matrix.cons_val_zero, convolution_def,
        ContinuousLinearMap.lsmul_apply, smul_eq_mul, neg_mul, integral_neg,
        Pi.neg_apply]
    change eLpNorm (fun ω => ((fun z => H ω z 0)
      ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
        Calculus.unitMassScaledMollifier 2 R) x) _ Q ≤ _
    rw [heq, eLpNorm_neg]
    exact hbound x hx 1
  · exact hbound x hx 0

end EinsteinRelation.Correctors
