import EinsteinRelation.Correctors.CenteredMollifierFields
import EinsteinRelation.Correctors.WeakEquationAveraging
import EinsteinRelation.Correctors.SpatialWeakCongruence
import EinsteinRelation.Correctors.WeightedLocalFlux

/-! # Integrating the common localized equations

Source: `paper/main.tex:926–938`. The localized equations are integrated
directly. In particular, the unweighted conditional fields need not satisfy
an equation outside their conditioning balls.
-/

open MeasureTheory

namespace EinsteinRelation.Correctors

/-- Whole-space localized equations and ordinary product integrability give
the spatial equations for the same five center averages.
Source: `paper/main.tex:926–938`. -/
theorem hasWeakGradient_and_flux_of_mollifier_weighted_equations
    {d : ℕ} {R : ℝ} (hR : 0 < R) {U : Set (Vec d)} (hU : IsOpen U)
    [IsFiniteMeasure (volume.restrict U)]
    (u : Vec d → Vec d → ℝ) (G : Vec d → Vec d → Vec d)
    (S : Vec d → Vec d → Mat d) (A : Vec d → Mat d) (e b : Vec d)
    (hui : Integrable (fun z : Vec d × Vec d =>
      Calculus.unitMassScaledMollifier d R (z.2 - z.1) * u z.1 z.2)
      (volume.prod (volume.restrict U)))
    (hGi : ∀ j, Integrable (fun z : Vec d × Vec d =>
      Calculus.unitMassScaledMollifier d R (z.2 - z.1) * G z.1 z.2 j)
      (volume.prod (volume.restrict U)))
    (hDu : ∀ j, Integrable (fun z : Vec d × Vec d => u z.1 z.2 *
      coordinateDerivative j (Calculus.unitMassScaledMollifier d R) (z.2 - z.1))
      (volume.prod (volume.restrict U)))
    (hSi : ∀ j k, Integrable (fun z : Vec d × Vec d =>
      Calculus.unitMassScaledMollifier d R (z.2 - z.1) * S z.1 z.2 j k)
      (volume.prod (volume.restrict U)))
    (hfluxi : ∀ j, Integrable (fun z : Vec d × Vec d =>
      Calculus.unitMassScaledMollifier d R (z.2 - z.1) *
        ((A z.2).mulVec (e + G z.1 z.2) - b) j)
      (volume.prod (volume.restrict U)))
    (hDS : ∀ j, Integrable (fun z : Vec d × Vec d =>
      ((S z.1 z.2).mulVec (gradient (Calculus.unitMassScaledMollifier d R) (z.2 - z.1))) j)
      (volume.prod (volume.restrict U)))
    (hweak : ∀ᵐ y : Vec d ∂volume,
      HasWeakGradient Set.univ
        (fun x => Calculus.unitMassScaledMollifier d R (x - y) * u y x)
        (fun x j => Calculus.unitMassScaledMollifier d R (x - y) * G y x j +
          u y x * coordinateDerivative j (Calculus.unitMassScaledMollifier d R) (x - y)) ∧
      HasWeakRowDivergence Set.univ
        (fun x j k => Calculus.unitMassScaledMollifier d R (x - y) * S y x j k)
        (fun x j => Calculus.unitMassScaledMollifier d R (x - y) *
          ((A x).mulVec (e + G y x) - b) j +
          ((S y x).mulVec (gradient (Calculus.unitMassScaledMollifier d R) (x - y))) j)) :
    let H : Vec d → Vec d := fun x j => ∫ y, u y x *
      coordinateDerivative j (Calculus.unitMassScaledMollifier d R) (x - y)
    let K : Vec d → Vec d := fun x j => ∫ y,
      ((S y x).mulVec (gradient (Calculus.unitMassScaledMollifier d R) (x - y))) j
    let D : Vec d → Vec d := fun x j =>
      (∫ y, Calculus.unitMassScaledMollifier d R (x - y) * G y x j) + H x j
    HasWeakGradient U
      (fun x => ∫ y, Calculus.unitMassScaledMollifier d R (x - y) * u y x) D ∧
    HasWeakRowDivergence U
      (fun x j k => ∫ y, Calculus.unitMassScaledMollifier d R (x - y) * S y x j k)
      (fun x => (A x).mulVec (e + D x) - b - ((A x).mulVec (H x) - K x)) := by
  dsimp only
  have hgrad := hasWeakGradient_integral volume U
    (fun y x => Calculus.unitMassScaledMollifier d R (x - y) * u y x)
    (fun y x j => Calculus.unitMassScaledMollifier d R (x - y) * G y x j +
      u y x * coordinateDerivative j (Calculus.unitMassScaledMollifier d R) (x - y))
    hui (fun j => (hGi j).add (hDu j))
    (hweak.mono fun _ h => hasWeakGradient_mono (Set.subset_univ U) h.1)
  have hdiv := hasWeakRowDivergence_integral volume U
    (fun y x j k => Calculus.unitMassScaledMollifier d R (x - y) * S y x j k)
    (fun y x j => Calculus.unitMassScaledMollifier d R (x - y) *
      ((A x).mulVec (e + G y x) - b) j +
      ((S y x).mulVec (gradient (Calculus.unitMassScaledMollifier d R) (x - y))) j)
    hSi (fun j => (hfluxi j).add (hDS j))
    (hweak.mono fun _ h => hasWeakRowDivergence_mono (Set.subset_univ U) h.2)
  have hsec := (integrable_translated_unitMassScaledMollifier_product hR U).prod_left_ae
  have hGs := ae_all_iff.mpr fun j => (hGi j).prod_left_ae
  have hHs := ae_all_iff.mpr fun j => (hDu j).prod_left_ae
  have hFs := ae_all_iff.mpr fun j => (hfluxi j).prod_left_ae
  have hKs := ae_all_iff.mpr fun j => (hDS j).prod_left_ae
  constructor
  · apply hasWeakGradient_congr_ae hU hgrad Filter.EventuallyEq.rfl
    filter_upwards [hGs, hHs] with x hxG hxH
    funext j
    exact integral_add (hxG j) (hxH j)
  · apply hasWeakRowDivergence_congr_ae hU hdiv Filter.EventuallyEq.rfl
    filter_upwards [hsec, hGs, hFs, hKs] with x hxw hxG hxF hxK
    funext j
    rw [integral_add (hxF j) (hxK j),
      integral_weight_mulVec_add volume
        (fun y => Calculus.unitMassScaledMollifier d R (x - y))
        (fun y => G y x) (A x) e b hxw hxG
        (integral_translated_unitMassScaledMollifier hR x) j]
    simp only [Matrix.mulVec, dotProduct, Pi.sub_apply, Pi.add_apply,
      Finset.sum_add_distrib, mul_add]
    ring

end EinsteinRelation.Correctors
