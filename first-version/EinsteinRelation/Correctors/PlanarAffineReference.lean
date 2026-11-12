import EinsteinRelation.Calculus.ClassicalSpatialDerivative
import EinsteinRelation.Correctors.CoefficientColumnDivergence
import EinsteinRelation.Correctors.PlanarAffineComparison

/-! Explicit affine references for the planar comparison in
`paper/main.tex:864–875`. -/
open MeasureTheory
namespace EinsteinRelation.Correctors

private theorem weakPartial_linear (l : Vec 2 →L[ℝ] ℝ) (j : Fin 2) :
    HasWeakPartialDerivative Set.univ j l (fun _ => l (unitVector j)) := by
  have he : coordinateDerivative j (fun x => l x) = fun _ => l (unitVector j) := by
    funext x
    unfold coordinateDerivative
    rw [l.fderiv]
  simpa only [he] using hasWeakPartialDerivative_of_contDiff j l l.contDiff

/-- An explicit planar reference with zero total coefficient flux and
constant row divergence; source `paper/main.tex:864–875`. -/
theorem planar_affine_reference_equations (i : Fin 2) (m : Vec 2) :
    HasWeakGradient Set.univ (fun x : Vec 2 => -(x i)) (fun _ => -(unitVector i)) ∧
    HasWeakRowDivergence Set.univ (planarAffineSkewReference m) (fun _ => -m) := by
  constructor
  · intro j
    simpa only [ContinuousLinearMap.neg_apply,ContinuousLinearMap.proj_apply,
      Pi.neg_apply,unitVector,Pi.single_apply,eq_comm] using
      weakPartial_linear (-(ContinuousLinearMap.proj i : Vec 2 →L[ℝ] ℝ)) j
  · let l : Vec 2 →L[ℝ] ℝ := m 1 • ContinuousLinearMap.proj 0 -
      m 0 • ContinuousLinearMap.proj 1
    have hl (j : Fin 2) : HasWeakPartialDerivative Set.univ j
        (fun x : Vec 2 => m 1*x 0-m 0*x 1) (fun _ => l (unitVector j)) := by
      simpa only [l,ContinuousLinearMap.sub_apply,ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.proj_apply,smul_eq_mul] using weakPartial_linear l j
    have hnl (j : Fin 2) : HasWeakPartialDerivative Set.univ j
        (fun x : Vec 2 => -(m 1*x 0-m 0*x 1)) (fun _ => -l (unitVector j)) := by
      simpa only [l,ContinuousLinearMap.neg_apply,ContinuousLinearMap.sub_apply,
        ContinuousLinearMap.smul_apply,ContinuousLinearMap.proj_apply,smul_eq_mul] using
        weakPartial_linear (-l) j
    have hz (j : Fin 2) : HasWeakPartialDerivative Set.univ j
        (fun _ : Vec 2 => (0:ℝ)) (fun _ => 0) := by
      simpa using weakPartial_linear (0 : Vec 2 →L[ℝ] ℝ) j
    intro k
    fin_cases k
    · have h := hasWeakDivergence_of_coordinate_derivatives (F := fun x =>
          planarAffineSkewReference m x 0) (D := fun _ => ![0,l (unitVector 1)])
          isOpen_univ (fun j => by fin_cases j; exact hz 0; exact hl 1)
      simpa [Fin.sum_univ_two,l,unitVector] using h
    · have h := hasWeakDivergence_of_coordinate_derivatives (F := fun x =>
          planarAffineSkewReference m x 1) (D := fun _ => ![-l (unitVector 0),0])
          isOpen_univ (fun j => by fin_cases j; exact hnl 0; exact hz 1)
      simpa [Fin.sum_univ_two,l,unitVector] using h
end EinsteinRelation.Correctors
