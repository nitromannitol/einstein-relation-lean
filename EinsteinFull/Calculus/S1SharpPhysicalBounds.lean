import EinsteinFull.Calculus.S1SharpBoundSupport
import EinsteinFull.Work.W8.SharpnessConstructionSupport
import EinsteinRelation.Sharpness.DivergenceProfile

/-! Uniform derivative bounds of every order for the constructed sharpness fields: the clock
density, the reduced coefficient, the physical coefficient and the physical potential of
`EinsteinFull.Work.W8.physicalPair`, uniformly over all noise samples and points
(`paper/main.tex:1534–1541`). -/

open Set

namespace EinsteinFull.Calculus.S1

open EinsteinRelation EinsteinRelation.Sharpness
open EinsteinFull.Work.W8

variable {d : ℕ}

theorem inverseCandidate_apply_eq' (i : Fin d) (g : Vec d) (j k : Fin d) :
    inverseCandidate i g j k =
      (if j = k then (1 : ℝ) else 0) - (jacobianFactor i g)⁻¹ * (unitVector i j * g k) := by
  simp only [inverseCandidate, outer, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.one_apply]

theorem coefficient_apply_eq_sum' (i : Fin d) (g : Vec d) (j k : Fin d) :
    coefficient i g j k = jacobianFactor i g *
      ∑ l, inverseCandidate i g j l * inverseCandidate i g k l := by
  simp only [coefficient, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply,
    Matrix.transpose_apply]

theorem coefficientDivergenceProfile_eq (i : Fin d) (g : Vec d) (H : Fin d → Fin d → ℝ) :
    coefficientDivergenceProfile i (g, H) =
      -(∑ k, H k k) + (2 * ∑ k, g k * H i k) * (1 + g i)⁻¹ -
        (∑ k, g k * g k) * H i i * ((1 + g i)⁻¹ * (1 + g i)⁻¹) := by
  unfold coefficientDivergenceProfile euclideanSq dot
  simp only [div_eq_mul_inv, ← inv_pow]
  ring

theorem unifBdd_corrector (d : ℕ) : UnifBdd (fun W : NoiseSample d => corrector W) :=
  UnifBdd.of_coordinate (fun W => corrector_contDiff W) fun l => by
    obtain ⟨C, -, h⟩ := exists_corrector_derivative_bound d l
    exact ⟨C, h⟩

theorem unifBdd_corrector_deriv (d : ℕ) (k : Fin d) :
    UnifBdd (fun (W : NoiseSample d) => coordinateDerivative k (corrector W)) :=
  (unifBdd_corrector d).coordDeriv k

theorem unifBdd_corrector_deriv₂ (d : ℕ) (m n : Fin d) :
    UnifBdd (fun (W : NoiseSample d) =>
      coordinateDerivative m (coordinateDerivative n (corrector W))) :=
  (unifBdd_corrector_deriv d n).coordDeriv m

theorem jacobianFactor_mem_Icc (i : Fin d) (W : NoiseSample d) (x : Vec d) :
    jacobianFactor i (gradient (corrector W) x) ∈ Icc (3 / 4 : ℝ) (5 / 4) :=
  jacobianFactor_bounds i _ (corrector_gradient_bound W x)

theorem jacobianFactor_ne_zero' (i : Fin d) (W : NoiseSample d) (x : Vec d) :
    jacobianFactor i (gradient (corrector W) x) ≠ 0 :=
  (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 3 / 4) (jacobianFactor_mem_Icc i W x).1).ne'

theorem unifBdd_jacobianFactor (i : Fin d) :
    UnifBdd (fun (W : NoiseSample d) x => jacobianFactor i (gradient (corrector W) x)) :=
  ((unifBdd_const (ι := NoiseSample d) (d := d) 1).add (unifBdd_corrector_deriv d i)).congr
    fun W x => rfl

theorem unifBdd_jacobianFactor_inv (i : Fin d) :
    UnifBdd (fun (W : NoiseSample d) x => (jacobianFactor i (gradient (corrector W) x))⁻¹) :=
  (unifBdd_jacobianFactor i).inv_Icc (lo := 3 / 4) (hi := 5 / 4) (by norm_num) (by norm_num)
    (jacobianFactor_mem_Icc i)

theorem unifBdd_inverseCandidate (i j l : Fin d) :
    UnifBdd (fun (W : NoiseSample d) x => inverseCandidate i (gradient (corrector W) x) j l) :=
  ((unifBdd_const (ι := NoiseSample d) (d := d) (if j = l then (1 : ℝ) else 0)).sub
    ((unifBdd_jacobianFactor_inv i).mul
      ((unifBdd_const (ι := NoiseSample d) (d := d) (unitVector i j)).mul
        (unifBdd_corrector_deriv d l)))).congr
    fun W x => (inverseCandidate_apply_eq' i _ j l).symm

theorem unifBdd_coefficient (i j k : Fin d) :
    UnifBdd (fun (W : NoiseSample d) x => coefficient i (gradient (corrector W) x) j k) :=
  ((unifBdd_jacobianFactor i).mul
    (UnifBdd.sum (fun l (W : NoiseSample d) x =>
        inverseCandidate i (gradient (corrector W) x) j l *
          inverseCandidate i (gradient (corrector W) x) k l)
      (fun l => (unifBdd_inverseCandidate i j l).mul (unifBdd_inverseCandidate i k l))
      Finset.univ)).congr
    fun W x => (coefficient_apply_eq_sum' i _ j k).symm

/-- The expression for the clock density in terms of the jet of the corrector. -/
theorem unifBdd_densityProfile (i : Fin d) :
    UnifBdd (fun (W : NoiseSample d) x =>
      -(∑ k, coordinateDerivative k (coordinateDerivative k (corrector W)) x) +
        (2 * ∑ k, coordinateDerivative k (corrector W) x *
          coordinateDerivative i (coordinateDerivative k (corrector W)) x) *
          (jacobianFactor i (gradient (corrector W) x))⁻¹ -
        (∑ k, coordinateDerivative k (corrector W) x * coordinateDerivative k (corrector W) x) *
          coordinateDerivative i (coordinateDerivative i (corrector W)) x *
          ((jacobianFactor i (gradient (corrector W) x))⁻¹ *
            (jacobianFactor i (gradient (corrector W) x))⁻¹)) := by
  have hsum1 := UnifBdd.sum (fun (k : Fin d) (W : NoiseSample d) x =>
    coordinateDerivative k (coordinateDerivative k (corrector W)) x)
    (fun k => unifBdd_corrector_deriv₂ d k k) Finset.univ
  have hsum2 := UnifBdd.sum (fun (k : Fin d) (W : NoiseSample d) x =>
    coordinateDerivative k (corrector W) x *
      coordinateDerivative i (coordinateDerivative k (corrector W)) x)
    (fun k => (unifBdd_corrector_deriv d k).mul (unifBdd_corrector_deriv₂ d i k)) Finset.univ
  have hsum3 := UnifBdd.sum (fun (k : Fin d) (W : NoiseSample d) x =>
    coordinateDerivative k (corrector W) x * coordinateDerivative k (corrector W) x)
    (fun k => (unifBdd_corrector_deriv d k).mul (unifBdd_corrector_deriv d k)) Finset.univ
  have hinv := unifBdd_jacobianFactor_inv i
  exact (hsum1.neg.add (hsum2.const_mul 2 |>.mul hinv)).sub
    ((hsum3.mul (unifBdd_corrector_deriv₂ d i i)).mul (hinv.mul hinv))

theorem densityField_corrector_eq (i : Fin d) (W : NoiseSample d) (x : Vec d) :
    densityField i (clockParameter i) (corrector W) x =
      1 + clockParameter i / 2 *
        (-(∑ k, coordinateDerivative k (coordinateDerivative k (corrector W)) x) +
          (2 * ∑ k, coordinateDerivative k (corrector W) x *
            coordinateDerivative i (coordinateDerivative k (corrector W)) x) *
            (jacobianFactor i (gradient (corrector W) x))⁻¹ -
          (∑ k, coordinateDerivative k (corrector W) x * coordinateDerivative k (corrector W) x) *
            coordinateDerivative i (coordinateDerivative i (corrector W)) x *
            ((jacobianFactor i (gradient (corrector W) x))⁻¹ *
              (jacobianFactor i (gradient (corrector W) x))⁻¹)) := by
  unfold densityField
  rw [divergence_coefficientField_column_eq_profile i (corrector W) (corrector_contDiff W)
    (fun y => jacobianFactor_ne_zero' i W y) x, coefficientDivergenceProfile_eq]
  simp only [jacobianFactor, gradient]

theorem unifBdd_density (i : Fin d) :
    UnifBdd (fun (W : NoiseSample d) x => densityField i (clockParameter i) (corrector W) x) :=
  (((unifBdd_const (ι := NoiseSample d) (d := d) (1 : ℝ)).add
    ((unifBdd_densityProfile i).const_mul (clockParameter i / 2)))).congr
    fun W x => (densityField_corrector_eq i W x).symm

theorem density_mem_Icc (i : Fin d) (W : NoiseSample d) (x : Vec d) :
    densityField i (clockParameter i) (corrector W) x ∈ Icc (3 / 4 : ℝ) (5 / 4) :=
  density_bounds i W x

theorem unifBdd_density_inv (i : Fin d) :
    UnifBdd (fun (W : NoiseSample d) x =>
      (densityField i (clockParameter i) (corrector W) x)⁻¹) :=
  (unifBdd_density i).inv_Icc (lo := 3 / 4) (hi := 5 / 4) (by norm_num) (by norm_num)
    (density_mem_Icc i)

theorem unifBdd_potential (i : Fin d) :
    UnifBdd (fun (W : NoiseSample d) x =>
      -(1 / 2 : ℝ) * Real.log (densityField i (clockParameter i) (corrector W) x)) :=
  ((unifBdd_density i).log_Icc (lo := 3 / 4) (hi := 5 / 4) (by norm_num) (by norm_num)
    (density_mem_Icc i)).const_mul (-(1 / 2 : ℝ))

/-- Uniform bounds on all derivatives of the four constructed fields. -/
theorem physicalPair_unifBdd (i : Fin d) :
    UnifBdd (fun (W : NoiseSample d) x => clockDensity (physicalPair i W) x) ∧
    (∀ j k : Fin d, UnifBdd (fun (W : NoiseSample d) x =>
      reducedCoefficient (physicalPair i W) x j k)) ∧
    (∀ j k : Fin d, UnifBdd (fun (W : NoiseSample d) x => (physicalPair i W).1 x j k)) ∧
    UnifBdd (fun (W : NoiseSample d) x => (physicalPair i W).2 x) := by
  refine ⟨(unifBdd_density i).congr fun W x => (physicalPair_clockDensity i W x).symm,
    fun j k => (unifBdd_coefficient i j k).congr fun W x => ?_,
    fun j k => ((unifBdd_density_inv i).mul (unifBdd_coefficient i j k)).congr fun W x => ?_,
    (unifBdd_potential i).congr fun W x => (physicalPair_apply i W x).2.symm⟩
  · exact congrFun (congrFun (physicalPair_reducedCoefficient i W x).symm j) k
  · have h := congrFun (congrFun (physicalPair_apply i W x).1 j) k
    simp only [Matrix.smul_apply, smul_eq_mul] at h
    exact h.symm

end EinsteinFull.Calculus.S1
