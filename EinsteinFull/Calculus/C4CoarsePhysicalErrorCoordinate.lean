import EinsteinFull.Blueprint.G3.Proofs.C6CoarseIdentification
import EinsteinFull.Calculus.C6CoarsePhysicalGaussianFlux
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation EinsteinRelation.External.AKM
open EinsteinRelation.Correctors EinsteinRelation.ReductionImageV3
open EinsteinRelation.Environment.AKMTestIntegralSupport
open EinsteinFull.External.Source.AKM
/-- The physical affine residual identifies each scalar coarse error. -/
theorem coarse_physical_error_coordinate_identity :
∀ {d : ℕ} (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (ω : PhysicalField d D.ellipticity) (i j : Fin d) (x : Vec d) (r : ℝ)
    (U F : Vec d),
    let κ := ellipticityScale D.ellipticity
    let a := project (r₀ := D.dependenceRange) Q.ellipticity_parameter ω
    let A := κ • homogenizedCoefficient Q
    let B := coarsenedCoefficient a A (D.dependenceRange⁻¹ • x)
      (r / D.dependenceRange)
    let f := fun y : Vec d => heatKernel 0 r y •
      (fun k => commutatorObservation Q k i (translate (x - y) (reduce ω.1)))
    Integrable f (volume : Measure (Vec d)) → F - A.mulVec U = κ • ∫ y, f y →
    (∫ y, heatKernel 0 r y *
      commutatorObservation Q j i (translate (x - y) (reduce ω.1))) -
        covarianceCoarseEntry D Q r x j i (reduce ω.1) =
      κ⁻¹ * (F - A.mulVec U - B.mulVec (unitVector i)) j := by
  intro d D Q ω i j x r U F κ a A B f hf he
  have hκ : κ ≠ 0 := ne_of_gt (ellipticityScale_pos D.one_le_ellipticity)
  have hω : reduce ω.1 ∈ physicalReducedRange D.ellipticity := ⟨ω.1, ω.2, rfl⟩
  have hInv : inverseReducePhysical ⟨reduce ω.1, hω⟩ = ω :=
    inverseReduce_reducePhysical ω
  have hentry : covarianceCoarseEntry D Q r x j i (reduce ω.1) = κ⁻¹ * B j i := by
    simp only [covarianceCoarseEntry, dite_eq_left hω, hInv]
    rfl
  let T : Vec d →L[ℝ] ℝ := ContinuousLinearMap.proj j
  have hT (v : Vec d) : T v = v j := rfl
  have hcoord : (∫ y, f y) j = ∫ y, heatKernel 0 r y *
      commutatorObservation Q j i (translate (x - y) (reduce ω.1)) := by
    simpa only [hT, f, Pi.smul_apply, smul_eq_mul] using (T.integral_comp_comm hf).symm
  have hB : B.mulVec (unitVector i) j = B j i := by
    simp [Matrix.mulVec, dotProduct, unitVector, Pi.single_apply, mul_ite]
  have he' := congrArg (fun v : Vec d => v j) he
  change (F - A.mulVec U) j = κ * (∫ y, f y) j at he'
  rw [hentry]
  change _ = κ⁻¹ * ((F - A.mulVec U) j - B.mulVec (unitVector i) j)
  rw [hB, he', hcoord]
  field_simp
end EinsteinFull.Blueprint
