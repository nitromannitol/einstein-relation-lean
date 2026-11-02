import EinsteinFull.Blueprint.G3.Proofs.C6CoarseIdentification
open MeasureTheory ProbabilityTheory
noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation EinsteinRelation.External.AKM
open EinsteinRelation.Correctors EinsteinRelation.ReductionImageV3
open EinsteinRelation.Environment.AKMTestIntegralSupport
open EinsteinFull.External.Source.AKM
theorem coarseCorrector_physical_gaussian_flux_identity :
    ∀ {d : ℕ} (D : StructuralData d)
      (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (i : Fin d) (φ : Corrector (actualCoefficientLaw Q) (unitVector i))
      (_hid : ∀ᵐ ω ∂physicalReferenceLaw Q, ∀ᵐ y ∂(volume : Measure (Vec d)),
        unitVector i + φ.grad (project (r₀ := D.dependenceRange)
          Q.ellipticity_parameter ω) y =
          (correctorUnitVector i + (canonicalCorrectorGradient Q i :
            Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
              (translate (D.dependenceRange • y) (reduce ω.1))).ofLp)
      (z : Vec d) (r : ℝ), 0 < r →
      ∀ᵐ ω ∂physicalReferenceLaw Q,
        let a := project (r₀ := D.dependenceRange) Q.ellipticity_parameter ω
        let A := ellipticityScale D.ellipticity • homogenizedCoefficient Q
        let U := ∫ y, heatKernel z r y • (unitVector i + φ.grad a y)
        let F := ∫ y, heatKernel z r y • (a y).mulVec (unitVector i + φ.grad a y)
        F - A.mulVec U = ellipticityScale D.ellipticity •
          ∫ y, heatKernel (D.dependenceRange • z) (D.dependenceRange * r) y •
            (fun j => commutatorObservation Q j i (translate y (reduce ω.1))) := by
  intro d D Q i φ hid z r hr
  let κ := ellipticityScale D.ellipticity
  let ρ := D.dependenceRange
  let A := κ • homogenizedCoefficient Q
  let T : Vec d →L[ℝ] Vec d := (Matrix.toLin' A).toContinuousLinearMap
  have hi := (measurePreserving_akmProject Q).quasiMeasurePreserving.ae
    (coarseCorrector_gaussianAffine_integrable Q i φ hid z hr)
  filter_upwards [hid, hi] with ω hω hI
  let a := project (r₀ := D.dependenceRange) Q.ellipticity_parameter ω
  let v := fun y => unitVector i + φ.grad a y
  let f := fun y : Vec d => fun j => commutatorObservation Q j i (translate y (reduce ω.1))
  have heq : (fun y => (a y).mulVec (v y) - A.mulVec (v y)) =ᵐ[volume]
      (fun y => κ • f (ρ • y)) := by
    filter_upwards [hω] with y hy
    have hv : v y = unitVector i + WithLp.ofLp (correctorGradient Q i
        (translate (ρ • y) (reduce ω.1))) := by
      have hu : (correctorUnitVector i).ofLp = unitVector i := by
        ext j
        simp [correctorUnitVector, unitVector, Pi.single_apply, eq_comm]
      have hval : WithLp.ofLp ((canonicalCorrectorGradient Q i :
          Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
          (translate (ρ • y) (reduce ω.1))) =
          WithLp.ofLp (correctorGradient Q i (translate (ρ • y) (reduce ω.1))) := by rfl
      rw [← hval]
      simpa only [WithLp.ofLp_add, hu] using hy
    rw [hv]
    ext j
    change (∑ k, (κ * (reduce ω.1).1 (ρ • y) j k) *
      (unitVector i k + correctorGradient Q i (translate (ρ • y) (reduce ω.1)) k)) -
      (∑ k, (κ * homogenizedCoefficient Q j k) *
      (unitVector i k + correctorGradient Q i (translate (ρ • y) (reduce ω.1)) k)) =
      κ * commutatorObservation Q j i (translate (ρ • y) (reduce ω.1))
    simp only [commutatorObservation, translate, ContinuousMap.coe_mk, add_zero, mul_sub, sub_mul,
      Finset.mul_sum, Finset.sum_sub_distrib, mul_assoc]
  calc
    _ = ∫ y, heatKernel z r y • ((a y).mulVec (v y) - A.mulVec (v y)) := by
      have hT (w : Vec d) : T w = A.mulVec w := by rfl
      have hAi : Integrable (fun y => heatKernel z r y • A.mulVec (v y)) := by
        simpa only [hT, Matrix.mulVec_smul] using T.integrable_comp hI.2.1
      simp_rw [smul_sub]
      rw [integral_sub hI.2.2 hAi]
      congr 1
      simpa only [hT, Matrix.mulVec_smul] using (T.integral_comp_comm hI.2.1).symm
    _ = ∫ y, heatKernel z r y • (κ • f (ρ • y)) :=
      integral_congr_ae (by
        filter_upwards [heq] with y hy
        rw [hy])
    _ = κ • ∫ y, heatKernel z r y • f (ρ • y) := by
      simp_rw [smul_comm (heatKernel z r _) κ]
      rw [integral_smul]
    _ = _ := congrArg (fun v : Vec d => κ • v)
      (coarseHeatKernel_integral_rescale f z hr
        (lt_of_lt_of_le zero_lt_one D.one_le_dependenceRange))
end EinsteinFull.Blueprint
