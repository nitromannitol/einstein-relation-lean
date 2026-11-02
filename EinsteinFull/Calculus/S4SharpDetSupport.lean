import EinsteinFull.Work.W8.SharpnessConstructionSupport
import EinsteinFull.Frozen.HomogenizedCoefficient
import EinsteinRelation.Sharpness.SharpEnvironmentDischarge
import EinsteinRelation.Sharpness.SharpLawRangeConcentration

/-!
# Deterministic and environment-level facts for the sharpness example

Support for the nodes `app:sharp-harmonic`, `app:sharp-clock` and
`sharp.example#positive-coefficient`: rank-one Jacobian identities, the identification
of the local gradient with the gradient of the constructed corrector, the first column
of the homogenized coefficient, and the mean identities of the physical law. No path
law is involved.
-/

open MeasureTheory
open scoped BigOperators

namespace EinsteinFull.Blueprint
open EinsteinRelation EinsteinRelation.Sharpness

theorem sharpJacobian_mulVec_unitVector {d : ℕ} (i : Fin d) (g : Vec d) :
    (jacobian i g).mulVec (unitVector i) = (jacobian i g).det • unitVector i := by
  have hii : unitVector i i = 1 := by simp [unitVector]
  have h1 : (outer (unitVector i) g).mulVec (unitVector i) = g i • unitVector i := by
    ext k
    simp only [Matrix.mulVec, dotProduct, outer, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single i]
    · rw [hii]; ring
    · intro l _ hl
      simp [unitVector, Pi.single_apply, hl]
    · simp
  rw [det_jacobian, jacobian, Matrix.add_mulVec, Matrix.one_mulVec, h1, jacobianFactor]
  ext k
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem sharpJacobian_transpose_mulVec_unitVector {d : ℕ} (i : Fin d) (g : Vec d) :
    (jacobian i g).transpose.mulVec (unitVector i) = unitVector i + g := by
  have hii : unitVector i i = 1 := by simp [unitVector]
  have h1 : (outer (unitVector i) g).transpose.mulVec (unitVector i) = g := by
    ext k
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, outer]
    rw [Finset.sum_eq_single i]
    · rw [hii]; ring
    · intro l _ hl
      simp [unitVector, Pi.single_apply, hl]
    · simp
  rw [jacobian, Matrix.transpose_add, Matrix.transpose_one, Matrix.add_mulVec,
    Matrix.one_mulVec, h1]

/-- The local gradient of the physical pair is the gradient of the constructed corrector. -/
theorem sharpLocalGradient_physicalPair {d : ℕ} (hd : 2 ≤ d) (W : NoiseSample d) :
    sharpLocalGradient hd (EinsteinFull.Work.W8.physicalPair (⟨0, by omega⟩ : Fin d) W) =
      gradient (EinsteinFull.Work.W8.corrector W) 0 := by
  obtain ⟨Λ, hΛ, hreg⟩ :=
    EinsteinFull.Work.W8.exists_physicalPair_regularity (⟨0, by omega⟩ : Fin d)
  have hΛ1 : (1 : ℝ) ≤ Λ := by linarith
  have hu := isUnit_det_reducedCoefficient hΛ1 (hreg W) 0
  have h := EinsteinFull.Work.W8.physicalPair_harmonic (⟨0, by omega⟩ : Fin d) W 0
  have h1 : ((reducedCoefficient
        (EinsteinFull.Work.W8.physicalPair (⟨0, by omega⟩ : Fin d) W) 0)⁻¹).mulVec
        (unitVector (⟨0, by omega⟩ : Fin d)) =
      unitVector (⟨0, by omega⟩ : Fin d) + gradient (EinsteinFull.Work.W8.corrector W) 0 := by
    calc _ = ((reducedCoefficient
            (EinsteinFull.Work.W8.physicalPair (⟨0, by omega⟩ : Fin d) W) 0)⁻¹).mulVec
            ((reducedCoefficient
              (EinsteinFull.Work.W8.physicalPair (⟨0, by omega⟩ : Fin d) W) 0).mulVec
              (unitVector (⟨0, by omega⟩ : Fin d) +
                gradient (EinsteinFull.Work.W8.corrector W) 0)) := by rw [h]
      _ = (((reducedCoefficient
            (EinsteinFull.Work.W8.physicalPair (⟨0, by omega⟩ : Fin d) W) 0)⁻¹ *
            (reducedCoefficient
              (EinsteinFull.Work.W8.physicalPair (⟨0, by omega⟩ : Fin d) W) 0))).mulVec
              (unitVector (⟨0, by omega⟩ : Fin d) +
                gradient (EinsteinFull.Work.W8.corrector W) 0) := by
          rw [Matrix.mulVec_mulVec]
      _ = _ := by rw [Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]
  unfold sharpLocalGradient
  rw [h1]
  abel

/-- The first column of the homogenized coefficient of the sharp law. -/
theorem homogenizedCoefficient_physicalPair_mulVec {d : ℕ} (i : Fin d)
    {P : Measure (NoiseSample d)} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hQ : Q.measure = P.map (EinsteinFull.Work.W8.physicalPair i)) :
    (homogenizedCoefficient Q).mulVec (unitVector i) = unitVector i :=
  abar_mulVec_unitVector_of_sharp Q i (EinsteinFull.Work.W8.clockParameter i)
    (EinsteinFull.Work.W8.seedScale d) EinsteinFull.Work.W8.corrector_gradient_bound
    (EinsteinFull.Work.W8.density_bounds i) (EinsteinFull.Work.W8.seedScale_pos d) hQ

private theorem measurable_sharpEnergy' {d : ℕ} (i : Fin d) :
    Measurable (fun g : Vec d => sharpEnergy i g) := by
  show Measurable fun g : Vec d => (∑ k, g k * g k) / (1 + g i)
  exact (Finset.measurable_sum _ fun k _ =>
    (measurable_pi_apply k).mul (measurable_pi_apply k)).div
    (measurable_const.add (measurable_pi_apply i))

/-- Environment-level mean identities of the sharp law, transferred to the noise space. -/
theorem sharpPositive_environment {d : ℕ} (hd : 2 ≤ d) {P : Measure (NoiseSample d)}
    (hP : External.IsWhiteNoiseLaw P) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hQ : Q.measure = P.map (EinsteinFull.Work.W8.physicalPair (⟨0, by omega⟩ : Fin d))) :
    (∫ W, gradient (EinsteinFull.Work.W8.corrector W) 0 (⟨0, by omega⟩ : Fin d) ∂P) = 0 ∧
    0 < ∫ W, euclideanSq (gradient (EinsteinFull.Work.W8.corrector W) 0) /
        (1 + gradient (EinsteinFull.Work.W8.corrector W) 0 (⟨0, by omega⟩ : Fin d)) ∂P ∧
    ((∫ ω, reducedCoefficient ω 0 (⟨0, by omega⟩ : Fin d) (⟨0, by omega⟩ : Fin d)
        ∂Q.measure) - 1 =
      ∫ W, euclideanSq (gradient (EinsteinFull.Work.W8.corrector W) 0) /
        (1 + gradient (EinsteinFull.Work.W8.corrector W) 0 (⟨0, by omega⟩ : Fin d)) ∂P) ∧
    ∫ ω, clockDensity ω 0 ∂Q.measure = 1 := by
  letI : IsProbabilityMeasure P := hP.1
  have hpair := EinsteinFull.Work.W8.measurable_physicalPair (⟨0, by omega⟩ : Fin d)
  have hmeas := measurable_sharpLocalGradient hd
  have hε := EinsteinFull.Work.W8.seedScale_pos d
  have hQ' : Q.measure = P.map (sharpPhysicalPair (⟨0, by omega⟩ : Fin d)
      (EinsteinFull.Work.W8.clockParameter (⟨0, by omega⟩ : Fin d))
      (EinsteinFull.Work.W8.seedScale d) EinsteinFull.Work.W8.corrector_gradient_bound
      (EinsteinFull.Work.W8.density_bounds (⟨0, by omega⟩ : Fin d))) := hQ
  have hm1 : Measurable (fun ω : FieldPair d =>
      sharpLocalGradient hd ω (⟨0, by omega⟩ : Fin d)) :=
    (measurable_pi_apply (⟨0, by omega⟩ : Fin d)).comp hmeas
  have hm2 : Measurable (fun ω : FieldPair d =>
      sharpEnergy (⟨0, by omega⟩ : Fin d) (sharpLocalGradient hd ω)) :=
    (measurable_sharpEnergy' (⟨0, by omega⟩ : Fin d)).comp hmeas
  have hT1 : ∫ ω, sharpLocalGradient hd ω (⟨0, by omega⟩ : Fin d) ∂Q.measure =
      ∫ W, gradient (EinsteinFull.Work.W8.corrector W) 0 (⟨0, by omega⟩ : Fin d) ∂P := by
    rw [hQ, integral_map hpair.aemeasurable hm1.aestronglyMeasurable]
    refine integral_congr_ae (Filter.Eventually.of_forall fun W => ?_)
    show sharpLocalGradient hd (EinsteinFull.Work.W8.physicalPair (⟨0, by omega⟩ : Fin d) W)
        (⟨0, by omega⟩ : Fin d) = _
    rw [sharpLocalGradient_physicalPair hd W]
  have hT2 : ∫ ω, sharpEnergy (⟨0, by omega⟩ : Fin d) (sharpLocalGradient hd ω) ∂Q.measure =
      ∫ W, euclideanSq (gradient (EinsteinFull.Work.W8.corrector W) 0) /
        (1 + gradient (EinsteinFull.Work.W8.corrector W) 0 (⟨0, by omega⟩ : Fin d)) ∂P := by
    rw [hQ, integral_map hpair.aemeasurable hm2.aestronglyMeasurable]
    refine integral_congr_ae (Filter.Eventually.of_forall fun W => ?_)
    show sharpEnergy (⟨0, by omega⟩ : Fin d)
        (sharpLocalGradient hd (EinsteinFull.Work.W8.physicalPair (⟨0, by omega⟩ : Fin d) W)) = _
    rw [sharpLocalGradient_physicalPair hd W]
    rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← hT1]
    exact integral_sharpLocalGradient_eq_zero hd _ _ hε
      EinsteinFull.Work.W8.corrector_gradient_bound
      (EinsteinFull.Work.W8.density_bounds (⟨0, by omega⟩ : Fin d)) P Q.measure hQ'
      Q.stationary hmeas
  · rw [← hT2]
    exact sharpLocalGradient_energy_pos hd Q _ _ EinsteinFull.Work.W8.corrector_gradient_bound
      (EinsteinFull.Work.W8.density_bounds (⟨0, by omega⟩ : Fin d)) hP hε hQ'
  · rw [← hT2]
    exact sharp_integral_a11_identity hd _ _ hε EinsteinFull.Work.W8.corrector_gradient_bound
      (EinsteinFull.Work.W8.density_bounds (⟨0, by omega⟩ : Fin d)) P Q.measure hQ'
      Q.stationary hmeas
  · exact sharp_meanMu_eq_one (⟨0, by omega⟩ : Fin d) _ _ hε
      EinsteinFull.Work.W8.corrector_gradient_bound
      (EinsteinFull.Work.W8.density_bounds (⟨0, by omega⟩ : Fin d)) P Q.measure hQ'
      Q.stationary

end EinsteinFull.Blueprint
