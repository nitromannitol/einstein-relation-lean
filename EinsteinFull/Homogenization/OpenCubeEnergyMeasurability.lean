import EinsteinFull.Homogenization.SourceDirichletMeasurability

/-!
# Local measurability on open triadic cubes

The Dirichlet energy of Armstrong, Kuusi and Mourrat,
*Quantitative Stochastic Homogenization and Large-Scale Regularity*, (1.7),
is determined measurably by coefficient observations inside the open cube.
-/

open MeasureTheory
open _root_.Homogenization

namespace EinsteinFull.Homogenization

open EinsteinRelation.Environment.AKMTestIntegralSupport

/-- The source Dirichlet energy is measurable for local observations in the
open triadic cube itself. -/
theorem measurable_sourceDirichletEnergy_openCube {d : ℕ} [NeZero d] {K : ℝ}
    (Q : TriadicCube d) (e : Vec d) :
    @Measurable (Coefficient d K) ℝ
      (localSigma (openCubeSet Q)) _
      (fun a => EinsteinRelation.External.AKM.sourceDirichletEnergy a
        (openCubeSet Q) e) := by
  let U := openCubeSet Q
  have hU : IsOpen U := isOpen_openCubeSet Q
  let : IsFiniteMeasure (volumeMeasureOn U) := by
    simpa [U, volumeMeasureOn] using
      (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume
  have hmeasure : volumeMeasureOn (cubeSet Q) = volumeMeasureOn U := by
    exact volume_restrict_cubeSet_eq_volume_restrict_openCubeSet Q
  obtain ⟨k, hk⟩ := exists_nat_ge K
  have hk' : K ≤ (k : ℝ) + 1 := by linarith
  have hSliceCube := regularCoefficient_aeeQuantitativeEllipticSlice (cubeSet Q)
    (measurableSet_cubeSet Q) k hk'
  have hF := measurable_regularCoefficient_toHilbertMatrixL2_of_le U hU k hk'
  have hMu : @Measurable (Coefficient d K) ℝ (localSigma U) _
      (fun a => Mu (cubeSet Q) (e, 0) (regularCoefficient a).toFun) := by
    have hRewrite : (fun a : Coefficient d K => Mu (cubeSet Q) (e, 0)
        (regularCoefficient a).toFun) = fun a => ⨅ j : ℕ,
          blockEnergyAverage (cubeSet Q) (regularCoefficient a).toFun
            (canonicalMuGeneratorAffineField (U := cubeSet Q) (e, 0)
              (TopologicalSpace.denseSeq (canonicalMuBlockCorrectionGeneratorSubmodule
                (cubeSet Q)) j)) := by
      funext a
      exact mu_eq_iInf_blockEnergyAverage_canonicalAEEMuGenerator Q k
        (rawSlice regularCoefficient hSliceCube a) (e, 0)
    rw [hRewrite]
    apply Measurable.iInf
    intro j
    let X := canonicalMuGeneratorAffineField (U := cubeSet Q) (e, 0)
      (TopologicalSpace.denseSeq (canonicalMuBlockCorrectionGeneratorSubmodule (cubeSet Q)) j)
    have hX : MemBlockL2 U X.eval := by
      have h := canonicalMuGeneratorAffineField_memBlockL2 (U := cubeSet Q) (e, 0)
        (TopologicalSpace.denseSeq (canonicalMuBlockCorrectionGeneratorSubmodule (cubeSet Q)) j)
      simpa [MemBlockL2, hmeasure, X] using h
    have hm := measurable_blockEnergyAverage_carrier hF X hX
    convert hm using 1
    funext a
    unfold blockEnergyAverage volumeAverage
    rw [volume_openCubeSet_eq_volume_cubeSet Q, setIntegral_cubeSet_eq_setIntegral_openCubeSet]
  change @Measurable (Coefficient d K) ℝ (localSigma U) _ _
  convert hMu using 1
  funext a
  rw [sourceDirichletEnergy_eq_Mu_regularCoefficient a hU e]
  exact (Mu_cubeSet_eq_openCubeSet_of_triadicCube Q (e, 0) (regularCoefficient a).toFun).symm

/-- The source Dirichlet energy is measurable for observations in its open
centered triadic cube. -/
theorem measurable_sourceDirichletEnergy_openTriadic {d : ℕ} [NeZero d] {K : ℝ}
    (n : ℕ) (e : Vec d) :
    @Measurable (Coefficient d K) ℝ
      (localSigma (EinsteinRelation.External.AKM.sourceTriadicCube d n)) _
      (fun a => EinsteinRelation.External.AKM.sourceDirichletEnergy a
        (EinsteinRelation.External.AKM.sourceTriadicCube d n) e) := by
  rw [sourceTriadicCube_eq_openCubeSet]
  exact measurable_sourceDirichletEnergy_openCube (originCube d (n : ℤ)) e

/-- The Dirichlet energy on any open triadic cube is measurable for the full
coefficient sigma algebra. -/
theorem measurable_sourceDirichletEnergy_openCube_full {d : ℕ} [NeZero d] {K : ℝ}
    (Q : TriadicCube d) (e : Vec d) :
    Measurable (fun a : Coefficient d K =>
      EinsteinRelation.External.AKM.sourceDirichletEnergy a (openCubeSet Q) e) :=
  (measurable_sourceDirichletEnergy_openCube Q e).mono
    (coefficientLocalSigma_le_coefficientSigma _) le_rfl

/-- Under a finite coefficient law, Dirichlet energy on any open triadic cube
is integrable. -/
theorem integrable_sourceDirichletEnergy_openCube {d : ℕ} [NeZero d] {K : ℝ}
    (hK : 0 ≤ K) (P : Measure (Coefficient d K)) [IsFiniteMeasure P]
    (Q : TriadicCube d) (e : Vec d) :
    Integrable (fun a => EinsteinRelation.External.AKM.sourceDirichletEnergy a
      (openCubeSet Q) e) P := by
  apply (integrable_const ((K / 2) * EinsteinRelation.euclideanSq e)).mono'
    (measurable_sourceDirichletEnergy_openCube_full Q e).aestronglyMeasurable
  exact ae_of_all _ fun a => by
    rw [Real.norm_of_nonneg (EinsteinRelation.External.AKM.sourceDirichletEnergy_nonneg a _ e)]
    exact EinsteinRelation.External.AKM.sourceDirichletEnergy_le_ellipticity hK a _
      (ne_of_lt (volume_openCubeSet_lt_top Q)) e

end EinsteinFull.Homogenization
