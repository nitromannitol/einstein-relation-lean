import EinsteinFull.Blueprint.G3.Proofs.C6CoarseIdentification

open MeasureTheory ProbabilityTheory
noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation EinsteinRelation.External.AKM
open EinsteinRelation.Correctors EinsteinRelation.ReductionImageV3
open EinsteinRelation.Environment.AKMTestIntegralSupport
open EinsteinFull.External.Source.AKM

/-- An actual-coefficient affine residual has an L² majorant, uniformly in the law. -/
theorem coarse_actual_affine_residual_L2_bound :
    ∀ (_hmom : node_corrector_u2D_construction_u23_smooth_u2D_momentsStmt)
      (d : ℕ) (_hd : 2 ≤ d) (D : StructuralData d),
    ∃ C : ℝ, 0 < C ∧
    ∀ Q : EnvironmentLaw d D.ellipticity D.dependenceRange,
      HasSmoothBounds D Q → ∀ i : Fin d,
    ∃ φ : Corrector (actualCoefficientLaw Q) (unitVector i),
      (∀ᵐ ω ∂physicalReferenceLaw Q, ∀ᵐ y ∂(volume : Measure (Vec d)),
        unitVector i + φ.grad (project (r₀ := D.dependenceRange)
          Q.ellipticity_parameter ω) y =
          (correctorUnitVector i + (canonicalCorrectorGradient Q i :
            Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
              (translate (D.dependenceRange • y) (reduce ω.1))).ofLp) ∧
      ∀ (z : Vec d) (r : ℝ), 1 ≤ r →
      ∃ W : Coefficient d (AKMUpperEllipticity D.ellipticity) → ℝ,
        MemLp W 2 (actualCoefficientLaw Q) ∧
        eLpNorm W 2 (actualCoefficientLaw Q) ≤ ENNReal.ofReal (C * r ^ (-(d : ℝ))) ∧
        (∀ᵐ a ∂actualCoefficientLaw Q,
          let A := ellipticityScale D.ellipticity • homogenizedCoefficient Q
          let B := coarsenedCoefficient a A z r
          let U := ∫ y, heatKernel z r y • (unitVector i + φ.grad a y)
          let F := ∫ y, heatKernel z r y • (a y).mulVec (unitVector i + φ.grad a y)
          euclideanNorm (F - A.mulVec U - B.mulVec (unitVector i)) ≤ W a) := by
  intro hmom d hd D
  obtain ⟨CD, hCD, hD⟩ := coarseCorrector_actual_defectProduct_of_smooth_moments hmom d hd D
  obtain ⟨CM, hCM, hM⟩ := coarseCorrector_actual_matrixGradient_product_L2
    d hd D.ellipticity D.one_le_ellipticity
  let q : ℝ := ((d : ℝ) + 1) * d
  have hq : 0 ≤ q := mul_nonneg (by positivity) (Nat.cast_nonneg d)
  refine ⟨CD + q * CM, add_pos_of_pos_of_nonneg hCD (mul_nonneg hq hCM.le), ?_⟩
  intro Q hs i
  obtain ⟨φ, hid, hφ⟩ := hD Q hs i
  refine ⟨φ, hid, ?_⟩
  intro z r hr
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
  let A := ellipticityScale D.ellipticity • homogenizedCoefficient Q
  let B := fun a : Coefficient d (AKMUpperEllipticity D.ellipticity) =>
    coarsenedCoefficient a A z r
  let N := fun a => Real.sqrt (∫ y, heatKernel z r y *
    euclideanNorm (unitVector i + φ.grad a y) ^ 2)
  let δ := fun a : Coefficient d (AKMUpperEllipticity D.ellipticity) =>
    External.Draft.normalizedCoarseFluxDefect a A z r
  let G := fun a => euclideanNorm (∫ y, heatKernel z r y • φ.grad a y)
  let V := fun a => External.Draft.coarsenedMatrixSize (B a) * G a
  let W := fun a => N a * δ a + q * V a
  obtain ⟨hDm, hDn⟩ := hφ z r hr
  obtain ⟨hMm, hMn⟩ := hM Q i φ z r hr
  have hscaled : eLpNorm (fun a => q * V a) 2 (actualCoefficientLaw Q) ≤
      ENNReal.ofReal (q * (CM * r ^ (-(d : ℝ)))) := by
    calc
      _ = ENNReal.ofReal q * eLpNorm V 2 (actualCoefficientLaw Q) := by
        have he := eLpNorm_const_smul q V 2 (actualCoefficientLaw Q)
        change eLpNorm (fun a => q * V a) 2 (actualCoefficientLaw Q) =
          ‖q‖ₑ * eLpNorm V 2 (actualCoefficientLaw Q) at he
        simpa only [Real.enorm_eq_ofReal_abs, abs_of_nonneg hq] using he
      _ ≤ ENNReal.ofReal q * ENNReal.ofReal (CM * r ^ (-(d : ℝ))) :=
        mul_le_mul' le_rfl hMn
      _ = _ := (ENNReal.ofReal_mul hq).symm
  refine ⟨W, hDm.add (hMm.const_mul q), ?_, ?_⟩
  · calc
      _ ≤ eLpNorm (fun a => N a * δ a) 2 (actualCoefficientLaw Q) +
          eLpNorm (fun a => q * V a) 2 (actualCoefficientLaw Q) :=
        eLpNorm_add_le (by norm_num)
      _ ≤ ENNReal.ofReal (CD * r ^ (-(d : ℝ))) +
          ENNReal.ofReal (q * (CM * r ^ (-(d : ℝ)))) := add_le_add hDn hscaled
      _ = _ := by
        rw [← ENNReal.ofReal_add (mul_nonneg hCD.le (Real.rpow_nonneg hr0.le _))
          (mul_nonneg hq (mul_nonneg hCM.le (Real.rpow_nonneg hr0.le _)))]
        congr 1
        ring
  · have hmass : (∫ y, heatKernel z r y) = 1 := by
      change (∫ y, euclideanHeatKernel (r ^ 2) (y - z)) = 1
      rw [integral_sub_right_eq_self, integral_euclideanHeatKernel (sq_pos_of_pos hr0)]
    have hc : Integrable (fun y => heatKernel z r y • unitVector i) :=
      ((integrable_euclideanHeatKernel (sq_pos_of_pos hr0)).comp_sub_right z).smul_const _
    filter_upwards [coarseCorrector_gaussian_commutatorResidual_le Q i φ hid A z hr0,
      coarseCorrector_gaussianAffine_integrable Q i φ hid z hr0] with a ha hi
    have hg : Integrable (fun y => heatKernel z r y • φ.grad a y) := by
      apply (hi.2.1.sub hc).congr
      exact Filter.Eventually.of_forall (fun y => by
        change heatKernel z r y • (unitVector i + φ.grad a y) -
          heatKernel z r y • unitVector i = heatKernel z r y • φ.grad a y
        simp only [smul_add, add_sub_cancel_left])
    have hU : (∫ y, heatKernel z r y • (unitVector i + φ.grad a y)) - unitVector i =
        ∫ y, heatKernel z r y • φ.grad a y := by
      simp_rw [smul_add]
      rw [integral_add hc hg, integral_smul_const, hmass, one_smul, add_sub_cancel_left]
    apply ha.trans
    change N a * δ a + _ ≤ N a * δ a + q * V a
    apply add_le_add le_rfl
    rw [hU]
    calc
      _ ≤ ((d : ℝ) + 1) * ‖(B a).mulVec (∫ y, heatKernel z r y • φ.grad a y)‖ :=
        euclideanNorm_le_dimension_mul_norm _
      _ ≤ ((d : ℝ) + 1) * ((d : ℝ) * External.Draft.coarsenedMatrixSize (B a) *
          ‖∫ y, heatKernel z r y • φ.grad a y‖) :=
        mul_le_mul_of_nonneg_left (coarseMatrix_mulVec_norm_le_size _ _) (by positivity)
      _ ≤ ((d : ℝ) + 1) * ((d : ℝ) * External.Draft.coarsenedMatrixSize (B a) * G a) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          (Calculus.S1.norm_le_euclideanNorm _)
          (mul_nonneg (Nat.cast_nonneg d) (Real.sqrt_nonneg _))) (by positivity)
      _ = _ := by dsimp only [q, V]; ring

#print axioms coarse_actual_affine_residual_L2_bound
#lint
end EinsteinFull.Blueprint
