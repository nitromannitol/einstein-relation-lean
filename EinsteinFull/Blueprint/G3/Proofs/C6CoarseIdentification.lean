import EinsteinFull.Blueprint.G3.node_p_u3A_covariance_u23_coarse_u2D_identification
import EinsteinFull.Blueprint.G3.node_corrector_u2D_construction_u23_smooth_u2D_moments
import EinsteinFull.Calculus.C6CoarseIdentificationSupport
import EinsteinFull.Calculus.C5TestCLTSupport
import EinsteinRelation.Correctors.HeatKernelScaling

open MeasureTheory
noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation EinsteinRelation.External.AKM
open EinsteinRelation.Correctors EinsteinRelation.ReductionImageV3
open EinsteinRelation.Environment.AKMTestIntegralSupport
open EinsteinFull.External.Source.AKM

/-- The allowed smooth-moments dependency controls the literal isotropic
Gaussian energy of the actual canonical affine gradient, uniformly in the law,
coordinate, center and every positive scale. -/
theorem coarseCorrector_isotropic_energy_of_smooth_moments
    (h : node_corrector_u2D_construction_u23_smooth_u2D_momentsStmt)
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) {p : ℝ} (hp : 2 ≤ p) :
    ∃ C : ℝ, 0 < C ∧
      ∀ Q : EnvironmentLaw d D.ellipticity D.dependenceRange,
        HasSmoothBounds D Q → ∀ (i : Fin d) (z : Vec d) (r : ℝ), 0 < r →
        (∀ᵐ ω ∂reducedLaw Q, Integrable (fun x => heatKernel z r x *
          euclideanNorm (unitVector i + WithLp.ofLp (correctorGradient Q i (translate x ω))) ^ 2)) ∧
        MemLp (fun ω => Real.sqrt (∫ x, heatKernel z r x *
          euclideanNorm (unitVector i + WithLp.ofLp (correctorGradient Q i (translate x ω))) ^ 2))
          (ENNReal.ofReal p) (reducedLaw Q) ∧
        eLpNorm (fun ω => Real.sqrt (∫ x, heatKernel z r x *
          euclideanNorm (unitVector i + WithLp.ofLp (correctorGradient Q i (translate x ω))) ^ 2))
          (ENNReal.ofReal p) (reducedLaw Q) ≤ ENNReal.ofReal C := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_two hp
  obtain ⟨C, hC, hmom⟩ := h d hd D p (by linarith)
  let M : ℝ := C ^ (1 / p)
  have hM : 0 ≤ M := Real.rpow_nonneg hC.le _
  refine ⟨1 + M, by positivity, ?_⟩
  intro Q hs i z r hr
  obtain ⟨hm, hb, _⟩ := hmom Q hs i 0
  have hm' : MemLp (fun ω => correctorGradient Q i ω) (ENNReal.ofReal p)
      (reducedLaw Q) := by
    simpa only [translate_zero] using hm
  have hb' : (∫ ω, ‖correctorGradient Q i ω‖ ^ p ∂reducedLaw Q) ≤ C := by
    simpa only [translate_zero] using hb
  have hn : eLpNorm (fun ω => correctorGradient Q i ω) (ENNReal.ofReal p)
      (reducedLaw Q) ≤ ENNReal.ofReal M := by
    rw [MemLp.eLpNorm_eq_integral_rpow_norm
      (ENNReal.ofReal_ne_zero_iff.mpr hp0) ENNReal.ofReal_ne_top hm']
    simp only [ENNReal.toReal_ofReal hp0.le]
    apply ENNReal.ofReal_le_ofReal
    simpa only [M, one_div] using Real.rpow_le_rpow (z := p⁻¹)
      (integral_nonneg fun _ => Real.rpow_nonneg (norm_nonneg _) _) hb' (inv_nonneg.mpr hp0.le)
  exact coarseCorrector_heatKernel_energy_moment_le Q i hp hM hm' hn z hr

/-- The sole smooth-moments dependency controls the actual normalized source
corrector's Gaussian energy, uniformly before choosing the law or its witness. -/
theorem coarseCorrector_actual_energy_of_smooth_moments
    (h : node_corrector_u2D_construction_u23_smooth_u2D_momentsStmt)
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) {p : ℝ} (hp : 2 ≤ p) :
    ∃ C : ℝ, 0 < C ∧
      ∀ Q : EnvironmentLaw d D.ellipticity D.dependenceRange,
        HasSmoothBounds D Q → ∀ (i : Fin d),
        ∃ φ : Corrector (actualCoefficientLaw Q) (unitVector i),
        (∀ᵐ ω ∂physicalReferenceLaw Q, ∀ᵐ y ∂(volume : Measure (Vec d)),
          unitVector i + φ.grad (project
            (r₀ := D.dependenceRange) Q.ellipticity_parameter ω) y =
            (correctorUnitVector i + (canonicalCorrectorGradient Q i :
              Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
                (translate (D.dependenceRange • y) (reduce ω.1))).ofLp) ∧
        ∀ (z : Vec d) (r : ℝ), 0 < r →
        (∀ᵐ a ∂actualCoefficientLaw Q,
          Integrable (fun y => heatKernel z r y *
            euclideanNorm (unitVector i + φ.grad a y) ^ 2)) ∧
        MemLp (fun a => Real.sqrt (∫ y, heatKernel z r y *
          euclideanNorm (unitVector i + φ.grad a y) ^ 2))
            (ENNReal.ofReal p) (actualCoefficientLaw Q) ∧
        eLpNorm (fun a => Real.sqrt (∫ y, heatKernel z r y *
          euclideanNorm (unitVector i + φ.grad a y) ^ 2))
            (ENNReal.ofReal p) (actualCoefficientLaw Q) ≤ ENNReal.ofReal C := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_two hp
  obtain ⟨C, hC, hmom⟩ := h d hd D p (by linarith)
  let M : ℝ := C ^ (1 / p)
  have hM : 0 ≤ M := Real.rpow_nonneg hC.le _
  refine ⟨1 + M, by positivity, ?_⟩
  intro Q hs i
  let : Fact (2 ≤ d) := ⟨hd⟩
  obtain ⟨φ, hid, _⟩ := exists_coarseCorrector_global_identification_meanFlux Q i
  refine ⟨φ, hid, ?_⟩
  intro z r hr
  obtain ⟨hm, hb, _⟩ := hmom Q hs i 0
  have hm' : MemLp (fun ω => correctorGradient Q i ω) (ENNReal.ofReal p)
      (reducedLaw Q) := by
    simpa only [translate_zero] using hm
  have hb' : (∫ ω, ‖correctorGradient Q i ω‖ ^ p ∂reducedLaw Q) ≤ C := by
    simpa only [translate_zero] using hb
  have hn : eLpNorm (fun ω => correctorGradient Q i ω) (ENNReal.ofReal p)
      (reducedLaw Q) ≤ ENNReal.ofReal M := by
    rw [MemLp.eLpNorm_eq_integral_rpow_norm
      (ENNReal.ofReal_ne_zero_iff.mpr hp0) ENNReal.ofReal_ne_top hm']
    simp only [ENNReal.toReal_ofReal hp0.le]
    apply ENNReal.ofReal_le_ofReal
    simpa only [M, one_div] using Real.rpow_le_rpow (z := p⁻¹)
      (integral_nonneg fun _ => Real.rpow_nonneg (norm_nonneg _) _) hb' (inv_nonneg.mpr hp0.le)
  exact coarseCorrector_actualGaussian_energy_moment_le Q i φ hid hp hM hm' hn z hr

/-- The literal physically normalized coarse matrix has the source L⁴ rate.
The constant is chosen before the environment law and all physical centers
and radii. No measurability of its signed entries is inferred from this norm. -/
theorem covarianceCoarse_matrixSize_L4
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) :
    ∃ C : ℝ, 0 < C ∧
      ∀ Q : EnvironmentLaw d D.ellipticity D.dependenceRange,
      ∀ (r : ℝ), D.dependenceRange ≤ r → ∀ x : Vec d,
      MemLp (fun ω => External.Draft.coarsenedMatrixSize
        (fun j k => covarianceCoarseEntry D Q r x j k ω)) 4 (reducedLaw Q) ∧
      Real.sqrt (Real.sqrt (∫ ω, (External.Draft.coarsenedMatrixSize
        (fun j k => covarianceCoarseEntry D Q r x j k ω)) ^ 4 ∂reducedLaw Q)) ≤
          C * r ^ (-(d : ℝ) / 2) := by
  obtain ⟨C₀, hC₀, hs⟩ := coarseActual_L4_estimates d hd D.ellipticity D.one_le_ellipticity
  let κ := ellipticityScale D.ellipticity
  have hκ : 0 < κ := ellipticityScale_pos D.one_le_ellipticity
  have hρ : 0 < D.dependenceRange := lt_of_lt_of_le zero_lt_one D.one_le_dependenceRange
  refine ⟨κ⁻¹ * C₀ * D.dependenceRange ^ ((d : ℝ) / 2), by positivity, ?_⟩
  intro Q r hr x
  have hr0 : 0 < r := lt_of_lt_of_le hρ hr
  obtain ⟨hB, _, hBn, _⟩ := hs Q (D.dependenceRange⁻¹ • x)
    (r / D.dependenceRange) ((le_div_iff₀ hρ).2 (by simpa using hr))
  let F := fun a : Coefficient d (AKMUpperEllipticity D.ellipticity) =>
    External.Draft.coarsenedMatrixSize
    (External.Source.AKM.coarsenedCoefficient a
      (ellipticityScale D.ellipticity • homogenizedCoefficient Q)
      (D.dependenceRange⁻¹ • x) (r / D.dependenceRange))
  let G := fun ω : FieldPair d => External.Draft.coarsenedMatrixSize
    (fun j k => covarianceCoarseEntry D Q r x j k ω)
  let T := fun ω : PhysicalField d D.ellipticity => reduce ω.1
  have hemb : MeasurableEmbedding T :=
    (Probability.measurableEmbedding_reduce d).comp
      (MeasurableEmbedding.subtype_coe
        (Sharpness.measurableSet_isRegular_fieldPair D.ellipticity))
  have hT : MeasurePreserving T (physicalReferenceLaw Q) (reducedLaw Q) :=
    measurePreserving_physicalReduction Q
  have heq : G ∘ T = fun ω => κ⁻¹ *
      F (project (r₀ := D.dependenceRange) Q.ellipticity_parameter ω) := by
    funext ω
    have hω : reduce ω.1 ∈ physicalReducedRange D.ellipticity := ⟨ω.1, ω.2, rfl⟩
    have hInv : inverseReducePhysical ⟨reduce ω.1, hω⟩ = ω :=
      inverseReduce_reducePhysical ω
    simp only [G, T, Function.comp_apply, covarianceCoarseEntry, dite_eq_left hω, hInv]
    exact coarseMatrix_size_smul _ (inv_nonneg.mpr hκ.le)
  have hG : MemLp G 4 (reducedLaw Q) := by
    rw [← hT.map_eq]
    apply hemb.memLp_map_measure_iff.mpr
    rw [heq]
    exact (hB.comp_measurePreserving (measurePreserving_akmProject Q)).const_mul κ⁻¹
  refine ⟨hG, ?_⟩
  have hi : (∫ ω, G ω ^ 4 ∂reducedLaw Q) =
      ∫ a, (κ⁻¹ * F a) ^ 4 ∂actualCoefficientLaw Q := by
    rw [← hT.map_eq, hemb.integral_map]
    change (∫ ω, ((G ∘ T) ω) ^ 4 ∂physicalReferenceLaw Q) = _
    rw [heq]
    exact (integral_map
      (measurable_project (r₀ := D.dependenceRange) Q.ellipticity_parameter).aemeasurable
      ((hB.const_mul κ⁻¹).aestronglyMeasurable.pow 4)).symm
  change Real.sqrt (Real.sqrt (∫ ω, G ω ^ 4 ∂reducedLaw Q)) ≤ _
  rw [hi, coarseFourthMoment_const_mul _ _ (inv_nonneg.mpr hκ.le)]
  calc
    _ ≤ κ⁻¹ * (C₀ * (r / D.dependenceRange) ^ (-(d : ℝ) / 2)) :=
      mul_le_mul_of_nonneg_left hBn (inv_nonneg.mpr hκ.le)
    _ = _ := by
      rw [Real.div_rpow hr0.le hρ.le, show -(d : ℝ) / 2 = -((d : ℝ) / 2) by ring,
        Real.rpow_neg hρ.le, div_inv_eq_mul]
      ring

/-- The normalized flux-defect contribution for the actual corrector has the
required L² decay. Its L⁴ energy factor uses only the smooth-moments dependency. -/
theorem coarseCorrector_actual_defectProduct_of_smooth_moments
    (h : node_corrector_u2D_construction_u23_smooth_u2D_momentsStmt)
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) :
    ∃ C : ℝ, 0 < C ∧
      ∀ Q : EnvironmentLaw d D.ellipticity D.dependenceRange,
      HasSmoothBounds D Q → ∀ i : Fin d,
      ∃ φ : Corrector (actualCoefficientLaw Q) (unitVector i),
      (∀ᵐ ω ∂physicalReferenceLaw Q, ∀ᵐ y ∂(volume : Measure (Vec d)),
        unitVector i + φ.grad (project
          (r₀ := D.dependenceRange) Q.ellipticity_parameter ω) y =
          (correctorUnitVector i + (canonicalCorrectorGradient Q i :
            Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
              (translate (D.dependenceRange • y) (reduce ω.1))).ofLp) ∧
      ∀ (z : Vec d) (r : ℝ), 1 ≤ r →
      let N := fun a : Coefficient d (AKMUpperEllipticity D.ellipticity) =>
        Real.sqrt (∫ y, heatKernel z r y *
        euclideanNorm (unitVector i + φ.grad a y) ^ 2)
      let δ := fun a : Coefficient d (AKMUpperEllipticity D.ellipticity) =>
        External.Draft.normalizedCoarseFluxDefect a
        (ellipticityScale D.ellipticity • homogenizedCoefficient Q) z r
      MemLp (fun a => N a * δ a) 2 (actualCoefficientLaw Q) ∧
      eLpNorm (fun a => N a * δ a) 2 (actualCoefficientLaw Q) ≤
        ENNReal.ofReal (C * r ^ (-(d : ℝ))) := by
  obtain ⟨CN, hCN, hN⟩ := coarseCorrector_actual_energy_of_smooth_moments
    h d hd D (p := 4) (by norm_num)
  obtain ⟨CD, hCD, hD⟩ := coarseActual_L4_estimates d hd
    D.ellipticity D.one_le_ellipticity
  refine ⟨CN * CD, mul_pos hCN hCD, ?_⟩
  intro Q hs i
  obtain ⟨φ, hid, hNφ⟩ := hN Q hs i
  refine ⟨φ, hid, ?_⟩
  intro z r hr
  dsimp only
  obtain ⟨_, hNm, hNn⟩ := hNφ z r (lt_of_lt_of_le zero_lt_one hr)
  norm_num at hNm hNn
  obtain ⟨_, hDm, _, hDn⟩ := hD Q z r hr
  have hDnorm : eLpNorm (fun a => External.Draft.normalizedCoarseFluxDefect a
      (ellipticityScale D.ellipticity • homogenizedCoefficient Q) z r) 4
        (actualCoefficientLaw Q) ≤ ENNReal.ofReal (CD * r ^ (-(d : ℝ))) := by
    rw [coarseNonnegative_eLpNorm_four
      (fun a => coarseFluxDefect_nonneg a _ z r) hDm]
    exact ENNReal.ofReal_le_ofReal hDn
  have hholder : ENNReal.HolderTriple (ENNReal.ofReal (4 : ℝ))
      (ENNReal.ofReal (4 : ℝ)) (ENNReal.ofReal (2 : ℝ)) := by
    rw [ENNReal.holderTriple_iff,
      ← ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 4),
      ← ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 2),
      ← ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ (4 : ℝ)⁻¹)
        (by norm_num : (0 : ℝ) ≤ (4 : ℝ)⁻¹)]
    norm_num
  have : ENNReal.HolderTriple 4 4 2 := by simpa using hholder
  refine ⟨hNm.fun_mul hDm, ?_⟩
  calc
    _ ≤ eLpNorm _ 4 (actualCoefficientLaw Q) *
        eLpNorm _ 4 (actualCoefficientLaw Q) := by
      simpa only [Pi.smul_apply, smul_eq_mul, Pi.mul_def] using
        (eLpNorm_smul_le_mul_eLpNorm (p := 4) (q := 4) (r := 2)
          hNm.aestronglyMeasurable hDm.aestronglyMeasurable)
    _ ≤ ENNReal.ofReal CN * ENNReal.ofReal (CD * r ^ (-(d : ℝ))) :=
      mul_le_mul' hNn hDnorm
    _ = _ := by rw [← ENNReal.ofReal_mul hCN.le]; congr 1; ring

/-- Once signed source-entry measurability is established, the literal physical
centering is exactly subtraction of its expectation under the reduced law. -/
theorem covarianceCoarse_centered_eq_sub_integral
    {d : ℕ} (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (r : ℝ) (x : Vec d) (j k : Fin d)
    (hm : AEStronglyMeasurable (fun a => External.Source.AKM.coarsenedCoefficient a
      (ellipticityScale D.ellipticity • homogenizedCoefficient Q)
      (D.dependenceRange⁻¹ • x) (r / D.dependenceRange) j k)
        (actualCoefficientLaw Q)) :
    covarianceCenteredCoarseEntry D Q r x j k = fun ω =>
      covarianceCoarseEntry D Q r x j k ω -
        ∫ a, covarianceCoarseEntry D Q r x j k a ∂reducedLaw Q := by
  let κ := ellipticityScale D.ellipticity
  let B := fun a : Coefficient d (AKMUpperEllipticity D.ellipticity) =>
    External.Source.AKM.coarsenedCoefficient a
      (ellipticityScale D.ellipticity • homogenizedCoefficient Q)
      (D.dependenceRange⁻¹ • x) (r / D.dependenceRange) j k
  let T := fun ω : PhysicalField d D.ellipticity => reduce ω.1
  have hemb : MeasurableEmbedding T :=
    (Probability.measurableEmbedding_reduce d).comp
      (MeasurableEmbedding.subtype_coe
        (Sharpness.measurableSet_isRegular_fieldPair D.ellipticity))
  have hT : MeasurePreserving T (physicalReferenceLaw Q) (reducedLaw Q) :=
    measurePreserving_physicalReduction Q
  have heq : covarianceCoarseEntry D Q r x j k ∘ T = fun ω =>
      κ⁻¹ * B (project (r₀ := D.dependenceRange) Q.ellipticity_parameter ω) := by
    funext ω
    have hω : reduce ω.1 ∈ physicalReducedRange D.ellipticity := ⟨ω.1, ω.2, rfl⟩
    have hInv : inverseReducePhysical ⟨reduce ω.1, hω⟩ = ω :=
      inverseReduce_reducePhysical ω
    simp only [T, Function.comp_apply, covarianceCoarseEntry, dite_eq_left hω, hInv]
    rfl
  have hi : (∫ ω, covarianceCoarseEntry D Q r x j k ω ∂reducedLaw Q) =
      κ⁻¹ * ∫ a, B a ∂actualCoefficientLaw Q := by
    rw [← hT.map_eq, hemb.integral_map]
    change (∫ ω, (covarianceCoarseEntry D Q r x j k ∘ T) ω
      ∂physicalReferenceLaw Q) = _
    rw [heq]
    calc
      _ = ∫ a, κ⁻¹ * B a ∂actualCoefficientLaw Q :=
        (integral_map
          (measurable_project (r₀ := D.dependenceRange) Q.ellipticity_parameter).aemeasurable
          (hm.const_mul κ⁻¹)).symm
      _ = _ := integral_const_mul _ _
  funext ω
  rw [hi]
  rfl


/-- Signed source-entry measurability suffices for physical L⁴ membership.
The matrix norm estimate supplies domination, while the measurable embedding
transports the signed observable without inferring its measurability from its norm. -/
theorem covarianceCoarse_entry_memLp_four
    {d : ℕ} (hd : 2 ≤ d) (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (r : ℝ) (hr : D.dependenceRange ≤ r) (x : Vec d) (j k : Fin d)
    (hm : AEStronglyMeasurable (fun a => External.Source.AKM.coarsenedCoefficient a
      (ellipticityScale D.ellipticity • homogenizedCoefficient Q)
      (D.dependenceRange⁻¹ • x) (r / D.dependenceRange) j k)
        (actualCoefficientLaw Q)) :
    MemLp (covarianceCoarseEntry D Q r x j k) 4 (reducedLaw Q) := by
  obtain ⟨C, hC, hs⟩ := coarseActual_L4_estimates d hd D.ellipticity D.one_le_ellipticity
  have hρ : 0 < D.dependenceRange := lt_of_lt_of_le zero_lt_one D.one_le_dependenceRange
  obtain ⟨hB, _⟩ := hs Q (D.dependenceRange⁻¹ • x)
    (r / D.dependenceRange) ((le_div_iff₀ hρ).2 (by simpa using hr))
  have hentry : MemLp (fun a => External.Source.AKM.coarsenedCoefficient a
      (ellipticityScale D.ellipticity • homogenizedCoefficient Q)
      (D.dependenceRange⁻¹ • x) (r / D.dependenceRange) j k)
      4 (actualCoefficientLaw Q) :=
    hB.mono' hm (ae_of_all _ fun a => by
      simpa only [Real.norm_eq_abs] using coarseMatrix_entry_le_size _ j k)
  let T := fun ω : PhysicalField d D.ellipticity => reduce ω.1
  have hemb : MeasurableEmbedding T :=
    (Probability.measurableEmbedding_reduce d).comp
      (MeasurableEmbedding.subtype_coe
        (Sharpness.measurableSet_isRegular_fieldPair D.ellipticity))
  have hT : MeasurePreserving T (physicalReferenceLaw Q) (reducedLaw Q) :=
    measurePreserving_physicalReduction Q
  rw [← hT.map_eq]
  apply hemb.memLp_map_measure_iff.mpr
  have heq : covarianceCoarseEntry D Q r x j k ∘ T = fun ω =>
      (ellipticityScale D.ellipticity)⁻¹ *
        External.Source.AKM.coarsenedCoefficient
          (project (r₀ := D.dependenceRange) Q.ellipticity_parameter ω)
          (ellipticityScale D.ellipticity • homogenizedCoefficient Q)
          (D.dependenceRange⁻¹ • x) (r / D.dependenceRange) j k := by
    funext ω
    have hω : reduce ω.1 ∈ physicalReducedRange D.ellipticity := ⟨ω.1, ω.2, rfl⟩
    have hInv : inverseReducePhysical ⟨reduce ω.1, hω⟩ = ω :=
      inverseReduce_reducePhysical ω
    simp only [T, Function.comp_apply, covarianceCoarseEntry, dite_eq_left hω, hInv]
  rw [heq]
  exact (hentry.comp_measurePreserving (measurePreserving_akmProject Q)).const_mul _

/-- The literal physical centered entry belongs to L² once signed source
measurability is established; centering uses the exact source expectation. -/
theorem covarianceCoarse_centered_entry_memLp_two
    {d : ℕ} (hd : 2 ≤ d) (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (r : ℝ) (hr : D.dependenceRange ≤ r) (x : Vec d) (j k : Fin d)
    (hm : AEStronglyMeasurable (fun a => External.Source.AKM.coarsenedCoefficient a
      (ellipticityScale D.ellipticity • homogenizedCoefficient Q)
      (D.dependenceRange⁻¹ • x) (r / D.dependenceRange) j k)
        (actualCoefficientLaw Q)) :
    MemLp (covarianceCenteredCoarseEntry D Q r x j k) 2 (reducedLaw Q) := by
  rw [covarianceCoarse_centered_eq_sub_integral D Q r x j k hm]
  exact (coarseCentered_secondMoment_le
    ((covarianceCoarse_entry_memLp_four hd D Q r hr x j k hm).mono_exponent
      (by norm_num : (2 : ENNReal) ≤ 4))).1

/-- Coordinatewise signed measurability gives L² membership for the entire
literal matrix-clock error vector. The clock coordinates are zero. -/
theorem covarianceCoarse_error_memLp_two
    {d : ℕ} (hd : 2 ≤ d) (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (r : ℝ) (hr : D.dependenceRange ≤ r) (x : Vec d)
    (hm : ∀ j k : Fin d, AEStronglyMeasurable
      (fun a => External.Source.AKM.coarsenedCoefficient a
        (ellipticityScale D.ellipticity • homogenizedCoefficient Q)
        (D.dependenceRange⁻¹ • x) (r / D.dependenceRange) j k)
      (actualCoefficientLaw Q)) :
    let error := fun ω : FieldPair d => fun a : JointObservationIndex d =>
      match a with
      | .inl (j,k) => (∫ z : Vec d, heatKernel 0 r z *
          commutatorObservation Q j k (translate (x-z) ω)) -
          covarianceCenteredCoarseEntry D Q r x j k ω
      | .inr _ => 0
    MemLp (fun ω => covarianceVectorSize (error ω)) 2 (reducedLaw Q) := by
  intro error
  have hrp : 0 < r := lt_of_lt_of_le
    (lt_of_lt_of_le zero_lt_one D.one_le_dependenceRange) hr
  apply (coarseFiniteVector_secondMoment (v := error) ?_).1
  intro a
  rcases a with ⟨j,k⟩ | a
  · exact (coarseCommutator_heatKernel_memLp_two Q j k x hrp).sub
      (covarianceCoarse_centered_entry_memLp_two hd D Q r hr x j k (hm j k))
  · exact memLp_const (0 : ℝ)

/-- Centering the physical signed entry contracts the error second moment,
since the literal Gaussian commutator has expectation zero. -/
theorem covarianceCoarse_centered_error_secondMoment_le
    {d : ℕ} (hd : 2 ≤ d) (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (r : ℝ) (hr : D.dependenceRange ≤ r) (x : Vec d) (j k : Fin d)
    (hm : AEStronglyMeasurable (fun a => External.Source.AKM.coarsenedCoefficient a
      (ellipticityScale D.ellipticity • homogenizedCoefficient Q)
      (D.dependenceRange⁻¹ • x) (r / D.dependenceRange) j k)
      (actualCoefficientLaw Q)) :
    (∫ ω, ((∫ z : Vec d, heatKernel 0 r z *
        commutatorObservation Q j k (translate (x-z) ω)) -
        covarianceCenteredCoarseEntry D Q r x j k ω)^2 ∂reducedLaw Q) ≤
      ∫ ω, ((∫ z : Vec d, heatKernel 0 r z *
        commutatorObservation Q j k (translate (x-z) ω)) -
        covarianceCoarseEntry D Q r x j k ω)^2 ∂reducedLaw Q := by
  have hrp : 0 < r := lt_of_lt_of_le
    (lt_of_lt_of_le zero_lt_one D.one_le_dependenceRange) hr
  rw [covarianceCoarse_centered_eq_sub_integral D Q r x j k hm]
  exact (coarseCenteredDifference_secondMoment_le
    (coarseCommutator_heatKernel_memLp_two Q j k x hrp)
    ((covarianceCoarse_entry_memLp_four hd D Q r hr x j k hm).mono_exponent
      (by norm_num : (2 : ENNReal) ≤ 4))
    (coarseCommutator_heatKernel_integrable_mean_zero Q j k x hrp).2.2).2

/-- Gradient uniqueness transfers the approved open-unit-ball estimate to
every actual unit corrector, with a constant chosen before the law. -/
theorem coarseCorrector_gradientAverage_L4 (d : ℕ) (hd : 2 ≤ d)
    (K : ℝ) (hK : 1 < K) :
    ∃ C : ℝ, 0 < C ∧ ∀ P : Measure (Coefficient d K), LawHypotheses P →
      ∀ (i : Fin d) (φ : Corrector P (unitVector i)) (z : Vec d) (r : ℝ),
      1 ≤ r →
        (∀ᵐ a ∂P, Integrable (fun y => heatKernel z r y • φ.grad a y)) ∧
        MemLp (fun a => euclideanNorm (∫ y, heatKernel z r y • φ.grad a y)) 4 P ∧
        Real.sqrt (Real.sqrt (∫ a, (euclideanNorm
          (∫ y, heatKernel z r y • φ.grad a y)) ^ 4 ∂P)) ≤
            C * r ^ (-(d : ℝ) / 2) := by
  obtain ⟨C, hC, hsource⟩ := coarseSource_gradientAverage_L4 d hd K hK
  refine ⟨2 * C, mul_pos (by norm_num) hC, ?_⟩
  intro P hP i φ z r hr
  letI : IsProbabilityMeasure P := hP.1
  obtain ⟨S, hS⟩ := hsource P hP
  obtain ⟨hI, hm, hb⟩ := hS (halfDirection i) (halfDirection_mem_ball i) z r hr
  let ψ : Corrector P (halfDirection i) := scaledAKMCorrector φ (1 / 2 : ℝ)
  have hu := Calculus.C5TestCLT.sourceCorrector_grad_ae_unique
    (zero_lt_one.trans hK)
    (fun n => ⟨measurable_translateCoefficient _, hP.2.1 n⟩)
    ψ.toSourceCorrector (S.corrector (halfDirection i))
  have hg : ∀ᵐ a ∂P, ∀ᵐ y ∂(volume : Measure (Vec d)),
      φ.grad a y = (2 : ℝ) • (S.corrector (halfDirection i)).grad a y := by
    filter_upwards [hu] with a ha
    filter_upwards [ha] with y hy
    change (1 / 2 : ℝ) • φ.grad a y = _ at hy
    calc
      φ.grad a y = (2 : ℝ) • ((1 / 2 : ℝ) • φ.grad a y) := by
        simp only [smul_smul]; norm_num
      _ = _ := congrArg (fun v : Vec d => (2 : ℝ) • v) hy
  have hi : ∀ᵐ a ∂P, Integrable (fun y => heatKernel z r y • φ.grad a y) := by
    filter_upwards [hI, hg] with a ha hga
    apply (ha.smul (2 : ℝ)).congr
    filter_upwards [hga] with y hy
    change (2 : ℝ) • (heatKernel z r y • (S.corrector (halfDirection i)).grad a y) =
      heatKernel z r y • φ.grad a y
    rw [hy, smul_comm]
  have he : (fun a => euclideanNorm (∫ y, heatKernel z r y • φ.grad a y)) =ᵐ[P]
      (fun a => 2 * euclideanNorm
        (∫ y, heatKernel z r y • (S.corrector (halfDirection i)).grad a y)) := by
    filter_upwards [hg] with a ha
    have heq : (∫ y, heatKernel z r y • φ.grad a y) =
        (2 : ℝ) • ∫ y, heatKernel z r y • (S.corrector (halfDirection i)).grad a y := by
      rw [← integral_smul]
      apply integral_congr_ae
      filter_upwards [ha] with y hy
      rw [hy, smul_comm]
    rw [heq, euclideanNorm_smul _ (by norm_num)]
  refine ⟨hi, (hm.const_mul (2 : ℝ)).ae_eq he.symm, ?_⟩
  have he4 : (∫ a, (euclideanNorm (∫ y, heatKernel z r y • φ.grad a y)) ^ 4 ∂P) =
      ∫ a, (2 * euclideanNorm
        (∫ y, heatKernel z r y • (S.corrector (halfDirection i)).grad a y)) ^ 4 ∂P :=
    integral_congr_ae (he.fun_comp fun t : ℝ => t ^ 4)
  rw [he4, coarseFourthMoment_const_mul P _ (by norm_num : (0 : ℝ) ≤ 2)]
  calc
    _ ≤ 2 * (C * r ^ (-(d : ℝ) / 2)) := mul_le_mul_of_nonneg_left hb (by norm_num)
    _ = _ := by ring

/-- Both factors in the coarse-matrix/averaged-gradient error have optimal
L⁴ decay; their actual-law product therefore has the required L² rate. -/
theorem coarseCorrector_actual_matrixGradient_product_L2
    (d : ℕ) (hd : 2 ≤ d) (L : ℝ) (hL : 1 ≤ L) :
    ∃ C : ℝ, 0 < C ∧ ∀ {r₀ : ℝ} (Q : EnvironmentLaw d L r₀)
      (i : Fin d) (φ : Corrector (actualCoefficientLaw Q) (unitVector i))
      (z : Vec d) (r : ℝ), 1 ≤ r →
      let B := fun a => External.Draft.coarsenedMatrixSize
        (coarsenedCoefficient a (ellipticityScale L • homogenizedCoefficient Q) z r)
      let G := fun a => euclideanNorm (∫ y, heatKernel z r y • φ.grad a y)
      MemLp (fun a => B a * G a) 2 (actualCoefficientLaw Q) ∧
      eLpNorm (fun a => B a * G a) 2 (actualCoefficientLaw Q) ≤
        ENNReal.ofReal (C * r ^ (-(d : ℝ))) := by
  obtain ⟨CB, hCB, hB⟩ := coarseActual_L4_estimates d hd L hL
  obtain ⟨CG, hCG, hG⟩ := coarseCorrector_gradientAverage_L4 d hd
    (AKMUpperEllipticity L) (one_lt_AKMUpperEllipticity hL)
  refine ⟨CB * CG, mul_pos hCB hCG, ?_⟩
  intro r₀ Q i φ z r hr
  dsimp only
  obtain ⟨hBm, _, hBn, _⟩ := hB Q z r hr
  obtain ⟨_, hGm, hGn⟩ := hG (actualCoefficientLaw Q)
    (lawHypotheses_actualCoefficientLaw Q) i φ z r hr
  have hBN : eLpNorm (fun a => External.Draft.coarsenedMatrixSize
      (coarsenedCoefficient a (ellipticityScale L • homogenizedCoefficient Q) z r))
      4 (actualCoefficientLaw Q) ≤ ENNReal.ofReal (CB * r ^ (-(d : ℝ) / 2)) := by
    rw [coarseNonnegative_eLpNorm_four (F := fun a => External.Draft.coarsenedMatrixSize
      (coarsenedCoefficient a (ellipticityScale L • homogenizedCoefficient Q) z r))
      (fun a => Real.sqrt_nonneg _) hBm]
    exact ENNReal.ofReal_le_ofReal hBn
  have hGN : eLpNorm (fun a => euclideanNorm
      (∫ y, heatKernel z r y • φ.grad a y)) 4 (actualCoefficientLaw Q) ≤
      ENNReal.ofReal (CG * r ^ (-(d : ℝ) / 2)) := by
    rw [coarseNonnegative_eLpNorm_four (F := fun a => euclideanNorm
      (∫ y, heatKernel z r y • φ.grad a y)) (fun a => Real.sqrt_nonneg _) hGm]
    exact ENNReal.ofReal_le_ofReal hGn
  have hholder : ENNReal.HolderTriple (ENNReal.ofReal (4 : ℝ))
      (ENNReal.ofReal (4 : ℝ)) (ENNReal.ofReal (2 : ℝ)) := by
    rw [ENNReal.holderTriple_iff,
      ← ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 4),
      ← ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 2),
      ← ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ (4 : ℝ)⁻¹)
        (by norm_num : (0 : ℝ) ≤ (4 : ℝ)⁻¹)]
    norm_num
  have : ENNReal.HolderTriple 4 4 2 := by simpa using hholder
  refine ⟨hBm.fun_mul hGm, ?_⟩
  calc
    _ ≤ eLpNorm _ 4 (actualCoefficientLaw Q) *
        eLpNorm _ 4 (actualCoefficientLaw Q) := by
      simpa only [Pi.smul_apply, smul_eq_mul, Pi.mul_def] using
        (eLpNorm_smul_le_mul_eLpNorm (p := 4) (q := 4) (r := 2)
          hBm.aestronglyMeasurable hGm.aestronglyMeasurable)
    _ ≤ ENNReal.ofReal (CB * r ^ (-(d : ℝ) / 2)) *
        ENNReal.ofReal (CG * r ^ (-(d : ℝ) / 2)) := mul_le_mul' hBN hGN
    _ = _ := by
      rw [← ENNReal.ofReal_mul (mul_nonneg hCB.le
        (Real.rpow_nonneg (le_trans zero_le_one hr) _))]
      congr 1
      rw [mul_mul_mul_comm, ← Real.rpow_add (lt_of_lt_of_le zero_lt_one hr)]
      congr 2
      ring

/-- The actual reduced canonical gradient inherits the optimal Gaussian L⁴
bound at the normalized spatial scale, without an identification premise. -/
theorem coarseCanonical_rescaled_gradientAverage_L4
    (d : ℕ) (hd : 2 ≤ d) (L : ℝ) (hL : 1 ≤ L) :
    ∃ C : ℝ, 0 < C ∧ ∀ {r₀ : ℝ} (Q : EnvironmentLaw d L r₀)
      (i : Fin d) (z : Vec d) (r : ℝ), 1 ≤ r →
      (∀ᵐ ω ∂reducedLaw Q, Integrable (fun y => heatKernel z r y •
        WithLp.ofLp (correctorGradient Q i (translate (r₀ • y) ω)))) ∧
      MemLp (fun ω => euclideanNorm (∫ y, heatKernel z r y •
        WithLp.ofLp (correctorGradient Q i (translate (r₀ • y) ω)))) 4 (reducedLaw Q) ∧
      Real.sqrt (Real.sqrt (∫ ω, (euclideanNorm (∫ y, heatKernel z r y •
        WithLp.ofLp (correctorGradient Q i (translate (r₀ • y) ω)))) ^ 4 ∂reducedLaw Q)) ≤
          C * r ^ (-(d : ℝ) / 2) := by
  obtain ⟨C, hC, hgrad⟩ := coarseCorrector_gradientAverage_L4 d hd
    (AKMUpperEllipticity L) (one_lt_AKMUpperEllipticity hL)
  refine ⟨C, hC, ?_⟩
  intro r₀ Q i z r hr
  letI : Fact (2 ≤ d) := ⟨hd⟩
  obtain ⟨φ, hid, _⟩ := exists_coarseCorrector_global_identification_meanFlux Q i
  obtain ⟨hI, hm, hb⟩ := hgrad (actualCoefficientLaw Q)
    (lawHypotheses_actualCoefficientLaw Q) i φ z r hr
  let N := fun a : Coefficient d (AKMUpperEllipticity L) =>
    euclideanNorm (∫ y, heatKernel z r y • φ.grad a y)
  let G := fun ω : FieldPair d => euclideanNorm (∫ y, heatKernel z r y •
    WithLp.ofLp (correctorGradient Q i (translate (r₀ • y) ω)))
  let T := fun ω : PhysicalField d L => reduce ω.1
  have hemb : MeasurableEmbedding T :=
    (Probability.measurableEmbedding_reduce d).comp
      (MeasurableEmbedding.subtype_coe (Sharpness.measurableSet_isRegular_fieldPair L))
  have hT : MeasurePreserving T (physicalReferenceLaw Q) (reducedLaw Q) :=
    measurePreserving_physicalReduction Q
  have hu : (correctorUnitVector i).ofLp = unitVector i := by
    ext j
    simp [correctorUnitVector, unitVector, Pi.single_apply, eq_comm]
  have hg : ∀ᵐ ω ∂physicalReferenceLaw Q, ∀ᵐ y ∂(volume : Measure (Vec d)),
      φ.grad (project (r₀ := r₀) Q.ellipticity_parameter ω) y =
        WithLp.ofLp (correctorGradient Q i (translate (r₀ • y) (T ω))) := by
    filter_upwards [hid] with ω hω
    filter_upwards [hω] with y hy
    have hv : WithLp.ofLp ((canonicalCorrectorGradient Q i :
        Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
        (translate (r₀ • y) (reduce ω.1))) =
        WithLp.ofLp (correctorGradient Q i (translate (r₀ • y) (T ω))) := by
      rfl
    apply add_left_cancel (a := unitVector i)
    rw [← hv]
    simpa only [WithLp.ofLp_add, hu] using hy
  have heq : (fun ω => N (project (r₀ := r₀) Q.ellipticity_parameter ω)) =ᵐ[
      physicalReferenceLaw Q] (G ∘ T) := by
    filter_upwards [hg] with ω hω
    apply congrArg euclideanNorm
    apply integral_congr_ae
    filter_upwards [hω] with y hy
    exact congrArg (fun v : Vec d => heatKernel z r y • v) hy
  have hG : MemLp G 4 (reducedLaw Q) := by
    rw [← hT.map_eq]
    apply hemb.memLp_map_measure_iff.mpr
    exact (hm.comp_measurePreserving (measurePreserving_akmProject Q)).ae_eq heq
  refine ⟨?_, hG, ?_⟩
  · have hi := (measurePreserving_akmProject Q).quasiMeasurePreserving.ae hI
    have hiT : ∀ᵐ ω ∂physicalReferenceLaw Q, Integrable (fun y => heatKernel z r y •
        WithLp.ofLp (correctorGradient Q i (translate (r₀ • y) (T ω)))) := by
      filter_upwards [hi, hg] with ω hω hωg
      apply hω.congr
      filter_upwards [hωg] with y hy
      exact congrArg (fun v : Vec d => heatKernel z r y • v) hy
    let p : FieldPair d → Prop := fun ω => Integrable (fun y => heatKernel z r y •
      WithLp.ofLp (correctorGradient Q i (translate (r₀ • y) ω)))
    have ha : ∀ᵐ ω ∂Measure.map T (physicalReferenceLaw Q), p ω :=
      hemb.ae_map_iff.mpr hiT
    change ∀ᵐ ω ∂reducedLaw Q, p ω
    rw [← hT.map_eq]
    exact ha
  · have hi : (∫ ω, G ω ^ 4 ∂reducedLaw Q) =
        ∫ a, N a ^ 4 ∂actualCoefficientLaw Q := by
      rw [← hT.map_eq, hemb.integral_map]
      calc
        _ = ∫ ω, N (project (r₀ := r₀) Q.ellipticity_parameter ω) ^ 4
            ∂physicalReferenceLaw Q :=
          integral_congr_ae (heq.symm.fun_comp fun t : ℝ => t ^ 4)
        _ = _ := (integral_map
          (measurable_project (r₀ := r₀) Q.ellipticity_parameter).aemeasurable
          (hm.aestronglyMeasurable.pow 4)).symm
    change Real.sqrt (Real.sqrt (∫ ω, G ω ^ 4 ∂reducedLaw Q)) ≤ _
    rw [hi]
    exact hb

/-- The literal isotropic Gaussian average has the exact physical dilation
formula, for total Bochner integrals as well as integrable observables. -/
theorem coarseHeatKernel_integral_rescale {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : Vec d → E) (z : Vec d) {r c : ℝ} (hr : 0 < r) (hc : 0 < c) :
    (∫ y, heatKernel z r y • f (c • y)) =
      ∫ y, heatKernel (c • z) (c * r) y • f y := by
  have hk (y : Vec d) : heatKernel (c • z) (c * r) (c • y) =
      (c ^ d)⁻¹ * heatKernel z r y := by
    unfold heatKernel
    rw [← smul_sub, mul_pow, euclideanHeatKernel_scale hc (sq_pos_of_pos hr)]
  have h := Measure.integral_comp_smul (volume : Measure (Vec d))
    (fun y => heatKernel (c • z) (c * r) y • f y) c
  simp only [Module.finrank_pi, Fintype.card_fin,
    abs_of_nonneg (inv_nonneg.mpr (pow_nonneg hc.le _)), hk, mul_smul] at h
  rw [integral_smul] at h
  exact smul_right_injective _ (inv_ne_zero (pow_ne_zero d hc.ne')) h

/-- The canonical Gaussian gradient average has the optimal fourth moment
at the literal physical radius and center, uniformly before choosing the law. -/
theorem coarseCanonical_physical_gradientAverage_L4
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) :
    ∃ C : ℝ, 0 < C ∧ ∀ Q : EnvironmentLaw d D.ellipticity D.dependenceRange,
      ∀ (i : Fin d) (x : Vec d) (r : ℝ), D.dependenceRange ≤ r →
      MemLp (fun ω => euclideanNorm (∫ y, heatKernel x r y •
        WithLp.ofLp (correctorGradient Q i (translate y ω)))) 4 (reducedLaw Q) ∧
      Real.sqrt (Real.sqrt (∫ ω, (euclideanNorm (∫ y, heatKernel x r y •
        WithLp.ofLp (correctorGradient Q i (translate y ω)))) ^ 4 ∂reducedLaw Q)) ≤
          C * r ^ (-(d : ℝ) / 2) := by
  obtain ⟨C, hC, hgrad⟩ := coarseCanonical_rescaled_gradientAverage_L4
    d hd D.ellipticity D.one_le_ellipticity
  have hρ : 0 < D.dependenceRange :=
    lt_of_lt_of_le zero_lt_one D.one_le_dependenceRange
  refine ⟨C * D.dependenceRange ^ ((d : ℝ) / 2),
    mul_pos hC (Real.rpow_pos_of_pos hρ _), ?_⟩
  intro Q i x r hr
  have hrp : 0 < r := lt_of_lt_of_le hρ hr
  have hs : 1 ≤ r / D.dependenceRange := (one_le_div hρ).mpr hr
  obtain ⟨_, hm, hb⟩ := hgrad Q i (D.dependenceRange⁻¹ • x)
    (r / D.dependenceRange) hs
  have heq : (fun ω : FieldPair d => euclideanNorm (∫ y,
      heatKernel (D.dependenceRange⁻¹ • x) (r / D.dependenceRange) y •
        WithLp.ofLp (correctorGradient Q i (translate (D.dependenceRange • y) ω)))) =
      (fun ω => euclideanNorm (∫ y, heatKernel x r y •
        WithLp.ofLp (correctorGradient Q i (translate y ω)))) := by
    funext ω
    apply congrArg euclideanNorm
    have hh := coarseHeatKernel_integral_rescale
      (fun y => WithLp.ofLp (correctorGradient Q i (translate y ω)))
      (D.dependenceRange⁻¹ • x) (div_pos hrp hρ) hρ
    simpa only [smul_smul, mul_inv_cancel₀ hρ.ne', one_smul,
      mul_div_cancel₀ _ hρ.ne'] using hh
  rw [heq] at hm
  have he4 := congrArg (fun F : FieldPair d → ℝ =>
    Real.sqrt (Real.sqrt (∫ ω, F ω ^ 4 ∂reducedLaw Q))) heq
  change Real.sqrt (Real.sqrt (∫ ω, _ ^ 4 ∂reducedLaw Q)) = _ at he4
  rw [he4] at hb
  refine ⟨hm, hb.trans ?_⟩
  rw [Real.div_rpow hrp.le hρ.le,
    show -(d : ℝ) / 2 = -((d : ℝ) / 2) by ring,
    Real.rpow_neg hρ.le, div_inv_eq_mul]
  exact le_of_eq (by ring)

end EinsteinFull.Blueprint
