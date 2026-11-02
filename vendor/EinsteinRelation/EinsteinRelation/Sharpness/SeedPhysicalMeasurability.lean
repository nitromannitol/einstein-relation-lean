import EinsteinRelation.Sharpness.FieldDerivativeMeasurability
import EinsteinRelation.Sharpness.SeedFieldDerivatives
import EinsteinRelation.Sharpness.SmoothFields
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/-! # Measurability of the physical evaluations of the canonical scaled seed

Source: `paper/main.tex`, Proposition 7.1, Step 1 (lines 1212–1218) and the physical fields of
lines 1218–1231. The scaled seed is `ψ_W = ε * seedField d W`, where `ε` is the scale of
`exists_seedField_gradient_scale`. It is chosen before the sample `W`, the point `x`, and the
parameter `δ`, and its Euclidean gradient is at most `1/4` for every sample.

For every sample the scaled seed is `C^∞`, and its jacobian factor `1 + ∂ᵢψ` is at least `3/4`.
Hence each coefficient entry is continuous (`SmoothFields`). The coefficient column
`y ↦ a(y)_{m i}` is packaged in the compact-open carrier `C(Vec d, ℝ)`, whose point evaluations are
measurable in the sample by the `FieldMeasurability` bridge. The parent `FieldDerivativeMeasurability`
producer then makes each coordinate derivative of that column measurable, and the clock density is
the finite sum of these derivatives. The potential `-(1/2) log μ` and the physical coefficient
`μ⁻¹ a` follow from their literal formulas.

No positivity or bound on the density is assumed: the inverse and the logarithm are measurable
functions of the sample without it. Locality and joint finite range are not claimed here.
-/

open MeasureTheory
open scoped BigOperators

namespace EinsteinRelation.Sharpness

/-- The coordinate derivative of a constant multiple is the constant times the coordinate
derivative, from the Fréchet derivative. -/
private theorem physicalEval_coordinateDerivative_const_mul {d : ℕ} (c : ℝ) (f : Vec d → ℝ)
    (x : Vec d) (hf : DifferentiableAt ℝ f x) (i : Fin d) :
    coordinateDerivative i (fun y => c * f y) x = c * coordinateDerivative i f x := by
  unfold coordinateDerivative
  rw [fderiv_const_mul hf c, ContinuousLinearMap.smul_apply, smul_eq_mul]

/-- The `i`-th gradient coordinate of the scaled canonical seed is `ε` times the actual singleton
iterated coordinate derivative of the seed, which is the jet producer of `SeedFieldDerivatives`. -/
private theorem physicalEval_gradient_apply_eq {d : ℕ} (ε : ℝ) (W : NoiseSample d) (x : Vec d)
    (i : Fin d) :
    gradient (fun y => ε * seedField d W y) x i =
      ε * iteratedCoordinateDerivative [i] (seedField d W) x :=
  physicalEval_coordinateDerivative_const_mul ε (seedField d W) x
    ((contDiff_seedField d W).differentiable (by simp) x) i

/-- The spatial gradient of the scaled canonical seed at a fixed point is measurable in the
sample. -/
private theorem physicalEval_measurable_gradient {d : ℕ} (ε : ℝ) (x : Vec d) :
    Measurable (fun W : NoiseSample d => gradient (fun y => ε * seedField d W y) x) := by
  refine measurable_pi_iff.mpr fun l => ?_
  simp only [physicalEval_gradient_apply_eq]
  exact (measurable_seedField_iteratedCoordinateDerivative d [l] x).const_mul ε

/-- Each coordinate of a vector is bounded by its Euclidean norm. -/
private theorem physicalEval_abs_coord_le_euclideanNorm {d : ℕ} (i : Fin d) (x : Vec d) :
    |x i| ≤ euclideanNorm x := by
  unfold euclideanNorm
  apply Real.abs_le_sqrt
  unfold euclideanSq dot
  rw [pow_two]
  exact Finset.single_le_sum (f := fun j => x j * x j)
    (fun j _ => mul_self_nonneg (x j)) (Finset.mem_univ i)

/-- Under the gradient bound `‖∇ψ‖ ≤ 1/4`, the jacobian factor `1 + ∂ᵢψ` is at least `3/4`. -/
private theorem physicalEval_three_quarters_le_jacobianFactor {d : ℕ} (i : Fin d) (g : Vec d)
    (hg : euclideanNorm g ≤ (1/4 : ℝ)) : (3/4 : ℝ) ≤ jacobianFactor i g := by
  have hcoord : |g i| ≤ euclideanNorm g := physicalEval_abs_coord_le_euclideanNorm i g
  have hneg : -|g i| ≤ g i := neg_abs_le (g i)
  unfold jacobianFactor
  linarith

/-- Along every sample of the scaled canonical seed, the jacobian factor is nonzero everywhere. -/
private theorem physicalEval_jacobianFactor_ne_zero {d : ℕ} (i : Fin d) (ε : ℝ)
    (hgrad : ∀ (W : NoiseSample d) (x : Vec d),
      euclideanNorm (gradient (fun y => ε * seedField d W y) x) ≤ (1/4 : ℝ))
    (W : NoiseSample d) (x : Vec d) :
    jacobianFactor i (gradient (fun y => ε * seedField d W y) x) ≠ 0 :=
  (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 3 / 4)
    (physicalEval_three_quarters_le_jacobianFactor i _ (hgrad W x))).ne'

/-- The scaled canonical seed is `C^∞` for every sample. -/
private theorem physicalEval_contDiff_scaled {d : ℕ} (ε : ℝ) (W : NoiseSample d) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y => ε * seedField d W y) :=
  contDiff_const.mul (contDiff_seedField d W)

/-- A coordinate projection on `Vec d` is Borel measurable. -/
private theorem physicalEval_measurable_coord {d : ℕ} (k : Fin d) :
    Measurable (fun g : Vec d => g k) :=
  measurable_pi_apply k

/-- The jacobian factor `1 + gᵢ` is Borel in the gradient, with no positivity hypothesis. -/
private theorem physicalEval_measurable_jacobianFactor {d : ℕ} (i : Fin d) :
    Measurable (fun g : Vec d => jacobianFactor i g) := by
  unfold jacobianFactor
  exact measurable_const.add (physicalEval_measurable_coord i)

/-- Entrywise formula for the candidate inverse, unfolding the rank-one definition. -/
private theorem physicalEval_inverseCandidate_apply {d : ℕ} (i : Fin d) (g : Vec d) (j k : Fin d) :
    inverseCandidate i g j k =
      (if j = k then (1 : ℝ) else 0) - (jacobianFactor i g)⁻¹ * (unitVector i j * g k) := by
  simp only [inverseCandidate, outer, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.one_apply]

/-- Each entry of the candidate inverse is Borel in the gradient, using the total inverse of
`1 + gᵢ`. -/
private theorem physicalEval_measurable_inverseCandidate {d : ℕ} (i j k : Fin d) :
    Measurable (fun g : Vec d => inverseCandidate i g j k) := by
  simp only [physicalEval_inverseCandidate_apply]
  exact measurable_const.sub ((physicalEval_measurable_jacobianFactor i).inv.mul
    ((physicalEval_measurable_coord k).const_mul (unitVector i j)))

/-- The coefficient entry as the jacobian factor times an explicit finite sum. -/
private theorem physicalEval_coefficient_apply_eq_sum {d : ℕ} (i : Fin d) (g : Vec d)
    (j k : Fin d) :
    coefficient i g j k = jacobianFactor i g *
      ∑ l, inverseCandidate i g j l * inverseCandidate i g k l := by
  simp only [coefficient, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply,
    Matrix.transpose_apply]

/-- Each coefficient entry is Borel in the gradient: a product of measurable factors, summed
over the finite index set. -/
private theorem physicalEval_measurable_coefficient {d : ℕ} (i j k : Fin d) :
    Measurable (fun g : Vec d => coefficient i g j k) := by
  simp only [physicalEval_coefficient_apply_eq_sum]
  exact (physicalEval_measurable_jacobianFactor i).mul
    (Finset.measurable_sum Finset.univ fun l _ =>
      (physicalEval_measurable_inverseCandidate i j l).mul
        (physicalEval_measurable_inverseCandidate i k l))

/-- The coefficient field of the scaled canonical seed, evaluated at a point `x`, is Borel in the
sample. -/
private theorem physicalEval_measurable_coefficientField {d : ℕ} (i : Fin d) (ε : ℝ) (j k : Fin d)
    (x : Vec d) :
    Measurable (fun W : NoiseSample d =>
      coefficientField i (fun y => ε * seedField d W y) x j k) :=
  (physicalEval_measurable_coefficient i j k).comp (physicalEval_measurable_gradient ε x)

/-- The coefficient entry `(j, k)` of the scaled canonical seed as a continuous function of the
position, for each sample. Continuity uses the jacobian bound from the gradient estimate. -/
private noncomputable def physicalEval_entryCM {d : ℕ} (i : Fin d) (ε : ℝ)
    (hgrad : ∀ (W : NoiseSample d) (x : Vec d),
      euclideanNorm (gradient (fun y => ε * seedField d W y) x) ≤ (1/4 : ℝ))
    (j k : Fin d) (W : NoiseSample d) : C(Vec d, ℝ) :=
  ⟨fun y => coefficientField i (fun z => ε * seedField d W z) y j k,
    (contDiff_coefficientField_entry i (fun z => ε * seedField d W z)
      (physicalEval_contDiff_scaled ε W)
      (physicalEval_jacobianFactor_ne_zero i ε hgrad W) j k).continuous⟩

/-- The packaged coefficient entry is Borel measurable in the sample, by the point-evaluation
bridge for the compact-open carrier. -/
private theorem physicalEval_measurable_entryCM {d : ℕ} (i : Fin d) (ε : ℝ)
    (hgrad : ∀ (W : NoiseSample d) (x : Vec d),
      euclideanNorm (gradient (fun y => ε * seedField d W y) x) ≤ (1/4 : ℝ))
    (j k : Fin d) :
    @Measurable (NoiseSample d) C(Vec d, ℝ) inferInstance (borel C(Vec d, ℝ))
      (physicalEval_entryCM i ε hgrad j k) :=
  measurable_continuousMap_of_evaluations (physicalEval_entryCM i ε hgrad j k)
    fun x => physicalEval_measurable_coefficientField i ε j k x

/-- The clock density is the finite sum of coordinate derivatives of the entries `a_{m i}` of
the first coefficient column. Source: `paper/main.tex`, lines 1218–1231 and `densityField`. -/
private theorem physicalEval_densityField_eq_sum {d : ℕ} (i : Fin d) (δ : ℝ) (ψ : Vec d → ℝ)
    (x : Vec d) :
    densityField i δ ψ x =
      1 + δ / 2 * ∑ m, coordinateDerivative m (fun y => coefficientField i ψ y m i) x := by
  have hcol : ∀ y m, (coefficientField i ψ y).mulVec (unitVector i) m =
      coefficientField i ψ y m i := by
    intro y m
    simp [Matrix.mulVec, dotProduct, unitVector, Pi.single_apply, mul_ite]
  unfold densityField divergence
  simp only [hcol]

/-- The clock density of the scaled canonical seed is Borel measurable in the sample, for every
`δ` and every point `x`. No positivity or bound on the density is used. -/
private theorem physicalEval_measurable_densityField {d : ℕ} (i : Fin d) (ε : ℝ)
    (hgrad : ∀ (W : NoiseSample d) (x : Vec d),
      euclideanNorm (gradient (fun y => ε * seedField d W y) x) ≤ (1/4 : ℝ))
    (δ : ℝ) (x : Vec d) :
    Measurable (fun W : NoiseSample d => densityField i δ (fun y => ε * seedField d W y) x) := by
  have hsum : ∀ m ∈ (Finset.univ : Finset (Fin d)),
      Measurable (fun W : NoiseSample d =>
        coordinateDerivative m (fun y => coefficientField i (fun z => ε * seedField d W z) y m i) x) :=
    fun m _ => measurable_coordinateDerivative_of_measurable_continuousMap
      (physicalEval_entryCM i ε hgrad m i) (physicalEval_measurable_entryCM i ε hgrad m i) m x
  simp only [physicalEval_densityField_eq_sum]
  exact measurable_const.add (measurable_const.mul (Finset.measurable_sum Finset.univ hsum))

/-- The physical potential `-(1/2) log μ` of the scaled canonical seed is Borel measurable in the
sample. The logarithm is measurable everywhere, so no positivity of `μ` is used. -/
private theorem physicalEval_measurable_potentialField {d : ℕ} (i : Fin d) (ε : ℝ)
    (hgrad : ∀ (W : NoiseSample d) (x : Vec d),
      euclideanNorm (gradient (fun y => ε * seedField d W y) x) ≤ (1/4 : ℝ))
    (δ : ℝ) (x : Vec d) :
    Measurable (fun W : NoiseSample d => potentialField i δ (fun y => ε * seedField d W y) x) := by
  simp only [potentialField]
  exact measurable_const.mul (physicalEval_measurable_densityField i ε hgrad δ x).log

/-- The physical coefficient entry is the product of the total inverse of the density and the
coefficient entry. Source: `paper/main.tex`, lines 1218–1231 and `physicalCoefficientField`. -/
private theorem physicalEval_physicalCoefficientField_apply {d : ℕ} (i : Fin d) (δ : ℝ)
    (ψ : Vec d → ℝ) (x : Vec d) (j k : Fin d) :
    physicalCoefficientField i δ ψ x j k =
      (densityField i δ ψ x)⁻¹ * coefficientField i ψ x j k := by
  simp only [physicalCoefficientField, Matrix.smul_apply, smul_eq_mul]

/-- Each physical coefficient entry of the scaled canonical seed is Borel measurable in the sample,
for every `δ` and point `x`. -/
private theorem physicalEval_measurable_physicalCoefficientField {d : ℕ} (i : Fin d) (ε : ℝ)
    (hgrad : ∀ (W : NoiseSample d) (x : Vec d),
      euclideanNorm (gradient (fun y => ε * seedField d W y) x) ≤ (1/4 : ℝ))
    (δ : ℝ) (x : Vec d) (j k : Fin d) :
    Measurable (fun W : NoiseSample d =>
      physicalCoefficientField i δ (fun y => ε * seedField d W y) x j k) := by
  simp only [physicalEval_physicalCoefficientField_apply]
  exact (physicalEval_measurable_densityField i ε hgrad δ x).inv.mul
    (physicalEval_measurable_coefficientField i ε j k x)

/-- Source: `paper/main.tex`, Proposition 7.1, Step 1, lines 1212–1218, and the physical fields of
lines 1218–1231. For every dimension and coordinate there is one scale `ε > 0`, given by
`exists_seedField_gradient_scale` and chosen before the sample, the point, and `δ`, such that the
scaled canonical seed has Euclidean gradient at most `1/4` everywhere. For every `δ` and point `x`,
the clock density, the physical potential, and every physical coefficient entry are Borel measurable
functions of the actual sample. -/
theorem exists_seedField_physical_evaluation_measurable :
    ∀ (d : ℕ) (i : Fin d), ∃ ε : ℝ, 0 < ε ∧
      (∀ (W : NoiseSample d) (x : Vec d),
        euclideanNorm (gradient (fun y => ε * seedField d W y) x) ≤ (1/4 : ℝ)) ∧
      (∀ (δ : ℝ) (x : Vec d),
        Measurable (fun W : NoiseSample d => densityField i δ (fun y => ε * seedField d W y) x) ∧
        Measurable (fun W : NoiseSample d => potentialField i δ (fun y => ε * seedField d W y) x) ∧
        ∀ (j k : Fin d), Measurable (fun W : NoiseSample d =>
          physicalCoefficientField i δ (fun y => ε * seedField d W y) x j k)) := by
  intro d i
  obtain ⟨ε, hε, hgrad⟩ := exists_seedField_gradient_scale d
  refine ⟨ε, hε, hgrad, fun δ x => ⟨?_, ?_, fun j k => ?_⟩⟩
  · exact physicalEval_measurable_densityField i ε hgrad δ x
  · exact physicalEval_measurable_potentialField i ε hgrad δ x
  · exact physicalEval_measurable_physicalCoefficientField i ε hgrad δ x j k

/-- The spatial gradient of the scaled canonical seed is Borel jointly in the sample and the point.
Each coordinate is `ε` times the joint singleton iterated derivative of `SeedFieldDerivatives`. -/
private theorem physicalEval_measurable_gradient_uncurry {d : ℕ} (ε : ℝ) :
    Measurable (fun p : NoiseSample d × Vec d =>
      gradient (fun y => ε * seedField d p.1 y) p.2) := by
  refine measurable_pi_iff.mpr fun l => ?_
  simp only [physicalEval_gradient_apply_eq]
  exact (measurable_seedField_iteratedCoordinateDerivative_uncurry d [l]).const_mul ε

/-- Joint measurability in `(ω, x)` of the coordinate derivative of a measurable continuous random
field. This is the joint form of `measurable_coordinateDerivative_of_measurable_continuousMap`,
composed from the parent producer `measurable_continuousMap_coordinateDerivative`. -/
private theorem physicalEval_measurable_coordinateDerivative_uncurry {Ω : Type} [MeasurableSpace Ω]
    {d : ℕ} (F : Ω → C(Vec d, ℝ))
    (hF : @Measurable Ω C(Vec d, ℝ) inferInstance (borel C(Vec d, ℝ)) F) (i : Fin d) :
    Measurable (fun p : Ω × Vec d => coordinateDerivative i (F p.1 : Vec d → ℝ) p.2) := by
  letI : MeasurableSpace C(Vec d, ℝ) := borel C(Vec d, ℝ)
  have hFp : Measurable (fun p : Ω × Vec d => F p.1) :=
    Measurable.fun_comp (g := F) (f := fun p : Ω × Vec d => p.1) hF measurable_fst
  have hJ : Measurable (fun p : Ω × Vec d => (F p.1, p.2)) := hFp.prodMk measurable_snd
  exact Measurable.fun_comp
    (g := fun q : C(Vec d, ℝ) × Vec d => coordinateDerivative i (q.1 : Vec d → ℝ) q.2)
    (f := fun p : Ω × Vec d => (F p.1, p.2))
    (measurable_continuousMap_coordinateDerivative d i) hJ

/-- The clock density of the scaled canonical seed is Borel jointly in the sample and the point, for
every `δ`. It is the finite sum of the joint coordinate derivatives of the first column entries. -/
private theorem physicalEval_measurable_densityField_uncurry {d : ℕ} (i : Fin d) (ε : ℝ)
    (hgrad : ∀ (W : NoiseSample d) (x : Vec d),
      euclideanNorm (gradient (fun y => ε * seedField d W y) x) ≤ (1/4 : ℝ))
    (δ : ℝ) :
    Measurable (fun p : NoiseSample d × Vec d =>
      densityField i δ (fun y => ε * seedField d p.1 y) p.2) := by
  have hsum : ∀ m ∈ (Finset.univ : Finset (Fin d)),
      Measurable (fun p : NoiseSample d × Vec d =>
        coordinateDerivative m (fun y => coefficientField i (fun z => ε * seedField d p.1 z) y m i)
          p.2) :=
    fun m _ => physicalEval_measurable_coordinateDerivative_uncurry
      (physicalEval_entryCM i ε hgrad m i) (physicalEval_measurable_entryCM i ε hgrad m i) m
  simp only [physicalEval_densityField_eq_sum]
  exact measurable_const.add (measurable_const.mul (Finset.measurable_sum Finset.univ hsum))

/-- Each coefficient entry of the scaled canonical seed is Borel jointly in the sample and the
point, through the joint gradient. -/
private theorem physicalEval_measurable_coefficientField_uncurry {d : ℕ} (i : Fin d) (ε : ℝ)
    (j k : Fin d) :
    Measurable (fun p : NoiseSample d × Vec d =>
      coefficientField i (fun y => ε * seedField d p.1 y) p.2 j k) :=
  Measurable.fun_comp (g := fun g : Vec d => coefficient i g j k)
    (f := fun p : NoiseSample d × Vec d => gradient (fun y => ε * seedField d p.1 y) p.2)
    (physicalEval_measurable_coefficient i j k) (physicalEval_measurable_gradient_uncurry ε)

/-- The physical potential `-(1/2) log μ` of the scaled canonical seed is Borel jointly in the
sample and the point. The logarithm is measurable everywhere, so no positivity of `μ` is used. -/
private theorem physicalEval_measurable_potentialField_uncurry {d : ℕ} (i : Fin d) (ε : ℝ)
    (hgrad : ∀ (W : NoiseSample d) (x : Vec d),
      euclideanNorm (gradient (fun y => ε * seedField d W y) x) ≤ (1/4 : ℝ))
    (δ : ℝ) :
    Measurable (fun p : NoiseSample d × Vec d =>
      potentialField i δ (fun y => ε * seedField d p.1 y) p.2) := by
  simp only [potentialField]
  exact measurable_const.mul (physicalEval_measurable_densityField_uncurry i ε hgrad δ).log

/-- Each physical coefficient entry of the scaled canonical seed is Borel jointly in the sample and
the point, for every `δ`. No positivity or bound on the density is used. -/
private theorem physicalEval_measurable_physicalCoefficientField_uncurry {d : ℕ}
    (i : Fin d) (ε : ℝ)
    (hgrad : ∀ (W : NoiseSample d) (x : Vec d),
      euclideanNorm (gradient (fun y => ε * seedField d W y) x) ≤ (1/4 : ℝ))
    (δ : ℝ) (j k : Fin d) :
    Measurable (fun p : NoiseSample d × Vec d =>
      physicalCoefficientField i δ (fun y => ε * seedField d p.1 y) p.2 j k) := by
  simp only [physicalEval_physicalCoefficientField_apply]
  exact (physicalEval_measurable_densityField_uncurry i ε hgrad δ).inv.mul
    (physicalEval_measurable_coefficientField_uncurry i ε j k)

/-- Source: `paper/main.tex`, Proposition 7.1, Step 1, lines 1212–1218, and the physical fields of
lines 1218–1231. For an arbitrary fixed scale `ε` whose Euclidean gradient bound `1/4` holds for
every sample and point, the clock density, the physical potential, and every physical coefficient
entry are Borel functions of the actual sample, for every `δ` and point `x`. The scale is supplied,
not chosen here, so that every consumer uses the same `ε`. -/
theorem seedField_physical_evaluation_measurable_of_gradient_bound :
    ∀ {d : ℕ} (i : Fin d) (ε : ℝ),
      (∀ (W : NoiseSample d) (x : Vec d),
        euclideanNorm (gradient (fun y => ε * seedField d W y) x) ≤ (1/4 : ℝ)) →
      ∀ (δ : ℝ) (x : Vec d),
        Measurable (fun W : NoiseSample d => densityField i δ (fun y => ε * seedField d W y) x) ∧
        Measurable (fun W : NoiseSample d => potentialField i δ (fun y => ε * seedField d W y) x) ∧
        ∀ j k : Fin d, Measurable (fun W : NoiseSample d =>
          physicalCoefficientField i δ (fun y => ε * seedField d W y) x j k) := by
  intro d i ε hgrad δ x
  exact ⟨physicalEval_measurable_densityField i ε hgrad δ x,
    physicalEval_measurable_potentialField i ε hgrad δ x,
    fun j k => physicalEval_measurable_physicalCoefficientField i ε hgrad δ x j k⟩

/-- Source: `paper/main.tex`, Proposition 7.1, Step 1, lines 1212–1218, and the physical fields of
lines 1218–1231. Joint form for the same arbitrary fixed scale `ε` and gradient bound: for every
`δ`, the clock density, the physical potential, and every physical coefficient entry are Borel
functions of the pair `(sample, point)`. -/
theorem seedField_physical_uncurry_measurable_of_gradient_bound :
    ∀ {d : ℕ} (i : Fin d) (ε : ℝ),
      (∀ (W : NoiseSample d) (x : Vec d),
        euclideanNorm (gradient (fun y => ε * seedField d W y) x) ≤ (1/4 : ℝ)) →
      ∀ δ : ℝ,
        Measurable (fun p : NoiseSample d × Vec d =>
          densityField i δ (fun y => ε * seedField d p.1 y) p.2) ∧
        Measurable (fun p : NoiseSample d × Vec d =>
          potentialField i δ (fun y => ε * seedField d p.1 y) p.2) ∧
        ∀ j k : Fin d, Measurable (fun p : NoiseSample d × Vec d =>
          physicalCoefficientField i δ (fun y => ε * seedField d p.1 y) p.2 j k) := by
  intro d i ε hgrad δ
  exact ⟨physicalEval_measurable_densityField_uncurry i ε hgrad δ,
    physicalEval_measurable_potentialField_uncurry i ε hgrad δ,
    fun j k => physicalEval_measurable_physicalCoefficientField_uncurry i ε hgrad δ j k⟩

end EinsteinRelation.Sharpness
