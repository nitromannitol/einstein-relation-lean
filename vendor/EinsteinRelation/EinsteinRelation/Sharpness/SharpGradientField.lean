import EinsteinRelation.Correctors.OrbitPotentialDomain
import EinsteinRelation.Environment.Bounds
import EinsteinRelation.Sharpness.GradientFieldCorrector
import EinsteinRelation.Sharpness.SeedGradientEnergy
import EinsteinRelation.Sharpness.SharpEnvironmentLaw
import EinsteinRelation.Sharpness.SharpPhysicalLaw

/-! # The sharp gradient field on the physical sharpness law

Source `paper/main.tex`, Proposition 7.1, Step 2 (lines 1235–1238), for the physical pair of
`SharpPhysicalLaw`. For a coefficient pair `ω` and a direction `i`, the orbit gradient is
`G_i(ω) = a(ω, 0)⁻¹ e_i - e_i`, where `a` is the reduced coefficient.

* `gradientField_exists_reduced_mem_of_orbit` and `gradient_field_corrector_identification_of_orbit`
  are the unconditional forms of Steps 1 and 2 of `GradientFieldCorrector`. The orbit-potential
  domain is supplied by `orbitPotentialGradientDomain_holds`.
* For a physical pair `ω = sharpPhysicalPair W`, inverting the constant harmonic flux shows that the
  orbit gradient at every point is the gradient of the scaled seed `ε · seedField W`. Hence the
  orbit gradient is measurable, bounded by `1/4` almost surely, satisfies the harmonic identity
  almost surely for every regular law, and is not almost surely zero.
* `integral_sharpGradientField_energy_pos`: the mean sharp energy of the gradient field is positive.

The orbit-potential property of the law is not yet discharged. It needs almost every environment of
the physical law to be a physical pair; this is the hypothesis `hR` of
`ae_clippedSharpGradient_orbit_of_mem_range`, which is not proved here. -/

open EinsteinRelation.Correctors
open MeasureTheory Filter

namespace EinsteinRelation.Sharpness

noncomputable section

/-! ### Steps 1 and 2 with the orbit-potential domain supplied -/

/-- Step 1 of `GradientFieldCorrector` with the orbit-potential domain supplied by
`orbitPotentialGradientDomain_holds`. -/
theorem gradientField_exists_reduced_mem_of_orbit {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (G : FieldPair d → Vec d) (M : ℝ)
    (hGm : Measurable G) (hGb : ∀ ω, euclideanNorm (G ω) ≤ 1 / 4)
    (hG : ∀ᵐ ω ∂Q.measure, ∃ φ : Vec d → ℝ, ContDiff ℝ 1 φ ∧ (∀ x, |φ x| ≤ M) ∧
      ∀ x, gradient φ x = G (translate x ω)) :
    ∃ E : Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q),
      E ∈ correctorPotentialDomain Q ∧
        ∀ᵐ ω ∂Q.measure, (⇑E) (reduce ω) = (WithLp.toLp 2 (G ω) : EuclideanSpace ℝ (Fin d)) :=
  gradientField_exists_reduced_mem Q (orbitPotentialGradientDomain_holds Q) G M hGm hGb hG

/-- Step 2 of `GradientFieldCorrector` with the orbit-potential domain supplied by
`orbitPotentialGradientDomain_holds`. -/
theorem gradient_field_corrector_identification_of_orbit {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i₁ : Fin d) (G : FieldPair d → Vec d) (M : ℝ)
    (hGm : Measurable G) (hGb : ∀ ω, euclideanNorm (G ω) ≤ 1 / 4)
    (hG : ∀ᵐ ω ∂Q.measure, ∃ φ : Vec d → ℝ, ContDiff ℝ 1 φ ∧ (∀ x, |φ x| ≤ M) ∧
      ∀ x, gradient φ x = G (translate x ω))
    (hharm : ∀ᵐ ω ∂Q.measure,
      (reducedCoefficient ω 0).mulVec (unitVector i₁ + G ω) = unitVector i₁) :
    (∀ᵐ ω ∂Q.measure, (WithLp.toLp 2 (G ω) : EuclideanSpace ℝ (Fin d)) =
        (canonicalCorrectorGradient Q i₁ :
          Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q)) (reduce ω)) ∧
      expectedCorrectorFlux Q i₁ = correctorUnitVector i₁ :=
  gradient_field_corrector_identification Q (orbitPotentialGradientDomain_holds Q) i₁ G M hGm hGb
    hG hharm

/-! ### The orbit gradient on coefficient pairs -/

/-- The orbit gradient in direction `i`, read from the reduced coefficient at the origin:
`G_i(ω) = a(ω, 0)⁻¹ e_i - e_i`. -/
def sharpGradientField {d : ℕ} (i : Fin d) (ω : FieldPair d) : Vec d :=
  Matrix.mulVec (reducedCoefficient ω 0)⁻¹ (unitVector i) - unitVector i

/-- The reduced coefficient at the origin of a translate is the reduced coefficient at the shift. -/
theorem reducedCoefficient_translate_zero {d : ℕ} (x : Vec d) (ω : FieldPair d) :
    reducedCoefficient (translate x ω) 0 = reducedCoefficient ω x := by
  simp [reducedCoefficient, clockDensity]

/-- The orbit gradient at a shift is the orbit gradient of the reduced coefficient at that shift. -/
theorem sharpGradientField_translate {d : ℕ} (i : Fin d) (x : Vec d) (ω : FieldPair d) :
    sharpGradientField i (translate x ω) =
      Matrix.mulVec (reducedCoefficient ω x)⁻¹ (unitVector i) - unitVector i := by
  unfold sharpGradientField
  rw [reducedCoefficient_translate_zero]

/-- A matrix whose quadratic form dominates `c |ξ|²` with `c > 0` has unit determinant. -/
private theorem isUnit_det_of_lower_bound {d : ℕ} {c : ℝ} (hc : 0 < c) {a : Mat d}
    (h : ∀ ξ : Vec d, c * euclideanSq ξ ≤ dot ξ (Matrix.mulVec a ξ)) : IsUnit a.det := by
  rw [isUnit_iff_ne_zero]
  intro hdet
  obtain ⟨v, hv, hav⟩ := (Matrix.exists_mulVec_eq_zero_iff (M := a)).mpr hdet
  have hlow := h v
  rw [hav, show dot v (0 : Vec d) = 0 by simp [dot]] at hlow
  have hsq : euclideanSq v ≤ 0 := by nlinarith
  have hv0 : v = 0 := by
    by_contra hne
    have hpos := (euclideanSq_pos_iff v).mpr hne
    linarith
  exact hv hv0

/-- The reduced coefficient of a regular pair is invertible at every point. -/
theorem isUnit_det_reducedCoefficient {d : ℕ} {L : ℝ} (hL : 1 ≤ L) {ω : FieldPair d}
    (hω : IsRegular L ω) (x : Vec d) : IsUnit (reducedCoefficient ω x).det := by
  have hL0 : 0 < L := lt_of_lt_of_le zero_lt_one hL
  exact isUnit_det_of_lower_bound (mul_pos (Real.exp_pos _) (inv_pos.mpr hL0))
    (fun ξ => (reducedCoefficient_energy_bounds ω x ξ L hL hω).1)

/-- Inverting the harmonic identity `a (e_i + g) = e_i` with invertible `a` gives
`g = a⁻¹ e_i - e_i`. -/
private theorem sharpGradient_eq_of_harmonic {d : ℕ} (i : Fin d) {a : Mat d} (ha : IsUnit a.det)
    {g : Vec d} (h : Matrix.mulVec a (unitVector i + g) = unitVector i) :
    Matrix.mulVec a⁻¹ (unitVector i) - unitVector i = g := by
  have h1 : Matrix.mulVec a⁻¹ (unitVector i) = unitVector i + g := by
    calc Matrix.mulVec a⁻¹ (unitVector i)
        = Matrix.mulVec a⁻¹ (Matrix.mulVec a (unitVector i + g)) := by rw [h]
      _ = Matrix.mulVec (a⁻¹ * a) (unitVector i + g) := by rw [Matrix.mulVec_mulVec]
      _ = unitVector i + g := by rw [Matrix.nonsing_inv_mul a ha, Matrix.one_mulVec]
  rw [h1]
  abel

/-- For a regular pair, the orbit gradient at every point solves the harmonic identity. -/
theorem sharpGradientField_harmonic_of_regular {d : ℕ} (i : Fin d) {L : ℝ} (hL : 1 ≤ L)
    {ω : FieldPair d} (hω : IsRegular L ω) (x : Vec d) :
    Matrix.mulVec (reducedCoefficient ω x) (unitVector i + sharpGradientField i (translate x ω)) =
      unitVector i := by
  rw [sharpGradientField_translate]
  have h1 : unitVector i +
      (Matrix.mulVec (reducedCoefficient ω x)⁻¹ (unitVector i) - unitVector i) =
        Matrix.mulVec (reducedCoefficient ω x)⁻¹ (unitVector i) := by
    abel
  rw [h1, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_det_reducedCoefficient hL hω x),
    Matrix.one_mulVec]

/-- Applying a matrix to a coordinate unit vector reads off a column. -/
theorem mulVec_unitVector_apply {d : ℕ} (M : Mat d) (i k : Fin d) :
    Matrix.mulVec M (unitVector i) k = M k i := by
  simp [Matrix.mulVec, dotProduct, unitVector, Pi.single_apply]

/-- The coordinates of the orbit gradient. -/
theorem sharpGradientField_apply {d : ℕ} (i k : Fin d) (ω : FieldPair d) :
    sharpGradientField i ω k = (reducedCoefficient ω 0)⁻¹ k i - unitVector i k := by
  unfold sharpGradientField
  rw [Pi.sub_apply, mulVec_unitVector_apply]

/-- Entries of a matrix inverse through the adjugate. -/
private theorem inv_apply_eq_det_inv_mul_adjugate {d : ℕ} (A : Mat d) (k i : Fin d) :
    A⁻¹ k i = A.det⁻¹ * A.adjugate k i := by
  rw [Matrix.inv_def, Ring.inverse_eq_inv] <;> rfl

/-- The reduced coefficient at the origin is continuous on coefficient pairs. -/
theorem continuous_reducedCoefficient_zero {d : ℕ} :
    Continuous (fun ω : FieldPair d => reducedCoefficient ω 0) := by
  have h1 : Continuous (fun ω : FieldPair d => ω.1 (0 : Vec d)) :=
    (continuous_eval_const (0 : Vec d)).comp continuous_fst
  have h2 : Continuous (fun ω : FieldPair d => ω.2 (0 : Vec d)) :=
    (continuous_eval_const (0 : Vec d)).comp continuous_snd
  have h3 : Continuous (fun ω : FieldPair d => clockDensity ω 0) := by
    unfold clockDensity
    exact Real.continuous_exp.comp (continuous_const.mul h2)
  exact h3.smul h1

/-- The orbit gradient is measurable on coefficient pairs. -/
theorem measurable_sharpGradientField {d : ℕ} (i : Fin d) :
    Measurable (sharpGradientField i) := by
  refine measurable_pi_iff.mpr fun k => ?_
  have hdet : Measurable (fun ω : FieldPair d => (reducedCoefficient ω 0).det) :=
    (continuous_reducedCoefficient_zero (d := d)).matrix_det.measurable
  have hadj : Measurable (fun ω : FieldPair d => (reducedCoefficient ω 0).adjugate k i) :=
    ((continuous_reducedCoefficient_zero (d := d)).matrix_adjugate.matrix_elem k i).measurable
  have hentry : Measurable (fun ω : FieldPair d => (reducedCoefficient ω 0)⁻¹ k i) := by
    simp only [inv_apply_eq_det_inv_mul_adjugate]
    exact hdet.inv.mul hadj
  simp only [sharpGradientField_apply]
  exact hentry.sub_const (unitVector i k)

/-- The Euclidean norm of the orbit gradient is measurable. -/
theorem measurable_sharpGradientField_norm {d : ℕ} (i : Fin d) :
    Measurable (fun ω : FieldPair d => euclideanNorm (sharpGradientField i ω)) := by
  have hcoord : ∀ j : Fin d, Measurable (fun ω : FieldPair d => sharpGradientField i ω j) :=
    fun j => (measurable_pi_apply j).comp (measurable_sharpGradientField i)
  have hsum : Measurable (fun ω : FieldPair d =>
      ∑ j, sharpGradientField i ω j * sharpGradientField i ω j) :=
    Finset.measurable_sum Finset.univ fun j _ => (hcoord j).mul (hcoord j)
  exact hsum.sqrt

/-! ### The orbit gradient of a physical pair -/

/-- The coordinate derivative of a scalar multiple of a differentiable function. -/
private theorem coordinateDerivative_scaled_seed {d : ℕ} (ε : ℝ) (W : NoiseSample d) (x : Vec d)
    (i : Fin d) :
    coordinateDerivative i (fun y => ε * seedField d W y) x =
      ε * coordinateDerivative i (seedField d W) x := by
  unfold coordinateDerivative
  rw [fderiv_const_mul ((contDiff_seedField d W).differentiable (by simp) x) ε,
    ContinuousLinearMap.smul_apply, smul_eq_mul]

/-- At every point, the orbit gradient of a physical pair is the gradient of the scaled seed. -/
theorem sharpGradientField_translate_pair_eq {d : ℕ} (i : Fin d) (δ ε : ℝ)
    (hgrad : ∀ (W : NoiseSample d) (x : Vec d),
      euclideanNorm (gradient (fun y => ε * seedField d W y) x) ≤ (1 / 4 : ℝ))
    (hμ : ∀ (W : NoiseSample d) (x : Vec d),
      (3 / 4 : ℝ) ≤ densityField i δ (fun y => ε * seedField d W y) x ∧
      densityField i δ (fun y => ε * seedField d W y) x ≤ (5 / 4 : ℝ))
    (W : NoiseSample d) (x : Vec d) :
    sharpGradientField i (translate x (sharpPhysicalPair i δ ε hgrad hμ W)) =
      gradient (fun y => ε * seedField d W y) x := by
  obtain ⟨Λ, hΛ, hreg⟩ := sharpPhysicalPair_regular i δ ε hgrad hμ
  rw [sharpGradientField_translate]
  exact sharpGradient_eq_of_harmonic i
    (isUnit_det_reducedCoefficient (by linarith) (hreg W) x)
    (sharpPhysicalPair_harmonic i δ ε hgrad hμ W x)

/-- The orbit gradient of a physical pair is bounded by `1/4` at the origin. -/
theorem sharpGradientField_pair_norm_le {d : ℕ} (i : Fin d) (δ ε : ℝ)
    (hgrad : ∀ (W : NoiseSample d) (x : Vec d),
      euclideanNorm (gradient (fun y => ε * seedField d W y) x) ≤ (1 / 4 : ℝ))
    (hμ : ∀ (W : NoiseSample d) (x : Vec d),
      (3 / 4 : ℝ) ≤ densityField i δ (fun y => ε * seedField d W y) x ∧
      densityField i δ (fun y => ε * seedField d W y) x ≤ (5 / 4 : ℝ))
    (W : NoiseSample d) :
    euclideanNorm (sharpGradientField i (sharpPhysicalPair i δ ε hgrad hμ W)) ≤ 1 / 4 := by
  have h := sharpGradientField_translate_pair_eq i δ ε hgrad hμ W 0
  rw [translate_zero] at h
  rw [h]
  exact hgrad W 0

/-- Almost every value of the physical law has orbit gradient of norm at most `1/4`. -/
theorem ae_sharpGradientField_norm_le {d : ℕ} (i : Fin d) (δ ε : ℝ)
    (hgrad : ∀ (W : NoiseSample d) (x : Vec d),
      euclideanNorm (gradient (fun y => ε * seedField d W y) x) ≤ (1 / 4 : ℝ))
    (hμ : ∀ (W : NoiseSample d) (x : Vec d),
      (3 / 4 : ℝ) ≤ densityField i δ (fun y => ε * seedField d W y) x ∧
      densityField i δ (fun y => ε * seedField d W y) x ≤ (5 / 4 : ℝ))
    (P : Measure (NoiseSample d)) :
    ∀ᵐ ω ∂(P.map (sharpPhysicalPair i δ ε hgrad hμ)),
      euclideanNorm (sharpGradientField i ω) ≤ 1 / 4 := by
  have hF := measurable_sharpPhysicalPair i δ ε hgrad hμ
  have hset : MeasurableSet {ω : FieldPair d | euclideanNorm (sharpGradientField i ω) ≤ 1 / 4} :=
    measurableSet_le (measurable_sharpGradientField_norm i) measurable_const
  exact (ae_map_iff hF.aemeasurable hset).mpr
    (ae_of_all P fun W => sharpGradientField_pair_norm_le i δ ε hgrad hμ W)

/-- For every regular law, the harmonic identity holds at every point for almost every
environment. -/
theorem ae_sharpGradientField_harmonic {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (i : Fin d) :
    ∀ᵐ ω ∂Q.measure, ∀ x : Vec d,
      Matrix.mulVec (reducedCoefficient ω x) (unitVector i + sharpGradientField i (translate x ω)) =
        unitVector i := by
  filter_upwards [Q.regular] with ω hω
  exact fun x => sharpGradientField_harmonic_of_regular i Q.ellipticity_parameter hω x

/-- The harmonic identity at the origin, almost surely, for every regular law. -/
theorem ae_sharpGradientField_harmonic_zero {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (i : Fin d) :
    ∀ᵐ ω ∂Q.measure,
      Matrix.mulVec (reducedCoefficient ω 0) (unitVector i + sharpGradientField i ω) =
        unitVector i := by
  filter_upwards [ae_sharpGradientField_harmonic Q i] with ω hω
  simpa only [translate_zero] using hω 0

/-! ### Non-degeneracy -/

/-- The orbit gradient of the physical pair is not almost surely zero under a white-noise law:
otherwise the coordinate derivative of the seed at the origin would vanish almost surely, which
contradicts `integral_seedField_coordinateDerivative_sq_pos`. -/
theorem not_ae_sharpGradientField_zero {d : ℕ} (i : Fin d) (δ ε : ℝ)
    (hgrad : ∀ (W : NoiseSample d) (x : Vec d),
      euclideanNorm (gradient (fun y => ε * seedField d W y) x) ≤ (1 / 4 : ℝ))
    (hμ : ∀ (W : NoiseSample d) (x : Vec d),
      (3 / 4 : ℝ) ≤ densityField i δ (fun y => ε * seedField d W y) x ∧
      densityField i δ (fun y => ε * seedField d W y) x ≤ (5 / 4 : ℝ))
    {P : Measure (NoiseSample d)} (hP : External.IsWhiteNoiseLaw P) (hε : 0 < ε) :
    ¬ (sharpGradientField i =ᵐ[P.map (sharpPhysicalPair i δ ε hgrad hμ)]
      (0 : FieldPair d → Vec d)) := by
  intro h
  have hF := measurable_sharpPhysicalPair i δ ε hgrad hμ
  have h' : ∀ᵐ ω ∂(P.map (sharpPhysicalPair i δ ε hgrad hμ)), sharpGradientField i ω = 0 := by
    filter_upwards [h] with ω hω
    exact hω
  have hset : MeasurableSet {ω : FieldPair d | sharpGradientField i ω = 0} :=
    measurable_sharpGradientField i (measurableSet_singleton 0)
  have hW : ∀ᵐ W ∂P, sharpGradientField i (sharpPhysicalPair i δ ε hgrad hμ W) = 0 :=
    (ae_map_iff hF.aemeasurable hset).mp h'
  have hsq : ∀ᵐ W ∂P, (coordinateDerivative i (seedField d W) 0) ^ 2 = 0 := by
    filter_upwards [hW] with W hWz
    have hg : gradient (fun y => ε * seedField d W y) 0 = 0 := by
      rw [← sharpGradientField_translate_pair_eq i δ ε hgrad hμ W 0, translate_zero]
      exact hWz
    have h1 : ε * coordinateDerivative i (seedField d W) 0 = 0 := by
      rw [← coordinateDerivative_scaled_seed ε W 0 i]
      exact congrFun hg i
    have h2 : coordinateDerivative i (seedField d W) 0 = 0 :=
      (mul_eq_zero.mp h1).resolve_left hε.ne'
    simp [h2]
  have hzero : ∫ W, (coordinateDerivative i (seedField d W) 0) ^ 2 ∂P = 0 := by
    rw [integral_congr_ae hsq]
    simp
  linarith [integral_seedField_coordinateDerivative_sq_pos hP i]

/-! ### The clipped orbit gradient and the mean sharp energy -/

/-- The orbit gradient truncated to the closed ball of radius `1/4`. It equals
`sharpGradientField` wherever that field is admissible, and it is bounded everywhere. -/
def clippedSharpGradient {d : ℕ} (i : Fin d) (ω : FieldPair d) : Vec d :=
  if euclideanNorm (sharpGradientField i ω) ≤ 1 / 4 then sharpGradientField i ω else 0

theorem clippedSharpGradient_norm_le {d : ℕ} (i : Fin d) (ω : FieldPair d) :
    euclideanNorm (clippedSharpGradient i ω) ≤ 1 / 4 := by
  unfold clippedSharpGradient
  split_ifs with h
  · exact h
  · norm_num [euclideanNorm, euclideanSq, dot]

theorem measurable_clippedSharpGradient {d : ℕ} (i : Fin d) :
    Measurable (clippedSharpGradient i) := by
  unfold clippedSharpGradient
  exact Measurable.ite (measurableSet_le (measurable_sharpGradientField_norm i) measurable_const)
    (measurable_sharpGradientField i) measurable_const

theorem clippedSharpGradient_ae_eq {d : ℕ} (i : Fin d) (δ ε : ℝ)
    (hgrad : ∀ (W : NoiseSample d) (x : Vec d),
      euclideanNorm (gradient (fun y => ε * seedField d W y) x) ≤ (1 / 4 : ℝ))
    (hμ : ∀ (W : NoiseSample d) (x : Vec d),
      (3 / 4 : ℝ) ≤ densityField i δ (fun y => ε * seedField d W y) x ∧
      densityField i δ (fun y => ε * seedField d W y) x ≤ (5 / 4 : ℝ))
    (P : Measure (NoiseSample d)) :
    clippedSharpGradient i =ᵐ[P.map (sharpPhysicalPair i δ ε hgrad hμ)] sharpGradientField i := by
  filter_upwards [ae_sharpGradientField_norm_le i δ ε hgrad hμ P] with ω hω
  unfold clippedSharpGradient
  rw [if_pos hω]

/-- The mean sharp energy of the orbit gradient of the physical law is strictly positive. -/
theorem integral_sharpGradientField_energy_pos {d : ℕ} (i : Fin d) (δ ε : ℝ)
    (hgrad : ∀ (W : NoiseSample d) (x : Vec d),
      euclideanNorm (gradient (fun y => ε * seedField d W y) x) ≤ (1 / 4 : ℝ))
    (hμ : ∀ (W : NoiseSample d) (x : Vec d),
      (3 / 4 : ℝ) ≤ densityField i δ (fun y => ε * seedField d W y) x ∧
      densityField i δ (fun y => ε * seedField d W y) x ≤ (5 / 4 : ℝ))
    {P : Measure (NoiseSample d)} (hP : External.IsWhiteNoiseLaw P) (hε : 0 < ε) :
    0 < ∫ ω, sharpEnergy i (sharpGradientField i ω)
      ∂(P.map (sharpPhysicalPair i δ ε hgrad hμ)) := by
  letI : IsProbabilityMeasure P := hP.1
  haveI : IsProbabilityMeasure (P.map (sharpPhysicalPair i δ ε hgrad hμ)) :=
    inferInstance
  have hae := clippedSharpGradient_ae_eq i δ ε hgrad hμ P
  have hne : ¬ (clippedSharpGradient i =ᵐ[P.map (sharpPhysicalPair i δ ε hgrad hμ)]
      (0 : FieldPair d → Vec d)) := by
    intro h
    exact not_ae_sharpGradientField_zero i δ ε hgrad hμ hP hε (hae.symm.trans h)
  have hpos := integral_gradientSharpEnergy_pos (P.map (sharpPhysicalPair i δ ε hgrad hμ)) i
    (measurable_clippedSharpGradient i) (clippedSharpGradient_norm_le i) hne
  have heq : ∫ ω, sharpEnergy i (clippedSharpGradient i ω)
      ∂(P.map (sharpPhysicalPair i δ ε hgrad hμ)) =
        ∫ ω, sharpEnergy i (sharpGradientField i ω)
          ∂(P.map (sharpPhysicalPair i δ ε hgrad hμ)) := by
    refine integral_congr_ae ?_
    filter_upwards [hae] with ω hω
    simp only [hω]
  rw [← heq]
  exact hpos

/-! ### The orbit-potential property of the physical law -/

/-- The orbit-potential property of the clipped orbit gradient, almost surely, once almost every
environment of the physical law is a physical pair. This is the measure-theoretic input that is
not proved in this file: the range of the physical pair must carry the law. -/
theorem ae_clippedSharpGradient_orbit_of_mem_range {d : ℕ} (i : Fin d) (δ ε : ℝ)
    (hgrad : ∀ (W : NoiseSample d) (x : Vec d),
      euclideanNorm (gradient (fun y => ε * seedField d W y) x) ≤ (1 / 4 : ℝ))
    (hμ : ∀ (W : NoiseSample d) (x : Vec d),
      (3 / 4 : ℝ) ≤ densityField i δ (fun y => ε * seedField d W y) x ∧
      densityField i δ (fun y => ε * seedField d W y) x ≤ (5 / 4 : ℝ))
    {P : Measure (NoiseSample d)} (hε : 0 < ε)
    (hR : ∀ᵐ ω ∂(P.map (sharpPhysicalPair i δ ε hgrad hμ)),
      ω ∈ Set.range (sharpPhysicalPair i δ ε hgrad hμ)) :
    ∀ᵐ ω ∂(P.map (sharpPhysicalPair i δ ε hgrad hμ)), ∃ φ : Vec d → ℝ,
      ContDiff ℝ 1 φ ∧ (∀ x, |φ x| ≤ ε) ∧
        ∀ x, gradient φ x = clippedSharpGradient i (translate x ω) := by
  filter_upwards [hR] with ω hω
  obtain ⟨W, rfl⟩ := hω
  refine ⟨fun y => ε * seedField d W y, (sharpSeed_contDiff ε W).of_le (mod_cast le_top),
    fun x => sharpSeed_abs_le hε W x, fun x => ?_⟩
  unfold clippedSharpGradient
  rw [sharpGradientField_translate_pair_eq i δ ε hgrad hμ W x, if_pos (hgrad W x)]

end

end EinsteinRelation.Sharpness
