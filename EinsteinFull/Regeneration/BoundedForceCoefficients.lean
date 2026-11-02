import EinsteinFull.External.Source.GMPDirichletKernel
import EinsteinRelation.Environment.SourceReducedBoundSupport
import EinsteinRelation.Regeneration.HalfSpaces

namespace EinsteinFull.Regeneration
open EinsteinRelation

/-- A globally bounded extension of the rescaled force density, equal to
`exp (2 * x i)` on the Euclidean ball of radius `B`. This is an explicit
coefficient construction, not a kernel or regeneration assumption. -/
noncomputable def boundedForceDensity {d : ℕ} (B : ℝ) (i : Fin d)
    (x : Vec d) : ℝ :=
  Real.exp (2 * max (-B) (min B (x i)))

/-- The corresponding extension of the actual reduced coefficient after
the spatial change of variables `x = lambda * y`. The factor `1/2` is the
one in the frozen reduced generator and GMP equation (5.4). -/
noncomputable def boundedForceCoefficient {d : ℕ} (ω : FieldPair d)
    (B : ℝ) (i : Fin d) (lam : ℝ) (x : Vec d) : Mat d :=
  (boundedForceDensity B i x / 2) • reducedCoefficient ω (lam⁻¹ • x)

/-- The clipping construction is continuous, hence measurable. -/
theorem continuous_boundedForceDensity {d : ℕ} (B : ℝ) (i : Fin d) :
    Continuous (boundedForceDensity B i) := by
  unfold boundedForceDensity
  exact Real.continuous_exp.comp
    (continuous_const.mul (continuous_const.max
      (continuous_const.min (continuous_apply i))))

/-- The matrix extension preserves continuity of the actual reduced field. -/
theorem continuous_boundedForceCoefficient {d : ℕ} (ω : FieldPair d)
    (B : ℝ) (i : Fin d) (lam : ℝ) :
    Continuous (boundedForceCoefficient ω B i lam) := by
  have ha : Continuous (fun x : Vec d => reducedCoefficient ω (lam⁻¹ • x)) :=
    (reduce ω).1.continuous.comp (continuous_id.const_smul lam⁻¹)
  exact ((continuous_boundedForceDensity B i).div_const 2).smul ha

/-- Bounds on the density are uniform in space and the environment. -/
theorem boundedForceDensity_bounds {d : ℕ} {B : ℝ} (hB : 0 ≤ B)
    (i : Fin d) (x : Vec d) :
    (Real.exp (2 * B))⁻¹ ≤ boundedForceDensity B i x ∧
      boundedForceDensity B i x ≤ Real.exp (2 * B) := by
  constructor
  · rw [← Real.exp_neg]
    apply Real.exp_le_exp.mpr
    have h := le_max_left (-B) (min B (x i))
    linarith
  · apply Real.exp_le_exp.mpr
    have h : max (-B) (min B (x i)) ≤ B :=
      max_le (by linarith) (min_le_left _ _)
    linarith

/-- On the containing Euclidean ball, the bounded extension is the actual
force weight. No coordinate sup norm is substituted for the ball. -/
theorem boundedForceDensity_eq {d : ℕ} {B : ℝ} (i : Fin d) (x : Vec d)
    (hx : euclideanNorm x ≤ B) :
    boundedForceDensity B i x = Real.exp (2 * x i) := by
  have hc := abs_le.mp ((EinsteinRelation.Regeneration.coordinate_abs_le_euclideanNorm x i).trans hx)
  simp only [boundedForceDensity, min_eq_right hc.2, max_eq_right hc.1]

/-- The matrix extension also agrees with the literal rescaled coefficient
on the whole closed containing ball. -/
theorem boundedForceCoefficient_eq {d : ℕ} (ω : FieldPair d) {B : ℝ}
    (i : Fin d) (lam : ℝ) (x : Vec d) (hx : euclideanNorm x ≤ B) :
    boundedForceCoefficient ω B i lam x =
      (Real.exp (2 * x i) / 2) • reducedCoefficient ω (lam⁻¹ • x) := by
  rw [boundedForceCoefficient, boundedForceDensity_eq i x hx]

/-- The source ellipticity parameter for the explicit bounded extension.
It depends on the original field bound and containing radius alone. -/
noncomputable def boundedForceKappa (L B : ℝ) : ℝ :=
  (2 * sourceReducedBound L * Real.exp (2 * B))⁻¹

/-- Positivity of the parameter precedes the environment and force. -/
theorem boundedForceKappa_pos {L B : ℝ} (hL : 1 ≤ L) :
    0 < boundedForceKappa L B := by
  unfold boundedForceKappa sourceReducedBound
  apply inv_pos.mpr
  have hp : 0 < 3 * L ^ 2 + L + 1 := by nlinarith [sq_nonneg L]
  positivity

/-- The extension satisfies the literal global coefficient hypotheses of
GMP (5.4). The ellipticity parameter is fixed before the environment,
coordinate direction and signed force; the matrix remains anisotropic. -/
theorem boundedForceCoefficient_elliptic {d : ℕ} {L B : ℝ}
    (hL : 1 ≤ L) (hB : 0 ≤ B) (ω : FieldPair d) (hω : IsRegular L ω)
    (i : Fin d) (lam : ℝ) :
    External.Source.GMP.IsUniformlyElliptic (boundedForceKappa L B)
      (boundedForceDensity B i) (boundedForceCoefficient ω B i lam) := by
  let Λ := sourceReducedBound L
  let E := Real.exp (2 * B)
  obtain ⟨hΛ, ha, _⟩ := sourceReducedBound_support hL hω
  have hΛpos : 0 < Λ := lt_of_lt_of_le zero_lt_one hΛ
  have hEpos : 0 < E := Real.exp_pos _
  have hEk : E ≤ 2 * Λ * E := by nlinarith
  have hkE : (2 * Λ * E)⁻¹ ≤ E⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le hEpos hEk
  refine ⟨(continuous_boundedForceDensity B i).measurable, ?_, ?_⟩
  · exact (continuous_boundedForceCoefficient ω B i lam).measurable
  · intro x
    obtain ⟨hρlo, hρhi⟩ := boundedForceDensity_bounds hB i x
    have hρpos : 0 < boundedForceDensity B i x := Real.exp_pos _
    have hsym := (ha (lam⁻¹ • x)).1
    refine ⟨hkE.trans hρlo, ?_, ?_, ?_⟩
    · change boundedForceDensity B i x ≤ ((2 * Λ * E)⁻¹)⁻¹
      rw [inv_inv]
      exact hρhi.trans hEk
    · change ((boundedForceDensity B i x / 2) •
          reducedCoefficient ω (lam⁻¹ • x)).transpose = _
      rw [Matrix.transpose_smul, hsym]
      rfl
    · intro v
      obtain ⟨hlo, hhi⟩ := (ha (lam⁻¹ • x)).2 v
      have hsq : 0 ≤ euclideanSq v := by
        change 0 ≤ ∑ j, v j * v j
        exact Finset.sum_nonneg (fun _ _ => mul_self_nonneg _)
      have hscalar : (2 * Λ * E)⁻¹ ≤ boundedForceDensity B i x / 2 * Λ⁻¹ := by
        calc
          (2 * Λ * E)⁻¹ = E⁻¹ / 2 * Λ⁻¹ := by
            field_simp
          _ ≤ boundedForceDensity B i x / 2 * Λ⁻¹ :=
            mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hρlo (by norm_num))
              (inv_nonneg.mpr hΛpos.le)
      change (boundedForceKappa L B * euclideanSq v ≤
          dotProduct v (((boundedForceDensity B i x / 2) •
            reducedCoefficient ω (lam⁻¹ • x)).mulVec v)) ∧
        (dotProduct v (((boundedForceDensity B i x / 2) •
            reducedCoefficient ω (lam⁻¹ • x)).mulVec v) ≤
          (boundedForceKappa L B)⁻¹ * euclideanSq v)
      simp only [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
      constructor
      · calc
          boundedForceKappa L B * euclideanSq v ≤
              (boundedForceDensity B i x / 2 * Λ⁻¹) * euclideanSq v :=
            mul_le_mul_of_nonneg_right hscalar hsq
          _ = (boundedForceDensity B i x / 2) * (Λ⁻¹ * euclideanSq v) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left hlo (by positivity)
      · change boundedForceDensity B i x / 2 *
          dotProduct v ((reducedCoefficient ω (lam⁻¹ • x)).mulVec v) ≤
            ((2 * Λ * E)⁻¹)⁻¹ * euclideanSq v
        rw [inv_inv]
        calc
          _ ≤ (boundedForceDensity B i x / 2) * (Λ * euclideanSq v) :=
            mul_le_mul_of_nonneg_left hhi (by positivity)
          _ ≤ (E / 2) * (Λ * euclideanSq v) :=
            mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hρhi (by norm_num))
              (mul_nonneg hΛpos.le hsq)
          _ ≤ (2 * Λ * E) * euclideanSq v := by
            have h : E / 2 * Λ ≤ 2 * Λ * E := by nlinarith
            nlinarith [mul_le_mul_of_nonneg_right h hsq]

end EinsteinFull.Regeneration
