import EinsteinFull.Calculus.SbxS4KilledSpectralR01
import EinsteinFull.Regeneration.BoundedForceCoefficients

namespace EinsteinFull
open EinsteinRelation EinsteinRelation.External.GantertSection7Support
open EinsteinFull.External.Source.GMP

/-- The physical reversible density with the force coordinate clipped at `±S`. -/
noncomputable def bPhysicalClippedRho {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (S μ : ℝ) (x : Vec d) : ℝ :=
  Real.exp (2 * max (-S) (min S (μ * x (firstCoordinateIndex hd))) - 2 * ω.2 x)

/-- The corresponding physical matrix coefficient, including the factor one half. -/
noncomputable def bPhysicalClippedAlpha {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (S μ : ℝ) (x : Vec d) : Mat d :=
  ((1 / 2 : ℝ) * bPhysicalClippedRho hd ω S μ x) • ω.1 x

/-- An ellipticity constant chosen using only the original bound and radius. -/
noncomputable def bPhysicalClippedKappa (L S : ℝ) : ℝ :=
  (2 * L * Real.exp (2 * (S + L)))⁻¹

theorem b_physical_clipped_kappa_pos {L S : ℝ} (hL : 1 ≤ L) :
    0 < bPhysicalClippedKappa L S := by
  unfold bPhysicalClippedKappa
  exact inv_pos.mpr (mul_pos (mul_pos (by norm_num) (by linarith)) (Real.exp_pos _))

theorem b_physical_clipped_rho_continuous {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (S μ : ℝ) : Continuous (bPhysicalClippedRho hd ω S μ) := by
  unfold bPhysicalClippedRho
  exact Real.continuous_exp.comp ((continuous_const.mul
    (continuous_const.max (continuous_const.min (continuous_const.mul
      (continuous_apply (firstCoordinateIndex hd)))))).sub
    (continuous_const.mul ω.2.continuous))

theorem b_physical_clipped_rho_bounds {d : ℕ} {L S : ℝ} (hS : 0 ≤ S)
    (hd : 2 ≤ d) (ω : FieldPair d) (hω : IsRegular L ω) (μ : ℝ) (x : Vec d) :
    (Real.exp (2 * (S + L)))⁻¹ ≤ bPhysicalClippedRho hd ω S μ x ∧
    bPhysicalClippedRho hd ω S μ x ≤ Real.exp (2 * (S + L)) := by
  have hv := abs_le.mp (hω.2.1 x)
  have hlo := le_max_left (-S) (min S (μ * x (firstCoordinateIndex hd)))
  have hhi : max (-S) (min S (μ * x (firstCoordinateIndex hd))) ≤ S :=
    max_le (by linarith) (min_le_left _ _)
  constructor
  · rw [← Real.exp_neg]
    apply Real.exp_le_exp.mpr
    linarith
  · apply Real.exp_le_exp.mpr
    linarith

theorem b_physical_clipped_elliptic {d : ℕ} {L S : ℝ} (hL : 1 ≤ L) (hS : 0 ≤ S)
    (hd : 2 ≤ d) (ω : FieldPair d) (hω : IsRegular L ω) (μ : ℝ) :
    IsUniformlyElliptic (bPhysicalClippedKappa L S)
      (bPhysicalClippedRho hd ω S μ) (bPhysicalClippedAlpha hd ω S μ) := by
  let E := Real.exp (2 * (S + L))
  have hLpos : 0 < L := by linarith
  have hEpos : 0 < E := Real.exp_pos _
  have hEk : E ≤ 2 * L * E := by nlinarith
  have hkE : (2 * L * E)⁻¹ ≤ E⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le hEpos hEk
  refine ⟨(b_physical_clipped_rho_continuous hd ω S μ).measurable, ?_, ?_⟩
  · let : MeasurableSpace (Vec d) := MeasurableSpace.pi
    let : BorelSpace (Vec d) := Pi.borelSpace
    let : MeasurableSpace (Mat d) := EinsteinRelation.instMeasurableSpaceMat d
    let : BorelSpace (Mat d) := EinsteinRelation.instBorelSpaceMat d
    have hc : Continuous (bPhysicalClippedAlpha hd ω S μ) := by
      unfold bPhysicalClippedAlpha
      exact (continuous_const.mul (b_physical_clipped_rho_continuous hd ω S μ)).smul
        ω.1.continuous
    exact hc.measurable
  · intro x
    obtain ⟨hρlo, hρhi⟩ := b_physical_clipped_rho_bounds hS hd ω hω μ x
    have hρpos : 0 < bPhysicalClippedRho hd ω S μ x := Real.exp_pos _
    refine ⟨hkE.trans hρlo, ?_, ?_, ?_⟩
    · change bPhysicalClippedRho hd ω S μ x ≤ ((2 * L * E)⁻¹)⁻¹
      rw [inv_inv]
      exact hρhi.trans hEk
    · change (((1 / 2 : ℝ) * bPhysicalClippedRho hd ω S μ x) • ω.1 x).transpose = _
      rw [Matrix.transpose_smul, (hω.1 x).1]
      rfl
    · intro v
      obtain ⟨hlo, hhi⟩ := (hω.1 x).2 v
      have hsq : 0 ≤ euclideanSq v := by
        change 0 ≤ ∑ j, v j * v j
        exact Finset.sum_nonneg (fun _ _ => mul_self_nonneg _)
      have hscalar : (2 * L * E)⁻¹ ≤ (1 / 2 * bPhysicalClippedRho hd ω S μ x) * L⁻¹ := by
        calc
          (2 * L * E)⁻¹ = (1 / 2 * E⁻¹) * L⁻¹ := by field_simp
          _ ≤ (1 / 2 * bPhysicalClippedRho hd ω S μ x) * L⁻¹ :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hρlo (by norm_num))
              (inv_nonneg.mpr hLpos.le)
      change (bPhysicalClippedKappa L S * euclideanSq v ≤
          dotProduct v ((((1 / 2 : ℝ) * bPhysicalClippedRho hd ω S μ x) • ω.1 x).mulVec v)) ∧
        (dotProduct v ((((1 / 2 : ℝ) * bPhysicalClippedRho hd ω S μ x) • ω.1 x).mulVec v) ≤
          (bPhysicalClippedKappa L S)⁻¹ * euclideanSq v)
      simp only [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
      constructor
      · calc
          bPhysicalClippedKappa L S * euclideanSq v ≤
              ((1 / 2 * bPhysicalClippedRho hd ω S μ x) * L⁻¹) * euclideanSq v :=
            mul_le_mul_of_nonneg_right hscalar hsq
          _ = (1 / 2 * bPhysicalClippedRho hd ω S μ x) * (L⁻¹ * euclideanSq v) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left hlo (by positivity)
      · change (1 / 2 * bPhysicalClippedRho hd ω S μ x) *
          dotProduct v ((ω.1 x).mulVec v) ≤ ((2 * L * E)⁻¹)⁻¹ * euclideanSq v
        rw [inv_inv]
        calc
          _ ≤ (1 / 2 * bPhysicalClippedRho hd ω S μ x) * (L * euclideanSq v) :=
            mul_le_mul_of_nonneg_left hhi (by positivity)
          _ ≤ (1 / 2 * E) * (L * euclideanSq v) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hρhi (by norm_num))
              (mul_nonneg hLpos.le hsq)
          _ ≤ (2 * L * E) * euclideanSq v := by
            have h : 1 / 2 * E * L ≤ 2 * L * E := by nlinarith
            nlinarith [mul_le_mul_of_nonneg_right h hsq]

theorem b_physical_clipped_eq_on_ball {d : ℕ} {S μ : ℝ} (hμ : 0 < μ)
    (hd : 2 ≤ d) (ω : FieldPair d) (x : Vec d)
    (hx : x ∈ sourceBall (0 : Vec d) (S / μ)) :
    bPhysicalClippedRho hd ω S μ x = s4PhysicalRho hd ω μ x ∧
    bPhysicalClippedAlpha hd ω S μ x = s4PhysicalAlpha hd ω μ x := by
  have hx' : euclideanNorm x < S / μ := by simpa [sourceBall] using hx
  have hc := (EinsteinRelation.Regeneration.coordinate_abs_le_euclideanNorm x
    (firstCoordinateIndex hd)).trans hx'.le
  have hc' : |μ * x (firstCoordinateIndex hd)| ≤ S := by
    rw [abs_mul, abs_of_pos hμ]
    exact (mul_le_mul_of_nonneg_left hc hμ.le).trans (by
      rw [mul_div_cancel₀ S (ne_of_gt hμ)])
  have hc'' := abs_le.mp hc'
  have heq : bPhysicalClippedRho hd ω S μ x = s4PhysicalRho hd ω μ x := by
    rw [s4PhysicalRho, physicalReversibleDensity_eq_source_formula]
    simp only [bPhysicalClippedRho, min_eq_right hc''.2, max_eq_right hc''.1]
    congr 1
    ring
  exact ⟨heq, by simp only [bPhysicalClippedAlpha, s4PhysicalAlpha, heq]⟩

/-- A uniform physical extension on the entire scaled Euclidean ball. -/
theorem b_physical_clipped_extension {d : ℕ} (hd : 2 ≤ d) (L S : ℝ)
    (hL : 1 ≤ L) (hS : 0 < S) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ (ω : FieldPair d), IsRegular L ω →
      ∀ μ : ℝ, 0 < μ → μ ≤ 1 →
        ∃ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
          IsUniformlyElliptic κ ρ α ∧
          ∀ x ∈ sourceBall (0 : Vec d) (S / μ),
            ρ x = s4PhysicalRho hd ω μ x ∧ α x = s4PhysicalAlpha hd ω μ x := by
  refine ⟨bPhysicalClippedKappa L S, b_physical_clipped_kappa_pos hL, ?_⟩
  intro ω hω μ hμ _
  exact ⟨bPhysicalClippedRho hd ω S μ, bPhysicalClippedAlpha hd ω S μ,
    b_physical_clipped_elliptic hL hS.le hd ω hω μ,
    fun x hx => b_physical_clipped_eq_on_ball hμ hd ω x hx⟩


end EinsteinFull
