import EinsteinFull.Blueprint.G4.node_p_u3A_integration_u23_uniform_u2D_profile_u2D_bounds
import EinsteinFull.Blueprint.Roots.node_p_u3A_covariance
import EinsteinFull.Blueprint.Foundation.node_corrector_u2D_construction
import EinsteinFull.Work.W3.GaussianJointProfileTestSupport
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

noncomputable section

namespace EinsteinFull.Blueprint

open EinsteinRelation MeasureTheory Filter
open scoped Topology NNReal BigOperators

/-- A quantitative covariance estimate gives the literal frozen limiting covariance. -/
theorem w2_jointCovariance_of_rate {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀)
    (Z : JointObservationIndex d → Lp ℂ 2 (reducedLaw Q))
    (covariance : Matrix (JointObservationIndex d) (JointObservationIndex d) ℝ)
    (N : ℕ) (ε C : ℝ) (hε : 0 < ε)
    (hrate : ∀ R : ℝ, ∀ hR : 2 ≤ R,
      ∀ F G : SchwartzMap (Vec d) (EuclideanSpace ℂ (JointObservationIndex d)),
        ‖(∫ ω, scaledJointPairing Q R (by linarith) Z F ω *
          scaledJointPairing Q R (by linarith) Z G ω ∂reducedLaw Q) -
          jointTestCovariance covariance F G‖ ≤
        C * schwartzTestNorm N F * schwartzTestNorm N G * R ^ (-ε)) :
    IsJointCovariance Q Z covariance := by
  intro F G
  rw [← jointTestCovariance_eq_integral]
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have ht : Tendsto (fun R : ℝ≥0 => (R : ℝ) + 2) atTop atTop :=
    tendsto_atTop_add_const_right atTop (2 : ℝ) (NNReal.tendsto_coe_atTop.mpr tendsto_id)
  have hz := ((tendsto_rpow_neg_atTop hε).comp ht).const_mul
    (C * schwartzTestNorm N F * schwartzTestNorm N G)
  simp only [mul_zero] at hz
  exact squeeze_zero (fun _ => norm_nonneg _) (fun R => hrate _ (by linarith [R.coe_nonneg]) F G) hz

private lemma coordinate_test_covariance {d : ℕ}
    (C : Matrix (JointObservationIndex d) (JointObservationIndex d) ℝ)
    (a b : JointObservationIndex d) (ψ φ : SchwartzMap (Vec d) ℂ) :
    jointTestCovariance C (jointCoordinateSchwartz a ψ) (jointCoordinateSchwartz b φ) =
      (∫ x : Vec d, ψ x * φ x) * (C a b : ℂ) := by
  have he (u v : JointObservationIndex d) :
      (∫ x : Vec d, jointCoordinateSchwartz a ψ x u * jointCoordinateSchwartz b φ x v) =
        if u = a then if v = b then ∫ x : Vec d, ψ x * φ x else 0 else 0 := by
    by_cases hu : u = a <;> by_cases hv : v = b <;>
      simp only [jointCoordinateSchwartz_apply, hu, hv, if_true, if_false,
        zero_mul, mul_zero, integral_zero]
  simp only [jointTestCovariance, he, ite_mul, zero_mul, Finset.sum_ite_irrel,
    Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- Coordinate Gaussian tests determine every entry of the actual limiting covariance. -/
theorem w2_jointCovariance_unique {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀)
    (Z : JointObservationIndex d → Lp ℂ 2 (reducedLaw Q))
    {C C' : Matrix (JointObservationIndex d) (JointObservationIndex d) ℝ}
    (hC : IsJointCovariance Q Z C) (hC' : IsJointCovariance Q Z C') : C = C' := by
  let first : Fin d := ⟨0, by omega⟩
  let ψ := profileGaussianSchwartz Q first 0
  have hi : (∫ x : Vec d, ψ x * ψ x) ≠ 0 := by
    have h := integral_homogenizedGaussianKernel_convolution Q first (1/2) (1/2)
      (by norm_num) (by norm_num) 0 (0 : Vec d)
    have he (x : Vec d) : homogenizedGaussianKernel Q first (1/2) (by norm_num) 0 (-x) =
        homogenizedGaussianKernel Q first (1/2) (by norm_num) 0 x := by
      rw [homogenizedGaussianKernel_zero_eq_ofReal, homogenizedGaussianKernel_zero_eq_ofReal,
        anisotropicGaussian_neg]
    simp only [zero_sub, he] at h
    change (∫ x : Vec d, ψ x * ψ x) = _ at h
    rw [h]
    simp only [homogenizedGaussianKernel, sub_zero, zero_mul, Pi.zero_apply,
      Complex.ofReal_zero, Finset.sum_const_zero, neg_zero, zero_div, Complex.exp_zero,
      mul_one, Complex.ofReal_ne_zero]
    exact div_ne_zero (Real.rpow_pos_of_pos (by positivity) _).ne'
      (Real.sqrt_pos.mpr (det_homogenizedCoefficient_pos Q)).ne'
  ext a b
  have he := tendsto_nhds_unique
    (hC (jointCoordinateSchwartz a ψ) (jointCoordinateSchwartz b ψ))
    (hC' (jointCoordinateSchwartz a ψ) (jointCoordinateSchwartz b ψ))
  rw [← jointTestCovariance_eq_integral, ← jointTestCovariance_eq_integral,
    coordinate_test_covariance, coordinate_test_covariance] at he
  exact Complex.ofReal_injective (mul_left_cancel₀ hi he)

/-- The covariance proposition bounds the entries of every covariance satisfying
its literal limiting characterization, with the same structural constant. -/
theorem w2_uniform_covariance_entries
    (hcov : node_p_u3A_covarianceStmt) (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) :
    ∃ B : ℝ, 0 < B ∧
      ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange), HasSmoothBounds D Q →
      ∀ (Z : JointObservationIndex d → Lp ℂ 2 (reducedLaw Q))
        (C : Matrix (JointObservationIndex d) (JointObservationIndex d) ℝ),
        IsJointObservation Q Z → IsJointCovariance Q Z C → ∀ a b, |C a b| ≤ B := by
  obtain ⟨ε, B, hε, hB, hh⟩ := hcov d hd D (2*d+11) (by omega)
  refine ⟨B, hB, ?_⟩
  intro Q hQ Z C hZ hC
  obtain ⟨C', _hpos, hop, hrate⟩ := hh Q hQ
  have he : C = C' := w2_jointCovariance_unique hd Q Z hC
    (w2_jointCovariance_of_rate Q Z C' (2*d+11) ε B hε (by
      intro R hR F G
      simpa only [jointTestCovariance_eq_integral] using hrate Z hZ R hR F G))
  subst C'
  intro a b
  have h := (PiLp.norm_apply_le
    (WithLp.toLp 2 (C.mulVec (WithLp.ofLp (EuclideanSpace.single b (1 : ℝ)))) ) a).trans
    (hop (EuclideanSpace.single b (1 : ℝ)))
  simpa only [EuclideanSpace.ofLp_single, Matrix.mulVec_single_one, Matrix.col_apply,
    PiLp.toLp_apply, Real.norm_eq_abs, EuclideanSpace.norm_single, norm_one, mul_one] using h

private lemma profile_contraction_bound {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀)
    (covariance : Matrix (JointObservationIndex d) (JointObservationIndex d) ℝ)
    (B : ℝ) (hb : ∀ a b, |covariance a b| ≤ B) (i k : Fin d) :
    |∑ j : Fin d, ∑ l : Fin d,
      ((homogenizedCoefficient Q)⁻¹) j l * covariance (.inl (j,i)) (.inl (l,k))| ≤
        (d : ℝ) * d * (sourceReducedBound Λ₀ * B) := by
  calc
    _ ≤ ∑ j : Fin d, ∑ l : Fin d,
        |((homogenizedCoefficient Q)⁻¹) j l * covariance (.inl (j,i)) (.inl (l,k))| :=
      (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun j _ =>
        Finset.abs_sum_le_sum_abs _ _))
    _ ≤ ∑ _j : Fin d, ∑ _l : Fin d, sourceReducedBound Λ₀ * B := by
      apply Finset.sum_le_sum
      intro j _
      apply Finset.sum_le_sum
      intro l _
      rw [abs_mul]
      exact mul_le_mul (abs_homogenizedCoefficient_inv_entry_le Q j l) (hb _ _)
        (abs_nonneg _) ((abs_nonneg _).trans
          (abs_homogenizedCoefficient_inv_entry_le Q j l))
    _ = _ := by simp [mul_assoc]

private lemma velocity_profile_normalForm {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀)
    (covariance : Matrix (JointObservationIndex d) (JointObservationIndex d) ℝ)
    (i : Fin d) (z : ℂ) :
    let first : Fin d := ⟨0, by omega⟩
    let p : ℝ := (2 * Real.pi) ^ (-(d : ℝ) / 2) / Real.sqrt (homogenizedCoefficient Q).det
    velocityGaussianProfile hd Q covariance i z =
      complexGaussianProfile
        (p / 4 * ∑ j, ∑ k, ((homogenizedCoefficient Q)⁻¹) j k *
          covariance (.inl (j,first)) (.inl (k,i)))
        (p / 4 * covariance (.inl (first,first)) (.inl (first,i)))
        (homogenizedCoefficient Q first first / 2) z := by
  dsimp [velocityGaussianProfile, complexGaussianProfile]
  push_cast
  ring

private lemma clock_profile_normalForm {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀)
    (covariance : Matrix (JointObservationIndex d) (JointObservationIndex d) ℝ) (z : ℂ) :
    let first : Fin d := ⟨0, by omega⟩
    let p : ℝ := (2 * Real.pi) ^ (-(d : ℝ) / 2) / Real.sqrt (homogenizedCoefficient Q).det
    clockGaussianProfile hd Q covariance z =
      complexGaussianProfile 0 (p / 2 * covariance (.inl (first,first)) (.inr ()))
        (homogenizedCoefficient Q first first / 2) z := by
  dsimp [clockGaussianProfile, complexGaussianProfile]
  push_cast
  ring

/-- Uniform bounds for the literal anisotropic profiles, from exactly their two graph dependencies. -/
@[nolint unusedArguments]
theorem node_p_u3A_integration_u23_uniform_u2D_profile_u2D_bounds_of_deps
    (hcov : node_p_u3A_covarianceStmt)
    (_hcorrector : node_corrector_u2D_constructionStmt) :
    node_p_u3A_integration_u23_uniform_u2D_profile_u2D_boundsStmt := by
  intro d hd D
  obtain ⟨B, hB, hb⟩ := w2_uniform_covariance_entries hcov d hd D
  let K := sourceReducedBound D.ellipticity
  have hK : 0 < K := by
    dsimp [K, sourceReducedBound]
    apply mul_pos (Real.exp_pos _)
    nlinarith [D.one_le_ellipticity, sq_nonneg D.ellipticity]
  let P := (2 * Real.pi) ^ (-(d : ℝ) / 2) *
    Real.sqrt ((Fintype.card (Equiv.Perm (Fin d)) : ℝ) * K ^ d)
  have hP : 0 ≤ P := by dsimp [P]; positivity
  let U := P / 4 * ((d : ℝ) * d * (K * B)) + P / 2 * B
  have hU : 0 ≤ U := by dsimp [U]; positivity
  refine ⟨K⁻¹ / 2, 1 + K / 2 + U, by positivity, by positivity, ?_⟩
  have hUC : U ≤ 1 + K / 2 + U := by linarith
  intro Q _hQ Z covariance hZ hC
  have hentries := hb Q _hQ Z covariance hZ hC
  let first : Fin d := ⟨0, by omega⟩
  let p : ℝ := (2 * Real.pi) ^ (-(d : ℝ) / 2) / Real.sqrt (homogenizedCoefficient Q).det
  have hp0 : 0 ≤ p := by dsimp [p]; positivity
  have hpP : p ≤ P := by
    dsimp [p, P]
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left (inv_sqrt_det_homogenizedCoefficient_le Q)
      (Real.rpow_nonneg (by positivity) _)
  have hγ : K⁻¹ ≤ homogenizedCoefficient Q first first ∧
      homogenizedCoefficient Q first first ≤ K := by
    have hl := homogenizedMatrix_quadratic_lower Q (unitVector first)
    have hu := homogenizedMatrix_quadratic_upper Q (unitVector first)
    simpa [homogenizedCoefficient, unitVector, dot, euclideanSq, Matrix.mulVec,
      dotProduct, Pi.single_apply, mul_ite, ite_mul] using! And.intro hl hu
  change K⁻¹ / 2 ≤ homogenizedCoefficient Q first first / 2 ∧
    homogenizedCoefficient Q first first / 2 ≤ 1 + K / 2 + U ∧ _
  refine ⟨by linarith [hγ.1], by linarith [hγ.2], ?_⟩
  intro κ
  cases κ with
  | none =>
    constructor
    · change |(0 : ℝ)| + |p / 2 * covariance (.inl (first,first)) (.inr ())| ≤ _
      have hh : |p / 2 * covariance (.inl (first,first)) (.inr ())| ≤ P / 2 * B := by
        rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ p / 2)]
        exact mul_le_mul (by linarith : p / 2 ≤ P / 2) (hentries _ _)
          (abs_nonneg _) (by positivity)
      have hPU : P / 2 * B ≤ U := by
        dsimp [U]
        exact le_add_of_nonneg_left (by positivity)
      simpa only [abs_zero, zero_add] using hh.trans (hPU.trans hUC)
    · exact clock_profile_normalForm hd Q covariance
  | some i =>
    constructor
    · change |p / 4 * ∑ j, ∑ k, ((homogenizedCoefficient Q)⁻¹) j k *
          covariance (.inl (j,first)) (.inl (k,i))| +
        |p / 4 * covariance (.inl (first,first)) (.inl (first,i))| ≤ _
      have h₀ : |p / 4 * ∑ j, ∑ k, ((homogenizedCoefficient Q)⁻¹) j k *
          covariance (.inl (j,first)) (.inl (k,i))| ≤
          P / 4 * ((d : ℝ) * d * (K * B)) := by
        rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ p / 4)]
        exact mul_le_mul (by linarith : p / 4 ≤ P / 4)
          (profile_contraction_bound Q covariance B hentries first i)
          (abs_nonneg _) (by positivity)
      have h₂ : |p / 4 * covariance (.inl (first,first)) (.inl (first,i))| ≤ P / 2 * B := by
        rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ p / 4)]
        exact mul_le_mul (by linarith : p / 4 ≤ P / 2) (hentries _ _)
          (abs_nonneg _) (by positivity)
      have hh := add_le_add h₀ h₂
      change _ ≤ U at hh
      exact hh.trans hUC
    · exact velocity_profile_normalForm hd Q covariance i

end EinsteinFull.Blueprint
