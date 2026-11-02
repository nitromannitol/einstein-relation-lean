import EinsteinFull.Work.W7.ClockCovarianceLimitProof

/-!
# Complex Schwartz consumers of the actual clock covariance

The tests here may have arbitrary commutator coordinates. We extract only
 their clock coordinate, in the literal L² Bochner spatial pairing. The final
restriction theorem uses the full frozen joint pairing on clock-only tests.
-/

open MeasureTheory

noncomputable section

namespace EinsteinFull
open EinsteinRelation

variable {d : ℕ} {Λ₀ r₀ : ℝ}

/-- The clock coordinate of an arbitrary joint Schwartz test is continuous. -/
theorem continuous_clockSchwartzCoordinate
    (F : SchwartzMap (Vec d) (EuclideanSpace ℂ (JointObservationIndex d))) :
    Continuous (fun x => F x (.inr ())) :=
  (PiLp.continuous_apply 2 _ (Sum.inr () : JointObservationIndex d)).comp F.continuous

/-- Its spatial integrability is inherited from the genuine Euclidean Schwartz map. -/
theorem integrable_clockSchwartzCoordinate
    (F : SchwartzMap (Vec d) (EuclideanSpace ℂ (JointObservationIndex d))) :
    Integrable (fun x => F x (.inr ())) :=
  F.integrable.mono (continuous_clockSchwartzCoordinate F).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => PiLp.norm_apply_le (F x) _)

/-- Real and imaginary tests reconstruct the actual L² Bochner integral. -/
theorem complexClockSpatialPairing_re_im (Q : EnvironmentLaw d Λ₀ r₀)
    (u : Lp ℂ 2 (reducedLaw Q)) {f : Vec d → ℂ}
    (hf : Integrable f) (hc : Continuous f) :
    complexClockSpatialPairing Q u f =
      complexClockSpatialPairing Q u (fun x => (f x).re) +
        Complex.I • complexClockSpatialPairing Q u (fun x => (f x).im) := by
  letI := reducedLaw_probability Q
  have hr := integrable_kernel_complexTranslation (reducedLaw Q) (reducedLaw_stationary Q)
    (fun x => ((f x).re : ℂ)) hf.re.ofReal (Complex.continuous_ofReal.comp (Complex.continuous_re.comp hc)) u
  have hi := integrable_kernel_complexTranslation (reducedLaw Q) (reducedLaw_stationary Q)
    (fun x => ((f x).im : ℂ)) hf.im.ofReal (Complex.continuous_ofReal.comp (Complex.continuous_im.comp hc)) u
  change (∫ x, f x • complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x u) = _
  calc
    _ = ∫ x, ((f x).re : ℂ) • complexTranslation (reducedLaw Q)
          (reducedLaw_stationary Q) x u +
        Complex.I • (((f x).im : ℂ) • complexTranslation (reducedLaw Q)
          (reducedLaw_stationary Q) x u) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        dsimp only
        rw [smul_smul, ← add_smul]
        congr 1
        simpa only [mul_comm Complex.I] using (Complex.re_add_im (f x)).symm
    _ = (∫ x, ((f x).re : ℂ) • complexTranslation (reducedLaw Q)
          (reducedLaw_stationary Q) x u) +
        ∫ x, Complex.I • (((f x).im : ℂ) • complexTranslation (reducedLaw Q)
          (reducedLaw_stationary Q) x u) := integral_add hr (hi.fun_smul Complex.I)
    _ = _ := by
      unfold complexClockSpatialPairing
      rw [integral_smul]

/-- The actual translated clock is real, so conjugating the second observation
has no effect. This explicitly fixes the normalization before complex tests. -/
theorem integral_translated_clock_conj (Q : EnvironmentLaw d Λ₀ r₀)
    {u : Lp ℂ 2 (reducedLaw Q)}
    (hu : (u : FieldPair d → ℂ) =ᵐ[reducedLaw Q]
      fun ω => (centeredClockField Q 0 ω : ℂ)) (x y : Vec d) :
    (∫ ω, complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x u ω *
      (starRingEnd ℂ) (complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) y u ω)
        ∂reducedLaw Q) = (clockCovariance Q x y : ℂ) := by
  have hy : (fun ω => complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) y u ω)
      =ᵐ[reducedLaw Q] fun ω => (centeredClockField Q y ω : ℂ) := by
    have hp := (measurePreserving_translate (reducedLaw Q)
      (reducedLaw_stationary Q) y).quasiMeasurePreserving.ae hu
    filter_upwards [coeFn_complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) y u,
      hp] with ω hω hω'
    rw [hω, hω']
    simp only [centeredClockField, translate_scalar, add_zero]
  rw [← integral_translated_clock_mul Q hu x y]
  apply integral_congr_ae
  filter_upwards [hy] with ω hω
  rw [hω]
  simp only [Complex.conj_ofReal]

/-- Conjugating both tests conjugates their bilinear limiting contraction.
There is no Hermitian conjugate in the source covariance formula. -/
theorem clockSchwartz_conjugate_contraction (Q : EnvironmentLaw d Λ₀ r₀)
    (F G : SchwartzMap (Vec d) (EuclideanSpace ℂ (JointObservationIndex d))) :
    (∫ x, (starRingEnd ℂ) (F x (.inr ())) * (clockCovarianceLimit Q : ℂ) *
      (starRingEnd ℂ) (G x (.inr ()))) =
      (starRingEnd ℂ) (∫ x, F x (.inr ()) * (clockCovarianceLimit Q : ℂ) * G x (.inr ())) := by
  rw [← integral_conj]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by simp only [map_mul, Complex.conj_ofReal]

/-- Quantitative clock covariance for every joint complex Schwartz test.
Only its clock coordinate is integrated, and the norm is the original joint norm. -/
theorem complexSchwartz_clock_covariance_error_le (Q : EnvironmentLaw d Λ₀ r₀)
    {N : ℕ} (hN : d < N)
    {u : Lp ℂ 2 (reducedLaw Q)}
    (hu : (u : FieldPair d → ℂ) =ᵐ[reducedLaw Q]
      fun ω => (centeredClockField Q 0 ω : ℂ))
    {R : ℝ} (hR : 0 < R)
    (F G : SchwartzMap (Vec d) (EuclideanSpace ℂ (JointObservationIndex d))) :
    ‖(∫ ω, scaledComplexClockPairing Q R u (fun x => F x (.inr ())) ω *
        scaledComplexClockPairing Q R u (fun x => G x (.inr ())) ω ∂reducedLaw Q) -
      ∫ x, F x (.inr ()) * (clockCovarianceLimit Q : ℂ) * G x (.inr ())‖ ≤
      (r₀ * clockVarianceConstant d Λ₀ r₀ * d * clockSchwartzWeightMass d N) *
        schwartzTestNorm N F * schwartzTestNorm N G * R⁻¹ := by
  have hg (x : Vec d) : ‖G x (.inr ())‖ ≤ schwartzTestNorm N G := by
    apply (PiLp.norm_apply_le (G x) _).trans
    exact (le_mul_of_one_le_left (norm_nonneg _)
      (one_le_pow₀ (le_add_of_nonneg_right (Real.sqrt_nonneg _)))).trans
        (clockSchwartz_weighted_value_le N G x)
  have ht (x z : Vec d) : ‖G (x + z) (.inr ()) - G x (.inr ())‖ ≤
      (d * schwartzTestNorm N G) * euclideanNorm z :=
    (PiLp.norm_apply_le (G (x + z) - G x) (.inr ())).trans
      (clockSchwartz_translation_le (by omega) G x z)
  have hI : (∫ x, ‖F x (.inr ())‖) ≤
      clockSchwartzWeightMass d N * schwartzTestNorm N F :=
    (integral_mono (integrable_clockSchwartzCoordinate F).norm F.integrable.norm
      (fun x => PiLp.norm_apply_le (F x) _)).trans (clockSchwartz_integral_norm_le hN F)
  have he : (∫ x, F x (.inr ()) * (clockCovarianceLimit Q : ℂ) * G x (.inr ())) =
      (clockCovarianceLimit Q : ℂ) * ∫ x, F x (.inr ()) * G x (.inr ()) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun _ => by ring
  rw [he]
  apply (scaledComplexClockPairing_error_le Q hu (continuous_clockSchwartzCoordinate F)
    (continuous_clockSchwartzCoordinate G) (integrable_clockSchwartzCoordinate F)
    (integrable_clockSchwartzCoordinate G)
    (mul_nonneg (Nat.cast_nonneg _) (clockSchwartz_norm_nonneg N G)) hg ht hR).trans
  have hV : 0 ≤ clockVarianceConstant d Λ₀ r₀ :=
    mul_nonneg (sq_nonneg _) (pow_nonneg (by linarith [Q.range_parameter]) _)
  have hb := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hI
    (mul_nonneg (mul_nonneg (zero_le_one.trans Q.range_parameter) hV)
      (mul_nonneg (Nat.cast_nonneg d) (clockSchwartz_norm_nonneg N G))))
    (inv_nonneg.mpr hR.le)
  convert hb using 1
  ring

/-- Uniform structural power rate for arbitrary complex Schwartz clock coordinates.
The scalar is the actual law-dependent covariance integral, shared by all tests. -/
theorem complexSchwartz_clock_covariance_scaling (d : ℕ) (D : StructuralData d)
    (N : ℕ) (hN : 2 * d + 10 < N) :
    ∃ ε C : ℝ, 0 < ε ∧ 0 < C ∧
    ∀ Q : EnvironmentLaw d D.ellipticity D.dependenceRange,
    ∃ q : ℝ, q = clockCovarianceLimit Q ∧ 0 ≤ q ∧ |q| ≤ C ∧
      ∀ u : Lp ℂ 2 (reducedLaw Q),
        ((u : FieldPair d → ℂ) =ᵐ[reducedLaw Q]
          fun ω => (centeredClockField Q 0 ω : ℂ)) →
      ∀ R : ℝ, 2 ≤ R →
      ∀ F G : SchwartzMap (Vec d) (EuclideanSpace ℂ (JointObservationIndex d)),
        ‖(∫ ω, scaledComplexClockPairing Q R u (fun x => F x (.inr ())) ω *
            scaledComplexClockPairing Q R u (fun x => G x (.inr ())) ω ∂reducedLaw Q) -
          ∫ x, F x (.inr ()) * (q : ℂ) * G x (.inr ())‖ ≤
          C * schwartzTestNorm N F * schwartzTestNorm N G * R ^ (-ε) := by
  let V := clockVarianceConstant d D.ellipticity D.dependenceRange
  let A := D.dependenceRange * V * d * clockSchwartzWeightMass d N
  have hr : 0 ≤ D.dependenceRange := zero_le_one.trans D.one_le_dependenceRange
  have hV : 0 ≤ V := mul_nonneg (sq_nonneg _) (pow_nonneg (mul_nonneg (by norm_num) hr) _)
  have hW : 0 ≤ clockSchwartzWeightMass d N :=
    integral_nonneg fun _ => Real.rpow_nonneg (by positivity) _
  have hA : 0 ≤ A := mul_nonneg (mul_nonneg (mul_nonneg hr hV) (Nat.cast_nonneg _)) hW
  refine ⟨1, 1 + V + A, by norm_num, by positivity, fun Q => ?_⟩
  refine ⟨clockCovarianceLimit Q, rfl, clockCovarianceLimit_nonneg Q,
    (abs_clockCovarianceLimit_le Q).trans (by dsimp only [V]; linarith), ?_⟩
  intro u hu R hR F G
  rw [Real.rpow_neg_one]
  exact (complexSchwartz_clock_covariance_error_le Q (by omega : d < N) hu
    (by linarith : 0 < R) F G).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (show A ≤ 1 + V + A by linarith) (clockSchwartz_norm_nonneg N F))
        (clockSchwartz_norm_nonneg N G)) (inv_nonneg.mpr (by linarith)))

/-- Exact identification with the frozen joint pairing when the other coordinates
vanish. This is an equality of L² Bochner integrals, before taking covariance. -/
theorem complexSchwartz_clock_exact_joint_consumer (Q : EnvironmentLaw d Λ₀ r₀)
    (R : ℝ) (hR : 0 < R) (Z : JointObservationIndex d → Lp ℂ 2 (reducedLaw Q))
    (F : SchwartzMap (Vec d) (EuclideanSpace ℂ (JointObservationIndex d)))
    (hF : ∀ x j i, F x (.inl (j, i)) = 0) :
    scaledComplexClockPairing Q R (Z (.inr ())) (fun x => F x (.inr ())) =
      scaledJointPairing Q R hR Z F :=
  (scaledJointPairing_eq_clock Q R hR Z F hF).symm

end EinsteinFull
