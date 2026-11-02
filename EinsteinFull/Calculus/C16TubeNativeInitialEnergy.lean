import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import EinsteinFull.External.Source.GMPDirichletSpectralKernel
import EinsteinFull.Blueprint.Foundation.Proofs.SbxS3TubeProbability

open MeasureTheory

namespace EinsteinFull.Calculus

/-- The total time integral of one positive spectral energy mode. -/
theorem c16_positive_spectral_mode_integral (ell : ℝ) (hell : 0 < ell) :
    (∫ t in Set.Ioi (0 : ℝ), ell * Real.exp (-(2 * ell) * t)) = (1 / 2 : ℝ) := by
  rw [integral_const_mul, integral_exp_mul_Ioi (neg_lt_zero.mpr (mul_pos (by norm_num) hell))]
  simp only [mul_zero, Real.exp_zero]
  have hne : ell ≠ 0 := ne_of_gt hell
  field_simp
  <;> ring

/-- Bessel's inequality bounds the time-integrated energy of finitely many
orthonormal positive modes by half the squared norm of the initial datum. -/
theorem c16_finite_spectral_mode_energy {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] {v : ℕ → H} (hv : Orthonormal ℝ v)
    (ell : ℕ → ℝ) (hell : ∀ n, 0 < ell n) (f : H) (s : Finset ℕ) :
    IntegrableOn (fun t => ∑ n ∈ s,
      (inner ℝ (v n) f) ^ 2 * (ell n * Real.exp (-(2 * ell n) * t)))
      (Set.Ioi 0) ∧
    (∫ t in Set.Ioi (0 : ℝ), ∑ n ∈ s,
      (inner ℝ (v n) f) ^ 2 * (ell n * Real.exp (-(2 * ell n) * t))) ≤
      (1 / 2 : ℝ) * ‖f‖ ^ 2 := by
  have hi (n : ℕ) : IntegrableOn (fun t =>
      (inner ℝ (v n) f) ^ 2 * (ell n * Real.exp (-(2 * ell n) * t)))
      (Set.Ioi 0) := by
    exact ((integrableOn_exp_mul_Ioi
      (neg_lt_zero.mpr (mul_pos (by norm_num) (hell n))) 0).const_mul (ell n)).const_mul _
  constructor
  · exact integrable_finset_sum s (fun n _ => hi n)
  · rw [integral_finset_sum s (fun n _ => hi n)]
    have he (n : ℕ) : (∫ t in Set.Ioi (0 : ℝ),
        (inner ℝ (v n) f) ^ 2 * (ell n * Real.exp (-(2 * ell n) * t))) =
        (1 / 2 : ℝ) * ‖inner ℝ (v n) f‖ ^ 2 := by
      rw [integral_const_mul, c16_positive_spectral_mode_integral (ell n) (hell n)]
      rw [Real.norm_eq_abs, sq_abs]
      ring
    simp_rw [he, ← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (hv.sum_inner_products_le f) (by norm_num)

/-- The same finite-mode estimate holds on any positive time interval. -/
theorem c16_finite_spectral_mode_energy_on_interval {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] {v : ℕ → H} (hv : Orthonormal ℝ v)
    (ell : ℕ → ℝ) (hell : ∀ n, 0 < ell n) (f : H) (s : Finset ℕ) (T : ℝ) :
    IntegrableOn (fun t => ∑ n ∈ s,
      (inner ℝ (v n) f) ^ 2 * (ell n * Real.exp (-(2 * ell n) * t)))
      (Set.Ioo 0 T) ∧
    (∫ t in Set.Ioo (0 : ℝ) T, ∑ n ∈ s,
      (inner ℝ (v n) f) ^ 2 * (ell n * Real.exp (-(2 * ell n) * t))) ≤
      (1 / 2 : ℝ) * ‖f‖ ^ 2 := by
  obtain ⟨hi, hb⟩ := c16_finite_spectral_mode_energy hv ell hell f s
  have hsub : Set.Ioo (0 : ℝ) T ⊆ Set.Ioi 0 := fun _ ht => ht.1
  refine ⟨hi.mono_set hsub, ?_⟩
  apply (integral_mono_measure (Measure.restrict_mono hsub le_rfl) ?_ hi).trans hb
  exact ae_of_all _ fun t => Finset.sum_nonneg fun n _ =>
    mul_nonneg (sq_nonneg _) (mul_nonneg (hell n).le (Real.exp_pos _).le)

/-- The finite-mode energy bound for the actual weighted Dirichlet spectrum. -/
theorem c16_dirichlet_finite_spectral_mode_energy {d : ℕ}
    {rho : EinsteinRelation.Vec d → ℝ} {alpha : EinsteinRelation.Vec d → EinsteinRelation.Mat d}
    {R : ℝ} (s : External.Source.GMP.DirichletSpectralResolution rho alpha R)
    (f : Lp ℝ 2 (External.Source.GMP.dirichletVolume rho R)) (I : Finset ℕ) (T : ℝ) :
    IntegrableOn (fun t => ∑ n ∈ I,
      (inner ℝ ((s.square_integrable n).toLp (s.eigenfunction n)) f) ^ 2 *
        (s.eigenvalue n * Real.exp (-(2 * s.eigenvalue n) * t))) (Set.Ioo 0 T) ∧
    (∫ t in Set.Ioo (0 : ℝ) T, ∑ n ∈ I,
      (inner ℝ ((s.square_integrable n).toLp (s.eigenfunction n)) f) ^ 2 *
        (s.eigenvalue n * Real.exp (-(2 * s.eigenvalue n) * t))) ≤
      (1 / 2 : ℝ) * ‖f‖ ^ 2 := by
  exact c16_finite_spectral_mode_energy_on_interval s.orthonormal s.eigenvalue
    s.eigenvalue_pos f I T

/-- The weighted spectral Hilbert norm is the actual weighted spatial energy. -/
theorem c16_dirichlet_weighted_norm_sq {d : ℕ}
    {rho : EinsteinRelation.Vec d → ℝ} {alpha : EinsteinRelation.Vec d → EinsteinRelation.Mat d}
    {R kappa : ℝ} (hkappa : 0 < kappa)
    (hell : External.Source.GMP.IsUniformlyElliptic kappa rho alpha)
    (phi : EinsteinRelation.Vec d → ℝ)
    (hphi : MemLp phi 2 (External.Source.GMP.dirichletVolume rho R)) :
    ‖hphi.toLp phi‖ ^ 2 = ∫ x in External.Source.GMP.sourceBall (0 : EinsteinRelation.Vec d) R,
      rho x * phi x ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  have heq : (∫ x, inner ℝ (hphi.toLp phi x) (hphi.toLp phi x)
      ∂External.Source.GMP.dirichletVolume rho R) =
      ∫ x, phi x ^ 2 ∂External.Source.GMP.dirichletVolume rho R := by
    apply integral_congr_ae
    filter_upwards [hphi.coeFn_toLp] with x hx
    rw [hx]
    simp only [Real.inner_apply, sq]
  rw [heq]
  change (∫ x, phi x ^ 2 ∂(volume.restrict
    (External.Source.GMP.sourceBall (0 : EinsteinRelation.Vec d) R)).withDensity
      (fun x => ENNReal.ofReal (rho x))) = _
  rw [integral_withDensity_eq_integral_toReal_smul hell.1.ennreal_ofReal
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards with x
  simp only [ENNReal.toReal_ofReal (hkappa.le.trans (hell.2.2 x).1), smul_eq_mul]

/-- Finite native spectral modes are controlled by the weighted spatial datum. -/
theorem c16_dirichlet_finite_modes_weighted_energy {d : ℕ}
    {rho : EinsteinRelation.Vec d → ℝ} {alpha : EinsteinRelation.Vec d → EinsteinRelation.Mat d}
    {R kappa : ℝ} (hkappa : 0 < kappa)
    (hell : External.Source.GMP.IsUniformlyElliptic kappa rho alpha)
    (s : External.Source.GMP.DirichletSpectralResolution rho alpha R)
    (phi : EinsteinRelation.Vec d → ℝ)
    (hphi : MemLp phi 2 (External.Source.GMP.dirichletVolume rho R))
    (I : Finset ℕ) (T : ℝ) :
    IntegrableOn (fun t => ∑ n ∈ I,
      (inner ℝ ((s.square_integrable n).toLp (s.eigenfunction n)) (hphi.toLp phi)) ^ 2 *
        (s.eigenvalue n * Real.exp (-(2 * s.eigenvalue n) * t))) (Set.Ioo 0 T) ∧
    (∫ t in Set.Ioo (0 : ℝ) T, ∑ n ∈ I,
      (inner ℝ ((s.square_integrable n).toLp (s.eigenfunction n)) (hphi.toLp phi)) ^ 2 *
        (s.eigenvalue n * Real.exp (-(2 * s.eigenvalue n) * t))) ≤
      (1 / 2 : ℝ) * ∫ x in External.Source.GMP.sourceBall (0 : EinsteinRelation.Vec d) R,
        rho x * phi x ^ 2 := by
  simpa only [c16_dirichlet_weighted_norm_sq hkappa hell phi hphi] using
    c16_dirichlet_finite_spectral_mode_energy s (hphi.toLp phi) I T

/-- Every spatial test belongs to the weighted Dirichlet L² space. -/
theorem c16_spatial_test_memLp_dirichlet {d : ℕ}
    {rho : EinsteinRelation.Vec d → ℝ} {alpha : EinsteinRelation.Vec d → EinsteinRelation.Mat d}
    {R kappa : ℝ} (hR : 0 < R)
    (hell : External.Source.GMP.IsUniformlyElliptic kappa rho alpha)
    (phi : EinsteinRelation.Vec d → ℝ)
    (hphi : EinsteinRelation.IsSpatialTest (External.Source.GMP.sourceBall 0 R) phi) :
    MemLp phi 2 (External.Source.GMP.dirichletVolume rho R) := by
  letI : IsFiniteMeasure (External.Source.GMP.dirichletVolume rho R) :=
    Blueprint.TubeProbability.dirichletVolume_isFinite rho R hR kappa⁻¹
      (fun x _ => (hell.2.2 x).2.1)
  obtain ⟨C, hC⟩ := (hphi.2.1.isCompact_range hphi.1.continuous).isBounded.exists_norm_le
  exact MemLp.of_bound hphi.1.continuous.aestronglyMeasurable C (ae_of_all _ fun x => hC (phi x) (Set.mem_range_self x))

/-- Finite spectral energies for a spatial test use its actual weighted
Fourier coefficients and are bounded by its initial weighted energy. -/
theorem c16_spatial_test_finite_spectral_energy {d : ℕ}
    {rho : EinsteinRelation.Vec d → ℝ} {alpha : EinsteinRelation.Vec d → EinsteinRelation.Mat d}
    {R kappa : ℝ} (hR : 0 < R) (hkappa : 0 < kappa)
    (hell : External.Source.GMP.IsUniformlyElliptic kappa rho alpha)
    (s : External.Source.GMP.DirichletSpectralResolution rho alpha R)
    (phi : EinsteinRelation.Vec d → ℝ)
    (hphi : EinsteinRelation.IsSpatialTest (External.Source.GMP.sourceBall 0 R) phi)
    (I : Finset ℕ) (T : ℝ) :
    let B := External.Source.GMP.sourceBall (0 : EinsteinRelation.Vec d) R
    let a := fun n => ∫ x in B, rho x * s.eigenfunction n x * phi x
    IntegrableOn (fun t => ∑ n ∈ I,
      (a n) ^ 2 * (s.eigenvalue n * Real.exp (-(2 * s.eigenvalue n) * t))) (Set.Ioo 0 T) ∧
    (∫ t in Set.Ioo (0 : ℝ) T, ∑ n ∈ I,
      (a n) ^ 2 * (s.eigenvalue n * Real.exp (-(2 * s.eigenvalue n) * t))) ≤
      (1 / 2 : ℝ) * ∫ x in B, rho x * phi x ^ 2 := by
  dsimp only
  let hp := c16_spatial_test_memLp_dirichlet hR hell phi hphi
  have hc (n : ℕ) : inner ℝ ((s.square_integrable n).toLp (s.eigenfunction n)) (hp.toLp phi) =
      ∫ x in External.Source.GMP.sourceBall (0 : EinsteinRelation.Vec d) R,
        rho x * s.eigenfunction n x * phi x :=
    Blueprint.TubeProbability.DimensionLift.dirichletVolume_inner_eq_native hkappa hell R _ _ _ _
      (s.square_integrable n).coeFn_toLp hp.coeFn_toLp
  simpa only [hc] using c16_dirichlet_finite_modes_weighted_energy hkappa hell s phi hp I T

end EinsteinFull.Calculus
