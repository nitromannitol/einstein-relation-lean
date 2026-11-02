import EinsteinFull.Calculus.C16TubeCutoffQuantitativeTrace

open MeasureTheory Filter EinsteinRelation EinsteinFull.External.Source.GMP
open scoped NNReal
open EinsteinFull.Blueprint.TubeProbability EinsteinFull.Blueprint.SbxS3UniformCrossHeat

namespace EinsteinFull.Calculus

/-- Converting the native weighted spectral row to the Lebesgue kernel
convention is valid at every pole. This uses no fundamental solution. -/
theorem br13_native_spectral_kernel_integral {d : ℕ} {κ R : ℝ}
    (hκ : 0 < κ) (hR : 0 < R) {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (hell : IsUniformlyElliptic κ ρ α)
    (s : DirichletSpectralResolution ρ α R)
    (φ : Vec d → ℝ) (hφ : IsSpatialTest (sourceBall 0 R) φ)
    (t : ℝ≥0) (x : Vec d) :
    (∫ y in sourceBall (0 : Vec d) R,
      (ρ y * ∑' n, Real.exp (-s.eigenvalue n * (t : ℝ)) *
        s.eigenfunction n x * s.eigenfunction n y) * φ y) =
    ∫ y, (∑' n, Real.exp (-s.eigenvalue n * (t : ℝ)) *
      s.eigenfunction n x * s.eigenfunction n y) *
      (c16_spatial_test_memLp_dirichlet hR hell φ hφ).toLp φ y
      ∂dirichletVolume ρ R := by
  let hp := c16_spatial_test_memLp_dirichlet hR hell φ hφ
  have hi : (∫ y, (∑' n, Real.exp (-s.eigenvalue n * (t : ℝ)) *
      s.eigenfunction n x * s.eigenfunction n y) * hp.toLp φ y
      ∂dirichletVolume ρ R) =
      ∫ y, (∑' n, Real.exp (-s.eigenvalue n * (t : ℝ)) *
        s.eigenfunction n x * s.eigenfunction n y) * φ y ∂dirichletVolume ρ R := by
    apply integral_congr_ae
    filter_upwards [hp.coeFn_toLp] with y hy
    rw [hy]
  rw [hi]
  change _ = ∫ y, (∑' n, Real.exp (-s.eigenvalue n * (t : ℝ)) *
    s.eigenfunction n x * s.eigenfunction n y) * φ y ∂(volume.restrict
      (sourceBall (0 : Vec d) R)).withDensity (fun y => ENNReal.ofReal (ρ y))
  rw [integral_withDensity_eq_integral_toReal_smul hell.1.ennreal_ofReal
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards [] with y
  simp only [ENNReal.toReal_ofReal (hκ.le.trans (hell.2.2 y).1), smul_eq_mul]
  ring

/-- The preceding every-pole integral represents the actual spectral heat
operator almost everywhere; its value at a prescribed pole is a representative. -/
theorem br13_native_kernel_integral_represents_heat {d : ℕ} {κ R : ℝ}
    (hκ : 0 < κ) (hR : 0 < R) {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (hell : IsUniformlyElliptic κ ρ α)
    (s : DirichletSpectralResolution ρ α R)
    (hspec : ∀ t : ℝ, 0 < t → ∀ x ∈ sourceBall (0 : Vec d) R,
      ∀ y ∈ sourceBall (0 : Vec d) R,
        Summable (fun n => Real.exp (-s.eigenvalue n * t) *
          s.eigenfunction n x * s.eigenfunction n y))
    (φ : Vec d → ℝ) (hφ : IsSpatialTest (sourceBall 0 R) φ)
    (t : ℝ≥0) (ht : 0 < (t : ℝ)) :
    (fun x => SpectralHeat.heatOperator (spectralHeatBasis s) s.eigenvalue
      (fun n => (s.eigenvalue_pos n).le) t
      ((c16_spatial_test_memLp_dirichlet hR hell φ hφ).toLp φ) x) =ᵐ[dirichletVolume ρ R]
    fun x => ∫ y in sourceBall (0 : Vec d) R,
      (ρ y * ∑' n, Real.exp (-s.eigenvalue n * (t : ℝ)) *
        s.eigenfunction n x * s.eigenfunction n y) * φ y := by
  filter_upwards [c16_supplied_spectral_heat_operator_ae_kernel_action s hspec t ht
    ((c16_spatial_test_memLp_dirichlet hR hell φ hφ).toLp φ)] with x hx
  exact hx.trans (br13_native_spectral_kernel_integral hκ hR hell s φ hφ t x).symm

/-- A uniformly absolutely summable spectral row may be integrated term by
term against a compactly supported test. The bounds concern the modes alone. -/
theorem br13_native_kernel_integral_spectral_series {d : ℕ} {κ R : ℝ}
    (hκ : 0 < κ) (hR : 0 < R) {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (hell : IsUniformlyElliptic κ ρ α)
    (s : DirichletSpectralResolution ρ α R)
    (φ : Vec d → ℝ) (hφ : IsSpatialTest (sourceBall 0 R) φ)
    (t : ℝ≥0) (_ht : 0 < (t : ℝ)) (x : Vec d) (_hx : x ∈ sourceBall 0 R)
    (hspec : ∀ y ∈ sourceBall (0 : Vec d) R,
      Summable (fun n => Real.exp (-s.eigenvalue n * (t : ℝ)) *
        s.eigenfunction n x * s.eigenfunction n y))
    (a : ℕ → ℝ) (ha : Summable a)
    (hbound : ∀ n y, y ∈ tsupport φ →
      |Real.exp (-s.eigenvalue n * (t : ℝ)) * s.eigenfunction n x *
        s.eigenfunction n y| ≤ a n) :
    (∫ y in sourceBall (0 : Vec d) R,
      (ρ y * ∑' n, Real.exp (-s.eigenvalue n * (t : ℝ)) *
        s.eigenfunction n x * s.eigenfunction n y) * φ y) =
    ∑' n, (Real.exp (-s.eigenvalue n * (t : ℝ)) * s.eigenfunction n x) *
      (spectralHeatBasis s).repr
        ((c16_spatial_test_memLp_dirichlet hR hell φ hφ).toLp φ) n := by
  let μ := dirichletVolume ρ R
  let hp := c16_spatial_test_memLp_dirichlet hR hell φ hφ
  letI : IsFiniteMeasure μ := Blueprint.TubeProbability.dirichletVolume_isFinite
    ρ R hR κ⁻¹ (fun y _ => (hell.2.2 y).2.1)
  have hφint : Integrable φ μ := hp.integrable (by norm_num)
  let F : ℕ → Vec d → ℝ := fun n y =>
    Real.exp (-s.eigenvalue n * (t : ℝ)) * s.eigenfunction n x *
      s.eigenfunction n y * φ y
  have hmeas (n : ℕ) : AEStronglyMeasurable (F n) μ := by
    exact (((s.square_integrable n).aestronglyMeasurable.const_mul _).mul hp.aestronglyMeasurable)
  have hmajor (n : ℕ) : ∀ᵐ y ∂μ, ‖F n y‖ ≤ a n * |φ y| := by
    apply ae_of_all
    intro y
    by_cases hy : φ y = 0
    · simp [F, hy]
    · have hy' : y ∈ tsupport φ := subset_closure hy
      have hh := mul_le_mul_of_nonneg_right (hbound n y hy') (abs_nonneg (φ y))
      simpa only [F, Real.norm_eq_abs, abs_mul] using hh
  have hsum : ∀ᵐ y ∂μ, Summable (fun n => a n * |φ y|) :=
    ae_of_all _ (fun y => ha.mul_right _)
  have hint : Integrable (fun y => ∑' n, a n * |φ y|) μ := by
    have heq : (fun y => ∑' n, a n * |φ y|) = fun y => (∑' n, a n) * |φ y| := by
      funext y
      exact tsum_mul_right
    rw [heq]
    exact hφint.abs.const_mul _
  have hball : ∀ᵐ y ∂μ, y ∈ sourceBall (0 : Vec d) R := by
    have hb : MeasurableSet (sourceBall (0 : Vec d) R) :=
      (dirichletBall (d := d) R).isOpen.measurableSet
    exact (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem hb)
  have hlim : ∀ᵐ y ∂μ, HasSum (fun n => F n y)
      ((∑' n, Real.exp (-s.eigenvalue n * (t : ℝ)) *
        s.eigenfunction n x * s.eigenfunction n y) * φ y) := by
    filter_upwards [hball] with y hy
    exact (hspec y hy).hasSum.mul_right (φ y)
  have hinterchange := hasSum_integral_of_dominated_convergence
    (fun n y => a n * |φ y|) hmeas hmajor hsum hint hlim
  rw [br13_native_spectral_kernel_integral hκ hR hell s φ hφ t x]
  have heq : (∫ y, (∑' n, Real.exp (-s.eigenvalue n * (t : ℝ)) *
      s.eigenfunction n x * s.eigenfunction n y) * hp.toLp φ y ∂μ) =
      ∫ y, (∑' n, Real.exp (-s.eigenvalue n * (t : ℝ)) *
        s.eigenfunction n x * s.eigenfunction n y) * φ y ∂μ := by
    apply integral_congr_ae
    filter_upwards [hp.coeFn_toLp] with y hy
    rw [hy]
  rw [heq, ← hinterchange.tsum_eq]
  apply tsum_congr
  intro n
  have hb : spectralHeatBasis s n = (s.square_integrable n).toLp (s.eigenfunction n) := by
    exact congrFun (HilbertBasis.coe_mk s.orthonormal
      (le_of_eq (Submodule.dense_iff_topologicalClosure_eq_top.mp s.complete).symm)) n
  rw [HilbertBasis.repr_apply_apply, hb, MeasureTheory.L2.inner_def]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [(s.square_integrable n).coeFn_toLp, hp.coeFn_toLp] with y hy hp'
  simp only [F, RCLike.inner_apply, conj_trivial, hy, hp']
  ring

/-- A spectral row whose absolute partial sums are uniformly bounded on the
test support may be integrated term by term. -/
theorem br13_native_kernel_integral_spectral_series_of_bounded_sums {d : ℕ} {κ R : ℝ}
    (hκ : 0 < κ) (hR : 0 < R) {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (hell : IsUniformlyElliptic κ ρ α)
    (s : DirichletSpectralResolution ρ α R)
    (φ : Vec d → ℝ) (hφ : IsSpatialTest (sourceBall 0 R) φ)
    (t : ℝ≥0) (_ht : 0 < (t : ℝ)) (x : Vec d) (_hx : x ∈ sourceBall 0 R)
    (hspec : ∀ y ∈ sourceBall (0 : Vec d) R,
      Summable (fun n => Real.exp (-s.eigenvalue n * (t : ℝ)) *
        s.eigenfunction n x * s.eigenfunction n y))
    (C : ℝ)
    (hbound : ∀ N y, y ∈ tsupport φ →
      (∑ n ∈ Finset.range N, |Real.exp (-s.eigenvalue n * (t : ℝ)) *
        s.eigenfunction n x * s.eigenfunction n y|) ≤ C) :
    (∫ y in sourceBall (0 : Vec d) R,
      (ρ y * ∑' n, Real.exp (-s.eigenvalue n * (t : ℝ)) *
        s.eigenfunction n x * s.eigenfunction n y) * φ y) =
    ∑' n, (Real.exp (-s.eigenvalue n * (t : ℝ)) * s.eigenfunction n x) *
      (spectralHeatBasis s).repr
        ((c16_spatial_test_memLp_dirichlet hR hell φ hφ).toLp φ) n := by
  let μ := dirichletVolume ρ R
  let hp := c16_spatial_test_memLp_dirichlet hR hell φ hφ
  letI : IsFiniteMeasure μ := Blueprint.TubeProbability.dirichletVolume_isFinite
    ρ R hR κ⁻¹ (fun y _ => (hell.2.2 y).2.1)
  have hφint : Integrable φ μ := hp.integrable (by norm_num)
  let F : ℕ → Vec d → ℝ := fun n y =>
    Real.exp (-s.eigenvalue n * (t : ℝ)) * s.eigenfunction n x *
      s.eigenfunction n y * φ y
  have hmeas (n : ℕ) : AEStronglyMeasurable (F n) μ := by
    exact (((s.square_integrable n).aestronglyMeasurable.const_mul _).mul hp.aestronglyMeasurable)
  have hmajor (n : ℕ) : ∀ᵐ y ∂μ, ‖F n y‖ ≤ ‖F n y‖ := ae_of_all _ (fun _ => le_rfl)
  have hsum : ∀ᵐ y ∂μ, Summable (fun n => ‖F n y‖) := by
    apply ae_of_all
    intro y
    by_cases hy : φ y = 0
    · simp [F, hy]
    · have hy' : y ∈ tsupport φ := subset_closure hy
      apply summable_of_sum_range_le (fun _ => norm_nonneg _) (c := C * |φ y|)
      intro N
      calc
        ∑ n ∈ Finset.range N, ‖F n y‖ =
            (∑ n ∈ Finset.range N, |Real.exp (-s.eigenvalue n * (t : ℝ)) *
              s.eigenfunction n x * s.eigenfunction n y|) * |φ y| := by
                simp [F, Real.norm_eq_abs, abs_mul, Finset.sum_mul]
        _ ≤ C * |φ y| := mul_le_mul_of_nonneg_right (hbound N y hy') (abs_nonneg _)
  have hmeas_sum : AEStronglyMeasurable (fun y => ∑' n, ‖F n y‖) μ := by
    apply aestronglyMeasurable_of_tendsto_ae (atTop : Filter ℕ)
      (fun N => Finset.aestronglyMeasurable_fun_sum _ (fun n _ => (hmeas n).norm))
    filter_upwards [hsum] with y hy
    exact hy.tendsto_sum_tsum_nat
  have hint : Integrable (fun y => ∑' n, ‖F n y‖) μ := by
    apply (hφint.abs.const_mul C).mono' hmeas_sum
    filter_upwards [hsum] with y hy
    by_cases hyφ : φ y = 0
    · simp [F, hyφ]
    · have hy' : y ∈ tsupport φ := subset_closure hyφ
      have hbound' : ∀ N, (∑ n ∈ Finset.range N, ‖F n y‖) ≤ C * |φ y| := by
        intro N
        calc
          ∑ n ∈ Finset.range N, ‖F n y‖ =
              (∑ n ∈ Finset.range N, |Real.exp (-s.eigenvalue n * (t : ℝ)) *
                s.eigenfunction n x * s.eigenfunction n y|) * |φ y| := by
                  simp [F, Real.norm_eq_abs, abs_mul, Finset.sum_mul]
          _ ≤ C * |φ y| := mul_le_mul_of_nonneg_right (hbound N y hy') (abs_nonneg _)
      have hs := hy.tsum_le_of_sum_range_le hbound'
      have hn : 0 ≤ ∑' n, ‖F n y‖ := tsum_nonneg (fun n => norm_nonneg (F n y))
      rw [Real.norm_eq_abs, abs_of_nonneg hn]
      exact hs
  have hball : ∀ᵐ y ∂μ, y ∈ sourceBall (0 : Vec d) R := by
    have hb : MeasurableSet (sourceBall (0 : Vec d) R) :=
      (dirichletBall (d := d) R).isOpen.measurableSet
    exact (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem hb)
  have hlim : ∀ᵐ y ∂μ, HasSum (fun n => F n y)
      ((∑' n, Real.exp (-s.eigenvalue n * (t : ℝ)) *
        s.eigenfunction n x * s.eigenfunction n y) * φ y) := by
    filter_upwards [hball] with y hy
    exact (hspec y hy).hasSum.mul_right (φ y)
  have hinterchange := hasSum_integral_of_dominated_convergence
    (fun n y => ‖F n y‖) hmeas hmajor hsum hint hlim
  rw [br13_native_spectral_kernel_integral hκ hR hell s φ hφ t x]
  have heq : (∫ y, (∑' n, Real.exp (-s.eigenvalue n * (t : ℝ)) *
      s.eigenfunction n x * s.eigenfunction n y) * hp.toLp φ y ∂μ) =
      ∫ y, (∑' n, Real.exp (-s.eigenvalue n * (t : ℝ)) *
        s.eigenfunction n x * s.eigenfunction n y) * φ y ∂μ := by
    apply integral_congr_ae
    filter_upwards [hp.coeFn_toLp] with y hy
    rw [hy]
  rw [heq, ← hinterchange.tsum_eq]
  apply tsum_congr
  intro n
  have hb : spectralHeatBasis s n = (s.square_integrable n).toLp (s.eigenfunction n) := by
    exact congrFun (HilbertBasis.coe_mk s.orthonormal
      (le_of_eq (Submodule.dense_iff_topologicalClosure_eq_top.mp s.complete).symm)) n
  rw [HilbertBasis.repr_apply_apply, hb, MeasureTheory.L2.inner_def]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [(s.square_integrable n).coeFn_toLp, hp.coeFn_toLp] with y hy hp'
  simp only [F, RCLike.inner_apply, conj_trivial, hy, hp']
  ring

/-- The pointwise coefficient series is a representative of the actual
spectral heat action when each interior row has a summable majorant on the
support of the test. -/
theorem br13_native_spectral_series_represents_heat {d : ℕ} {κ R : ℝ}
    (hκ : 0 < κ) (hR : 0 < R) {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (hell : IsUniformlyElliptic κ ρ α)
    (s : DirichletSpectralResolution ρ α R)
    (hspec : ∀ t : ℝ, 0 < t → ∀ x ∈ sourceBall (0 : Vec d) R,
      ∀ y ∈ sourceBall (0 : Vec d) R,
        Summable (fun n => Real.exp (-s.eigenvalue n * t) *
          s.eigenfunction n x * s.eigenfunction n y))
    (φ : Vec d → ℝ) (hφ : IsSpatialTest (sourceBall 0 R) φ)
    (t : ℝ≥0) (ht : 0 < (t : ℝ))
    (hmajor : ∀ x ∈ sourceBall (0 : Vec d) R, ∃ a : ℕ → ℝ,
      Summable a ∧ ∀ n y, y ∈ tsupport φ →
        |Real.exp (-s.eigenvalue n * (t : ℝ)) * s.eigenfunction n x *
          s.eigenfunction n y| ≤ a n) :
    (fun x => SpectralHeat.heatOperator (spectralHeatBasis s) s.eigenvalue
      (fun n => (s.eigenvalue_pos n).le) t
      ((c16_spatial_test_memLp_dirichlet hR hell φ hφ).toLp φ) x) =ᵐ[dirichletVolume ρ R]
    fun x => ∑' n, (Real.exp (-s.eigenvalue n * (t : ℝ)) * s.eigenfunction n x) *
      (spectralHeatBasis s).repr
        ((c16_spatial_test_memLp_dirichlet hR hell φ hφ).toLp φ) n := by
  have hball : ∀ᵐ x ∂dirichletVolume ρ R, x ∈ sourceBall (0 : Vec d) R := by
    have hb : MeasurableSet (sourceBall (0 : Vec d) R) :=
      (dirichletBall (d := d) R).isOpen.measurableSet
    exact (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem hb)
  filter_upwards [br13_native_kernel_integral_represents_heat hκ hR hell s hspec φ hφ t ht,
    hball] with x hx hxb
  obtain ⟨a, ha, hb⟩ := hmajor x hxb
  exact hx.trans (br13_native_kernel_integral_spectral_series hκ hR hell s φ hφ t ht x hxb
    (hspec t ht x hxb) a ha hb)

/-- The pointwise coefficient series is a representative of the actual
spectral heat action when the absolute partial sums of each interior row are bounded on the
support of the test. -/
theorem br13_native_bounded_spectral_series_represents_heat {d : ℕ} {κ R : ℝ}
    (hκ : 0 < κ) (hR : 0 < R) {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (hell : IsUniformlyElliptic κ ρ α)
    (s : DirichletSpectralResolution ρ α R)
    (hspec : ∀ t : ℝ, 0 < t → ∀ x ∈ sourceBall (0 : Vec d) R,
      ∀ y ∈ sourceBall (0 : Vec d) R,
        Summable (fun n => Real.exp (-s.eigenvalue n * t) *
          s.eigenfunction n x * s.eigenfunction n y))
    (φ : Vec d → ℝ) (hφ : IsSpatialTest (sourceBall 0 R) φ)
    (t : ℝ≥0) (ht : 0 < (t : ℝ))
    (hmajor : ∀ x ∈ sourceBall (0 : Vec d) R, ∃ C : ℝ,
      ∀ N y, y ∈ tsupport φ →
        (∑ n ∈ Finset.range N, |Real.exp (-s.eigenvalue n * (t : ℝ)) *
          s.eigenfunction n x * s.eigenfunction n y|) ≤ C) :
    (fun x => SpectralHeat.heatOperator (spectralHeatBasis s) s.eigenvalue
      (fun n => (s.eigenvalue_pos n).le) t
      ((c16_spatial_test_memLp_dirichlet hR hell φ hφ).toLp φ) x) =ᵐ[dirichletVolume ρ R]
    fun x => ∑' n, (Real.exp (-s.eigenvalue n * (t : ℝ)) * s.eigenfunction n x) *
      (spectralHeatBasis s).repr
        ((c16_spatial_test_memLp_dirichlet hR hell φ hφ).toLp φ) n := by
  have hball : ∀ᵐ x ∂dirichletVolume ρ R, x ∈ sourceBall (0 : Vec d) R := by
    have hb : MeasurableSet (sourceBall (0 : Vec d) R) :=
      (dirichletBall (d := d) R).isOpen.measurableSet
    exact (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem hb)
  filter_upwards [br13_native_kernel_integral_represents_heat hκ hR hell s hspec φ hφ t ht,
    hball] with x hx hxb
  obtain ⟨C, hC⟩ := hmajor x hxb
  exact hx.trans (br13_native_kernel_integral_spectral_series_of_bounded_sums
    hκ hR hell s φ hφ t ht x hxb (hspec t ht x hxb) C hC)

#print axioms br13_native_bounded_spectral_series_represents_heat
#print axioms br13_native_kernel_integral_spectral_series_of_bounded_sums
#print axioms br13_native_spectral_series_represents_heat
#print axioms br13_native_kernel_integral_spectral_series

#print axioms br13_native_spectral_kernel_integral
#print axioms br13_native_kernel_integral_represents_heat

end EinsteinFull.Calculus
