import EinsteinFull.Calculus.C17TubeGaussianSecondMoment
import EinsteinFull.Calculus.C12TubeGaussianIntegratedTail

open EinsteinRelation MeasureTheory Filter EinsteinFull.External.Source.GMP
open scoped Topology
noncomputable section
namespace EinsteinFull.Calculus

private theorem c17_sourceBall_measurable {d : ℕ} (x : Vec d) (r : ℝ) :
    MeasurableSet (sourceBall x r) := by
  have hc : Continuous (fun z : Vec d => euclideanNorm z) := by
    unfold euclideanNorm euclideanSq dot
    exact Real.continuous_sqrt.comp
      (continuous_finset_sum _ fun i _ => (continuous_apply i).mul (continuous_apply i))
  exact (isOpen_lt (hc.comp (continuous_id.sub continuous_const)) continuous_const).measurableSet

theorem c17_moment_tail_bound {d : ℕ} (μ : Measure (Vec d))
    (x : Vec d) (r M : ℝ) (hr : 0 < r) (f : Vec d → ℝ)
    (hf : Integrable f μ) (hf0 : ∀ᵐ y ∂μ, 0 ≤ f y)
    (hfm : Integrable (fun y => f y * euclideanSq (y-x)) μ)
    (hM : (∫ y, f y * euclideanSq (y-x) ∂μ) ≤ M) :
    (∫ y in (sourceBall x r)ᶜ, f y ∂μ) ≤ M / r^2 := by
  have hs := c17_sourceBall_measurable x r
  have hr2 : 0 < r^2 := sq_pos_of_pos hr
  have hpoint : ∀ᵐ y ∂μ.restrict (sourceBall x r)ᶜ,
      r^2 * f y ≤ f y * euclideanSq (y-x) := by
    filter_upwards [ae_restrict_mem hs.compl, ae_restrict_of_ae hf0] with y hy hfy
    have hd : r ≤ euclideanNorm (y-x) := le_of_not_gt hy
    have hn : 0 ≤ euclideanNorm (y-x) := Real.sqrt_nonneg _
    have hsq : r^2 ≤ euclideanSq (y-x) := by
      rw [TimeChange.euclideanSq_eq_sq_euclideanNorm]
      nlinarith
    nlinarith
  have hi := integral_mono_ae (hf.const_mul (r^2)).integrableOn hfm.integrableOn hpoint
  rw [integral_const_mul] at hi
  have hnonneg : ∀ᵐ y ∂μ, 0 ≤ f y * euclideanSq (y-x) := by
    filter_upwards [hf0] with y hy
    apply mul_nonneg hy
    simp only [euclideanSq, dot]
    exact Finset.sum_nonneg (fun i _ => mul_self_nonneg _)
  have hrest := integral_mono_measure (Measure.restrict_le_self :
    μ.restrict (sourceBall x r)ᶜ ≤ μ) hnonneg hfm
  apply (le_div_iff₀ hr2).2
  nlinarith

theorem c17_moment_to_interior_mass {d : ℕ} (μ : Measure (Vec d))
    (x : Vec d) (r m M : ℝ) (hr : 0 < r) (f : Vec d → ℝ)
    (hf : Integrable f μ) (hf0 : ∀ᵐ y ∂μ, 0 ≤ f y)
    (hfm : Integrable (fun y => f y * euclideanSq (y-x)) μ)
    (hm : m ≤ ∫ y, f y ∂μ)
    (hM : (∫ y, f y * euclideanSq (y-x) ∂μ) ≤ M) :
    m - M/r^2 ≤ ∫ y in sourceBall x r, f y ∂μ := by
  have ht := c17_moment_tail_bound μ x r M hr f hf hf0 hfm hM
  have hsplit := integral_add_compl (c17_sourceBall_measurable x r) hf
  linarith

/-- The native spectral row has interior mass controlled by its Gaussian second moment.
The total-row lower bound is an explicit input. -/
theorem c17_native_spectral_interior_mass (d : ℕ) (hd : 2 ≤ d) :
    ∃ D : ℝ, 0 < D ∧ ∀ (κ R : ℝ) (hκ : 0 < κ)
      (ρ : Vec d → ℝ) (α : Vec d → Mat d)
      (h : IsUniformlyElliptic κ ρ α)
      (s : DirichletSpectralResolution ρ α R)
      (C t : ℝ), 0 < C → 0 < t → ∀ (x : Vec d) (r m : ℝ), 0 < r →
      let k := (sourceBall (0 : Vec d) R).indicator
        (fun y => ∑' n, Real.exp (-s.eigenvalue n * t) *
          s.eigenfunction n x * s.eigenfunction n y)
      Measurable k →
      (∀ y, 0 ≤ k y ∧ k y ≤ C * Real.rpow t (-(d : ℝ)/2) *
        Real.exp (-euclideanSq (y-x)/(C*t))) →
      m ≤ ∫ y, k y * ρ y →
      m - (D * κ⁻¹ * Real.rpow C ((d : ℝ)/2+2) * t)/r^2 ≤
        ∫ y in sourceBall x r, k y * ρ y := by
  obtain ⟨D, hD, hmoment⟩ := c17_native_spectral_row_second_moment d hd
  refine ⟨D, hD, ?_⟩
  intro κ R hκ ρ α h s C t hC ht x r m hr k hk hkb hm
  obtain ⟨hmi, hmb⟩ := hmoment κ R hκ ρ α h s C t hC ht x hk hkb
  have hρ : ∀ y, 0 ≤ ρ y ∧ ρ y ≤ κ⁻¹ :=
    fun y => ⟨le_trans hκ.le (h.2.2 y).1, (h.2.2 y).2.1⟩
  have hi : Integrable (fun y => k y * ρ y) := by
    apply ((c12_translated_gaussian_euclidean (mul_pos hC ht) x).1.const_mul
      (C * Real.rpow t (-(d : ℝ)/2) * κ⁻¹)).mono'
      (hk.mul h.1).aestronglyMeasurable
    filter_upwards [] with y
    simp only [Pi.mul_apply, Real.norm_eq_abs]
    rw [abs_of_nonneg (mul_nonneg (hkb y).1 (hρ y).1)]
    calc
      k y * ρ y ≤ (C * Real.rpow t (-(d : ℝ)/2) *
          Real.exp (-euclideanSq (y-x)/(C*t))) * κ⁻¹ :=
        mul_le_mul (hkb y).2 (hρ y).2 (hρ y).1
          (mul_nonneg (mul_nonneg hC.le (Real.rpow_nonneg ht.le _)) (Real.exp_pos _).le)
      _ = _ := by ring
  have hn : ∀ᵐ y, 0 ≤ k y * ρ y :=
    ae_of_all _ (fun y => mul_nonneg (hkb y).1 (hρ y).1)
  apply c17_moment_to_interior_mass volume x r m _ hr (fun y => k y * ρ y) hi hn
  · convert hmi using 1 <;> ext y <;> ring
  · exact hm
  · convert hmb using 1 <;> congr 1 <;> ext y <;> ring

end EinsteinFull.Calculus
