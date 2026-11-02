import EinsteinFull.Calculus.SbxBLocalMassApproximateIdentityR14
import EinsteinFull.Calculus.SbxBSpectralRowSubmarkovR14
import EinsteinFull.Calculus.SbxBNativeSurvivalMassR05
import EinsteinFull.Calculus.SbxBSpectralCutoffMassAtZeroR14
import EinsteinFull.Calculus.SbxBContinuousDensityColumnDeltaR14

open MeasureTheory Filter EinsteinRelation EinsteinFull.External.Source.GMP
open EinsteinFull.Blueprint.TubeProbability EinsteinFull.Blueprint.SbxS3UniformCrossHeat
open scoped Topology

namespace EinsteinFull.Calculus

/-- The scalar cutoff-preservation assertion for the actual weighted spectral row. -/
def br14SpectralCutoffPreservation {d : ℕ} {ρ : Vec d → ℝ}
    {α : Vec d → Mat d} {R : ℝ} (s : DirichletSpectralResolution ρ α R) : Prop :=
  ∀ (x : Vec d) (r : ℝ), 0 < r → sourceBall x (2*r) ⊆ sourceBall 0 R →
    ∀ φ : Vec d → ℝ, IsSpatialTest (sourceBall 0 R) φ →
      tsupport φ ⊆ sourceBall x (2*r) →
      (∀ z, 0 ≤ φ z ∧ φ z ≤ 1) →
      (∀ z ∈ sourceBall x r, φ z = 1) →
      (∀ z, euclideanSq (fun i => fderiv ℝ φ z (unitVector i)) ≤ 1024 / r^2) →
      Tendsto (fun t : ℝ => ∫ y, (∑' n, Real.exp (-s.eigenvalue n*t) *
        s.eigenfunction n x * s.eigenfunction n y) * φ y ∂dirichletVolume ρ R)
        (𝓝[>] 0) (𝓝 1)

/-- Cutoff preservation yields the initial spectral action on compact continuous tests. -/
theorem br14_spectral_compact_test_initial_delta {d : ℕ} (hd : 2 ≤ d)
    {κ R : ℝ} (hκ : 0 < κ) (hR : 0 < R)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (hell : IsUniformlyElliptic κ ρ α)
    (s : DirichletSpectralResolution ρ α R) (hcut : br14SpectralCutoffPreservation s)
    (x : Vec d) (hx : x ∈ sourceBall 0 R) (f : Vec d → ℝ)
    (hf : Continuous f) (hfc : HasCompactSupport f) :
    Tendsto (fun t : ℝ => ∫ y, (∑' n, Real.exp (-s.eigenvalue n*t) *
      s.eigenfunction n x * s.eigenfunction n y) * f y ∂dirichletVolume ρ R)
      (𝓝[>] 0) (𝓝 (f x)) := by
  classical
  let U : Set (Vec d) := sourceBall 0 R
  let μ : Measure (Vec d) := volume.restrict U
  let k : ℝ → Vec d → ℝ := fun t y => ρ y * ∑' n,
    Real.exp (-s.eigenvalue n*t) * s.eigenfunction n x * s.eigenfunction n y
  let q : ℝ → Vec d → ℝ := fun t => U.indicator (k t)
  have hU : MeasurableSet U := (dirichletBall (d := d) R).isOpen.measurableSet
  have haeq (t : ℝ) : q t =ᵐ[μ] k t := by
    filter_upwards [ae_restrict_mem hU] with y hy
    simp [q, hy]
  have hk (t : ℝ) (ht : 0 < t) := br14_native_spectral_row_submarkov hd hκ hR hell s t ht x hx
  have hqi (t : ℝ) (ht : 0 < t) : Integrable (q t) μ := (hk t ht).2.1.congr (haeq t).symm
  have hqn (t : ℝ) (ht : 0 < t) (y : Vec d) : 0 ≤ q t y := by
    by_cases hy : y ∈ U
    · simpa [q, hy, k] using (hk t ht).1 y hy
    · simp [q, hy]
  have hmass (t : ℝ) (ht : 0 < t) : (∫ y, q t y ∂μ) ≤ 1 := by
    rw [integral_congr_ae (haeq t)]
    exact (hk t ht).2.2.2
  have hweighted (t : ℝ) (g : Vec d → ℝ) :
      (∫ y, (∑' n, Real.exp (-s.eigenvalue n*t) * s.eigenfunction n x *
        s.eigenfunction n y) * g y ∂dirichletVolume ρ R) =
      ∫ y, k t y * g y ∂μ := by
    rw [← b_native_weighted_cutoff_eq hκ hell (fun τ _ y => k τ y) g t x]
    apply integral_congr_ae
    filter_upwards [] with y
    dsimp only [k]
    have hρ : ρ y ≠ 0 := ne_of_gt (hκ.trans_le (hell.2.2 y).1)
    rw [mul_div_cancel_left₀ _ hρ]
  have hnorm (y : Vec d) : ‖y‖ ≤ euclideanNorm y := by
    apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr
    intro i
    apply Real.le_sqrt_of_sq_le
    rw [Real.norm_eq_abs, sq_abs]
    change y i ^ 2 ≤ ∑ j : Fin d, y j * y j
    simpa only [pow_two] using (Finset.single_le_sum (fun j _ => mul_self_nonneg (y j)) (Finset.mem_univ i))
  have hlocal (a : ℝ) (ha : 0 < a) : Tendsto
      (fun t : ℝ => ∫ y in Metric.ball x a, q t y ∂μ) (𝓝[>] 0) (𝓝 1) := by
    obtain ⟨δ, hδ, hδsub⟩ := Metric.isOpen_iff.mp (dirichletBall (d := d) R).isOpen x hx
    let r : ℝ := min a δ / 4
    have hr : 0 < r := by dsimp [r]; positivity
    have hsmalla : 2*r < a := by dsimp [r]; have := min_le_left a δ; linarith
    have hsmallδ : 2*r < δ := by dsimp [r]; have := min_le_right a δ; linarith
    have hmetric (y : Vec d) (hy : y ∈ sourceBall x (2*r)) : dist y x < 2*r := by
      rw [dist_eq_norm]
      exact lt_of_le_of_lt (hnorm (y-x)) hy
    have hinside : sourceBall x (2*r) ⊆ sourceBall 0 R := by
      intro y hy
      exact hδsub (Metric.mem_ball.mpr ((hmetric y hy).trans hsmallδ))
    obtain ⟨φ, hφ, hsupp, hbounds, hplateau, hgrad⟩ := b_interior_ball_cutoff x hr hinside
    have hlim := hcut x r hr hinside φ hφ hsupp hbounds hplateau hgrad
    have hlim' : Tendsto (fun t : ℝ => ∫ y, q t y * φ y ∂μ) (𝓝[>] 0) (𝓝 1) := by
      apply hlim.congr'
      filter_upwards [] with t
      calc
        _ = ∫ y, k t y * φ y ∂μ := hweighted t φ
        _ = ∫ y, q t y * φ y ∂μ := by
          apply integral_congr_ae
          filter_upwards [haeq t] with y hy
          rw [hy]
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlim' tendsto_const_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      have hi : Integrable (fun y => q t y * φ y) μ :=
        (hqi t ht).mul_bdd hφ.1.continuous.aestronglyMeasurable
          (ae_of_all _ fun y => by simpa [Real.norm_eq_abs, abs_of_nonneg (hbounds y).1] using (hbounds y).2)
      have hj : Integrable ((Metric.ball x a).indicator (q t)) μ := (hqi t ht).indicator measurableSet_ball
      rw [← integral_indicator measurableSet_ball]
      apply integral_mono_ae hi hj
      filter_upwards [] with y
      by_cases hy : y ∈ Metric.ball x a
      · simp only [Set.indicator_of_mem hy]
        exact mul_le_of_le_one_right (hqn t ht y) (hbounds y).2
      · have hz : φ y = 0 := image_eq_zero_of_notMem_tsupport (fun hy' =>
          hy (Metric.mem_ball.mpr ((hmetric y (hsupp hy')).trans hsmalla)))
        simp [hy, hz]
    · filter_upwards [self_mem_nhdsWithin] with t ht
      rw [← integral_indicator measurableSet_ball]
      exact le_trans (integral_mono_ae ((hqi t ht).indicator measurableSet_ball) (hqi t ht)
        (ae_of_all _ fun y => by
          by_cases hy : y ∈ Metric.ball x a
          · simp [hy]
          · simpa [hy] using hqn t ht y)) (hmass t ht)
  obtain ⟨B, hB⟩ := (hfc.isCompact_range hf).isBounded.exists_norm_le
  have hfb (y : Vec d) : |f y| ≤ B := by
    simpa [Real.norm_eq_abs] using hB (f y) (Set.mem_range_self y)
  have hlim : Tendsto (fun t : ℝ => ∫ y, q t y * f y ∂μ)
      (𝓝[>] 0) (𝓝 (f x)) := by
    first
    | exact br14_local_mass_approximate_identity μ q x f hf B hfb hqi hqn hmass
        1 (by norm_num) (fun r hr _ => hlocal r hr)
    | exact br14_local_mass_approximate_identity μ q x f hf B hfb hqi hqn hmass hlocal
  apply hlim.congr'
  filter_upwards [] with t
  calc
    _ = ∫ y, k t y * f y ∂μ := by
      apply integral_congr_ae
      filter_upwards [haeq t] with y hy
      rw [hy]
    _ = _ := (hweighted t f).symm

/-- The exponential spacetime defect estimate supplies cutoff preservation. -/
theorem br14_spectral_cutoff_preservation_of_exponential_defect
    (d : ℕ) (hd : 2 ≤ d) (κ : ℝ) (hκ : 0 < κ)
    (hDecay : ∃ D : ℝ, 0 < D ∧
      ∀ (R : ℝ), 0 < R → ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
        IsUniformlyElliptic κ ρ α →
      ∀ (s : DirichletSpectralResolution ρ α R) (x : Vec d) (r : ℝ), 0 < r →
        sourceBall x (2*r) ⊆ sourceBall 0 R →
      ∀ φ : Vec d → ℝ, IsSpatialTest (sourceBall 0 R) φ →
        tsupport φ ⊆ sourceBall x (2*r) →
        (∀ z, 0 ≤ φ z ∧ φ z ≤ 1) →
        (∀ z ∈ sourceBall x r, φ z = 1) →
        (∀ z, euclideanSq (fun i => fderiv ℝ φ z (unitVector i)) ≤ 1024 / r^2) →
      ∀ T : ℝ, 0 < T → T ≤ r^2 →
        (∫ z in Set.Ioo (0 : ℝ) T ×ˢ sourceBall x (r/2),
          |(∫ y, (∑' n, Real.exp (-s.eigenvalue n * z.1) *
              s.eigenfunction n z.2 * s.eigenfunction n y) * φ y ∂dirichletVolume ρ R) - 1| ^ 2)
          ≤ D * T * r^d * Real.exp (-(r^2 / (D*T))))
    {R : ℝ} (hR : 0 < R) {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (hell : IsUniformlyElliptic κ ρ α) (s : DirichletSpectralResolution ρ α R) :
    br14SpectralCutoffPreservation s := by
  intro x r hr hinside φ hφ hsupp hbounds hplateau hgrad
  exact br14_spectral_cutoff_initial_one d hd κ hκ hDecay hR hell s x r hr
    hinside φ hφ hsupp hbounds hplateau hgrad

/-- The compact-test trace required by the native column conversion. -/
theorem br14_weighted_row_initial_trace_of_cutoff {d : ℕ} (hd : 2 ≤ d)
    {κ R : ℝ} (hκ : 0 < κ) (hR : 0 < R)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (hell : IsUniformlyElliptic κ ρ α)
    (s : DirichletSpectralResolution ρ α R) (hcut : br14SpectralCutoffPreservation s) :
    br14WeightedRowInitialTrace s := by
  intro x hx f hf hfc _
  exact br14_spectral_compact_test_initial_delta hd hκ hR hell s hcut x hx f hf hfc

#print axioms br14_spectral_cutoff_preservation_of_exponential_defect
#print axioms br14_weighted_row_initial_trace_of_cutoff

#print axioms br14_spectral_compact_test_initial_delta

end EinsteinFull.Calculus
