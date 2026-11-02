import EinsteinFull.Blueprint.Foundation.Proofs.SbxS3UniformCrossHeat

open MeasureTheory PDE Filter EinsteinFull.External.Source.GMP EinsteinRelation
open EinsteinFull.Blueprint.TubeProbability
open EinsteinFull.Blueprint.TubeProbability.DimensionLift
open EinsteinFull.Blueprint.SbxS3UniformCrossHeat
open scoped Topology NNReal

namespace EinsteinFull.Calculus

/-- The sub-Markov mass bound holds for the supplied native spectrum. -/
theorem c8_native_spectral_heat_mass_bounds {d : ℕ} (hd : 2 ≤ d)
    {κ R : ℝ} (hκ : 0 < κ) (hR : 0 < R)
    {ρ : PDE.Vec d → ℝ} {α : PDE.Vec d → EinsteinRelation.Mat d}
    (h : IsUniformlyElliptic κ ρ α)
    (s : DirichletSpectralResolution ρ α R)
    (u : ℕ → DirichletHilbertSpace (d := d) R hR)
    (hs : Tendsto s.eigenvalue atTop atTop)
    (hb : ∀ n, spectralHeatBasis s n = dirichletHilbertInclusion ρ R hR κ⁻¹
      (fun x _ => (h.2.2 x).2.1) (u n))
    (hv : ∀ n w, (∫ x in sourceBall (0 : PDE.Vec d) R,
      dot ((α x).mulVec (fun i => (u n).val (some i) x))
        (fun i => w.val (some i) x)) = s.eigenvalue n * inner ℝ
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) (u n))
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) w)) :
    ∀ (t : ℝ≥0), 0 < (t : ℝ) → ∀ x ∈ sourceBall 0 R,
      0 ≤ (∫ y, ∑' i, Real.exp (-s.eigenvalue i * (t : ℝ)) *
        s.eigenfunction i x * s.eigenfunction i y ∂dirichletVolume ρ R) ∧
      (∫ y, ∑' i, Real.exp (-s.eigenvalue i * (t : ℝ)) *
        s.eigenfunction i x * s.eigenfunction i y ∂dirichletVolume ρ R) ≤ 1 := by
  haveI : IsFiniteMeasure (dirichletVolume ρ R) :=
    dirichletVolume_isFinite ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1)
  let one : Lp ℝ 2 (dirichletVolume ρ R) := Lp.const 2 _ (1 : ℝ)
  have hone : ∀ᵐ x ∂dirichletVolume ρ R, 0 ≤ one x ∧ one x ≤ 1 := by
    filter_upwards [Lp.coeFn_const (μ := dirichletVolume ρ R) (p := 2) (c := (1 : ℝ))] with x hx
    simp only [one, Function.const_apply] at hx
    rw [hx]
    exact ⟨zero_le_one, le_rfl⟩
  intro t ht x hx
  have hm := spectral_heat_action_order_of_variational hd hκ h R hR s hs u hb hv
    t ht one hone x hx
  have he : (∫ y, (∑' i, Real.exp (-s.eigenvalue i * (t : ℝ)) *
      s.eigenfunction i x * s.eigenfunction i y) * one y ∂dirichletVolume ρ R) =
      ∫ y, ∑' i, Real.exp (-s.eigenvalue i * (t : ℝ)) *
        s.eigenfunction i x * s.eigenfunction i y ∂dirichletVolume ρ R := by
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_const (μ := dirichletVolume ρ R) (p := 2) (c := (1 : ℝ))] with y hy
    simp only [one, Function.const_apply] at hy
    rw [hy, mul_one]
  rwa [he] at hm

/-- Translate a weighted integral of a quotient to its Lebesgue form. -/
theorem c8_weighted_quotient_integral {d : ℕ} {κ R : ℝ} (hκ : 0 < κ)
    {ρ : PDE.Vec d → ℝ} {α : PDE.Vec d → EinsteinRelation.Mat d}
    (h : IsUniformlyElliptic κ ρ α) (f ψ : PDE.Vec d → ℝ) :
    (∫ x, f x * (ψ x / ρ x) ∂dirichletVolume ρ R) =
      ∫ x in sourceBall (0 : PDE.Vec d) R, f x * ψ x := by
  change (∫ x, f x * (ψ x / ρ x) ∂(volume.restrict
    (sourceBall (0 : PDE.Vec d) R)).withDensity (fun x => ENNReal.ofReal (ρ x))) = _
  rw [integral_withDensity_eq_integral_toReal_smul h.1.ennreal_ofReal
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  exact ae_of_all _ fun x => by
    dsimp only
    rw [ENNReal.toReal_ofReal (hκ.le.trans (h.2.2 x).1), smul_eq_mul]
    have hr : ρ x ≠ 0 := ne_of_gt (hκ.trans_le (h.2.2 x).1)
    field_simp
    <;> ring

/-- A positive sub-Markov kernel concentrates on the plateau of any cutoff
whose action tends to one. -/
theorem c8_cutoff_defect_tendsto_zero {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (K : ℝ → X → ℝ) (φ : X → ℝ)
    (hφ : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1)
    (hK : ∀ t > 0, Integrable (K t) μ ∧
      Integrable (fun x => K t x * φ x) μ ∧
      (∀ᵐ x ∂μ, 0 ≤ K t x) ∧ (∫ x, K t x ∂μ) ≤ 1)
    (hsurv : Tendsto (fun t : ℝ => ∫ x, K t x * φ x ∂μ)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1)) :
    Tendsto (fun t : ℝ => ∫ x, K t x * (1 - φ x) ∂μ)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have hu : Tendsto (fun t : ℝ => 1 - ∫ x, K t x * φ x ∂μ)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    simpa using (tendsto_const_nhds : Tendsto (fun _ : ℝ => (1 : ℝ))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1)).sub hsurv
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
  · filter_upwards [self_mem_nhdsWithin] with t ht
    apply integral_nonneg_of_ae
    filter_upwards [(hK t ht).2.2.1] with x hx
    exact mul_nonneg hx (sub_nonneg.mpr (hφ x).2)
  · filter_upwards [self_mem_nhdsWithin] with t ht
    have hi := hK t ht
    have he : (fun x => K t x * (1 - φ x)) =
        fun x => K t x - K t x * φ x := by
      funext x
      ring
    rw [he, integral_sub hi.1 hi.2.1]
    linarith [hi.2.2.2]

/-- Cutoff survival also forces the total sub-Markov mass to tend to one. -/
theorem c8_mass_tendsto_one_of_cutoff {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (K : ℝ → X → ℝ) (φ : X → ℝ)
    (hφ : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1)
    (hK : ∀ t > 0, Integrable (K t) μ ∧
      Integrable (fun x => K t x * φ x) μ ∧
      (∀ᵐ x ∂μ, 0 ≤ K t x) ∧ (∫ x, K t x ∂μ) ≤ 1)
    (hsurv : Tendsto (fun t : ℝ => ∫ x, K t x * φ x ∂μ)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1)) :
    Tendsto (fun t : ℝ => ∫ x, K t x ∂μ)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hsurv tendsto_const_nhds
  · filter_upwards [self_mem_nhdsWithin] with t ht
    have hi := hK t ht
    apply integral_mono_ae hi.2.1 hi.1
    filter_upwards [hi.2.2.1] with x hx
    exact mul_le_of_le_one_right hx (hφ x).2
  · filter_upwards [self_mem_nhdsWithin] with t ht
    exact (hK t ht).2.2.2

/-- Cutoff survival yields vanishing cutoff defect for the supplied native
spectral row. -/
theorem c8_native_cutoff_defect_of_survival {d : ℕ} (hd : 2 ≤ d)
    {κ R : ℝ} (hκ : 0 < κ) (hR : 0 < R)
    {ρ : PDE.Vec d → ℝ} {α : PDE.Vec d → EinsteinRelation.Mat d}
    (h : IsUniformlyElliptic κ ρ α)
    (s : DirichletSpectralResolution ρ α R)
    (u : ℕ → DirichletHilbertSpace (d := d) R hR)
    (hs : Tendsto s.eigenvalue atTop atTop)
    (hb : ∀ n, spectralHeatBasis s n = dirichletHilbertInclusion ρ R hR κ⁻¹
      (fun x _ => (h.2.2 x).2.1) (u n))
    (hv : ∀ n w, (∫ x in sourceBall (0 : PDE.Vec d) R,
      dot ((α x).mulVec (fun i => (u n).val (some i) x))
        (fun i => w.val (some i) x)) = s.eigenvalue n * inner ℝ
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) (u n))
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) w))
    (y : PDE.Vec d) (hy : y ∈ sourceBall 0 R)
    (φ : PDE.Vec d → ℝ) (hφ : IsSpatialTest (sourceBall 0 R) φ)
    (hbound : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1)
    (hsurv : Tendsto (fun t : ℝ => ∫ x,
      (∑' n, Real.exp (-s.eigenvalue n * t) * s.eigenfunction n y *
        s.eigenfunction n x) * φ x ∂dirichletVolume ρ R)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1)) :
    Tendsto (fun t : ℝ => ∫ x,
      (∑' n, Real.exp (-s.eigenvalue n * t) * s.eigenfunction n y *
        s.eigenfunction n x) * (1 - φ x) ∂dirichletVolume ρ R)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  haveI : IsFiniteMeasure (dirichletVolume ρ R) :=
    dirichletVolume_isFinite ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1)
  have hφlp : MemLp φ 2 (dirichletVolume ρ R) := by
    apply MemLp.of_bound hφ.1.continuous.aestronglyMeasurable 1
    exact ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hbound x).1]
      exact (hbound x).2
  apply c8_cutoff_defect_tendsto_zero (dirichletVolume ρ R) _ φ hbound _ hsurv
  intro t ht
  have hrow := spectral_heat_row_memLp hd hκ h hR s t ht y hy
  refine ⟨hrow.integrable (by norm_num), hrow.integrable_mul hφlp, ?_, ?_⟩
  · have hac : dirichletVolume ρ R ≪ volume.restrict (sourceBall (0 : PDE.Vec d) R) :=
      withDensity_absolutelyContinuous _ _
    filter_upwards [hac.ae_le (ae_restrict_mem (dirichletBall (d := d) R).isOpen.measurableSet)] with x hx
    simpa only [Real.coe_toNNReal _ ht.le] using
      (spectral_heat_kernel_nonneg_of_variational hd hκ h R hR s hs u hb hv).2
        t.toNNReal (by simpa only [Real.coe_toNNReal _ ht.le] using ht) y hy x hx
  · simpa only [Real.coe_toNNReal _ ht.le] using
      (c8_native_spectral_heat_mass_bounds hd hκ hR h s u hs hb hv
        t.toNNReal (by simpa only [Real.coe_toNNReal _ ht.le] using ht) y hy).2

/-- A smooth cutoff supported in a prescribed Euclidean neighborhood, with a
smaller Euclidean plateau inside the Dirichlet ball. -/
@[nolint unusedArguments]
theorem c8_exists_local_spatial_cutoff {d : ℕ} {R : ℝ} (hR : 0 < R)
    (y : PDE.Vec d) (hy : y ∈ sourceBall 0 R) {ε : ℝ} (hε : 0 < ε) :
    ∃ (φ : PDE.Vec d → ℝ) (r : ℝ),
      IsSpatialTest (sourceBall 0 R) φ ∧
      (∀ x, 0 ≤ φ x ∧ φ x ≤ 1) ∧
      tsupport φ ⊆ sourceBall y ε ∧
      0 < r ∧ sourceBall y r ⊆ sourceBall 0 R ∧
      (∀ x ∈ sourceBall y r, φ x = 1) := by
  have hU : IsOpen (sourceBall (0 : PDE.Vec d) R) := (dirichletBall (d := d) R).isOpen
  have hV : IsOpen (sourceBall y ε) := by
    rw [← pde_ball_eq_sourceBall y hε]
    exact PDE.isOpen_euclideanBall _ _
  have hyV : y ∈ sourceBall y ε := by
    simp [sourceBall, euclideanNorm, euclideanSq, dot, hε]
  obtain ⟨δ, hδ, hδsub⟩ := Metric.isOpen_iff.mp (hU.inter hV) y ⟨hy, hyV⟩
  let b : ContDiffBump y := ⟨δ / 4, δ / 2, by positivity, by linarith⟩
  have hnorm (x : PDE.Vec d) : ‖x‖ ≤ euclideanNorm x := by
    apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr
    intro i
    apply Real.le_sqrt_of_sq_le
    rw [Real.norm_eq_abs, sq_abs]
    change x i ^ 2 ≤ ∑ j : Fin d, x j * x j
    simpa only [pow_two] using
      (Finset.single_le_sum (fun j _ => mul_self_nonneg (x j)) (Finset.mem_univ i))
  have hs : tsupport b ⊆ sourceBall 0 R ∩ sourceBall y ε := by
    intro x hx
    apply hδsub
    rw [b.tsupport_eq] at hx
    have hx' : dist x y ≤ δ / 2 := Metric.mem_closedBall.mp hx
    exact Metric.mem_ball.mpr (by linarith)
  have hsmall : sourceBall y (δ / 4) ⊆ Metric.ball y δ := by
    intro x hx
    apply Metric.mem_ball.mpr
    rw [dist_eq_norm]
    have hx' : euclideanNorm (x - y) < δ / 4 := hx
    have := hnorm (x - y)
    linarith
  refine ⟨b, δ / 4, ⟨b.contDiff, b.hasCompactSupport, fun x hx => (hs hx).1⟩,
    fun _ => ⟨b.nonneg, b.le_one⟩, fun x hx => (hs hx).2, by positivity,
    fun x hx => (hδsub (hsmall hx)).1, ?_⟩
  intro x hx
  apply b.one_of_mem_closedBall
  apply Metric.mem_closedBall.mpr
  rw [dist_eq_norm]
  have hx' : euclideanNorm (x - y) < δ / 4 := hx
  exact (hnorm (x - y)).trans (le_of_lt hx')

/-- A pointwise cutoff estimate controls the error of a positive kernel action. -/
@[nolint unusedArguments]
theorem c8_kernel_action_cutoff_error {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (k φ f : X → ℝ) (a ε C : ℝ)
    (hε : 0 ≤ ε) (hC : 0 ≤ C)
    (hk : Integrable k μ) (hkφ : Integrable (fun x => k x * φ x) μ)
    (hkf : Integrable (fun x => k x * f x) μ)
    (hkn : ∀ᵐ x ∂μ, 0 ≤ k x)
    (hbound : ∀ x, |f x - a| ≤ ε + C * (1 - φ x)) :
    |(∫ x, k x * f x ∂μ) - a * (∫ x, k x ∂μ)| ≤
      ε * (∫ x, k x ∂μ) + C *
        ((∫ x, k x ∂μ) - (∫ x, k x * φ x ∂μ)) := by
  have hd : Integrable (fun x => k x * (f x - a)) μ := by
    convert hkf.sub (hk.mul_const a) using 1 <;> ext x <;> simp only [Pi.sub_apply] <;> ring
  have hg : Integrable (fun x => ε * k x + C * (k x - k x * φ x)) μ :=
    (hk.const_mul ε).add ((hk.sub hkφ).const_mul C)
  have he : (∫ x, k x * (f x - a) ∂μ) =
      (∫ x, k x * f x ∂μ) - a * (∫ x, k x ∂μ) := by
    have hf : (fun x => k x * (f x - a)) = fun x => k x * f x - k x * a := by
      funext x; ring
    rw [hf, integral_sub hkf (hk.mul_const a), integral_mul_const]
    ring
  rw [← he]
  calc
    |∫ x, k x * (f x - a) ∂μ| ≤ ∫ x, |k x * (f x - a)| ∂μ :=
      abs_integral_le_integral_abs
    _ ≤ ∫ x, ε * k x + C * (k x - k x * φ x) ∂μ := by
      apply integral_mono_ae hd.abs hg
      filter_upwards [hkn] with x hx
      rw [abs_mul, abs_of_nonneg hx]
      have h := mul_le_mul_of_nonneg_left (hbound x) hx
      nlinarith
    _ = ε * (∫ x, k x ∂μ) + C *
        ((∫ x, k x ∂μ) - (∫ x, k x * φ x ∂μ)) := by
      change (∫ x, (fun x => ε * k x) x +
        (fun x => C * (k - (fun x => k x * φ x)) x) x ∂μ) = _
      rw [integral_add (hk.const_mul ε) ((hk.sub hkφ).const_mul C),
        integral_const_mul, integral_const_mul]
      simp only [Pi.sub_apply, integral_sub hk hkφ]

/-- A continuous function with globally bounded deviation admits a local
cutoff estimate at every interior point. -/
theorem c8_continuous_local_cutoff_estimate {d : ℕ} {R : ℝ} (hR : 0 < R)
    (y : PDE.Vec d) (hy : y ∈ sourceBall 0 R) (f : PDE.Vec d → ℝ)
    (hf : ContinuousAt f y) (C : ℝ) (hC : ∀ x, |f x - f y| ≤ C)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (φ : PDE.Vec d → ℝ) (r : ℝ),
      IsSpatialTest (sourceBall 0 R) φ ∧
      (∀ x, 0 ≤ φ x ∧ φ x ≤ 1) ∧
      0 < r ∧ sourceBall y r ⊆ sourceBall 0 R ∧
      (∀ x ∈ sourceBall y r, φ x = 1) ∧
      (∀ x, |f x - f y| ≤ ε + C * (1 - φ x)) := by
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC y)
  obtain ⟨δ, hδ, hnear⟩ := Metric.continuousAt_iff.mp hf ε hε
  obtain ⟨φ, r, hφ, hφbound, hsupp, hr, hrsub, hplateau⟩ :=
    c8_exists_local_spatial_cutoff hR y hy hδ
  refine ⟨φ, r, hφ, hφbound, hr, hrsub, hplateau, ?_⟩
  intro x
  by_cases hx : x ∈ sourceBall y δ
  · have hnorm : ‖x - y‖ ≤ euclideanNorm (x - y) := by
      apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr
      intro i
      apply Real.le_sqrt_of_sq_le
      rw [Real.norm_eq_abs, sq_abs]
      change (x - y) i ^ 2 ≤ ∑ j : Fin d, (x - y) j * (x - y) j
      simpa only [pow_two] using
        (Finset.single_le_sum (fun j _ => mul_self_nonneg ((x - y) j)) (Finset.mem_univ i))
    have hdist : dist x y < δ := by
      rw [dist_eq_norm]
      exact lt_of_le_of_lt hnorm hx
    have hn := hnear hdist
    rw [Real.dist_eq] at hn
    have hp := mul_nonneg hC0 (sub_nonneg.mpr (hφbound x).2)
    linarith
  · have hzero : φ x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hsupp h))
    rw [hzero]
    have := hC x
    linarith

#print axioms c8_continuous_local_cutoff_estimate

/-- Cutoff survival and local approximation imply convergence of a bounded
kernel action to the prescribed value. -/
theorem c8_kernel_action_tendsto_of_cutoffs {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (K : ℝ → X → ℝ) (f : X → ℝ) (a : ℝ)
    (hf : ∀ t > 0, Integrable (fun x => K t x * f x) μ)
    (hcut : ∀ ε > 0, ∃ (φ : X → ℝ) (C : ℝ),
      0 ≤ C ∧ (∀ x, 0 ≤ φ x ∧ φ x ≤ 1) ∧
      (∀ x, |f x - a| ≤ ε + C * (1 - φ x)) ∧
      (∀ t > 0, Integrable (K t) μ ∧
        Integrable (fun x => K t x * φ x) μ ∧
        (∀ᵐ x ∂μ, 0 ≤ K t x) ∧ (∫ x, K t x ∂μ) ≤ 1) ∧
      Tendsto (fun t : ℝ => ∫ x, K t x * φ x ∂μ)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 1)) :
    Tendsto (fun t : ℝ => ∫ x, K t x * f x ∂μ)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds a) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨φ, C, hC, hφ, happrox, hK, hsurv⟩ := hcut (ε / 4) (by positivity)
  have hm := c8_mass_tendsto_one_of_cutoff μ K φ hφ hK hsurv
  have hdef : Tendsto (fun t : ℝ =>
      (∫ x, K t x ∂μ) - (∫ x, K t x * φ x ∂μ))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    simpa using hm.sub hsurv
  have hb : Tendsto (fun t : ℝ => ε / 4 * (∫ x, K t x ∂μ) + C *
      ((∫ x, K t x ∂μ) - (∫ x, K t x * φ x ∂μ)))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (ε / 4)) := by
    simpa using ((tendsto_const_nhds.mul hm).add (tendsto_const_nhds.mul hdef))
  have hb' : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      ε / 4 * (∫ x, K t x ∂μ) + C *
        ((∫ x, K t x ∂μ) - (∫ x, K t x * φ x ∂μ)) < ε / 2 :=
    hb.eventually (Iio_mem_nhds (by linarith))
  have ha : Tendsto (fun t : ℝ => a * (∫ x, K t x ∂μ))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds a) := by
    simpa using tendsto_const_nhds.mul hm
  have ha' := (Metric.tendsto_nhds.mp ha) (ε / 2) (by positivity)
  filter_upwards [self_mem_nhdsWithin, hb', ha'] with t ht htbound htmass
  have he := c8_kernel_action_cutoff_error μ (K t) φ f a (ε / 4) C
    (by positivity) hC (hK t ht).1 (hK t ht).2.1 (hf t ht)
    (hK t ht).2.2.1 happrox
  rw [Real.dist_eq] at htmass ⊢
  have htri := abs_add_le ((∫ x, K t x * f x ∂μ) - a * (∫ x, K t x ∂μ))
    (a * (∫ x, K t x ∂μ) - a)
  have hid : (∫ x, K t x * f x ∂μ) - a =
      ((∫ x, K t x * f x ∂μ) - a * (∫ x, K t x ∂μ)) +
        (a * (∫ x, K t x ∂μ) - a) := by ring
  rw [hid]
  linarith

/-- Conditional every-pole convergence of the native spectral action on a
continuous bounded test, from survival of its local smooth cutoffs. -/
theorem c8_native_continuous_action_of_cutoff_survival {d : ℕ} (hd : 2 ≤ d)
    {κ R : ℝ} (hκ : 0 < κ) (hR : 0 < R)
    {ρ : PDE.Vec d → ℝ} {α : PDE.Vec d → EinsteinRelation.Mat d}
    (h : IsUniformlyElliptic κ ρ α)
    (s : DirichletSpectralResolution ρ α R)
    (u : ℕ → DirichletHilbertSpace (d := d) R hR)
    (hs : Tendsto s.eigenvalue atTop atTop)
    (hb : ∀ n, spectralHeatBasis s n = dirichletHilbertInclusion ρ R hR κ⁻¹
      (fun x _ => (h.2.2 x).2.1) (u n))
    (hv : ∀ n w, (∫ x in sourceBall (0 : PDE.Vec d) R,
      dot ((α x).mulVec (fun i => (u n).val (some i) x))
        (fun i => w.val (some i) x)) = s.eigenvalue n * inner ℝ
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) (u n))
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) w))
    (y : PDE.Vec d) (hy : y ∈ sourceBall 0 R)
    (f : PDE.Vec d → ℝ) (hf : ContinuousAt f y)
    (hflp : MemLp f 2 (dirichletVolume ρ R))
    (C : ℝ) (hC : ∀ x, |f x - f y| ≤ C)
    (hsurv : ∀ φ : PDE.Vec d → ℝ, IsSpatialTest (sourceBall 0 R) φ →
      (∀ x, 0 ≤ φ x ∧ φ x ≤ 1) →
      (∃ r : ℝ, 0 < r ∧ sourceBall y r ⊆ sourceBall 0 R ∧
        ∀ x ∈ sourceBall y r, φ x = 1) →
      Tendsto (fun t : ℝ => ∫ x,
        (∑' n, Real.exp (-s.eigenvalue n * t) * s.eigenfunction n y *
          s.eigenfunction n x) * φ x ∂dirichletVolume ρ R)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 1)) :
    Tendsto (fun t : ℝ => ∫ x,
      (∑' n, Real.exp (-s.eigenvalue n * t) * s.eigenfunction n y *
        s.eigenfunction n x) * f x ∂dirichletVolume ρ R)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (f y)) := by
  haveI : IsFiniteMeasure (dirichletVolume ρ R) :=
    dirichletVolume_isFinite ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1)
  apply c8_kernel_action_tendsto_of_cutoffs (dirichletVolume ρ R) _ f (f y)
  · intro t ht
    exact (spectral_heat_row_memLp hd hκ h hR s t ht y hy).integrable_mul hflp
  · intro ε hε
    obtain ⟨φ, r, hφ, hφbound, hr, hrsub, hplateau, happrox⟩ :=
      c8_continuous_local_cutoff_estimate hR y hy f hf C hC hε
    have hφlp : MemLp φ 2 (dirichletVolume ρ R) := by
      apply MemLp.of_bound hφ.1.continuous.aestronglyMeasurable 1
      exact ae_of_all _ fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hφbound x).1]
        exact (hφbound x).2
    refine ⟨φ, C, (abs_nonneg _).trans (hC y), hφbound, happrox, ?_,
      hsurv φ hφ hφbound ⟨r, hr, hrsub, hplateau⟩⟩
    intro t ht
    have hrow := spectral_heat_row_memLp hd hκ h hR s t ht y hy
    refine ⟨hrow.integrable (by norm_num), hrow.integrable_mul hφlp, ?_, ?_⟩
    · have hac : dirichletVolume ρ R ≪ volume.restrict (sourceBall (0 : PDE.Vec d) R) :=
        withDensity_absolutelyContinuous _ _
      filter_upwards [hac.ae_le (ae_restrict_mem (dirichletBall (d := d) R).isOpen.measurableSet)] with x hx
      simpa only [Real.coe_toNNReal _ ht.le] using
        (spectral_heat_kernel_nonneg_of_variational hd hκ h R hR s hs u hb hv).2
          t.toNNReal (by simpa only [Real.coe_toNNReal _ ht.le] using ht) y hy x hx
    · simpa only [Real.coe_toNNReal _ ht.le] using
        (c8_native_spectral_heat_mass_bounds hd hκ hR h s u hs hb hv
          t.toNNReal (by simpa only [Real.coe_toNNReal _ ht.le] using ht) y hy).2

/-- A spatial test divided by a continuous elliptic density is continuous,
square-integrable, and has bounded deviation from its value at any point. -/
theorem c8_spatial_test_quotient_properties {d : ℕ} {κ R : ℝ}
    (hκ : 0 < κ) (hR : 0 < R)
    {ρ : PDE.Vec d → ℝ} {α : PDE.Vec d → EinsteinRelation.Mat d}
    (h : IsUniformlyElliptic κ ρ α) (hρ : Continuous ρ)
    (ψ : PDE.Vec d → ℝ) (hψ : IsSpatialTest (sourceBall 0 R) ψ)
    (y : PDE.Vec d) :
    Continuous (fun x => ψ x / ρ x) ∧
    MemLp (fun x => ψ x / ρ x) 2 (dirichletVolume ρ R) ∧
    ∃ C : ℝ, ∀ x, |ψ x / ρ x - ψ y / ρ y| ≤ C := by
  haveI : IsFiniteMeasure (dirichletVolume ρ R) :=
    dirichletVolume_isFinite ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1)
  have hρpos (x : PDE.Vec d) : 0 < ρ x := hκ.trans_le (h.2.2 x).1
  have hc : Continuous (fun x => ψ x / ρ x) :=
    hψ.1.continuous.div hρ (fun x => ne_of_gt (hρpos x))
  obtain ⟨B, hB⟩ := (hψ.2.1.isCompact_range hψ.1.continuous).isBounded.exists_norm_le
  let M : ℝ := max B 0 / κ
  have hM : 0 ≤ M := div_nonneg (le_max_right _ _) hκ.le
  have hbound (x : PDE.Vec d) : |ψ x / ρ x| ≤ M := by
    rw [abs_div, abs_of_pos (hρpos x)]
    have hBx : |ψ x| ≤ B := by
      simpa only [Real.norm_eq_abs] using hB (ψ x) (Set.mem_range_self x)
    calc
      |ψ x| / ρ x ≤ |ψ x| / κ :=
        div_le_div_of_nonneg_left (abs_nonneg _) hκ (h.2.2 x).1
      _ ≤ max B 0 / κ := div_le_div_of_nonneg_right
        (hBx.trans (le_max_left _ _)) hκ.le
  refine ⟨hc, ?_, 2 * M, ?_⟩
  · apply MemLp.of_bound hc.aestronglyMeasurable M
    exact ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hbound x
  · intro x
    have := abs_sub (ψ x / ρ x) (ψ y / ρ y)
    linarith [hbound x, hbound y]

/-- Every-pole initial delta for the native spectrum, conditional on the
survival of all local smooth cutoffs. -/
theorem c8_native_initial_delta_of_cutoff_survival {d : ℕ} (hd : 2 ≤ d)
    {κ R : ℝ} (hκ : 0 < κ) (hR : 0 < R)
    {ρ : PDE.Vec d → ℝ} {α : PDE.Vec d → EinsteinRelation.Mat d}
    (h : IsUniformlyElliptic κ ρ α) (hρ : Continuous ρ)
    (s : DirichletSpectralResolution ρ α R)
    (u : ℕ → DirichletHilbertSpace (d := d) R hR)
    (hs : Tendsto s.eigenvalue atTop atTop)
    (hb : ∀ n, spectralHeatBasis s n = dirichletHilbertInclusion ρ R hR κ⁻¹
      (fun x _ => (h.2.2 x).2.1) (u n))
    (hv : ∀ n w, (∫ x in sourceBall (0 : PDE.Vec d) R,
      dot ((α x).mulVec (fun i => (u n).val (some i) x))
        (fun i => w.val (some i) x)) = s.eigenvalue n * inner ℝ
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) (u n))
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) w))
    (hsurv : ∀ y ∈ sourceBall (0 : PDE.Vec d) R,
      ∀ φ : PDE.Vec d → ℝ, IsSpatialTest (sourceBall 0 R) φ →
      (∀ x, 0 ≤ φ x ∧ φ x ≤ 1) →
      (∃ r : ℝ, 0 < r ∧ sourceBall y r ⊆ sourceBall 0 R ∧
        ∀ x ∈ sourceBall y r, φ x = 1) →
      Tendsto (fun t : ℝ => ∫ x,
        (∑' n, Real.exp (-s.eigenvalue n * t) * s.eigenfunction n y *
          s.eigenfunction n x) * φ x ∂dirichletVolume ρ R)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 1)) :
    ∀ y ∈ sourceBall (0 : PDE.Vec d) R, ∀ ψ : PDE.Vec d → ℝ,
      IsSpatialTest (sourceBall 0 R) ψ →
      Tendsto (fun t : ℝ => ∫ x in sourceBall (0 : PDE.Vec d) R,
        (ρ y * ∑' n, Real.exp (-s.eigenvalue n * t) *
          s.eigenfunction n x * s.eigenfunction n y) * ψ x)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (ψ y)) := by
  intro y hy ψ hψ
  obtain ⟨hc, hlp, C, hC⟩ := c8_spatial_test_quotient_properties hκ hR h hρ ψ hψ y
  have hact := c8_native_continuous_action_of_cutoff_survival hd hκ hR h s u hs hb hv
    y hy (fun x => ψ x / ρ x) hc.continuousAt hlp C hC (hsurv y hy)
  have hlim := (tendsto_const_nhds : Tendsto (fun _ : ℝ => ρ y)
    (nhdsWithin 0 (Set.Ioi 0)) (nhds (ρ y))).mul hact
  have hyρ : ρ y ≠ 0 := ne_of_gt (hκ.trans_le (h.2.2 y).1)
  have hlimit : ρ y * (ψ y / ρ y) = ψ y := by field_simp
  rw [hlimit] at hlim
  convert hlim using 1
  funext t
  rw [c8_weighted_quotient_integral hκ h]
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact ae_of_all _ fun x => by
    have hk : (∑' n, Real.exp (-s.eigenvalue n * t) * s.eigenfunction n y *
        s.eigenfunction n x) =
        ∑' n, Real.exp (-s.eigenvalue n * t) * s.eigenfunction n x *
          s.eigenfunction n y := by
      congr 1
      funext n
      ring
    dsimp only
    rw [hk]
    ring

/-- Strong L² convergence implies mean absolute convergence for every
finite measure, including weighted restrictions to local neighborhoods. -/
theorem c8_finite_l2_to_mean {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (v : ℝ → Lp ℝ 2 μ)
    (hv : Tendsto v (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)) :
    Tendsto (fun t : ℝ => ∫ x, |v t x| ∂μ)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have hn (w : Lp ℝ 2 μ) : (∫ x, |w x| ∂μ) ≤
      (μ Set.univ ^ (1 / 2 : ℝ)).toReal * ‖w‖ := by
    have hb : eLpNorm w 1 μ ≤ eLpNorm w 2 μ * μ Set.univ ^ (1 / 2 : ℝ) := by
      convert eLpNorm_le_eLpNorm_mul_rpow_measure_univ (by norm_num : (1 : ENNReal) ≤ 2)
        (Lp.aestronglyMeasurable w) using 1
      norm_num
    have hfin : eLpNorm w 2 μ * μ Set.univ ^ (1 / 2 : ℝ) ≠ ⊤ := by
      apply ENNReal.mul_ne_top (Lp.memLp w).ne
      finiteness
    have hi := ENNReal.toReal_mono hfin hb
    rw [eLpNorm_one_eq_lintegral_enorm (Lp.aestronglyMeasurable w),
      ← integral_norm_eq_lintegral_enorm (Lp.aestronglyMeasurable w),
      ENNReal.toReal_mul, ← Lp.norm_def] at hi
    simpa only [Real.norm_eq_abs, mul_comm] using hi
  have hnorm : Tendsto (fun t : ℝ => (μ Set.univ ^ (1 / 2 : ℝ)).toReal * ‖v t‖)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    simpa using tendsto_const_nhds.mul hv.norm
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hnorm
  · exact Filter.Eventually.of_forall fun t => integral_nonneg fun x => abs_nonneg _
  · exact Filter.Eventually.of_forall fun t => hn (v t)

/-- Strong global weighted L² convergence and local oscillation control on
positive-mass plateau neighborhoods imply convergence at the pole. -/
theorem c8_point_tendsto_of_global_l2_local_oscillation {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (u : ℝ → X → ℝ) (φ : X → ℝ)
    (y : X) (b : ℝ) (v : ℝ → Lp ℝ 2 μ)
    (hv : Tendsto v (nhdsWithin 0 (Set.Ioi 0)) (nhds 0))
    (heq : ∀ t > 0, ∀ᵐ x ∂μ, v t x = u t x - φ x)
    (hlocal : ∀ ε > 0, ∃ A : Set X,
      0 < (μ.restrict A).real Set.univ ∧
      (∀ᵐ x ∂μ.restrict A, φ x = b) ∧
      (∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        ∀ᵐ x ∂μ.restrict A, |u t y - u t x| ≤ ε)) :
    Tendsto (fun t : ℝ => u t y)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds b) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨A, hmass, hplateau, hosc⟩ := hlocal (ε / 2) (by positivity)
  have hmean := c8_finite_l2_to_mean μ v hv
  have hsmall : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      (∫ x, |v t x| ∂μ) < ε / 2 * (μ.restrict A).real Set.univ :=
    hmean.eventually (Iio_mem_nhds (by positivity))
  filter_upwards [self_mem_nhdsWithin, hosc, hsmall] with t ht htosc htmean
  have hvint : Integrable (fun x => |v t x|) μ := by
    simpa only [Real.norm_eq_abs] using ((Lp.memLp (v t)).integrable (by norm_num)).norm
  have hp : ∀ᵐ x ∂μ.restrict A, |u t y - b| ≤ ε / 2 + |v t x| := by
    filter_upwards [htosc, hplateau,
      (heq t ht).filter_mono (ae_mono Measure.restrict_le_self)] with x hx hφ hxv
    have htri := abs_add_le (u t y - u t x) (u t x - b)
    have hsum : u t y - u t x + (u t x - b) = u t y - b := by ring
    rw [hsum] at htri
    rw [hφ] at hxv
    rw [hxv]
    linarith
  have hi := integral_mono_ae (integrable_const |u t y - b|)
    ((integrable_const (ε / 2)).add (hvint.mono_measure Measure.restrict_le_self)) hp
  change (∫ _x, |u t y - b| ∂μ.restrict A) ≤
    ∫ x, ε / 2 + |v t x| ∂μ.restrict A at hi
  simp only [integral_add (integrable_const (ε / 2))
    (hvint.mono_measure Measure.restrict_le_self), integral_const, smul_eq_mul] at hi
  have hmono : (∫ x, |v t x| ∂μ.restrict A) ≤ ∫ x, |v t x| ∂μ :=
    integral_mono_measure Measure.restrict_le_self (ae_of_all _ fun _ => abs_nonneg _) hvint
  rw [Real.dist_eq]
  nlinarith

/-- The spectral cutoff survives at a pole if its heat action has uniformly
small oscillation on positive-mass subsets of the cutoff plateau. -/
theorem c8_native_cutoff_survival_of_local_oscillation {d : ℕ} (hd : 2 ≤ d)
    {κ R : ℝ} (hκ : 0 < κ) (hR : 0 < R)
    {ρ : PDE.Vec d → ℝ} {α : PDE.Vec d → EinsteinRelation.Mat d}
    (h : IsUniformlyElliptic κ ρ α) (s : DirichletSpectralResolution ρ α R)
    (y : PDE.Vec d) (φ : PDE.Vec d → ℝ)
    (hφ : IsSpatialTest (sourceBall 0 R) φ) (hbound : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1)
    (hlocal : ∀ ε > 0, ∃ A : Set (PDE.Vec d),
      0 < ((dirichletVolume ρ R).restrict A).real Set.univ ∧
      (∀ᵐ x ∂(dirichletVolume ρ R).restrict A, φ x = 1) ∧
      (∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        ∀ᵐ x ∂(dirichletVolume ρ R).restrict A,
          |(∫ z, (∑' n, Real.exp (-s.eigenvalue n * t) * s.eigenfunction n y *
            s.eigenfunction n z) * φ z ∂dirichletVolume ρ R) -
           (∫ z, (∑' n, Real.exp (-s.eigenvalue n * t) * s.eigenfunction n x *
            s.eigenfunction n z) * φ z ∂dirichletVolume ρ R)| ≤ ε)) :
    Tendsto (fun t : ℝ => ∫ x,
      (∑' n, Real.exp (-s.eigenvalue n * t) * s.eigenfunction n y *
        s.eigenfunction n x) * φ x ∂dirichletVolume ρ R)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
  haveI : IsFiniteMeasure (dirichletVolume ρ R) :=
    dirichletVolume_isFinite ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1)
  have hφlp : MemLp φ 2 (dirichletVolume ρ R) := by
    apply MemLp.of_bound hφ.1.continuous.aestronglyMeasurable 1
    exact ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hbound x).1]
      exact (hbound x).2
  let F : Lp ℝ 2 (dirichletVolume ρ R) := hφlp.toLp φ
  let T : ℝ → Lp ℝ 2 (dirichletVolume ρ R) := fun t =>
    SpectralHeat.heatOperator (spectralHeatBasis s) s.eigenvalue
      (fun n => (s.eigenvalue_pos n).le) t.toNNReal F
  have hc : Continuous T :=
    (SpectralHeat.heatOperator_continuous (spectralHeatBasis s) s.eigenvalue
      (fun n => (s.eigenvalue_pos n).le) F).comp continuous_real_toNNReal
  have hzero : T 0 = F := by
    simp [T, SpectralHeat.heatOperator_zero]
  have hv : Tendsto (fun t => T t - F) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have ht : Tendsto (fun t : ℝ => T t - F) (nhds 0) (nhds (T 0 - F)) :=
      (hc.sub (continuous_const : Continuous (fun _ : ℝ => F))).continuousAt.tendsto
    simpa only [hzero, sub_self] using ht.mono_left
      (nhdsWithin_le_nhds : nhdsWithin (0 : ℝ) (Set.Ioi 0) ≤ nhds 0)
  apply c8_point_tendsto_of_global_l2_local_oscillation (dirichletVolume ρ R)
    (fun t x => ∫ z, (∑' n, Real.exp (-s.eigenvalue n * t) *
      s.eigenfunction n x * s.eigenfunction n z) * φ z ∂dirichletVolume ρ R)
    φ y 1 (fun t => T t - F) hv ?_ hlocal
  intro t ht
  have ha := spectral_heat_operator_ae_kernel_action hd hκ h hR s t.toNNReal
    (by simpa only [Real.coe_toNNReal _ ht.le] using ht) F
  filter_upwards [ha, Lp.coeFn_sub (T t) F, hφlp.coeFn_toLp] with x hx hsub hF
  have hi : (∫ z, (∑' n, Real.exp (-s.eigenvalue n * t) *
      s.eigenfunction n x * s.eigenfunction n z) * F z ∂dirichletVolume ρ R) =
      ∫ z, (∑' n, Real.exp (-s.eigenvalue n * t) *
        s.eigenfunction n x * s.eigenfunction n z) * φ z ∂dirichletVolume ρ R := by
    apply integral_congr_ae
    filter_upwards [hφlp.coeFn_toLp] with z hz
    rw [hz]
  change (T t - F) x = _
  rw [hsub]
  simp only [Pi.sub_apply]
  change T t x = _ at hx
  simp only [Real.coe_toNNReal _ ht.le] at hx
  rw [hx, hi, hF]

/-- A nonempty Euclidean ball inside the Dirichlet domain has positive finite
weighted mass. -/
theorem c8_dirichlet_plateau_ball_positive {d : ℕ} {κ R r : ℝ} (hκ : 0 < κ)
    {ρ : PDE.Vec d → ℝ} {α : PDE.Vec d → EinsteinRelation.Mat d}
    (h : IsUniformlyElliptic κ ρ α) (hR : 0 < R)
    (y : PDE.Vec d) (hr : 0 < r) (hsub : sourceBall y r ⊆ sourceBall 0 R) :
    0 < ((dirichletVolume ρ R).restrict (sourceBall y r)).real Set.univ := by
  haveI : IsFiniteMeasure (dirichletVolume ρ R) :=
    dirichletVolume_isFinite ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1)
  have hopen : IsOpen (sourceBall y r) := by
    rw [← pde_ball_eq_sourceBall y hr]
    exact PDE.isOpen_euclideanBall _ _
  have hne : (sourceBall y r).Nonempty := by
    refine ⟨y, ?_⟩
    simp [sourceBall, euclideanNorm, euclideanSq, dot, hr]
  have hpos := dirichletVolume_open_pos hκ h R hopen hsub hne
  rw [measureReal_def, Measure.restrict_apply_univ]
  exact ENNReal.toReal_pos (ne_of_gt hpos) (measure_ne_top _ _)

/-- Uniform small-time oscillation on Euclidean plateau balls implies native
spectral cutoff survival at the pole. -/
theorem c8_native_cutoff_survival_of_ball_oscillation {d : ℕ} (hd : 2 ≤ d)
    {κ R : ℝ} (hκ : 0 < κ) (hR : 0 < R)
    {ρ : PDE.Vec d → ℝ} {α : PDE.Vec d → EinsteinRelation.Mat d}
    (h : IsUniformlyElliptic κ ρ α) (s : DirichletSpectralResolution ρ α R)
    (y : PDE.Vec d) (φ : PDE.Vec d → ℝ)
    (hφ : IsSpatialTest (sourceBall 0 R) φ) (hbound : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1)
    (hlocal : ∀ ε > 0, ∃ r : ℝ, 0 < r ∧ sourceBall y r ⊆ sourceBall 0 R ∧
      (∀ x ∈ sourceBall y r, φ x = 1) ∧
      (∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        ∀ x ∈ sourceBall y r,
          |(∫ z, (∑' n, Real.exp (-s.eigenvalue n * t) * s.eigenfunction n y *
            s.eigenfunction n z) * φ z ∂dirichletVolume ρ R) -
           (∫ z, (∑' n, Real.exp (-s.eigenvalue n * t) * s.eigenfunction n x *
            s.eigenfunction n z) * φ z ∂dirichletVolume ρ R)| ≤ ε)) :
    Tendsto (fun t : ℝ => ∫ x,
      (∑' n, Real.exp (-s.eigenvalue n * t) * s.eigenfunction n y *
        s.eigenfunction n x) * φ x ∂dirichletVolume ρ R)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
  apply c8_native_cutoff_survival_of_local_oscillation hd hκ hR h s y φ hφ hbound
  intro ε hε
  obtain ⟨r, hr, hsub, hplateau, hosc⟩ := hlocal ε hε
  have hopen : IsOpen (sourceBall y r) := by
    rw [← pde_ball_eq_sourceBall y hr]
    exact PDE.isOpen_euclideanBall _ _
  refine ⟨sourceBall y r, c8_dirichlet_plateau_ball_positive hκ h hR y hr hsub, ?_, ?_⟩
  · filter_upwards [ae_restrict_mem hopen.measurableSet] with x hx
    exact hplateau x hx
  · filter_upwards [hosc] with t ht
    filter_upwards [ae_restrict_mem hopen.measurableSet] with x hx
    exact ht x hx

#print axioms c8_native_cutoff_survival_of_ball_oscillation
#print axioms c8_dirichlet_plateau_ball_positive

#print axioms c8_native_cutoff_survival_of_local_oscillation

#print axioms c8_point_tendsto_of_global_l2_local_oscillation

#print axioms c8_finite_l2_to_mean



#print axioms c8_native_initial_delta_of_cutoff_survival

#print axioms c8_spatial_test_quotient_properties

#print axioms c8_native_continuous_action_of_cutoff_survival

#print axioms c8_kernel_action_tendsto_of_cutoffs

#print axioms c8_kernel_action_cutoff_error

#print axioms c8_exists_local_spatial_cutoff

#print axioms c8_native_cutoff_defect_of_survival

#print axioms c8_mass_tendsto_one_of_cutoff

#print axioms c8_cutoff_defect_tendsto_zero

#print axioms c8_weighted_quotient_integral

#print axioms c8_native_spectral_heat_mass_bounds

end EinsteinFull.Calculus
