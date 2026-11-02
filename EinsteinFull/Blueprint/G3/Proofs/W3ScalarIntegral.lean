import EinsteinFull.Blueprint.G3.node_l_u3A_finite_u2D_xi_u23_scalar_u2D_integral
import EinsteinFull.Blueprint.Roots.node_p_u3A_scalar
import EinsteinFull.Blueprint.G2.node_p_u3A_scalar_u23_unit_u2D_initialization
import EinsteinFull.Work.W3.GaussianDerivativeAveragingSupport
import EinsteinFull.Calculus.ComplexGeneratorSpatialSupport
import EinsteinFull.Calculus.ComplexTransposeSupport
import EinsteinFull.Work.W2.MassiveCorrectorGradientSupport
import EinsteinRelation.Clock.CentredClockField
import EinsteinFull.Blueprint.G3.Proofs.W4Queue0420_1

open MeasureTheory Set
open scoped NNReal ENNReal

noncomputable section
namespace EinsteinFull.Blueprint.ScalarIntegral
open EinsteinRelation

private instance reducedProbability {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) : IsProbabilityMeasure (reducedLaw Q) :=
  reducedLaw_probability Q

private theorem coefficient_clock_observations {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) :
    ∃ (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedCoefficientObservation Q a ∧ IsReducedClockObservation Q μ := by
  have ha (j k : Fin d) : MemLp (fun ω : FieldPair d => (ω.1 0 j k : ℂ))
      2 (reducedLaw Q) := (memLp_reduced_coefficient_complex Q j k).mono_exponent le_top
  have hm : MemLp (fun ω : FieldPair d => (ω.2 0 : ℂ)) 2 (reducedLaw Q) := by
    apply (memLp_top_of_bound
      (Complex.continuous_ofReal.comp Clock.continuous_clockAtOrigin).aestronglyMeasurable
      (sourceReducedBound Λ) ?_).mono_exponent le_top
    filter_upwards [Clock.ae_abs_clockAtOrigin_le Q] with ω hω
    simpa only [Function.comp_apply, Complex.norm_real, Real.norm_eq_abs] using! hω
  exact ⟨fun j k => (ha j k).toLp _, hm.toLp _,
    fun j k => (ha j k).coeFn_toLp, hm.coeFn_toLp⟩

/-- The literal reduced drift has zero mean, by testing its divergence against one. -/
theorem finiteXi_scalar_drift_mean_zero {d : ℕ} {D : StructuralData d}
    {Q : EnvironmentLaw d D.ellipticity D.dependenceRange} {hQ : HasSmoothBounds D Q}
    {β : Fin d → Lp ℂ 2 (reducedLaw Q)} (hβ : IsReducedDriftObservation Q hQ β)
    (j : Fin d) : (∫ ω, β j ω ∂reducedLaw Q) = 0 := by
  have he := hβ.integral_mul j (Lp.const 2 (reducedLaw Q) 1) (fun _ => 0)
    (hasComplexHorizontalGradient_const _ (reducedLaw_stationary Q) 1)
  have hl : (∫ ω, β j ω * Lp.const 2 (reducedLaw Q) (1 : ℂ) ω ∂reducedLaw Q) =
      ∫ ω, β j ω ∂reducedLaw Q := by
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_const 2 (reducedLaw Q) (1 : ℂ)] with ω hω
    simp only [hω, Function.const_apply, mul_one]
  have hr : (∫ ω, ∑ k : Fin d, (ω.1 0 k j : ℂ) *
      (0 : Lp ℂ 2 (reducedLaw Q)) ω ∂reducedLaw Q) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [Lp.coeFn_zero ℂ 2 (reducedLaw Q)] with ω hω
    simp only [hω, Pi.zero_apply, mul_zero, Finset.sum_const_zero]
  simpa only [hl, hr, mul_zero] using! he

/-- Centering does not change the actual unforced drift orbit, including at time zero. -/
theorem finiteXi_scalar_centered_orbit {d : ℕ} {D : StructuralData d}
    {Q : EnvironmentLaw d D.ellipticity D.dependenceRange} {hQ : HasSmoothBounds D Q}
    {β : Fin d → Lp ℂ 2 (reducedLaw Q)} (hβ : IsReducedDriftObservation Q hQ β)
    {i : Fin d} {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i 0 P) (t : ℝ≥0) (j : Fin d) :
    centeredComplexLp Q (P t (β j)) = P t (β j) := by
  have hm := (hP.integral_orbit_graph_forced (β j) t).integral_eq_zero
  rw [integral_congr_ae (Lp.coeFn_sub (P t (β j)) (β j))] at hm
  change (∫ ω, P t (β j) ω - β j ω ∂reducedLaw Q) = 0 at hm
  rw [integral_sub (integrable_complexLp Q _) (integrable_complexLp Q _),
    finiteXi_scalar_drift_mean_zero hβ j, sub_zero] at hm
  change P t (β j) - Lp.const 2 (reducedLaw Q) _ = _
  rw [hm, map_zero, sub_zero]

/-- The prescribed scalar Prop gives all-order wide averaged bounds on the
actual uncentered drift orbit after its structural threshold. -/
theorem finiteXi_scalar_wide_derivative_decay
    (hscalar : node_p_u3A_scalarStmt) (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) :
    ∃ t₀ : ℝ, ∃ Cder : ℕ → ℝ, 1 ≤ t₀ ∧ (∀ k, 0 < Cder k) ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q) (β : Fin d → Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β →
    ∀ (P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)),
      IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ 0 P →
    ∀ t : ℝ≥0, t₀ ≤ (t : ℝ) → ∀ s : ℝ, 2 * (t : ℝ) ≤ s → ∀ hs : 0 < s,
    ∀ (j : Fin d) (k : ℕ) (dirs : Fin k → Fin d),
      ‖gaussianDerivativeAverage hd Q s hs k dirs (P t (β j))‖ ≤
        Cder k * s ^ (-(1 / 2 + (d : ℝ) / 4) - (k : ℝ) / 2) := by
  obtain ⟨a₀, η₀, ha₀, ha₁, hη, hs⟩ := hscalar d hd D
  obtain ⟨C, Dp, t₀, Cder, hC, hDp, ht₀, hCder, hs⟩ := hs 2 le_rfl
  refine ⟨t₀, Cder, ht₀, hCder, ?_⟩
  intro Q hQ β hβ P hP t ht s hst hpos j k dirs
  obtain ⟨a, μ, ha, hμ⟩ := coefficient_clock_observations Q
  have he := (hs Q hQ β a μ hβ ha hμ 0 P
    (fun r => complexL2Transpose (reducedLaw Q) (P r)) hP
    (isComplexTransposeSemigroup_complexL2Transpose Q P)).2 t ht (by simp) (by
      simpa only [norm_zero, zero_mul] using! Real.rpow_nonneg t.property η₀)
  have hmem : velocityEndpoint Q ⟨0, by omega⟩ j 0 P β a t ∈
      endpointCollection Q ⟨0, by omega⟩ 0 P
        (fun r => complexL2Transpose (reducedLaw Q) (P r)) β a μ t :=
    Or.inl (Or.inr ⟨j, rfl⟩)
  have hb := ((he _ hmem).2.2 k dirs s (by nlinarith [t.property]) hpos).2
  simp only [velocityEndpoint, zero_smul, add_zero,
    finiteXi_scalar_centered_orbit hβ hP, ENNReal.ofReal_ofNat,
    norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero, Real.exp_zero,
    mul_one, zero_mul, add_zero, ← Lp.norm_def] at hb
  apply hb.trans_eq
  rw [mul_assoc, ← Real.rpow_add hpos]
  congr 2
  ring

/-- Unit initialization includes time zero and supplies the actual averaged
drift bound throughout each structural finite horizon. -/
theorem finiteXi_scalar_initial_average_decay
    (hinit : node_p_u3A_scalar_u23_unit_u2D_initializationStmt)
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) (T : ℝ) (hT : 1 ≤ T) :
    ∃ C : ℝ, 1 ≤ C ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q) (β : Fin d → Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β →
    ∀ (P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)),
      IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ 0 P →
    ∀ t : ℝ≥0, (t : ℝ) ≤ T → ∀ s : ℝ, (t : ℝ) / 2 ≤ s → ∀ hs : 0 < s,
    ∀ j : Fin d,
      ‖gaussianAverage hd Q s hs (P t (β j))‖ ≤
        C * s ^ (-(1 / 2 + (d : ℝ) / 4)) := by
  obtain ⟨C, hC, hi⟩ := hinit d hd D (1 / 2) (by norm_num) (by norm_num)
    2 le_rfl T hT
  refine ⟨C, hC, ?_⟩
  intro Q hQ β hβ P hP t ht s hst hs j
  obtain ⟨a, μ, ha, hμ⟩ := coefficient_clock_observations Q
  have hb := (hi Q hQ β a μ hβ ha hμ 0 P
    (fun r => complexL2Transpose (reducedLaw Q) (P r)) hP
    (isComplexTransposeSemigroup_complexL2Transpose Q P) (.inl j) (by simp)
    t ht).2 s (by linarith) hs
  simpa only [indexedEndpoint, velocityEndpoint, zero_smul, add_zero,
    finiteXi_scalar_centered_orbit hβ hP, ENNReal.ofReal_ofNat, norm_zero,
    zero_mul, add_zero, ← Lp.norm_def] using hb.2

/-- The entire post-threshold time integral already has the target's factor
tau and its all-order spatial exponent. The initial interval is kept separate. -/
theorem finiteXi_scalar_late_integral_decay
    (hscalar : node_p_u3A_scalarStmt) (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) :
    ∃ t₀ : ℝ, ∃ Cder : ℕ → ℝ, 1 ≤ t₀ ∧ (∀ k, 0 < Cder k) ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q) (β : Fin d → Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β →
    ∀ (P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)),
      IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ 0 P →
    ∀ τ : ℝ≥0, t₀ ≤ (τ : ℝ) → ∀ s : ℝ, 2 * (τ : ℝ) ≤ s → ∀ hs : 0 < s,
    ∀ (i : Fin d) (k : ℕ) (dirs : Fin k → Fin d),
      ‖∫ r in Icc t₀ (τ : ℝ),
        gaussianDerivativeAverage hd Q s hs k dirs (P r.toNNReal (β i))‖ ≤
        Cder k * (τ : ℝ) * s ^ (-(1 / 2 + (d : ℝ) / 4) - (k : ℝ) / 2) := by
  obtain ⟨t₀, Cder, ht₀, hCder, hdec⟩ :=
    finiteXi_scalar_wide_derivative_decay hscalar d hd D
  refine ⟨t₀, Cder, ht₀, hCder, ?_⟩
  intro Q hQ β hβ P hP τ hτ s hst hs i k dirs
  have hb := norm_setIntegral_le_of_norm_le_const
    (μ := volume) (s := Icc t₀ (τ : ℝ))
    (f := fun r : ℝ => gaussianDerivativeAverage hd Q s hs k dirs (P r.toNNReal (β i)))
    (C := Cder k * s ^ (-(1 / 2 + (d : ℝ) / 4) - (k : ℝ) / 2))
    isCompact_Icc.measure_lt_top (fun r hr => by
      have hr0 : 0 ≤ r := le_trans (by linarith) hr.1
      exact hdec Q hQ β hβ P hP r.toNNReal
        (by simpa only [Real.coe_toNNReal r hr0] using! hr.1) s
        (by simpa only [Real.coe_toNNReal r hr0] using!
          (show 2 * r ≤ s by linarith [hr.2])) hs i k dirs)
  have hvol : volume.real (Icc t₀ (τ : ℝ)) = (τ : ℝ) - t₀ := by
    rw [Real.volume_real_Icc, max_eq_left (sub_nonneg.mpr hτ)]
  rw [hvol] at hb
  calc
    _ ≤ (Cder k * s ^ (-(1 / 2 + (d : ℝ) / 4) - (k : ℝ) / 2)) *
        ((τ : ℝ) - t₀) := hb
    _ ≤ (Cder k * s ^ (-(1 / 2 + (d : ℝ) / 4) - (k : ℝ) / 2)) * (τ : ℝ) :=
      mul_le_mul_of_nonneg_left (by linarith)
        (mul_nonneg (hCder k).le (Real.rpow_nonneg hs.le _))
    _ = _ := by ring

/-- The literal differentiated corrector splits into its initial interval and
its post-threshold interval; both are genuine Bochner integrals. -/
theorem finiteXi_scalar_corrector_split {d : ℕ} (hd : 2 ≤ d) {Λ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ r₀)
    (P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ 0 P)
    (β : Fin d → Lp ℂ 2 (reducedLaw Q)) (τ : ℝ≥0)
    (t₀ : ℝ) (ht₀ : 0 ≤ t₀) (hτ : t₀ ≤ (τ : ℝ))
    (s : ℝ) (hs : 0 < s) (i : Fin d) (k : ℕ) (dirs : Fin k → Fin d) :
    gaussianDerivativeAverage hd Q s hs k dirs
        (finiteTimeCorrector Q P hP.2.2.1 β τ i) =
      (∫ r in Icc (0 : ℝ) t₀,
        gaussianDerivativeAverage hd Q s hs k dirs (P r.toNNReal (β i))) +
      (∫ r in Icc t₀ (τ : ℝ),
        gaussianDerivativeAverage hd Q s hs k dirs (P r.toNNReal (β i))) := by
  rw [gaussianDerivativeAverage_finiteTimeCorrector hd Q ⟨0, by omega⟩ P hP β τ i]
  have hf : IntegrableOn (fun r : ℝ =>
      gaussianDerivativeAverage hd Q s hs k dirs (P r.toNNReal (β i)))
      (Icc (0 : ℝ) (τ : ℝ)) := by
    simpa only [gaussianDerivativeAverageCLM_apply] using!
      (gaussianDerivativeAverageCLM hd Q s hs k dirs).integrable_comp
        (integrableOn_finiteTimeCorrector_integrand Q ⟨0, by omega⟩ P hP β τ i)
  have ha := hf.mono_set (show Ico (0 : ℝ) t₀ ⊆ Icc (0 : ℝ) (τ : ℝ) from
    fun _ hr => ⟨hr.1, hr.2.le.trans hτ⟩)
  have hb := hf.mono_set (Icc_subset_Icc_left ht₀)
  have hdj : Disjoint (Ico (0 : ℝ) t₀) (Icc t₀ (τ : ℝ)) :=
    disjoint_left.mpr (fun _ ha hb => (not_lt_of_ge hb.1) ha.2)
  have he := setIntegral_union hdj measurableSet_Icc ha hb
  rw [Ico_union_Icc_eq_Icc ht₀ hτ, ← integral_Icc_eq_integral_Ico] at he
  exact he

open UnforcedIdentification

/-- Every coordinate derivative of a Gaussian average is its strong horizontal derivative. -/
theorem derivativeAverage_hasHorizontalDerivative {d : ℕ} (hd : 2 ≤ d) {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (s : ℝ) (hs : 0 < s)
    (k : ℕ) (dirs : Fin k → Fin d) (j : Fin d) (f : Lp ℂ 2 (reducedLaw Q)) :
    HasComplexHorizontalDerivative (reducedLaw Q) (reducedLaw_stationary Q) j
      (gaussianDerivativeAverage hd Q s hs k dirs f)
      (gaussianDerivativeAverage hd Q s hs (k + 1) (Fin.cons j dirs) f) := by
  have h := stationarySchwartzAverage_hasHorizontalDerivative Q j
    (unforcedGaussianDerivativeSchwartz Q ⟨0, by omega⟩ s hs k dirs) f
  convert h using 1
  · simp only [stationarySchwartzAverage, gaussianDerivativeAverage,
      unforcedGaussianDerivativeSchwartz_apply]
  · change _ = stationarySchwartzAverage Q
      (unforcedGaussianDerivativeSchwartz Q ⟨0, by omega⟩ s hs (k + 1)
        (Fin.cons j dirs)) f
    simp only [stationarySchwartzAverage, gaussianDerivativeAverage,
      unforcedGaussianDerivativeSchwartz_apply]

/-- All natural orders retain a half-time zero-order average of the actual datum. -/
theorem derivativeAverage_half_split {d : ℕ} (hd : 2 ≤ d) {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (s : ℝ) (hs : 0 < s)
    (k : ℕ) (dirs : Fin k → Fin d) (f : Lp ℂ 2 (reducedLaw Q)) :
    gaussianDerivativeAverage hd Q s hs k dirs f =
      gaussianDerivativeAverage hd Q (s / 2) (half_pos hs) k dirs
        (gaussianAverage hd Q (s / 2) (half_pos hs) f) := by
  induction k with
  | zero =>
    have hz (u : ℝ) (hu : 0 < u) (g : Lp ℂ 2 (reducedLaw Q)) :
        gaussianDerivativeAverage hd Q u hu 0 dirs g = gaussianAverage hd Q u hu g := by
      unfold gaussianDerivativeAverage gaussianAverage
      simp only [iteratedFDeriv_zero_apply]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        have he := homogenizedGaussianKernel_neg_force Q ⟨0, by omega⟩ u hu 0 (-x)
        simp only [neg_zero, neg_neg] at he
        dsimp only
        rw [he]
    rw [hz, hz]
    have h := homogeneousAverage_half_split hd Q s hs 0 f
    simpa only [mul_zero] using! h
  | succ k ih =>
    have hleft := derivativeAverage_hasHorizontalDerivative hd Q s hs k
      (Fin.tail dirs) (dirs 0) f
    have hright := derivativeAverage_hasHorizontalDerivative hd Q (s / 2) (half_pos hs) k
      (Fin.tail dirs) (dirs 0) (gaussianAverage hd Q (s / 2) (half_pos hs) f)
    rw [ih (Fin.tail dirs)] at hleft
    simpa only [Fin.cons_self_tail] using! hleft.unique hright

/-- Exact dilation of every coordinate derivative of the actual unforced kernel. -/
theorem derivativeKernel_scale {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (i : Fin d) (s : ℝ) (hs : 0 < s)
    (k : ℕ) (dirs : Fin k → Fin d) (x : Vec d) :
    iteratedFDeriv ℝ k (homogenizedGaussianKernel Q i s hs 0) x
        (fun j => unitVector (dirs j)) =
      (s ^ (-(d : ℝ) / 2) * (Real.sqrt s)⁻¹ ^ k) •
        iteratedFDeriv ℝ k (homogenizedGaussianKernel Q i 1 zero_lt_one 0)
          ((Real.sqrt s)⁻¹ • x) (fun j => unitVector (dirs j)) := by
  let K := homogenizedGaussianSchwartz Q i 1 zero_lt_one (by norm_num) le_rfl 0
  let A : Vec d →L[ℝ] Vec d := (Real.sqrt s)⁻¹ • ContinuousLinearMap.id ℝ (Vec d)
  have hK : (K : Vec d → ℂ) = homogenizedGaussianKernel Q i 1 zero_lt_one 0 :=
    funext (homogenizedGaussianSchwartz_apply Q i 1 zero_lt_one (by norm_num) le_rfl 0)
  have he : homogenizedGaussianKernel Q i s hs 0 =
      s ^ (-(d : ℝ) / 2) • ((K : Vec d → ℂ) ∘ A) := by
    ext y
    simpa only [Pi.smul_apply, Function.comp_apply, A, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.id_apply, hK] using homogenizedGaussianKernel_zero_scale Q i s hs y
  rw [he, iteratedFDeriv_const_smul_apply ((K.smooth k).comp A.contDiff).contDiffAt,
    A.iteratedFDeriv_comp_right (K.smooth k) x le_rfl]
  simp only [ContinuousMultilinearMap.smul_apply,
    ContinuousMultilinearMap.compContinuousLinearMap_apply, A,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply]
  rw [ContinuousMultilinearMap.map_smul_univ]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, smul_smul, hK]

/-- The all-order derivative kernel L¹ norm has exactly its parabolic scaling. -/
theorem derivativeKernel_integral_scale {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (i : Fin d) (s : ℝ) (hs : 0 < s)
    (k : ℕ) (dirs : Fin k → Fin d) :
    (∫ x : Vec d, ‖iteratedFDeriv ℝ k (homogenizedGaussianKernel Q i s hs 0) x
        (fun j => unitVector (dirs j))‖) =
      s ^ (-(k : ℝ) / 2) * ∫ x : Vec d,
        ‖iteratedFDeriv ℝ k (homogenizedGaussianKernel Q i 1 zero_lt_one 0) x
          (fun j => unitVector (dirs j))‖ := by
  simp_rw [derivativeKernel_scale Q i s hs k dirs, norm_smul,
    Real.norm_of_nonneg (show 0 ≤ s ^ (-(d : ℝ) / 2) * (Real.sqrt s)⁻¹ ^ k by positivity)]
  rw [integral_const_mul,
    Measure.integral_comp_inv_smul_of_nonneg volume
      (fun x : Vec d => ‖iteratedFDeriv ℝ k
        (homogenizedGaussianKernel Q i 1 zero_lt_one 0) x
          (fun j => unitVector (dirs j))‖) (Real.sqrt_nonneg s)]
  simp only [Module.finrank_pi, Fintype.card_fin]
  have hp (n : ℕ) : (Real.sqrt s) ^ n = s ^ ((n : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hs.le]
    congr 1
    ring
  rw [inv_pow, hp k, hp d, ← Real.rpow_neg hs.le]
  simp only [smul_eq_mul]
  rw [← mul_assoc, ← Real.rpow_add hs, ← Real.rpow_add hs]
  congr 2
  ring

/-- Structural all-order L¹ bounds, chosen before the environment law. -/
theorem exists_derivativeKernel_integral_bound (d : ℕ) (Λ : ℝ) (hΛ : 1 ≤ Λ) :
    ∃ B : ℕ → ℝ, (∀ k, 0 < B k) ∧
      ∀ (r : ℝ) (Q : EnvironmentLaw d Λ r) (i : Fin d)
        (s : ℝ) (hs : 0 < s) (k : ℕ) (dirs : Fin k → Fin d),
      (∫ x : Vec d, ‖iteratedFDeriv ℝ k (homogenizedGaussianKernel Q i s hs 0) x
        (fun j => unitVector (dirs j))‖) ≤ B k * s ^ (-(k : ℝ) / 2) := by
  let m := (volume : Measure (Vec d)).integrablePower
  let H := (2 : ℝ) ^ m * ∫ x : Vec d, (1 + ‖x‖) ^ (-(m : ℝ))
  let A (k : ℕ) := gaussianSchwartzOrderBound d Λ 0 k *
      Real.exp (gaussianSchwartzOrderBound d Λ 0 k) +
    gaussianSchwartzOrderBound d Λ m k * Real.exp (gaussianSchwartzOrderBound d Λ m k)
  have hH : 0 ≤ H := mul_nonneg (by positivity) (integral_nonneg fun x => by positivity)
  have hA (k : ℕ) : 0 ≤ A k := by
    dsimp only [A]
    exact add_nonneg (mul_nonneg (gaussianSchwartzOrderBound_pos d Λ hΛ 0 k).le
      (Real.exp_pos _).le) (mul_nonneg (gaussianSchwartzOrderBound_pos d Λ hΛ m k).le
        (Real.exp_pos _).le)
  refine ⟨fun k => H * A k + 1, fun k => add_pos_of_nonneg_of_pos (mul_nonneg hH (hA k)) zero_lt_one, ?_⟩
  intro r Q i s hs k dirs
  rw [derivativeKernel_integral_scale Q i s hs]
  have hunit (j : Fin d) : ‖unitVector j‖ = 1 := by
    unfold unitVector
    rw [Pi.norm_single, norm_one]
  let K := homogenizedGaussianSchwartz Q i 1 zero_lt_one (by norm_num) le_rfl 0
  have hK : (K : Vec d → ℂ) = homogenizedGaussianKernel Q i 1 zero_lt_one 0 :=
    funext (homogenizedGaussianSchwartz_apply Q i 1 zero_lt_one (by norm_num) le_rfl 0)
  have heval (x : Vec d) :
      ‖iteratedFDeriv ℝ k (K : Vec d → ℂ) x (fun j => unitVector (dirs j))‖ ≤
        ‖iteratedFDeriv ℝ k (K : Vec d → ℂ) x‖ := by
    simpa only [hunit, Finset.prod_const_one, mul_one] using!
      (iteratedFDeriv ℝ k (K : Vec d → ℂ) x).le_opNorm (fun j => unitVector (dirs j))
  have hi := K.integral_pow_mul_iteratedFDeriv_le ℂ volume 0 k
  simp only [pow_zero, one_mul, zero_add] at hi
  have hsemi (n : ℕ) : SchwartzMap.seminorm ℂ n k K ≤
      gaussianSchwartzOrderBound d Λ n k * Real.exp (gaussianSchwartzOrderBound d Λ n k) := by
    simpa only [norm_zero, add_zero, one_pow, mul_one] using!
      seminorm_homogenizedGaussianSchwartz_le Q i 1 zero_lt_one (by norm_num) le_rfl 0 n k
  have hb : (∫ x : Vec d, ‖iteratedFDeriv ℝ k (K : Vec d → ℂ) x
      (fun j => unitVector (dirs j))‖) ≤ H * A k + 1 := by
    calc
      _ ≤ ∫ x : Vec d, ‖iteratedFDeriv ℝ k (K : Vec d → ℂ) x‖ := by
        apply integral_mono
        · simpa only [hK, unforcedGaussianDerivativeSchwartz_apply] using!
            (unforcedGaussianDerivativeSchwartz Q i 1 zero_lt_one k dirs).integrable.norm
        · simpa only [pow_zero, one_mul] using! K.integrable_pow_mul_iteratedFDeriv volume 0 k
        · exact heval
      _ ≤ H * A k := hi.trans (mul_le_mul_of_nonneg_left (add_le_add (hsemi 0) (hsemi m)) hH)
      _ ≤ H * A k + 1 := le_add_of_nonneg_right zero_le_one
  rw [hK] at hb
  exact (mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg hs.le _)).trans_eq (mul_comm _ _)

/-- Half-scale powers retain exactly the expected spatial exponent. -/
private theorem half_scale_powers (s a b : ℝ) (hs : 0 < s) :
    (s / 2) ^ a * (s / 2) ^ b = (2 : ℝ) ^ (-(a + b)) * s ^ (a + b) := by
  rw [← Real.rpow_add (half_pos hs), Real.div_rpow hs.le (by norm_num),
    Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
  ring

/-- The initialized average transfers to every order, including at time zero. -/
theorem initial_derivative_decay
    (hinit : node_p_u3A_scalar_u23_unit_u2D_initializationStmt)
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) (T : ℝ) (hT : 1 ≤ T) :
    ∃ A : ℕ → ℝ, (∀ k, 0 < A k) ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q) (β : Fin d → Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β →
    ∀ (P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)),
      IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ 0 P →
    ∀ t : ℝ≥0, (t : ℝ) ≤ T → ∀ s : ℝ, (t : ℝ) ≤ s → ∀ hs : 0 < s,
    ∀ (i : Fin d) (k : ℕ) (dirs : Fin k → Fin d),
      ‖gaussianDerivativeAverage hd Q s hs k dirs (P t (β i))‖ ≤
        A k * s ^ (-(1 / 2 + (d : ℝ) / 4) - (k : ℝ) / 2) := by
  obtain ⟨C, hC, hav⟩ := finiteXi_scalar_initial_average_decay hinit d hd D T hT
  obtain ⟨B, hB, hb⟩ := exists_derivativeKernel_integral_bound d D.ellipticity D.one_le_ellipticity
  let h : ℝ := 1 / 2 + (d : ℝ) / 4
  refine ⟨fun k => B k * C * (2 : ℝ) ^ (h + (k : ℝ) / 2), ?_, ?_⟩
  · intro k
    exact mul_pos (mul_pos (hB k) (lt_of_lt_of_le zero_lt_one hC))
      (Real.rpow_pos_of_pos (by norm_num) _)
  intro Q hQ β hβ P hP t ht s hts hs i k dirs
  rw [derivativeAverage_half_split hd Q s hs]
  have hnorm := norm_gaussianDerivativeAverage_le hd Q (s / 2) (half_pos hs) k dirs
    (gaussianAverage hd Q (s / 2) (half_pos hs) (P t (β i)))
  have havg := hav Q hQ β hβ P hP t ht (s / 2) (by linarith) (half_pos hs) i
  calc
    _ ≤ (B k * (s / 2) ^ (-(k : ℝ) / 2)) *
        (C * (s / 2) ^ (-h)) := hnorm.trans (mul_le_mul
      (hb _ Q _ (s / 2) (half_pos hs) k dirs) havg (norm_nonneg _)
      (mul_nonneg (hB k).le (Real.rpow_nonneg (half_pos hs).le _)))
    _ = B k * C * ((s / 2) ^ (-(k : ℝ) / 2) * (s / 2) ^ (-h)) := by ring
    _ = _ := by
      rw [half_scale_powers s _ _ hs]
      have ha : -(k : ℝ) / 2 + -h = -h - (k : ℝ) / 2 := by ring
      rw [ha, show -(-h - (k : ℝ) / 2) = h + (k : ℝ) / 2 by ring]
      ring

end EinsteinFull.Blueprint.ScalarIntegral

namespace EinsteinFull.Blueprint
open EinsteinRelation ScalarIntegral

/-- The literal finite-time scalar corrector satisfies the all-order wide
Gaussian derivative bound, including its entire initial time interval. -/
theorem node_l_u3A_finite_u2D_xi_u23_scalar_u2D_integral_of_deps
    (hscalar : node_p_u3A_scalarStmt)
    (hinit : node_p_u3A_scalar_u23_unit_u2D_initializationStmt) :
    node_l_u3A_finite_u2D_xi_u23_scalar_u2D_integralStmt := by
  intro d hd D
  obtain ⟨t₀, Cder, ht₀, hCder, hlate⟩ := finiteXi_scalar_late_integral_decay hscalar d hd D
  obtain ⟨A, hA, hinitial⟩ := initial_derivative_decay hinit d hd D t₀ ht₀
  refine ⟨t₀, fun k => A k + Cder k, ht₀,
    fun k => add_pos (hA k) (hCder k), ?_⟩
  intro Q hQ β hβ P hP τ hτ s hst hs i k _hk dirs
  have htpos : 0 ≤ t₀ := le_trans zero_le_one ht₀
  have hbound := norm_setIntegral_le_of_norm_le_const
    (μ := volume) (s := Icc (0 : ℝ) t₀)
    (f := fun r : ℝ => gaussianDerivativeAverage hd Q s hs k dirs (P r.toNNReal (β i)))
    (C := A k * s ^ (-(1 / 2 + (d : ℝ) / 4) - (k : ℝ) / 2))
    isCompact_Icc.measure_lt_top (fun r hr => by
      apply hinitial Q hQ β hβ P hP r.toNNReal
      · simpa only [Real.coe_toNNReal r hr.1] using! hr.2
      · simpa only [Real.coe_toNNReal r hr.1] using!
          (show r ≤ s by linarith [hr.2, τ.property]))
  have hvol : volume.real (Icc (0 : ℝ) t₀) = t₀ := by
    rw [Real.volume_real_Icc, sub_zero, max_eq_left htpos]
  rw [hvol] at hbound
  have hintegral : ‖∫ r in Icc (0 : ℝ) t₀,
      gaussianDerivativeAverage hd Q s hs k dirs (P r.toNNReal (β i))‖ ≤
      A k * (τ : ℝ) * s ^ (-(1 / 2 + (d : ℝ) / 4) - (k : ℝ) / 2) := by
    calc
      _ ≤ (A k * s ^ (-(1 / 2 + (d : ℝ) / 4) - (k : ℝ) / 2)) * t₀ := hbound
      _ ≤ (A k * s ^ (-(1 / 2 + (d : ℝ) / 4) - (k : ℝ) / 2)) * (τ : ℝ) :=
        mul_le_mul_of_nonneg_left hτ (mul_nonneg (hA k).le (Real.rpow_nonneg hs.le _))
      _ = _ := by ring
  rw [finiteXi_scalar_corrector_split hd Q P hP β τ t₀ htpos hτ s hs i k dirs]
  exact (norm_add_le _ _).trans ((add_le_add hintegral
    (hlate Q hQ β hβ P hP τ hτ s hst hs i k dirs)).trans_eq (by ring))

end EinsteinFull.Blueprint
