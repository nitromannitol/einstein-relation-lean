import EinsteinFull.Calculus.C18PhysicalEvolutionSmoothing
import EinsteinFull.Calculus.C3SublinearSmoothBootstrap
import EinsteinFull.Calculus.PhysicalH1CongruenceSupport
import SuperdiffusionCLT.Probability.HonestSliceStep
import Mathlib.Analysis.Normed.Lp.SmoothApprox

open MeasureTheory Filter
open scoped NNReal ENNReal BigOperators Topology

namespace EinsteinFull
open EinsteinRelation

/-- The standard reciprocal scale provides nonzero admissible signed steps
converging to zero. -/
theorem c24_quotient_scale_properties :
    (∀ n, 0 < |Blueprint.C3SublinearC1.mollifierScale n| ∧
      |Blueprint.C3SublinearC1.mollifierScale n| ≤ 1) ∧
    Tendsto Blueprint.C3SublinearC1.mollifierScale atTop (𝓝[≠] (0 : ℝ)) := by
  constructor
  · intro n
    have hp := Blueprint.C3SublinearC1.mollifierScale_pos n
    rw [abs_of_pos hp]
    refine ⟨hp, ?_⟩
    change 1 / (n + 1 : ℝ) ≤ 1
    exact (div_le_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) n])
  · exact Blueprint.C3SublinearC1.mollifierScale_tendsto.mono_right (nhdsGT_le_nhdsNE 0)

/-- A uniformly bounded finite family in physical L² has a simultaneous weak
cluster point, retaining the sum-of-squares bound. -/
theorem c24_physical_L2_family_weak_compactness {d m : ℕ}
    (q : ℕ → Fin m → Lp ℂ 2 (volume : Measure (Vec d))) (R : ℝ)
    (hR : 0 ≤ R) (hq : ∀ n, ∑ j, ‖q n j‖ ^ 2 ≤ R ^ 2) :
    ∃ Q : Fin m → Lp ℂ 2 (volume : Measure (Vec d)),
      (∑ j, ‖Q j‖ ^ 2) ≤ R ^ 2 ∧
      ∃ l : Filter ℕ, l.NeBot ∧ l ≤ atTop ∧
        ∀ j (v : Lp ℂ 2 (volume : Measure (Vec d))),
          Tendsto (fun n => inner ℝ (q n j) v) l (𝓝 (inner ℝ (Q j) v)) := by
  let V : ℕ → PiLp 2 (fun _ : Fin m => Lp ℂ 2 (volume : Measure (Vec d))) :=
    fun n => WithLp.toLp 2 (q n)
  have hV (n : ℕ) : ‖V n‖ ≤ R := by
    have hsq : ‖V n‖ ^ 2 ≤ R ^ 2 := by
      simpa only [V, PiLp.norm_sq_eq_of_L2, WithLp.ofLp_toLp] using hq n
    nlinarith [norm_nonneg (V n)]
  obtain ⟨w, hw, l, hl, hltop, hweak⟩ :=
    Blueprint.C3SublinearSmooth.exists_weak_limit_of_norm_bound V hV
  refine ⟨WithLp.ofLp w, ?_, l, hl, hltop, ?_⟩
  · rw [← PiLp.norm_sq_eq_of_L2]
    nlinarith [norm_nonneg w]
  · intro j v
    have ht := Blueprint.C3SublinearSmooth.tendsto_inner_clm_of_tendsto_inner hweak
      (PiLp.proj (𝕜 := ℝ) 2
        (fun _ : Fin m => Lp ℂ 2 (volume : Measure (Vec d))) j) v
    simpa only [V, PiLp.proj_apply, PiLp.toLp_apply] using ht

/-- Pairing a whole-space real difference quotient with a smooth compactly
supported test converges to the distributional derivative pairing. -/
theorem c24_real_quotient_test_limit {d : ℕ}
    (u : Lp ℝ 2 (volume : Measure (Vec d))) (i : Fin d)
    {U : Set (Vec d)} [IsFiniteMeasure (volume.restrict U)]
    (hUopen : IsOpen U) (hUbd : Bornology.IsBounded U)
    {ψ : Vec d → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψU : tsupport ψ ⊆ U) (hcpt : HasCompactSupport ψ)
    {s : ℕ → ℝ} (hs : Tendsto s atTop (𝓝[≠] (0 : ℝ))) :
    Tendsto (fun n => ∫ x, Homogenization.euclideanForwardDifferenceQuotient
      (s n) i u x * ψ x) atTop
      (𝓝 (-(∫ x in U, u x * Homogenization.euclideanCoordDeriv i ψ x))) := by
  let μ : Measure (Vec d) := volume
  have hu : MemLp (u : Vec d → ℝ) 2 (μ.restrict U) :=
    (Lp.memLp u).mono_measure Measure.restrict_le_self
  have hp : MemLp ψ 2 μ := hψ.continuous.memLp_of_hasCompactSupport hcpt
  have ht := (SuperdiffusionCLT.Probability.Stationary.tendsto_setIntegral_mul_backwardDifferenceQuotient
    hUbd hu hψ hψU i).comp hs
  obtain ⟨δ, hδ0, hδU⟩ := hcpt.exists_cthickening_subset_open hUopen hψU
  have hev : ∀ᶠ h : ℝ in 𝓝[≠] (0 : ℝ), ‖h • Homogenization.basisVec i‖ ≤ δ := by
    have hcont : Continuous fun h : ℝ => ‖h • Homogenization.basisVec i‖ :=
      continuous_norm.comp (continuous_id.smul continuous_const)
    have hlt : ∀ᶠ h : ℝ in 𝓝 (0 : ℝ), ‖h • Homogenization.basisVec i‖ < δ :=
      (hcont.tendsto 0).eventually (Iio_mem_nhds (by simpa using hδ0))
    exact (hlt.mono fun _ hh => le_of_lt hh).filter_mono nhdsWithin_le_nhds
  apply ht.neg.congr'
  filter_upwards [hs.eventually hev] with n hn
  have hthick : Metric.cthickening ‖(-(s n)) • Homogenization.basisVec i‖ (tsupport ψ) ⊆ U :=
    fun x hx => hδU (Metric.cthickening_mono (by simpa only [neg_smul, norm_neg] using hn)
      (tsupport ψ) hx)
  have hmp := measurePreserving_add_right μ (s n • Homogenization.basisVec i)
  have hmm := measurePreserving_add_right μ ((-s n) • Homogenization.basisVec i)
  have h1 : Integrable (fun x : Vec d => u (Homogenization.euclideanCoordShift (s n) i x) * ψ x) := by
    apply ((Lp.memLp u).comp_measurePreserving hmp).integrable_mul hp
  have h2 : Integrable (fun x : Vec d => u x * ψ x) := (Lp.memLp u).integrable_mul hp
  have h3 : Integrable (fun x : Vec d => u x * ψ (Homogenization.euclideanCoordShift (-s n) i x)) := by
    apply (Lp.memLp u).integrable_mul (hp.comp_measurePreserving hmm)
  rw [SuperdiffusionCLT.Probability.Stationary.integral_euclideanForwardDifferenceQuotient_mul_eq_neg_of_integrable
    (s n) i h1 h2 h3,
    SuperdiffusionCLT.Probability.Stationary.integral_mul_euclideanBackwardDifferenceQuotient_eq_setIntegral
      (s n) i hthick]
  rfl

/-- The quotient test limit also applies to L² representatives of the
actual pointwise difference quotients. -/
theorem c24_real_L2_quotient_test_limit {d : ℕ}
    (u : Lp ℝ 2 (volume : Measure (Vec d))) (i : Fin d)
    {U : Set (Vec d)} [IsFiniteMeasure (volume.restrict U)]
    (hUopen : IsOpen U) (hUbd : Bornology.IsBounded U)
    {ψ : Vec d → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψU : tsupport ψ ⊆ U) (hcpt : HasCompactSupport ψ)
    {s : ℕ → ℝ} (hs : Tendsto s atTop (𝓝[≠] (0 : ℝ)))
    (q : ℕ → Lp ℝ 2 (volume : Measure (Vec d)))
    (hq : ∀ n, (q n : Vec d → ℝ) =ᵐ[volume]
      (fun x => Homogenization.euclideanForwardDifferenceQuotient (s n) i u x)) :
    Tendsto (fun n => inner ℝ (q n)
      ((hψ.continuous.memLp_of_hasCompactSupport hcpt (μ := (volume : Measure (Vec d)))
        (p := 2)).toLp ψ)) atTop
      (𝓝 (-(∫ x in U, u x * Homogenization.euclideanCoordDeriv i ψ x))) := by
  let hp : MemLp ψ 2 (volume : Measure (Vec d)) :=
    hψ.continuous.memLp_of_hasCompactSupport hcpt
  have ht := c24_real_quotient_test_limit u i hUopen hUbd hψ hψU hcpt hs
  apply ht.congr
  intro n
  simp only [L2.inner_def, RCLike.inner_apply', conj_trivial]
  apply integral_congr_ae
  filter_upwards [hq n, hp.coeFn_toLp] with x hqx hpx
  rw [hqx, hpx]

/-- Pairings of real quotient representatives converge to the supplied weak
coordinate derivative on each smooth compactly supported test. -/
theorem c24_real_L2_quotient_weak_derivative_limit {d : ℕ}
    (u g : Lp ℝ 2 (volume : Measure (Vec d))) (i : Fin d)
    (hg : HasWeakPartialDerivative Set.univ i u g)
    {U : Set (Vec d)} [IsFiniteMeasure (volume.restrict U)]
    (hUopen : IsOpen U) (hUbd : Bornology.IsBounded U)
    {ψ : Vec d → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψU : tsupport ψ ⊆ U) (hcpt : HasCompactSupport ψ)
    {s : ℕ → ℝ} (hs : Tendsto s atTop (𝓝[≠] (0 : ℝ)))
    (q : ℕ → Lp ℝ 2 (volume : Measure (Vec d)))
    (hq : ∀ n, (q n : Vec d → ℝ) =ᵐ[volume]
      (fun x => Homogenization.euclideanForwardDifferenceQuotient (s n) i u x)) :
    Tendsto (fun n => inner ℝ (q n)
      ((hψ.continuous.memLp_of_hasCompactSupport hcpt (μ := (volume : Measure (Vec d)))
        (p := 2)).toLp ψ)) atTop
      (𝓝 (inner ℝ g
        ((hψ.continuous.memLp_of_hasCompactSupport hcpt (μ := (volume : Measure (Vec d)))
          (p := 2)).toLp ψ))) := by
  let hp : MemLp ψ 2 (volume : Measure (Vec d)) :=
    hψ.continuous.memLp_of_hasCompactSupport hcpt
  have hset : (∫ x in U, u x * Homogenization.euclideanCoordDeriv i ψ x) =
      ∫ x, u x * coordinateDerivative i ψ x := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
    · rfl
    · intro x hx
      simp only [Homogenization.euclideanCoordDeriv,
        fderiv_of_notMem_tsupport ℝ (fun ht => hx (hψU ht)),
        zero_apply, mul_zero]
  have hpair : inner ℝ g (hp.toLp ψ) = ∫ x, g x * ψ x := by
    simp only [L2.inner_def, RCLike.inner_apply', conj_trivial]
    exact integral_congr_ae (hp.coeFn_toLp.mono fun x hx => by
      change g x * _ = g x * _
      rw [hx])
  have hweak := hg.2.2 ψ ⟨hψ, hcpt, Set.subset_univ _⟩
  simp only [Measure.restrict_univ] at hweak
  have ht := c24_real_L2_quotient_test_limit u i hUopen hUbd hψ hψU hcpt hs q hq
  rw [hset, hweak, neg_neg, ← hpair] at ht
  exact ht

/-- A complex physical L² function is the sum of its real component and
`I` times its imaginary component, both embedded in complex L². -/
theorem c24_physical_L2_real_imag_decomposition {d : ℕ}
    (f : Lp ℂ 2 (volume : Measure (Vec d))) :
    Complex.ofRealCLM.compLpL 2 volume (Complex.reCLM.compLpL 2 volume f) +
      Complex.I • Complex.ofRealCLM.compLpL 2 volume (Complex.imCLM.compLpL 2 volume f) = f := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_add
      (Complex.ofRealCLM.compLpL 2 volume (Complex.reCLM.compLpL 2 volume f))
      (Complex.I • Complex.ofRealCLM.compLpL 2 volume (Complex.imCLM.compLpL 2 volume f)),
    Lp.coeFn_smul Complex.I (Complex.ofRealCLM.compLpL 2 volume (Complex.imCLM.compLpL 2 volume f)),
    Complex.ofRealCLM.coeFn_compLpL (Complex.reCLM.compLpL 2 volume f),
    Complex.ofRealCLM.coeFn_compLpL (Complex.imCLM.compLpL 2 volume f),
    Complex.reCLM.coeFn_compLpL f, Complex.imCLM.coeFn_compLpL f]
    with x ha hb hc hd he hh
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at ha hb
  rw [ha, hb, hc, hd, he, hh]
  simpa only [Complex.ofRealCLM_apply, Complex.reCLM_apply, Complex.imCLM_apply,
    mul_comm Complex.I] using Complex.re_add_im (f x)

/-- Weak convergence of both real components implies weak convergence of the
complex L² sequence. -/
theorem c24_physical_L2_weak_of_components {d : ℕ}
    (q : ℕ → Lp ℂ 2 (volume : Measure (Vec d)))
    (g : Lp ℂ 2 (volume : Measure (Vec d))) (l : Filter ℕ)
    (hr : ∀ v : Lp ℝ 2 (volume : Measure (Vec d)),
      Tendsto (fun n => inner ℝ (Complex.reCLM.compLpL 2 volume (q n)) v) l
        (𝓝 (inner ℝ (Complex.reCLM.compLpL 2 volume g) v)))
    (hi : ∀ v : Lp ℝ 2 (volume : Measure (Vec d)),
      Tendsto (fun n => inner ℝ (Complex.imCLM.compLpL 2 volume (q n)) v) l
        (𝓝 (inner ℝ (Complex.imCLM.compLpL 2 volume g) v))) :
    ∀ v : Lp ℂ 2 (volume : Measure (Vec d)),
      Tendsto (fun n => inner ℝ (q n) v) l (𝓝 (inner ℝ g v)) := by
  let A := Complex.ofRealCLM.compLpL 2 (volume : Measure (Vec d))
  let B := (Complex.I • Complex.ofRealCLM).compLpL 2 (volume : Measure (Vec d))
  have hB (u : Lp ℝ 2 (volume : Measure (Vec d))) : B u = Complex.I • A u := by
    apply Lp.ext
    filter_upwards [(Complex.I • Complex.ofRealCLM).coeFn_compLpL u,
      Complex.ofRealCLM.coeFn_compLpL u, Lp.coeFn_smul Complex.I (A u)]
      with x hb ha hc
    simp only [B, A, Pi.smul_apply, smul_eq_mul, smul_apply] at hb ha hc ⊢
    rw [hb, hc, ha]
  intro v
  have ht := (Blueprint.C3SublinearSmooth.tendsto_inner_clm_of_tendsto_inner hr A v).add
    (Blueprint.C3SublinearSmooth.tendsto_inner_clm_of_tendsto_inner hi B v)
  simp only [hB, ← inner_add_left] at ht
  dsimp only [A] at ht
  simp only [c24_physical_L2_real_imag_decomposition] at ht
  exact ht

/-- Real smooth compactly supported functions are dense in physical L². -/
theorem c24_dense_real_smooth_tests {d : ℕ} :
    Dense {v : Lp ℝ 2 (volume : Measure (Vec d)) |
      ∃ ψ : Vec d → ℝ, v =ᵐ[volume] ψ ∧ HasCompactSupport ψ ∧
        ContDiff ℝ (⊤ : ℕ∞) ψ} := by
  exact Lp.dense_hasCompactSupport_contDiff (by norm_num)

/-- Weak cluster points are identified by their pairings with any dense
family of test vectors. -/
theorem c24_weak_limit_eq_of_dense_tests
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v : ℕ → E) (w u : E) (l : Filter ℕ) [l.NeBot]
    (S : Set E) (hS : Dense S)
    (hw : ∀ y : E, Tendsto (fun n => inner ℝ (v n) y) l (𝓝 (inner ℝ w y)))
    (hu : ∀ y ∈ S, Tendsto (fun n => inner ℝ (v n) y) l (𝓝 (inner ℝ u y))) :
    w = u := by
  apply hS.eq_of_inner_left ℝ
  intro y hy
  exact tendsto_nhds_unique (hw y) (hu y hy)

/-- A weak cluster point of the actual real difference quotients is the
supplied weak derivative. -/
theorem c24_real_quotient_cluster_eq_derivative {d : ℕ}
    (u g w : Lp ℝ 2 (volume : Measure (Vec d))) (i : Fin d)
    (hg : HasWeakPartialDerivative Set.univ i u g)
    {s : ℕ → ℝ} (hs : Tendsto s atTop (𝓝[≠] (0 : ℝ)))
    (q : ℕ → Lp ℝ 2 (volume : Measure (Vec d)))
    (hq : ∀ n, (q n : Vec d → ℝ) =ᵐ[volume]
      (fun x => Homogenization.euclideanForwardDifferenceQuotient (s n) i u x))
    (l : Filter ℕ) [l.NeBot] (hlt : l ≤ atTop)
    (hw : ∀ v : Lp ℝ 2 (volume : Measure (Vec d)),
      Tendsto (fun n => inner ℝ (q n) v) l (𝓝 (inner ℝ w v))) : w = g := by
  apply c24_weak_limit_eq_of_dense_tests q w g l _ c24_dense_real_smooth_tests hw
  intro v hv
  obtain ⟨ψ, hvψ, hcpt, hψ⟩ := hv
  obtain ⟨R, hR, hψR⟩ := hcpt.isCompact.isBounded.subset_ball_lt 0 0
  let _ : IsFiniteMeasure (volume.restrict (Metric.ball (0 : Vec d) R)) := ⟨by simpa using (measure_ball_lt_top (μ := (volume : Measure (Vec d)))
      (x := (0 : Vec d)) (r := R))⟩
  let hp : MemLp ψ 2 (volume : Measure (Vec d)) :=
    hψ.continuous.memLp_of_hasCompactSupport hcpt
  have hv' : v = hp.toLp ψ := by
    apply Lp.ext
    exact hvψ.trans hp.coeFn_toLp.symm
  subst v
  exact (c24_real_L2_quotient_weak_derivative_limit u g i hg
    Metric.isOpen_ball Metric.isBounded_ball hψ hψR hcpt hs q hq).mono_left hlt

/-- The real and imaginary components of a complex coordinate quotient are
the actual real coordinate quotients of the corresponding components. -/
theorem c24_complex_quotient_components {d : ℕ}
    (f q : Lp ℂ 2 (volume : Measure (Vec d))) (i : Fin d) (h : ℝ)
    (hq : (q : Vec d → ℂ) =ᵐ[volume]
      (fun x => (f (x + h • unitVector i) - f x) / (h : ℂ))) :
    ((Complex.reCLM.compLpL 2 volume q : Vec d → ℝ) =ᵐ[volume]
      (fun x => Homogenization.euclideanForwardDifferenceQuotient h i
        (Complex.reCLM.compLpL 2 volume f) x)) ∧
    ((Complex.imCLM.compLpL 2 volume q : Vec d → ℝ) =ᵐ[volume]
      (fun x => Homogenization.euclideanForwardDifferenceQuotient h i
        (Complex.imCLM.compLpL 2 volume f) x)) := by
  have hr := Complex.reCLM.coeFn_compLpL f
  have hi := Complex.imCLM.coeFn_compLpL f
  have hm := (measurePreserving_add_right (volume : Measure (Vec d))
    (h • unitVector i)).quasiMeasurePreserving
  have hrs := hm.ae hr
  have his := hm.ae hi
  constructor
  · filter_upwards [Complex.reCLM.coeFn_compLpL q, hq, hr, hrs] with x h1 h2 h3 h4
    simp only [Complex.reCLM_apply] at h1 h3 h4
    rw [h1, h2]
    simp only [unitVector] at h3 h4
    simp only [Homogenization.euclideanForwardDifferenceQuotient,
      Homogenization.euclideanCoordShift, Homogenization.basisVec, unitVector]
    simp only [h3, h4, div_eq_mul_inv, ← Complex.ofReal_inv, Complex.mul_re,
      Complex.sub_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  · filter_upwards [Complex.imCLM.coeFn_compLpL q, hq, hi, his] with x h1 h2 h3 h4
    simp only [Complex.imCLM_apply] at h1 h3 h4
    rw [h1, h2]
    simp only [unitVector] at h3 h4
    simp only [Homogenization.euclideanForwardDifferenceQuotient,
      Homogenization.euclideanCoordShift, Homogenization.basisVec, unitVector]
    simp only [h3, h4, div_eq_mul_inv, ← Complex.ofReal_inv, Complex.mul_im,
      Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add]

/-- A complex quotient weak cluster point is the supplied H1 gradient. -/
theorem c24_complex_quotient_cluster_eq_gradient {d : ℕ}
    (f w : Lp ℂ 2 (volume : Measure (Vec d)))
    (G : Fin d → Lp ℂ 2 (volume : Measure (Vec d))) (i : Fin d)
    (hG : IsPhysicalH1Graph volume (Or.inl rfl) f G)
    {s : ℕ → ℝ} (hs : Tendsto s atTop (𝓝[≠] (0 : ℝ)))
    (q : ℕ → Lp ℂ 2 (volume : Measure (Vec d)))
    (hq : ∀ n, (q n : Vec d → ℂ) =ᵐ[volume]
      (fun x => (f (x + s n • unitVector i) - f x) / (s n : ℂ)))
    (l : Filter ℕ) [l.NeBot] (hlt : l ≤ atTop)
    (hw : ∀ v : Lp ℂ 2 (volume : Measure (Vec d)),
      Tendsto (fun n => inner ℝ (q n) v) l (𝓝 (inner ℝ w v))) : w = G i := by
  have hpart (L : ℂ →L[ℝ] ℝ)
      (hweak : HasWeakPartialDerivative Set.univ i
        (fun x => L (f x)) (fun x => L (G i x)))
      (hqL : ∀ n, (L.compLpL 2 volume (q n) : Vec d → ℝ) =ᵐ[volume]
        (fun x => Homogenization.euclideanForwardDifferenceQuotient (s n) i
          (L.compLpL 2 volume f) x)) :
      L.compLpL 2 volume w = L.compLpL 2 volume (G i) := by
    have hderiv : HasWeakPartialDerivative Set.univ i
        (L.compLpL 2 volume f) (L.compLpL 2 volume (G i)) :=
      (hasWeakPartialDerivative_congr_of_absolutelyContinuous volume
        Measure.AbsolutelyContinuous.rfl i (L.coeFn_compLpL f)
        (L.coeFn_compLpL (G i))).mpr hweak
    apply c24_real_quotient_cluster_eq_derivative _ _ _ i hderiv hs _ hqL l hlt
    intro v
    exact Blueprint.C3SublinearSmooth.tendsto_inner_clm_of_tendsto_inner hw
      (L.compLpL 2 volume) v
  have hr := hpart Complex.reCLM (hG.1 i)
    (fun n => (c24_complex_quotient_components f (q n) i (s n) (hq n)).1)
  have hi := hpart Complex.imCLM (hG.2 i)
    (fun n => (c24_complex_quotient_components f (q n) i (s n) (hq n)).2)
  rw [← c24_physical_L2_real_imag_decomposition w,
    ← c24_physical_L2_real_imag_decomposition (G i), hr, hi]

/-- Distributional derivatives are preserved by simultaneous weak L² limits. -/
theorem c24_weak_partial_derivative_of_weak_limit {d : ℕ} (i : Fin d)
    (f g : Lp ℝ 2 (volume : Measure (Vec d)))
    (fn gn : ℕ → Lp ℝ 2 (volume : Measure (Vec d)))
    (l : Filter ℕ) [l.NeBot]
    (hf : ∀ v : Lp ℝ 2 (volume : Measure (Vec d)),
      Tendsto (fun n => inner ℝ (fn n) v) l (𝓝 (inner ℝ f v)))
    (hg : ∀ v : Lp ℝ 2 (volume : Measure (Vec d)),
      Tendsto (fun n => inner ℝ (gn n) v) l (𝓝 (inner ℝ g v)))
    (hn : ∀ n, HasWeakPartialDerivative Set.univ i (fn n) (gn n)) :
    HasWeakPartialDerivative Set.univ i f g := by
  refine ⟨locallyIntegrableOn_univ.mpr ((Lp.memLp f).locallyIntegrable (by norm_num)),
    locallyIntegrableOn_univ.mpr ((Lp.memLp g).locallyIntegrable (by norm_num)), ?_⟩
  intro φ hφ
  have hd : Continuous (coordinateDerivative i φ) :=
    (hφ.1.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdc : HasCompactSupport (coordinateDerivative i φ) :=
    hφ.2.1.fderiv_apply ℝ (unitVector i)
  have hm := hd.memLp_of_hasCompactSupport hdc (μ := (volume : Measure (Vec d))) (p := 2)
  have hp := hφ.1.continuous.memLp_of_hasCompactSupport hφ.2.1
    (μ := (volume : Measure (Vec d))) (p := 2)
  let v := hm.toLp (coordinateDerivative i φ)
  let w := hp.toLp φ
  have hpair (u : Lp ℝ 2 (volume : Measure (Vec d))) :
      inner ℝ u v = ∫ x, u x * coordinateDerivative i φ x := by
    simp only [L2.inner_def, RCLike.inner_apply', conj_trivial]
    exact integral_congr_ae (hm.coeFn_toLp.mono fun x hx => by
      change u x * _ = u x * _
      rw [hx])
  have hpair' (u : Lp ℝ 2 (volume : Measure (Vec d))) :
      inner ℝ u w = ∫ x, u x * φ x := by
    simp only [L2.inner_def, RCLike.inner_apply', conj_trivial]
    exact integral_congr_ae (hp.coeFn_toLp.mono fun x hx => by
      change u x * _ = u x * _
      rw [hx])
  have hl := hf v
  have hr := (hg w).neg
  simp only [hpair] at hl
  simp only [hpair'] at hr
  simp only [Measure.restrict_univ]
  apply tendsto_nhds_unique hl
  exact hr.congr (fun n => by simpa only [Measure.restrict_univ] using ((hn n).2.2 φ hφ).symm)

/-- The physical H1 graph is stable under simultaneous weak L² limits. -/
theorem c24_physical_H1_graph_of_weak_limit {d : ℕ}
    (f : Lp ℂ 2 (volume : Measure (Vec d)))
    (G : Fin d → Lp ℂ 2 (volume : Measure (Vec d)))
    (fn : ℕ → Lp ℂ 2 (volume : Measure (Vec d)))
    (Gn : ℕ → Fin d → Lp ℂ 2 (volume : Measure (Vec d)))
    (l : Filter ℕ) [l.NeBot]
    (hf : ∀ v : Lp ℂ 2 (volume : Measure (Vec d)),
      Tendsto (fun n => inner ℝ (fn n) v) l (𝓝 (inner ℝ f v)))
    (hG : ∀ j v, Tendsto (fun n => inner ℝ (Gn n j) v) l (𝓝 (inner ℝ (G j) v)))
    (hn : ∀ n, IsPhysicalH1Graph volume (Or.inl rfl) (fn n) (Gn n)) :
    IsPhysicalH1Graph volume (Or.inl rfl) f G := by
  have hpart (L : ℂ →L[ℝ] ℝ) (j : Fin d)
      (h : ∀ n, HasWeakPartialDerivative Set.univ j
        (fun x => L (fn n x)) (fun x => L (Gn n j x))) :
      HasWeakPartialDerivative Set.univ j
        (fun x => L (f x)) (fun x => L (G j x)) := by
    let A : Lp ℂ 2 (volume : Measure (Vec d)) →L[ℝ]
        Lp ℝ 2 (volume : Measure (Vec d)) := L.compLpL 2 volume
    have hc (u v : Lp ℂ 2 (volume : Measure (Vec d))) :
        HasWeakPartialDerivative Set.univ j (A u) (A v) ↔
          HasWeakPartialDerivative Set.univ j
            (fun x => L (u x)) (fun x => L (v x)) :=
      hasWeakPartialDerivative_congr_of_absolutelyContinuous volume
        Measure.AbsolutelyContinuous.rfl j (L.coeFn_compLpL u) (L.coeFn_compLpL v)
    apply (hc f (G j)).mp
    apply c24_weak_partial_derivative_of_weak_limit j (A f) (A (G j))
      (fun n => A (fn n)) (fun n => A (Gn n j)) l
    · intro v
      exact Blueprint.C3SublinearSmooth.tendsto_inner_clm_of_tendsto_inner hf A v
    · intro v
      exact Blueprint.C3SublinearSmooth.tendsto_inner_clm_of_tendsto_inner (hG j) A v
    · intro n
      exact (hc (fn n) (Gn n j)).mpr (h n)
  constructor
  · intro j
    exact hpart Complex.reCLM j (fun n => (hn n).1 j)
  · intro j
    exact hpart Complex.imCLM j (fun n => (hn n).2 j)

/-- A bounded family of physical H1 quotients whose values have a weak limit
has a physical H1 limit with the same gradient-energy bound. -/
theorem c24_physical_H1_of_bounded_weak_quotients {d : ℕ}
    (u : Lp ℂ 2 (volume : Measure (Vec d)))
    (q : ℕ → Lp ℂ 2 (volume : Measure (Vec d)))
    (Q : ℕ → Fin d → Lp ℂ 2 (volume : Measure (Vec d)))
    (R : ℝ) (hR : 0 ≤ R)
    (hbound : ∀ n, ∑ j, ‖Q n j‖ ^ 2 ≤ R ^ 2)
    (hgraph : ∀ n, IsPhysicalH1Graph volume (Or.inl rfl) (q n) (Q n))
    (hvalue : ∀ v : Lp ℂ 2 (volume : Measure (Vec d)),
      Tendsto (fun n => inner ℝ (q n) v) atTop (𝓝 (inner ℝ u v))) :
    ∃ H : Fin d → Lp ℂ 2 (volume : Measure (Vec d)),
      IsPhysicalH1Graph volume (Or.inl rfl) u H ∧
        ∑ j, ‖H j‖ ^ 2 ≤ R ^ 2 := by
  obtain ⟨H, hH, l, hl, hltop, hweak⟩ :=
    c24_physical_L2_family_weak_compactness Q R hR hbound
  let _ : l.NeBot := hl
  refine ⟨H, ?_, hH⟩
  exact c24_physical_H1_graph_of_weak_limit u H q Q l
    (fun v => (hvalue v).mono_left hltop) hweak hgraph

/-- Extract the gradient part of a weakly convergent family of quotient graphs. -/
private theorem c24_graph_of_cons_weak_limit {d : ℕ}
    (q : ℕ → Lp ℂ 2 (volume : Measure (Vec d)))
    (Q : ℕ → Fin d → Lp ℂ 2 (volume : Measure (Vec d)))
    (W : Fin (d + 1) → Lp ℂ 2 (volume : Measure (Vec d)))
    (R : ℝ) (l : Filter ℕ) [l.NeBot]
    (hW : ∑ j, ‖W j‖ ^ 2 ≤ R ^ 2)
    (hw0 : ∀ v, Tendsto (fun n => inner ℝ (q n) v) l (𝓝 (inner ℝ (W 0) v)))
    (hwQ : ∀ j v, Tendsto (fun n => inner ℝ (Q n j) v) l
      (𝓝 (inner ℝ (W j.succ) v)))
    (hgraph : ∀ n, IsPhysicalH1Graph volume (Or.inl rfl) (q n) (Q n)) :
    IsPhysicalH1Graph volume (Or.inl rfl) (W 0) (fun j => W j.succ) ∧
      (∑ j : Fin d, ‖W j.succ‖ ^ 2) ≤ R ^ 2 := by
  constructor
  · exact c24_physical_H1_graph_of_weak_limit (W 0) (fun j => W j.succ)
      q Q l hw0 hwQ hgraph
  · rw [Fin.sum_univ_succ] at hW
    exact (le_add_of_nonneg_left (sq_nonneg ‖W 0‖)).trans hW

private theorem c24_cons_energy {d : ℕ}
    (q : Lp ℂ 2 (volume : Measure (Vec d)))
    (Q : Fin d → Lp ℂ 2 (volume : Measure (Vec d))) :
    (∑ j : Fin (d + 1),
      ‖(Fin.cons (α := fun _ => Lp ℂ 2 (volume : Measure (Vec d))) q Q) j‖ ^ 2) =
      ‖q‖ ^ 2 + ∑ j, ‖Q j‖ ^ 2 := by
  rw [Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]

private theorem c24_compact_cons {d : ℕ}
    (q : ℕ → Lp ℂ 2 (volume : Measure (Vec d)))
    (Q : ℕ → Fin d → Lp ℂ 2 (volume : Measure (Vec d)))
    (R : ℝ) (hR : 0 ≤ R)
    (hbound : ∀ n, ‖q n‖ ^ 2 + (∑ j, ‖Q n j‖ ^ 2) ≤ R ^ 2) :
    ∃ (W : Fin (d + 1) → Lp ℂ 2 (volume : Measure (Vec d))) (l : Filter ℕ),
      l.NeBot ∧ l ≤ atTop ∧ (∑ j, ‖W j‖ ^ 2 ≤ R ^ 2) ∧
      (∀ v : Lp ℂ 2 (volume : Measure (Vec d)),
        Tendsto (fun n => inner ℝ (q n) v) l (𝓝 (inner ℝ (W 0) v))) ∧
      (∀ (j : Fin d) (v : Lp ℂ 2 (volume : Measure (Vec d))),
        Tendsto (fun n => inner ℝ (Q n j) v) l (𝓝 (inner ℝ (W j.succ) v))) := by
  let V : ℕ → Fin (d + 1) → Lp ℂ 2 (volume : Measure (Vec d)) :=
    fun n => Fin.cons (α := fun _ => Lp ℂ 2 (volume : Measure (Vec d))) (q n) (Q n)
  have hV : ∀ n, ∑ j, ‖V n j‖ ^ 2 ≤ R ^ 2 := by
    intro n
    rw [show (∑ j, ‖V n j‖ ^ 2) = ‖q n‖ ^ 2 + ∑ j, ‖Q n j‖ ^ 2 from
      c24_cons_energy (q n) (Q n)]
    exact hbound n
  obtain ⟨W, hW, l, hl, hltop, hw⟩ :=
    c24_physical_L2_family_weak_compactness V R hR hV
  refine ⟨W, l, hl, hltop, hW, ?_, ?_⟩
  · intro v
    simpa only [V, Fin.cons_zero] using hw 0 v
  · intro j v
    simpa only [V, Fin.cons_succ] using hw j.succ v

private theorem c24_compact_quotient_graph {d : ℕ}
    (q : ℕ → Lp ℂ 2 (volume : Measure (Vec d)))
    (Q : ℕ → Fin d → Lp ℂ 2 (volume : Measure (Vec d)))
    (R : ℝ) (hR : 0 ≤ R)
    (hbound : ∀ n, ‖q n‖ ^ 2 + (∑ j, ‖Q n j‖ ^ 2) ≤ R ^ 2)
    (hgraph : ∀ n, IsPhysicalH1Graph volume (Or.inl rfl) (q n) (Q n)) :
    ∃ (W : Fin (d + 1) → Lp ℂ 2 (volume : Measure (Vec d))) (l : Filter ℕ),
      l.NeBot ∧ l ≤ atTop ∧
      (∀ v : Lp ℂ 2 (volume : Measure (Vec d)),
        Tendsto (fun n => inner ℝ (q n) v) l (𝓝 (inner ℝ (W 0) v))) ∧
      IsPhysicalH1Graph volume (Or.inl rfl) (W 0) (fun j => W j.succ) ∧
      (∑ j : Fin d, ‖W j.succ‖ ^ 2) ≤ R ^ 2 := by
  obtain ⟨W, l, hl, hltop, hW, hw0, hwQ⟩ := c24_compact_cons q Q R hR hbound
  let _ : l.NeBot := hl
  obtain ⟨hgraphW, hboundW⟩ :=
    c24_graph_of_cons_weak_limit q Q W R l hW hw0 hwQ hgraph
  exact ⟨W, l, hl, hltop, hw0, hgraphW, hboundW⟩

/-- Bounded quotient graphs need only converge against a dense set of tests:
compactness identifies their value limit and preserves the derivative graph. -/
theorem c24_physical_H1_of_dense_test_quotients {d : ℕ}
    (u : Lp ℂ 2 (volume : Measure (Vec d)))
    (q : ℕ → Lp ℂ 2 (volume : Measure (Vec d)))
    (Q : ℕ → Fin d → Lp ℂ 2 (volume : Measure (Vec d)))
    (R : ℝ) (hR : 0 ≤ R)
    (hbound : ∀ n, ‖q n‖ ^ 2 + (∑ j, ‖Q n j‖ ^ 2) ≤ R ^ 2)
    (hgraph : ∀ n, IsPhysicalH1Graph volume (Or.inl rfl) (q n) (Q n))
    (S : Set (Lp ℂ 2 (volume : Measure (Vec d)))) (hS : Dense S)
    (hvalue : ∀ v ∈ S,
      Tendsto (fun n => inner ℝ (q n) v) atTop (𝓝 (inner ℝ u v))) :
    ∃ H : Fin d → Lp ℂ 2 (volume : Measure (Vec d)),
      IsPhysicalH1Graph volume (Or.inl rfl) u H ∧
        ∑ j, ‖H j‖ ^ 2 ≤ R ^ 2 := by
  obtain ⟨W, l, hl, hltop, hw0, hgraphW, hboundW⟩ :=
    c24_compact_quotient_graph q Q R hR hbound hgraph
  let _ : l.NeBot := hl
  have hzero : W 0 = u := by
    apply c24_weak_limit_eq_of_dense_tests q (W 0) u l S hS hw0
    intro v hv
    exact (hvalue v hv).mono_left hltop
  refine ⟨fun j => W j.succ, ?_, hboundW⟩
  rw [hzero] at hgraphW
  exact hgraphW

/-- Bounded actual coordinate quotient graphs give an H1 graph for the
corresponding component of the original supplied gradient. -/
theorem c24_physical_H1_of_actual_quotients {d : ℕ}
    (f : Lp ℂ 2 (volume : Measure (Vec d)))
    (G : Fin d → Lp ℂ 2 (volume : Measure (Vec d))) (i : Fin d)
    (hG : IsPhysicalH1Graph volume (Or.inl rfl) f G)
    {s : ℕ → ℝ} (hs : Tendsto s atTop (𝓝[≠] (0 : ℝ)))
    (q : ℕ → Lp ℂ 2 (volume : Measure (Vec d)))
    (Q : ℕ → Fin d → Lp ℂ 2 (volume : Measure (Vec d)))
    (R : ℝ) (hR : 0 ≤ R)
    (hq : ∀ n, (q n : Vec d → ℂ) =ᵐ[volume]
      (fun x => (f (x + s n • unitVector i) - f x) / (s n : ℂ)))
    (hbound : ∀ n, ‖q n‖ ^ 2 + (∑ j, ‖Q n j‖ ^ 2) ≤ R ^ 2)
    (hgraph : ∀ n, IsPhysicalH1Graph volume (Or.inl rfl) (q n) (Q n)) :
    ∃ H : Fin d → Lp ℂ 2 (volume : Measure (Vec d)),
      IsPhysicalH1Graph volume (Or.inl rfl) (G i) H ∧
        ∑ j, ‖H j‖ ^ 2 ≤ R ^ 2 := by
  obtain ⟨W, l, hl, hltop, hw0, hgraphW, hboundW⟩ :=
    c24_compact_quotient_graph q Q R hR hbound hgraph
  let _ : l.NeBot := hl
  have hzero : W 0 = G i :=
    c24_complex_quotient_cluster_eq_gradient f (W 0) G i hG hs q hq l hltop hw0
  refine ⟨fun j => W j.succ, ?_, hboundW⟩
  rw [hzero] at hgraphW
  exact hgraphW

/-- A uniform bound on the actual coordinate quotient graphs yields H2
regularity for the same supplied gradient. -/
theorem c24_physical_H2_of_actual_quotients {d : ℕ}
    (f : Lp ℂ 2 (volume : Measure (Vec d)))
    (G : Fin d → Lp ℂ 2 (volume : Measure (Vec d)))
    (hG : IsPhysicalH1Graph volume (Or.inl rfl) f G)
    {s : ℕ → ℝ} (hs : Tendsto s atTop (𝓝[≠] (0 : ℝ)))
    (q : Fin d → ℕ → Lp ℂ 2 (volume : Measure (Vec d)))
    (Q : Fin d → ℕ → Fin d → Lp ℂ 2 (volume : Measure (Vec d)))
    (R : ℝ) (hR : 0 ≤ R)
    (hq : ∀ i n, (q i n : Vec d → ℂ) =ᵐ[volume]
      (fun x => (f (x + s n • unitVector i) - f x) / (s n : ℂ)))
    (hbound : ∀ i n, ‖q i n‖ ^ 2 + (∑ j, ‖Q i n j‖ ^ 2) ≤ R ^ 2)
    (hgraph : ∀ i n, IsPhysicalH1Graph volume (Or.inl rfl) (q i n) (Q i n)) :
    ∃ H : Fin d → Fin d → Lp ℂ 2 (volume : Measure (Vec d)),
      IsPhysicalH1Graph volume (Or.inl rfl) f G ∧
      (∀ i, IsPhysicalH1Graph volume (Or.inl rfl) (G i) (H i)) ∧
      (∑ i, ∑ j, ‖H i j‖ ^ 2) ≤ (d : ℝ) * R ^ 2 := by
  classical
  have hex : ∀ i, ∃ H : Fin d → Lp ℂ 2 (volume : Measure (Vec d)),
      IsPhysicalH1Graph volume (Or.inl rfl) (G i) H ∧
        ∑ j, ‖H j‖ ^ 2 ≤ R ^ 2 := by
    intro i
    exact c24_physical_H1_of_actual_quotients f G i hG hs (q i) (Q i) R hR
      (hq i) (hbound i) (hgraph i)
  choose H hgraph' hbound' using hex
  refine ⟨H, hG, hgraph', ?_⟩
  calc
    (∑ i, ∑ j, ‖H i j‖ ^ 2) ≤ ∑ _i : Fin d, R ^ 2 :=
      Finset.sum_le_sum (fun i _ => hbound' i)
    _ = (d : ℝ) * R ^ 2 := by simp

/-- An energy bound on the actual gradient difference quotients yields an
H2 graph for the supplied H1 gradient. -/
theorem c24_physical_H2_of_gradient_quotient_energy {d : ℕ}
    (f : Lp ℂ 2 (volume : Measure (Vec d)))
    (G : Fin d → Lp ℂ 2 (volume : Measure (Vec d)))
    (hG : IsPhysicalH1Graph volume (Or.inl rfl) f G)
    (R : ℝ) (hR : 0 ≤ R)
    (henergy : ∀ (i : Fin d) (h : ℝ), 0 < |h| → |h| ≤ 1 →
      ‖G i‖ ^ 2 + ∑ j, ((eLpNorm
        (fun x => (G j (x + h • unitVector i) - G j x) / (h : ℂ))
        2 (volume : Measure (Vec d))).toReal) ^ 2 ≤ R ^ 2) :
    ∃ H : Fin d → Fin d → Lp ℂ 2 (volume : Measure (Vec d)),
      IsPhysicalH1Graph volume (Or.inl rfl) f G ∧
      (∀ i, IsPhysicalH1Graph volume (Or.inl rfl) (G i) (H i)) ∧
      (∑ i, ∑ j, ‖H i j‖ ^ 2) ≤ (d : ℝ) * R ^ 2 := by
  classical
  let s := Blueprint.C3SublinearC1.mollifierScale
  have hscale := c24_quotient_scale_properties
  have hex : ∀ (i : Fin d) (n : ℕ), ∃ (q : Lp ℂ 2 (volume : Measure (Vec d)))
      (Q : Fin d → Lp ℂ 2 (volume : Measure (Vec d))),
      IsPhysicalH1Graph volume (Or.inl rfl) q Q ∧
      (q : Vec d → ℂ) =ᵐ[volume]
        (fun x => (f (x + s n • unitVector i) - f x) / (s n : ℂ)) ∧
      ‖q‖ ^ 2 + (∑ j, ‖Q j‖ ^ 2) ≤ R ^ 2 := by
    intro i n
    obtain ⟨q, Q, hqG, hq, hQ⟩ :=
      c18_physical_H1_difference_quotient hG (-(s n • unitVector i)) (s n)
    have hq' : (q : Vec d → ℂ) =ᵐ[volume]
        (fun x => (f (x + s n • unitVector i) - f x) / (s n : ℂ)) := by
      simpa only [sub_neg_eq_add, div_eq_mul_inv, mul_comm] using hq
    have hQ' (j : Fin d) : (Q j : Vec d → ℂ) =ᵐ[volume]
        (fun x => (G j (x + s n • unitVector i) - G j x) / (s n : ℂ)) := by
      simpa only [sub_neg_eq_add, div_eq_mul_inv, mul_comm] using hQ j
    have hn : s n ≠ 0 := abs_pos.mp (hscale.1 n).1
    have hb := c18_physical_H1_coordinate_difference_quotient_bound hG i (s n) hn
    rw [← eLpNorm_congr_ae hq', ← Lp.norm_def] at hb
    have he := henergy i (s n) (hscale.1 n).1 (hscale.1 n).2
    have heq (j : Fin d) :
        (eLpNorm (fun x => (G j (x + s n • unitVector i) - G j x) /
          (s n : ℂ)) 2 (volume : Measure (Vec d))).toReal = ‖Q j‖ := by
      rw [← eLpNorm_congr_ae (hQ' j), ← Lp.norm_def]
    simp only [heq] at he
    refine ⟨q, Q, hqG, hq', ?_⟩
    nlinarith [norm_nonneg q, norm_nonneg (G i)]
  choose q Q hgraph hq hbound using hex
  exact c24_physical_H2_of_actual_quotients f G hG hscale.2 q Q R hR
    hq hbound hgraph

/-- A common gradient-energy bound for each coordinate quotient gives H2
regularity and the corresponding finite sum bound. -/
theorem c24_physical_H2_of_bounded_weak_quotients {d : ℕ}
    (f : Lp ℂ 2 (volume : Measure (Vec d)))
    (G : Fin d → Lp ℂ 2 (volume : Measure (Vec d)))
    (q : Fin d → ℕ → Lp ℂ 2 (volume : Measure (Vec d)))
    (Q : Fin d → ℕ → Fin d → Lp ℂ 2 (volume : Measure (Vec d)))
    (R : ℝ) (hR : 0 ≤ R)
    (hG : IsPhysicalH1Graph volume (Or.inl rfl) f G)
    (hbound : ∀ j n, ∑ k, ‖Q j n k‖ ^ 2 ≤ R ^ 2)
    (hgraph : ∀ j n, IsPhysicalH1Graph volume (Or.inl rfl) (q j n) (Q j n))
    (hvalue : ∀ j (v : Lp ℂ 2 (volume : Measure (Vec d))),
      Tendsto (fun n => inner ℝ (q j n) v) atTop (𝓝 (inner ℝ (G j) v))) :
    ∃ H : Fin d → Fin d → Lp ℂ 2 (volume : Measure (Vec d)),
      IsPhysicalH1Graph volume (Or.inl rfl) f G ∧
      (∀ j, IsPhysicalH1Graph volume (Or.inl rfl) (G j) (H j)) ∧
      (∑ j, ∑ k, ‖H j k‖ ^ 2) ≤ (d : ℝ) * R ^ 2 := by
  classical
  have hex : ∀ j, ∃ H : Fin d → Lp ℂ 2 (volume : Measure (Vec d)),
      IsPhysicalH1Graph volume (Or.inl rfl) (G j) H ∧
        ∑ k, ‖H k‖ ^ 2 ≤ R ^ 2 := by
    intro j
    exact c24_physical_H1_of_bounded_weak_quotients (G j) (q j) (Q j) R hR
      (hbound j) (hgraph j) (hvalue j)
  choose H hgraph' hbound' using hex
  refine ⟨H, hG, hgraph', ?_⟩
  calc
    (∑ j, ∑ k, ‖H j k‖ ^ 2) ≤ ∑ _j : Fin d, R ^ 2 :=
      Finset.sum_le_sum (fun j _ => hbound' j)
    _ = (d : ℝ) * R ^ 2 := by simp

/-- Dense-test convergence and a common bound on quotient graphs give
coordinatewise H2 regularity with a finite total energy bound. -/
theorem c24_physical_H2_of_dense_test_quotients {d : ℕ}
    (f : Lp ℂ 2 (volume : Measure (Vec d)))
    (G : Fin d → Lp ℂ 2 (volume : Measure (Vec d)))
    (q : Fin d → ℕ → Lp ℂ 2 (volume : Measure (Vec d)))
    (Q : Fin d → ℕ → Fin d → Lp ℂ 2 (volume : Measure (Vec d)))
    (R : ℝ) (hR : 0 ≤ R)
    (hG : IsPhysicalH1Graph volume (Or.inl rfl) f G)
    (hbound : ∀ j n, ‖q j n‖ ^ 2 + (∑ k, ‖Q j n k‖ ^ 2) ≤ R ^ 2)
    (hgraph : ∀ j n, IsPhysicalH1Graph volume (Or.inl rfl) (q j n) (Q j n))
    (S : Set (Lp ℂ 2 (volume : Measure (Vec d)))) (hS : Dense S)
    (hvalue : ∀ j v, v ∈ S →
      Tendsto (fun n => inner ℝ (q j n) v) atTop (𝓝 (inner ℝ (G j) v))) :
    ∃ H : Fin d → Fin d → Lp ℂ 2 (volume : Measure (Vec d)),
      IsPhysicalH1Graph volume (Or.inl rfl) f G ∧
      (∀ j, IsPhysicalH1Graph volume (Or.inl rfl) (G j) (H j)) ∧
      (∑ j, ∑ k, ‖H j k‖ ^ 2) ≤ (d : ℝ) * R ^ 2 := by
  classical
  have hex : ∀ j, ∃ H : Fin d → Lp ℂ 2 (volume : Measure (Vec d)),
      IsPhysicalH1Graph volume (Or.inl rfl) (G j) H ∧
        ∑ k, ‖H k‖ ^ 2 ≤ R ^ 2 := by
    intro j
    exact c24_physical_H1_of_dense_test_quotients (G j) (q j) (Q j) R hR
      (hbound j) (hgraph j) S hS (hvalue j)
  choose H hgraph' hbound' using hex
  refine ⟨H, hG, hgraph', ?_⟩
  calc
    (∑ j, ∑ k, ‖H j k‖ ^ 2) ≤ ∑ _j : Fin d, R ^ 2 :=
      Finset.sum_le_sum (fun j _ => hbound' j)
    _ = (d : ℝ) * R ^ 2 := by simp


/-- Combine first-gradient and actual difference-quotient energy estimates to
obtain a quantitative H2 bound for the same physical gradient. -/
theorem c24_physical_H2_of_separate_energy_bounds {d : ℕ}
    (f : Lp ℂ 2 (volume : Measure (Vec d)))
    (G : Fin d → Lp ℂ 2 (volume : Measure (Vec d)))
    (hG : IsPhysicalH1Graph volume (Or.inl rfl) f G)
    (A B E : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hE : 0 ≤ E)
    (hfirst : (∑ j, ‖G j‖ ^ 2) ≤ A * E)
    (hquotient : ∀ (i : Fin d) (h : ℝ), 0 < |h| → |h| ≤ 1 →
      (∑ j, ((eLpNorm
        (fun x => (G j (x + h • unitVector i) - G j x) / (h : ℂ))
        2 (volume : Measure (Vec d))).toReal) ^ 2) ≤ B * E) :
    ∃ H : Fin d → Fin d → Lp ℂ 2 (volume : Measure (Vec d)),
      (∀ i, IsPhysicalH1Graph volume (Or.inl rfl) (G i) (H i)) ∧
      (∑ i, ‖G i‖ ^ 2) + (∑ i, ∑ j, ‖H i j‖ ^ 2) ≤
        (A + (d : ℝ) * (A + B)) * E := by
  classical
  have hsum : 0 ≤ (A + B) * E := mul_nonneg (add_nonneg hA hB) hE
  have henergy : ∀ (i : Fin d) (h : ℝ), 0 < |h| → |h| ≤ 1 →
      ‖G i‖ ^ 2 + ∑ j, ((eLpNorm
        (fun x => (G j (x + h • unitVector i) - G j x) / (h : ℂ))
        2 (volume : Measure (Vec d))).toReal) ^ 2 ≤
        (Real.sqrt ((A + B) * E)) ^ 2 := by
    intro i h hh hh1
    have hi : ‖G i‖ ^ 2 ≤ ∑ j, ‖G j‖ ^ 2 :=
      Finset.single_le_sum (fun j _ => sq_nonneg ‖G j‖) (Finset.mem_univ i)
    rw [Real.sq_sqrt hsum]
    have hq := hquotient i h hh hh1
    nlinarith only [hi, hfirst, hq]
  obtain ⟨H, _, hH, hbound⟩ :=
    c24_physical_H2_of_gradient_quotient_energy f G hG
      (Real.sqrt ((A + B) * E)) (Real.sqrt_nonneg _) henergy
  refine ⟨H, hH, ?_⟩
  rw [Real.sq_sqrt hsum] at hbound
  nlinarith only [hfirst, hbound]


/-- The actual forward or transpose generator graph provides a first-gradient
bound in the L2 graph norm, with a constant independent of the functions. -/
theorem c24_physical_generator_pair_first_gradient {d : ℕ} {Λ : ℝ}
    {M : ℕ → ℝ} {ω : FieldPair d} {i : Fin d} {ζ : ℂ}
    (hΛ : 1 ≤ Λ) (hell : IsElliptic Λ ω.1) (hsmooth : IsSmoothWithBounds M ω)
    (f g : Lp ℂ 2 (volume : Measure (Vec d)))
    (hfg : IsPhysicalComplexGeneratorPair ω.1 i ζ f g ∨
      IsPhysicalComplexTransposeGeneratorPair ω.1 i ζ f g) :
    ∃ G : Fin d → Lp ℂ 2 (volume : Measure (Vec d)),
      IsPhysicalH1Graph volume (Or.inl rfl) f G ∧
      (∑ j, ‖G j‖ ^ 2) ≤
        (4 * Λ + 4 * ((d : ℝ) + 1) ^ 2 * Λ ^ 4 * ‖ζ‖ ^ 2) *
          (‖f‖ ^ 2 + ‖g‖ ^ 2) := by
  have hΛ0 : 0 < Λ := lt_of_lt_of_le zero_lt_one hΛ
  have ha : ∀ j k, MemLp (fun x => (ω.1 x j k : ℂ)) ∞ volume :=
    memLp_complex_elliptic_entry volume ω.1 Λ hΛ0 hell
      (fun j k => (hsmooth.1.1 j k).continuous)
  have hA : ∀ᵐ x ∂volume, S5Elliptic (ω.1 x) Λ :=
    Filter.Eventually.of_forall (s5Elliptic_of_isElliptic hΛ hell)
  have hex : ∃ G : Fin d → Lp ℂ 2 (volume : Measure (Vec d)),
      IsPhysicalH1Graph volume (Or.inl rfl) f G ∧
      (∑ j, ‖G j‖ ^ 2) ≤ 4 * Λ * ‖f‖ * ‖g‖ +
        4 * ((d : ℝ) + 1) ^ 2 * Λ ^ 4 * ‖ζ‖ ^ 2 * ‖f‖ ^ 2 := by
    rcases hfg with hf | hf
    · exact Blueprint.physical_complex_generator_gradient_bound ω.1 i ζ ha hΛ0 hA hf
    · exact Blueprint.physical_complex_transpose_generator_gradient_bound ω.1 i ζ ha hΛ0 hA hf
  obtain ⟨G, hG, hbound⟩ := hex
  refine ⟨G, hG, hbound.trans ?_⟩
  have hproduct : ‖f‖ * ‖g‖ ≤ ‖f‖ ^ 2 + ‖g‖ ^ 2 := by
    nlinarith [sq_nonneg (‖f‖ - ‖g‖)]
  have hmul := mul_le_mul_of_nonneg_left hproduct (show 0 ≤ 4 * Λ by positivity)
  have hrest : 0 ≤ (4 * ((d : ℝ) + 1) ^ 2 * Λ ^ 4 * ‖ζ‖ ^ 2) * ‖g‖ ^ 2 := by
    positivity
  nlinarith only [hmul, hrest]

end EinsteinFull
