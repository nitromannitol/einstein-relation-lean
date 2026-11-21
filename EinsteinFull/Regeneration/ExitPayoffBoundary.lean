import EinsteinFull.Regeneration.ExitPayoffContinuity
import EinsteinFull.Calculus.C16SourceExponentialMax
import EinsteinFull.Calculus.C16ReducedMPExistence
import EinsteinFull.Calculus.U5RegularPhysicalCompensator
import EinsteinFull.Calculus.U6RegularUnforcedRealization
import EinsteinFull.Calculus.U8RegularExitTails

/-!
# Exit payoffs at boundary points

A coordinate exponential is a strict subsolution of the regular generator at almost every
point once its rate is large. Dynkin's formula for it, stopped at the exit from a small
ball cut by a supporting coordinate half-space, bounds the expected time spent before the
half-space is crossed by a quantity that vanishes with the distance to the hyperplane.
Together with the Gaussian bound on early displacement, this shows that the diffusion
started close to a boundary point of a coordinate-convex set exits close to that point,
so exit payoffs are continuous at every boundary point.
-/

open MeasureTheory ProbabilityTheory Filter Set EinsteinRelation EinsteinRelation.Diffusion
open EinsteinRelation.External.GantertSection7Support
open scoped NNReal ENNReal Topology

namespace EinsteinFull.Regeneration

/-- A coordinate is bounded by the Euclidean norm. -/
theorem abs_apply_le_euclideanNorm {d : ℕ} (v : Vec d) (j : Fin d) :
    |v j| ≤ euclideanNorm v := by
  apply Real.le_sqrt_of_sq_le
  rw [sq_abs]
  change v j ^ 2 ≤ ∑ k : Fin d, v k * v k
  simpa only [pow_two] using
    (Finset.single_le_sum (fun k _ => mul_self_nonneg (v k)) (Finset.mem_univ j))

/-- The sup norm is bounded by the Euclidean norm. -/
theorem norm_le_euclideanNorm {d : ℕ} (v : Vec d) : ‖v‖ ≤ euclideanNorm v := by
  apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr
  intro j
  rw [Real.norm_eq_abs]
  exact abs_apply_le_euclideanNorm v j

/-- A large coordinate exponential rate makes the exponential a strict subsolution of the
regular generator at almost every point, with a rate uniform over the coordinate and the
sign of the exponent. -/
theorem exists_coordinate_exp_subsolution {d : ℕ} (hd : 2 ≤ d) {Λ : ℝ} (hΛ : 1 ≤ Λ)
    {ω : FieldPair d} (hω : IsRegular Λ ω) (lam : ℝ) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ᵐ y ∂(volume : Measure (Vec d)), ∀ (j : Fin d) (q : ℝ), |q| = κ →
      κ * Real.exp (q * y j) ≤
        physicalGenerator (firstCoordinateIndex hd) ω lam (fun z => Real.exp (q * z j)) y := by
  obtain ⟨_, _, _, ⟨c, hc, hell⟩, _, ⟨M, hM⟩⟩ :=
    EinsteinFull.physical_svHypotheses (lt_of_lt_of_le zero_lt_one hΛ) hω
      (firstCoordinateIndex hd) lam
  let κ : ℝ := 2 * (|M| + 1) / c
  have hκ : 0 < κ := by positivity
  refine ⟨κ, hκ, ?_⟩
  filter_upwards [EinsteinFull.u2_regular_physical_generator_ae_textbook hd ω lam Λ hΛ hω]
    with y hy
  intro j q hq
  have hsmooth : ContDiff ℝ 2 (fun z : Vec d => Real.exp (q * z j)) :=
    (contDiff_const.mul (contDiff_apply ℝ ℝ j)).exp
  rw [hy _ hsmooth, EinsteinFull.c16_svGenerator_coordinate_exp]
  have hajj : c ≤ ω.1 y j j := by
    have h := hell y (unitVector j)
    have hsq : euclideanSq (unitVector j : Vec d) = 1 := by
      simp [euclideanSq, dot, unitVector, Pi.single_apply]
    have hdot : dot (unitVector j : Vec d) ((ω.1 y).mulVec (unitVector j)) = ω.1 y j j := by
      simp [dot, unitVector, Matrix.mulVec, dotProduct, Pi.single_apply]
    rw [hsq, hdot, mul_one] at h
    exact h
  have hb : -(κ * |M|) ≤ q * EinsteinFull.physicalDrift ω (firstCoordinateIndex hd) lam y j := by
    have h1 := hM y j
    have h2 : |q * EinsteinFull.physicalDrift ω (firstCoordinateIndex hd) lam y j| ≤ κ * |M| := by
      rw [abs_mul, hq]
      exact mul_le_mul_of_nonneg_left (h1.trans (le_abs_self M)) hκ.le
    exact (abs_le.mp h2).1
  have hq2 : q ^ 2 = κ ^ 2 := by rw [← sq_abs, hq]
  have hquad : κ ^ 2 / 2 * c ≤ q ^ 2 / 2 * ω.1 y j j := by
    rw [hq2]
    exact mul_le_mul_of_nonneg_left hajj (by positivity)
  have hkey : κ ^ 2 / 2 * c = κ * (|M| + 1) := by
    simp only [κ]
    field_simp
  have hsum : κ ≤ q * EinsteinFull.physicalDrift ω (firstCoordinateIndex hd) lam y j +
      q ^ 2 / 2 * ω.1 y j j := by
    nlinarith [abs_nonneg M]
  rw [mul_comm κ]
  exact mul_le_mul_of_nonneg_left hsum (Real.exp_pos _).le


/-- A path integral up to a measurable random time is measurable in the path. -/
theorem measurable_stopped_pathIntegral {d : ℕ} (g : Vec d → ℝ) (hg : Measurable g)
    (T : Path d → ℝ≥0) (hT : Measurable T) :
    Measurable (fun γ : Path d => ∫ s in (0 : ℝ)..(T γ : ℝ), g (γ s.toNNReal)) := by
  have heval : Measurable (fun p : Path d × ℝ => p.1 p.2.toNNReal) :=
    (continuous_eval.comp (continuous_fst.prodMk
      (continuous_real_toNNReal.comp continuous_snd))).measurable
  have hset : MeasurableSet {p : Path d × ℝ | p.2 ∈ Set.Ioc (0 : ℝ) (T p.1 : ℝ)} := by
    have h1 : MeasurableSet {p : Path d × ℝ | 0 < p.2} :=
      measurableSet_lt measurable_const measurable_snd
    have h2 : MeasurableSet {p : Path d × ℝ | p.2 ≤ (T p.1 : ℝ)} :=
      measurableSet_le measurable_snd (measurable_coe_nnreal_real.comp (hT.comp measurable_fst))
    exact h1.inter h2
  have hJ : Measurable (fun p : Path d × ℝ =>
      {p : Path d × ℝ | p.2 ∈ Set.Ioc (0 : ℝ) (T p.1 : ℝ)}.indicator
        (fun p => g (p.1 p.2.toNNReal)) p) :=
    (hg.comp heval).indicator hset
  have he : (fun γ : Path d => ∫ s in (0 : ℝ)..(T γ : ℝ), g (γ s.toNNReal)) =
      fun γ => ∫ s, {p : Path d × ℝ | p.2 ∈ Set.Ioc (0 : ℝ) (T p.1 : ℝ)}.indicator
        (fun p => g (p.1 p.2.toNNReal)) (γ, s) := by
    funext γ
    rw [intervalIntegral.integral_of_le (T γ).coe_nonneg, ← integral_indicator measurableSet_Ioc]
    rfl
  rw [he]
  exact (hJ.stronglyMeasurable.integral_prod_right' (ν := (volume : Measure ℝ))).measurable

variable {d : ℕ} {hd : 2 ≤ d} {L : ℝ} {hL : 1 ≤ L} {ω : FieldPair d} {hω : IsRegular L ω}
  {lam : ℝ} {h₀ : 0 ≤ lam} {h₁ : lam ≤ 1}

/-- Dynkin's formula for a coordinate exponential subsolution: before leaving a ball of
radius `η` or crossing the hyperplane `q y_j = b`, the expected elapsed time is at most
`(e^{b - q x_j} - 1) e^{κ η} / κ`. -/
theorem integral_exitTimeTrunc_le_of_subsolution
    (G : GantertFixedEnvironmentRealization hd L hL ω hω lam h₀ h₁) (κ : ℝ) (hκ : 0 < κ)
    (hsub : ∀ᵐ y ∂(volume : Measure (Vec d)), ∀ (j : Fin d) (q : ℝ), |q| = κ →
      κ * Real.exp (q * y j) ≤
        physicalGenerator (firstCoordinateIndex hd) ω lam (fun z => Real.exp (q * z j)) y)
    (j : Fin d) (q : ℝ) (hq : |q| = κ) (b : ℝ) (x : Vec d) (hx : q * x j < b)
    (η : ℝ) (hη : 0 < η) (t : ℝ≥0) :
    ∫ γ, ((MarkovProcess.ContinuousPath.exitTimeTrunc
        ({y : Vec d | euclideanNorm (y - x) < η} ∩ {y : Vec d | q * y j < b}) t γ : ℝ≥0) : ℝ)
        ∂G.pathLaw x ≤
      (Real.exp (b - q * x j) - 1) * Real.exp (κ * η) / κ := by
  let K := G.pathLaw
  have : IsMarkovKernel K := G.pathLaw_isMarkovKernel
  have : IsProbabilityMeasure (K x) := G.pathLaw_isMarkovKernel.isProbabilityMeasure x
  have hfdd := EinsteinFull.u6_arbitrary_supplied_gmp_canonical_FDD hd ω lam L hL hω h₀ h₁ G
  let W : Set (Vec d) := {y : Vec d | euclideanNorm (y - x) < η} ∩ {y : Vec d | q * y j < b}
  have hcontj : Continuous (fun y : Vec d => q * y j) := continuous_const.mul (continuous_apply j)
  have hcontn : Continuous (fun y : Vec d => euclideanNorm (y - x)) :=
    (Calculus.Feller.continuous_euclideanNorm d).comp (continuous_id.sub continuous_const)
  have hWopen : IsOpen W :=
    (isOpen_lt hcontn continuous_const).inter (isOpen_lt hcontj continuous_const)
  have hxW : x ∈ W := by
    refine ⟨?_, hx⟩
    simp only [Set.mem_ofPred_eq, sub_self]
    simpa [euclideanNorm, euclideanSq, dot] using hη
  let T : Path d → ℝ≥0 := MarkovProcess.ContinuousPath.exitTimeTrunc W t
  have hT : IsStoppingTime (MarkovProcess.ContinuousPath.canonicalFiltration (alpha := Vec d))
      (fun γ => (T γ : WithTop ℝ≥0)) :=
    MarkovProcess.ContinuousPath.isStoppingTime_exitTimeTrunc W hWopen t
  have hTt : ∀ γ, T γ ≤ t := fun γ => MarkovProcess.ContinuousPath.exitTimeTrunc_le W t γ
  have hTm : Measurable T := MarkovProcess.ContinuousPath.measurable_of_isStoppingTime T hT
  -- the cutoff barrier
  let χ : ContDiffBump x := ⟨2 * η, 3 * η, by positivity, by linarith⟩
  let v : Vec d → ℝ := fun y => Real.exp (q * y j)
  let u : Vec d → ℝ := fun y => χ y * v y
  have hv : ContDiff ℝ (⊤ : ℕ∞) v := (contDiff_const.mul (contDiff_apply ℝ ℝ j)).exp
  have hu : ContDiff ℝ (⊤ : ℕ∞) u := χ.contDiff.mul hv
  have huc : HasCompactSupport u := χ.hasCompactSupport.mul_right
  have hloc : ∀ y : Vec d, euclideanNorm (y - x) ≤ η → u =ᶠ[𝓝 y] v := by
    intro y hy
    filter_upwards [Metric.ball_mem_nhds y hη] with y' hy'
    have hdist : dist y' x ≤ 2 * η := by
      calc dist y' x ≤ dist y' y + dist y x := dist_triangle _ _ _
        _ ≤ η + η := by
            refine add_le_add (le_of_lt hy') ?_
            rw [dist_eq_norm]
            exact (norm_le_euclideanNorm _).trans hy
        _ = 2 * η := by ring
    have h1 : χ y' = 1 := χ.one_of_mem_closedBall (Metric.mem_closedBall.mpr hdist)
    simp only [u, h1, one_mul]
  have hD := EinsteinFull.u5_regular_physical_compensated_stopping_mean_zero hd ω lam L hL hω K
    hfdd x u hu huc T hT t hTt
  -- the path bound
  let Lg := physicalGenerator (firstCoordinateIndex hd) ω lam
  obtain ⟨Bg, hBg0, hBg⟩ := EinsteinFull.sbxS4_physicalGenerator_bounded hd
    (firstCoordinateIndex hd) (lt_of_lt_of_le zero_lt_one hL) hω lam hu huc
  have hLgm : Measurable (Lg u) := measurable_physicalGenerator _ ω lam u
  let c' : ℝ := κ * Real.exp (q * x j - κ * η)
  have hpath := EinsteinFull.c16_ae_path_of_averaged_occupation (K x)
    (EinsteinFull.u6_fixed_environment_realization_occupation_ac hd hL ω hω lam h₀ h₁ G x) hsub
  have hbound : ∀ᵐ γ ∂K x, compensatedTest Lg u (T γ) γ ≤
      (Real.exp b - Real.exp (q * x j)) - c' * (T γ : ℝ) := by
    filter_upwards [G.pathLaw_starts_at x, hpath] with γ hγ0 hγ
    change γ 0 = x at hγ0
    have hux : u x = v x := (hloc x (by simp [euclideanNorm, euclideanSq, dot]; positivity)).self_of_nhds
    have hclos : γ (T γ) ∈ closure W :=
      MarkovProcess.ContinuousPath.stopped_exitTimeTrunc_mem_closure W hWopen t γ (hγ0 ▸ hxW)
    have hclosW : closure W ⊆ {y : Vec d | euclideanNorm (y - x) ≤ η} ∩
        {y : Vec d | q * y j ≤ b} := by
      apply closure_minimal _ ((isClosed_le hcontn continuous_const).inter
        (isClosed_le hcontj continuous_const))
      intro y hy
      exact ⟨show euclideanNorm (y - x) ≤ η from le_of_lt hy.1,
        show q * y j ≤ b from le_of_lt hy.2⟩
    have hTpos := hclosW hclos
    have huT : u (γ (T γ)) ≤ Real.exp b := by
      rw [(hloc _ hTpos.1).self_of_nhds]
      exact Real.exp_le_exp.mpr hTpos.2
    have hint_lower : c' * (T γ : ℝ) ≤ ∫ s in (0 : ℝ)..(T γ : ℝ), Lg u (γ s.toNNReal) := by
      rw [intervalIntegral.integral_of_le (T γ).coe_nonneg, integral_Ioc_eq_integral_Ioo]
      have hconst : ∫ s in Set.Ioo (0 : ℝ) (T γ : ℝ), c' = c' * (T γ : ℝ) := by
        rw [setIntegral_const, Real.volume_real_Ioo_of_le (T γ).coe_nonneg, sub_zero, smul_eq_mul,
          mul_comm]
      rw [← hconst]
      apply setIntegral_mono_ae_restrict
      · exact integrableOn_const (by simp)
      · refine Integrable.of_bound ?_ Bg (Eventually.of_forall fun s => ?_)
        · exact (hLgm.comp (γ.continuous.comp continuous_real_toNNReal).measurable).aestronglyMeasurable
        · rw [Real.norm_eq_abs]
          exact hBg _
      · have hγ' : ∀ᵐ s ∂(volume.restrict (Set.Ioo (0 : ℝ) (T γ : ℝ))),
            ∀ (j : Fin d) (q : ℝ), |q| = κ → κ * Real.exp (q * (γ s.toNNReal) j) ≤
              Lg (fun z => Real.exp (q * z j)) (γ s.toNNReal) :=
          ae_restrict_of_ae_restrict_of_subset Set.Ioo_subset_Ioi_self hγ
        filter_upwards [hγ', ae_restrict_mem measurableSet_Ioo] with s hs hsI
        have hsT : s.toNNReal < T γ := by
          rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hsI.1.le]
          exact hsI.2
        have hmem : γ s.toNNReal ∈ W :=
          MarkovProcess.ContinuousPath.mem_of_lt_exitTimeTrunc W t γ hsT
        have hgen : Lg u (γ s.toNNReal) = Lg v (γ s.toNNReal) :=
          EinsteinFull.u5_physicalGenerator_congr_nhds _ ω lam (hloc _ (le_of_lt hmem.1))
        change c' ≤ Lg u (γ s.toNNReal)
        rw [hgen]
        have hlow := hs j q hq
        have hcoord : |(γ s.toNNReal) j - x j| ≤ η :=
          (abs_apply_le_euclideanNorm _ j).trans (le_of_lt hmem.1)
        have hexp : Real.exp (q * x j - κ * η) ≤ Real.exp (q * (γ s.toNNReal) j) := by
          apply Real.exp_le_exp.mpr
          have h1 : |q * ((γ s.toNNReal) j - x j)| ≤ κ * η := by
            rw [abs_mul, hq]
            exact mul_le_mul_of_nonneg_left hcoord hκ.le
          have h2 := (abs_le.mp h1).1
          nlinarith
        calc c' = κ * Real.exp (q * x j - κ * η) := rfl
          _ ≤ κ * Real.exp (q * (γ s.toNNReal) j) := mul_le_mul_of_nonneg_left hexp hκ.le
          _ ≤ Lg v (γ s.toNNReal) := hlow
    unfold compensatedTest
    rw [hγ0, hux]
    change u (γ (T γ)) - Real.exp (q * x j) - ∫ s in (0 : ℝ)..(T γ : ℝ), Lg u (γ s.toNNReal) ≤ _
    linarith
  -- integrate
  obtain ⟨Cc, hCc⟩ := (EinsteinFull.u5_regular_physical_compensated_continuous_bounded hd ω lam L
    hL hω u hu huc t).2
  have hcompm : Measurable (fun γ : Path d => compensatedTest Lg u (T γ) γ) := by
    unfold compensatedTest
    exact ((hu.continuous.measurable.comp
      (MarkovProcess.ContinuousPath.measurable_eval_stoppingTime_borel T hT)).sub
      (hu.continuous.measurable.comp (measurable_pathPosition 0))).sub
      (measurable_stopped_pathIntegral (Lg u) hLgm T hTm)
  have hcompi : Integrable (fun γ : Path d => compensatedTest Lg u (T γ) γ) (K x) :=
    Integrable.of_bound hcompm.aestronglyMeasurable Cc
      (Eventually.of_forall fun γ => hCc (T γ) (hTt γ) γ)
  have hTi : Integrable (fun γ : Path d => (T γ : ℝ)) (K x) :=
    Integrable.of_bound (measurable_coe_nnreal_real.comp hTm).aestronglyMeasurable t
      (Eventually.of_forall fun γ => by
        rw [Real.norm_eq_abs, abs_of_nonneg (T γ).coe_nonneg]
        exact_mod_cast hTt γ)
  have hmono := integral_mono_ae hcompi
    ((integrable_const (Real.exp b - Real.exp (q * x j))).sub (hTi.const_mul c')) hbound
  have hrhs : ∫ γ, ((Real.exp b - Real.exp (q * x j)) - c' * (T γ : ℝ)) ∂K x =
      (Real.exp b - Real.exp (q * x j)) - c' * ∫ γ, (T γ : ℝ) ∂K x := by
    rw [integral_sub (integrable_const _) (hTi.const_mul c'), integral_const, integral_const_mul]
    simp [measureReal_def]
  change ∫ γ, compensatedTest Lg u (T γ) γ ∂K x ≤
    ∫ γ, ((Real.exp b - Real.exp (q * x j)) - c' * (T γ : ℝ)) ∂K x at hmono
  rw [hD, hrhs] at hmono
  have hc'pos : 0 < c' := by positivity
  have hkey : c' * ∫ γ, (T γ : ℝ) ∂K x ≤ Real.exp b - Real.exp (q * x j) := by linarith
  have hc'eq : (Real.exp b - Real.exp (q * x j)) / c' =
      (Real.exp (b - q * x j) - 1) * Real.exp (κ * η) / κ := by
    simp only [c']
    rw [Real.exp_sub, Real.exp_sub]
    field_simp
  rw [← hc'eq]
  exact (le_div_iff₀ hc'pos).mpr (by linarith)


/-- The exit position of the diffusion started inside a half-space region is far from the
start only if the path moves far before a short time, or the half-space is not crossed
before that time. -/
theorem exitPosition_far_le
    (G : GantertFixedEnvironmentRealization hd L hL ω hω lam h₀ h₁) (κ : ℝ) (hκ : 0 < κ)
    (hsub : ∀ᵐ y ∂(volume : Measure (Vec d)), ∀ (j : Fin d) (q : ℝ), |q| = κ →
      κ * Real.exp (q * y j) ≤
        physicalGenerator (firstCoordinateIndex hd) ω lam (fun z => Real.exp (q * z j)) y)
    (C c : ℝ) (hC : 0 < C) (htail : ∀ (t : ℝ≥0), 0 < t → ∀ (x : Vec d) (R : ℝ), 0 ≤ R →
      G.pathLaw x {γ | ∃ u : ℝ≥0, u ≤ t ∧ R ≤ euclideanNorm (γ u - x)} ≤
        ENNReal.ofReal (C * Real.exp (C * (t : ℝ) - c * R ^ 2 / (t : ℝ))))
    (U : Set (Vec d)) (j : Fin d) (q : ℝ) (hq : |q| = κ) (b : ℝ)
    (hU : ∀ y ∈ U, q * y j < b) (x : Vec d) (hx : x ∈ U) (η : ℝ) (hη : 0 < η)
    (t : ℝ≥0) (ht : 0 < t) :
    (G.pathLaw x).real {γ : Path d |
      η ≤ euclideanNorm (γ ((MarkovProcess.ContinuousPath.exitTimeTop U γ).untopD 0) - x)} ≤
      C * Real.exp (C * (t : ℝ) - c * η ^ 2 / (t : ℝ)) +
        (Real.exp (b - q * x j) - 1) * Real.exp (κ * η) / κ / (t : ℝ) := by
  let K := G.pathLaw
  have : IsProbabilityMeasure (K x) := G.pathLaw_isMarkovKernel.isProbabilityMeasure x
  let V : Set (Vec d) := {y : Vec d | euclideanNorm (y - x) < η}
  let H : Set (Vec d) := {y : Vec d | q * y j < b}
  let W : Set (Vec d) := V ∩ H
  let T : Path d → ℝ≥0 := MarkovProcess.ContinuousPath.exitTimeTrunc W t
  have hcontj : Continuous (fun y : Vec d => q * y j) := continuous_const.mul (continuous_apply j)
  have hcontn : Continuous (fun y : Vec d => euclideanNorm (y - x)) :=
    (Calculus.Feller.continuous_euclideanNorm d).comp (continuous_id.sub continuous_const)
  have hWopen : IsOpen W :=
    (isOpen_lt hcontn continuous_const).inter (isOpen_lt hcontj continuous_const)
  have hT : IsStoppingTime (MarkovProcess.ContinuousPath.canonicalFiltration (alpha := Vec d))
      (fun γ => (T γ : WithTop ℝ≥0)) :=
    MarkovProcess.ContinuousPath.isStoppingTime_exitTimeTrunc W hWopen t
  have hTm : Measurable T := MarkovProcess.ContinuousPath.measurable_of_isStoppingTime T hT
  have hTt : ∀ γ, T γ ≤ t := fun γ => MarkovProcess.ContinuousPath.exitTimeTrunc_le W t γ
  let A₁ : Set (Path d) := {γ | ∃ u : ℝ≥0, u ≤ t ∧ η ≤ euclideanNorm (γ u - x)}
  let A₂ : Set (Path d) := {γ | (t : ℝ) ≤ (T γ : ℝ)}
  let A₀ : Set (Path d) := {γ | γ 0 ≠ x}
  have hA₀ : K x A₀ = 0 := by
    have h := G.pathLaw_starts_at x
    rw [ae_iff] at h
    simpa [A₀, pathPosition] using h
  have hsubset : {γ : Path d |
      η ≤ euclideanNorm (γ ((MarkovProcess.ContinuousPath.exitTimeTop U γ).untopD 0) - x)} ⊆
      A₁ ∪ A₂ ∪ A₀ := by
    intro γ hγ
    by_cases h0 : γ 0 = x
    swap
    · exact Or.inr h0
    left
    by_cases hfin : MarkovProcess.ContinuousPath.exitTime U γ = ⊤
    · exfalso
      have hun : (MarkovProcess.ContinuousPath.exitTimeTop U γ).untopD 0 = 0 := by
        have htop : MarkovProcess.ContinuousPath.exitTimeTop U γ = ⊤ := by
          rw [MarkovProcess.ContinuousPath.exitTimeTop_apply]
          exact hfin
        rw [htop]
        rfl
      change η ≤ euclideanNorm (γ ((MarkovProcess.ContinuousPath.exitTimeTop U γ).untopD 0) - x)
        at hγ
      rw [hun, h0, sub_self] at hγ
      have : euclideanNorm (0 : Vec d) = 0 := by simp [euclideanNorm, euclideanSq, dot]
      linarith
    have hX : (MarkovProcess.ContinuousPath.exitTimeTop U γ).untopD 0 =
        (MarkovProcess.ContinuousPath.exitTime U γ).toNNReal :=
      MarkovProcess.ContinuousPath.untopD_exitTimeTop_eq_toNNReal U γ hfin
    change η ≤ euclideanNorm (γ ((MarkovProcess.ContinuousPath.exitTimeTop U γ).untopD 0) - x)
      at hγ
    rw [hX] at hγ
    by_cases hτt : (MarkovProcess.ContinuousPath.exitTime U γ).toNNReal ≤ t
    · exact Or.inl ⟨_, hτt, hγ⟩
    by_cases hfar : ∃ u : ℝ≥0, u ≤ t ∧ η ≤ euclideanNorm (γ u - x)
    · exact Or.inl hfar
    right
    have hτt' : t < (MarkovProcess.ContinuousPath.exitTime U γ).toNNReal := not_le.mp hτt
    have hfar' : ∀ u : ℝ≥0, u ≤ t → euclideanNorm (γ u - x) < η :=
      fun u hu => lt_of_not_ge (fun h => hfar ⟨u, hu, h⟩)
    have hUH : MarkovProcess.ContinuousPath.exitTime U γ ≤
        MarkovProcess.ContinuousPath.exitTime H γ :=
      MarkovProcess.ContinuousPath.exitTime_mono (fun y hy => hU y hy) γ
    have hle : (t : ℝ≥0∞) ≤ MarkovProcess.ContinuousPath.exitTime W γ := by
      rw [MarkovProcess.ContinuousPath.le_exitTime_iff]
      intro v hv
      by_contra hvt
      have hvt' : v < t := by exact_mod_cast not_le.mp hvt
      apply hv
      refine ⟨hfar' v hvt'.le, ?_⟩
      apply MarkovProcess.ContinuousPath.mem_of_lt_exitTime H γ v
      calc (v : ℝ≥0∞) < t := by exact_mod_cast hvt'
        _ < (MarkovProcess.ContinuousPath.exitTime U γ).toNNReal := by exact_mod_cast hτt'
        _ ≤ MarkovProcess.ContinuousPath.exitTime U γ := ENNReal.coe_toNNReal_le_self
        _ ≤ MarkovProcess.ContinuousPath.exitTime H γ := hUH
    have hTeq : T γ = t := by
      apply le_antisymm (hTt γ)
      have h := MarkovProcess.ContinuousPath.coe_exitTimeTrunc_ennreal W t γ
      have : ((T γ : ℝ≥0) : ℝ≥0∞) = min (MarkovProcess.ContinuousPath.exitTime W γ) t := h
      rw [min_eq_right hle] at this
      exact le_of_eq (ENNReal.coe_injective this).symm
    change (t : ℝ) ≤ (T γ : ℝ)
    rw [hTeq]
  have hA₁ : (K x).real A₁ ≤ C * Real.exp (C * (t : ℝ) - c * η ^ 2 / (t : ℝ)) :=
    ENNReal.toReal_le_of_le_ofReal (by positivity) (htail t ht x η hη.le)
  have hTi : Integrable (fun γ : Path d => (T γ : ℝ)) (K x) :=
    Integrable.of_bound (measurable_coe_nnreal_real.comp hTm).aestronglyMeasurable t
      (Eventually.of_forall fun γ => by
        rw [Real.norm_eq_abs, abs_of_nonneg (T γ).coe_nonneg]
        exact_mod_cast hTt γ)
  have hA₂ : (K x).real A₂ ≤
      (Real.exp (b - q * x j) - 1) * Real.exp (κ * η) / κ / (t : ℝ) := by
    have hmk := mul_meas_ge_le_integral_of_nonneg (Eventually.of_forall fun γ => (T γ).coe_nonneg)
      hTi (t : ℝ)
    have hint := integral_exitTimeTrunc_le_of_subsolution G κ hκ hsub j q hq b x (hU x hx) η hη t
    have htpos : (0 : ℝ) < t := by exact_mod_cast ht
    rw [le_div_iff₀ htpos, mul_comm]
    exact hmk.trans hint
  calc (K x).real {γ : Path d |
        η ≤ euclideanNorm (γ ((MarkovProcess.ContinuousPath.exitTimeTop U γ).untopD 0) - x)}
      ≤ (K x).real (A₁ ∪ A₂ ∪ A₀) := measureReal_mono hsubset
    _ ≤ (K x).real (A₁ ∪ A₂) + (K x).real A₀ := measureReal_union_le _ _
    _ ≤ (K x).real A₁ + (K x).real A₂ + 0 := by
        gcongr
        · exact measureReal_union_le _ _
        · rw [measureReal_def, hA₀, ENNReal.toReal_zero]
    _ ≤ _ := by linarith


/-- A Gaussian bound becomes arbitrarily small at short times. -/
theorem exists_small_time_gaussian (C c η ε : ℝ) (hc : 0 < c) (hη : 0 < η) (hε : 0 < ε) :
    ∃ t : ℝ≥0, 0 < t ∧ C * Real.exp (C * (t : ℝ) - c * η ^ 2 / (t : ℝ)) < ε := by
  have hk : 0 < c * η ^ 2 := by positivity
  have hinv : Tendsto (fun s : ℝ => -(c * η ^ 2) * s⁻¹) (𝓝[>] 0) atBot :=
    tendsto_inv_nhdsGT_zero.const_mul_atTop_of_neg (neg_lt_zero.mpr hk)
  have hlinear : Tendsto (fun s : ℝ => C * s) (𝓝[>] 0) (𝓝 0) := by
    simpa only [mul_zero, id_eq] using
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => C) (𝓝[>] (0 : ℝ)) (𝓝 C)).mul
        (tendsto_id.mono_left nhdsWithin_le_nhds)
  have harg : Tendsto (fun s : ℝ => C * s - c * η ^ 2 / s) (𝓝[>] 0) atBot := by
    simpa only [sub_eq_add_neg, div_eq_mul_inv, neg_mul] using hlinear.add_atBot hinv
  have hlim : Tendsto (fun s : ℝ => C * Real.exp (C * s - c * η ^ 2 / s)) (𝓝[>] 0) (𝓝 0) := by
    simpa only [mul_zero, Function.comp_def] using (Real.tendsto_exp_atBot.comp harg).const_mul C
  have hevent := hlim.eventually (Iio_mem_nhds hε)
  obtain ⟨δ, hδ, hsmall⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hevent
  change 0 < δ at hδ
  refine ⟨Real.toNNReal (δ / 2), Real.toNNReal_pos.mpr (by linarith), ?_⟩
  apply hsmall
  rw [Real.coe_toNNReal _ (by linarith)]
  constructor <;> linarith

/-- An exit payoff tends to the payoff at a boundary point separated from the set by a
coordinate hyperplane. -/
theorem tendsto_exitPayoff_of_separated
    (G : GantertFixedEnvironmentRealization hd L hL ω hω lam h₀ h₁)
    (U : Set (Vec d)) (hUo : IsOpen U) (f : Vec d → ℝ) (hf : Continuous f) (B : ℝ)
    (hB : ∀ y, |f y| ≤ B) (z : Vec d) (j : Fin d) (σ : ℝ) (hσ : σ = 1 ∨ σ = -1)
    (hsep : ∀ y ∈ U, σ * y j < σ * z j) :
    Tendsto (exitPayoff G U f) (𝓝 z) (𝓝 (f z)) := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have : IsMarkovKernel G.pathLaw := G.pathLaw_isMarkovKernel
  have hfdd := EinsteinFull.u6_arbitrary_supplied_gmp_canonical_FDD hd ω lam L hL hω h₀ h₁ G
  obtain ⟨κ, hκ, hsub⟩ := exists_coordinate_exp_subsolution hd hL hω lam
  obtain ⟨C, c, hC, hc, htail⟩ :=
    EinsteinFull.u8_regular_signed_physical_path_exit_tail hd ω lam L hL hω G.pathLaw hfdd
  rw [Metric.tendsto_nhds]
  intro ζ hζ
  obtain ⟨ρ₁, hρ₁, hfz⟩ := Metric.continuous_iff.mp hf z (ζ / 2) (half_pos hζ)
  let η : ℝ := ρ₁ / 2
  have hη : 0 < η := half_pos hρ₁
  let ε' : ℝ := ζ / (8 * (B + 1))
  have hε' : 0 < ε' := by positivity
  obtain ⟨t, ht, htsmall⟩ := exists_small_time_gaussian C c η ε' hc hη hε'
  have htpos : (0 : ℝ) < t := by exact_mod_cast ht
  -- the hyperplane-distance factor
  let A : ℝ := Real.exp (κ * η) / κ / (t : ℝ)
  have hA : 0 ≤ A := by positivity
  have hcontr : Continuous (fun r : ℝ => (Real.exp (κ * r) - 1) * A) :=
    ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).sub continuous_const).mul
      continuous_const
  obtain ⟨ρ₂, hρ₂, hsmall₂⟩ := Metric.continuous_iff.mp hcontr 0 ε' hε'
  let ρ : ℝ := min ρ₂ η
  have hρ : 0 < ρ := lt_min hρ₂ hη
  have hcontn : Continuous (fun y : Vec d => euclideanNorm (y - z)) :=
    (Calculus.Feller.continuous_euclideanNorm d).comp (continuous_id.sub continuous_const)
  have hnear : {y : Vec d | euclideanNorm (y - z) < ρ} ∈ 𝓝 z := by
    apply (isOpen_lt hcontn continuous_const).mem_nhds
    simp only [Set.mem_ofPred_eq, sub_self]
    simpa [euclideanNorm, euclideanSq, dot] using hρ
  filter_upwards [hnear] with y hy
  change euclideanNorm (y - z) < ρ at hy
  have hyz : dist y z < ρ₁ := by
    rw [dist_eq_norm]
    calc ‖y - z‖ ≤ euclideanNorm (y - z) := norm_le_euclideanNorm _
      _ < ρ := hy
      _ ≤ η := min_le_right _ _
      _ < ρ₁ := by simp only [η]; linarith
  by_cases hyU : y ∉ U
  · rw [exitPayoff_of_notMem G U f y hyU]
    exact (hfz y hyz).trans (half_lt_self hζ)
  push Not at hyU
  -- the separating coordinate exponential
  let q : ℝ := σ * κ
  have hq : |q| = κ := by
    rcases hσ with h | h <;> simp [q, h, abs_of_pos hκ]
  let b : ℝ := q * z j
  have hU : ∀ w ∈ U, q * w j < b := by
    intro w hw
    have h := hsep w hw
    simp only [q, b]
    nlinarith
  have hfar := exitPosition_far_le G κ hκ hsub C c hC htail U j q hq b hU y hyU η hη t ht
  have hfactor : (Real.exp (b - q * y j) - 1) * Real.exp (κ * η) / κ / (t : ℝ) < ε' := by
    have hr0 : 0 ≤ euclideanNorm (y - z) := Real.sqrt_nonneg _
    have hbq : b - q * y j ≤ κ * euclideanNorm (y - z) := by
      have h1 : b - q * y j = q * (z j - y j) := by simp only [b]; ring
      have h2 : |z j - y j| ≤ euclideanNorm (y - z) := by
        rw [abs_sub_comm]
        exact abs_apply_le_euclideanNorm (y - z) j
      rw [h1]
      calc q * (z j - y j) ≤ |q * (z j - y j)| := le_abs_self _
        _ = κ * |z j - y j| := by rw [abs_mul, hq]
        _ ≤ κ * euclideanNorm (y - z) := mul_le_mul_of_nonneg_left h2 hκ.le
    have hmono : (Real.exp (b - q * y j) - 1) * A ≤
        (Real.exp (κ * euclideanNorm (y - z)) - 1) * A :=
      mul_le_mul_of_nonneg_right (by linarith [Real.exp_le_exp.mpr hbq]) hA
    have hdist : dist (euclideanNorm (y - z)) 0 < ρ₂ := by
      rw [Real.dist_eq, sub_zero, abs_of_nonneg hr0]
      exact lt_of_lt_of_le hy (min_le_left _ _)
    have hval := hsmall₂ _ hdist
    rw [Real.dist_eq] at hval
    simp only [mul_zero, Real.exp_zero, sub_self, zero_mul, sub_zero] at hval
    have hpos : 0 ≤ (Real.exp (κ * euclideanNorm (y - z)) - 1) * A := by
      apply mul_nonneg _ hA
      have := Real.one_le_exp (mul_nonneg hκ.le hr0)
      linarith
    rw [abs_of_nonneg hpos] at hval
    calc (Real.exp (b - q * y j) - 1) * Real.exp (κ * η) / κ / (t : ℝ)
        = (Real.exp (b - q * y j) - 1) * A := by simp only [A]; ring
      _ ≤ _ := hmono
      _ < ε' := hval
  have hprob : (G.pathLaw y).real {γ : Path d |
      η ≤ euclideanNorm (γ ((MarkovProcess.ContinuousPath.exitTimeTop U γ).untopD 0) - y)} <
      2 * ε' := by linarith
  -- integrate the pointwise estimate
  have : IsProbabilityMeasure (G.pathLaw y) := G.pathLaw_isMarkovKernel.isProbabilityMeasure y
  let X : Path d → Vec d := fun γ => γ ((MarkovProcess.ContinuousPath.exitTimeTop U γ).untopD 0)
  have hXm : Measurable X := MarkovProcess.ContinuousPath.measurable_eval_untopD_exitTimeTop U hUo
  let Afar : Set (Path d) := {γ : Path d | η ≤ euclideanNorm (X γ - y)}
  have hAm : MeasurableSet Afar :=
    measurableSet_le measurable_const ((Calculus.Feller.continuous_euclideanNorm d).measurable.comp
      (hXm.sub measurable_const))
  have hfX : Integrable (fun γ => f (X γ)) (G.pathLaw y) :=
    Integrable.of_bound (hf.measurable.comp hXm).aestronglyMeasurable B
      (Eventually.of_forall fun γ => by rw [Real.norm_eq_abs]; exact hB _)
  have hpoint : ∀ γ, |f (X γ) - f z| ≤ ζ / 2 + 2 * B * Afar.indicator (fun _ => (1 : ℝ)) γ := by
    intro γ
    by_cases hγ : γ ∈ Afar
    · rw [Set.indicator_of_mem hγ, mul_one]
      have h := abs_sub (f (X γ)) (f z)
      have h1 := hB (X γ)
      have h2 := hB z
      linarith
    · rw [Set.indicator_of_notMem hγ, mul_zero, add_zero]
      have hclose : euclideanNorm (X γ - y) < η := lt_of_not_ge hγ
      have hd' : dist (X γ) z < ρ₁ := by
        rw [dist_eq_norm]
        calc ‖X γ - z‖ = ‖(X γ - y) + (y - z)‖ := by congr 1; abel
          _ ≤ ‖X γ - y‖ + ‖y - z‖ := norm_add_le _ _
          _ ≤ euclideanNorm (X γ - y) + euclideanNorm (y - z) :=
              add_le_add (norm_le_euclideanNorm _) (norm_le_euclideanNorm _)
          _ < η + η := add_lt_add hclose (lt_of_lt_of_le hy (min_le_right _ _))
          _ = ρ₁ := by simp only [η]; ring
      have h := hfz (X γ) hd'
      rw [Real.dist_eq] at h
      exact h.le
  have hind : Integrable (fun γ => ζ / 2 + 2 * B * Afar.indicator (fun _ => (1 : ℝ)) γ)
      (G.pathLaw y) :=
    (integrable_const _).add ((integrable_const (1 : ℝ)).indicator hAm |>.const_mul _)
  have hval : exitPayoff G U f y - f z = ∫ γ, (f (X γ) - f z) ∂G.pathLaw y := by
    rw [integral_sub hfX (integrable_const _), integral_const]
    simp [measureReal_def]
    rfl
  rw [Real.dist_eq, hval]
  calc |∫ γ, (f (X γ) - f z) ∂G.pathLaw y|
      ≤ ∫ γ, |f (X γ) - f z| ∂G.pathLaw y := abs_integral_le_integral_abs
    _ ≤ ∫ γ, (ζ / 2 + 2 * B * Afar.indicator (fun _ => (1 : ℝ)) γ) ∂G.pathLaw y :=
        integral_mono (hfX.sub (integrable_const _)).abs hind hpoint
    _ = ζ / 2 + 2 * B * (G.pathLaw y).real Afar := by
        rw [integral_add (integrable_const _)
          ((integrable_const (1 : ℝ)).indicator hAm |>.const_mul _), integral_const,
          integral_const_mul, integral_indicator hAm, setIntegral_const]
        simp [measureReal_def]
    _ ≤ ζ / 2 + 2 * B * (2 * ε') := by gcongr
    _ < ζ := by
        simp only [ε']
        have h8 : 0 < 8 * (B + 1) := by positivity
        rw [show ζ / 2 + 2 * B * (2 * (ζ / (8 * (B + 1)))) =
          ζ / 2 + ζ * (B / (2 * (B + 1))) by field_simp; ring]
        have hfrac : B / (2 * (B + 1)) < 1 / 2 := by
          rw [div_lt_iff₀ (by positivity)]
          linarith
        nlinarith


/-- An exit payoff from an open set separated from each exterior point by a coordinate
hyperplane is continuous everywhere, provided exits are almost surely finite. -/
theorem continuous_exitPayoff_of_separated
    (G : GantertFixedEnvironmentRealization hd L hL ω hω lam h₀ h₁)
    (U : Set (Vec d)) (hUo : IsOpen U) (f : Vec d → ℝ) (hf : Continuous f) (B : ℝ)
    (hB : ∀ y, |f y| ≤ B)
    (hfin : ∀ x, ∀ᵐ γ ∂G.pathLaw x, MarkovProcess.ContinuousPath.exitTime U γ ≠ ⊤)
    (hsep : ∀ z ∉ U, ∃ (j : Fin d) (σ : ℝ), (σ = 1 ∨ σ = -1) ∧ ∀ y ∈ U, σ * y j < σ * z j) :
    Continuous (exitPayoff G U f) := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x ∈ U
  · exact (continuousOn_exitPayoff G U hUo f hf.measurable B hB hfin).continuousAt
      (hUo.mem_nhds hx)
  · obtain ⟨j, σ, hσ, hsepx⟩ := hsep x hx
    have h := tendsto_exitPayoff_of_separated G U hUo f hf B hB x j σ hσ hsepx
    rw [ContinuousAt, exitPayoff_of_notMem G U f x hx]
    exact h

/-- A coordinate slab intersected with a ball of the sup norm is separated from each exterior
point by a coordinate hyperplane. -/
theorem slab_ball_separated (i : Fin d) (c y : Vec d) (R N : ℝ) :
    ∀ z ∉ coordinateSlab i c R ∩ Metric.ball y N, ∃ (j : Fin d) (σ : ℝ), (σ = 1 ∨ σ = -1) ∧
      ∀ w ∈ coordinateSlab i c R ∩ Metric.ball y N, σ * w j < σ * z j := by
  intro z hz
  by_cases hN : 0 < N
  swap
  · refine ⟨i, 1, Or.inl rfl, fun w hw => ?_⟩
    exact absurd (lt_of_le_of_lt dist_nonneg (Metric.mem_ball.mp hw.2)) hN
  by_cases hzs : z ∈ coordinateSlab i c R
  · have hzb : z ∉ Metric.ball y N := fun h => hz ⟨hzs, h⟩
    rw [Metric.mem_ball, dist_eq_norm, not_lt] at hzb
    have hex : ∃ k : Fin d, N ≤ |z k - y k| := by
      by_contra hcon
      have hall : ∀ k : Fin d, ‖(z - y) k‖ < N := fun k => by
        rw [Real.norm_eq_abs, Pi.sub_apply]
        exact lt_of_not_ge fun h => hcon ⟨k, h⟩
      exact absurd ((pi_norm_lt_iff hN).mpr hall) (not_lt.mpr hzb)
    obtain ⟨k, hk⟩ := hex
    refine ⟨k, ?_⟩
    rcases le_or_gt 0 (z k - y k) with h | h
    · rw [abs_of_nonneg h] at hk
      refine ⟨1, Or.inl rfl, fun w hw => ?_⟩
      have hwk : |w k - y k| < N := by
        have h1 := Metric.mem_ball.mp hw.2
        rw [dist_eq_norm] at h1
        have h2 := norm_le_pi_norm (w - y) k
        rw [Real.norm_eq_abs, Pi.sub_apply] at h2
        linarith
      have := (abs_lt.mp hwk).2
      linarith
    · rw [abs_of_neg h] at hk
      refine ⟨-1, Or.inr rfl, fun w hw => ?_⟩
      have hwk : |w k - y k| < N := by
        have h1 := Metric.mem_ball.mp hw.2
        rw [dist_eq_norm] at h1
        have h2 := norm_le_pi_norm (w - y) k
        rw [Real.norm_eq_abs, Pi.sub_apply] at h2
        linarith
      have := (abs_lt.mp hwk).1
      linarith
  · have hzi : R ≤ |z i - c i| := by
      simpa [coordinateSlab] using hzs
    refine ⟨i, ?_⟩
    rcases le_or_gt 0 (z i - c i) with h | h
    · rw [abs_of_nonneg h] at hzi
      refine ⟨1, Or.inl rfl, fun w hw => ?_⟩
      have := (abs_lt.mp (show |w i - c i| < R from hw.1)).2
      linarith
    · rw [abs_of_neg h] at hzi
      refine ⟨-1, Or.inr rfl, fun w hw => ?_⟩
      have := (abs_lt.mp (show |w i - c i| < R from hw.1)).1
      linarith

end EinsteinFull.Regeneration
