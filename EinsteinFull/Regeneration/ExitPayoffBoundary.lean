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

end EinsteinFull.Regeneration
