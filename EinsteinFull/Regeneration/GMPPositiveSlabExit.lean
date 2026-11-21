import EinsteinFull.Regeneration.ExitPayoffRescaledEquation
import EinsteinFull.Regeneration.GMPPayoffComparison
import EinsteinFull.Regeneration.GMPSlabExitMoment
import EinsteinFull.Regeneration.GMPCompactExitPayoff

/-!
# Positive slab exits

Gantert–Mathieu–Piatnitski, Lemma 4.3, for the reduced zero-potential diffusion: beyond a
width threshold depending only on the dimension and the ellipticity bound, the diffusion
started anywhere leaves the slab of half-width `l / μ` around its start through the upper
force face with probability at least `2/3`.

The bounded-slab exit payoffs are continuous everywhere, and after translation and
rescaling by the force they are Sobolev solutions of the unit-force weighted equation in
the open slab, by Dynkin's formula, the zero-boundary resolvents and the change of
variables. The slab comparison therefore applies to them.
-/

open MeasureTheory ProbabilityTheory Filter Set EinsteinRelation
open EinsteinRelation.Regeneration EinsteinRelation.Diffusion
open EinsteinRelation.External.GantertSection7Support
open scoped NNReal ENNReal

namespace EinsteinFull.Regeneration

/-- A coordinate slab box lies in the closed sup-norm ball whose radius is its larger
half-side. -/
theorem coordinateSlabBox_subset_closedBall (n : ℕ) (i : Fin (n + 1)) (s l : ℝ) :
    coordinateSlabBox n i s l ⊆
      Metric.closedBall (0 : PDE.Vec (n + 1)) (max l (Real.exp (s * l / (n + 1)))) := by
  intro x hx
  simp only [coordinateSlabBox, mem_preimage, MeasurableEquiv.piFinSuccAbove_apply, mem_prod,
    mem_Icc, Pi.le_def] at hx
  have hR : 0 ≤ max l (Real.exp (s * l / (n + 1))) :=
    (Real.exp_pos _).le.trans (le_max_right _ _)
  rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg hR]
  intro j
  rw [Real.norm_eq_abs]
  rcases Fin.eq_self_or_eq_succAbove i j with h | ⟨k, rfl⟩
  · subst h
    exact (abs_le.mpr ⟨hx.1.1, hx.1.2⟩).trans (le_max_left _ _)
  · exact (abs_le.mpr ⟨hx.2.1 k, hx.2.2 k⟩).trans (le_max_right _ _)

/-- On the closed ball, the bounded-slab payoff is the exit payoff of any payoff that agrees
with the smooth slab payoff there. -/
theorem gmpBoundedSlabPayoff_eq_exitPayoff
    {d : ℕ} {hd : 2 ≤ d} {L : ℝ} {hL : 1 ≤ L}
    {ω : FieldPair d} {hω : IsRegular L ω} {lam : ℝ} {h₀ : 0 ≤ lam} {h₁ : lam ≤ 1}
    (G : GantertFixedEnvironmentRealization hd L hL ω hω lam h₀ h₁)
    (i : Fin d) (c : Vec d) (R : ℝ) (y : Vec d) (N : ℝ) (f : Vec d → ℝ)
    (hf : Set.EqOn f (slabSmoothPayoff i c R) (Metric.closedBall y N))
    (hfin : ∀ x, ∀ᵐ γ ∂G.pathLaw x,
      MarkovProcess.ContinuousPath.exitTime (coordinateSlab i c R ∩ Metric.ball y N) γ ≠ ⊤)
    (x : Vec d) (hx : x ∈ Metric.closedBall y N) :
    gmpBoundedSlabPayoff G i c R y N x =
      exitPayoff G (coordinateSlab i c R ∩ Metric.ball y N) f x := by
  by_cases hxD : x ∈ coordinateSlab i c R ∩ Metric.ball y N
  · unfold gmpBoundedSlabPayoff exitPayoff
    apply integral_congr_ae
    filter_upwards [G.pathLaw_starts_at x, hfin x] with γ hstart hγ
    change γ 0 = x at hstart
    exact (exit_payoff_eq_of_eqOn_closedBall _
      ((isOpen_coordinateSlab i c R).inter Metric.isOpen_ball) y N inter_subset_right f
      (slabSmoothPayoff i c R) hf γ (hstart ▸ hxD) hγ).symm
  · change exitPayoff G _ (slabSmoothPayoff i c R) x = _
    rw [exitPayoff_of_notMem G _ _ x hxD, exitPayoff_of_notMem G _ _ x hxD]
    exact (hf hx).symm

/-- GMP Lemma 4.3 for the reduced zero-potential diffusion: positive slab exits have
probability at least `2/3` from every start, for all widths beyond a threshold fixed before
the environment, the force and the realization. -/
theorem gmp_positive_slab_exit (n : ℕ) (hd : 2 ≤ n + 1) (Λ : ℝ) (hΛ : 1 ≤ Λ) :
    ∃ l₀ : ℝ, 1 ≤ l₀ ∧ ∀ l : ℝ, l₀ ≤ l → ∀ (r : ℝ)
      (Q : EnvironmentLaw (n + 1) Λ r) (μ : ℝ) (hμ : 0 < μ) (hμ1 : μ ≤ 1)
      (ω : FieldPair (n + 1))
      (hω : IsRegular (sourceReducedBound Λ) (zeroPotentialReducedPair ω))
      (G : GantertFixedEnvironmentRealization hd (sourceReducedBound Λ)
        (one_le_sourceReducedBound Q.ellipticity_parameter) (zeroPotentialReducedPair ω)
        hω μ hμ.le hμ1) (c : Vec (n + 1)),
      (2 / 3 : ℝ) ≤ (G.pathLaw c).real {γ |
        coordinateSlabExit γ (Renewal.forceCoord hd) (l / μ) ≠ ⊤ ∧
        γ (coordinateSlabExit γ (Renewal.forceCoord hd) (l / μ)).toNNReal
          (Renewal.forceCoord hd) - γ 0 (Renewal.forceCoord hd) = l / μ} := by
  obtain ⟨l₀, hl₀, hmain⟩ := gmp_positive_slab_exit_of_eventual_weak_solutions n hd Λ hΛ
  refine ⟨l₀, hl₀, ?_⟩
  intro l hl r Q μ hμ hμ1 ω hω G c
  apply hmain l hl r Q μ hμ hμ1 ω hω G c c
  have hl1 : 1 ≤ l := hl₀.trans hl
  have hl0 : 0 < l := lt_of_lt_of_le zero_lt_one hl1
  have hμi : 0 < μ⁻¹ := inv_pos.mpr hμ
  set i := Renewal.forceCoord hd with hi
  obtain ⟨δ, -, -, hmean⟩ := uniform_regular_gmp_slab_exit_mean (n + 1) hd Λ r l hl1
  obtain ⟨δ', -, -, hexp⟩ :=
    uniform_regular_gmp_slab_exit_exponential_moment (n + 1) hd Λ r l hl1
  let R : ℝ := l + Real.exp (2 * l / (n + 1)) + 1
  have hRl : l < R := by
    have := Real.exp_pos (2 * l / (n + 1))
    simp only [R]
    linarith
  have hRe : Real.exp (2 * l / (n + 1)) < R := by
    simp only [R]
    linarith
  have hR1 : 1 < R := lt_of_le_of_lt hl1 hRl
  filter_upwards [eventually_ge_atTop ⌈R / μ⌉₊] with N hN
  have hNR : R / μ ≤ (N : ℝ) := (Nat.le_ceil (R / μ)).trans (by exact_mod_cast hN)
  let D := coordinateSlab i c (l / μ) ∩ Metric.ball c (N : ℝ)
  have hDo : IsOpen D := (isOpen_coordinateSlab i c (l / μ)).inter Metric.isOpen_ball
  have hDs : D ⊆ coordinateSlab i c (l / μ) := inter_subset_left
  have hfin : ∀ x, ∀ᵐ γ ∂G.pathLaw x, MarkovProcess.ContinuousPath.exitTime D γ ≠ ⊤ :=
    fun x => (hexp Q μ hμ hμ1 ω hω G c x D hDo hDs).1
  let Km : ℝ := (Real.exp δ * Real.exp (δ / 4) / (1 - Real.exp (δ / 4 - δ / 2))) / (δ / 4)
  have hμ2 : 0 < μ ^ 2 := by positivity
  have hτ : ∀ x, Integrable (fun γ => (MarkovProcess.ContinuousPath.exitTime D γ).toReal)
      (G.pathLaw x) := by
    intro x
    have h := ((hmean Q μ hμ hμ1 ω hω G c x D hDo hDs).1).const_mul (μ ^ 2)⁻¹
    refine h.congr (Eventually.of_forall fun γ => ?_)
    change (μ ^ 2)⁻¹ * (μ ^ 2 * _) = _
    rw [← mul_assoc, inv_mul_cancel₀ hμ2.ne', one_mul]
  have hM : ∀ x, ∫ γ, (MarkovProcess.ContinuousPath.exitTime D γ).toReal ∂G.pathLaw x ≤
      (μ ^ 2)⁻¹ * Km := by
    intro x
    have h := (hmean Q μ hμ hμ1 ω hω G c x D hDo hDs).2
    have heq : ∫ γ, (MarkovProcess.ContinuousPath.exitTime D γ).toReal ∂G.pathLaw x =
        (μ ^ 2)⁻¹ * ∫ γ, μ ^ 2 * (MarkovProcess.ContinuousPath.exitTime D γ).toReal
          ∂G.pathLaw x := by
      rw [integral_const_mul, ← mul_assoc, inv_mul_cancel₀ hμ2.ne', one_mul]
    rw [heq]
    exact mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hμ2.le)
  have : IsLocallyFiniteMeasure (physicalReversibleMeasure (zeroPotentialReducedPair ω) hd μ) :=
    EinsteinFull.Work.W5.gantert_physicalMeasure_locallyFinite hd _ μ
  have hDm : physicalReversibleMeasure (zeroPotentialReducedPair ω) hd μ D ≠ ⊤ :=
    ((measure_mono inter_subset_right).trans_lt (measure_ball_lt_top (x := c))).ne
  obtain ⟨f, hf, hfc, -, hfeq⟩ := exists_compact_smooth_slabPayoff i c c (l / μ) (N : ℝ)
  let U : Set (PDE.Vec (n + 1)) := Metric.ball 0 R
  have hU : PDE.IsOpenBoundedConvexDomain U := PDE.Ch4Infra.isOpenBoundedConvexDomain_ball 0 R
  have hAz : ∀ z ∈ U, dist (c + μ⁻¹ • z) c < N := by
    intro z hz
    have hz' : ‖z‖ < R := by simpa only [U, Metric.mem_ball, dist_zero_right] using hz
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hμi]
    calc μ⁻¹ * ‖z‖ < μ⁻¹ * R := mul_lt_mul_of_pos_left hz' hμi
      _ = R / μ := by rw [div_eq_inv_mul]
      _ ≤ N := hNR
  let S := openForceSlab U i l
  have hS : IsOpen S := isOpen_openForceSlab hU.isOpen i l
  have hSD : ∀ z ∈ S, c + μ⁻¹ • z ∈ D := by
    intro z hz
    refine ⟨?_, Metric.mem_ball.mpr (hAz z hz.1)⟩
    have hzi : |z i| < l := abs_lt.mpr hz.2
    change |(c + μ⁻¹ • z) i - c i| < l / μ
    rw [show (c + μ⁻¹ • z) i - c i = μ⁻¹ * z i by simp, abs_mul, abs_of_pos hμi,
      div_eq_inv_mul]
    exact mul_lt_mul_of_pos_left hzi hμi
  have hF : ∀ z ∈ U, gmpScaledSlabPayoff G i c l μ c N z = exitPayoff G D f (c + μ⁻¹ • z) :=
    fun z hz => gmpBoundedSlabPayoff_eq_exitPayoff G i c (l / μ) c N f hfeq hfin
      (c + μ⁻¹ • z) (Metric.mem_closedBall.mpr (hAz z hz).le)
  obtain ⟨u, hu, hsol⟩ := exists_rescaled_exitPayoff_solution G (fun _ => rfl) hμ D hDo hDm f
    hf hfc hfin hτ ((μ ^ 2)⁻¹ * Km) hM c U hU (gmpScaledSlabPayoff G i c l μ c N) hF S hS
    inter_subset_left hSD
  have hcont : Continuous (gmpScaledSlabPayoff G i c l μ c N) := by
    have hP := continuous_exitPayoff_of_separated G D hDo (slabSmoothPayoff i c (l / μ))
      (slabSmoothPayoff_smooth i c (l / μ)).continuous 1
      (fun x => abs_le.mpr ⟨by linarith [(slabSmoothPayoff_mem_Icc i c (l / μ) x).1],
        (slabSmoothPayoff_mem_Icc i c (l / μ) x).2⟩) hfin
      (slab_ball_separated i c c (l / μ) N)
    exact hP.comp (continuous_const.add (continuous_const_smul μ⁻¹))
  refine ⟨U, hU, u, ?_, ⟨0, 1, one_pos, Metric.closedBall_subset_ball hR1⟩, hu, hu ▸ hcont,
    hsol⟩
  exact (coordinateSlabBox_subset_closedBall n i 2 l).trans
    (Metric.closedBall_subset_ball (max_lt hRl hRe))

end EinsteinFull.Regeneration
