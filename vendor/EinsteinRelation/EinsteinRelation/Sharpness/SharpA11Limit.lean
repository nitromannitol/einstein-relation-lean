import EinsteinRelation.Sharpness.SharpExampleFromSteps
import EinsteinRelation.Mobility.ClockEstimateDischarge
import EinsteinRelation.Clock.LocalObservableAveraging
import EinsteinRelation.Entropy.DivergenceFromFisher

/-! # The limit of the `a₁₁` averages (end of Step 3 of Proposition 7.1)

Source: `paper/main.tex` 1256-1257: "the estimate `eq.clock-resolvent` applies to `a₁₁ - E a₁₁` in
place of `μ - Eμ`; letting `s ↓ 0` shows that this limit converges to `E a₁₁` as `λ ↓ 0`". The proof
is the clock estimate of `Mobility/ClockEstimateFromSteps.lean` with the observable `a₁₁` at the
origin, clamped at its ellipticity bound so that it is bounded everywhere. The clamp is inactive on
regular environments. The response bound of Proposition 6.1, applied to the centred observable, and
the Abel limit of the Laplace densities give `|A(λ) - E a₁₁| ≤ C λ`
(`exists_a11Estimate`). Hence `SharpA11LimitStep` follows from `ScalarDecompositionTwin` alone
(`sharpA11LimitStep_of_scalarDecomposition`).
-/

open MeasureTheory Filter
open scoped NNReal ENNReal Topology

noncomputable section

namespace EinsteinRelation.Sharpness

variable {d : ℕ}

/-- The ellipticity bound of the reduced coefficient. -/
def a11Bound (Λ₀ : ℝ) : ℝ := Real.exp (2 * Λ₀) * Λ₀

/-- The clamp of a diagonal coefficient entry at the origin to `[0, K]`. -/
def clampedEntry (K : ℝ) (i : Fin d) (p : Mat d × ℝ) : ℝ := max 0 (min K (p.1 i i))

theorem measurable_clampedEntry (K : ℝ) (i : Fin d) : Measurable (clampedEntry (d := d) K i) :=
  ((continuous_const.max (continuous_const.min (continuous_fst.matrix_elem i i)))).measurable

theorem clampedEntry_nonneg (K : ℝ) (i : Fin d) (p : Mat d × ℝ) : 0 ≤ clampedEntry K i p :=
  le_max_left _ _

theorem clampedEntry_le {K : ℝ} (hK : 0 ≤ K) (i : Fin d) (p : Mat d × ℝ) :
    clampedEntry K i p ≤ K :=
  max_le hK (min_le_left _ _)

theorem clampedEntry_eq {K : ℝ} (i : Fin d) {p : Mat d × ℝ} (h0 : 0 ≤ p.1 i i) (hK : p.1 i i ≤ K) :
    clampedEntry K i p = p.1 i i := by
  unfold clampedEntry
  rw [min_eq_right hK, max_eq_right h0]

/-- The diagonal entries of a regular reduced coefficient lie in `[0, a11Bound Λ₀]`. -/
theorem reducedCoefficient_diag_mem {Λ₀ : ℝ} (hΛ : 1 ≤ Λ₀) {ω : FieldPair d} (hω : IsRegular Λ₀ ω)
    (x : Vec d) (i : Fin d) :
    0 ≤ reducedCoefficient ω x i i ∧ reducedCoefficient ω x i i ≤ a11Bound Λ₀ := by
  have h := reducedCoefficient_energy_bounds ω x (unitVector i) Λ₀ hΛ hω
  have hdot : dot (unitVector i) ((reducedCoefficient ω x).mulVec (unitVector i)) =
      reducedCoefficient ω x i i := by
    simp [dot, unitVector, Matrix.mulVec, dotProduct, Pi.single_apply]
  have hsq : euclideanSq (unitVector (d := d) i) = 1 := by
    simp [euclideanSq, dot, unitVector, Pi.single_apply]
  rw [hdot, hsq, mul_one, mul_one] at h
  refine ⟨le_trans ?_ h.1, h.2⟩
  have hΛ0 : 0 < Λ₀ := by linarith
  positivity

/-! ## Fubini and the expectation limit -/

/-- The expected time integral of a bounded observable is the time integral of its expectation. -/
theorem integral_primitive_observation (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (P : QuenchedPathLaws d) (op : ∀ᵐ ω ∂Q, IsProbabilityMeasure (originLaw P ω))
    (g : FieldPair d → ℝ) (hg : Measurable g) {B : ℝ} (hB : ∀ w, |g w| ≤ B) {t : ℝ}
    (ht : 0 ≤ t) :
    ∫ z, (∫ u in (0 : ℝ)..t, g (Carriers.reducedObservationAt u.toNNReal z))
        ∂(Carriers.annealedCoordinateJoint Q P op) =
      ∫ u in (0 : ℝ)..t, Density.observationMean Q P op g u := by
  haveI : IsProbabilityMeasure (Carriers.annealedCoordinateJoint Q P op) :=
    Probability.ValidAnnealedLawSupport.annealedJointOnProbabilityFibers_isProbabilityMeasure Q
      (originLaw P) op
  set J := Carriers.annealedCoordinateJoint Q P op
  have hF : Measurable fun p : (FieldPair d × Path d) × ℝ =>
      g (Carriers.reducedObservationAt p.2.toNNReal p.1) :=
    hg.comp (laplaceDensity_measurable_observation.comp measurable_swap)
  have hint : Integrable (Function.uncurry fun (z : FieldPair d × Path d) (u : ℝ) =>
      g (Carriers.reducedObservationAt u.toNNReal z)) (J.prod (volume.restrict (Set.Ioc 0 t))) :=
    (integrable_const B).mono' hF.aestronglyMeasurable
      (ae_of_all _ fun p => by rw [Real.norm_eq_abs]; exact hB _)
  simp only [intervalIntegral.integral_of_le ht]
  rw [integral_integral_swap hint]
  rfl

/-- The expected primitive of the clamped entry, divided by the time, converges to the almost-sure
rate of the paths. -/
theorem tendsto_primitive_observationMean (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (P : QuenchedPathLaws d) (op : ∀ᵐ ω ∂Q, IsProbabilityMeasure (originLaw P ω)) {K : ℝ}
    (hK : 0 ≤ K) (i : Fin d) {A : ℝ}
    (hfib : ∀ᵐ ω ∂Q, ∀ᵐ γ ∂(originLaw P ω), Tendsto (fun t : ℝ≥0 =>
      (∫ u in (0 : ℝ)..(t : ℝ), clampedEntry K i
        ((Carriers.reducedObservationAt u.toNNReal (ω, γ)).1 0,
          (Carriers.reducedObservationAt u.toNNReal (ω, γ)).2 0)) / (t : ℝ)) atTop (𝓝 A)) :
    Tendsto (fun t : ℝ => (∫ u in (0 : ℝ)..t, Density.observationMean Q P op
      (fun w => clampedEntry K i (w.1 0, w.2 0)) u) / t) atTop (𝓝 A) := by
  haveI : IsProbabilityMeasure (Carriers.annealedCoordinateJoint Q P op) :=
    Probability.ValidAnnealedLawSupport.annealedJointOnProbabilityFibers_isProbabilityMeasure Q
      (originLaw P) op
  set J := Carriers.annealedCoordinateJoint Q P op
  set g : FieldPair d → ℝ := fun w => clampedEntry K i (w.1 0, w.2 0) with hgdef
  have hgm : Measurable g := (measurable_clampedEntry K i).comp
    ((((continuous_eval_const (0 : Vec d)).comp continuous_fst).prodMk
      ((continuous_eval_const (0 : Vec d)).comp continuous_snd)).measurable)
  have hg0 : ∀ w, 0 ≤ g w := fun w => clampedEntry_nonneg K i _
  have hgK : ∀ w, g w ≤ K := fun w => clampedEntry_le hK i _
  have hgB : ∀ w, |g w| ≤ K := fun w => by rw [abs_of_nonneg (hg0 w)]; exact hgK w
  have hobsF : Measurable fun p : (FieldPair d × Path d) × ℝ =>
      g (Carriers.reducedObservationAt p.2.toNNReal p.1) :=
    hgm.comp (laplaceDensity_measurable_observation.comp measurable_swap)
  set Φ : ℝ≥0 → FieldPair d × Path d → ℝ := fun s z =>
    ∫ u in (0 : ℝ)..(s : ℝ), g (Carriers.reducedObservationAt u.toNNReal z) with hΦdef
  have hΦm : ∀ s : ℝ≥0, Measurable (Φ s) := by
    intro s
    have hΦeq : Φ s = fun z => ∫ u in Set.Ioc 0 (s : ℝ),
        g (Carriers.reducedObservationAt u.toNNReal z) :=
      funext fun z => intervalIntegral.integral_of_le s.2
    rw [hΦeq]
    exact ((hobsF.stronglyMeasurable).integral_prod_right'
      (ν := (volume : Measure ℝ).restrict (Set.Ioc 0 (s : ℝ)))).measurable
  have hII : ∀ (z : FieldPair d × Path d) (a b : ℝ),
      IntervalIntegrable (fun u => g (Carriers.reducedObservationAt u.toNNReal z)) volume a b := by
    intro z a b
    refine (intervalIntegrable_const (c := K)).mono_fun
      (hobsF.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
      (ae_of_all _ fun u => ?_)
    simp only [Real.norm_eq_abs, abs_of_nonneg (hg0 _), abs_of_nonneg hK]
    exact hgK _
  have hΦ0 : ∀ s z, 0 ≤ Φ s z := fun s z =>
    intervalIntegral.integral_nonneg s.2 fun u _ => hg0 _
  have hΦK : ∀ (s : ℝ≥0) z, Φ s z ≤ K * (s : ℝ) := by
    intro s z
    have h := intervalIntegral.integral_mono_on s.2 (hII z 0 s) intervalIntegrable_const
      (fun u _ => hgK (Carriers.reducedObservationAt u.toNNReal z))
    simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at h
    calc Φ s z ≤ (s : ℝ) * K := h
      _ = K * (s : ℝ) := mul_comm _ _
  have hmono : ∀ z, Monotone fun s : ℝ≥0 => Φ s z := by
    intro z s s' hss'
    show Φ s z ≤ Φ s' z
    simp only [hΦdef]
    rw [← intervalIntegral.integral_add_adjacent_intervals (hII z 0 s) (hII z s s')]
    have : 0 ≤ ∫ u in (s : ℝ)..(s' : ℝ), g (Carriers.reducedObservationAt u.toNNReal z) :=
      intervalIntegral.integral_nonneg (by exact_mod_cast hss') fun u _ => hg0 _
    linarith
  have hS : MeasurableSet {z : FieldPair d × Path d |
      Tendsto (fun n : ℕ => Φ (n : ℝ≥0) z / ((n : ℝ≥0) : ℝ)) atTop (𝓝 A)} :=
    measurableSet_tendsto (𝓝 A) (f := fun (n : ℕ) z => Φ (n : ℝ≥0) z / ((n : ℝ≥0) : ℝ))
      fun n => (hΦm n).div_const _
  have hJ : ∀ᵐ z ∂J, z ∈ {z : FieldPair d × Path d |
      Tendsto (fun n : ℕ => Φ (n : ℝ≥0) z / ((n : ℝ≥0) : ℝ)) atTop (𝓝 A)} :=
    Clock.ae_annealedCoordinateJoint_mem Q P op hS
      (hfib.mono fun ω hω => hω.mono fun γ hγ => hγ.comp tendsto_natCast_atTop_atTop)
  have hlimJ : ∀ᵐ z ∂J, Tendsto (fun s : ℝ≥0 => Φ s z / (s : ℝ)) atTop (𝓝 A) :=
    hJ.mono fun z hz => Clock.tendsto_div_of_tendsto_natCast (fun s => hΦ0 s z) (hmono z) hz
  have hlim := Clock.tendsto_integral_clock_div_of_ae J Φ K A
    (fun s => (hΦm s).aestronglyMeasurable) (ae_of_all _ fun z s => ⟨hΦ0 s z, hΦK s z⟩) hlimJ
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  have h := integral_primitive_observation Q P op g hgm hgB ht
  simp only [hΦdef, Real.coe_toNNReal t ht]
  rw [h]

/-! ## The estimate `|A(λ) - E a₁₁| ≤ C λ` -/

private theorem sa_integral_rho_eq_one {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (P : QuenchedPathLaws d) (hprob : ∀ᵐ ω ∂Q.measure, IsProbabilityMeasure (originLaw P ω))
    (s : {r : ℝ // 0 < r}) {rho : FieldPair d → ℝ}
    (hrho : Carriers.IsReducedLaplaceDensity Q.measure P hprob s rho) :
    ∫ w, rho w ∂(Carriers.reducedReferenceLaw Q) = 1 ∧
      Integrable rho (Carriers.reducedReferenceLaw Q) := by
  obtain ⟨hm, hnn, hlaw⟩ := hrho
  haveI := laplaceDensity_isProbabilityMeasure_observed Q P hprob s
  have hone : ∫⁻ w, ENNReal.ofReal (rho w) ∂(Carriers.reducedReferenceLaw Q) = 1 := by
    have h := measure_univ (μ := Carriers.reducedLaplaceObservedLaw Q.measure P hprob s)
    rw [hlaw, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at h
    exact h
  have hint : Integrable rho (Carriers.reducedReferenceLaw Q) := by
    refine ⟨hm.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ hnn), hone]
    exact ENNReal.one_lt_top
  refine ⟨?_, hint⟩
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hnn) hm.aestronglyMeasurable, hone]
  simp

/-- **The `a₁₁` estimate** (`paper/main.tex` 1256-1257). With the constants of Proposition 6.1, for
every reduced family and every small force, the almost-sure time-average limit `A` of `a_ii` along the
reduced paths satisfies `|A - E a_ii| ≤ C λ`. -/
theorem exists_a11Estimate (H61 : ScalarDecompositionTwin) (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ)
    (hΛ₀ : 1 ≤ Λ₀) (hr₀ : 1 ≤ r₀) (i : Fin d) :
    ∃ C lamStar : ℝ, 0 < lamStar ∧ lamStar ≤ 1 ∧
      ∀ (Q : EnvironmentLaw d Λ₀ r₀) (P' : DiffusionFamily d),
        IsGMPReducedFamily hd Q.ellipticity_parameter Q P' →
        ∀ lam : ℝ, 0 < lam → lam ≤ lamStar → ∀ A : ℝ,
          (∀ᵐ ω ∂Q.measure, ∀ᵐ γ ∂(P' lam (0, ω)), Tendsto (fun t : ℝ≥0 =>
            (∫ u in (0 : ℝ)..(t : ℝ), reducedCoefficient ω (γ u.toNNReal) i i) / (t : ℝ))
              atTop (𝓝 A)) →
          |A - ∫ w, w.1 0 i i ∂(Carriers.reducedReferenceLaw Q)| ≤ C * lam := by
  set K := a11Bound Λ₀ with hKdef
  have hK : 0 ≤ K := by
    have : 0 < Λ₀ := by linarith
    rw [hKdef, a11Bound]
    exact mul_nonneg (Real.exp_pos _).le this.le
  obtain ⟨C₀, hC₀, l₀, hr₀l, hH'⟩ := H61 d hd Λ₀ r₀ hΛ₀ hr₀
  have hl₀ : 0 < l₀ := by linarith
  have hC₀l : 0 < 4 * C₀ := by linarith
  obtain ⟨p₀, -, hp⟩ := hH' l₀ le_rfl
  obtain ⟨M, -, hM⟩ := Clock.exists_observable_averaging d hd Λ₀ r₀ K
  obtain ⟨C, hC0, hHC⟩ := hp p₀ le_rfl (M (4 * p₀))
  refine ⟨C * (1 + l₀ / (2 * C₀) + 4 * C₀ / l₀), min 1 (l₀ / (4 * C₀)),
    lt_min one_pos (div_pos hl₀ hC₀l), min_le_left _ _, ?_⟩
  intro Q P' hGMP lam hl0 hlamle A hae
  have hlam1 : lam ≤ 1 := hlamle.trans (min_le_left _ _)
  have hsmall : lam ≤ l₀ / (4 * C₀) := hlamle.trans (min_le_right _ _)
  have hGMPlam :=
    (isGMPReducedFamily_iff hd Q.ellipticity_parameter Q P').mp hGMP lam hl0.le hlam1
  have hop : ∀ᵐ ω ∂Q.measure, IsProbabilityMeasure (originLaw (P' lam) ω) :=
    isProbabilityMeasure_of_isGMPReducedOriginLaw hd Q.ellipticity_parameter Q lam hl0.le hlam1
      (originLaw (P' lam)) hGMPlam
  have hex : ∀ s : {r : ℝ // 0 < r}, ∃ rho : FieldPair d → ℝ,
      Carriers.IsReducedLaplaceDensity Q.measure (P' lam) hop s rho :=
    fun s => exists_reducedLaplaceDensity_of_gmp hd Q hl0 hlam1 (P' lam) hop hGMPlam s
  choose rho hrho using hex
  haveI : IsProbabilityMeasure (Carriers.reducedReferenceLaw Q) :=
    Entropy.reducedReferenceLaw_isProbabilityMeasure Q
  set φ : Mat d × ℝ → ℝ := clampedEntry K i with hφdef
  set g : FieldPair d → ℝ := fun w => φ (w.1 0, w.2 0) with hgdef
  have hφm : Measurable φ := measurable_clampedEntry K i
  have hgm : Measurable g := hφm.comp
    ((((continuous_eval_const (0 : Vec d)).comp continuous_fst).prodMk
      ((continuous_eval_const (0 : Vec d)).comp continuous_snd)).measurable)
  have hgB : ∀ w, |g w| ≤ K := fun w => by
    rw [abs_of_nonneg (clampedEntry_nonneg K i _)]; exact clampedEntry_le hK i _
  -- The clamp is inactive along the paths of regular environments.
  have hfib : ∀ᵐ ω ∂Q.measure, ∀ᵐ γ ∂(originLaw (P' lam) ω), Tendsto (fun t : ℝ≥0 =>
      (∫ u in (0 : ℝ)..(t : ℝ), clampedEntry K i
        ((Carriers.reducedObservationAt u.toNNReal (ω, γ)).1 0,
          (Carriers.reducedObservationAt u.toNNReal (ω, γ)).2 0)) / (t : ℝ)) atTop (𝓝 A) := by
    filter_upwards [hae, Q.regular] with ω hω hreg
    filter_upwards [hω] with γ hγ
    refine hγ.congr fun t => ?_
    congr 1
    refine intervalIntegral.integral_congr fun u _ => ?_
    show reducedCoefficient ω (γ u.toNNReal) i i =
      clampedEntry K i ((translate (γ u.toNNReal) (reduce ω)).1 0,
        (translate (γ u.toNNReal) (reduce ω)).2 0)
    rw [translate_matrix, add_zero]
    obtain ⟨h0, h1⟩ := reducedCoefficient_diag_mem hΛ₀ hreg (γ u.toNNReal) i
    exact (clampedEntry_eq (K := K) (p := ((reduce ω).1 (γ u.toNNReal),
      (translate (γ u.toNNReal) (reduce ω)).2 0)) i h0 h1).symm
  have hlim := tendsto_primitive_observationMean Q.measure (P' lam) hop hK i hfib
  have hF_tend := Density.tendsto_integral_mul_density Q.measure (P' lam) hop rho hrho g hgm hgB A
    hlim
  -- The mean of the clamped observable is the mean of `a_ii`.
  set m : ℝ := ∫ w, g w ∂(Carriers.reducedReferenceLaw Q) with hmdef
  have hm : m = ∫ w, w.1 0 i i ∂(Carriers.reducedReferenceLaw Q) := by
    have hset : MeasurableSet {w : FieldPair d | 0 ≤ w.1 0 i i ∧ w.1 0 i i ≤ K} := by
      have hc : Continuous fun w : FieldPair d => w.1 0 i i :=
        ((continuous_eval_const (0 : Vec d)).comp continuous_fst).matrix_elem i i
      exact (measurableSet_le measurable_const hc.measurable).inter
        (measurableSet_le hc.measurable measurable_const)
    have hae' : ∀ᵐ w ∂(Carriers.reducedReferenceLaw Q), 0 ≤ w.1 0 i i ∧ w.1 0 i i ≤ K := by
      unfold Carriers.reducedReferenceLaw
      refine (ae_map_iff (Probability.measurable_reduce (d := d)).aemeasurable hset).2 ?_
      filter_upwards [Q.regular] with η hη
      exact reducedCoefficient_diag_mem hΛ₀ hη 0 i
    refine integral_congr_ae (hae'.mono fun w hw => ?_)
    exact clampedEntry_eq i hw.1 hw.2
  have hF' : ∀ R : ℝ, 2 ≤ R → (∃ k : ℕ, R = 2 ^ k) → C₀ * R ≤ l₀ / (2 * lam) →
      l₀ / (4 * C₀ * lam) ≤ R → ∀ s : ℝ, 0 < s → s ≤ lam ^ 2 →
      |(if hs : 0 < s then ∫ w, rho ⟨s, hs⟩ w * g w ∂(Measure.map reduce Q.measure) else 0) - m| ≤
        C * (s * R + lam + lam ^ 2 * R + R⁻¹) := by
    intro R hR2 hRk hup _ s hs hsle
    have hRpos : 0 < R := by linarith
    have hbd : ∀ᵐ w ∂(Carriers.reducedReferenceLaw Q), |φ (w.1 (0 : Vec d), w.2 (0 : Vec d))| ≤ K :=
      ae_of_all _ fun w => hgB w
    have hHR := hHC Q (Clock.isStationary_reducedReferenceLaw Q) M rfl R hR2 hRk
      (Clock.centredObservable Q φ) (hM Q φ hφm hbd R hRpos)
    have hb := hHR.2 lam hl0 hlam1 hup Q.measure Q.probability (P' lam) hop
      ⟨rfl, hGMPlam⟩ ⟨s, hs⟩ hsle (rho ⟨s, hs⟩) (hrho ⟨s, hs⟩)
    rw [dif_pos hs]
    obtain ⟨hρ1, hρint⟩ := sa_integral_rho_eq_one Q (P' lam) hop ⟨s, hs⟩ (hrho ⟨s, hs⟩)
    have hρg : Integrable (fun w => rho ⟨s, hs⟩ w * g w) (Carriers.reducedReferenceLaw Q) :=
      hρint.mul_bdd hgm.aestronglyMeasurable (ae_of_all _ fun w => by
        rw [Real.norm_eq_abs]; exact hgB w)
    have heq : (∫ w, rho ⟨s, hs⟩ w * g w ∂(Carriers.reducedReferenceLaw Q)) - m =
        ∫ w, rho ⟨s, hs⟩ w * Clock.centredObservable Q φ w ∂(Carriers.reducedReferenceLaw Q) := by
      have hpt : ∀ w, rho ⟨s, hs⟩ w * Clock.centredObservable Q φ w =
          rho ⟨s, hs⟩ w * g w - m * rho ⟨s, hs⟩ w := fun w => by
        simp only [Clock.centredObservable, hgdef, hmdef]
        ring
      rw [integral_congr_ae (ae_of_all _ hpt), integral_sub hρg (hρint.const_mul m),
        integral_const_mul, hρ1, mul_one]
    change |(∫ w, rho ⟨s, hs⟩ w * g w ∂(Carriers.reducedReferenceLaw Q)) - m| ≤ _
    rw [heq]
    exact hb.2
  have hest := Clock.clock_rate_of_resolvent C₀ l₀ hC₀ hl₀ lam hl0 hsmall
    (fun s : ℝ => if hs : 0 < s then
      ∫ w, rho ⟨s, hs⟩ w * g w ∂(Measure.map reduce Q.measure) else 0)
    m A C hC0 hF' hF_tend
  rw [← hm]
  exact hest

/-- **`SharpA11LimitStep` from Proposition 6.1** (`paper/main.tex` 1256-1257): the time-average limits
`A(λ)` of `a₁₁` converge to `E a₁₁` as `λ ↓ 0`, at rate `O(λ)`. The sharp structure of the law is not
used. -/
theorem sharpA11LimitStep_of_scalarDecomposition (H61 : ScalarDecompositionTwin) (hd : 2 ≤ d) :
    SharpA11LimitStep hd := by
  intro Λ₀ r₀ δ Q _ P' hP' A hA
  set i₀ : Fin d := ⟨0, by omega⟩ with hi₀
  obtain ⟨C, lamStar, hls0, hls1, hest⟩ :=
    exists_a11Estimate H61 d hd Λ₀ r₀ Q.ellipticity_parameter Q.range_parameter i₀
  have hmean : ∫ ω, sharpA11 hd ω 0 ∂Q.measure =
      ∫ w, w.1 0 i₀ i₀ ∂(Carriers.reducedReferenceLaw Q) := by
    unfold Carriers.reducedReferenceLaw
    have hc : Continuous fun w : FieldPair d => w.1 0 i₀ i₀ :=
      ((continuous_eval_const (0 : Vec d)).comp continuous_fst).matrix_elem i₀ i₀
    rw [integral_map (Probability.measurable_reduce (d := d)).aemeasurable
      hc.aestronglyMeasurable]
    rfl
  rw [hmean, Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  refine ⟨min lamStar (ε / (|C| + 1)), lt_min hls0 (by positivity), fun lam hlam hdist => ?_⟩
  have hl0 : 0 < lam := hlam
  rw [Real.dist_eq, sub_zero, abs_of_pos hl0] at hdist
  have hlS : lam ≤ lamStar := (lt_of_lt_of_le hdist (min_le_left _ _)).le
  have hlε : lam < ε / (|C| + 1) := lt_of_lt_of_le hdist (min_le_right _ _)
  have hb := hest Q P' hP' lam hl0 hlS (A lam) (hA lam hl0 (hlS.trans hls1))
  rw [Real.dist_eq]
  calc |A lam - ∫ w, w.1 0 i₀ i₀ ∂(Carriers.reducedReferenceLaw Q)| ≤ C * lam := hb
    _ ≤ |C| * lam := mul_le_mul_of_nonneg_right (le_abs_self C) hl0.le
    _ < (|C| + 1) * (ε / (|C| + 1)) := by
        have := mul_lt_mul_of_pos_left hlε (by positivity : (0 : ℝ) < |C| + 1)
        nlinarith [abs_nonneg C]
    _ = ε := by field_simp

end EinsteinRelation.Sharpness
