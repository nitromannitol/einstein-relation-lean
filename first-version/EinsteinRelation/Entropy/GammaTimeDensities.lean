import EinsteinRelation.Entropy.GammaTimes
import EinsteinRelation.Density.LaplaceDensityIntegral
import EinsteinRelation.Density.LaplaceDensityAbel
import EinsteinRelation.Regeneration.FirstRewardFromGirsanov
import EinsteinRelation.Entropy.EllipticRegularity

/-! # Densities at Gamma times

The reduced environment law at an independent Gamma(m+1, μ) time, `ν_m`, and its density `ρ_m`
with respect to the reduced reference law. These are the densities of the discrete resolvent route
to Lemma 4.1. The file proves

* `integral_mul_gammaDensity`: `∫ ρ_m g = ∫ gk_m(t) E[g(ω_t)] dt` for bounded measurable `g`;
* `reducedLaplaceObservedLaw_eq_sum`: the exponential-time law of rate `s ≤ μ` is the mixture
  `∑ w_m ν_m`, so `ρ_s = ∑ w_m ρ_m` almost everywhere (`ae_laplaceDensity_eq_tsum`).
-/

open MeasureTheory Filter Set
open scoped Topology ENNReal NNReal

noncomputable section

namespace EinsteinRelation.Entropy

variable {d : ℕ}

/-! ## The Gamma time law -/

/-- The Gamma(m+1, μ) law on the time axis. -/
def gammaTimeLaw (μ : ℝ) (m : ℕ) : Measure ℝ :=
  (volume : Measure ℝ).withDensity fun t => ENNReal.ofReal (gk μ m t)

instance (μ : ℝ) (m : ℕ) : SFinite (gammaTimeLaw μ m) := by
  unfold gammaTimeLaw
  infer_instance

theorem isProbabilityMeasure_gammaTimeLaw {μ : ℝ} (hμ : 0 < μ) (m : ℕ) :
    IsProbabilityMeasure (gammaTimeLaw μ m) := by
  constructor
  rw [gammaTimeLaw, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (integrable_gk hμ m) (ae_of_all _ (gk_nonneg hμ.le m)),
    integral_gk hμ m, ENNReal.ofReal_one]

theorem integral_gammaTimeLaw {μ : ℝ} (hμ : 0 < μ) (m : ℕ) (φ : ℝ → ℝ) :
    ∫ t, φ t ∂(gammaTimeLaw μ m) = ∫ t, gk μ m t * φ t := by
  rw [gammaTimeLaw, integral_withDensity_eq_integral_toReal_smul
    (measurable_gk μ m).ennreal_ofReal (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (ae_of_all _ fun t => ?_)
  simp only [ENNReal.toReal_ofReal (gk_nonneg hμ.le m t), smul_eq_mul]

theorem ae_gammaTimeLaw_pos (μ : ℝ) (m : ℕ) : ∀ᵐ t ∂(gammaTimeLaw μ m), 0 < t := by
  rw [gammaTimeLaw, ae_withDensity_iff (measurable_gk μ m).ennreal_ofReal]
  have hne : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ 0 :=
    measure_eq_zero_iff_ae_notMem.mp (Real.volume_singleton (a := (0 : ℝ)))
  filter_upwards [hne] with x hx hpos
  rcases lt_trichotomy x 0 with h | h | h
  · rw [gk_of_neg μ m h, ENNReal.ofReal_zero] at hpos
    exact absurd rfl hpos
  · exact absurd h hx
  · exact h

/-! ## The observed law at a Gamma time -/

/-- The reduced environment law at an independent Gamma(m+1, μ) time. -/
def gammaObservedLaw (Q : Measure (FieldPair d)) (P : QuenchedPathLaws d)
    (op : ∀ᵐ ω ∂Q, IsProbabilityMeasure (originLaw P ω)) (μ : ℝ) (m : ℕ) :
    Measure (FieldPair d) :=
  ((gammaTimeLaw μ m).prod (Carriers.annealedCoordinateJoint Q P op)).map
    (fun z : ℝ × (FieldPair d × Path d) => Carriers.reducedObservationAt z.1.toNNReal z.2)

theorem isProbabilityMeasure_gammaObservedLaw (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (P : QuenchedPathLaws d) (op : ∀ᵐ ω ∂Q, IsProbabilityMeasure (originLaw P ω)) {μ : ℝ}
    (hμ : 0 < μ) (m : ℕ) : IsProbabilityMeasure (gammaObservedLaw Q P op μ m) := by
  haveI := isProbabilityMeasure_gammaTimeLaw hμ m
  haveI := Density.isProbabilityMeasure_annealedCoordinateJoint Q P op
  exact Measure.isProbabilityMeasure_map
    (laplaceDensity_measurable_observation (d := d)).aemeasurable

theorem integral_gammaObservedLaw (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (P : QuenchedPathLaws d) (op : ∀ᵐ ω ∂Q, IsProbabilityMeasure (originLaw P ω)) {μ : ℝ}
    (hμ : 0 < μ) (m : ℕ) (g : FieldPair d → ℝ) (hg : Measurable g) {B : ℝ}
    (hB : ∀ w, |g w| ≤ B) :
    ∫ w, g w ∂(gammaObservedLaw Q P op μ m) =
      ∫ t, gk μ m t * Density.observationMean Q P op g t := by
  haveI := isProbabilityMeasure_gammaTimeLaw hμ m
  haveI := Density.isProbabilityMeasure_annealedCoordinateJoint Q P op
  have hobs := laplaceDensity_measurable_observation (d := d)
  have hint : Integrable (fun z : ℝ × (FieldPair d × Path d) =>
      g (Carriers.reducedObservationAt z.1.toNNReal z.2))
      ((gammaTimeLaw μ m).prod (Carriers.annealedCoordinateJoint Q P op)) :=
    Integrable.of_bound (hg.comp hobs).aestronglyMeasurable B
      (ae_of_all _ fun z => by rw [Real.norm_eq_abs]; exact hB _)
  unfold gammaObservedLaw
  rw [integral_map hobs.aemeasurable hg.aestronglyMeasurable, integral_prod _ hint,
    integral_gammaTimeLaw hμ m]
  rfl

theorem gammaObservedLaw_absolutelyContinuous {Λ₀ r₀ : ℝ} (hd : 2 ≤ d)
    (Q : EnvironmentLaw d Λ₀ r₀) {lam : ℝ} (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (P : QuenchedPathLaws d) (op : ∀ᵐ ω ∂Q.measure, IsProbabilityMeasure (originLaw P ω))
    (hGMP : IsGMPReducedOriginLaw hd Q.ellipticity_parameter Q lam h0 h1 (originLaw P))
    (μ : ℝ) (m : ℕ) :
    gammaObservedLaw Q.measure P op μ m ≪ Measure.map reduce Q.measure := by
  intro A hA0
  obtain ⟨B, hAB, hBm, hB0⟩ := exists_measurable_superset_of_null hA0
  refine measure_mono_null hAB ?_
  haveI : IsProbabilityMeasure (Carriers.annealedCoordinateJoint Q.measure P op) :=
    Density.isProbabilityMeasure_annealedCoordinateJoint _ P op
  have hzero : ∀ᵐ τ ∂(gammaTimeLaw μ m),
      Carriers.annealedCoordinateJoint Q.measure P op
        (Prod.mk τ ⁻¹' ((fun z : ℝ × (FieldPair d × Path d) =>
          Carriers.reducedObservationAt z.1.toNNReal z.2) ⁻¹' B)) = 0 := by
    filter_upwards [ae_gammaTimeLaw_pos μ m] with τ hτ
    have hset : Prod.mk τ ⁻¹' ((fun z : ℝ × (FieldPair d × Path d) =>
        Carriers.reducedObservationAt z.1.toNNReal z.2) ⁻¹' B) =
        {q : FieldPair d × Path d | Carriers.reducedObservationAt (Real.toNNReal τ) q ∈ B} :=
      Set.ext fun q => Iff.rfl
    rw [hset]
    exact laplaceDensity_observed_time_null hd Q h0 h1 P op hGMP hBm hB0
      (t := Real.toNNReal τ) (Real.toNNReal_pos.mpr hτ)
  unfold gammaObservedLaw
  exact laplaceDensity_map_prod_apply_eq_zero (gammaTimeLaw μ m) _
    (laplaceDensity_measurable_observation (d := d)) hBm hzero

/-- A density of the reduced environment law at a Gamma(m+1, μ) time. -/
def IsGammaDensity (Q : Measure (FieldPair d)) (P : QuenchedPathLaws d)
    (op : ∀ᵐ ω ∂Q, IsProbabilityMeasure (originLaw P ω)) (μ : ℝ) (m : ℕ)
    (rho : FieldPair d → ℝ) : Prop :=
  Measurable rho ∧ (∀ w, 0 ≤ rho w) ∧
    gammaObservedLaw Q P op μ m = (Measure.map reduce Q).withDensity fun w => ENNReal.ofReal (rho w)

theorem exists_gammaDensity {Λ₀ r₀ : ℝ} (hd : 2 ≤ d) (Q : EnvironmentLaw d Λ₀ r₀) {lam : ℝ}
    (h0 : 0 ≤ lam) (h1 : lam ≤ 1) (P : QuenchedPathLaws d)
    (op : ∀ᵐ ω ∂Q.measure, IsProbabilityMeasure (originLaw P ω))
    (hGMP : IsGMPReducedOriginLaw hd Q.ellipticity_parameter Q lam h0 h1 (originLaw P))
    {μ : ℝ} (hμ : 0 < μ) (m : ℕ) : ∃ rho, IsGammaDensity Q.measure P op μ m rho := by
  haveI : IsProbabilityMeasure (Measure.map reduce Q.measure) :=
    Measure.isProbabilityMeasure_map (Probability.measurable_reduce (d := d)).aemeasurable
  haveI := isProbabilityMeasure_gammaObservedLaw Q.measure P op hμ m
  exact laplaceDensity_exists_density _ _
    (gammaObservedLaw_absolutelyContinuous hd Q h0 h1 P op hGMP μ m)

theorem integral_mul_gammaDensity (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (P : QuenchedPathLaws d) (op : ∀ᵐ ω ∂Q, IsProbabilityMeasure (originLaw P ω)) {μ : ℝ}
    (hμ : 0 < μ) (m : ℕ) {rho : FieldPair d → ℝ} (hrho : IsGammaDensity Q P op μ m rho)
    (g : FieldPair d → ℝ) (hg : Measurable g) {B : ℝ} (hB : ∀ w, |g w| ≤ B) :
    ∫ w, rho w * g w ∂(Measure.map reduce Q) =
      ∫ t, gk μ m t * Density.observationMean Q P op g t := by
  obtain ⟨hρ, hnonneg, hlaw⟩ := hrho
  have hm : Measurable (fun w => ENNReal.ofReal (rho w)) := ENNReal.measurable_ofReal.comp hρ
  have hdens : ∫ w, g w ∂((Measure.map reduce Q).withDensity fun w => ENNReal.ofReal (rho w)) =
      ∫ w, rho w * g w ∂(Measure.map reduce Q) := by
    rw [integral_withDensity_eq_integral_toReal_smul hm
      (ae_of_all _ fun w => ENNReal.ofReal_lt_top) g]
    refine integral_congr_ae (ae_of_all _ fun w => ?_)
    show (ENNReal.ofReal (rho w)).toReal • g w = rho w * g w
    rw [ENNReal.toReal_ofReal (hnonneg w), smul_eq_mul]
  rw [← hdens, ← hlaw]
  exact integral_gammaObservedLaw Q P op hμ m g hg hB

/-! ## The exponential-time law as a Gamma mixture -/

theorem expMeasure_eq_sum {s μ : ℝ} (hs : 0 < s) (hsμ : s ≤ μ) :
    ProbabilityTheory.expMeasure s =
      Measure.sum fun m => ENNReal.ofReal (gweight s μ m) • gammaTimeLaw μ m := by
  have hμ : 0 < μ := hs.trans_le hsμ
  have hpdf : ProbabilityTheory.exponentialPDF s =
      ∑' m, fun t => ENNReal.ofReal (gweight s μ m * gk μ m t) := by
    funext t
    rw [exponentialPDF_eq_tsum hs hsμ t, ENNReal.tsum_apply]
  rw [show ProbabilityTheory.expMeasure s =
      (volume : Measure ℝ).withDensity (ProbabilityTheory.exponentialPDF s) from rfl, hpdf,
    withDensity_tsum fun m => ((measurable_gk μ m).const_mul _).ennreal_ofReal]
  congr 1
  funext m
  rw [gammaTimeLaw, ← withDensity_smul _ (measurable_gk μ m).ennreal_ofReal]
  congr 1
  funext t
  rw [Pi.smul_apply, smul_eq_mul, ENNReal.ofReal_mul (gweight_nonneg hs.le hsμ hμ m)]

theorem reducedLaplaceObservedLaw_eq_sum (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (P : QuenchedPathLaws d) (op : ∀ᵐ ω ∂Q, IsProbabilityMeasure (originLaw P ω)) {s μ : ℝ}
    (hs : 0 < s) (hsμ : s ≤ μ) :
    Carriers.reducedLaplaceObservedLaw Q P op ⟨s, hs⟩ =
      Measure.sum fun m => ENNReal.ofReal (gweight s μ m) • gammaObservedLaw Q P op μ m := by
  haveI := Density.isProbabilityMeasure_annealedCoordinateJoint Q P op
  unfold Carriers.reducedLaplaceObservedLaw gammaObservedLaw
  rw [expMeasure_eq_sum hs hsμ, Measure.prod_sum_left,
    Measure.map_sum (laplaceDensity_measurable_observation (d := d)).aemeasurable]
  congr 1
  funext m
  rw [Measure.prod_smul_left, Measure.map_smul]

/-- **The Laplace density is the Gamma mixture of the Gamma densities**, almost everywhere. -/
theorem ae_laplaceDensity_eq_tsum (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (P : QuenchedPathLaws d) (op : ∀ᵐ ω ∂Q, IsProbabilityMeasure (originLaw P ω)) {s μ : ℝ}
    (hs : 0 < s) (hsμ : s ≤ μ) {rho : FieldPair d → ℝ}
    (hrho : Carriers.IsReducedLaplaceDensity Q P op ⟨s, hs⟩ rho) {ρ : ℕ → FieldPair d → ℝ}
    (hρ : ∀ m, IsGammaDensity Q P op μ m (ρ m)) :
    ∀ᵐ w ∂(Measure.map reduce Q), ENNReal.ofReal (rho w) =
      ∑' m, ENNReal.ofReal (gweight s μ m) * ENNReal.ofReal (ρ m w) := by
  haveI : IsProbabilityMeasure (Measure.map reduce Q) :=
    Measure.isProbabilityMeasure_map (Probability.measurable_reduce (d := d)).aemeasurable
  obtain ⟨hρm, -, hlaw⟩ := hrho
  have hm : ∀ m, Measurable fun w => ENNReal.ofReal (gweight s μ m) * ENNReal.ofReal (ρ m w) :=
    fun m => ((hρ m).1.ennreal_ofReal).const_mul _
  have hsum : (Measure.map reduce Q).withDensity (fun w => ENNReal.ofReal (rho w)) =
      (Measure.map reduce Q).withDensity
        (∑' m, fun w => ENNReal.ofReal (gweight s μ m) * ENNReal.ofReal (ρ m w)) := by
    rw [← hlaw, reducedLaplaceObservedLaw_eq_sum Q P op hs hsμ, withDensity_tsum hm]
    congr 1
    funext m
    rw [(hρ m).2.2, ← withDensity_smul _ (hρ m).1.ennreal_ofReal]
    rfl
  have hfin : ∫⁻ w, ENNReal.ofReal (rho w) ∂(Measure.map reduce Q) ≠ ∞ := by
    have h1 : (Measure.map reduce Q).withDensity (fun w => ENNReal.ofReal (rho w)) univ = 1 := by
      haveI := Density.isProbabilityMeasure_annealedCoordinateJoint Q P op
      haveI := ProbabilityTheory.isProbabilityMeasure_expMeasure hs
      haveI : IsProbabilityMeasure (Carriers.reducedLaplaceObservedLaw Q P op ⟨s, hs⟩) := by
        unfold Carriers.reducedLaplaceObservedLaw
        exact Measure.isProbabilityMeasure_map
          (laplaceDensity_measurable_observation (d := d)).aemeasurable
      rw [← hlaw]
      exact measure_univ
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at h1
    rw [h1]
    exact ENNReal.one_ne_top
  have hsum' : (Measure.map reduce Q).withDensity (fun w => ENNReal.ofReal (rho w)) =
      (Measure.map reduce Q).withDensity
        (fun w => ∑' m, ENNReal.ofReal (gweight s μ m) * ENNReal.ofReal (ρ m w)) := by
    rw [hsum]
    congr 1
    funext w
    exact ENNReal.tsum_apply
  exact (withDensity_eq_iff hρm.ennreal_ofReal.aemeasurable
    (Measurable.ennreal_tsum hm).aemeasurable hfin).mp hsum'

/-! ## The `L²` bound -/

theorem integrable_gammaDensity (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (P : QuenchedPathLaws d) (op : ∀ᵐ ω ∂Q, IsProbabilityMeasure (originLaw P ω)) {μ : ℝ}
    (hμ : 0 < μ) (m : ℕ) {rho : FieldPair d → ℝ} (hrho : IsGammaDensity Q P op μ m rho) :
    Integrable rho (Measure.map reduce Q) := by
  haveI := isProbabilityMeasure_gammaObservedLaw Q P op hμ m
  have h1 : ∫⁻ w, ENNReal.ofReal (rho w) ∂(Measure.map reduce Q) = 1 := by
    have h := measure_univ (μ := gammaObservedLaw Q P op μ m)
    rw [hrho.2.2, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at h
    exact h
  refine ⟨hrho.1.aestronglyMeasurable, ?_⟩
  unfold HasFiniteIntegral
  have e : ∀ w, ‖rho w‖ₑ = ENNReal.ofReal (rho w) := fun w =>
    Real.enorm_eq_ofReal (hrho.2.1 w)
  simp only [e, h1]
  exact ENNReal.one_lt_top

/-- **Girsanov at a fixed time** for a bounded nonnegative observable:
`E^λ[ψ(ω_t)] ≤ e^{c t} ‖ψ‖₂` with `c = ½ K λ²`. -/
theorem observationMean_le_of_girsanov {Λ₀ r₀ : ℝ} (hGir : GirsanovEndpointStep)
    (hInv : UnforcedEnvironmentInvarianceStep) (hd : 2 ≤ d) (Q : EnvironmentLaw d Λ₀ r₀)
    {lam : ℝ} (h0 : 0 ≤ lam) (h1 : lam ≤ 1) (P : QuenchedPathLaws d)
    (hP : IsGMPReducedOriginLaw hd Q.ellipticity_parameter Q lam h0 h1 (originLaw P))
    (op : ∀ᵐ ω ∂Q.measure, IsProbabilityMeasure (originLaw P ω))
    (P' : DiffusionFamily d) (hP' : IsGMPReducedFamily hd Q.ellipticity_parameter Q P')
    (hP'0 : ∀ᵐ ω ∂Q.measure, IsProbabilityMeasure (originLaw (P' 0) ω))
    {ψ : FieldPair d → ℝ} (hψm : Measurable ψ) (hψ0 : ∀ w, 0 ≤ ψ w) {M : ℝ}
    (hψM : ∀ w, ψ w ≤ M) {t : ℝ} (ht : 0 ≤ t) :
    Density.observationMean Q.measure P op ψ t ≤
      Real.exp ((1 / 2) * sourceReducedBound Λ₀ * lam ^ 2 * t) *
        Real.sqrt (∫ w, ψ w ^ 2 ∂(Carriers.reducedReferenceLaw Q)) := by
  haveI : IsProbabilityMeasure (Carriers.annealedCoordinateJoint Q.measure P op) :=
    Density.isProbabilityMeasure_annealedCoordinateJoint _ P op
  haveI : IsProbabilityMeasure (Carriers.reducedReferenceLaw Q) :=
    Entropy.reducedReferenceLaw_isProbabilityMeasure Q
  have h := annealed_sq_le_of_girsanov_origin hGir hInv hd Q h0 h1 P hP op P' hP' hP'0
    (G := fun w => Real.sqrt (ψ w)) (Real.continuous_sqrt.measurable.comp hψm) t.toNNReal
    (q := 2) one_lt_two
  have e1 : ∀ x : ℝ, 0 ≤ x → ENNReal.ofReal |Real.sqrt x| ^ (2 : ℝ) = ENNReal.ofReal x :=
    fun x hx => by
      rw [abs_of_nonneg (Real.sqrt_nonneg x), ENNReal.ofReal_rpow_of_nonneg (Real.sqrt_nonneg x)
        (by norm_num), Real.rpow_two, Real.sq_sqrt hx]
  have e2 : ∀ x : ℝ, 0 ≤ x →
      ENNReal.ofReal |Real.sqrt x| ^ (2 * ((2 : ℝ) / (2 - 1))) = ENNReal.ofReal (x ^ 2) :=
    fun x hx => by
      rw [abs_of_nonneg (Real.sqrt_nonneg x), ENNReal.ofReal_rpow_of_nonneg (Real.sqrt_nonneg x)
        (by norm_num), show (2 : ℝ) * (2 / (2 - 1)) = (2 : ℕ) * 2 by norm_num, Real.rpow_mul
        (Real.sqrt_nonneg x), Real.rpow_natCast, Real.sq_sqrt hx, Real.rpow_two]
  simp only [e1 _ (hψ0 _), e2 _ (hψ0 _)] at h
  have hψ2 : Integrable (fun w => ψ w ^ 2) (Carriers.reducedReferenceLaw Q) :=
    Integrable.of_bound (hψm.pow_const 2).aestronglyMeasurable (M ^ 2) (ae_of_all _ fun w => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (hψ0 w) (hψM w) 2)
  rw [← ofReal_integral_eq_lintegral_ofReal hψ2 (ae_of_all _ fun w => sq_nonneg _),
    show ((2 : ℝ) - 1) / 2 = 1 / 2 by norm_num,
    ENNReal.ofReal_rpow_of_nonneg (integral_nonneg fun w => sq_nonneg _) (by norm_num),
    ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.sqrt_eq_rpow, Real.coe_toNNReal t ht] at h
  have hobs := laplaceDensity_measurable_observation_fixed (d := d) t.toNNReal
  have hm : Density.observationMean Q.measure P op ψ t =
      (∫⁻ z, ENNReal.ofReal (ψ (Carriers.reducedObservationAt t.toNNReal z))
        ∂(Carriers.annealedCoordinateJoint Q.measure P op)).toReal := by
    unfold Density.observationMean
    exact integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun z => hψ0 _)
      (hψm.comp hobs).aestronglyMeasurable
  rw [hm]
  have h' := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
  rw [ENNReal.toReal_ofReal (mul_nonneg (Real.exp_pos _).le (Real.sqrt_nonneg _))] at h'
  convert h' using 2
  ring

/-- The Gamma density integrates bounded nonnegative observables with the `L²` bound
`∫ ρ_m ψ ≤ (μ/(μ - c))^{m+1} ‖ψ‖₂`, `c = ½ K λ² < μ`. -/
theorem integral_mul_gammaDensity_le {Λ₀ r₀ : ℝ} (hGir : GirsanovEndpointStep)
    (hInv : UnforcedEnvironmentInvarianceStep) (hd : 2 ≤ d) (Q : EnvironmentLaw d Λ₀ r₀)
    {lam : ℝ} (h0 : 0 ≤ lam) (h1 : lam ≤ 1) (P : QuenchedPathLaws d)
    (hP : IsGMPReducedOriginLaw hd Q.ellipticity_parameter Q lam h0 h1 (originLaw P))
    (op : ∀ᵐ ω ∂Q.measure, IsProbabilityMeasure (originLaw P ω))
    (P' : DiffusionFamily d) (hP' : IsGMPReducedFamily hd Q.ellipticity_parameter Q P')
    (hP'0 : ∀ᵐ ω ∂Q.measure, IsProbabilityMeasure (originLaw (P' 0) ω))
    {μ : ℝ} (hμ : (1 / 2) * sourceReducedBound Λ₀ * lam ^ 2 < μ) (m : ℕ)
    {rho : FieldPair d → ℝ} (hrho : IsGammaDensity Q.measure P op μ m rho)
    {ψ : FieldPair d → ℝ} (hψm : Measurable ψ) (hψ0 : ∀ w, 0 ≤ ψ w) {M : ℝ}
    (hψM : ∀ w, ψ w ≤ M) :
    ∫ w, rho w * ψ w ∂(Carriers.reducedReferenceLaw Q) ≤
      (μ / (μ - (1 / 2) * sourceReducedBound Λ₀ * lam ^ 2)) ^ (m + 1) *
        Real.sqrt (∫ w, ψ w ^ 2 ∂(Carriers.reducedReferenceLaw Q)) := by
  set c := (1 / 2) * sourceReducedBound Λ₀ * lam ^ 2 with hcdef
  have hc0 : 0 ≤ c := by
    have := (sourceReducedBound_pos' Λ₀).le
    positivity
  have hμ0 : 0 < μ := hc0.trans_lt hμ
  haveI : IsProbabilityMeasure (Carriers.annealedCoordinateJoint Q.measure P op) :=
    Density.isProbabilityMeasure_annealedCoordinateJoint _ P op
  have hB : ∀ w, |ψ w| ≤ M := fun w => by rw [abs_of_nonneg (hψ0 w)]; exact hψM w
  have href : Carriers.reducedReferenceLaw Q = Measure.map reduce Q.measure := rfl
  rw [href, integral_mul_gammaDensity Q.measure P op hμ0 m hrho ψ hψm hB, ← href]
  set R := Real.sqrt (∫ w, ψ w ^ 2 ∂(Carriers.reducedReferenceLaw Q)) with hRdef
  have hmeas := Density.measurable_integral_reducedObservationAt Q.measure P op ψ hψm
  have hle : ∀ t, gk μ m t * Density.observationMean Q.measure P op ψ t ≤
      R * (gk μ m t * Real.exp (c * t)) := fun t => by
    by_cases ht : 0 ≤ t
    · have hg := observationMean_le_of_girsanov hGir hInv hd Q h0 h1 P hP op P' hP' hP'0 hψm hψ0
        hψM ht
      rw [← hcdef] at hg
      calc gk μ m t * Density.observationMean Q.measure P op ψ t
          ≤ gk μ m t * (Real.exp (c * t) * R) :=
            mul_le_mul_of_nonneg_left hg (gk_nonneg hμ0.le m t)
        _ = R * (gk μ m t * Real.exp (c * t)) := by ring
    · rw [gk_of_neg μ m (not_le.mp ht)]
      simp
  have hint1 : Integrable (fun t => gk μ m t * Density.observationMean Q.measure P op ψ t) := by
    refine Integrable.mono' ((integrable_gk hμ0 m).mul_const M)
      ((measurable_gk μ m).mul hmeas).aestronglyMeasurable (ae_of_all _ fun t => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (gk_nonneg hμ0.le m t)]
    exact mul_le_mul_of_nonneg_left
      (Density.abs_integral_reducedObservationAt_le Q.measure P op ψ hB t) (gk_nonneg hμ0.le m t)
  calc ∫ t, gk μ m t * Density.observationMean Q.measure P op ψ t
      ≤ ∫ t, R * (gk μ m t * Real.exp (c * t)) :=
        integral_mono hint1 ((integrable_gk_mul_exp hμ m).const_mul R) hle
    _ = (μ / (μ - c)) ^ (m + 1) * R := by
        rw [integral_const_mul, integral_gk_mul_exp hμ m, mul_comm]

/-- A nonnegative integrable function `ρ` with `∫ ρ ψ ≤ C ‖ψ‖₂` for its truncations
`ψ = min(ρ, n)` is in `L²`, with `∫ ρ² ≤ C²`. -/
theorem memLp_two_of_truncation_bound {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}
    [IsFiniteMeasure ν] {ρ : Ω → ℝ} (hρm : Measurable ρ) (hρ0 : ∀ w, 0 ≤ ρ w)
    (hρi : Integrable ρ ν) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ n : ℕ, ∫ w, ρ w * min (ρ w) n ∂ν ≤ C * Real.sqrt (∫ w, min (ρ w) n ^ 2 ∂ν)) :
    MemLp ρ 2 ν ∧ ∫ w, ρ w ^ 2 ∂ν ≤ C ^ 2 := by
  have hmin : ∀ n : ℕ, Measurable fun w => min (ρ w) n := fun n => hρm.min measurable_const
  have hmin0 : ∀ (n : ℕ) w, 0 ≤ min (ρ w) n := fun n w => le_min (hρ0 w) (Nat.cast_nonneg n)
  have hmin2 : ∀ n : ℕ, Integrable (fun w => min (ρ w) n ^ 2) ν := fun n =>
    Integrable.of_bound ((hmin n).pow_const 2).aestronglyMeasurable ((n : ℝ) ^ 2)
      (ae_of_all _ fun w => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact pow_le_pow_left₀ (hmin0 n w) (min_le_right _ _) 2)
  have hsq : ∀ n : ℕ, ∫ w, min (ρ w) n ^ 2 ∂ν ≤ C ^ 2 := by
    intro n
    set a := ∫ w, min (ρ w) n ^ 2 ∂ν with hadef
    have ha0 : 0 ≤ a := integral_nonneg fun w => sq_nonneg _
    have hle : a ≤ ∫ w, ρ w * min (ρ w) n ∂ν := by
      refine integral_mono_of_nonneg (ae_of_all _ fun w => sq_nonneg _) ?_ (ae_of_all _ fun w => ?_)
      · refine Integrable.mono' (hρi.mul_const n) (hρm.mul (hmin n)).aestronglyMeasurable
          (ae_of_all _ fun w => ?_)
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hρ0 w) (hmin0 n w))]
        exact mul_le_mul_of_nonneg_left (min_le_right _ _) (hρ0 w)
      · show min (ρ w) n ^ 2 ≤ ρ w * min (ρ w) n
        rw [sq]
        exact mul_le_mul_of_nonneg_right (min_le_left _ _) (hmin0 n w)
    have h2 := hle.trans (h n)
    have hsa : Real.sqrt a ≤ C := by
      rcases ha0.eq_or_lt with ha | ha
      · rw [← ha, Real.sqrt_zero]
        exact hC
      · have hpos : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
        have : Real.sqrt a * Real.sqrt a ≤ C * Real.sqrt a := by
          rw [Real.mul_self_sqrt ha0]
          exact h2
        exact le_of_mul_le_mul_right this hpos
    calc a = Real.sqrt a ^ 2 := (Real.sq_sqrt ha0).symm
      _ ≤ C ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hsa 2
  have hlim : Tendsto (fun n : ℕ => ∫⁻ w, ENNReal.ofReal (min (ρ w) n ^ 2) ∂ν) atTop
      (𝓝 (∫⁻ w, ENNReal.ofReal (ρ w ^ 2) ∂ν)) := by
    refine lintegral_tendsto_of_tendsto_of_monotone
      (fun n => ((hmin n).pow_const 2).ennreal_ofReal.aemeasurable)
      (ae_of_all _ fun w n k hnk => ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (hmin0 n w)
        (min_le_min_left _ (Nat.cast_le.mpr hnk)) 2)) (ae_of_all _ fun w => ?_)
    obtain ⟨N, hN⟩ := exists_nat_ge (ρ w)
    exact tendsto_atTop_of_eventually_const (i₀ := N) fun n hn => by
      rw [min_eq_left (hN.trans (Nat.cast_le.mpr hn))]
  have hbound : ∫⁻ w, ENNReal.ofReal (ρ w ^ 2) ∂ν ≤ ENNReal.ofReal (C ^ 2) :=
    le_of_tendsto' hlim fun n => by
      rw [← ofReal_integral_eq_lintegral_ofReal (hmin2 n) (ae_of_all _ fun w => sq_nonneg _)]
      exact ENNReal.ofReal_le_ofReal (hsq n)
  have hfin : ∫⁻ w, ENNReal.ofReal (ρ w ^ 2) ∂ν ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hbound
  have hi2 : Integrable (fun w => ρ w ^ 2) ν := by
    have hi := integrable_toReal_of_lintegral_ne_top
      (hρm.pow_const 2).ennreal_ofReal.aemeasurable hfin
    refine hi.congr (ae_of_all _ fun w => ?_)
    exact ENNReal.toReal_ofReal (sq_nonneg _)
  refine ⟨(memLp_two_iff_integrable_sq hρm.aestronglyMeasurable).mpr hi2, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun w => sq_nonneg _)
    (hρm.pow_const 2).aestronglyMeasurable]
  calc (∫⁻ w, ENNReal.ofReal (ρ w ^ 2) ∂ν).toReal ≤ (ENNReal.ofReal (C ^ 2)).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound
    _ = C ^ 2 := ENNReal.toReal_ofReal (sq_nonneg _)

/-- **The Gamma densities are in `L²`**, with `∫ ρ_m² ≤ (μ/(μ - c))^{2(m+1)}`. -/
theorem memLp_gammaDensity {Λ₀ r₀ : ℝ} (hGir : GirsanovEndpointStep)
    (hInv : UnforcedEnvironmentInvarianceStep) (hd : 2 ≤ d) (Q : EnvironmentLaw d Λ₀ r₀)
    {lam : ℝ} (h0 : 0 ≤ lam) (h1 : lam ≤ 1) (P : QuenchedPathLaws d)
    (hP : IsGMPReducedOriginLaw hd Q.ellipticity_parameter Q lam h0 h1 (originLaw P))
    (op : ∀ᵐ ω ∂Q.measure, IsProbabilityMeasure (originLaw P ω))
    (P' : DiffusionFamily d) (hP' : IsGMPReducedFamily hd Q.ellipticity_parameter Q P')
    (hP'0 : ∀ᵐ ω ∂Q.measure, IsProbabilityMeasure (originLaw (P' 0) ω))
    {μ : ℝ} (hμ : (1 / 2) * sourceReducedBound Λ₀ * lam ^ 2 < μ) (m : ℕ)
    {rho : FieldPair d → ℝ} (hrho : IsGammaDensity Q.measure P op μ m rho) :
    MemLp rho 2 (Carriers.reducedReferenceLaw Q) ∧
      ∫ w, rho w ^ 2 ∂(Carriers.reducedReferenceLaw Q) ≤
        ((μ / (μ - (1 / 2) * sourceReducedBound Λ₀ * lam ^ 2)) ^ (m + 1)) ^ 2 := by
  haveI : IsProbabilityMeasure (Carriers.reducedReferenceLaw Q) :=
    Entropy.reducedReferenceLaw_isProbabilityMeasure Q
  have hc0 : 0 ≤ (1 / 2) * sourceReducedBound Λ₀ * lam ^ 2 := by
    have := (sourceReducedBound_pos' Λ₀).le
    positivity
  have hμ0 : 0 < μ := hc0.trans_lt hμ
  have hC : 0 ≤ (μ / (μ - (1 / 2) * sourceReducedBound Λ₀ * lam ^ 2)) ^ (m + 1) :=
    pow_nonneg (div_nonneg hμ0.le (sub_pos.mpr hμ).le) _
  exact memLp_two_of_truncation_bound hrho.1 hrho.2.1
    (integrable_gammaDensity Q.measure P op hμ0 m hrho) hC fun n =>
      integral_mul_gammaDensity_le hGir hInv hd Q h0 h1 P hP op P' hP' hP'0 hμ m hrho
        (hrho.1.min measurable_const) (fun w => le_min (hrho.2.1 w) (Nat.cast_nonneg n))
        (fun w => min_le_right _ _)

end EinsteinRelation.Entropy
