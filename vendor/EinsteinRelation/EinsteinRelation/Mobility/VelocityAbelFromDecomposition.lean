import EinsteinRelation.Mobility.VelocityRateFromSteps
import EinsteinRelation.Density.LaplaceDensityIntegral
import EinsteinRelation.Clock.AbelLimit
import EinsteinRelation.Clock.LaplaceIntegrationByParts
import EinsteinRelation.Probability.MeanRate

/-! # The velocity Abel limit from the drift-martingale decomposition

Source: `paper/main.tex` 1140-1147. Write `Y = Y^λ` for the reduced diffusion from the origin and
`b = b_i^λ = ½ D·(a e_i) + λ e₁·a e_i` for its drift. The paper uses that the martingale part
`M_t = Y_t·e_i - ∫₀ᵗ b(ω_u) du` has second moment at most `C t`. This file states that input as the
step proposition `DriftDecompositionStep` and proves `VelocityAbelStep` from it.

The argument follows the source. By the Laplace identity for `ρ_s`,
`E[ρ_s b] = s ∫₀^∞ e^{-st} E[b(ω_t)] dt`. An integration by parts in time turns this into
`s² ∫₀^∞ e^{-st} E[A_t] dt` with `A_t = ∫₀ᵗ b(ω_u) du`. The law of large numbers and the
second-moment bound give `E[A_t] / t → v_i` (`tendsto_integral_div_of_sq_le`), and the Abel limit of
`Clock.AbelLimit` concludes.

The divergence `D·(a e_i)` is any weak horizontal divergence, so it is determined only almost
everywhere under the reduced reference law. The proof works with a bounded measurable version. At
each positive time the observed environment charges no null set of the reference law
(`laplaceDensity_observed_time_null`), so the version does not change any quantity along the path.
-/

open MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace EinsteinRelation

open Carriers

variable {d : ℕ}

/-- The drift `b_i^λ = ½ D·(a e_i) + λ e₁·a e_i` of the reduced diffusion on the reduced sample,
with `D·(a e_i)` the given weak horizontal divergence `divA` (`paper/main.tex` 1124). -/
noncomputable def velocityDrift (hd : 2 ≤ d) (lam : ℝ) (i : Fin d) (divA : FieldPair d → ℝ)
    (ω : FieldPair d) : ℝ :=
  (1 / 2 : ℝ) * divA ω + lam * (ω.1 0) (firstIdx hd) i

/-- The martingale part `M_t = Y_t·e_i - ∫₀ᵗ b(ω_u) du` of the coordinate path, where `ω_u` is the
reduced environment observed at time `u`. -/
noncomputable def driftMartingalePart (b : FieldPair d → ℝ) (i : Fin d) (t : ℝ)
    (z : FieldPair d × Path d) : ℝ :=
  z.2 t.toNNReal i - ∫ u in (0 : ℝ)..t, b (reducedObservationAt u.toNNReal z)

/-- Step `DriftDecompositionStep` (`paper/main.tex` 1144-1146): for the reduced GMP family at force
`0 < λ ≤ 1` and every weak horizontal divergence `D·(a e_i)`, the drift `b_i^λ` is essentially
bounded, and the martingale part `M_t = Y_t·e_i - ∫₀ᵗ b_i^λ(ω_u) du` of the coordinate path is
square integrable under the annealed law, with second moment at most `C t`. The source also uses
that `M_t` has mean zero; the argument below does not need it. -/
def DriftDecompositionStep : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ) (Q : EnvironmentLaw d Λ₀ r₀) (P' : DiffusionFamily d),
    IsGMPReducedFamily hd Q.ellipticity_parameter Q P' →
    ∀ lam : ℝ, 0 < lam → lam ≤ 1 →
      ∀ (hQ : IsStationary (reducedReferenceLaw Q)) (i : Fin d) (divA : FieldPair d → ℝ),
        HasWeakHorizontalDivergence (reducedReferenceLaw Q) hQ
          (fun ω : FieldPair d => (ω.1 0).mulVec (unitVector i)) divA →
        ∀ (origin_probability : ∀ᵐ ω ∂Q.measure, IsProbabilityMeasure (originLaw (P' lam) ω)),
          ∃ B C : ℝ, (∀ᵐ w ∂reducedReferenceLaw Q, |velocityDrift hd lam i divA w| ≤ B) ∧
            ∀ t : ℝ, 0 ≤ t →
              MemLp (driftMartingalePart (velocityDrift hd lam i divA) i t) 2
                  (annealedCoordinateJoint Q.measure (P' lam) origin_probability) ∧
                ∫ z, driftMartingalePart (velocityDrift hd lam i divA) i t z ^ 2
                    ∂(annealedCoordinateJoint Q.measure (P' lam) origin_probability) ≤ C * t

/-! ### A bounded measurable version of an essentially bounded function -/

theorem exists_bounded_measurable_version {α : Type*} [MeasurableSpace α] {ν : Measure α}
    {f : α → ℝ} (hf : AEStronglyMeasurable f ν) {B : ℝ} (hB : ∀ᵐ w ∂ν, |f w| ≤ B) :
    ∃ g : α → ℝ, Measurable g ∧ (∀ w, |g w| ≤ |B|) ∧ f =ᵐ[ν] g := by
  refine ⟨fun w => max (-|B|) (min |B| (hf.mk f w)), ?_, fun w => ?_, ?_⟩
  · exact measurable_const.max (measurable_const.min hf.stronglyMeasurable_mk.measurable)
  · rw [abs_le]
    exact ⟨le_max_left _ _, max_le (by linarith [abs_nonneg B]) (min_le_left _ _)⟩
  · filter_upwards [hf.ae_eq_mk, hB] with w hw hwB
    rw [← hw]
    have h1 : -|B| ≤ f w := by linarith [neg_abs_le (f w), hwB, le_abs_self B]
    have h2 : f w ≤ |B| := (le_abs_self _).trans (hwB.trans (le_abs_self B))
    rw [min_eq_right h2, max_eq_right h1]

/-! ### Quantities along the annealed path -/

variable {Λ₀ r₀ : ℝ}

/-- Two functions that agree almost everywhere under the reduced reference law have the same time
integrals along almost every annealed path, at every nonnegative horizon. -/
theorem ae_intervalIntegral_observation_eq (hd : 2 ≤ d) (Q : EnvironmentLaw d Λ₀ r₀) {lam : ℝ}
    (h0 : 0 ≤ lam) (h1 : lam ≤ 1) (P : QuenchedPathLaws d)
    (hprob : ∀ᵐ ω ∂Q.measure, IsProbabilityMeasure (originLaw P ω))
    (hGMP : IsGMPReducedOriginLaw hd Q.ellipticity_parameter Q lam h0 h1 (originLaw P))
    {f g : FieldPair d → ℝ} (hfg : f =ᵐ[reducedReferenceLaw Q] g) {t : ℝ} (ht : 0 ≤ t) :
    ∀ᵐ z ∂annealedCoordinateJoint Q.measure P hprob,
      ∫ u in (0 : ℝ)..t, f (reducedObservationAt u.toNNReal z) =
        ∫ u in (0 : ℝ)..t, g (reducedObservationAt u.toNNReal z) := by
  haveI := Density.isProbabilityMeasure_annealedCoordinateJoint Q.measure P hprob
  set N := toMeasurable (reducedReferenceLaw Q) {w | f w ≠ g w}
  have hN : MeasurableSet N := measurableSet_toMeasurable _ _
  have hN0 : Measure.map reduce Q.measure N = 0 := by
    change reducedReferenceLaw Q N = 0
    rw [measure_toMeasurable]
    exact hfg
  have hT : MeasurableSet {p : ℝ × (FieldPair d × Path d) |
      reducedObservationAt p.1.toNNReal p.2 ∈ N} :=
    hN.preimage (laplaceDensity_measurable_observation (d := d))
  have hslice : ∀ᵐ u ∂(volume.restrict (Set.Ioi (0 : ℝ))),
      ∀ᵐ z ∂annealedCoordinateJoint Q.measure P hprob, reducedObservationAt u.toNNReal z ∉ N := by
    rw [ae_restrict_iff' measurableSet_Ioi]
    refine ae_of_all _ fun u hu => ?_
    have hu' : (0 : ℝ≥0) < u.toNNReal := Real.toNNReal_pos.mpr hu
    exact measure_eq_zero_iff_ae_notMem.mp
      (laplaceDensity_observed_time_null hd Q h0 h1 P hprob hGMP hN hN0 hu')
  have hswap := (Measure.ae_ae_comm (μ := volume.restrict (Set.Ioi (0 : ℝ)))
    (ν := annealedCoordinateJoint Q.measure P hprob)
    (p := fun u z => reducedObservationAt u.toNNReal z ∉ N) hT.compl).mp hslice
  filter_upwards [hswap] with z hz
  refine intervalIntegral.integral_congr_ae ?_
  rw [ae_restrict_iff' measurableSet_Ioi] at hz
  filter_upwards [hz] with u hu huI
  rw [Set.uIoc_of_le ht] at huI
  have hnot := hu huI.1
  by_contra hne
  exact hnot (subset_toMeasurable _ _ hne)

/-- The time integral of a bounded measurable observation is measurable in the path. -/
theorem measurable_intervalIntegral_observation {g : FieldPair d → ℝ} (hg : Measurable g)
    (t : ℝ) :
    Measurable fun z : FieldPair d × Path d =>
      ∫ u in (0 : ℝ)..t, g (reducedObservationAt u.toNNReal z) := by
  have hF : StronglyMeasurable fun p : ℝ × (FieldPair d × Path d) =>
      g (reducedObservationAt p.1.toNNReal p.2) :=
    (hg.comp (laplaceDensity_measurable_observation (d := d))).stronglyMeasurable
  have h1 := hF.integral_prod_left' (μ := volume.restrict (Set.Ioc (0 : ℝ) t))
  have h2 := hF.integral_prod_left' (μ := volume.restrict (Set.Ioc t (0 : ℝ)))
  change Measurable fun z : FieldPair d × Path d =>
    (∫ u in Set.Ioc (0 : ℝ) t, g (reducedObservationAt u.toNNReal z)) -
      ∫ u in Set.Ioc t (0 : ℝ), g (reducedObservationAt u.toNNReal z)
  exact h1.measurable.sub h2.measurable

/-- Fubini for the time integral of a bounded measurable observation. -/
theorem integral_intervalIntegral_observation (J : Measure (FieldPair d × Path d))
    [IsProbabilityMeasure J] {g : FieldPair d → ℝ} (hg : Measurable g) {B : ℝ}
    (hB : ∀ w, |g w| ≤ B) {t : ℝ} (ht : 0 ≤ t) :
    ∫ z, (∫ u in (0 : ℝ)..t, g (reducedObservationAt u.toNNReal z)) ∂J =
      ∫ u in (0 : ℝ)..t, ∫ z, g (reducedObservationAt u.toNNReal z) ∂J := by
  have hF : Measurable fun p : (FieldPair d × Path d) × ℝ =>
      g (reducedObservationAt p.2.toNNReal p.1) :=
    hg.comp ((laplaceDensity_measurable_observation (d := d)).comp measurable_swap)
  haveI : IsFiniteMeasure (volume.restrict (Set.Ioc (0 : ℝ) t)) := by
    rw [isFiniteMeasure_restrict]; exact measure_Ioc_lt_top.ne
  have hint : Integrable (Function.uncurry fun (z : FieldPair d × Path d) (u : ℝ) =>
      g (reducedObservationAt u.toNNReal z)) (J.prod (volume.restrict (Set.Ioc (0 : ℝ) t))) :=
    (integrable_const B).mono' hF.aestronglyMeasurable
      (ae_of_all _ fun p => by rw [Real.norm_eq_abs]; exact hB _)
  simp only [intervalIntegral.integral_of_le ht]
  exact integral_integral_swap hint

/-- Along almost every path the coordinate `Y_t·e_i / t` converges to `v_i`, so it converges in
probability under the annealed law. -/
theorem tendsto_measureReal_coordinate_velocity (Q : EnvironmentLaw d Λ₀ r₀)
    (P : QuenchedPathLaws d) (hprob : ∀ᵐ ω ∂Q.measure, IsProbabilityMeasure (originLaw P ω))
    {v : Vec d} (hv : HasQuenchedVelocity Q.measure (originLaw P) v) (i : Fin d) {δ : ℝ}
    (hδ : 0 < δ) :
    Tendsto (fun t : ℝ => (annealedCoordinateJoint Q.measure P hprob).real
      {z | δ ≤ |z.2 t.toNNReal i / t - v i|}) atTop (𝓝 0) := by
  haveI := Density.isProbabilityMeasure_annealedCoordinateJoint Q.measure P hprob
  set S : ℝ → Set (FieldPair d × Path d) := fun t => {z | δ ≤ |z.2 t.toNNReal i / t - v i|}
  have hS : ∀ t, MeasurableSet (S t) := fun t => by
    have hc : Continuous fun z : FieldPair d × Path d => z.2 t.toNNReal i :=
      (continuous_apply i).comp ((continuous_eval_const t.toNNReal).comp continuous_snd)
    exact measurableSet_le measurable_const
      (continuous_abs.measurable.comp ((hc.measurable.div_const t).sub_const (v i)))
  -- The annealed mass is an iterated lower integral of the indicator, against the probability
  -- part of the kernel, which agrees with the kernel almost everywhere.
  set K := Probability.probabilityPart (originLaw P)
  have hKae := Probability.probabilityPart_ae_eq Q.measure (originLaw P) hprob
  have hmass : ∀ t, annealedCoordinateJoint Q.measure P hprob (S t) =
      ∫⁻ ω, ∫⁻ γ, (S t).indicator 1 (ω, γ) ∂K ω ∂Q.measure := fun t => by
    rw [← lintegral_indicator_one (hS t)]
    unfold annealedCoordinateJoint
    rw [Probability.ValidAnnealedLawSupport.annealedJointOnProbabilityFibers_lintegral
      Q.measure (originLaw P) hprob _ (measurable_one.indicator (hS t))]
    refine lintegral_congr_ae ?_
    filter_upwards [hKae] with ω hω
    rw [hω]
  have hlim : Tendsto (fun t => annealedCoordinateJoint Q.measure P hprob (S t)) atTop (𝓝 0) := by
    simp_rw [hmass]
    rw [show (0 : ℝ≥0∞) = ∫⁻ _, 0 ∂Q.measure by simp]
    refine tendsto_lintegral_filter_of_dominated_convergence (fun _ => 1)
      (Eventually.of_forall fun t => Measurable.lintegral_kernel_prod_right' (κ := K)
        (measurable_one.indicator (hS t)))
      (Eventually.of_forall fun t => ?_) (by simp) ?_
    · filter_upwards [hprob, hKae] with ω hω hKω
      haveI := hω
      rw [hKω]
      calc ∫⁻ γ, (S t).indicator 1 (ω, γ) ∂originLaw P ω ≤ ∫⁻ _, 1 ∂originLaw P ω :=
            lintegral_mono fun γ => Set.indicator_le_self' (fun _ _ => zero_le_one) _
        _ = 1 := by rw [lintegral_one, measure_univ]
    · filter_upwards [hprob, hv, hKae] with ω hω hvω hKω
      haveI := hω
      rw [hKω]
      rw [show (0 : ℝ≥0∞) = ∫⁻ _, 0 ∂originLaw P ω by simp]
      refine tendsto_lintegral_filter_of_dominated_convergence (fun _ => 1)
        (Eventually.of_forall fun t => (measurable_one.indicator (hS t)).comp measurable_prodMk_left)
        (Eventually.of_forall fun t => ae_of_all _ fun γ =>
          Set.indicator_le_self' (fun _ _ => zero_le_one) _)
        (by rw [lintegral_one, measure_univ]; exact ENNReal.one_ne_top) ?_
      filter_upwards [hvω] with γ hγ
      have hcoord : Tendsto (fun t : ℝ => ((t.toNNReal : ℝ))⁻¹ * γ t.toNNReal i) atTop
          (𝓝 (v i)) := by
        have h := ((continuous_apply i).tendsto v).comp (hγ.comp tendsto_real_toNNReal_atTop)
        simpa [Function.comp_def] using h
      have hev : ∀ᶠ t : ℝ in atTop, |γ t.toNNReal i / t - v i| < δ := by
        have h := (Metric.tendsto_nhds.mp hcoord) δ hδ
        filter_upwards [h, eventually_ge_atTop (0 : ℝ)] with t ht ht0
        rw [Real.dist_eq, Real.coe_toNNReal _ ht0, inv_mul_eq_div] at ht
        exact ht
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hev] with t ht
      have hnot : (ω, γ) ∉ S t := fun h => absurd ht (not_lt.mpr h)
      simp [Set.indicator_of_notMem hnot]
  have hreal := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hlim
  simpa [Measure.real, Function.comp_def] using hreal

/-! ### The velocity Abel limit -/

/-- **`VelocityAbelStep` from `DriftDecompositionStep`** (`paper/main.tex` 1140-1147). The
Laplace identity for `ρ_s`, an integration by parts in time, the mean rate of the drift integral and
the Abel limit give `E[ρ_s b_i^λ] → v_i` as `s ↓ 0`. -/
theorem velocityAbelStep_of_driftDecomposition (hDD : DriftDecompositionStep) :
    VelocityAbelStep := by
  intro d hd Λ₀ r₀ Q P' hP' lam hlam hlam1 v hv hQ i divA hdiv origin_probability rhoOf hrho
  obtain ⟨B, C, hB, hM⟩ :=
    hDD d hd Λ₀ r₀ Q P' hP' lam hlam hlam1 hQ i divA hdiv origin_probability
  set J := annealedCoordinateJoint Q.measure (P' lam) origin_probability with hJ
  haveI : IsProbabilityMeasure J :=
    Density.isProbabilityMeasure_annealedCoordinateJoint Q.measure (P' lam) origin_probability
  have hGMP : IsGMPReducedOriginLaw hd Q.ellipticity_parameter Q lam hlam.le hlam1
      (originLaw (P' lam)) := hP' lam hlam.le hlam1
  -- A bounded measurable version `bt` of the drift.
  have hentry : Continuous fun ω : FieldPair d => (ω.1 0) (firstIdx hd) i :=
    (continuous_apply i).comp ((continuous_apply (firstIdx hd)).comp
      ((continuous_eval_const (0 : Vec d)).comp continuous_fst))
  have hbm : AEStronglyMeasurable (velocityDrift hd lam i divA) (reducedReferenceLaw Q) :=
    (hdiv.2.1.aestronglyMeasurable.const_mul _).add (hentry.aestronglyMeasurable.const_mul lam)
  obtain ⟨bt, hbt, hbtB, hbbt⟩ := exists_bounded_measurable_version hbm hB
  set B' := |B| with hB'
  -- The expected drift along the path and its primitive.
  set g : ℝ → ℝ := fun t => ∫ z, bt (reducedObservationAt t.toNNReal z) ∂J with hgdef
  have hg : Measurable g :=
    Density.measurable_integral_reducedObservationAt Q.measure (P' lam) origin_probability bt hbt
  have hgB : ∀ t, |g t| ≤ B' :=
    Density.abs_integral_reducedObservationAt_le Q.measure (P' lam) origin_probability bt hbtB
  have hgint : ∀ a b : ℝ, IntervalIntegrable g volume a b := fun a b =>
    (intervalIntegrable_const (c := B')).mono_fun' hg.aestronglyMeasurable
      (ae_of_all _ fun u => by simpa [Real.norm_eq_abs] using hgB u)
  set G : ℝ → ℝ := fun t => ∫ u in (0 : ℝ)..t, g u with hGdef
  have hGcont : Continuous G := intervalIntegral.continuous_primitive hgint 0
  have hGB : ∀ t, 0 ≤ t → |G t| ≤ B' * t := fun t ht => by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := t) (f := g)
      (C := B') (fun u _ => by rw [Real.norm_eq_abs]; exact hgB u)
    rwa [Real.norm_eq_abs, sub_zero, abs_of_nonneg ht] at h
  -- The mean rate `G t / t → v i`.
  set A : ℝ → FieldPair d × Path d → ℝ :=
    fun t z => ∫ u in (0 : ℝ)..t, bt (reducedObservationAt u.toNNReal z) with hAdef
  have hAm : ∀ t, Measurable (A t) := fun t => measurable_intervalIntegral_observation hbt t
  have hAB : ∀ t, 0 ≤ t → ∀ᵐ z ∂J, |A t z| ≤ B' * t := fun t ht => ae_of_all _ fun z => by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := t)
      (f := fun u => bt (reducedObservationAt u.toNNReal z)) (C := B')
      (fun u _ => by rw [Real.norm_eq_abs]; exact hbtB _)
    rwa [Real.norm_eq_abs, sub_zero, abs_of_nonneg ht] at h
  have hMeq : ∀ t, 0 ≤ t → driftMartingalePart (velocityDrift hd lam i divA) i t =ᵐ[J]
      fun z => z.2 t.toNNReal i - A t z := fun t ht => by
    filter_upwards [ae_intervalIntegral_observation_eq hd Q hlam.le hlam1 (P' lam)
      origin_probability hGMP hbbt ht] with z hz
    simp only [driftMartingalePart, hAdef]
    rw [hz]
  have hMint : ∀ t, 0 ≤ t → Integrable (fun z => (z.2 t.toNNReal i - A t z) ^ 2) J :=
    fun t ht => ((hM t ht).1.integrable_sq).congr ((hMeq t ht).mono fun z hz => by
      simp only; rw [hz])
  have hM2 : ∀ t, 0 ≤ t → ∫ z, (z.2 t.toNNReal i - A t z) ^ 2 ∂J ≤ C * t := fun t ht => by
    have heq : ∫ z, (z.2 t.toNNReal i - A t z) ^ 2 ∂J =
        ∫ z, driftMartingalePart (velocityDrift hd lam i divA) i t z ^ 2 ∂J :=
      integral_congr_ae ((hMeq t ht).mono fun z hz => by simp only; rw [hz])
    rw [heq]
    exact (hM t ht).2
  have hmean := tendsto_integral_div_of_sq_le (μ := J) (fun t z => z.2 t.toNNReal i) A hAm hAB
    hMint hM2 (fun δ hδ =>
      tendsto_measureReal_coordinate_velocity Q (P' lam) origin_probability hv i hδ)
  have hGlim : Tendsto (fun t => G t / t) atTop (𝓝 (v i)) := by
    refine hmean.congr' ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    rw [integral_intervalIntegral_observation J hbt hbtB ht]
  -- The Abel limit.
  have habel := Clock.abel_tendsto_of_bounded_rate G hGcont.measurable B' (v i) hGB hGlim
  refine habel.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s (hs : 0 < s)
  have h1 : ∫ ω, rhoOf s ω * ((1 / 2 : ℝ) * divA ω + lam * (ω.1 0) (firstIdx hd) i)
      ∂reducedReferenceLaw Q = ∫ ω, rhoOf s ω * bt ω ∂reducedReferenceLaw Q :=
    integral_congr_ae (hbbt.mono fun w hw => by
      simp only [velocityDrift] at hw
      simp only [hw])
  have h2 := Density.integral_mul_density_eq_setIntegral_Ici Q.measure (P' lam) origin_probability
    ⟨s, hs⟩ (rhoOf s) (hrho ⟨s, hs⟩) bt hbt hbtB
  have h3 := Clock.laplace_eq_laplace_primitive g hg B' hgB hs
  rw [h1]
  change s ^ 2 * ∫ t in Set.Ioi (0 : ℝ), Real.exp (-(s * t)) * G t =
    ∫ ω, rhoOf s ω * bt ω ∂(Measure.map reduce Q.measure)
  rw [h2, integral_Ici_eq_integral_Ioi, ← h3, ← integral_const_mul]
  exact integral_congr_ae (ae_of_all _ fun t => by ring)

end EinsteinRelation
