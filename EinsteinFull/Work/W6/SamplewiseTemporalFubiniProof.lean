import EinsteinFull.Work.W6.PhysicalSemigroupWeakTimeRealizationProof
import EinsteinFull.Calculus.ComplexZeroForceFluxSupport
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# Joint representatives of stationary L2 paths

Measurable countable approximations are chosen with a geometric error in L2.
The pointwise limit is formed using real and imaginary limsups. This avoids
assuming that the chosen coercion from L2 is jointly measurable.
-/

open MeasureTheory Filter Set
open scoped Topology NNReal ENNReal

noncomputable section
namespace EinsteinFull
open EinsteinRelation

private theorem measurable_simpleFunc_evaluation {T Ω : Type*}
    [MeasurableSpace T] [MeasurableSpace Ω] (μ : Measure Ω)
    (v : SimpleFunc T (Lp ℂ 2 μ)) :
    Measurable (fun p : T × Ω => v p.1 p.2) := by
  letI : MeasurableSpace (Lp ℂ 2 μ) := borel _
  letI : BorelSpace (Lp ℂ 2 μ) := ⟨rfl⟩
  letI : Countable (Set.range v) := v.finite_range.countable.to_subtype
  have he : Measurable (fun p : Set.range v × Ω => p.1.val p.2) :=
    measurable_from_prod_countable_right fun a => (Lp.stronglyMeasurable a.val).measurable
  exact he.comp (((v.measurable.comp measurable_fst).subtype_mk (h := fun p => ⟨p.1, rfl⟩)).prodMk measurable_snd)

/-- A strongly measurable L2 path has jointly measurable countable-range
approximations with a prescribed geometric error at every parameter. -/
theorem StronglyMeasurable.exists_joint_l2_approx {T Ω : Type*}
    [MeasurableSpace T] [MeasurableSpace Ω] {μ : Measure Ω}
    {u : T → Lp ℂ 2 μ} (hu : StronglyMeasurable u) :
    ∃ v : ℕ → T → Lp ℂ 2 μ,
      (∀ n, Measurable (fun p : T × Ω => v n p.1 p.2)) ∧
      ∀ n t, ‖v n t - u t‖ < (1 / 2 : ℝ) ^ n := by
  classical
  letI : MeasurableSpace (Lp ℂ 2 μ) := borel _
  letI : BorelSpace (Lp ℂ 2 μ) := ⟨rfl⟩
  have hex (n : ℕ) (t : T) : ∃ k, ‖hu.approx k t - u t‖ < (1 / 2 : ℝ) ^ n := by
    have ht : Tendsto (fun k => ‖hu.approx k t - u t‖) atTop (𝓝 0) := by
      simpa only [sub_self, norm_zero] using! ((hu.tendsto_approx t).sub_const (u t)).norm
    have he := ht.eventually (gt_mem_nhds (pow_pos (by norm_num : (0 : ℝ) < 1 / 2) n))
    simpa only [sub_self, norm_zero] using! he.exists
  let k : ℕ → T → ℕ := fun n t => Nat.find (hex n t)
  have hk (n : ℕ) : Measurable (k n) :=
    measurable_find (hex n) (fun j => measurableSet_lt
      (((hu.approx j).stronglyMeasurable.sub hu).norm.measurable) measurable_const)
  refine ⟨fun n t => hu.approx (k n t) t, ?_, fun n t => Nat.find_spec (hex n t)⟩
  intro n
  have he : Measurable (fun p : ℕ × (T × Ω) => hu.approx p.1 p.2.1 p.2.2) :=
    measurable_from_prod_countable_right fun j => measurable_simpleFunc_evaluation μ (hu.approx j)
  exact he.comp (((hk n).comp measurable_fst).prodMk measurable_id)

/-- A jointly measurable representative of a strongly measurable complex L2
path. Equality is asserted separately at each parameter; the representative
itself is a single measurable function on the product. -/
theorem StronglyMeasurable.exists_joint_l2_representative {T Ω : Type*}
    [MeasurableSpace T] [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {u : T → Lp ℂ 2 μ} (hu : StronglyMeasurable u) :
    ∃ U : T × Ω → ℂ, Measurable U ∧ ∀ t, (fun ω => U (t, ω)) =ᵐ[μ] u t := by
  obtain ⟨v, hv, herr⟩ := StronglyMeasurable.exists_joint_l2_approx hu
  let U : T × Ω → ℂ := fun p =>
    (limsup (fun n => (v n p.1 p.2).re) atTop : ℝ) +
      (limsup (fun n => (v n p.1 p.2).im) atTop : ℝ) * Complex.I
  have hUm : Measurable U :=
    (Complex.measurable_ofReal.comp (.limsup fun n => Complex.measurable_re.comp (hv n))).add
      ((Complex.measurable_ofReal.comp (.limsup fun n => Complex.measurable_im.comp (hv n))).mul
        measurable_const)
  refine ⟨U, hUm, fun t => ?_⟩
  have hB : (∑' n : ℕ, ENNReal.ofReal (4 * (1 / 2 : ℝ) ^ n)) ≠ ⊤ := by
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity)
      (summable_geometric_two.mul_left 4)]
    exact ENNReal.ofReal_ne_top
  have hca : ∀ N n m : ℕ, N ≤ n → N ≤ m →
      eLpNorm ((fun ω => v n t ω) - (fun ω => v m t ω)) 2 μ <
        ENNReal.ofReal (4 * (1 / 2 : ℝ) ^ N) := by
    intro N n m hn hm
    rw [eLpNorm_congr_ae (Lp.coeFn_sub _ _).symm, ← Lp.enorm_def, ← ofReal_norm_eq_enorm]
    apply (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr
    have hnm : ‖v n t - v m t‖ ≤ ‖v n t - u t‖ + ‖v m t - u t‖ :=
      by simpa only [norm_sub_rev (u t) (v m t)] using!
        norm_sub_le_norm_sub_add_norm_sub (v n t) (u t) (v m t)
    have hnN : (1 / 2 : ℝ) ^ n ≤ (1 / 2 : ℝ) ^ N :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hn
    have hmN : (1 / 2 : ℝ) ^ m ≤ (1 / 2 : ℝ) ^ N :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hm
    have hpos : 0 < (1 / 2 : ℝ) ^ N := by positivity
    linarith [herr n t, herr m t]
  have hlim := Lp.ae_tendsto_of_cauchy_eLpNorm
    (fun n => Lp.aestronglyMeasurable (v n t)) (by norm_num : (1 : ℝ≥0∞) ≤ 2) hB hca
  have hpoint : ∀ᵐ ω ∂μ, Tendsto (fun n => v n t ω) atTop (𝓝 (U (t, ω))) := by
    filter_upwards [hlim] with ω hω
    obtain ⟨z, hz⟩ := hω
    have hre := (Complex.continuous_re.tendsto z |>.comp hz).limsup_eq
    have him := (Complex.continuous_im.tendsto z |>.comp hz).limsup_eq
    simp only [Function.comp_def] at hre him
    have he : U (t, ω) = z := by
      dsimp only [U]
      rw [hre, him, Complex.re_add_im]
    rw [he]
    exact hz
  have hvlim : Tendsto (fun n => v n t) atTop (𝓝 (u t)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun n => norm_nonneg _) (fun n => (herr n t).le)
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num))
  exact tendstoInMeasure_ae_unique
    (tendstoInMeasure_of_tendsto_ae (fun n => Lp.aestronglyMeasurable (v n t)) hpoint)
    (tendstoInMeasure_of_tendsto_Lp hvlim)

private theorem integral_norm_le_l2 {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (f : Lp ℂ 2 μ) :
    (∫ ω, ‖f ω‖ ∂μ) ≤ ‖f‖ := by
  rw [integral_norm_eq_lintegral_enorm (Lp.aestronglyMeasurable f),
    ← eLpNorm_one_eq_lintegral_enorm (Lp.aestronglyMeasurable f), Lp.norm_def]
  exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top f)
    (eLpNorm_le_eLpNorm_of_exponent_le (by norm_num : (1 : ℝ≥0∞) ≤ 2))

/-- Integrability of the L2 path supplies integrability of its measurable
representative on the time/environment product. -/
theorem integrable_joint_l2_representative {T Ω : Type*}
    [MeasurableSpace T] [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : Measure T} {u : T → Lp ℂ 2 μ} (hu : Integrable u ν)
    {U : T × Ω → ℂ} (hU : Measurable U)
    (heq : ∀ t, (fun ω => U (t, ω)) =ᵐ[μ] u t) :
    Integrable U (ν.prod μ) := by
  apply (integrable_prod_iff hU.aestronglyMeasurable).mpr
  refine ⟨ae_of_all _ (fun t => ((Lp.memLp (u t)).integrable (by norm_num)).congr
    (heq t).symm), ?_⟩
  apply hu.norm.mono' (hU.stronglyMeasurable.norm.integral_prod_right.aestronglyMeasurable)
  filter_upwards with t
  rw [Real.norm_of_nonneg (integral_nonneg (fun ω => norm_nonneg _)),
    integral_congr_ae ((heq t).mono (fun ω h => congrArg norm h))]
  exact integral_norm_le_l2 (u t)

/-- Literal equality between the L2 Bochner integral and the samplewise time
integral. Measurability and integrability, rather than an uncountable AE
intersection, justify this identification. -/
theorem coeFn_integral_joint_l2_representative {T Ω : Type*}
    [MeasurableSpace T] [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : Measure T} [SFinite ν] {u : T → Lp ℂ 2 μ} (hu : Integrable u ν)
    {U : T × Ω → ℂ} (hU : Measurable U)
    (heq : ∀ t, (fun ω => U (t, ω)) =ᵐ[μ] u t) :
    (fun ω => (∫ t, u t ∂ν) ω) =ᵐ[μ] fun ω => ∫ t, U (t, ω) ∂ν := by
  have hi := integrable_joint_l2_representative hu hU heq
  apply Integrable.ae_eq_of_forall_setIntegral_eq _ _
    ((Lp.memLp _).integrable (by norm_num)) hi.integral_prod_right
  intro A hA hμA
  have ht := integral_inner (𝕜 := ℂ) hu (indicatorConstLp 2 hA hμA.ne (1 : ℂ))
  rw [L2.inner_indicatorConstLp_one hA hμA.ne] at ht
  simp_rw [L2.inner_indicatorConstLp_one hA hμA.ne] at ht
  rw [← ht]
  have hir : Integrable U (ν.prod (μ.restrict A)) :=
    by
      have h := hi.integrableOn (s := Set.univ ×ˢ A)
      rwa [IntegrableOn, ← Measure.prod_restrict, Measure.restrict_univ] at h
  rw [← integral_integral_swap (f := fun t ω => U (t, ω)) hir]
  apply integral_congr_ae
  filter_upwards with t
  exact integral_congr_ae (ae_restrict_of_ae (heq t).symm)

/-- A measurable complex environment identity transfers to spatial orbits on
one environment event. The spatial quantifier is AE, as stationarity permits. -/
theorem ae_spatial_complex_orbit_congr {d : ℕ} (Q : Measure (FieldPair d))
    [IsProbabilityMeasure Q] (hQ : IsStationary Q)
    {a b : FieldPair d → ℂ} (ha : Measurable a) (hb : Measurable b)
    (hab : a =ᵐ[Q] b) :
    ∀ᵐ ω ∂Q, ∀ᵐ x ∂(volume : Measure (Vec d)),
      a (translate x ω) = b (translate x ω) := by
  apply (Measure.ae_ae_comm ?_).mp
    (ae_of_all _ fun x => (measurePreserving_translate Q hQ x).quasiMeasurePreserving.ae hab)
  exact measurableSet_eq_fun (ha.comp Probability.continuous_translate.measurable)
    (hb.comp Probability.continuous_translate.measurable)

/-- Joint measurability survives the literal stationary spatial translation. -/
theorem measurable_joint_spatial_translate {T : Type*} [MeasurableSpace T] {d : ℕ}
    {U : T × FieldPair d → ℂ} (hU : Measurable U) :
    Measurable (fun p : T × (Vec d × FieldPair d) => U (p.1, translate p.2.1 p.2.2)) :=
  hU.comp (measurable_fst.prodMk
    (Probability.continuous_translate.measurable.comp measurable_snd))

/-- Stationarity transports joint time/environment integrability to every finite
spatial region. The product is ordered so its AE sections are samplewise. -/
theorem integrable_joint_spatial_translate {T : Type*} [MeasurableSpace T]
    {ν : Measure T} [SFinite ν] {d : ℕ} (Q : Measure (FieldPair d))
    [IsProbabilityMeasure Q] (hQ : IsStationary Q)
    (m : Measure (Vec d)) [IsFiniteMeasure m]
    {U : T × FieldPair d → ℂ} (hi : Integrable U (ν.prod Q)) :
    Integrable (fun p : (Vec d × T) × FieldPair d =>
      U (p.1.2, translate p.1.1 p.2)) ((m.prod ν).prod Q) := by
  have ha := measurePreserving_prodAssoc m ν Q
  have hb : Integrable (fun p : (Vec d × T) × FieldPair d => U (p.1.2, p.2))
      ((m.prod ν).prod Q) :=
    (ha.integrable_comp (hi.comp_snd m).aestronglyMeasurable).mpr (hi.comp_snd m)
  have hm := (MeasurePreserving.id (m.prod ν)).skew_product
    (g := fun p ω => translate p.1 ω)
    (Probability.continuous_translate.measurable.comp
      ((measurable_fst.fst).prodMk measurable_snd))
    (ae_of_all _ fun p => (measurePreserving_translate Q hQ p.1).map_eq)
  exact (hm.integrable_comp hb.aestronglyMeasurable).mpr hb

/-- A countable spatial exhaustion yields local space-time integrability on
one environment event, simultaneously for every compact spatial set. -/
theorem ae_locally_integrable_joint_spatial_translate {T : Type*} [MeasurableSpace T]
    {ν : Measure T} [SFinite ν] {d : ℕ} (Q : Measure (FieldPair d))
    [IsProbabilityMeasure Q] (hQ : IsStationary Q)
    {U : T × FieldPair d → ℂ} (hi : Integrable U (ν.prod Q)) :
    ∀ᵐ ω ∂Q, ∀ K : Set (Vec d), IsCompact K →
      Integrable (fun p : Vec d × T => U (p.2, translate p.1 ω))
        ((volume.restrict K).prod ν) := by
  have hb (n : ℕ) : ∀ᵐ ω ∂Q,
      Integrable (fun p : Vec d × T => U (p.2, translate p.1 ω))
        ((volume.restrict (Metric.closedBall 0 (n : ℝ))).prod ν) := by
    letI : IsFiniteMeasure (volume.restrict (Metric.closedBall (0 : Vec d) (n : ℝ))) :=
      isFiniteMeasure_restrict.mpr (isCompact_closedBall (0 : Vec d) (n : ℝ)).measure_ne_top
    exact (integrable_joint_spatial_translate Q hQ _ hi).prod_left_ae
  filter_upwards [ae_all_iff.mpr hb] with ω hω
  intro K hK
  obtain ⟨r, hr⟩ := hK.isBounded.subset_closedBall (0 : Vec d)
  obtain ⟨n, hn⟩ := exists_nat_gt r
  have hsub : K ⊆ Metric.closedBall 0 (n : ℝ) :=
    hr.trans (Metric.closedBall_subset_closedBall hn.le)
  have h := hω n
  rw [← Measure.restrict_univ (μ := ν), Measure.prod_restrict] at h ⊢
  exact h.mono_measure (Measure.restrict_mono_set _ (Set.prod_mono hsub Subset.rfl))

/-- Local space-time integrability supplies every bounded separated temporal
and spatial test at once. Both orders of integration have the same value. -/
theorem integral_spatial_temporal_tests {X T : Type*}
    [MeasurableSpace X] [MeasurableSpace T] {m : Measure X} {ν : Measure T}
    [SFinite m] [SFinite ν] {F : X × T → ℂ} (hi : Integrable F (m.prod ν))
    {φ : X → ℂ} {η : T → ℂ} (hφ : Measurable φ) (hη : Measurable η)
    {C D : ℝ} (hC : ∀ x, ‖φ x‖ ≤ C) (hD : ∀ t, ‖η t‖ ≤ D) :
    (∫ x, φ x * (∫ t, η t * F (x, t) ∂ν) ∂m) =
      ∫ t, η t * (∫ x, φ x * F (x, t) ∂m) ∂ν := by
  have h := (hi.bdd_mul (hη.comp measurable_snd).aestronglyMeasurable
    (ae_of_all _ fun p => hD p.2)).bdd_mul
    (hφ.comp measurable_fst).aestronglyMeasurable (ae_of_all _ fun p => hC p.1)
  have hf := integral_integral_swap (f := fun x t => φ x * (η t * F (x, t))) h
  calc
    _ = ∫ x, ∫ t, φ x * (η t * F (x, t)) ∂ν ∂m := by
      simp only [integral_const_mul]
    _ = ∫ t, ∫ x, φ x * (η t * F (x, t)) ∂m ∂ν := hf
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with t
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact ae_of_all _ fun x => mul_left_comm _ _ _

/-- The Bochner integral is identified after spatial translation on a single
environment event, without exchanging an uncountable family of AE statements. -/
theorem ae_spatial_coeFn_integral_joint_l2_representative
    {T : Type*} [MeasurableSpace T] {ν : Measure T} [SFinite ν]
    {d : ℕ} (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q] (hQ : IsStationary Q)
    {u : T → Lp ℂ 2 Q} (hu : Integrable u ν)
    {U : T × FieldPair d → ℂ} (hU : Measurable U)
    (heq : ∀ t, (fun ω => U (t, ω)) =ᵐ[Q] u t) :
    ∀ᵐ ω ∂Q, ∀ᵐ x ∂(volume : Measure (Vec d)),
      (∫ t, u t ∂ν) (translate x ω) = ∫ t, U (t, translate x ω) ∂ν := by
  exact ae_spatial_complex_orbit_congr Q hQ
    (Lp.stronglyMeasurable _).measurable
    hU.stronglyMeasurable.integral_prod_left'.measurable
    (coeFn_integral_joint_l2_representative hu hU heq)

/-- The actual semigroup has a single joint measurable time/environment
representative, and hence a joint measurable time/space/environment realization. -/
theorem IsComplexEnvironmentSemigroup.exists_joint_spatial_representative
    {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P) (f : Lp ℂ 2 (reducedLaw Q)) :
    ∃ U : ℝ × FieldPair d → ℂ, Measurable U ∧
      (∀ s, (fun ω => U (s, ω)) =ᵐ[reducedLaw Q] P s.toNNReal f) ∧
      Measurable (fun p : ℝ × (Vec d × FieldPair d) => U (p.1, translate p.2.1 p.2.2)) := by
  letI : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  obtain ⟨U, hU, heq⟩ := StronglyMeasurable.exists_joint_l2_representative
    (((hP.2.2.1 f).comp continuous_real_toNNReal).stronglyMeasurable)
  exact ⟨U, hU, heq, measurable_joint_spatial_translate hU⟩

/-- The actual positive-time gradient, extended by zero, is strongly measurable
on the entire time line; no regularity at time zero is asserted. -/
theorem IsComplexEnvironmentSemigroup.stronglyMeasurable_gradientOrbit
    {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P) (f : Lp ℂ 2 (reducedLaw Q)) :
    StronglyMeasurable (hP.gradientOrbit f) := by
  apply stronglyMeasurable_of_restrict_of_restrict_compl measurableSet_Ioi
  · exact (continuousOn_iff_continuous_restrict.mp (hP.continuousOn_gradientOrbit f)).stronglyMeasurable
  · have he : (Ioi (0 : ℝ))ᶜ.domRestrict (hP.gradientOrbit f) = fun _ => 0 := by
      funext s
      exact dif_neg s.property
    rw [he]
    exact stronglyMeasurable_const

/-- All actual coordinate gradients have jointly measurable representatives,
chosen together from the finite family. -/
theorem IsComplexEnvironmentSemigroup.exists_joint_gradient_representative
    {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P) (f : Lp ℂ 2 (reducedLaw Q)) :
    ∃ V : Fin d → ℝ × FieldPair d → ℂ, (∀ j, Measurable (V j)) ∧
      ∀ j s, (fun ω => V j (s, ω)) =ᵐ[reducedLaw Q] (hP.gradientOrbit f s) j := by
  letI : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  have he (j : Fin d) := StronglyMeasurable.exists_joint_l2_representative
    ((PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q)) j).continuous.comp_stronglyMeasurable
      (hP.stronglyMeasurable_gradientOrbit f))
  choose V hV heq using he
  exact ⟨V, hV, heq⟩

/-- For prescribed countable time windows, one
joint representative realizes the actual primitive and its integrated gradient
on one environment event. Every compact spatial test is included in the weak
gradient predicates. No pointwise time trace is asserted. -/
theorem IsComplexEnvironmentSemigroup.exists_ae_samplewise_timeIntegrals
    {d : ℕ} [Fact (2 ≤ d)] {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀}
    {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P) (f : Lp ℂ 2 (reducedLaw Q))
    (t : ℕ → ℝ≥0) :
    ∃ (U : ℝ × FieldPair d → ℂ) (V : Fin d → ℝ × FieldPair d → ℂ),
      Measurable U ∧ (∀ j, Measurable (V j)) ∧
      (∀ s, (fun ω => U (s, ω)) =ᵐ[reducedLaw Q] P s.toNNReal f) ∧
      (∀ j s, (fun ω => V j (s, ω)) =ᵐ[reducedLaw Q] (hP.gradientOrbit f s) j) ∧
      ∀ᵐ ω ∂reducedLaw Q, ∀ n,
        let A := fun x => ∫ s in Icc (0 : ℝ) (t n : ℝ), U (s, translate x ω)
        let B := fun x j => ∫ s in Icc (0 : ℝ) (t n : ℝ), V j (s, translate x ω)
        ((fun x => (∫ s in Icc (0 : ℝ) (t n : ℝ), P s.toNNReal f) (translate x ω))
          =ᵐ[volume] A) ∧
        (∀ j, (fun x => ((∫ s in Icc (0 : ℝ) (t n : ℝ), hP.gradientOrbit f s) j)
          (translate x ω)) =ᵐ[volume] fun x => B x j) ∧
        HasWeakGradient univ (fun x => (A x).re) (fun x j => (B x j).re) ∧
        HasWeakGradient univ (fun x => (A x).im) (fun x j => (B x j).im) ∧
        (∀ L : Set (Vec d), IsCompact L →
          MemLp A 2 (volume.restrict L) ∧ ∀ j, MemLp (fun x => B x j) 2 (volume.restrict L)) ∧
        ∀ K : Set (Vec d), IsCompact K →
          Integrable (fun p : Vec d × ℝ => U (p.2, translate p.1 ω))
            ((volume.restrict K).prod (volume.restrict (Icc (0 : ℝ) (t n : ℝ)))) ∧
          ∀ j, Integrable (fun p : Vec d × ℝ => V j (p.2, translate p.1 ω))
            ((volume.restrict K).prod (volume.restrict (Icc (0 : ℝ) (t n : ℝ)))) := by
  letI : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  obtain ⟨U, hU, heU, _⟩ := hP.exists_joint_spatial_representative f
  obtain ⟨V, hV, heV⟩ := hP.exists_joint_gradient_representative f
  have hiU (n : ℕ) := integrableOn_comp_toNNReal_Icc _ (hP.2.2.1 f) (t n : ℝ)
  let T (j : Fin d) : PiLp 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q)) →L[ℂ]
      Lp ℂ 2 (reducedLaw Q) := PiLp.proj 2 _ j
  have hiV (n : ℕ) (j : Fin d) := (T j).integrable_comp (hP.integrableOn_gradientOrbit f (t n))
  have hcU (n : ℕ) := ae_spatial_coeFn_integral_joint_l2_representative
    (reducedLaw Q) (reducedLaw_stationary Q) (hiU n) hU heU
  have hcV (n : ℕ) (j : Fin d) : ∀ᵐ ω ∂reducedLaw Q, ∀ᵐ x ∂(volume : Measure (Vec d)),
      ((∫ s in Icc (0 : ℝ) (t n : ℝ), hP.gradientOrbit f s) j) (translate x ω) =
        ∫ s in Icc (0 : ℝ) (t n : ℝ), V j (s, translate x ω) := by
    have h := ae_spatial_coeFn_integral_joint_l2_representative
      (reducedLaw Q) (reducedLaw_stationary Q) (hiV n j) (hV j) (heV j)
    have hp := (T j).integral_comp_comm (hP.integrableOn_gradientOrbit f (t n))
    change (∫ s in Icc (0 : ℝ) (t n : ℝ), (hP.gradientOrbit f s) j) =
      (∫ s in Icc (0 : ℝ) (t n : ℝ), hP.gradientOrbit f s) j at hp
    change (∀ᵐ ω ∂reducedLaw Q, ∀ᵐ x ∂(volume : Measure (Vec d)),
      (∫ s in Icc (0 : ℝ) (t n : ℝ), (hP.gradientOrbit f s) j) (translate x ω) =
        ∫ s in Icc (0 : ℝ) (t n : ℝ), V j (s, translate x ω)) at h
    simpa only [hp] using! h
  have hlU (n : ℕ) := ae_locally_integrable_joint_spatial_translate
    (reducedLaw Q) (reducedLaw_stationary Q)
    (integrable_joint_l2_representative (hiU n) hU heU)
  have hlV (n : ℕ) (j : Fin d) := ae_locally_integrable_joint_spatial_translate
    (reducedLaw Q) (reducedLaw_stationary Q)
    (integrable_joint_l2_representative (hiV n j) (hV j) (heV j))
  obtain ⟨G, hG, hsp⟩ := hP.exists_ae_windowIntegrals_spatial f (fun _ => 0) t
  have hint (n : ℕ) : (∫ s in (0 : ℝ)..(t n : ℝ), P s.toNNReal f) =
      ∫ s in Icc (0 : ℝ) (t n : ℝ), P s.toNNReal f := by
    rw [intervalIntegral.integral_of_le (NNReal.coe_nonneg (t n)), integral_Icc_eq_integral_Ioc]
  have hGeq (n : ℕ) : G n = fun j => (∫ s in Icc (0 : ℝ) (t n : ℝ), hP.gradientOrbit f s) j := by
    have hg := hG n
    change HasComplexHorizontalGradient _ _ (∫ s in (0 : ℝ)..(t n : ℝ), P s.toNNReal f) _ at hg
    rw [hint n] at hg
    exact hg.unique (hP.integral_orbit_gradient f (t n))
  refine ⟨U, V, hU, hV, heU, heV, ?_⟩
  filter_upwards [hsp, ae_all_iff.mpr hcU,
    ae_all_iff.mpr (fun n => ae_all_iff.mpr (hcV n)),
    ae_all_iff.mpr hlU,
    ae_all_iff.mpr (fun n => ae_all_iff.mpr (hlV n))]
    with ω hsp hcu hcv hlu hlv
  intro n
  have hs := hsp n
  dsimp only at hs
  simp only [NNReal.coe_zero, hint n, hGeq n] at hs
  refine ⟨hcu n, hcv n, ?_, ?_, ?_, fun K hK => ⟨hlu n K hK, fun j => hlv n j K hK⟩⟩
  · intro j
    exact (hs.1 j).congr_ae
      (by simpa only [Measure.restrict_univ] using! (hcu n).mono (fun x h => congrArg Complex.re h))
      (by simpa only [Measure.restrict_univ] using! (hcv n j).mono (fun x h => congrArg Complex.re h))
  · intro j
    exact (hs.2.1 j).congr_ae
      (by simpa only [Measure.restrict_univ] using! (hcu n).mono (fun x h => congrArg Complex.im h))
      (by simpa only [Measure.restrict_univ] using! (hcv n j).mono (fun x h => congrArg Complex.im h))
  · intro L hL
    exact ⟨(hs.2.2 L hL).1.ae_eq (ae_restrict_of_ae (hcu n)),
      fun j => ((hs.2.2 L hL).2.2 j).ae_eq (ae_restrict_of_ae (hcv n j))⟩

end EinsteinFull
