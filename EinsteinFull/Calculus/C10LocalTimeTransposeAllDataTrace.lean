import EinsteinFull.Calculus.C9LocalTimeTransposeTrace
import EinsteinFull.Work.W2.TransposeAllDataHorizonEnergySupport
import EinsteinFull.Work.W2.TransposeCoreUniformOrbitSupport
import EinsteinFull.Work.W3.ForwardLocalSpacetimeEnergySupport
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators
noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation EinsteinFull
private theorem trace_L2_norm_sq {X : Type*} [MeasurableSpace X]
    {μ : Measure X} (f : Lp ℂ 2 μ) :
    ‖f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp only [real_inner_self_eq_norm_sq]

private theorem trace_toLp_norm_sq {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {f : X → ℂ} (hf : MemLp f 2 μ) :
    ‖hf.toLp f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂μ := by
  rw [trace_L2_norm_sq]
  exact integral_congr_ae (hf.coeFn_toLp.mono fun _ hx =>
    congrArg (fun z : ℂ => ‖z‖ ^ 2) hx)

/-- Squared local masses are continuous for strong local L² convergence. -/
private theorem trace_mass_tendsto {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {f : ℕ → X → ℂ} {g : X → ℂ}
    (hf : ∀ n, MemLp (f n) 2 μ) (hg : MemLp g 2 μ)
    (he : Tendsto (fun n => ∫ x, ‖f n x - g x‖ ^ 2 ∂μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, ‖f n x‖ ^ 2 ∂μ) atTop
      (𝓝 (∫ x, ‖g x‖ ^ 2 ∂μ)) := by
  have hd (n : ℕ) : ‖(hf n).toLp (f n) - hg.toLp g‖ ^ 2 =
      ∫ x, ‖f n x - g x‖ ^ 2 ∂μ := by
    rw [trace_L2_norm_sq]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub ((hf n).toLp (f n)) (hg.toLp g),
      (hf n).coeFn_toLp, hg.coeFn_toLp] with x hx hfx hgx
    simp only [hx, Pi.sub_apply, hfx, hgx]
  have hsq : Tendsto (fun n => ‖(hf n).toLp (f n) - hg.toLp g‖ ^ 2)
      atTop (𝓝 0) := by simpa only [hd] using he
  have hn := hsq.sqrt
  simp only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] at hn
  have ht := (tendsto_iff_norm_sub_tendsto_zero.mpr hn).norm.pow 2
  simpa only [trace_toLp_norm_sq] using ht

/-- Nonnegative integrable errors with vanishing expectation have an almost
surely vanishing subsequence. The selected sequence may depend on the window. -/
private theorem trace_error_subsequence {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {e : ℕ → Ω → ℝ}
    (hi : ∀ n, Integrable (e n) μ) (he : ∀ n ω, 0 ≤ e n ω)
    (ht : Tendsto (fun n => ∫ ω, e n ω ∂μ) atTop (𝓝 0)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧
      ∀ᵐ ω ∂μ, Tendsto (fun n => e (ns n) ω) atTop (𝓝 0) := by
  let E (n : ℕ) : Lp ℝ 1 μ := (hi n).toL1 (e n)
  have hn (n : ℕ) : ‖E n‖ = ∫ ω, e n ω ∂μ := by
    rw [L1.norm_eq_integral_norm]
    apply integral_congr_ae
    filter_upwards [(hi n).coeFn_toL1] with ω hω
    rw [hω, Real.norm_eq_abs, abs_of_nonneg (he n ω)]
  have hE : Tendsto E atTop (𝓝 0) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simpa only [sub_zero, hn] using ht
  obtain ⟨ns, hns, hae⟩ := (tendstoInMeasure_of_tendsto_Lp hE).exists_seq_tendsto_ae
  refine ⟨ns, hns, ?_⟩
  filter_upwards [hae, ae_all_iff.mpr (fun n => (hi n).coeFn_toL1),
    Lp.coeFn_zero ℝ 1 μ] with ω hω heω hz
  simpa only [E, heω, hz, Pi.zero_apply] using hω

/-- Product L² convergence gives samplewise convergence of local masses along
one subsequence, retaining the prescribed representatives. -/
private theorem trace_section_mass_subsequence
    {X Ω : Type*} [MeasurableSpace X] [MeasurableSpace Ω]
    {ν : Measure X} {μ : Measure Ω} [SFinite ν] [SFinite μ]
    {F : ℕ → X × Ω → ℂ} {G : X × Ω → ℂ}
    (hF : ∀ n, Measurable (F n)) (hG : Measurable G)
    (hiF : ∀ n, Integrable (fun p => ‖F n p‖ ^ 2) (ν.prod μ))
    (hiG : Integrable (fun p => ‖G p‖ ^ 2) (ν.prod μ))
    (ht : Tendsto (fun n => ∫ ω, ∫ x, ‖F n (x, ω) - G (x, ω)‖ ^ 2 ∂ν ∂μ)
      atTop (𝓝 0)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∀ᵐ ω ∂μ,
      Tendsto (fun n => ∫ x, ‖F (ns n) (x, ω)‖ ^ 2 ∂ν) atTop
        (𝓝 (∫ x, ‖G (x, ω)‖ ^ 2 ∂ν)) := by
  have hMG : MemLp G 2 (ν.prod μ) :=
    (memLp_two_iff_integrable_sq_norm hG.aestronglyMeasurable).mpr hiG
  have hiD (n : ℕ) : Integrable (fun p => ‖F n p - G p‖ ^ 2) (ν.prod μ) :=
    (((memLp_two_iff_integrable_sq_norm (hF n).aestronglyMeasurable).mpr
      (hiF n)).sub hMG).norm.integrable_sq
  obtain ⟨ns, hns, he⟩ := trace_error_subsequence
    (fun n => (hiD n).integral_prod_right)
    (fun n ω => integral_nonneg fun x => sq_nonneg _) ht
  refine ⟨ns, hns, ?_⟩
  filter_upwards [he, hiG.prod_left_ae,
    ae_all_iff.mpr (fun n => (hiF n).prod_left_ae)] with ω heω hgω hfω
  have hf (n : ℕ) : MemLp (fun x => F (ns n) (x, ω)) 2 ν :=
    (memLp_two_iff_integrable_sq_norm
      ((hF (ns n)).comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable).mpr
        (hfω (ns n))
  have hg : MemLp (fun x => G (x, ω)) 2 ν :=
    (memLp_two_iff_integrable_sq_norm
      (hG.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable).mpr hgω
  exact trace_mass_tendsto hf hg heω

private theorem trace_repr_square_integral {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {u : Lp ℂ 2 μ} {U : Ω → ℂ} (hU : U =ᵐ[μ] u) :
    (∫ ω, ‖U ω‖ ^ 2 ∂μ) = ‖u‖ ^ 2 := by
  rw [trace_L2_norm_sq]
  exact integral_congr_ae (hU.mono fun _ h => congrArg (fun z : ℂ => ‖z‖ ^ 2) h)

/-- Stationarity transports path L² convergence to local sample masses. -/
private theorem trace_spatial_mass_subsequence {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q] (hQ : IsStationary Q)
    {ν : Measure ℝ} [SFinite ν] (m : Measure (Vec d)) [IsFiniteMeasure m]
    {u : ℕ → ℝ → Lp ℂ 2 Q} {v : ℝ → Lp ℂ 2 Q}
    {U : ℕ → ℝ × FieldPair d → ℂ} {V : ℝ × FieldPair d → ℂ}
    (hU : ∀ n, Measurable (U n)) (hV : Measurable V)
    (heU : ∀ n s, (fun ω => U n (s, ω)) =ᵐ[Q] u n s)
    (heV : ∀ s, (fun ω => V (s, ω)) =ᵐ[Q] v s)
    (hiU : ∀ n, Integrable (fun s => ‖u n s‖ ^ 2) ν)
    (hiV : Integrable (fun s => ‖v s‖ ^ 2) ν)
    (hiD : ∀ n, Integrable (fun s => ‖u n s - v s‖ ^ 2) ν)
    (ht : Tendsto (fun n => ∫ s, ‖u n s - v s‖ ^ 2 ∂ν) atTop (𝓝 0)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∀ᵐ ω ∂Q,
      Tendsto (fun n => ∫ p : Vec d × ℝ,
        ‖U (ns n) (p.2, translate p.1 ω)‖ ^ 2 ∂(m.prod ν)) atTop
        (𝓝 (∫ p : Vec d × ℝ, ‖V (p.2, translate p.1 ω)‖ ^ 2 ∂(m.prod ν))) := by
  have hmap : Measurable (fun p : (Vec d × ℝ) × FieldPair d =>
      (p.1.2, translate p.1.1 p.2)) :=
    measurable_fst.snd.prodMk (Probability.continuous_translate.measurable.comp
      (measurable_fst.fst.prodMk measurable_snd))
  have heD (n : ℕ) (s : ℝ) :
      (fun ω => U n (s, ω) - V (s, ω)) =ᵐ[Q] (fun ω => (u n s - v s) ω) := by
    filter_upwards [heU n s, heV s, Lp.coeFn_sub (u n s) (v s)] with ω hu hv hd
    simp only [hu, hv, hd, Pi.sub_apply]
  have hD (n : ℕ) : Integrable (fun p => ‖U n p - V p‖ ^ 2) (ν.prod Q) :=
    integrable_sq_joint_l2_representative (hiD n) ((hU n).sub hV) (heD n)
  apply trace_section_mass_subsequence (fun n => (hU n).comp hmap) (hV.comp hmap)
    (fun n => integrable_joint_spatial_energy Q hQ m
      (integrable_sq_joint_l2_representative (hiU n) (hU n) (heU n)))
    (integrable_joint_spatial_energy Q hQ m
      (integrable_sq_joint_l2_representative hiV hV heV))
  have he (n : ℕ) :
      (∫ ω, ∫ p : Vec d × ℝ,
        ‖U n (p.2, translate p.1 ω) - V (p.2, translate p.1 ω)‖ ^ 2 ∂(m.prod ν) ∂Q) =
      m.real univ * ∫ s, ‖u n s - v s‖ ^ 2 ∂ν := by
    have hs := integral_joint_spatial_energy Q hQ m (((hU n).sub hV).norm.pow_const 2) (hD n)
    dsimp only [Pi.sub_apply] at hs
    rw [hs]
    congr 1
    exact integral_congr_ae (ae_of_all _ fun s => trace_repr_square_integral (heD n s))
  simpa only [Function.comp_apply, Pi.sub_apply, he, mul_zero] using ht.const_mul (m.real univ)

private theorem trace_spatial_square {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q] (hQ : IsStationary Q)
    (m : Measure (Vec d)) [IsFiniteMeasure m]
    {U : FieldPair d → ℂ} (hU : Measurable U) (hM : MemLp U 2 Q) :
    Integrable (fun p : Vec d × FieldPair d => ‖U (translate p.1 p.2)‖ ^ 2)
      (m.prod Q) ∧
    (∫ ω, ∫ x, ‖U (translate x ω)‖ ^ 2 ∂m ∂Q) =
      m.real univ * ∫ ω, ‖U ω‖ ^ 2 ∂Q := by
  have hb := hM.norm.integrable_sq.comp_snd m
  have hm := (MeasurePreserving.id m).skew_product
    (g := fun x ω => translate x ω) Probability.continuous_translate.measurable
    (ae_of_all _ fun x => (measurePreserving_translate Q hQ x).map_eq)
  have hi : Integrable (fun p : Vec d × FieldPair d => ‖U (translate p.1 p.2)‖ ^ 2)
      (m.prod Q) := (hm.integrable_comp hb.aestronglyMeasurable).mpr hb
  refine ⟨hi, ?_⟩
  have he (x : Vec d) : (∫ ω, ‖U (translate x ω)‖ ^ 2 ∂Q) =
      ∫ ω, ‖U ω‖ ^ 2 ∂Q := by
    have hme : AEStronglyMeasurable (fun ω => ‖U ω‖ ^ 2)
        (Measure.map (translate x) Q) := (hU.norm.pow_const 2).aestronglyMeasurable
    rw [← integral_map (measurePreserving_translate Q hQ x).measurable.aemeasurable hme,
      (measurePreserving_translate Q hQ x).map_eq]
  rw [← integral_integral_swap hi]
  simp only [he, integral_const, smul_eq_mul]

private theorem trace_terminal_mass_subsequence {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q] (hQ : IsStationary Q)
    (m : Measure (Vec d)) [IsFiniteMeasure m]
    {u : ℕ → Lp ℂ 2 Q} {v : Lp ℂ 2 Q}
    (ht : Tendsto u atTop (𝓝 v)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∀ᵐ ω ∂Q,
      Tendsto (fun n => ∫ x, ‖u (ns n) (translate x ω)‖ ^ 2 ∂m) atTop
        (𝓝 (∫ x, ‖v (translate x ω)‖ ^ 2 ∂m)) := by
  have hmap : Measurable (fun p : Vec d × FieldPair d => translate p.1 p.2) :=
    Probability.continuous_translate.measurable
  apply trace_section_mass_subsequence
    (fun n => (Lp.stronglyMeasurable (u n)).measurable.comp hmap)
    ((Lp.stronglyMeasurable v).measurable.comp hmap)
    (fun n => (trace_spatial_square Q hQ m (Lp.stronglyMeasurable (u n)).measurable
      (Lp.memLp (u n))).1)
    (trace_spatial_square Q hQ m (Lp.stronglyMeasurable v).measurable (Lp.memLp v)).1
  have he (n : ℕ) :
      (∫ ω, ∫ x, ‖u n (translate x ω) - v (translate x ω)‖ ^ 2 ∂m ∂Q) =
      m.real univ * ‖u n - v‖ ^ 2 := by
    have hh := (trace_spatial_square Q hQ m
      ((Lp.stronglyMeasurable (u n)).measurable.sub (Lp.stronglyMeasurable v).measurable)
      ((Lp.memLp (u n)).sub (Lp.memLp v))).2
    dsimp only [Pi.sub_apply] at hh
    rw [hh]
    congr 1
    exact trace_repr_square_integral (u := u n - v) (Lp.coeFn_sub (u n) v).symm
  have hn := ((ht.sub_const v).norm.pow 2).const_mul (m.real univ)
  simpa only [Function.comp_apply, he, sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0),
    mul_zero] using hn

private theorem trace_orbit_error_integral_tendsto
    {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
    {P T : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (hT : IsComplexTransposeSemigroup Q P T)
    (f : Lp ℂ 2 (reducedLaw Q)) (b c : ℝ) :
    Tendsto (fun n => ∫ s in Icc b c,
      ‖T s.toNNReal (complexTransposeResolventApproximation Q i ζ n f) -
        T s.toNNReal f‖ ^ 2) atTop (𝓝 0) := by
  let u := fun n => complexTransposeResolventApproximation Q i ζ n f
  let K := Real.exp (complexForceShift d Λ₀ ζ * (c.toNNReal : ℝ))
  have he (n : ℕ) (s : ℝ) (hs : s ∈ Icc b c) :
      ‖T s.toNNReal (u n) - T s.toNNReal f‖ ^ 2 ≤ (K * ‖u n - f‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (hT.orbit_approximation_error_le hP
      c.toNNReal n f s.toNNReal (Real.toNNReal_le_toNNReal hs.2)) 2
  have hc (g : Lp ℂ 2 (reducedLaw Q)) : Continuous (fun s : ℝ => T s.toNNReal g) :=
    (hT.continuous_apply hP g).comp continuous_real_toNNReal
  have hb (n : ℕ) :
      (∫ s in Icc b c, ‖T s.toNNReal (u n) - T s.toNNReal f‖ ^ 2) ≤
        volume.real (Icc b c) * (K * ‖u n - f‖) ^ 2 := by
    have hi : IntegrableOn (fun s : ℝ => ‖T s.toNNReal (u n) - T s.toNNReal f‖ ^ 2)
        (Icc b c) volume :=
      (((hc (u n)).sub (hc f)).norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc
    calc
      _ ≤ ∫ s in Icc b c, (K * ‖u n - f‖) ^ 2 :=
        integral_mono_ae hi (integrable_const _) (ae_restrict_mem measurableSet_Icc |>.mono
          fun s hs => he n s hs)
      _ = _ := by rw [integral_const, smul_eq_mul, measureReal_restrict_apply_univ]
  have ht := (((tendsto_complexTransposeResolventApproximation Q i ζ f).sub_const f).norm.const_mul K).pow 2
  have ht' := ht.const_mul (volume.real (Icc b c))
  simp only [sub_self, norm_zero, mul_zero, zero_pow (by decide : 2 ≠ 0)] at ht'
  exact squeeze_zero (fun n => integral_nonneg fun s => sq_nonneg _) hb ht'

/-- Terminal-ball trace for arbitrary actual transpose L² data. -/
theorem local_time_transpose_all_data_ae_terminal_ball_L2
    (d : ℕ) [Fact (2 ≤ d)] :
    ∃ B : ℝ, 0 < B ∧
    ∀ (Λ₀ r₀ : ℝ) (Q : EnvironmentLaw d Λ₀ r₀)
      (i : Fin d) (ζ : ℂ)
      (P T : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)),
      IsComplexEnvironmentSemigroup Q i ζ P →
      IsComplexTransposeSemigroup Q P T →
    ∀ (f : Lp ℂ 2 (reducedLaw Q)),
    ∃ W : ℝ × FieldPair d → ℂ,
      Measurable W ∧
      (∀ s, (fun ω => W (s, ω)) =ᵐ[reducedLaw Q] T s.toNNReal f) ∧
      ∀ b c : ℝ, 0 ≤ b → b < c →
        ∀ (z : Vec d) (r : ℝ), 0 < r →
          ∀ᵐ ω ∂reducedLaw Q,
            (∫ x in {x | euclideanNorm (x - z) ≤ r},
              ‖(T c.toNNReal f) (translate x ω)‖ ^ 2) ≤
            2 * ((c - b)⁻¹ +
              10 * (Real.exp (2 * Λ₀) * Λ₀) ^ 3 *
                (‖ζ‖ ^ 2 + (d : ℝ) * B ^ 2 / r ^ 2)) *
              (∫ s in Icc b c, ∫ x in {x | euclideanNorm (x - z) ≤ 2 * r},
                ‖W (s, translate x ω)‖ ^ 2)
 := by
  obtain ⟨B, hB, htrace⟩ := local_time_transpose_ae_terminal_ball_L2 d
  refine ⟨B, hB, ?_⟩
  intro Λ₀ r₀ Q i ζ P T hP hT f
  let := reducedLaw_probability Q
  let u := fun n => complexTransposeResolventApproximation Q i ζ n f
  let g := fun (n : ℕ) =>
    (((complexForceShift d Λ₀ ζ + ((n : ℝ) + 1) : ℝ) : ℂ) • u n -
      (((n : ℝ) + 1 : ℝ) : ℂ) • f)
  have hgraph (n : ℕ) : IsComplexTransposeGeneratorPair Q i ζ (u n) (g n) :=
    complexTransposeResolventApproximation_graph Q i ζ n f
  choose U hU heU hbound using fun n => htrace Λ₀ r₀ Q i ζ P T hP hT (u n) (g n) (hgraph n)
  have hc (a : Lp ℂ 2 (reducedLaw Q)) : Continuous (fun s : ℝ => T s.toNNReal a) :=
    (hT.continuous_apply hP a).comp continuous_real_toNNReal
  obtain ⟨W, hW, heW⟩ := EinsteinFull.StronglyMeasurable.exists_joint_l2_representative (hc f).stronglyMeasurable
  refine ⟨W, hW, heW, ?_⟩
  intro b c hb hbc z r hr
  let K := {x : Vec d | euclideanNorm (x - z) ≤ 2 * r}
  let S := {x : Vec d | euclideanNorm (x - z) ≤ r}
  have hK : IsCompact K := isCompact_physical_euclidean_closedBall z (2 * r)
  have hS : IsCompact S := isCompact_physical_euclidean_closedBall z r
  let : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.mpr hK.measure_ne_top
  let : IsFiniteMeasure (volume.restrict S) := isFiniteMeasure_restrict.mpr hS.measure_ne_top
  have hiU (n : ℕ) : IntegrableOn (fun s => ‖T s.toNNReal (u n)‖ ^ 2)
      (Icc b c) volume := (hc (u n)).norm.pow 2 |>.continuousOn.integrableOn_compact isCompact_Icc
  have hiW : IntegrableOn (fun s => ‖T s.toNNReal f‖ ^ 2)
      (Icc b c) volume := (hc f).norm.pow 2 |>.continuousOn.integrableOn_compact isCompact_Icc
  have hiD (n : ℕ) : IntegrableOn
      (fun s => ‖T s.toNNReal (u n) - T s.toNNReal f‖ ^ 2) (Icc b c) volume :=
    (((hc (u n)).sub (hc f)).norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc
  obtain ⟨ns, hns, hspace⟩ := trace_spatial_mass_subsequence
    (reducedLaw Q) (reducedLaw_stationary Q) (volume.restrict K)
    hU hW heU heW hiU hiW hiD (trace_orbit_error_integral_tendsto hP hT f b c)
  have hut : Tendsto (fun n => T c.toNNReal (u (ns n))) atTop (𝓝 (T c.toNNReal f)) :=
    ((T c.toNNReal).continuous.tendsto f).comp
      ((tendsto_complexTransposeResolventApproximation Q i ζ f).comp hns.tendsto_atTop)
  obtain ⟨ms, hms, hterminal⟩ := trace_terminal_mass_subsequence
    (reducedLaw Q) (reducedLaw_stationary Q) (volume.restrict S) hut
  have hiωU (n : ℕ) := (integrable_joint_spatial_energy (reducedLaw Q)
    (reducedLaw_stationary Q) (volume.restrict K)
    (integrable_sq_joint_l2_representative (hiU n) (hU n) (heU n))).prod_left_ae
  have hiωW := (integrable_joint_spatial_energy (reducedLaw Q)
    (reducedLaw_stationary Q) (volume.restrict K)
    (integrable_sq_joint_l2_representative hiW hW heW)).prod_left_ae
  filter_upwards [hspace, hterminal, hiωW, ae_all_iff.mpr hiωU,
    ae_all_iff.mpr (fun n => hbound n b c hb hbc z r hr)] with ω hs ht hw hu hineq
  have heq (F : ℝ × FieldPair d → ℂ)
      (hi : Integrable (fun p : Vec d × ℝ => ‖F (p.2, translate p.1 ω)‖ ^ 2)
        ((volume.restrict K).prod (volume.restrict (Icc b c)))) :
      (∫ p : Vec d × ℝ, ‖F (p.2, translate p.1 ω)‖ ^ 2
        ∂((volume.restrict K).prod (volume.restrict (Icc b c)))) =
        ∫ s in Icc b c, ∫ x in K, ‖F (s, translate x ω)‖ ^ 2 := by
    rw [integral_prod _ hi, integral_integral_swap hi]
  have hs' := hs.comp hms.tendsto_atTop
  simp only [heq W hw, heq (U _) (hu _)] at hs'
  exact le_of_tendsto_of_tendsto ht (hs'.const_mul
    (2 * ((c - b)⁻¹ + 10 * (Real.exp (2 * Λ₀) * Λ₀) ^ 3 *
      (‖ζ‖ ^ 2 + (d : ℝ) * B ^ 2 / r ^ 2))))
    (Eventually.of_forall fun n => hineq (ns (ms n)))

end EinsteinFull.Blueprint
