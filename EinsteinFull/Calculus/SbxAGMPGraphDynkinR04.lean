import EinsteinFull.Calculus.SbxS5RegularGMPActionR03
import EinsteinFull.Calculus.SbxAEndpointL2BoundR04

/-! Finite-horizon occupation of actual GMP generator graph approximations. -/

open EinsteinRelation MeasureTheory ProbabilityTheory
open EinsteinRelation.External.GantertSection7Support
open scoped NNReal ENNReal Topology

namespace EinsteinFull

/-- The graph residual has vanishing actual-GMP annealed occupation if the
literal finite-horizon occupation L² estimate holds for measurable real tests. -/
theorem s5_gmp_graph_residual_occupation_tendsto_of_l2_estimate
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (mu : ℝ) (h0 : 0 ≤ mu) (h1 : mu ≤ 1) (P : QuenchedPathLaws d)
    (_hP : IsGMPReducedKernel hd Q.ellipticity_parameter Q mu h0 h1 P)
    (T : ℝ≥0)
    (hocc : ∀ (v : FieldPair d → ℝ), Measurable v → MemLp v 2 (reducedLaw Q) →
      (∫⁻ t in Set.Ioc (0 : ℝ) (T : ℝ),
        ∫⁻ ω, ∫⁻ γ : Path d, ‖v (translate (γ t.toNNReal) (reduce ω))‖ₑ
          ∂P (0, ω) ∂Q.measure) ≤
        (ENNReal.ofReal (Real.exp (mu ^ 2 * (Real.exp (2 * Λ₀) * Λ₀) * (T : ℝ))) ^
          (1 / 2 : ℝ) * eLpNorm v 2 (reducedLaw Q)) *
            (volume : Measure ℝ) (Set.Ioc 0 (T : ℝ)))
    (s : ℝ) (hs : 0 < s) (f g : Lp ℂ 2 (reducedLaw Q))
    (hfg : IsComplexGeneratorPair Q ⟨0, by omega⟩ (mu : ℂ) f g)
    {G : Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hG : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) f G)
    (L : ℂ →L[ℝ] ℝ) :
    ∃ (r : ℕ → FieldPair d → ℝ) (hr : ∀ n, MemLp (r n) 2 (reducedLaw Q)),
      (∀ n, Measurable (r n)) ∧
      (∀ n, r n =ᵐ[reducedLaw Q] fun w =>
        s * horizontalMollify (Calculus.unitMassScaledMollifier d (Entropy.scaleSeq n))
          (fun v => L (f v)) w -
        envGenerator hd mu (horizontalMollify
          (Calculus.unitMassScaledMollifier d (Entropy.scaleSeq n)) (fun v => L (f v))) w -
        L (((s : ℂ) • f - g) w)) ∧
      Filter.Tendsto (fun n => ∫⁻ t in Set.Ioc (0 : ℝ) (T : ℝ),
        ∫⁻ ω, ∫⁻ γ : Path d, ‖r n (translate (γ t.toNNReal) (reduce ω))‖ₑ
          ∂P (0, ω) ∂Q.measure) Filter.atTop (𝓝 0) := by
  obtain ⟨r, hr, hm, he, ht⟩ :=
    u3_signed_graph_mollified_residual_representatives hd Q mu s hs f g hfg hG L
  refine ⟨r, hr, hm, he, ?_⟩
  let C : ℝ≥0∞ := ENNReal.ofReal (Real.exp
    (mu ^ 2 * (Real.exp (2 * Λ₀) * Λ₀) * (T : ℝ))) ^ (1 / 2 : ℝ)
  let M : ℝ≥0∞ := (volume : Measure ℝ) (Set.Ioc 0 (T : ℝ))
  have hC : C ≠ ∞ :=
    ne_of_lt (ENNReal.rpow_lt_top_of_nonneg (by norm_num) ENNReal.ofReal_lt_top.ne)
  have hM : M ≠ ∞ := measure_Ioc_lt_top.ne
  have hr_lim : Filter.Tendsto (fun n => eLpNorm (r n) 2 (reducedLaw Q))
      Filter.atTop (𝓝 0) := by
    have hh := ENNReal.tendsto_ofReal ht
    simp only [ENNReal.ofReal_zero] at hh
    apply hh.congr
    intro n
    rw [Lp.norm_def, eLpNorm_congr_ae (hr n).coeFn_toLp,
      ENNReal.ofReal_toReal (hr n).eLpNorm_ne_top]
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds _
    (fun _ => bot_le) (fun n => hocc (r n) (hm n) (hr n))
  have hh := ENNReal.Tendsto.const_mul hr_lim (Or.inr hC)
  have hh' := ENNReal.Tendsto.mul_const (b := M) hh (Or.inr hM)
  simpa [C, M] using hh'


/-- Annealed occupation convergence yields a quenched subsequence for the
same supplied GMP kernel. -/
theorem s5_gmp_occupation_quenched_subsequence_of_tendsto
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (mu : ℝ) (h0 : 0 ≤ mu) (h1 : mu ≤ 1) (P : QuenchedPathLaws d)
    (hP : IsGMPReducedKernel hd Q.ellipticity_parameter Q mu h0 h1 P)
    (T : ℝ≥0) (r : ℕ → FieldPair d → ℝ) (hm : ∀ n, Measurable (r n))
    (hlim : Filter.Tendsto (fun n => ∫⁻ t in Set.Ioc (0 : ℝ) (T : ℝ),
      ∫⁻ ω, ∫⁻ γ : Path d, ‖r n (translate (γ t.toNNReal) (reduce ω))‖ₑ
        ∂P (0, ω) ∂Q.measure) Filter.atTop (𝓝 0)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∀ᵐ ω ∂Q.measure,
      Filter.Tendsto (fun n => ∫ t in Set.Ioc (0 : ℝ) (T : ℝ),
        ∫ γ : Path d, |r (ns n) (translate (γ t.toNNReal) (reduce ω))| ∂P (0, ω))
        Filter.atTop (𝓝 0) := by
  obtain ⟨K, hmarkov, hK⟩ := s5_gmp_origin_markov_version hd Q mu h0 h1 P hP
  let : IsMarkovKernel K := hmarkov
  have hK' : ∀ᵐ ω ∂Q.measure, P (0, ω) = K ω := hK.mono fun _ h => h.symm
  let μ := (volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) (T : ℝ))
  let ν := μ.prod (Q.measure ⊗ₘ K)
  let E : ℝ × (FieldPair d × Path d) → FieldPair d := fun p =>
    translate (p.2.2 p.1.toNNReal) (reduce p.2.1)
  have hE : Measurable E := by
    exact (Probability.continuous_translate.comp
      ((continuous_eval.comp ((continuous_snd.comp continuous_snd).prodMk
        (continuous_real_toNNReal.comp continuous_fst))).prodMk
        (Probability.continuous_reduce.comp (continuous_fst.comp continuous_snd)))).measurable
  let J (n : ℕ) : ℝ≥0∞ := ∫⁻ p, ‖r n (E p)‖ₑ ∂ν
  have hJ : Filter.Tendsto J Filter.atTop (𝓝 0) := by
    apply hlim.congr
    intro n
    exact (u3_supplied_force_finite_time_joint_occupation Q P K hK' T (r n) (hm n)).symm
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1
    (hJ.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ≥0∞) < 1)))
  let R (n : ℕ) := r (n + N)
  let F (n : ℕ) : ℝ × (FieldPair d × Path d) → ℝ := fun p => |R n (E p)|
  have hF (n : ℕ) : Measurable (F n) := (continuous_abs.measurable.comp ((hm (n + N)).comp hE))
  have hJfin (n : ℕ) : J (n + N) < ∞ :=
    (hN (n + N) (Nat.le_add_left N n)).trans_le le_top
  have hi (n : ℕ) : Integrable (F n) ν := by
    refine ⟨(hF n).aestronglyMeasurable, ?_⟩
    apply hasFiniteIntegral_iff_enorm.mpr
    simpa only [F, R, Real.enorm_eq_ofReal_abs, abs_abs, J] using hJfin n
  have hshift : Filter.Tendsto (fun n => J (n + N)) Filter.atTop (𝓝 0) :=
    hJ.comp (Filter.tendsto_add_atTop_nat N)
  have hreal : Filter.Tendsto (fun n => ∫ p, F n p ∂ν) Filter.atTop (𝓝 0) := by
    have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hshift
    simp only [ENNReal.toReal_zero] at h
    apply h.congr
    intro n
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun p => abs_nonneg _)
      (hF n).aestronglyMeasurable]
    simp only [R, Real.enorm_eq_ofReal_abs, J, Function.comp_def]
  obtain ⟨ns, hns, ha⟩ := u3_finite_time_occupation_quenched_subsequence Q K T R hi hreal
  refine ⟨fun n => ns n + N, fun i j hij => Nat.add_lt_add_right (hns hij) N, ?_⟩
  filter_upwards [ha, hK'] with ω hω hKω
  simpa only [R, hKω] using hω

/-- The graph residual vanishes along a quenched subsequence under the
literal finite-horizon occupation L² estimate. -/
theorem s5_gmp_graph_residual_quenched_subsequence_of_l2_estimate
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (mu : ℝ) (h0 : 0 ≤ mu) (h1 : mu ≤ 1) (P : QuenchedPathLaws d)
    (hP : IsGMPReducedKernel hd Q.ellipticity_parameter Q mu h0 h1 P)
    (T : ℝ≥0)
    (hocc : ∀ (v : FieldPair d → ℝ), Measurable v → MemLp v 2 (reducedLaw Q) →
      (∫⁻ t in Set.Ioc (0 : ℝ) (T : ℝ),
        ∫⁻ ω, ∫⁻ γ : Path d, ‖v (translate (γ t.toNNReal) (reduce ω))‖ₑ
          ∂P (0, ω) ∂Q.measure) ≤
        (ENNReal.ofReal (Real.exp (mu ^ 2 * (Real.exp (2 * Λ₀) * Λ₀) * (T : ℝ))) ^
          (1 / 2 : ℝ) * eLpNorm v 2 (reducedLaw Q)) *
            (volume : Measure ℝ) (Set.Ioc 0 (T : ℝ)))
    (s : ℝ) (hs : 0 < s) (f g : Lp ℂ 2 (reducedLaw Q))
    (hfg : IsComplexGeneratorPair Q ⟨0, by omega⟩ (mu : ℂ) f g)
    {G : Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hG : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) f G)
    (L : ℂ →L[ℝ] ℝ) :
    ∃ (r : ℕ → FieldPair d → ℝ) (ns : ℕ → ℕ), StrictMono ns ∧
      (∀ n, Measurable (r n)) ∧
      (∀ n, r n =ᵐ[reducedLaw Q] fun w =>
        s * horizontalMollify (Calculus.unitMassScaledMollifier d (Entropy.scaleSeq n))
          (fun v => L (f v)) w -
        envGenerator hd mu (horizontalMollify
          (Calculus.unitMassScaledMollifier d (Entropy.scaleSeq n)) (fun v => L (f v))) w -
        L (((s : ℂ) • f - g) w)) ∧
      ∀ᵐ ω ∂Q.measure,
        Filter.Tendsto (fun n => ∫ t in Set.Ioc (0 : ℝ) (T : ℝ),
          ∫ γ : Path d, |r (ns n) (translate (γ t.toNNReal) (reduce ω))|
            ∂P (0, ω)) Filter.atTop (𝓝 0) := by
  obtain ⟨r, hr, hm, he, hlim⟩ :=
    s5_gmp_graph_residual_occupation_tendsto_of_l2_estimate
      hd Q mu h0 h1 P hP T hocc s hs f g hfg hG L
  obtain ⟨ns, hns, hocc'⟩ :=
    s5_gmp_occupation_quenched_subsequence_of_tendsto hd Q mu h0 h1 P hP T r hm hlim
  exact ⟨r, ns, hns, hm, he, hocc'⟩

/-- The actual GMP paths avoid reduced-law null sets at almost every time. -/
theorem s5_gmp_environment_null_occupation
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1) (Y : QuenchedPathLaws d)
    (hY : IsGMPReducedKernel hd Q.ellipticity_parameter Q lam h0 h1 Y)
    (N : Set (FieldPair d)) (hNm : MeasurableSet N) (hN : reducedLaw Q N = 0) :
    ∀ᵐ ω ∂Q.measure, ∀ᵐ γ ∂Y (0, ω),
      ∀ᵐ t ∂volume.restrict (Set.Ioi (0 : ℝ)),
        translate (γ t.toNNReal) (reduce ω) ∉ N := by
  let : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  have hn : ∀ᵐ ρ ∂reducedLaw Q, ρ ∉ N := by
    simpa only [ae_iff, not_not, Set.ofPred_mem_eq] using hN
  have horbit : ∀ᵐ ρ ∂reducedLaw Q, ∀ᵐ x ∂(volume : Measure (Vec d)),
      translate x ρ ∉ N := by
    apply (Measure.ae_ae_comm (μ := (volume : Measure (Vec d)))
      (ν := reducedLaw Q) (hNm.preimage Probability.continuous_translate.measurable).compl).mp
    exact ae_of_all _ fun x =>
      (measurePreserving_translate (reducedLaw Q) (reducedLaw_stationary Q) x).quasiMeasurePreserving.ae hn
  have hpull : ∀ᵐ ω ∂Q.measure, ∀ᵐ x ∂(volume : Measure (Vec d)),
      translate x (reduce ω) ∉ N :=
    ae_of_ae_map Probability.measurable_reduce.aemeasurable horbit
  have hΛ : 0 < Λ₀ := lt_of_lt_of_le zero_lt_one Q.ellipticity_parameter
  filter_upwards [Q.regular, hpull,
    s5_gmp_textbook_at_every_start hd Q lam h0 h1 Y hY]
    with ω hω horbitω htextbook
  have hocc := foundation_reduced_textbook_averaged_occupation_ac_of_two_le
    hd hΛ hω (firstCoordinateIndex hd) lam (htextbook 0)
  exact c16_ae_path_of_averaged_occupation (Y (0, ω)) hocc horbitω


/-- Reduced-law representatives agree along actual GMP occupation. -/
theorem s5_gmp_ae_eq_time_first_occupation
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1) (Y : QuenchedPathLaws d)
    (hY : IsGMPReducedKernel hd Q.ellipticity_parameter Q lam h0 h1 Y)
    (T : ℝ≥0) (f g : FieldPair d → ℝ) (hfg : f =ᵐ[reducedLaw Q] g) :
    ∀ᵐ ω ∂Q.measure, ∀ᵐ t ∂volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ)),
      ∀ᵐ γ ∂Y (0, ω),
        f (translate (γ t.toNNReal) (reduce ω)) =
          g (translate (γ t.toNNReal) (reduce ω)) := by
  obtain ⟨N, hsub, hNm, hN⟩ := exists_measurable_superset_of_null (ae_iff.mp hfg)
  filter_upwards [s5_gmp_environment_null_occupation hd Q lam h0 h1 Y hY N hNm hN,
    s5_gmp_textbook_at_every_start hd Q lam h0 h1 Y hY] with ω hω hprob
  let : IsProbabilityMeasure (Y (0, ω)) := (hprob 0).1
  have hE : Measurable (fun p : Path d × ℝ => translate (p.1 p.2.toNNReal) (reduce ω)) := by
    exact (Probability.continuous_translate.comp
      ((continuous_eval.comp (continuous_fst.prodMk
        (continuous_real_toNNReal.comp continuous_snd))).prodMk continuous_const)).measurable
  have havoid : ∀ᵐ γ ∂Y (0, ω),
      ∀ᵐ t ∂volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ)),
        translate (γ t.toNNReal) (reduce ω) ∉ N := by
    filter_upwards [hω] with γ hγ
    exact ae_restrict_of_ae_restrict_of_subset (fun _ ht => ht.1) hγ
  have hm : MeasurableSet {p : Path d × ℝ |
      translate (p.1 p.2.toNNReal) (reduce ω) ∉ N} := (hNm.preimage hE).compl
  have hswap := (Measure.ae_ae_comm (μ := Y (0, ω))
    (ν := volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ))) hm).mp havoid
  filter_upwards [hswap] with t ht
  filter_upwards [ht] with γ hγ
  by_contra hne
  exact hγ (hsub hne)


/-- Absolute occupation depends only on the reduced-law representative. -/
theorem s5_gmp_absolute_occupation_eq
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1) (Y : QuenchedPathLaws d)
    (hY : IsGMPReducedKernel hd Q.ellipticity_parameter Q lam h0 h1 Y)
    (T : ℝ≥0) (f g : FieldPair d → ℝ) (hfg : f =ᵐ[reducedLaw Q] g) :
    ∀ᵐ ω ∂Q.measure,
      (∫ t in Set.Ioc (0 : ℝ) (T : ℝ), ∫ γ : Path d,
        |f (translate (γ t.toNNReal) (reduce ω))| ∂Y (0, ω)) =
      ∫ t in Set.Ioc (0 : ℝ) (T : ℝ), ∫ γ : Path d,
        |g (translate (γ t.toNNReal) (reduce ω))| ∂Y (0, ω) := by
  filter_upwards [s5_gmp_ae_eq_time_first_occupation hd Q lam h0 h1 Y hY T f g hfg] with ω hω
  apply integral_congr_ae
  filter_upwards [hω] with t ht
  apply integral_congr_ae
  filter_upwards [ht] with γ hγ
  rw [hγ]

/-- The literal graph residual vanishes along a quenched subsequence under
the finite-horizon occupation L² estimate. -/
theorem s5_gmp_literal_graph_residual_quenched_subsequence_of_l2_estimate
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (mu : ℝ) (h0 : 0 ≤ mu) (h1 : mu ≤ 1) (P : QuenchedPathLaws d)
    (hP : IsGMPReducedKernel hd Q.ellipticity_parameter Q mu h0 h1 P)
    (T : ℝ≥0)
    (hocc : ∀ (v : FieldPair d → ℝ), Measurable v → MemLp v 2 (reducedLaw Q) →
      (∫⁻ t in Set.Ioc (0 : ℝ) (T : ℝ),
        ∫⁻ ω, ∫⁻ γ : Path d, ‖v (translate (γ t.toNNReal) (reduce ω))‖ₑ
          ∂P (0, ω) ∂Q.measure) ≤
        (ENNReal.ofReal (Real.exp (mu ^ 2 * (Real.exp (2 * Λ₀) * Λ₀) * (T : ℝ))) ^
          (1 / 2 : ℝ) * eLpNorm v 2 (reducedLaw Q)) *
            (volume : Measure ℝ) (Set.Ioc 0 (T : ℝ)))
    (s : ℝ) (hs : 0 < s) (f g : Lp ℂ 2 (reducedLaw Q))
    (hfg : IsComplexGeneratorPair Q ⟨0, by omega⟩ (mu : ℂ) f g)
    {G : Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hG : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) f G)
    (L : ℂ →L[ℝ] ℝ) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∀ᵐ ω ∂Q.measure,
      Filter.Tendsto (fun n => ∫ t in Set.Ioc (0 : ℝ) (T : ℝ),
        ∫ γ : Path d, |s * horizontalMollify
            (Calculus.unitMassScaledMollifier d (Entropy.scaleSeq (ns n)))
            (fun v => L (f v)) (translate (γ t.toNNReal) (reduce ω)) -
          envGenerator hd mu (horizontalMollify
            (Calculus.unitMassScaledMollifier d (Entropy.scaleSeq (ns n))) (fun v => L (f v)))
            (translate (γ t.toNNReal) (reduce ω)) -
          L (((s : ℂ) • f - g) (translate (γ t.toNNReal) (reduce ω)))| ∂P (0, ω))
        Filter.atTop (𝓝 0) := by
  obtain ⟨r, ns, hns, _, he, hocc'⟩ :=
    s5_gmp_graph_residual_quenched_subsequence_of_l2_estimate
      hd Q mu h0 h1 P hP T hocc s hs f g hfg hG L
  have ha := fun n => s5_gmp_absolute_occupation_eq hd Q mu h0 h1 P hP T
    (r (ns n)) _ (he (ns n))
  refine ⟨ns, hns, ?_⟩
  filter_upwards [ae_all_iff.mpr ha, hocc'] with ω hω hωocc
  apply hωocc.congr
  intro n
  exact hω n

/-- The actual GMP mollified graph orbit is a local martingale. -/
theorem s5_gmp_graph_mollified_orbit_local_martingale
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1) (s : ℝ) (hs : 0 < s)
    (Y : QuenchedPathLaws d)
    (hY : IsGMPReducedKernel hd Q.ellipticity_parameter Q lam h0 h1 Y)
    (f g : Lp ℂ 2 (reducedLaw Q))
    (hfg : IsComplexGeneratorPair Q ⟨0, by omega⟩ (lam : ℂ) f g)
    {G : Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hG : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) f G)
    (L : ℂ →L[ℝ] ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᵐ ω ∂Q.measure,
      let A := reducedCoefficient ω
      let b := forcedDrift A ⟨0, by omega⟩ lam
      let φ := orbit (horizontalMollify (Calculus.unitMassScaledMollifier d δ)
        (fun v => L (f v))) (reduce ω)
      (∀ t : ℝ≥0, ∀ᵐ γ ∂(Y (0, ω)).map (External.Bass.pathMeasurableEquiv d).symm,
        IntervalIntegrable (fun u : ℝ => External.Bass.generator A b φ (γ u.toNNReal))
          volume 0 (t : ℝ)) ∧
      External.Bass.IsLocalMartingale (External.Bass.compensatedTest A b φ)
        ((Y (0, ω)).map (External.Bass.pathMeasurableEquiv d).symm) := by
  let i : Fin d := ⟨0, by omega⟩
  let rhs := (s : ℂ) • f - (g + (0 - (lam : ℂ)) • complexForceDrift Q i (WithLp.toLp 2 G))
  have hres : unforcedComplexResolvent Q i s hs rhs = f :=
    (isComplexGeneratorPair_iff_resolvent Q i s hs f _).mp (hfg.change_force 0 hG)
  have htests := c17_unforced_resolvent_compact_orbit_tests Q i s hs rhs L hδ
  rw [hres] at htests
  have htests' := ae_of_ae_map Probability.measurable_reduce.aemeasurable htests
  have hΛ : 0 < Λ₀ := lt_of_lt_of_le zero_lt_one Q.ellipticity_parameter
  filter_upwards [Q.regular, htests',
    s5_gmp_textbook_at_every_start hd Q lam h0 h1 Y hY]
    with ω hω htestsω hP
  obtain ⟨ψ, hψ, hlocal⟩ := htestsω
  have hφ : ContDiff ℝ 2 (orbit (horizontalMollify
      (Calculus.unitMassScaledMollifier d δ) (fun v => L (f v))) (reduce ω)) := by
    rw [contDiff_iff_contDiffAt]
    intro x
    obtain ⟨n, hn⟩ := (hlocal x).exists
    exact ((contDiff_two_of_top (hψ n).1).contDiffAt).congr_of_eventuallyEq hn.1.symm
  obtain ⟨hA, _, ⟨Ma, hAb⟩, _, hbm, ⟨Mb, hbb⟩⟩ := reduced_svHypotheses hΛ hω i lam
  have htext : SolvesMartingaleProblem (External.Draft.svGenerator (reducedCoefficient ω)
      (forcedDrift (reducedCoefficient ω) i lam)) (0 : Vec d) (Y (0, ω)) := hP 0
  letI : MeasurableSpace (Vec d) := MeasurableSpace.pi
  letI : MeasurableSpace (Mat d) := EinsteinRelation.instMeasurableSpaceMat d
  have hsource := External.Bass.solves_of_frozen (d := d)
    (a := reducedCoefficient ω) (b := forcedDrift (reducedCoefficient ω) i lam)
    htext hA.measurable hbm hAb hbb
  exact hsource.2.2 _ hφ


/-- Exponential coordinate maxima are integrable for the supplied GMP law. -/
theorem s5_gmp_exp_coordinate_max_integrable
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1) (Y : QuenchedPathLaws d)
    (hY : IsGMPReducedKernel hd Q.ellipticity_parameter Q lam h0 h1 Y)
    (j : Fin d)
    (a : ℝ) (T : ℝ≥0) :
    ∀ᵐ ω ∂Q.measure, Integrable (fun γ : Path d => Real.exp (a *
      sSup ((fun t : ℝ≥0 => |(γ t) j - (0 : Vec d) j|) '' Set.Icc 0 T))) (Y (0, ω)) := by
  have hΛ : 0 < Λ₀ := lt_of_lt_of_le zero_lt_one Q.ellipticity_parameter
  let i := firstCoordinateIndex hd
  obtain ⟨Y₀, _, hY₀⟩ := foundation_reduced_textbook_kernel hΛ i 0
  filter_upwards [Q.regular, s5_gmp_textbook_at_every_start hd Q lam h0 h1 Y hY]
    with ω hω hYtext
  have h₀ := hY₀ ω hω
  have hZ := u3_reduced_force_density_memLp_two (by omega) hΛ hω i h₀ lam T
  have htilt := u3_reduced_force_finite_horizon_law (by omega) hΛ hω i h₀ lam T (hYtext 0)
  let M : Path d → ℝ := fun γ =>
    sSup ((fun t : ℝ≥0 => |(γ t) j - (0 : Vec d) j|) '' Set.Icc 0 T)
  let U : Path d → ℝ := fun γ => Real.exp (a * M γ)
  let Z : Path d → ℝ := fun γ => Real.exp
    (lam * ((γ T) i - (0 : Vec d) i) - ∫ u in Set.Ioc (0 : ℝ) (T : ℝ),
      (lam * forcedDrift (reducedCoefficient ω) i 0 (γ u.toNNReal) i +
        (lam ^ 2 / 2) * reducedCoefficient ω (γ u.toNNReal) i i))
  let R := (Y₀ (0, ω)).withDensity (fun γ => ENNReal.ofReal (Z γ))
  change MemLp Z 2 (Y₀ (0, ω)) at hZ
  have hMm : Measurable M := (c16_continuous_coordinate_max j (0 : Vec d) T).measurable
  have hUm : Measurable U := Real.measurable_exp.comp (measurable_const.mul hMm)
  have hU : MemLp U 2 (Y₀ (0, ω)) := by
    apply (memLp_two_iff_integrable_sq hUm.aestronglyMeasurable).2
    have h₀j : SolvesMartingaleProblem (External.Draft.svGenerator (reducedCoefficient ω)
        (forcedDrift (reducedCoefficient ω) j 0)) 0 (Y₀ (0, ω)) := by
      have he : forcedDrift (reducedCoefficient ω) j 0 =
          forcedDrift (reducedCoefficient ω) i 0 := by
        funext x k
        simp [forcedDrift]
      rw [he]
      exact h₀
    have hi := c16_reduced_textbook_exp_coordinate_max_integrable (by omega) hΛ hω j h₀j (2 * a) T
    convert hi using 1
    funext γ
    change (Real.exp (a * M γ)) ^ 2 = Real.exp (2 * a * M γ)
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hmul : Integrable (fun γ => Z γ * U γ) (Y₀ (0, ω)) := hZ.integrable_mul hU
  have hR : Integrable U R := by
    apply (integrable_withDensity_iff_integrable_smul₀' hZ.aemeasurable.ennreal_ofReal
      (ae_of_all _ fun γ => ENNReal.ofReal_lt_top)).2
    convert hmul using 1
    funext γ
    simp only [ENNReal.toReal_ofReal (show 0 ≤ Z γ from (Real.exp_pos _).le), smul_eq_mul]
  have heq : Measure.map M (Y (0, ω)) = Measure.map M R := by
    ext S hS
    rw [Measure.map_apply hMm hS, Measure.map_apply hMm hS,
      withDensity_apply _ (hS.preimage hMm)]
    exact htilt _ ((u3_coordinate_max_measurable_past j T) hS)
  have hmap : Integrable (fun z : ℝ => Real.exp (a * z)) (Measure.map M R) :=
    (integrable_map_measure (Real.measurable_exp.comp (measurable_const.mul measurable_id)).aestronglyMeasurable
      hMm.aemeasurable).2 hR
  rw [← heq] at hmap
  exact hmap.comp_measurable hMm



/-- Exponential sums of coordinate maxima are integrable under the GMP law. -/
theorem s5_gmp_exp_sum_coordinate_max_integrable
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1) (Y : QuenchedPathLaws d)
    (hY : IsGMPReducedKernel hd Q.ellipticity_parameter Q lam h0 h1 Y)
    (a : ℝ) (T : ℝ≥0) :
    ∀ᵐ ω ∂Q.measure, Integrable (fun γ : Path d => Real.exp (∑ j : Fin d,
      a * sSup ((fun t : ℝ≥0 => |(γ t) j - (0 : Vec d) j|) '' Set.Icc 0 T)))
      (Y (0, ω)) := by
  let M : Fin d → Path d → ℝ := fun j γ =>
    sSup ((fun t : ℝ≥0 => |(γ t) j - (0 : Vec d) j|) '' Set.Icc 0 T)
  have hM (j : Fin d) : Measurable (M j) :=
    (c16_continuous_coordinate_max j (0 : Vec d) T).measurable
  have hm : Measurable (fun γ : Path d => Real.exp (∑ j : Fin d, a * M j γ)) :=
    Real.measurable_exp.comp (Finset.measurable_sum _ fun j _ => measurable_const.mul (hM j))
  have heach := fun j : Fin d => s5_gmp_exp_coordinate_max_integrable hd Q lam h0 h1 Y hY j ((d : ℝ) * a) T
  filter_upwards [ae_all_iff.mpr heach] with ω hω
  have hsum : Integrable (fun γ : Path d => ∑ j : Fin d,
      Real.exp (((d : ℝ) * a) * M j γ)) (Y (0, ω)) :=
    integrable_finset_sum _ fun j _ => hω j
  refine hsum.mono' hm.aestronglyMeasurable (Filter.Eventually.of_forall fun γ => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  obtain ⟨j, hj, hmax⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin d))
    (fun j => a * M j γ) ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  have hs : (∑ k : Fin d, a * M k γ) ≤ (d : ℝ) * (a * M j γ) := by
    calc
      _ ≤ ∑ _k : Fin d, a * M j γ := Finset.sum_le_sum fun k hk => hmax k hk
      _ = _ := by simp
  calc
    Real.exp (∑ k : Fin d, a * M k γ) ≤ Real.exp (((d : ℝ) * a) * M j γ) := by
      apply Real.exp_le_exp.mpr
      nlinarith [hs]
    _ ≤ ∑ k : Fin d, Real.exp (((d : ℝ) * a) * M k γ) :=
      Finset.single_le_sum (f := fun k : Fin d => Real.exp (((d : ℝ) * a) * M k γ))
        (fun k _ => (Real.exp_pos _).le) hj


/-- Compact mollified orbits have an integrable finite-horizon bound. -/
theorem s5_gmp_mollified_orbit_integrable_horizon_bound
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1) (Y : QuenchedPathLaws d)
    (hY : IsGMPReducedKernel hd Q.ellipticity_parameter Q lam h0 h1 Y)
    (ζ : Vec d → ℝ) (hζ : Continuous ζ) (hc : HasCompactSupport ζ)
    (a : FieldPair d → ℝ) (ham : Measurable a) (ha : MemLp a 2 (reducedLaw Q))
    (T : ℝ≥0) :
    ∀ᵐ ω ∂Q.measure, ∃ H : Path d → ℝ, Integrable H (Y (0, ω)) ∧
      ∀ γ : Path d, ∀ t : ℝ≥0, t ≤ T →
        |horizontalMollify ζ a (translate (γ t) (reduce ω))| ≤ H γ := by
  obtain ⟨C, hC, hζb⟩ := u3_compact_kernel_exponential_weight_bound ζ hζ hc
  have hiw : ∀ᵐ ω ∂Q.measure, Integrable (fun z : Vec d =>
      (∏ j : Fin d, Real.exp (-|z j|)) * |a (translate z (reduce ω))|) volume := by
    exact (Probability.measurableEmbedding_reduce d).ae_map_iff.mp
      (u3_stationary_exponential_weighted_orbit_integrable Q a ham ha)
  filter_upwards [hiw, s5_gmp_exp_sum_coordinate_max_integrable hd Q lam h0 h1 Y hY 1 T] with ω hi hs
  let J : ℝ := ∫ z : Vec d, (∏ j : Fin d, Real.exp (-|z j|)) *
    |a (translate z (reduce ω))|
  have hJ : 0 ≤ J := by
    apply integral_nonneg
    intro z
    positivity
  let D : ℝ := C * J
  have hD : 0 ≤ D := mul_nonneg hC hJ
  let H : Path d → ℝ := fun γ => D * Real.exp (∑ j : Fin d,
    sSup ((fun t : ℝ≥0 => |(γ t) j - (0 : Vec d) j|) '' Set.Icc 0 T))
  have hH : Integrable H (Y (0, ω)) := by
    simpa only [H, one_mul] using hs.const_mul D
  refine ⟨H, hH, ?_⟩
  intro γ t ht
  have hb := u3_horizontalMollify_weighted_orbit_bound ζ hζ.measurable a ham
    (reduce ω) C hC hζb hi (γ t)
  have hm := u3_exp_coordinate_sum_le_horizon_max 1 (by norm_num) T t ht γ
  simp only [one_mul] at hm
  calc
    |horizontalMollify ζ a (translate (γ t) (reduce ω))| ≤
        D * Real.exp (∑ j : Fin d, |(γ t) j|) := by
      simpa only [D, J, mul_comm, mul_left_comm, mul_assoc] using hb
    _ ≤ H γ := mul_le_mul_of_nonneg_left hm hD



/-- The literal occupation estimate gives joint finite-horizon integrability. -/
theorem s5_gmp_joint_occupation_integrable_of_l2_estimate
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (mu : ℝ) (h0 : 0 ≤ mu) (h1 : mu ≤ 1) (P : QuenchedPathLaws d)
    (hP : IsGMPReducedKernel hd Q.ellipticity_parameter Q mu h0 h1 P)
    (T : ℝ≥0)
    (hocc : ∀ (v : FieldPair d → ℝ), Measurable v → MemLp v 2 (reducedLaw Q) →
      (∫⁻ t in Set.Ioc (0 : ℝ) (T : ℝ),
        ∫⁻ ω, ∫⁻ γ : Path d, ‖v (translate (γ t.toNNReal) (reduce ω))‖ₑ
          ∂P (0, ω) ∂Q.measure) ≤
        (ENNReal.ofReal (Real.exp (mu ^ 2 * (Real.exp (2 * Λ₀) * Λ₀) * (T : ℝ))) ^
          (1 / 2 : ℝ) * eLpNorm v 2 (reducedLaw Q)) *
            (volume : Measure ℝ) (Set.Ioc 0 (T : ℝ)))
    (r : FieldPair d → ℝ) (hm : Measurable r) (hr : MemLp r 2 (reducedLaw Q)) :
    ∃ K : Kernel (FieldPair d) (Path d), IsMarkovKernel K ∧
      (∀ᵐ ω ∂Q.measure, P (0, ω) = K ω) ∧
      Integrable (fun p : ℝ × (FieldPair d × Path d) =>
        |r (translate (p.2.2 p.1.toNNReal) (reduce p.2.1))|)
        ((volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ))).prod (Q.measure ⊗ₘ K)) := by
  obtain ⟨K, hmarkov, hK⟩ := s5_gmp_origin_markov_version hd Q mu h0 h1 P hP
  let : IsMarkovKernel K := hmarkov
  have hK' : ∀ᵐ ω ∂Q.measure, P (0, ω) = K ω := hK.mono fun _ h => h.symm
  refine ⟨K, hmarkov, hK', ?_⟩
  let E : ℝ × (FieldPair d × Path d) → FieldPair d := fun p =>
    translate (p.2.2 p.1.toNNReal) (reduce p.2.1)
  have hE : Measurable E := by
    exact (Probability.continuous_translate.comp
      ((continuous_eval.comp ((continuous_snd.comp continuous_snd).prodMk
        (continuous_real_toNNReal.comp continuous_fst))).prodMk
        (Probability.continuous_reduce.comp (continuous_fst.comp continuous_snd)))).measurable
  refine ⟨(continuous_abs.measurable.comp (hm.comp hE)).aestronglyMeasurable, ?_⟩
  apply hasFiniteIntegral_iff_enorm.mpr
  have hC : ENNReal.ofReal (Real.exp
      (mu ^ 2 * (Real.exp (2 * Λ₀) * Λ₀) * (T : ℝ))) ^ (1 / 2 : ℝ) ≠ ∞ :=
    ne_of_lt (ENNReal.rpow_lt_top_of_nonneg (by norm_num) ENNReal.ofReal_lt_top.ne)
  have hfin : (∫⁻ t in Set.Ioc (0 : ℝ) (T : ℝ),
        ∫⁻ ω, ∫⁻ γ : Path d, ‖r (translate (γ t.toNNReal) (reduce ω))‖ₑ
          ∂P (0, ω) ∂Q.measure) < ∞ := by
    refine lt_of_le_of_lt (hocc r hm hr) ?_
    exact ENNReal.mul_lt_top (ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr hC)
      (lt_top_iff_ne_top.mpr hr.eLpNorm_ne_top)) measure_Ioc_lt_top
  rw [← u3_supplied_force_finite_time_joint_occupation Q P K hK' T r hm] at hfin
  simpa only [Real.enorm_eq_ofReal_abs, abs_abs] using hfin

/-- Almost-everywhere equal observables agree along almost every GMP path. -/
theorem s5_gmp_ae_eq_path_occupation
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1) (Y : QuenchedPathLaws d)
    (hY : IsGMPReducedKernel hd Q.ellipticity_parameter Q lam h0 h1 Y)
    (f g : FieldPair d → ℝ) (hfg : f =ᵐ[reducedLaw Q] g) :
    ∀ᵐ ω ∂Q.measure, ∀ᵐ γ ∂Y (0, ω),
      ∀ᵐ t ∂volume.restrict (Set.Ioi (0 : ℝ)),
        f (translate (γ t.toNNReal) (reduce ω)) =
          g (translate (γ t.toNNReal) (reduce ω)) := by
  obtain ⟨N, hsub, hNm, hN⟩ := exists_measurable_superset_of_null (ae_iff.mp hfg)
  filter_upwards [s5_gmp_environment_null_occupation hd Q lam h0 h1 Y hY N hNm hN]
    with ω hω
  filter_upwards [hω] with γ hγ
  filter_upwards [hγ] with t ht
  by_contra hne
  exact ht (hsub hne)


/-- The actual GMP graph generator has integrable path occupation under the literal L² estimate. -/
theorem s5_gmp_graph_generator_path_occupation_integrable_of_l2_estimate
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam s : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1) (hs : 0 < s)
    (Y : QuenchedPathLaws d)
    (hY : IsGMPReducedKernel hd Q.ellipticity_parameter Q lam h0 h1 Y)
    (f g : Lp ℂ 2 (reducedLaw Q))
    (hfg : IsComplexGeneratorPair Q ⟨0, by omega⟩ (lam : ℂ) f g)
    {G : Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hG : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) f G)
    (L : ℂ →L[ℝ] ℝ) (T : ℝ≥0) (n : ℕ)
    (hocc : ∀ (v : FieldPair d → ℝ), Measurable v → MemLp v 2 (reducedLaw Q) →
      (∫⁻ t in Set.Ioc (0 : ℝ) (T : ℝ),
        ∫⁻ ω, ∫⁻ γ : Path d, ‖v (translate (γ t.toNNReal) (reduce ω))‖ₑ
          ∂Y (0, ω) ∂Q.measure) ≤
        (ENNReal.ofReal (Real.exp (lam ^ 2 * (Real.exp (2 * Λ₀) * Λ₀) * (T : ℝ))) ^
          (1 / 2 : ℝ) * eLpNorm v 2 (reducedLaw Q)) *
            (volume : Measure ℝ) (Set.Ioc 0 (T : ℝ))) :
    ∀ᵐ ω ∂Q.measure, ∀ᵐ γ ∂Y (0, ω),
      IntegrableOn (fun t : ℝ => |envGenerator hd lam (horizontalMollify
        (Calculus.unitMassScaledMollifier d (Entropy.scaleSeq n)) (fun v => L (f v)))
          (translate (γ t.toNNReal) (reduce ω))|) (Set.Ioc 0 (T : ℝ)) volume := by
  obtain ⟨a, ham, ha, hae⟩ :=
    u3_signed_graph_mollified_generator_representatives hd Q lam s hs f g hfg hG L
  obtain ⟨K, hmarkov, hK, hi⟩ :=
    s5_gmp_joint_occupation_integrable_of_l2_estimate
      hd Q lam h0 h1 Y hY T hocc (a n) (ham n) (ha n)
  let : IsMarkovKernel K := hmarkov
  have hsections := Measure.ae_ae_of_ae_compProd hi.prod_left_ae
  have heq := s5_gmp_ae_eq_path_occupation hd Q lam h0 h1 Y hY (a n) _ (hae n)
  filter_upwards [hK, hsections, heq] with ω hKω hsectionω heqω
  rw [← hKω] at hsectionω
  filter_upwards [hsectionω, heqω] with γ hsectionγ heqγ
  have ht := ae_restrict_of_ae_restrict_of_subset
    (fun t (ht : t ∈ Set.Ioc (0 : ℝ) (T : ℝ)) => ht.1) heqγ
  apply hsectionγ.congr
  filter_upwards [ht] with t ht
  exact congrArg abs ht


/-- The actual GMP graph generator has integrable quenched occupation under the literal L² estimate. -/
theorem s5_gmp_graph_generator_quenched_occupation_integrable_of_l2_estimate
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam s : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1) (hs : 0 < s)
    (Y : QuenchedPathLaws d)
    (hY : IsGMPReducedKernel hd Q.ellipticity_parameter Q lam h0 h1 Y)
    (f g : Lp ℂ 2 (reducedLaw Q))
    (hfg : IsComplexGeneratorPair Q ⟨0, by omega⟩ (lam : ℂ) f g)
    {G : Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hG : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) f G)
    (L : ℂ →L[ℝ] ℝ) (T : ℝ≥0) (n : ℕ)
    (hocc : ∀ (v : FieldPair d → ℝ), Measurable v → MemLp v 2 (reducedLaw Q) →
      (∫⁻ t in Set.Ioc (0 : ℝ) (T : ℝ),
        ∫⁻ ω, ∫⁻ γ : Path d, ‖v (translate (γ t.toNNReal) (reduce ω))‖ₑ
          ∂Y (0, ω) ∂Q.measure) ≤
        (ENNReal.ofReal (Real.exp (lam ^ 2 * (Real.exp (2 * Λ₀) * Λ₀) * (T : ℝ))) ^
          (1 / 2 : ℝ) * eLpNorm v 2 (reducedLaw Q)) *
            (volume : Measure ℝ) (Set.Ioc 0 (T : ℝ))) :
    ∀ᵐ ω ∂Q.measure, Integrable (fun γ : Path d =>
      ∫ t in Set.Ioc 0 (T : ℝ), |envGenerator hd lam (horizontalMollify
        (Calculus.unitMassScaledMollifier d (Entropy.scaleSeq n)) (fun v => L (f v)))
          (translate (γ t.toNNReal) (reduce ω))|) (Y (0, ω)) := by
  obtain ⟨a, ham, ha, hae⟩ :=
    u3_signed_graph_mollified_generator_representatives hd Q lam s hs f g hfg hG L
  obtain ⟨K, hmarkov, hK, hi⟩ :=
    s5_gmp_joint_occupation_integrable_of_l2_estimate
      hd Q lam h0 h1 Y hY T hocc (a n) (ham n) (ha n)
  let : IsMarkovKernel K := hmarkov
  have hn := hi.integral_norm_prod_right
  have hn' : Integrable (fun p : FieldPair d × Path d =>
      ∫ t in Set.Ioc 0 (T : ℝ), |a n (translate (p.2 t.toNNReal) (reduce p.1))|)
      (Q.measure ⊗ₘ K) := by
    simpa only [Real.norm_eq_abs, abs_abs] using hn
  have hsections := (Measure.integrable_compProd_iff hn'.aestronglyMeasurable).mp hn'
  have heq := s5_gmp_ae_eq_path_occupation hd Q lam h0 h1 Y hY (a n) _ (hae n)
  filter_upwards [hK, hsections.1, heq] with ω hKω hsectionω heqω
  rw [← hKω] at hsectionω
  apply hsectionω.congr
  filter_upwards [heqω] with γ heqγ
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae_restrict_of_subset (fun _ ht => ht.1) heqγ] with t ht
  exact congrArg abs ht


/-- The mollified graph orbit is a true martingale under the occupation L² estimate. -/
theorem s5_gmp_graph_mollified_orbit_martingale_of_l2_estimate
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam s : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1) (hs : 0 < s)
    (Y : QuenchedPathLaws d)
    (hY : IsGMPReducedKernel hd Q.ellipticity_parameter Q lam h0 h1 Y)
    (f g : Lp ℂ 2 (reducedLaw Q))
    (hfg : IsComplexGeneratorPair Q ⟨0, by omega⟩ (lam : ℂ) f g)
    {G : Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hG : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) f G)
    (L : ℂ →L[ℝ] ℝ) (n : ℕ)
    (hocc : ∀ (T : ℝ≥0) (v : FieldPair d → ℝ), Measurable v → MemLp v 2 (reducedLaw Q) →
      (∫⁻ t in Set.Ioc (0 : ℝ) (T : ℝ),
        ∫⁻ ω, ∫⁻ γ : Path d, ‖v (translate (γ t.toNNReal) (reduce ω))‖ₑ
          ∂Y (0, ω) ∂Q.measure) ≤
        (ENNReal.ofReal (Real.exp (lam ^ 2 * (Real.exp (2 * Λ₀) * Λ₀) * (T : ℝ))) ^
          (1 / 2 : ℝ) * eLpNorm v 2 (reducedLaw Q)) *
            (volume : Measure ℝ) (Set.Ioc 0 (T : ℝ))) :
    ∀ᵐ ω ∂Q.measure,
      Martingale (External.Bass.compensatedTest (reducedCoefficient ω)
        (forcedDrift (reducedCoefficient ω) ⟨0, by omega⟩ lam)
        (orbit (horizontalMollify (Calculus.unitMassScaledMollifier d (Entropy.scaleSeq n))
          (fun v => L (f v))) (reduce ω))) (External.Bass.filtration d)
        ((Y (0, ω)).map (External.Bass.pathMeasurableEquiv d).symm) := by
  let V : FieldPair d → ℝ := fun v => L (f v)
  let M := horizontalMollify (Calculus.unitMassScaledMollifier d (Entropy.scaleSeq n)) V
  have hVm : Measurable V := L.continuous.measurable.comp (Lp.stronglyMeasurable f).measurable
  have hV : MemLp V 2 (reducedLaw Q) := L.comp_memLp' (Lp.memLp f)
  have hb := fun N : ℕ => s5_gmp_mollified_orbit_integrable_horizon_bound
    hd Q lam h0 h1 Y hY _
    (Entropy.contDiff_unitMassScaledMollifier _).continuous
    (Entropy.hasCompactSupport_unitMassScaledMollifier (Entropy.scaleSeq_pos n))
    V hVm hV (N : ℝ≥0)
  have ho := fun N : ℕ => s5_gmp_graph_generator_quenched_occupation_integrable_of_l2_estimate
    hd Q lam s h0 h1 hs Y hY f g hfg hG L (N : ℝ≥0) n (hocc (N : ℝ≥0))
  have hp := fun N : ℕ => s5_gmp_graph_generator_path_occupation_integrable_of_l2_estimate
    hd Q lam s h0 h1 hs Y hY f g hfg hG L (N : ℝ≥0) n (hocc (N : ℝ≥0))
  filter_upwards [Q.regular, s5_gmp_textbook_at_every_start hd Q lam h0 h1 Y hY,
    ae_all_iff.mpr hb, ae_all_iff.mpr ho, ae_all_iff.mpr hp,
    s5_gmp_graph_mollified_orbit_local_martingale
      hd Q lam h0 h1 s hs Y hY f g hfg hG L (Entropy.scaleSeq_pos n)]
    with ω hω hP hbω hoω hpω hlocal
  let : IsProbabilityMeasure (Y (0, ω)) := (hP 0).1
  let e := External.Bass.pathMeasurableEquiv d
  let P := (Y (0, ω)).map e.symm
  let : IsProbabilityMeasure P := inferInstance
  have hsymmetric : ∀ x j k, (reduce ω).1 x j k = (reduce ω).1 x k j := by
    intro x j k
    have he := congrArg (fun A : Mat d => A j k) (reducedCoefficient_symm hω x)
    exact he.symm
  have he (x : Vec d) : envGenerator hd lam M (translate x (reduce ω)) =
      External.Bass.generator (reducedCoefficient ω)
        (forcedDrift (reducedCoefficient ω) ⟨0, by omega⟩ lam) (orbit M (reduce ω)) x := by
    exact u3_signed_envGenerator_eq_svGenerator hd (reduce ω) M lam hsymmetric x
  apply u3_compensated_local_martingale_of_natural_occupation_bound hlocal.2
  · intro N
    obtain ⟨H, hH, hbH⟩ := hbω N
    refine ⟨H ∘ e, ?_, ?_⟩
    · apply (integrable_map_equiv e.symm (H ∘ e)).2
      simpa [Function.comp_def] using hH
    · exact Filter.Eventually.of_forall fun γ t ht => hbH (e γ) t ht
  · intro N
    apply (integrable_map_equiv e.symm _).2
    change Integrable (fun γ : Path d => ∫ u in Set.Ioc (0 : ℝ) (N : ℝ),
      |External.Bass.generator (reducedCoefficient ω)
        (forcedDrift (reducedCoefficient ω) ⟨0, by omega⟩ lam)
        (orbit M (reduce ω)) (γ u.toNNReal)|) (Y (0, ω))
    simpa only [← he, NNReal.coe_natCast] using hoω N
  · intro N
    have hmap : ∀ᵐ γ ∂P.map e, IntegrableOn
        (fun u : ℝ => |External.Bass.generator (reducedCoefficient ω)
          (forcedDrift (reducedCoefficient ω) ⟨0, by omega⟩ lam)
          (orbit M (reduce ω)) (e.symm γ u.toNNReal)|) (Set.Ioc 0 (N : ℝ)) volume := by
      simpa only [P, e, External.Bass.map_pathMeasurableEquiv_symm_roundtrip,
        External.Bass.pathMeasurableEquiv_symm_apply, ← he,
        NNReal.coe_natCast] using hpω N
    have hh := ae_of_ae_map e.measurable.aemeasurable hmap
    simpa only [e, MeasurableEquiv.symm_apply_apply] using hh


/-- The graph-generator compensator is integrable under the occupation L² estimate. -/
theorem s5_gmp_graph_generator_compensator_integrable_of_l2_estimate
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam s : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1) (hs : 0 < s)
    (Y : QuenchedPathLaws d)
    (hY : IsGMPReducedKernel hd Q.ellipticity_parameter Q lam h0 h1 Y)
    (f g : Lp ℂ 2 (reducedLaw Q))
    (hfg : IsComplexGeneratorPair Q ⟨0, by omega⟩ (lam : ℂ) f g)
    {G : Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hG : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) f G)
    (L : ℂ →L[ℝ] ℝ) (T : ℝ≥0) (n : ℕ)
    (hocc : ∀ (v : FieldPair d → ℝ), Measurable v → MemLp v 2 (reducedLaw Q) →
      (∫⁻ t in Set.Ioc (0 : ℝ) (T : ℝ),
        ∫⁻ ω, ∫⁻ γ : Path d, ‖v (translate (γ t.toNNReal) (reduce ω))‖ₑ
          ∂Y (0, ω) ∂Q.measure) ≤
        (ENNReal.ofReal (Real.exp (lam ^ 2 * (Real.exp (2 * Λ₀) * Λ₀) * (T : ℝ))) ^
          (1 / 2 : ℝ) * eLpNorm v 2 (reducedLaw Q)) *
            (volume : Measure ℝ) (Set.Ioc 0 (T : ℝ))) :
    ∀ᵐ ω ∂Q.measure, Integrable (fun γ : Path d =>
      ∫ t in Set.Ioc 0 (T : ℝ), envGenerator hd lam (horizontalMollify
        (Calculus.unitMassScaledMollifier d (Entropy.scaleSeq n)) (fun v => L (f v)))
          (translate (γ t.toNNReal) (reduce ω))) (Y (0, ω)) := by
  obtain ⟨a, ham, ha, hae⟩ :=
    u3_signed_graph_mollified_generator_representatives hd Q lam s hs f g hfg hG L
  obtain ⟨K, hmarkov, hK, hi⟩ :=
    s5_gmp_joint_occupation_integrable_of_l2_estimate
      hd Q lam h0 h1 Y hY T hocc (a n) (ham n) (ha n)
  let : IsMarkovKernel K := hmarkov
  let E : ℝ × (FieldPair d × Path d) → FieldPair d := fun p =>
    translate (p.2.2 p.1.toNNReal) (reduce p.2.1)
  have hE : Measurable E := by
    exact (Probability.continuous_translate.comp
      ((continuous_eval.comp ((continuous_snd.comp continuous_snd).prodMk
        (continuous_real_toNNReal.comp continuous_fst))).prodMk
        (Probability.continuous_reduce.comp (continuous_fst.comp continuous_snd)))).measurable
  have hj : Integrable (fun p : ℝ × (FieldPair d × Path d) => a n (E p))
      ((volume.restrict (Set.Ioc 0 (T : ℝ))).prod (Q.measure ⊗ₘ K)) := by
    apply hi.mono' ((ham n).comp hE).aestronglyMeasurable
    filter_upwards [] with p
    simp only [Real.norm_eq_abs, Function.comp_apply, E, le_refl]
  have hn := hj.integral_prod_right
  have hsections := (Measure.integrable_compProd_iff hn.aestronglyMeasurable).mp hn
  have heq := s5_gmp_ae_eq_path_occupation hd Q lam h0 h1 Y hY (a n) _ (hae n)
  filter_upwards [hK, hsections.1, heq] with ω hKω hsectionω heqω
  rw [← hKω] at hsectionω
  apply hsectionω.congr
  filter_upwards [heqω] with γ heqγ
  apply integral_congr_ae
  exact ae_restrict_of_ae_restrict_of_subset (fun _ ht => ht.1) heqγ


/-- Mollified graph orbits satisfy Dynkin’s formula under the occupation L² estimate. -/
theorem s5_gmp_graph_mollified_dynkin_of_l2_estimate
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam s : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1) (hs : 0 < s)
    (Y : QuenchedPathLaws d)
    (hY : IsGMPReducedKernel hd Q.ellipticity_parameter Q lam h0 h1 Y)
    (f g : Lp ℂ 2 (reducedLaw Q))
    (hfg : IsComplexGeneratorPair Q ⟨0, by omega⟩ (lam : ℂ) f g)
    {G : Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hG : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) f G)
    (L : ℂ →L[ℝ] ℝ) (n : ℕ) (T : ℝ≥0)
    (hocc : ∀ (U : ℝ≥0) (v : FieldPair d → ℝ), Measurable v → MemLp v 2 (reducedLaw Q) →
      (∫⁻ t in Set.Ioc (0 : ℝ) (U : ℝ),
        ∫⁻ ω, ∫⁻ γ : Path d, ‖v (translate (γ t.toNNReal) (reduce ω))‖ₑ
          ∂Y (0, ω) ∂Q.measure) ≤
        (ENNReal.ofReal (Real.exp (lam ^ 2 * (Real.exp (2 * Λ₀) * Λ₀) * (U : ℝ))) ^
          (1 / 2 : ℝ) * eLpNorm v 2 (reducedLaw Q)) *
            (volume : Measure ℝ) (Set.Ioc 0 (U : ℝ))) :
    ∀ᵐ ω ∂Q.measure,
      (∫ γ : Path d, horizontalMollify
        (Calculus.unitMassScaledMollifier d (Entropy.scaleSeq n)) (fun v => L (f v))
          (translate (γ T) (reduce ω)) ∂Y (0, ω)) -
      horizontalMollify (Calculus.unitMassScaledMollifier d (Entropy.scaleSeq n))
        (fun v => L (f v)) (reduce ω) =
      ∫ γ : Path d, (∫ u in Set.Ioc (0 : ℝ) (T : ℝ),
        envGenerator hd lam (horizontalMollify
          (Calculus.unitMassScaledMollifier d (Entropy.scaleSeq n)) (fun v => L (f v)))
          (translate (γ u.toNNReal) (reduce ω))) ∂Y (0, ω) := by
  let V : FieldPair d → ℝ := fun v => L (f v)
  let M := horizontalMollify (Calculus.unitMassScaledMollifier d (Entropy.scaleSeq n)) V
  have hVm : Measurable V := L.continuous.measurable.comp (Lp.stronglyMeasurable f).measurable
  have hV : MemLp V 2 (reducedLaw Q) := L.comp_memLp' (Lp.memLp f)
  have hMm : Measurable M := measurable_horizontalMollify _
    (Entropy.contDiff_unitMassScaledMollifier _).continuous.measurable hVm
  have hM : MemLp M 2 (reducedLaw Q) :=
    Entropy.memLp_horizontalMollify_unitMass (reducedLaw_stationary Q)
      (Entropy.scaleSeq_pos n) ENNReal.ofNat_ne_top hVm hV
  have hb := s5_gmp_mollified_orbit_integrable_horizon_bound hd Q lam h0 h1 Y hY
    _ (Entropy.contDiff_unitMassScaledMollifier _).continuous
    (Entropy.hasCompactSupport_unitMassScaledMollifier (Entropy.scaleSeq_pos n))
    V hVm hV T
  filter_upwards [Q.regular, s5_gmp_textbook_at_every_start hd Q lam h0 h1 Y hY,
    s5_gmp_graph_mollified_orbit_martingale_of_l2_estimate hd Q lam s h0 h1 hs Y hY f g hfg hG L n hocc,
    hb, s5_gmp_graph_generator_compensator_integrable_of_l2_estimate
      hd Q lam s h0 h1 hs Y hY f g hfg hG L T n (hocc T)]
    with ω hω htext hmart hbω hc
  let : IsProbabilityMeasure (Y (0, ω)) := (htext 0).1
  obtain ⟨H, hH, hbH⟩ := hbω
  have hobs (t : ℝ≥0) : Measurable (fun γ : Path d => M (translate (γ t) (reduce ω))) := by
    apply hMm.comp
    exact (Probability.continuous_translate.comp
      ((continuous_eval.comp (continuous_id.prodMk continuous_const)).prodMk continuous_const)).measurable
  have ht : Integrable (fun γ : Path d => M (translate (γ T) (reduce ω))) (Y (0, ω)) := by
    apply hH.mono' (hobs T).aestronglyMeasurable
    filter_upwards [] with γ
    simpa only [Real.norm_eq_abs] using hbH γ T (le_refl T)
  have hzero : Integrable (fun γ : Path d => M (translate (γ 0) (reduce ω))) (Y (0, ω)) := by
    apply hH.mono' (hobs 0).aestronglyMeasurable
    filter_upwards [] with γ
    simpa only [Real.norm_eq_abs] using hbH γ 0 bot_le
  have hsymmetric : ∀ x j k, (reduce ω).1 x j k = (reduce ω).1 x k j := by
    intro x j k
    have he := congrArg (fun A : Mat d => A j k) (reducedCoefficient_symm hω x)
    exact he.symm
  have he (x : Vec d) : envGenerator hd lam M (translate x (reduce ω)) =
      External.Bass.generator (reducedCoefficient ω)
        (forcedDrift (reducedCoefficient ω) ⟨0, by omega⟩ lam) (orbit M (reduce ω)) x := by
    exact u3_signed_envGenerator_eq_svGenerator hd (reduce ω) M lam hsymmetric x
  have hz := hmart.setIntegral_eq (show (0 : ℝ≥0) ≤ T from bot_le) MeasurableSet.univ
  have hz' : (∫ γ : External.Bass.Path d, External.Bass.compensatedTest
      (reducedCoefficient ω) (forcedDrift (reducedCoefficient ω) ⟨0, by omega⟩ lam)
      (orbit M (reduce ω)) T γ ∂(Y (0, ω)).map (External.Bass.pathMeasurableEquiv d).symm) = 0 := by
    simpa [External.Bass.compensatedTest] using hz.symm
  rw [integral_map_equiv] at hz'
  have hz'' : (∫ γ : Path d, M (translate (γ T) (reduce ω)) -
      M (translate (γ 0) (reduce ω)) - (∫ u in Set.Ioc (0 : ℝ) (T : ℝ),
        envGenerator hd lam M (translate (γ u.toNNReal) (reduce ω))) ∂Y (0, ω)) = 0 := by
    have hzinterval : (∫ γ : Path d, M (translate (γ T) (reduce ω)) -
        M (translate (γ 0) (reduce ω)) - (∫ u in (0 : ℝ)..(T : ℝ),
          envGenerator hd lam M (translate (γ u.toNNReal) (reduce ω))) ∂Y (0, ω)) = 0 := by
      simpa only [External.Bass.compensatedTest, External.Bass.pathMeasurableEquiv_symm_apply,
        orbit, ← he] using hz'
    convert hzinterval using 1
    apply integral_congr_ae
    filter_upwards [] with γ
    have hi : (∫ u in (0 : ℝ)..(T : ℝ), envGenerator hd lam M
        (translate (γ u.toNNReal) (reduce ω))) =
        ∫ u in Set.Ioc (0 : ℝ) (T : ℝ), envGenerator hd lam M
          (translate (γ u.toNNReal) (reduce ω)) := intervalIntegral.integral_of_le T.property
    rw [hi]
  have hstart : (∫ γ : Path d, M (translate (γ 0) (reduce ω)) ∂Y (0, ω)) = M (reduce ω) := by
    calc
      _ = ∫ _ : Path d, M (reduce ω) ∂Y (0, ω) := integral_congr_ae
        ((htext 0).2.1.mono fun _ h => by simp only [h, translate_zero])
      _ = M (reduce ω) := by simp
  change (∫ γ : Path d, M (translate (γ T) (reduce ω)) ∂Y (0, ω)) - M (reduce ω) = _
  have hc' : Integrable (fun γ : Path d => ∫ u in Set.Ioc (0 : ℝ) (T : ℝ),
      envGenerator hd lam M (translate (γ u.toNNReal) (reduce ω))) (Y (0, ω)) := hc
  change (∫ γ : Path d, ((fun γ : Path d => M (translate (γ T) (reduce ω))) -
    (fun γ : Path d => M (translate (γ 0) (reduce ω)))) γ -
      (∫ u in Set.Ioc (0 : ℝ) (T : ℝ), envGenerator hd lam M
        (translate (γ u.toNNReal) (reduce ω))) ∂Y (0, ω)) = 0 at hz''
  rw [integral_sub (ht.sub hzero) hc'] at hz''
  simp only [Pi.sub_apply] at hz''
  rw [integral_sub ht hzero, hstart] at hz''
  exact sub_eq_zero.mp hz''


/-- L²-small observations have vanishing annealed endpoint occupation under
    the literal endpoint L² estimate. -/
theorem s5_gmp_endpoint_residual_tendsto_of_l2_estimate
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (mu : ℝ) (h0 : 0 ≤ mu) (h1 : mu ≤ 1) (P : QuenchedPathLaws d)
    (_hP : IsGMPReducedKernel hd Q.ellipticity_parameter Q mu h0 h1 P)
    (t : ℝ≥0)
    (hendpoint : ∀ (v : FieldPair d → ℝ), Measurable v → MemLp v 2 (reducedLaw Q) →
      (∫⁻ ω, ∫⁻ γ : Path d, ‖v (translate (γ t) (reduce ω))‖ₑ
        ∂P (0, ω) ∂Q.measure) ≤
        ENNReal.ofReal (Real.exp (mu ^ 2 * (Real.exp (2 * Λ₀) * Λ₀) * (t : ℝ))) ^
          (1 / 2 : ℝ) * eLpNorm v 2 (reducedLaw Q))
    (r : ℕ → FieldPair d → ℝ) (hm : ∀ n, Measurable (r n))
    (hr : ∀ n, MemLp (r n) 2 (reducedLaw Q))
    (hlim : Filter.Tendsto (fun n => ‖(hr n).toLp (r n)‖) Filter.atTop (𝓝 0)) :
    Filter.Tendsto (fun n => ∫⁻ ω, ∫⁻ γ : Path d,
      ‖r n (translate (γ t) (reduce ω))‖ₑ ∂P (0, ω) ∂Q.measure)
      Filter.atTop (𝓝 0) := by
  let C : ℝ≥0∞ := ENNReal.ofReal (Real.exp
    (mu ^ 2 * (Real.exp (2 * Λ₀) * Λ₀) * (t : ℝ))) ^ (1 / 2 : ℝ)
  have hC : C ≠ ∞ :=
    ne_of_lt (ENNReal.rpow_lt_top_of_nonneg (by norm_num) ENNReal.ofReal_lt_top.ne)
  have hr_lim : Filter.Tendsto (fun n => eLpNorm (r n) 2 (reducedLaw Q))
      Filter.atTop (𝓝 0) := by
    have hh := ENNReal.tendsto_ofReal hlim
    simp only [ENNReal.ofReal_zero] at hh
    apply hh.congr
    intro n
    rw [Lp.norm_def, eLpNorm_congr_ae (hr n).coeFn_toLp,
      ENNReal.ofReal_toReal (hr n).eLpNorm_ne_top]
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds _
    (fun _ => bot_le) (fun n => hendpoint (r n) (hm n) (hr n))
  simpa [C] using ENNReal.Tendsto.const_mul hr_lim (Or.inr hC)


/-- L²-small real observables have a quenched subsequence with vanishing
absolute endpoint expectation under the original supplied law. -/
theorem s5_gmp_endpoint_quenched_subsequence_of_l2_estimate
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1) (Y : QuenchedPathLaws d)
    (hY : IsGMPReducedKernel hd Q.ellipticity_parameter Q lam h0 h1 Y)
    (t : ℝ≥0)
    (hendpoint : ∀ (v : FieldPair d → ℝ), Measurable v → MemLp v 2 (reducedLaw Q) →
      (∫⁻ ω, ∫⁻ γ : Path d, ‖v (translate (γ t) (reduce ω))‖ₑ
        ∂Y (0, ω) ∂Q.measure) ≤
        ENNReal.ofReal (Real.exp (lam ^ 2 * (Real.exp (2 * Λ₀) * Λ₀) * (t : ℝ))) ^
          (1 / 2 : ℝ) * eLpNorm v 2 (reducedLaw Q))
    (r : ℕ → FieldPair d → ℝ)
    (hm : ∀ n, Measurable (r n)) (hr : ∀ n, MemLp (r n) 2 (reducedLaw Q))
    (hlim : Filter.Tendsto (fun n => ‖(hr n).toLp (r n)‖) Filter.atTop (𝓝 0)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∀ᵐ ω ∂Q.measure,
      Filter.Tendsto (fun n => ∫ γ : Path d,
        |r (ns n) (translate (γ t) (reduce ω))| ∂Y (0, ω)) Filter.atTop (𝓝 0) := by
  let : IsProbabilityMeasure Q.measure := Q.probability
  obtain ⟨K, hmarkov, hK⟩ := s5_gmp_origin_markov_version hd Q lam h0 h1 Y hY
  let : IsMarkovKernel K := hmarkov
  have hK' : ∀ᵐ ω ∂Q.measure, Y (0, ω) = K ω := hK.mono fun _ h => h.symm
  let E : FieldPair d × Path d → FieldPair d := fun p =>
    translate (p.2 t) (reduce p.1)
  have hE : Measurable E := by
    exact (Probability.continuous_translate.comp
      ((continuous_eval.comp (continuous_snd.prodMk continuous_const)).prodMk
        (Probability.continuous_reduce.comp continuous_fst))).measurable
  let J (n : ℕ) : ℝ≥0∞ := ∫⁻ p, ‖r n (E p)‖ₑ ∂(Q.measure ⊗ₘ K)
  have hJ : Filter.Tendsto J Filter.atTop (𝓝 0) := by
    have ht := s5_gmp_endpoint_residual_tendsto_of_l2_estimate
      hd Q lam h0 h1 Y hY t hendpoint r hm hr hlim
    apply ht.congr
    intro n
    have hmeas : Measurable (fun p : FieldPair d × Path d => ‖r n (E p)‖ₑ) :=
      ((hm n).comp hE).enorm
    symm
    change (∫⁻ p, ‖r n (E p)‖ₑ ∂(Q.measure ⊗ₘ K)) = _
    rw [Measure.lintegral_compProd hmeas]
    apply lintegral_congr_ae
    filter_upwards [hK'] with ω hω
    simp only [E, hω]
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1
    (hJ.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ≥0∞) < 1)))
  let R (n : ℕ) := r (n + N)
  let F (n : ℕ) : FieldPair d × Path d → ℝ := fun p => |R n (E p)|
  have hF (n : ℕ) : Measurable (F n) :=
    continuous_abs.measurable.comp ((hm (n + N)).comp hE)
  have hJfin (n : ℕ) : J (n + N) < ∞ :=
    (hN (n + N) (Nat.le_add_left N n)).trans_le le_top
  have hi (n : ℕ) : Integrable (F n) (Q.measure ⊗ₘ K) := by
    refine ⟨(hF n).aestronglyMeasurable, ?_⟩
    apply hasFiniteIntegral_iff_enorm.mpr
    simpa only [F, R, Real.enorm_eq_ofReal_abs, abs_abs, J] using hJfin n
  let A (n : ℕ) (ω : FieldPair d) := ∫ γ, F n (ω, γ) ∂K ω
  have hApos (n : ℕ) (ω : FieldPair d) : 0 ≤ A n ω :=
    integral_nonneg fun γ => abs_nonneg _
  have hA (n : ℕ) : Integrable (A n) Q.measure := by
    have h := (Measure.integrable_compProd_iff (hi n).aestronglyMeasurable).mp (hi n)
    have hn : ∀ p, ‖F n p‖ = F n p := fun p =>
      (Real.norm_eq_abs _).trans (abs_of_nonneg (abs_nonneg _))
    simpa only [A, hn] using h.2
  have hshift : Filter.Tendsto (fun n => J (n + N)) Filter.atTop (𝓝 0) :=
    hJ.comp (Filter.tendsto_add_atTop_nat N)
  have hreal : Filter.Tendsto (fun n => ∫ p, F n p ∂(Q.measure ⊗ₘ K))
      Filter.atTop (𝓝 0) := by
    have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hshift
    simp only [ENNReal.toReal_zero] at h
    apply h.congr
    intro n
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun p => abs_nonneg _)
      (hF n).aestronglyMeasurable]
    simp only [R, Real.enorm_eq_ofReal_abs, J, Function.comp_def]
  have heLp : Filter.Tendsto (fun n => eLpNorm (A n - 0) 1 Q.measure) Filter.atTop (𝓝 0) := by
    have heq (n : ℕ) : eLpNorm (A n - 0) 1 Q.measure =
        ENNReal.ofReal (∫ p, F n p ∂(Q.measure ⊗ₘ K)) := by
      simp only [sub_zero]
      rw [eLpNorm_one_eq_lintegral_enorm (hA n).aestronglyMeasurable,
        ← ofReal_integral_norm_eq_lintegral_enorm (hA n)]
      simp_rw [Real.norm_eq_abs, abs_of_nonneg (hApos n _)]
      rw [Measure.integral_compProd (hi n)]
    simp_rw [heq]
    simpa only [ENNReal.ofReal_zero, Function.comp_def] using
      (ENNReal.continuous_ofReal.tendsto 0).comp hreal
  obtain ⟨ns, hns, ha⟩ :=
    (tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (1 : ℝ≥0∞) ≠ 0) heLp).exists_seq_tendsto_ae
  refine ⟨fun n => ns n + N, fun i j hij => Nat.add_lt_add_right (hns hij) N, ?_⟩
  filter_upwards [ha, hK'] with ω hω hKω
  simpa only [A, F, R, E, Pi.zero_apply, hKω] using hω



/-- L²-small tests have vanishing annealed occupation under the literal estimate. -/
theorem s5_gmp_occupation_residual_tendsto_of_l2_estimate
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (mu : ℝ) (h0 : 0 ≤ mu) (h1 : mu ≤ 1) (P : QuenchedPathLaws d)
    (_hP : IsGMPReducedKernel hd Q.ellipticity_parameter Q mu h0 h1 P)
    (T : ℝ≥0)
    (hocc : ∀ (v : FieldPair d → ℝ), Measurable v → MemLp v 2 (reducedLaw Q) →
      (∫⁻ t in Set.Ioc (0 : ℝ) (T : ℝ),
        ∫⁻ ω, ∫⁻ γ : Path d, ‖v (translate (γ t.toNNReal) (reduce ω))‖ₑ
          ∂P (0, ω) ∂Q.measure) ≤
        (ENNReal.ofReal (Real.exp (mu ^ 2 * (Real.exp (2 * Λ₀) * Λ₀) * (T : ℝ))) ^
          (1 / 2 : ℝ) * eLpNorm v 2 (reducedLaw Q)) *
            (volume : Measure ℝ) (Set.Ioc 0 (T : ℝ)))
    (r : ℕ → FieldPair d → ℝ) (hm : ∀ n, Measurable (r n))
    (hr : ∀ n, MemLp (r n) 2 (reducedLaw Q))
    (hlim : Filter.Tendsto (fun n => ‖(hr n).toLp (r n)‖) Filter.atTop (𝓝 0)) :
    Filter.Tendsto (fun n => ∫⁻ t in Set.Ioc (0 : ℝ) (T : ℝ),
      ∫⁻ ω, ∫⁻ γ : Path d, ‖r n (translate (γ t.toNNReal) (reduce ω))‖ₑ
        ∂P (0, ω) ∂Q.measure) Filter.atTop (𝓝 0) := by
  let C : ℝ≥0∞ := ENNReal.ofReal (Real.exp
    (mu ^ 2 * (Real.exp (2 * Λ₀) * Λ₀) * (T : ℝ))) ^ (1 / 2 : ℝ)
  let M : ℝ≥0∞ := (volume : Measure ℝ) (Set.Ioc 0 (T : ℝ))
  have hC : C ≠ ∞ :=
    ne_of_lt (ENNReal.rpow_lt_top_of_nonneg (by norm_num) ENNReal.ofReal_lt_top.ne)
  have hM : M ≠ ∞ := measure_Ioc_lt_top.ne
  have hr_lim : Filter.Tendsto (fun n => eLpNorm (r n) 2 (reducedLaw Q))
      Filter.atTop (𝓝 0) := by
    have hh := ENNReal.tendsto_ofReal hlim
    simp only [ENNReal.ofReal_zero] at hh
    apply hh.congr
    intro n
    rw [Lp.norm_def, eLpNorm_congr_ae (hr n).coeFn_toLp,
      ENNReal.ofReal_toReal (hr n).eLpNorm_ne_top]
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds _
    (fun _ => bot_le) (fun n => hocc (r n) (hm n) (hr n))
  have hh := ENNReal.Tendsto.const_mul hr_lim (Or.inr hC)
  have hh' := ENNReal.Tendsto.mul_const (b := M) hh (Or.inr hM)
  simpa [C, M] using hh'


theorem s5_gmp_occupation_endpoints_subsequence_of_l2_estimates
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (mu : ℝ) (h0 : 0 ≤ mu) (h1 : mu ≤ 1) (P : QuenchedPathLaws d)
    (hP : IsGMPReducedKernel hd Q.ellipticity_parameter Q mu h0 h1 P)
    (T : ℝ≥0)
    (hocc : ∀ (v : FieldPair d → ℝ), Measurable v → MemLp v 2 (reducedLaw Q) →
      (∫⁻ t in Set.Ioc (0 : ℝ) (T : ℝ),
        ∫⁻ ω, ∫⁻ γ : Path d, ‖v (translate (γ t.toNNReal) (reduce ω))‖ₑ
          ∂P (0, ω) ∂Q.measure) ≤
        (ENNReal.ofReal (Real.exp (mu ^ 2 * (Real.exp (2 * Λ₀) * Λ₀) * (T : ℝ))) ^
          (1 / 2 : ℝ) * eLpNorm v 2 (reducedLaw Q)) *
            (volume : Measure ℝ) (Set.Ioc 0 (T : ℝ)))
    (hendpoint : ∀ (t : ℝ≥0), ∀ (v : FieldPair d → ℝ), Measurable v → MemLp v 2 (reducedLaw Q) →
      (∫⁻ ω, ∫⁻ γ : Path d, ‖v (translate (γ t) (reduce ω))‖ₑ
        ∂P (0, ω) ∂Q.measure) ≤
        ENNReal.ofReal (Real.exp (mu ^ 2 * (Real.exp (2 * Λ₀) * Λ₀) * (t : ℝ))) ^
          (1 / 2 : ℝ) * eLpNorm v 2 (reducedLaw Q))
    (r : ℕ → FieldPair d → ℝ)
    (hm : ∀ n, Measurable (r n)) (hr : ∀ n, MemLp (r n) 2 (reducedLaw Q))
    (hlim : Filter.Tendsto (fun n => ‖(hr n).toLp (r n)‖) Filter.atTop (𝓝 0)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∀ᵐ ω ∂Q.measure,
      Filter.Tendsto (fun n => ∫ t in Set.Ioc (0 : ℝ) (T : ℝ),
        ∫ γ : Path d, |r (ns n) (translate (γ t.toNNReal) (reduce ω))| ∂P (0, ω))
        Filter.atTop (𝓝 0) ∧
      Filter.Tendsto (fun n => ∫ γ : Path d,
        |r (ns n) (translate (γ 0) (reduce ω))| ∂P (0, ω)) Filter.atTop (𝓝 0) ∧
      Filter.Tendsto (fun n => ∫ γ : Path d,
        |r (ns n) (translate (γ T) (reduce ω))| ∂P (0, ω)) Filter.atTop (𝓝 0) := by
  have hres := s5_gmp_occupation_residual_tendsto_of_l2_estimate hd Q mu h0 h1 P hP T hocc r hm hr hlim
  obtain ⟨a, ha, hocc'⟩ := s5_gmp_occupation_quenched_subsequence_of_tendsto
    hd Q mu h0 h1 P hP T r hm hres
  obtain ⟨b, hb, hzero⟩ := s5_gmp_endpoint_quenched_subsequence_of_l2_estimate
    hd Q mu h0 h1 P hP 0 (hendpoint 0) (r ∘ a) (fun n => hm (a n))
      (fun n => hr (a n)) (hlim.comp ha.tendsto_atTop)
  obtain ⟨c, hc, hend⟩ := s5_gmp_endpoint_quenched_subsequence_of_l2_estimate
    hd Q mu h0 h1 P hP T (hendpoint T) (r ∘ a ∘ b) (fun n => hm (a (b n)))
      (fun n => hr (a (b n))) (hlim.comp (ha.comp hb).tendsto_atTop)
  refine ⟨a ∘ b ∘ c, (ha.comp hb).comp hc, ?_⟩
  filter_upwards [hocc', hzero, hend] with ω hωocc hωzero hωend
  exact ⟨hωocc.comp (hb.comp hc).tendsto_atTop,
    hωzero.comp hc.tendsto_atTop, hωend⟩



/-- The literal occupation estimate gives quenched Fubini. -/
theorem s5_gmp_occupation_fubini_of_l2_estimate
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (mu : ℝ) (h0 : 0 ≤ mu) (h1 : mu ≤ 1) (P : QuenchedPathLaws d)
    (hP : IsGMPReducedKernel hd Q.ellipticity_parameter Q mu h0 h1 P)
    (T : ℝ≥0)
    (hocc : ∀ (v : FieldPair d → ℝ), Measurable v → MemLp v 2 (reducedLaw Q) →
      (∫⁻ t in Set.Ioc (0 : ℝ) (T : ℝ),
        ∫⁻ ω, ∫⁻ γ : Path d, ‖v (translate (γ t.toNNReal) (reduce ω))‖ₑ
          ∂P (0, ω) ∂Q.measure) ≤
        (ENNReal.ofReal (Real.exp (mu ^ 2 * (Real.exp (2 * Λ₀) * Λ₀) * (T : ℝ))) ^
          (1 / 2 : ℝ) * eLpNorm v 2 (reducedLaw Q)) *
            (volume : Measure ℝ) (Set.Ioc 0 (T : ℝ)))
    (r : FieldPair d → ℝ) (hm : Measurable r)
    (hr : MemLp r 2 (reducedLaw Q)) :
    ∀ᵐ ω ∂Q.measure,
      Integrable (fun p : Path d × ℝ =>
        r (translate (p.1 p.2.toNNReal) (reduce ω)))
          ((P (0, ω)).prod (volume.restrict (Set.Ioc 0 (T : ℝ)))) ∧
      (∫ γ : Path d, (∫ t in Set.Ioc 0 (T : ℝ),
        r (translate (γ t.toNNReal) (reduce ω))) ∂P (0, ω)) =
      ∫ t in Set.Ioc 0 (T : ℝ), ∫ γ : Path d,
        r (translate (γ t.toNNReal) (reduce ω)) ∂P (0, ω) := by
  obtain ⟨K, hmarkov, hK, hi⟩ :=
    s5_gmp_joint_occupation_integrable_of_l2_estimate
      hd Q mu h0 h1 P hP T hocc r hm hr
  let : IsMarkovKernel K := hmarkov
  let E : ℝ × (FieldPair d × Path d) → FieldPair d := fun p =>
    translate (p.2.2 p.1.toNNReal) (reduce p.2.1)
  have hE : Measurable E := by
    exact (Probability.continuous_translate.comp
      ((continuous_eval.comp ((continuous_snd.comp continuous_snd).prodMk
        (continuous_real_toNNReal.comp continuous_fst))).prodMk
        (Probability.continuous_reduce.comp (continuous_fst.comp continuous_snd)))).measurable
  have hi' : Integrable (fun p : ℝ × (FieldPair d × Path d) => r (E p))
      ((volume.restrict (Set.Ioc 0 (T : ℝ))).prod (Q.measure ⊗ₘ K)) := by
    apply hi.mono' (hm.comp hE).aestronglyMeasurable
    filter_upwards [] with p
    simp only [Real.norm_eq_abs, Function.comp_apply, E, le_refl]
  have htime := Measure.ae_ae_of_ae_compProd hi'.prod_left_ae
  have hn := hi'.integral_norm_prod_right
  have hsections := (Measure.integrable_compProd_iff hn.aestronglyMeasurable).mp hn
  filter_upwards [hK, htime, hsections.1] with ω hKω htimeω hnormω
  let : IsProbabilityMeasure (P (0, ω)) := by rw [hKω]; infer_instance
  rw [← hKω] at htimeω hnormω
  have hmeas : Measurable (fun p : Path d × ℝ =>
      r (translate (p.1 p.2.toNNReal) (reduce ω))) := by
    apply hm.comp
    exact (Probability.continuous_translate.comp
      ((continuous_eval.comp (continuous_fst.prodMk
        (continuous_real_toNNReal.comp continuous_snd))).prodMk continuous_const)).measurable
  have hp : Integrable (fun p : Path d × ℝ =>
      r (translate (p.1 p.2.toNNReal) (reduce ω)))
      ((P (0, ω)).prod (volume.restrict (Set.Ioc 0 (T : ℝ)))) := by
    apply (integrable_prod_iff hmeas.aestronglyMeasurable).mpr
    exact ⟨htimeω, hnormω⟩
  exact ⟨hp, (integral_prod _ hp).symm.trans (integral_prod_symm _ hp)⟩


/-- The graph residual and mollification errors share a quenched subsequence. -/
theorem s5_gmp_graph_mollification_joint_subsequence_of_l2_estimates
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (mu s : ℝ) (h0 : 0 ≤ mu) (h1 : mu ≤ 1) (hs : 0 < s) (P : QuenchedPathLaws d)
    (hP : IsGMPReducedKernel hd Q.ellipticity_parameter Q mu h0 h1 P)
    (T : ℝ≥0)
    (hocc : ∀ (v : FieldPair d → ℝ), Measurable v → MemLp v 2 (reducedLaw Q) →
      (∫⁻ t in Set.Ioc (0 : ℝ) (T : ℝ),
        ∫⁻ ω, ∫⁻ γ : Path d, ‖v (translate (γ t.toNNReal) (reduce ω))‖ₑ
          ∂P (0, ω) ∂Q.measure) ≤
        (ENNReal.ofReal (Real.exp (mu ^ 2 * (Real.exp (2 * Λ₀) * Λ₀) * (T : ℝ))) ^
          (1 / 2 : ℝ) * eLpNorm v 2 (reducedLaw Q)) *
            (volume : Measure ℝ) (Set.Ioc 0 (T : ℝ)))
    (hendpoint : ∀ (t : ℝ≥0), ∀ (v : FieldPair d → ℝ), Measurable v → MemLp v 2 (reducedLaw Q) →
      (∫⁻ ω, ∫⁻ γ : Path d, ‖v (translate (γ t) (reduce ω))‖ₑ
        ∂P (0, ω) ∂Q.measure) ≤
        ENNReal.ofReal (Real.exp (mu ^ 2 * (Real.exp (2 * Λ₀) * Λ₀) * (t : ℝ))) ^
          (1 / 2 : ℝ) * eLpNorm v 2 (reducedLaw Q))
    (f g : Lp ℂ 2 (reducedLaw Q))
    (hfg : IsComplexGeneratorPair Q ⟨0, by omega⟩ (mu : ℂ) f g)
    {G : Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hG : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) f G)
    (L : ℂ →L[ℝ] ℝ) :
    let V : FieldPair d → ℝ := fun w => L (f w)
    let M (n : ℕ) := horizontalMollify
      (Calculus.unitMassScaledMollifier d (Entropy.scaleSeq n)) V
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∀ᵐ ω ∂Q.measure,
      Filter.Tendsto (fun n => ∫ t in Set.Ioc (0 : ℝ) (T : ℝ),
        ∫ γ : Path d, |s * M (ns n) (translate (γ t.toNNReal) (reduce ω)) -
          envGenerator hd mu (M (ns n)) (translate (γ t.toNNReal) (reduce ω)) -
          L (((s : ℂ) • f - g) (translate (γ t.toNNReal) (reduce ω)))| ∂P (0, ω))
        Filter.atTop (𝓝 0) ∧
      Filter.Tendsto (fun n => ∫ t in Set.Ioc (0 : ℝ) (T : ℝ),
        ∫ γ : Path d, |M (ns n) (translate (γ t.toNNReal) (reduce ω)) -
          V (translate (γ t.toNNReal) (reduce ω))| ∂P (0, ω)) Filter.atTop (𝓝 0) ∧
      Filter.Tendsto (fun n => ∫ γ : Path d,
        |M (ns n) (translate (γ 0) (reduce ω)) - V (translate (γ 0) (reduce ω))|
          ∂P (0, ω)) Filter.atTop (𝓝 0) ∧
      Filter.Tendsto (fun n => ∫ γ : Path d,
        |M (ns n) (translate (γ T) (reduce ω)) - V (translate (γ T) (reduce ω))|
          ∂P (0, ω)) Filter.atTop (𝓝 0) := by
  let V : FieldPair d → ℝ := fun w => L (f w)
  have hVm : Measurable V := L.continuous.measurable.comp (Lp.stronglyMeasurable f).measurable
  have hV : MemLp V 2 (reducedLaw Q) := L.comp_memLp' (Lp.memLp f)
  let r (n : ℕ) := fun w => horizontalMollify
    (Calculus.unitMassScaledMollifier d (Entropy.scaleSeq n)) V w - V w
  have hm (n : ℕ) : Measurable (r n) :=
    (measurable_horizontalMollify _
      (Entropy.contDiff_unitMassScaledMollifier _).continuous.measurable hVm).sub hVm
  have hr (n : ℕ) : MemLp (r n) 2 (reducedLaw Q) :=
    (Entropy.memLp_horizontalMollify_unitMass (reducedLaw_stationary Q)
      (Entropy.scaleSeq_pos n) ENNReal.ofNat_ne_top hVm hV).sub hV
  have ht := (Calculus.tendsto_eLpNorm_horizontalMollify_unitMassScaledMollifier
    (reducedLaw Q) (reducedLaw_stationary Q) 2 ENNReal.ofNat_ne_top hVm hV).comp
      Entropy.tendsto_scaleSeq
  have htr := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp ht
  simp only [ENNReal.toReal_zero] at htr
  have hlim : Filter.Tendsto (fun n => ‖(hr n).toLp (r n)‖) Filter.atTop (𝓝 0) := by
    apply htr.congr
    intro n
    rw [Lp.norm_def, eLpNorm_congr_ae (hr n).coeFn_toLp]
    rfl
  obtain ⟨a, ha, hgraph⟩ := s5_gmp_literal_graph_residual_quenched_subsequence_of_l2_estimate
    hd Q mu h0 h1 P hP T hocc s hs f g hfg hG L
  obtain ⟨b, hb, hboth⟩ := s5_gmp_occupation_endpoints_subsequence_of_l2_estimates
    hd Q mu h0 h1 P hP T hocc hendpoint (r ∘ a) (fun n => hm (a n))
      (fun n => hr (a n)) (hlim.comp ha.tendsto_atTop)
  refine ⟨a ∘ b, ha.comp hb, ?_⟩
  filter_upwards [hgraph, hboth] with ω hωgraph hωboth
  exact ⟨hωgraph.comp hb.tendsto_atTop, hωboth⟩



/-- A quenched compensator is bounded by absolute occupation. -/
theorem s5_gmp_compensator_abs_le_occupation_of_l2_estimate
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (mu : ℝ) (h0 : 0 ≤ mu) (h1 : mu ≤ 1) (P : QuenchedPathLaws d)
    (hP : IsGMPReducedKernel hd Q.ellipticity_parameter Q mu h0 h1 P)
    (T : ℝ≥0)
    (hocc : ∀ (v : FieldPair d → ℝ), Measurable v → MemLp v 2 (reducedLaw Q) →
      (∫⁻ t in Set.Ioc (0 : ℝ) (T : ℝ),
        ∫⁻ ω, ∫⁻ γ : Path d, ‖v (translate (γ t.toNNReal) (reduce ω))‖ₑ
          ∂P (0, ω) ∂Q.measure) ≤
        (ENNReal.ofReal (Real.exp (mu ^ 2 * (Real.exp (2 * Λ₀) * Λ₀) * (T : ℝ))) ^
          (1 / 2 : ℝ) * eLpNorm v 2 (reducedLaw Q)) *
            (volume : Measure ℝ) (Set.Ioc 0 (T : ℝ))) (r : FieldPair d → ℝ) (hm : Measurable r)
    (hr : MemLp r 2 (reducedLaw Q)) :
    ∀ᵐ ω ∂Q.measure,
      |∫ γ : Path d, (∫ t in Set.Ioc 0 (T : ℝ),
        r (translate (γ t.toNNReal) (reduce ω))) ∂P (0, ω)| ≤
      ∫ t in Set.Ioc 0 (T : ℝ), ∫ γ : Path d,
        |r (translate (γ t.toNNReal) (reduce ω))| ∂P (0, ω) := by
  filter_upwards [s5_gmp_textbook_at_every_start hd Q mu h0 h1 P hP,
    s5_gmp_occupation_fubini_of_l2_estimate hd Q mu h0 h1 P hP T hocc r hm hr] with ω hω hp
  let : IsProbabilityMeasure (P (0, ω)) := (hω 0).1
  let F : Path d × ℝ → ℝ := fun p => r (translate (p.1 p.2.toNNReal) (reduce ω))
  have hi : Integrable F ((P (0, ω)).prod (volume.restrict (Set.Ioc 0 (T : ℝ)))) := hp.1
  calc
    _ = ‖∫ p, F p ∂((P (0, ω)).prod (volume.restrict (Set.Ioc 0 (T : ℝ))))‖ := by
      rw [integral_prod _ hi, Real.norm_eq_abs]
    _ ≤ ∫ p, ‖F p‖ ∂((P (0, ω)).prod (volume.restrict (Set.Ioc 0 (T : ℝ)))) :=
      norm_integral_le_integral_norm F
    _ = _ := by
      simpa only [F, Real.norm_eq_abs] using integral_prod_symm (fun p => ‖F p‖) hi.norm


/-- Small tests have vanishing quenched signed compensators and endpoints. -/
theorem s5_gmp_expectation_compensator_subsequence_of_l2_estimates
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (mu : ℝ) (h0 : 0 ≤ mu) (h1 : mu ≤ 1) (P : QuenchedPathLaws d)
    (hP : IsGMPReducedKernel hd Q.ellipticity_parameter Q mu h0 h1 P)
    (T : ℝ≥0)
    (hocc : ∀ (v : FieldPair d → ℝ), Measurable v → MemLp v 2 (reducedLaw Q) →
      (∫⁻ t in Set.Ioc (0 : ℝ) (T : ℝ),
        ∫⁻ ω, ∫⁻ γ : Path d, ‖v (translate (γ t.toNNReal) (reduce ω))‖ₑ
          ∂P (0, ω) ∂Q.measure) ≤
        (ENNReal.ofReal (Real.exp (mu ^ 2 * (Real.exp (2 * Λ₀) * Λ₀) * (T : ℝ))) ^
          (1 / 2 : ℝ) * eLpNorm v 2 (reducedLaw Q)) *
            (volume : Measure ℝ) (Set.Ioc 0 (T : ℝ)))
    (hendpoint : ∀ (t : ℝ≥0), ∀ (v : FieldPair d → ℝ), Measurable v → MemLp v 2 (reducedLaw Q) →
      (∫⁻ ω, ∫⁻ γ : Path d, ‖v (translate (γ t) (reduce ω))‖ₑ
        ∂P (0, ω) ∂Q.measure) ≤
        ENNReal.ofReal (Real.exp (mu ^ 2 * (Real.exp (2 * Λ₀) * Λ₀) * (t : ℝ))) ^
          (1 / 2 : ℝ) * eLpNorm v 2 (reducedLaw Q)) (r : ℕ → FieldPair d → ℝ)
    (hm : ∀ n, Measurable (r n)) (hr : ∀ n, MemLp (r n) 2 (reducedLaw Q))
    (hlim : Filter.Tendsto (fun n => ‖(hr n).toLp (r n)‖) Filter.atTop (𝓝 0)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∀ᵐ ω ∂Q.measure,
      Filter.Tendsto (fun n => ∫ γ : Path d, (∫ t in Set.Ioc (0 : ℝ) (T : ℝ),
        r (ns n) (translate (γ t.toNNReal) (reduce ω))) ∂P (0, ω)) Filter.atTop (𝓝 0) ∧
      Filter.Tendsto (fun n => ∫ γ : Path d,
        r (ns n) (translate (γ 0) (reduce ω)) ∂P (0, ω)) Filter.atTop (𝓝 0) ∧
      Filter.Tendsto (fun n => ∫ γ : Path d,
        r (ns n) (translate (γ T) (reduce ω)) ∂P (0, ω)) Filter.atTop (𝓝 0) := by
  obtain ⟨ns, hns, hconv⟩ := s5_gmp_occupation_endpoints_subsequence_of_l2_estimates
    hd Q mu h0 h1 P hP T hocc hendpoint r hm hr hlim
  have hbound : ∀ᵐ ω ∂Q.measure, ∀ n,
      |∫ γ : Path d, (∫ t in Set.Ioc (0 : ℝ) (T : ℝ),
        r (ns n) (translate (γ t.toNNReal) (reduce ω))) ∂P (0, ω)| ≤
      ∫ t in Set.Ioc (0 : ℝ) (T : ℝ), ∫ γ : Path d,
        |r (ns n) (translate (γ t.toNNReal) (reduce ω))| ∂P (0, ω) := by
    exact ae_all_iff.mpr fun n => s5_gmp_compensator_abs_le_occupation_of_l2_estimate
      hd Q mu h0 h1 P hP T hocc (r (ns n)) (hm (ns n)) (hr (ns n))
  refine ⟨ns, hns, ?_⟩
  filter_upwards [hconv, hbound] with ω hc hb
  refine ⟨?_, ?_, ?_⟩
  · apply squeeze_zero_norm (a := fun n => ∫ t in Set.Ioc (0 : ℝ) (T : ℝ),
        ∫ γ : Path d, |r (ns n) (translate (γ t.toNNReal) (reduce ω))| ∂P (0, ω))
    · intro n
      simpa only [Real.norm_eq_abs] using hb n
    · exact hc.1
  · apply squeeze_zero_norm (a := fun n => ∫ γ : Path d,
        |r (ns n) (translate (γ 0) (reduce ω))| ∂P (0, ω))
    · intro n
      simpa only [Real.norm_eq_abs] using
        (norm_integral_le_integral_norm (fun γ : Path d =>
          r (ns n) (translate (γ 0) (reduce ω))))
    · exact hc.2.1
  · apply squeeze_zero_norm (a := fun n => ∫ γ : Path d,
        |r (ns n) (translate (γ T) (reduce ω))| ∂P (0, ω))
    · intro n
      simpa only [Real.norm_eq_abs] using
        (norm_integral_le_integral_norm (fun γ : Path d =>
          r (ns n) (translate (γ T) (reduce ω))))
    · exact hc.2.2


/-- The literal graph residual has a vanishing quenched compensator. -/
theorem s5_gmp_graph_residual_compensator_subsequence_of_l2_estimates
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (mu s : ℝ) (h0 : 0 ≤ mu) (h1 : mu ≤ 1) (hs : 0 < s) (P : QuenchedPathLaws d)
    (hP : IsGMPReducedKernel hd Q.ellipticity_parameter Q mu h0 h1 P)
    (T : ℝ≥0)
    (hocc : ∀ (v : FieldPair d → ℝ), Measurable v → MemLp v 2 (reducedLaw Q) →
      (∫⁻ t in Set.Ioc (0 : ℝ) (T : ℝ),
        ∫⁻ ω, ∫⁻ γ : Path d, ‖v (translate (γ t.toNNReal) (reduce ω))‖ₑ
          ∂P (0, ω) ∂Q.measure) ≤
        (ENNReal.ofReal (Real.exp (mu ^ 2 * (Real.exp (2 * Λ₀) * Λ₀) * (T : ℝ))) ^
          (1 / 2 : ℝ) * eLpNorm v 2 (reducedLaw Q)) *
            (volume : Measure ℝ) (Set.Ioc 0 (T : ℝ)))
    (hendpoint : ∀ (t : ℝ≥0), ∀ (v : FieldPair d → ℝ), Measurable v → MemLp v 2 (reducedLaw Q) →
      (∫⁻ ω, ∫⁻ γ : Path d, ‖v (translate (γ t) (reduce ω))‖ₑ
        ∂P (0, ω) ∂Q.measure) ≤
        ENNReal.ofReal (Real.exp (mu ^ 2 * (Real.exp (2 * Λ₀) * Λ₀) * (t : ℝ))) ^
          (1 / 2 : ℝ) * eLpNorm v 2 (reducedLaw Q)) (f g : Lp ℂ 2 (reducedLaw Q))
    (hfg : IsComplexGeneratorPair Q ⟨0, by omega⟩ (mu : ℂ) f g)
    {G : Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hG : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) f G)
    (L : ℂ →L[ℝ] ℝ) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∀ᵐ ω ∂Q.measure,
      Filter.Tendsto (fun n => ∫ γ : Path d, (∫ t in Set.Ioc (0 : ℝ) (T : ℝ),
        (s * horizontalMollify (Calculus.unitMassScaledMollifier d (Entropy.scaleSeq (ns n)))
          (fun v => L (f v)) (translate (γ t.toNNReal) (reduce ω)) -
        envGenerator hd mu (horizontalMollify
          (Calculus.unitMassScaledMollifier d (Entropy.scaleSeq (ns n))) (fun v => L (f v)))
          (translate (γ t.toNNReal) (reduce ω)) -
        L (((s : ℂ) • f - g) (translate (γ t.toNNReal) (reduce ω))))) ∂P (0, ω))
        Filter.atTop (𝓝 0) := by
  obtain ⟨r, hr, hm, he, hlim⟩ :=
    u3_signed_graph_mollified_residual_representatives hd Q mu s hs f g hfg hG L
  obtain ⟨ns, hns, hconv⟩ := s5_gmp_expectation_compensator_subsequence_of_l2_estimates
    hd Q mu h0 h1 P hP T hocc hendpoint r hm hr hlim
  have ha := fun n => s5_gmp_ae_eq_path_occupation hd Q mu h0 h1 P hP (r (ns n)) _ (he (ns n))
  refine ⟨ns, hns, ?_⟩
  filter_upwards [hconv, ae_all_iff.mpr ha] with ω hc heq
  apply hc.1.congr
  intro n
  apply integral_congr_ae
  filter_upwards [heq n] with γ hγ
  apply integral_congr_ae
  exact ae_restrict_of_ae_restrict_of_subset (fun _ ht => ht.1) hγ



/-- Graph and mollification compensators vanish along a common subsequence. -/
theorem s5_gmp_graph_joint_compensator_subsequence_of_l2_estimates
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (mu s : ℝ) (h0 : 0 ≤ mu) (h1 : mu ≤ 1) (hs : 0 < s) (P : QuenchedPathLaws d)
    (hP : IsGMPReducedKernel hd Q.ellipticity_parameter Q mu h0 h1 P)
    (T : ℝ≥0)
    (hocc : ∀ (v : FieldPair d → ℝ), Measurable v → MemLp v 2 (reducedLaw Q) →
      (∫⁻ t in Set.Ioc (0 : ℝ) (T : ℝ),
        ∫⁻ ω, ∫⁻ γ : Path d, ‖v (translate (γ t.toNNReal) (reduce ω))‖ₑ
          ∂P (0, ω) ∂Q.measure) ≤
        (ENNReal.ofReal (Real.exp (mu ^ 2 * (Real.exp (2 * Λ₀) * Λ₀) * (T : ℝ))) ^
          (1 / 2 : ℝ) * eLpNorm v 2 (reducedLaw Q)) *
            (volume : Measure ℝ) (Set.Ioc 0 (T : ℝ)))
    (hendpoint : ∀ (t : ℝ≥0), ∀ (v : FieldPair d → ℝ), Measurable v → MemLp v 2 (reducedLaw Q) →
      (∫⁻ ω, ∫⁻ γ : Path d, ‖v (translate (γ t) (reduce ω))‖ₑ
        ∂P (0, ω) ∂Q.measure) ≤
        ENNReal.ofReal (Real.exp (mu ^ 2 * (Real.exp (2 * Λ₀) * Λ₀) * (t : ℝ))) ^
          (1 / 2 : ℝ) * eLpNorm v 2 (reducedLaw Q)) (f g : Lp ℂ 2 (reducedLaw Q))
    (hfg : IsComplexGeneratorPair Q ⟨0, by omega⟩ (mu : ℂ) f g)
    {G : Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hG : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) f G)
    (L : ℂ →L[ℝ] ℝ) :
    let V : FieldPair d → ℝ := fun w => L (f w)
    let M (n : ℕ) := horizontalMollify
      (Calculus.unitMassScaledMollifier d (Entropy.scaleSeq n)) V
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∀ᵐ ω ∂Q.measure,
      Filter.Tendsto (fun n => ∫ γ : Path d, (∫ t in Set.Ioc (0 : ℝ) (T : ℝ),
        (s * M (ns n) (translate (γ t.toNNReal) (reduce ω)) -
          envGenerator hd mu (M (ns n)) (translate (γ t.toNNReal) (reduce ω)) -
          L (((s : ℂ) • f - g) (translate (γ t.toNNReal) (reduce ω))))) ∂P (0, ω))
        Filter.atTop (𝓝 0) ∧
      Filter.Tendsto (fun n => ∫ γ : Path d, (∫ t in Set.Ioc (0 : ℝ) (T : ℝ),
        (M (ns n) (translate (γ t.toNNReal) (reduce ω)) -
          V (translate (γ t.toNNReal) (reduce ω)))) ∂P (0, ω)) Filter.atTop (𝓝 0) ∧
      Filter.Tendsto (fun n => ∫ γ : Path d,
        (M (ns n) (translate (γ 0) (reduce ω)) - V (translate (γ 0) (reduce ω)))
          ∂P (0, ω)) Filter.atTop (𝓝 0) ∧
      Filter.Tendsto (fun n => ∫ γ : Path d,
        (M (ns n) (translate (γ T) (reduce ω)) - V (translate (γ T) (reduce ω)))
          ∂P (0, ω)) Filter.atTop (𝓝 0) := by
  let V : FieldPair d → ℝ := fun w => L (f w)
  have hVm : Measurable V := L.continuous.measurable.comp (Lp.stronglyMeasurable f).measurable
  have hV : MemLp V 2 (reducedLaw Q) := L.comp_memLp' (Lp.memLp f)
  let r (n : ℕ) := fun w => horizontalMollify
    (Calculus.unitMassScaledMollifier d (Entropy.scaleSeq n)) V w - V w
  have hm (n : ℕ) : Measurable (r n) :=
    (measurable_horizontalMollify _
      (Entropy.contDiff_unitMassScaledMollifier _).continuous.measurable hVm).sub hVm
  have hr (n : ℕ) : MemLp (r n) 2 (reducedLaw Q) :=
    (Entropy.memLp_horizontalMollify_unitMass (reducedLaw_stationary Q)
      (Entropy.scaleSeq_pos n) ENNReal.ofNat_ne_top hVm hV).sub hV
  have ht := (Calculus.tendsto_eLpNorm_horizontalMollify_unitMassScaledMollifier
    (reducedLaw Q) (reducedLaw_stationary Q) 2 ENNReal.ofNat_ne_top hVm hV).comp
      Entropy.tendsto_scaleSeq
  have htr := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp ht
  simp only [ENNReal.toReal_zero] at htr
  have hlim : Filter.Tendsto (fun n => ‖(hr n).toLp (r n)‖) Filter.atTop (𝓝 0) := by
    apply htr.congr
    intro n
    rw [Lp.norm_def, eLpNorm_congr_ae (hr n).coeFn_toLp]
    rfl
  obtain ⟨a, ha, hgraph⟩ := s5_gmp_graph_residual_compensator_subsequence_of_l2_estimates
    hd Q mu s h0 h1 hs P hP T hocc hendpoint f g hfg hG L
  obtain ⟨b, hb, herror⟩ := s5_gmp_expectation_compensator_subsequence_of_l2_estimates
    hd Q mu h0 h1 P hP T hocc hendpoint (r ∘ a) (fun n => hm (a n))
      (fun n => hr (a n)) (hlim.comp ha.tendsto_atTop)
  refine ⟨a ∘ b, ha.comp hb, ?_⟩
  filter_upwards [hgraph, herror] with ω hg he
  exact ⟨hg.comp hb.tendsto_atTop, he⟩


/-- GMP compensators respect subtraction of L² tests. -/
theorem s5_gmp_compensator_sub_of_l2_estimate
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (mu : ℝ) (h0 : 0 ≤ mu) (h1 : mu ≤ 1) (P : QuenchedPathLaws d)
    (hP : IsGMPReducedKernel hd Q.ellipticity_parameter Q mu h0 h1 P)
    (T : ℝ≥0)
    (hocc : ∀ (v : FieldPair d → ℝ), Measurable v → MemLp v 2 (reducedLaw Q) →
      (∫⁻ t in Set.Ioc (0 : ℝ) (T : ℝ),
        ∫⁻ ω, ∫⁻ γ : Path d, ‖v (translate (γ t.toNNReal) (reduce ω))‖ₑ
          ∂P (0, ω) ∂Q.measure) ≤
        (ENNReal.ofReal (Real.exp (mu ^ 2 * (Real.exp (2 * Λ₀) * Λ₀) * (T : ℝ))) ^
          (1 / 2 : ℝ) * eLpNorm v 2 (reducedLaw Q)) *
            (volume : Measure ℝ) (Set.Ioc 0 (T : ℝ))) (f g : FieldPair d → ℝ) (hf : Measurable f) (hg : Measurable g)
    (hflp : MemLp f 2 (reducedLaw Q)) (hglp : MemLp g 2 (reducedLaw Q)) :
    ∀ᵐ ω ∂Q.measure,
      (∫ γ : Path d, (∫ t in Set.Ioc (0 : ℝ) (T : ℝ),
        (f (translate (γ t.toNNReal) (reduce ω)) -
          g (translate (γ t.toNNReal) (reduce ω)))) ∂P (0, ω)) =
      (∫ γ : Path d, (∫ t in Set.Ioc (0 : ℝ) (T : ℝ),
        f (translate (γ t.toNNReal) (reduce ω))) ∂P (0, ω)) -
      (∫ γ : Path d, (∫ t in Set.Ioc (0 : ℝ) (T : ℝ),
        g (translate (γ t.toNNReal) (reduce ω))) ∂P (0, ω)) := by
  filter_upwards [s5_gmp_textbook_at_every_start hd Q mu h0 h1 P hP,
    s5_gmp_occupation_fubini_of_l2_estimate hd Q mu h0 h1 P hP T hocc f hf hflp,
    s5_gmp_occupation_fubini_of_l2_estimate hd Q mu h0 h1 P hP T hocc g hg hglp] with ω htext hfi hgi
  let : IsProbabilityMeasure (P (0, ω)) := (htext 0).1
  let F : Path d × ℝ → ℝ := fun p => f (translate (p.1 p.2.toNNReal) (reduce ω))
  let G : Path d × ℝ → ℝ := fun p => g (translate (p.1 p.2.toNNReal) (reduce ω))
  have hF : Integrable F ((P (0, ω)).prod (volume.restrict (Set.Ioc 0 (T : ℝ)))) := hfi.1
  have hG : Integrable G ((P (0, ω)).prod (volume.restrict (Set.Ioc 0 (T : ℝ)))) := hgi.1
  change (∫ γ : Path d, (∫ t in Set.Ioc (0 : ℝ) (T : ℝ),
    ((F - G) (γ, t))) ∂P (0, ω)) =
    (∫ γ : Path d, (∫ t in Set.Ioc (0 : ℝ) (T : ℝ), F (γ, t)) ∂P (0, ω)) -
    (∫ γ : Path d, (∫ t in Set.Ioc (0 : ℝ) (T : ℝ), G (γ, t)) ∂P (0, ω))
  rw [← integral_prod _ (hF.sub hG), ← integral_prod _ hF, ← integral_prod _ hG]
  exact integral_sub hF hG


/-- Algebra of the literal graph compensator. -/
theorem s5_gmp_graph_compensator_algebra_of_l2_estimate
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (mu s : ℝ) (h0 : 0 ≤ mu) (h1 : mu ≤ 1) (hs : 0 < s) (P : QuenchedPathLaws d)
    (hP : IsGMPReducedKernel hd Q.ellipticity_parameter Q mu h0 h1 P)
    (T : ℝ≥0)
    (hocc : ∀ (v : FieldPair d → ℝ), Measurable v → MemLp v 2 (reducedLaw Q) →
      (∫⁻ t in Set.Ioc (0 : ℝ) (T : ℝ),
        ∫⁻ ω, ∫⁻ γ : Path d, ‖v (translate (γ t.toNNReal) (reduce ω))‖ₑ
          ∂P (0, ω) ∂Q.measure) ≤
        (ENNReal.ofReal (Real.exp (mu ^ 2 * (Real.exp (2 * Λ₀) * Λ₀) * (T : ℝ))) ^
          (1 / 2 : ℝ) * eLpNorm v 2 (reducedLaw Q)) *
            (volume : Measure ℝ) (Set.Ioc 0 (T : ℝ))) (f g : Lp ℂ 2 (reducedLaw Q))
    (hfg : IsComplexGeneratorPair Q ⟨0, by omega⟩ (mu : ℂ) f g)
    {G : Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hG : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) f G)
    (L : ℂ →L[ℝ] ℝ) (n : ℕ) :
    let V : FieldPair d → ℝ := fun w => L (f w)
    let W : FieldPair d → ℝ := fun w => L (g w)
    let M := horizontalMollify (Calculus.unitMassScaledMollifier d (Entropy.scaleSeq n)) V
    ∀ᵐ ω ∂Q.measure,
      (∫ γ : Path d, (∫ t in Set.Ioc (0 : ℝ) (T : ℝ),
        (s * M (translate (γ t.toNNReal) (reduce ω)) -
          envGenerator hd mu M (translate (γ t.toNNReal) (reduce ω)) -
          L (((s : ℂ) • f - g) (translate (γ t.toNNReal) (reduce ω))))) ∂P (0, ω)) =
      s * (∫ γ : Path d, (∫ t in Set.Ioc (0 : ℝ) (T : ℝ),
        (M (translate (γ t.toNNReal) (reduce ω)) -
          V (translate (γ t.toNNReal) (reduce ω)))) ∂P (0, ω)) -
      ((∫ γ : Path d, (∫ t in Set.Ioc (0 : ℝ) (T : ℝ),
        envGenerator hd mu M (translate (γ t.toNNReal) (reduce ω))) ∂P (0, ω)) -
       (∫ γ : Path d, (∫ t in Set.Ioc (0 : ℝ) (T : ℝ),
        W (translate (γ t.toNNReal) (reduce ω))) ∂P (0, ω))) := by
  let V : FieldPair d → ℝ := fun w => L (f w)
  let W : FieldPair d → ℝ := fun w => L (g w)
  let M := horizontalMollify (Calculus.unitMassScaledMollifier d (Entropy.scaleSeq n)) V
  have hVm : Measurable V := L.continuous.measurable.comp (Lp.stronglyMeasurable f).measurable
  have hWm : Measurable W := L.continuous.measurable.comp (Lp.stronglyMeasurable g).measurable
  have hV : MemLp V 2 (reducedLaw Q) := L.comp_memLp' (Lp.memLp f)
  have hW : MemLp W 2 (reducedLaw Q) := L.comp_memLp' (Lp.memLp g)
  have hMm : Measurable M := measurable_horizontalMollify _
    (Entropy.contDiff_unitMassScaledMollifier _).continuous.measurable hVm
  have hM : MemLp M 2 (reducedLaw Q) :=
    Entropy.memLp_horizontalMollify_unitMass (reducedLaw_stationary Q)
      (Entropy.scaleSeq_pos n) ENNReal.ofNat_ne_top hVm hV
  obtain ⟨a, ham, ha, hae⟩ :=
    u3_signed_graph_mollified_generator_representatives hd Q mu s hs f g hfg hG L
  let B : FieldPair d → ℝ := fun w => s * (M w - V w)
  let H : FieldPair d → ℝ := fun w => a n w - W w
  have hBm : Measurable B := measurable_const.mul (hMm.sub hVm)
  have hHm : Measurable H := (ham n).sub hWm
  have hB : MemLp B 2 (reducedLaw Q) := (hM.sub hV).const_mul s
  have hH : MemLp H 2 (reducedLaw Q) := (ha n).sub hW
  have he : (fun w => B w - H w) =ᵐ[reducedLaw Q]
      fun w => s * M w - envGenerator hd mu M w - L (((s : ℂ) • f - g) w) := by
    filter_upwards [hae n, u3_real_linear_graph_representative_ae Q s f g L] with w hgen hgraph
    change a n w = envGenerator hd mu M w at hgen
    change L (((s : ℂ) • f - g) w) = s * V w - W w at hgraph
    dsimp only [B, H]
    rw [hgen, hgraph]
    ring
  have hepath := s5_gmp_ae_eq_path_occupation hd Q mu h0 h1 P hP (fun w => B w - H w)
      (fun w => s * M w - envGenerator hd mu M w - L (((s : ℂ) • f - g) w)) he
  have hgpath := s5_gmp_ae_eq_path_occupation hd Q mu h0 h1 P hP (a n) (envGenerator hd mu M) (hae n)
  filter_upwards [hepath, hgpath,
    s5_gmp_compensator_sub_of_l2_estimate hd Q mu h0 h1 P hP T hocc B H hBm hHm hB hH,
    s5_gmp_compensator_sub_of_l2_estimate hd Q mu h0 h1 P hP T hocc (a n) W
      (ham n) hWm (ha n) hW] with ω heω hgω hsub hsub'
  have heq : (∫ γ : Path d, (∫ t in Set.Ioc (0 : ℝ) (T : ℝ),
      (B (translate (γ t.toNNReal) (reduce ω)) - H (translate (γ t.toNNReal) (reduce ω)))) ∂P (0, ω)) =
      ∫ γ : Path d, (∫ t in Set.Ioc (0 : ℝ) (T : ℝ),
        (s * M (translate (γ t.toNNReal) (reduce ω)) -
          envGenerator hd mu M (translate (γ t.toNNReal) (reduce ω)) -
          L (((s : ℂ) • f - g) (translate (γ t.toNNReal) (reduce ω))))) ∂P (0, ω) := by
    apply integral_congr_ae
    filter_upwards [heω] with γ hγ
    apply integral_congr_ae
    exact ae_restrict_of_ae_restrict_of_subset (fun _ ht => ht.1) hγ
  have hgen : (∫ γ : Path d, (∫ t in Set.Ioc (0 : ℝ) (T : ℝ),
      a n (translate (γ t.toNNReal) (reduce ω))) ∂P (0, ω)) =
      ∫ γ : Path d, (∫ t in Set.Ioc (0 : ℝ) (T : ℝ),
        envGenerator hd mu M (translate (γ t.toNNReal) (reduce ω))) ∂P (0, ω) := by
    apply integral_congr_ae
    filter_upwards [hgω] with γ hγ
    apply integral_congr_ae
    exact ae_restrict_of_ae_restrict_of_subset (fun _ ht => ht.1) hγ
  dsimp only [H] at hsub
  rw [hsub', hgen] at hsub
  rw [← heq, hsub]
  simp only [B, integral_const_mul]
  rfl



/-- The literal endpoint estimate gives quenched endpoint integrability. -/
theorem s5_gmp_endpoint_integrable_of_l2_estimate
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (mu : ℝ) (h0 : 0 ≤ mu) (h1 : mu ≤ 1) (P : QuenchedPathLaws d)
    (hP : IsGMPReducedKernel hd Q.ellipticity_parameter Q mu h0 h1 P)
    (t : ℝ≥0)
    (hendpoint : ∀ (v : FieldPair d → ℝ), Measurable v → MemLp v 2 (reducedLaw Q) →
      (∫⁻ ω, ∫⁻ γ : Path d, ‖v (translate (γ t) (reduce ω))‖ₑ
        ∂P (0, ω) ∂Q.measure) ≤
        ENNReal.ofReal (Real.exp (mu ^ 2 * (Real.exp (2 * Λ₀) * Λ₀) * (t : ℝ))) ^
          (1 / 2 : ℝ) * eLpNorm v 2 (reducedLaw Q))
    (v : FieldPair d → ℝ) (hv : Measurable v) (hlp : MemLp v 2 (reducedLaw Q)) :
    ∀ᵐ ω ∂Q.measure, Integrable
      (fun γ : Path d => v (translate (γ t) (reduce ω))) (P (0, ω)) := by
  obtain ⟨K, hmarkov, hK⟩ := s5_gmp_origin_markov_version hd Q mu h0 h1 P hP
  let : IsMarkovKernel K := hmarkov
  have hK' : ∀ᵐ ω ∂Q.measure, P (0, ω) = K ω := hK.mono fun _ h => h.symm
  let E : FieldPair d × Path d → ℝ := fun p => v (translate (p.2 t) (reduce p.1))
  have hE : Measurable E := hv.comp (Probability.continuous_translate.comp
    ((continuous_eval.comp (continuous_snd.prodMk continuous_const)).prodMk
      (Probability.continuous_reduce.comp continuous_fst))).measurable
  have hC : ENNReal.ofReal (Real.exp
      (mu ^ 2 * (Real.exp (2 * Λ₀) * Λ₀) * (t : ℝ))) ^ (1 / 2 : ℝ) ≠ ∞ :=
    ne_of_lt (ENNReal.rpow_lt_top_of_nonneg (by norm_num) ENNReal.ofReal_lt_top.ne)
  have hfin : (∫⁻ ω, ∫⁻ γ : Path d, ‖v (translate (γ t) (reduce ω))‖ₑ
      ∂P (0, ω) ∂Q.measure) < ∞ :=
    lt_of_le_of_lt (hendpoint v hv hlp)
      (ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr hC) (lt_top_iff_ne_top.mpr hlp.eLpNorm_ne_top))
  have heq : (∫⁻ p, ‖E p‖ₑ ∂(Q.measure ⊗ₘ K)) =
      ∫⁻ ω, ∫⁻ γ : Path d, ‖v (translate (γ t) (reduce ω))‖ₑ ∂P (0, ω) ∂Q.measure := by
    rw [Measure.lintegral_compProd hE.enorm]
    apply lintegral_congr_ae
    filter_upwards [hK'] with ω hω
    simp only [E, hω]
  have hi : Integrable E (Q.measure ⊗ₘ K) := by
    refine ⟨hE.aestronglyMeasurable, ?_⟩
    apply hasFiniteIntegral_iff_enorm.mpr
    rw [heq]
    exact hfin
  have hsections := (Measure.integrable_compProd_iff hi.aestronglyMeasurable).mp hi
  filter_upwards [hsections.1, hK'] with ω hω hKω
  simpa only [E, hKω] using hω



/-- Mollified GMP generator compensators converge to the graph output. -/
theorem s5_gmp_graph_generator_compensator_subsequence_of_l2_estimates
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (mu s : ℝ) (h0 : 0 ≤ mu) (h1 : mu ≤ 1) (hs : 0 < s) (P : QuenchedPathLaws d)
    (hP : IsGMPReducedKernel hd Q.ellipticity_parameter Q mu h0 h1 P)
    (T : ℝ≥0)
    (hocc : ∀ (v : FieldPair d → ℝ), Measurable v → MemLp v 2 (reducedLaw Q) →
      (∫⁻ t in Set.Ioc (0 : ℝ) (T : ℝ),
        ∫⁻ ω, ∫⁻ γ : Path d, ‖v (translate (γ t.toNNReal) (reduce ω))‖ₑ
          ∂P (0, ω) ∂Q.measure) ≤
        (ENNReal.ofReal (Real.exp (mu ^ 2 * (Real.exp (2 * Λ₀) * Λ₀) * (T : ℝ))) ^
          (1 / 2 : ℝ) * eLpNorm v 2 (reducedLaw Q)) *
            (volume : Measure ℝ) (Set.Ioc 0 (T : ℝ)))
    (hendpoint : ∀ (t : ℝ≥0), ∀ (v : FieldPair d → ℝ), Measurable v → MemLp v 2 (reducedLaw Q) →
      (∫⁻ ω, ∫⁻ γ : Path d, ‖v (translate (γ t) (reduce ω))‖ₑ
        ∂P (0, ω) ∂Q.measure) ≤
        ENNReal.ofReal (Real.exp (mu ^ 2 * (Real.exp (2 * Λ₀) * Λ₀) * (t : ℝ))) ^
          (1 / 2 : ℝ) * eLpNorm v 2 (reducedLaw Q)) (f g : Lp ℂ 2 (reducedLaw Q))
    (hfg : IsComplexGeneratorPair Q ⟨0, by omega⟩ (mu : ℂ) f g)
    {G : Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hG : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) f G)
    (L : ℂ →L[ℝ] ℝ) :
    let V : FieldPair d → ℝ := fun w => L (f w)
    let W : FieldPair d → ℝ := fun w => L (g w)
    let M (n : ℕ) := horizontalMollify
      (Calculus.unitMassScaledMollifier d (Entropy.scaleSeq n)) V
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∀ᵐ ω ∂Q.measure,
      Filter.Tendsto (fun n => ∫ γ : Path d, (∫ t in Set.Ioc (0 : ℝ) (T : ℝ),
        envGenerator hd mu (M (ns n)) (translate (γ t.toNNReal) (reduce ω))) ∂P (0, ω))
        Filter.atTop (𝓝 (∫ γ : Path d, (∫ t in Set.Ioc (0 : ℝ) (T : ℝ),
          W (translate (γ t.toNNReal) (reduce ω))) ∂P (0, ω))) ∧
      Filter.Tendsto (fun n => ∫ γ : Path d,
        (M (ns n) (translate (γ 0) (reduce ω)) - V (translate (γ 0) (reduce ω)))
          ∂P (0, ω)) Filter.atTop (𝓝 0) ∧
      Filter.Tendsto (fun n => ∫ γ : Path d,
        (M (ns n) (translate (γ T) (reduce ω)) - V (translate (γ T) (reduce ω)))
          ∂P (0, ω)) Filter.atTop (𝓝 0) := by
  obtain ⟨ns, hns, hc⟩ := s5_gmp_graph_joint_compensator_subsequence_of_l2_estimates
    hd Q mu s h0 h1 hs P hP T hocc hendpoint f g hfg hG L
  have halg := fun n => s5_gmp_graph_compensator_algebra_of_l2_estimate
    hd Q mu s h0 h1 hs P hP T hocc f g hfg hG L (ns n)
  refine ⟨ns, hns, ?_⟩
  filter_upwards [hc, ae_all_iff.mpr halg] with ω hc ha
  refine ⟨?_, hc.2.2⟩
  have ht := (hc.2.1.const_mul s).sub hc.1
  have ht' := ht.const_add (∫ γ : Path d, (∫ t in Set.Ioc (0 : ℝ) (T : ℝ),
    L (g (translate (γ t.toNNReal) (reduce ω)))) ∂P (0, ω))
  simp only [mul_zero, sub_self, add_zero] at ht'
  apply ht'.congr
  intro n
  have hn := ha n
  linarith


/-- Dynkin identity for an actual GMP graph pair under literal estimates. -/
theorem s5_gmp_graph_dynkin_of_l2_estimates
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (mu s : ℝ) (h0 : 0 ≤ mu) (h1 : mu ≤ 1) (hs : 0 < s) (P : QuenchedPathLaws d)
    (hP : IsGMPReducedKernel hd Q.ellipticity_parameter Q mu h0 h1 P)
    (T : ℝ≥0)
    (hocc : ∀ (U : ℝ≥0) (v : FieldPair d → ℝ), Measurable v → MemLp v 2 (reducedLaw Q) →
      (∫⁻ t in Set.Ioc (0 : ℝ) (U : ℝ),
        ∫⁻ ω, ∫⁻ γ : Path d, ‖v (translate (γ t.toNNReal) (reduce ω))‖ₑ
          ∂P (0, ω) ∂Q.measure) ≤
        (ENNReal.ofReal (Real.exp (mu ^ 2 * (Real.exp (2 * Λ₀) * Λ₀) * (U : ℝ))) ^
          (1 / 2 : ℝ) * eLpNorm v 2 (reducedLaw Q)) *
            (volume : Measure ℝ) (Set.Ioc 0 (U : ℝ)))
    (hendpoint : ∀ (t : ℝ≥0), ∀ (v : FieldPair d → ℝ), Measurable v → MemLp v 2 (reducedLaw Q) →
      (∫⁻ ω, ∫⁻ γ : Path d, ‖v (translate (γ t) (reduce ω))‖ₑ
        ∂P (0, ω) ∂Q.measure) ≤
        ENNReal.ofReal (Real.exp (mu ^ 2 * (Real.exp (2 * Λ₀) * Λ₀) * (t : ℝ))) ^
          (1 / 2 : ℝ) * eLpNorm v 2 (reducedLaw Q)) (f g : Lp ℂ 2 (reducedLaw Q))
    (hfg : IsComplexGeneratorPair Q ⟨0, by omega⟩ (mu : ℂ) f g)
    {G : Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hG : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) f G)
    (L : ℂ →L[ℝ] ℝ) :
    ∀ᵐ ω ∂Q.measure,
      (∫ γ : Path d, L (f (translate (γ T) (reduce ω))) ∂P (0, ω)) -
        L (f (reduce ω)) =
      ∫ γ : Path d, (∫ t in Set.Ioc (0 : ℝ) (T : ℝ),
        L (g (translate (γ t.toNNReal) (reduce ω)))) ∂P (0, ω) := by
  let V : FieldPair d → ℝ := fun w => L (f w)
  let M (n : ℕ) := horizontalMollify
    (Calculus.unitMassScaledMollifier d (Entropy.scaleSeq n)) V
  have hVm : Measurable V := L.continuous.measurable.comp (Lp.stronglyMeasurable f).measurable
  have hV : MemLp V 2 (reducedLaw Q) := L.comp_memLp' (Lp.memLp f)
  have hMm (n : ℕ) : Measurable (M n) := measurable_horizontalMollify _
    (Entropy.contDiff_unitMassScaledMollifier _).continuous.measurable hVm
  have hM (n : ℕ) : MemLp (M n) 2 (reducedLaw Q) :=
    Entropy.memLp_horizontalMollify_unitMass (reducedLaw_stationary Q)
      (Entropy.scaleSeq_pos n) ENNReal.ofNat_ne_top hVm hV
  obtain ⟨ns, hns, hc⟩ := s5_gmp_graph_generator_compensator_subsequence_of_l2_estimates
    hd Q mu s h0 h1 hs P hP T (hocc T) hendpoint f g hfg hG L
  have hdyn (n : ℕ) := s5_gmp_graph_mollified_dynkin_of_l2_estimate
    hd Q mu s h0 h1 hs P hP f g hfg hG L (ns n) T hocc
  have hMi (n : ℕ) := s5_gmp_endpoint_integrable_of_l2_estimate
    hd Q mu h0 h1 P hP T (hendpoint T) (M (ns n)) (hMm (ns n)) (hM (ns n))
  filter_upwards [hc, s5_gmp_textbook_at_every_start hd Q mu h0 h1 P hP, ae_all_iff.mpr hdyn, ae_all_iff.mpr hMi,
    s5_gmp_endpoint_integrable_of_l2_estimate hd Q mu h0 h1 P hP T (hendpoint T) V hVm hV]
    with ω hc htext hdyn hMi hVi
  have hstartlaw := htext 0
  let : IsProbabilityMeasure (P (0, ω)) := hstartlaw.1
  have hstart (n : ℕ) : (∫ γ : Path d,
      (M (ns n) (translate (γ 0) (reduce ω)) - V (translate (γ 0) (reduce ω))) ∂P (0, ω)) =
      M (ns n) (reduce ω) - V (reduce ω) := by
    calc
      _ = ∫ _ : Path d, (M (ns n) (reduce ω) - V (reduce ω)) ∂P (0, ω) :=
        integral_congr_ae (hstartlaw.2.1.mono fun _ h => by simp only [h, translate_zero])
      _ = _ := by simp
  have ht := (hc.2.2.sub hc.2.1).const_add
    ((∫ γ : Path d, V (translate (γ T) (reduce ω)) ∂P (0, ω)) - V (reduce ω))
  simp only [sub_self, add_zero] at ht
  have hlim : Filter.Tendsto (fun n =>
      (∫ γ : Path d, M (ns n) (translate (γ T) (reduce ω)) ∂P (0, ω)) -
        M (ns n) (reduce ω)) Filter.atTop
      (𝓝 ((∫ γ : Path d, V (translate (γ T) (reduce ω)) ∂P (0, ω)) - V (reduce ω))) := by
    apply ht.congr
    intro n
    rw [integral_sub (hMi n) hVi, hstart n]
    linarith
  have hlim' := hlim.congr (fun n => hdyn n)
  exact tendsto_nhds_unique hlim' hc.1


/-- Time-integrated actual GMP graph Dynkin identity. -/
theorem s5_gmp_graph_dynkin_fubini_of_l2_estimates
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (mu s : ℝ) (h0 : 0 ≤ mu) (h1 : mu ≤ 1) (hs : 0 < s) (P : QuenchedPathLaws d)
    (hP : IsGMPReducedKernel hd Q.ellipticity_parameter Q mu h0 h1 P)
    (T : ℝ≥0)
    (hocc : ∀ (U : ℝ≥0) (v : FieldPair d → ℝ), Measurable v → MemLp v 2 (reducedLaw Q) →
      (∫⁻ t in Set.Ioc (0 : ℝ) (U : ℝ),
        ∫⁻ ω, ∫⁻ γ : Path d, ‖v (translate (γ t.toNNReal) (reduce ω))‖ₑ
          ∂P (0, ω) ∂Q.measure) ≤
        (ENNReal.ofReal (Real.exp (mu ^ 2 * (Real.exp (2 * Λ₀) * Λ₀) * (U : ℝ))) ^
          (1 / 2 : ℝ) * eLpNorm v 2 (reducedLaw Q)) *
            (volume : Measure ℝ) (Set.Ioc 0 (U : ℝ)))
    (hendpoint : ∀ (t : ℝ≥0), ∀ (v : FieldPair d → ℝ), Measurable v → MemLp v 2 (reducedLaw Q) →
      (∫⁻ ω, ∫⁻ γ : Path d, ‖v (translate (γ t) (reduce ω))‖ₑ
        ∂P (0, ω) ∂Q.measure) ≤
        ENNReal.ofReal (Real.exp (mu ^ 2 * (Real.exp (2 * Λ₀) * Λ₀) * (t : ℝ))) ^
          (1 / 2 : ℝ) * eLpNorm v 2 (reducedLaw Q)) (f g : Lp ℂ 2 (reducedLaw Q))
    (hfg : IsComplexGeneratorPair Q ⟨0, by omega⟩ (mu : ℂ) f g)
    {G : Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hG : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) f G)
    (L : ℂ →L[ℝ] ℝ) :
    ∀ᵐ ω ∂Q.measure,
      (∫ γ : Path d, L (f (translate (γ T) (reduce ω))) ∂P (0, ω)) -
        L (f (reduce ω)) =
      ∫ t in Set.Ioc (0 : ℝ) (T : ℝ), ∫ γ : Path d,
        L (g (translate (γ t.toNNReal) (reduce ω))) ∂P (0, ω) := by
  let W : FieldPair d → ℝ := fun w => L (g w)
  have hWm : Measurable W := L.continuous.measurable.comp (Lp.stronglyMeasurable g).measurable
  have hW : MemLp W 2 (reducedLaw Q) := L.comp_memLp' (Lp.memLp g)
  filter_upwards [s5_gmp_graph_dynkin_of_l2_estimates hd Q mu s h0 h1 hs P hP T hocc hendpoint f g hfg hG L,
    s5_gmp_occupation_fubini_of_l2_estimate hd Q mu h0 h1 P hP T (hocc T) W hWm hW]
    with ω hdyn hfub
  exact hdyn.trans hfub.2


/-- Actual GMP Dynkin identity for a generator pair. -/
theorem s5_gmp_generator_pair_dynkin_of_l2_estimates
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (mu : ℝ) (h0 : 0 ≤ mu) (h1 : mu ≤ 1) (P : QuenchedPathLaws d)
    (hP : IsGMPReducedKernel hd Q.ellipticity_parameter Q mu h0 h1 P)
    (T : ℝ≥0)
    (hocc : ∀ (U : ℝ≥0) (v : FieldPair d → ℝ), Measurable v → MemLp v 2 (reducedLaw Q) →
      (∫⁻ t in Set.Ioc (0 : ℝ) (U : ℝ),
        ∫⁻ ω, ∫⁻ γ : Path d, ‖v (translate (γ t.toNNReal) (reduce ω))‖ₑ
          ∂P (0, ω) ∂Q.measure) ≤
        (ENNReal.ofReal (Real.exp (mu ^ 2 * (Real.exp (2 * Λ₀) * Λ₀) * (U : ℝ))) ^
          (1 / 2 : ℝ) * eLpNorm v 2 (reducedLaw Q)) *
            (volume : Measure ℝ) (Set.Ioc 0 (U : ℝ)))
    (hendpoint : ∀ (t : ℝ≥0), ∀ (v : FieldPair d → ℝ), Measurable v → MemLp v 2 (reducedLaw Q) →
      (∫⁻ ω, ∫⁻ γ : Path d, ‖v (translate (γ t) (reduce ω))‖ₑ
        ∂P (0, ω) ∂Q.measure) ≤
        ENNReal.ofReal (Real.exp (mu ^ 2 * (Real.exp (2 * Λ₀) * Λ₀) * (t : ℝ))) ^
          (1 / 2 : ℝ) * eLpNorm v 2 (reducedLaw Q)) (f g : Lp ℂ 2 (reducedLaw Q))
    (hfg : IsComplexGeneratorPair Q ⟨0, by omega⟩ (mu : ℂ) f g)
    (L : ℂ →L[ℝ] ℝ) :
    ∀ᵐ ω ∂Q.measure,
      (∫ γ : Path d, L (f (translate (γ T) (reduce ω))) ∂P (0, ω)) -
        L (f (reduce ω)) =
      ∫ t in Set.Ioc (0 : ℝ) (T : ℝ), ∫ γ : Path d,
        L (g (translate (γ t.toNNReal) (reduce ω))) ∂P (0, ω) := by
  obtain ⟨G, hG, hform⟩ := hfg
  exact s5_gmp_graph_dynkin_fubini_of_l2_estimates hd Q mu 1 h0 h1 (by norm_num)
    P hP T hocc hendpoint f g ⟨G, hG, hform⟩ hG L



/-- The literal endpoint L²-to-L¹ estimate follows from the actual GMP force change. -/
theorem s5_gmp_literal_endpoint_l2_estimate
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (mu : ℝ) (h0 : 0 ≤ mu) (h1 : mu ≤ 1) (P : QuenchedPathLaws d)
    (hP : IsGMPReducedKernel hd Q.ellipticity_parameter Q mu h0 h1 P)
    (t : ℝ≥0) (v : FieldPair d → ℝ) (hv : Measurable v)
    (hlp : MemLp v 2 (reducedLaw Q)) :
    (∫⁻ ω, ∫⁻ γ : Path d, ‖v (translate (γ t) (reduce ω))‖ₑ
      ∂P (0, ω) ∂Q.measure) ≤
      ENNReal.ofReal (Real.exp (mu ^ 2 * (Real.exp (2 * Λ₀) * Λ₀) * (t : ℝ))) ^
        (1 / 2 : ℝ) * eLpNorm v 2 (reducedLaw Q) := by
  let A : FieldPair d → ℂ := fun w => ((‖v w‖ : ℝ) : ℂ)
  have hA : MemLp A 2 (reducedLaw Q) := hlp.norm.ofReal
  let F : Lp ℂ 2 (reducedLaw Q) := hA.toLp A
  have hAm : Measurable A := Complex.continuous_ofReal.measurable.comp hv.norm
  obtain ⟨P₀, hP₀⟩ := SbxS3Section3R01.joint_reduced_kernel_exists hd Q 0 (by norm_num) (by norm_num)
  obtain ⟨K, hmark, hK⟩ := s5_gmp_origin_markov_version hd Q 0 (by norm_num) (by norm_num) P₀ hP₀
  letI : IsMarkovKernel K := hmark
  have hb := s9_gmp_endpoint_annealed_bound_of_unforced_marginal hd Q mu h0 h1 P₀ P hP₀ hP
    K hK t (s9_gmp_unforced_joint_endpoint_marginal hd Q P₀ hP₀ K hK t) F
  have he := SbxS4Dynkin.ae_eq_at_supplied_endpoint hd Q mu h0 h1 P hP t
    (Lp.stronglyMeasurable F).measurable hAm hA.coeFn_toLp
  have hi := s9_gmp_endpoint_integrable hd Q mu h0 h1 P hP t F
  have hleft : (∫⁻ ω, ∫⁻ γ : Path d, ‖v (translate (γ t) (reduce ω))‖ₑ
      ∂P (0, ω) ∂Q.measure) =
      ∫⁻ ω, ‖∫ γ : Path d, F (translate (γ t) (reduce ω)) ∂P (0, ω)‖ₑ ∂Q.measure := by
    apply lintegral_congr_ae
    filter_upwards [he, hi] with ω heω hiω
    have hreal : Integrable (fun γ : Path d => |v (translate (γ t) (reduce ω))|) (P (0, ω)) := by
      apply (Complex.reCLM.integrable_comp hiω).congr
      filter_upwards [heω] with γ hγ
      simpa only [Complex.reCLM_apply, A, Complex.ofReal_re, Real.norm_eq_abs] using congrArg Complex.re hγ
    have hmean : (∫ γ : Path d, F (translate (γ t) (reduce ω)) ∂P (0, ω)) =
        ((∫ γ : Path d, |v (translate (γ t) (reduce ω))| ∂P (0, ω) : ℝ) : ℂ) := by
      rw [integral_congr_ae heω]
      simpa only [A, Real.norm_eq_abs] using (integral_complex_ofReal)
    rw [hmean]
    have hn : 0 ≤ ∫ γ : Path d, |v (translate (γ t) (reduce ω))| ∂P (0, ω) :=
      integral_nonneg fun _ => abs_nonneg _
    have heqenorm (x : ℝ) : ‖(x : ℂ)‖ₑ = ‖x‖ₑ :=
      enorm_eq_iff_norm_eq.mpr (Complex.norm_real x)
    rw [heqenorm, Real.enorm_eq_ofReal hn,
      ofReal_integral_eq_lintegral_ofReal hreal (ae_of_all _ fun _ => abs_nonneg _)]
    apply lintegral_congr
    intro γ
    exact Real.enorm_eq_ofReal_abs _
  have hright : eLpNorm (fun ρ => F ρ) 2 (reducedLaw Q) = eLpNorm v 2 (reducedLaw Q) := by
    rw [eLpNorm_congr_ae hA.coeFn_toLp]
    apply eLpNorm_congr_norm_ae hA.aestronglyMeasurable hlp.aestronglyMeasurable
    filter_upwards [] with w
    simp only [A, Complex.norm_real, Real.norm_eq_abs, abs_abs]
  rw [hleft]
  simpa only [hright] using hb


/-- Finite-horizon occupation estimate for an actual GMP law. -/
theorem s5_gmp_literal_occupation_l2_estimate
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (mu : ℝ) (h0 : 0 ≤ mu) (h1 : mu ≤ 1) (P : QuenchedPathLaws d)
    (hP : IsGMPReducedKernel hd Q.ellipticity_parameter Q mu h0 h1 P)
    (T : ℝ≥0) (v : FieldPair d → ℝ) (hv : Measurable v)
    (hlp : MemLp v 2 (reducedLaw Q)) :
    (∫⁻ t in Set.Ioc (0 : ℝ) (T : ℝ),
      ∫⁻ ω, ∫⁻ γ : Path d, ‖v (translate (γ t.toNNReal) (reduce ω))‖ₑ
        ∂P (0, ω) ∂Q.measure) ≤
      (ENNReal.ofReal (Real.exp (mu ^ 2 * (Real.exp (2 * Λ₀) * Λ₀) * (T : ℝ))) ^
        (1 / 2 : ℝ) * eLpNorm v 2 (reducedLaw Q)) *
          (volume : Measure ℝ) (Set.Ioc 0 (T : ℝ)) := by
  let C : ℝ≥0∞ := ENNReal.ofReal (Real.exp
    (mu ^ 2 * (Real.exp (2 * Λ₀) * Λ₀) * (T : ℝ))) ^ (1 / 2 : ℝ)
  have hk : 0 ≤ mu ^ 2 * (Real.exp (2 * Λ₀) * Λ₀) := by
    have hΛ : 0 < Λ₀ := lt_of_lt_of_le zero_lt_one Q.ellipticity_parameter
    positivity
  calc
    _ ≤ ∫⁻ _ in Set.Ioc (0 : ℝ) (T : ℝ), C * eLpNorm v 2 (reducedLaw Q) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      apply (s5_gmp_literal_endpoint_l2_estimate hd Q mu h0 h1 P hP t.toNNReal v hv hlp).trans
      apply mul_le_mul' _ le_rfl
      apply ENNReal.rpow_le_rpow _ (by norm_num)
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      apply mul_le_mul_of_nonneg_left _ hk
      simpa only [Real.coe_toNNReal _ (le_of_lt ht.1)] using ht.2
    _ = _ := by rw [lintegral_const, Measure.restrict_apply_univ]

/-- Dynkin identity for an actual GMP law and an L² generator pair. -/
theorem s5_gmp_generator_pair_dynkin
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (mu : ℝ) (h0 : 0 ≤ mu) (h1 : mu ≤ 1) (P : QuenchedPathLaws d)
    (hP : IsGMPReducedKernel hd Q.ellipticity_parameter Q mu h0 h1 P)
    (T : ℝ≥0) (f g : Lp ℂ 2 (reducedLaw Q))
    (hfg : IsComplexGeneratorPair Q ⟨0, by omega⟩ (mu : ℂ) f g)
    (L : ℂ →L[ℝ] ℝ) :
    ∀ᵐ ω ∂Q.measure,
      (∫ γ : Path d, L (f (translate (γ T) (reduce ω))) ∂P (0, ω)) -
        L (f (reduce ω)) =
      ∫ t in Set.Ioc (0 : ℝ) (T : ℝ), ∫ γ : Path d,
        L (g (translate (γ t.toNNReal) (reduce ω))) ∂P (0, ω) := by
  exact s5_gmp_generator_pair_dynkin_of_l2_estimates hd Q mu h0 h1 P hP T
    (fun U v hv hlp => s5_gmp_literal_occupation_l2_estimate hd Q mu h0 h1 P hP U v hv hlp)
    (fun t v hv hlp => s5_gmp_literal_endpoint_l2_estimate hd Q mu h0 h1 P hP t v hv hlp)
    f g hfg L


end EinsteinFull
