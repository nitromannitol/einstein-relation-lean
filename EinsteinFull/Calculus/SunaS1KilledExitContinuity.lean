import EinsteinFull.Calculus.U8RegularExitTails
import EinsteinFull.Calculus.U6BoundedPhysicalResolvent
import EinsteinRelation.External.GantertSection7Support
import MarkovProcess.Killed.Kernel
import EinsteinFull.Work.W1.StoppedKernelLocalitySupport

open MeasureTheory Filter Topology
open EinsteinRelation EinsteinRelation.Diffusion
open EinsteinRelation.External.GantertSection7Support
open scoped NNReal ENNReal

namespace EinsteinFull

private theorem s1_localityExitTime_eq {d : ℕ} (U : Set (Vec d)) (γ : Path d) :
    localityExitTime U γ = MarkovProcess.ContinuousPath.exitTime U γ := by
  apply le_antisymm
  · apply le_sInf
    rintro _ ⟨t, rfl, ht⟩
    exact iInf_le_of_le t (iInf_le _ ht)
  · apply le_iInf
    intro t
    apply le_iInf
    intro ht
    exact MarkovProcess.ContinuousPath.exitTime_le_of_notMem U γ t ht

private noncomputable def s1ExitHeadTime (n : ℕ) : ℝ≥0 := ((n + 1 : ℕ) : ℝ≥0)⁻¹

private theorem s1_exitHeadTime_pos (n : ℕ) : 0 < s1ExitHeadTime n := by
  dsimp [s1ExitHeadTime]
  positivity

private theorem s1_tendsto_exitHeadTime_zero :
    Tendsto (fun n => (s1ExitHeadTime n : ℝ≥0∞)) atTop (𝓝 0) := by
  have hcast : ∀ n : ℕ, (s1ExitHeadTime n : ℝ≥0∞) = ((n + 1 : ℕ) : ℝ≥0∞)⁻¹ := by
    intro n
    rw [s1ExitHeadTime, ENNReal.coe_inv (by positivity), ENNReal.coe_natCast]
  simpa only [hcast, Function.comp_def] using
    ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1)

/-- For a continuous supplied path started inside an open domain, the probability
of exit by time t tends to zero as t decreases to zero. -/
theorem s1_supplied_killed_exit_probability_tendsto_zero
    {d : ℕ} (hd : 2 ≤ d) (L : ℝ) (hL : 1 ≤ L) (ω : FieldPair d)
    (hω : IsRegular L ω) (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (G : GantertFixedEnvironmentRealization hd L hL ω hω lam h0 h1)
    (U : Set (Vec d)) (hU : IsOpen U) (x : Vec d) (hx : x ∈ U) :
    Filter.Tendsto (fun t : ℝ≥0 =>
      ((G.pathLaw x) {γ | Diffusion.localityExitTime U γ ≤ (t : ℝ≥0∞)}).toReal)
      (𝓝[>] 0) (𝓝 0) := by
  let : ProbabilityTheory.IsMarkovKernel G.pathLaw := G.pathLaw_isMarkovKernel
  let E : ℝ≥0 → Set (Path d) := fun t => {γ | localityExitTime U γ ≤ (t : ℝ≥0∞)}
  have hzero : G.pathLaw x (⋂ t > 0, E t) = 0 := by
    apply measure_mono_null (t := {γ : Path d | γ 0 ≠ x})
    · intro γ hγ hstart
      have hp : 0 < localityExitTime U γ := by
        rw [s1_localityExitTime_eq]
        exact (MarkovProcess.ContinuousPath.exitTime_pos_iff U hU γ).2 (by simpa only [hstart] using hx)
      have hle : localityExitTime U γ ≤ 0 :=
        ge_of_tendsto s1_tendsto_exitHeadTime_zero
          (Eventually.of_forall fun n => Set.mem_iInter.mp
            (Set.mem_iInter.mp hγ _)
            (s1_exitHeadTime_pos n))
      exact hp.not_ge hle
    · exact ae_iff.mp (G.pathLaw_starts_at x)
  have hl := tendsto_measure_biInter_gt (μ := G.pathLaw x) (s := E)
    (fun t _ => (measurableSet_le (measurable_localityExitTime U hU) measurable_const).nullMeasurableSet)
    (fun _ _ _ h γ hγ => hγ.trans (ENNReal.coe_le_coe.mpr h))
    ⟨1, zero_lt_one, measure_ne_top _ _⟩
  have hl' : Tendsto (fun t : ℝ≥0 => G.pathLaw x (E t)) (𝓝[>] 0) (𝓝 0) := by
    simpa only [Function.comp_def, hzero] using hl
  simpa only [ENNReal.toReal_zero, E, Function.comp_def] using (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hl'

/-- The bounded endpoint expectation lost on killing vanishes at small times. -/
theorem s1_supplied_killed_endpoint_error_tendsto_zero
    {d : ℕ} (hd : 2 ≤ d) (L : ℝ) (hL : 1 ≤ L) (ω : FieldPair d)
    (hω : IsRegular L ω) (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (G : GantertFixedEnvironmentRealization hd L hL ω hω lam h0 h1)
    (U : Set (Vec d)) (hU : IsOpen U) (x : Vec d) (hx : x ∈ U)
    (f : BoundedContinuousFunction (Vec d) ℝ) :
    Tendsto (fun t : ℝ≥0 =>
      (∫ γ : Path d, f (γ t) ∂G.pathLaw x) -
      ∫ γ in {γ : Path d | (t : ℝ≥0∞) < localityExitTime U γ},
        f (γ t) ∂G.pathLaw x) (𝓝[>] 0) (𝓝 0) := by
  let : ProbabilityTheory.IsMarkovKernel G.pathLaw := G.pathLaw_isMarkovKernel
  apply squeeze_zero_norm
  · intro t
    have hs : MeasurableSet {γ : Path d | (t : ℝ≥0∞) < localityExitTime U γ} :=
      measurableSet_lt measurable_const (measurable_localityExitTime U hU)
    have hi : Integrable (fun γ : Path d => f (γ t)) (G.pathLaw x) :=
      Integrable.of_bound (f.continuous.comp (continuous_eval_const t)).aestronglyMeasurable
        ‖f‖ (Eventually.of_forall fun γ => f.norm_coe_le_norm (γ t))
    have hb := norm_integral_sub_setIntegral_le
      (μ := G.pathLaw x) (f := fun γ : Path d => f (γ t))
      (Eventually.of_forall fun γ => f.norm_coe_le_norm (γ t)) hs hi
    simpa only [Set.compl_ofPred, not_lt, Measure.real] using hb
  · simpa only [zero_mul] using
      (s1_supplied_killed_exit_probability_tendsto_zero hd L hL ω hω lam h0 h1 G U hU x hx).mul_const ‖f‖

/-- A uniform displacement estimate gives uniform small-time exit control. -/
theorem s1_supplied_killed_exit_probability_locally_uniform_of_displacement
    {d : ℕ} (hd : 2 ≤ d) (L : ℝ) (hL : 1 ≤ L) (ω : FieldPair d)
    (hω : IsRegular L ω) (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (G : GantertFixedEnvironmentRealization hd L hL ω hω lam h0 h1)
    (hdisp : ∀ R : ℝ, 0 < R → ∀ ε : ℝ, 0 < ε →
      ∃ δ : ℝ, 0 < δ ∧ ∀ y : Vec d, ∀ t : ℝ≥0, (t : ℝ) < δ →
        ((G.pathLaw y) {γ | ∃ u : ℝ≥0, u ≤ t ∧
          R ≤ euclideanNorm (γ u - y)}).toReal < ε)
    (U : Set (Vec d)) (hU : IsOpen U) (x : Vec d) (hx : x ∈ U)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ delta rho : ℝ, 0 < delta ∧ 0 < rho ∧
      ∀ y : Vec d, euclideanNorm (y-x) < rho →
      ∀ t : ℝ≥0, (t : ℝ) < delta →
        ((G.pathLaw y) {gamma | Diffusion.localityExitTime U gamma ≤
          (t : ℝ≥0∞)}).toReal < epsilon := by
  let : ProbabilityTheory.IsMarkovKernel G.pathLaw := G.pathLaw_isMarkovKernel
  have hn (v : Vec d) : ‖v‖ ≤ euclideanNorm v := by
    apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr
    intro i
    apply Real.le_sqrt_of_sq_le
    rw [Real.norm_eq_abs, sq_abs]
    change v i ^ 2 ≤ ∑ j : Fin d, v j * v j
    simpa only [pow_two] using
      (Finset.single_le_sum (fun j _ => mul_self_nonneg (v j)) (Finset.mem_univ i))
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hU x hx
  have hr2 : 0 < r / 2 := by linarith
  obtain ⟨delta, hdelta, hdisp'⟩ := hdisp (r / 2) hr2 epsilon hepsilon
  refine ⟨delta, r / 2, hdelta, hr2, ?_⟩
  intro y hy t ht
  apply (ENNReal.toReal_mono (measure_ne_top (G.pathLaw y) _) ?_).trans_lt
    (hdisp' y t ht)
  apply measure_mono
  intro γ hγ
  change localityExitTime U γ ≤ (t : ℝ≥0∞) at hγ
  rw [s1_localityExitTime_eq] at hγ
  have hhit := (MarkovProcess.ContinuousPath.exitTime_le_iff_mem_hitsSetBy U hU t γ).mp hγ
  obtain ⟨u, hu⟩ := hhit
  refine ⟨u, u.property, ?_⟩
  have houtside : r ≤ ‖γ u - x‖ := by
    by_contra h
    apply hu
    apply hball
    simpa only [Metric.mem_ball, dist_eq_norm] using (not_le.mp h)
  have htriangle := norm_add_le (γ u - y) (y - x)
  have hnear : ‖y - x‖ < r / 2 := (hn _).trans_lt hy
  have hbound := hn (γ u - y)
  have heq : γ u - y + (y - x) = γ u - x := by abel
  rw [heq] at htriangle
  linarith

/-- Exit before a short time is uniformly unlikely for starts near an interior point. -/
theorem s1_supplied_killed_exit_probability_locally_uniform
    {d : ℕ} (hd : 2 ≤ d) (L : ℝ) (hL : 1 ≤ L) (ω : FieldPair d)
    (hω : IsRegular L ω) (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (G : GantertFixedEnvironmentRealization hd L hL ω hω lam h0 h1)
    (U : Set (Vec d)) (hU : IsOpen U) (x : Vec d) (hx : x ∈ U)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ delta rho : ℝ, 0 < delta ∧ 0 < rho ∧
      ∀ y : Vec d, euclideanNorm (y-x) < rho →
      ∀ t : ℝ≥0, (t : ℝ) < delta →
        ((G.pathLaw y) {gamma | Diffusion.localityExitTime U gamma ≤
          (t : ℝ≥0∞)}).toReal < epsilon := by
  let : ProbabilityTheory.IsMarkovKernel G.pathLaw := G.pathLaw_isMarkovKernel
  apply s1_supplied_killed_exit_probability_locally_uniform_of_displacement
    hd L hL ω hω lam h0 h1 G ?_ U hU x hx epsilon hepsilon
  intro R hR ε hε
  obtain ⟨C, c, hC, hc, htail⟩ :=
    u8_regular_signed_physical_path_exit_tail hd ω lam L hL hω G.pathLaw
      (u6_arbitrary_supplied_gmp_canonical_FDD hd ω lam L hL hω h0 h1 G)
  have hk : 0 < c * R ^ 2 := by positivity
  have hinv : Tendsto (fun s : ℝ => -(c * R ^ 2) * s⁻¹) (𝓝[>] 0) atBot :=
    tendsto_inv_nhdsGT_zero.const_mul_atTop_of_neg (neg_lt_zero.mpr hk)
  have hlinear : Tendsto (fun s : ℝ => C * s) (𝓝[>] 0) (𝓝 0) := by
    simpa only [mul_zero, id_eq] using
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => C) (𝓝[>] (0 : ℝ)) (𝓝 C)).mul
        (tendsto_id.mono_left nhdsWithin_le_nhds)
  have harg : Tendsto (fun s : ℝ => C * s - c * R ^ 2 / s) (𝓝[>] 0) atBot := by
    simpa only [sub_eq_add_neg, div_eq_mul_inv, neg_mul] using hlinear.add_atBot hinv
  have hlim : Tendsto (fun s : ℝ => C * Real.exp (C * s - c * R ^ 2 / s))
      (𝓝[>] 0) (𝓝 0) := by
    simpa only [mul_zero, Function.comp_def] using (Real.tendsto_exp_atBot.comp harg).const_mul C
  have hevent := hlim.eventually (Iio_mem_nhds hε)
  obtain ⟨δ, hδ, hsmall⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hevent
  change 0 < δ at hδ
  let s : ℝ≥0 := Real.toNNReal (δ / 2)
  have hs : 0 < s := by
    dsimp [s]
    exact Real.toNNReal_pos.mpr (by linarith)
  have hsreal : (s : ℝ) = δ / 2 := Real.coe_toNNReal _ (by linarith)
  have hsmall' : C * Real.exp (C * (s : ℝ) - c * R ^ 2 / (s : ℝ)) < ε := by
    apply hsmall
    rw [hsreal]
    constructor <;> linarith
  refine ⟨(s : ℝ), by exact_mod_cast hs, ?_⟩
  intro y t ht
  have hts : t ≤ s := NNReal.coe_le_coe.mp (le_of_lt ht)
  have hsub : {γ : Path d | ∃ u : ℝ≥0, u ≤ t ∧ R ≤ euclideanNorm (γ u - y)} ⊆
      {γ : Path d | ∃ u : ℝ≥0, u ≤ s ∧ R ≤ euclideanNorm (γ u - y)} := by
    rintro γ ⟨u, hu, hR⟩
    exact ⟨u, hu.trans hts, hR⟩
  have hmeasure := (measure_mono hsub).trans (htail s hs y R hR.le)
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hmeasure
  rw [ENNReal.toReal_ofReal (by positivity)] at hreal
  exact hreal.trans_lt hsmall'

end EinsteinFull
