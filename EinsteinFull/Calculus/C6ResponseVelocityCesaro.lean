import EinsteinFull.Blueprint.G4.node_p_u3A_response_u23_cesaro_u2D_abel
import EinsteinFull.Calculus.C4RealSemigroupAt
import EinsteinFull.Calculus.ComplexSemigroupUniquenessSupport
import EinsteinFull.Calculus.S4MartingaleSllnSupport
import EinsteinRelation.Probability.MeanRate
import EinsteinFull.Calculus.S4CoefficientFamilySupport
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

open MeasureTheory Filter
open scoped Topology NNReal ENNReal
namespace EinsteinFull.Blueprint
open EinsteinRelation
/-- The supplied semigroup has the path interpretation of the canonical evolution.
This uses generator uniqueness and adds no realization assumption on `Y`. -/
theorem response_semigroup_path_expectation
    (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ)
    (Q : EnvironmentLaw d Λ₀ r₀) (hreal : RealSemigroupAt hd Q) (lam : ℝ)
    (P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (hP : IsComplexEnvironmentSemigroup Q (⟨0, by omega⟩ : Fin d) (lam : ℂ) P)
    (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator (⟨0, by omega⟩ : Fin d) ω lam)
        0 (Y (0, ω)))
    (t : ℝ≥0) (f : Lp ℂ 2 (reducedLaw Q)) :
    ∀ᵐ ω ∂Q.measure,
      Integrable (fun γ : Path d => f (translate (γ t) (reduce ω))) (Y (0, ω)) ∧
      P t f (reduce ω) =
        ∫ γ : Path d, f (translate (γ t) (reduce ω)) ∂Y (0, ω) := by
  rw [hP.eq_forcedComplexEvolution]
  exact (hreal lam).2.2.2.2 Y hY t f

/-- Integrating the path interpretation gives the actual quenched expectation,
with the original law on environments and the reduced observation on paths. -/
theorem response_semigroup_mean_path_expectation
    (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ)
    (Q : EnvironmentLaw d Λ₀ r₀) (hreal : RealSemigroupAt hd Q) (lam : ℝ)
    (P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (hP : IsComplexEnvironmentSemigroup Q (⟨0, by omega⟩ : Fin d) (lam : ℂ) P)
    (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator (⟨0, by omega⟩ : Fin d) ω lam)
        0 (Y (0, ω)))
    (t : ℝ≥0) (f : Lp ℂ 2 (reducedLaw Q)) :
    (∫ ω, P t f ω ∂reducedLaw Q) =
      ∫ ω, ∫ γ : Path d, f (translate (γ t) (reduce ω)) ∂Y (0, ω) ∂Q.measure := by
  change (∫ ω, P t f ω ∂Measure.map reduce Q.measure) = _
  rw [integral_map EinsteinRelation.Probability.measurable_reduce.aemeasurable
    (Lp.stronglyMeasurable (P t f)).aestronglyMeasurable]
  exact integral_congr_ae ((response_semigroup_path_expectation
    d hd Λ₀ r₀ Q hreal lam P hP Y hY t f).mono fun _ h => h.2)

/-- The compact-test martingale has zero mean at each time. Extending this
identity to the coordinate function still requires a cutoff limit. -/
theorem response_compensatedTest_mean_zero {d : ℕ}
    {L : (Vec d → ℝ) → Vec d → ℝ} {x : Vec d} {μ : Measure (Path d)}
    (hμ : SolvesMartingaleProblem L x μ)
    (f : Vec d → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfc : HasCompactSupport f)
    (t : ℝ≥0) : ∫ γ, compensatedTest L f t γ ∂μ = 0 := by
  have : IsProbabilityMeasure μ := hμ.1
  have hm := (hμ.2.2 f hf hfc).2.2
  calc
    (∫ γ, compensatedTest L f t γ ∂μ) =
        ∫ γ, (μ[compensatedTest L f t | pathFiltration d 0]) γ ∂μ :=
      (integral_condExp (pathFiltration d |>.le 0)).symm
    _ = ∫ γ, compensatedTest L f 0 γ ∂μ :=
      integral_congr_ae (hm.condExp_ae_eq (show (0 : ℝ≥0) ≤ t from bot_le))
    _ = 0 := by simp [compensatedTest]

/-- The cutoff variance estimate supplies genuine square integrability for
unbounded smooth tests with bounded gradient and linear growth. The constant
may depend on the fixed environment, which suffices for a quenched limit. -/
theorem response_compensatedTest_second_moment {d : ℕ} {Λ₀ : ℝ}
    (hΛ : 0 < Λ₀) {ω : FieldPair d} (hω : IsRegular Λ₀ ω)
    (hs : IsSmoothFieldPair ω) (i : Fin d) (lam : ℝ)
    {μ : Measure (Path d)}
    (hμ : SolvesMartingaleProblem (reducedGenerator i ω lam) 0 μ)
    {f : Vec d → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) {G a b : ℝ}
    (hG : ∀ y j, |fderiv ℝ f y (unitVector j)| ≤ G)
    (hgrow : ∀ y, |f y| ≤ a + b * ‖y‖) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t : ℝ≥0,
      MemLp (compensatedTest (reducedGenerator i ω lam) f t) 2 μ ∧
      (∫ γ, compensatedTest (reducedGenerator i ω lam) f t γ ^ 2 ∂μ) ≤ B * t := by
  obtain ⟨B, hB⟩ := lintegral_sq_reduced_le hΛ hω hs i lam hμ hf hG hgrow ha hb
  refine ⟨max B 0, le_max_right _ _, fun t => ?_⟩
  have hc := continuous_compensatedTest_path hf.continuous
    (continuous_reducedGenerator_apply hs i lam hf) t
  have hnn : 0 ≤ᵐ[μ] (fun γ => compensatedTest (reducedGenerator i ω lam) f t γ ^ 2) :=
    ae_of_all _ fun _ => sq_nonneg _
  have hi : Integrable (fun γ => compensatedTest (reducedGenerator i ω lam) f t γ ^ 2) μ :=
    (lintegral_ofReal_ne_top_iff_integrable (hc.pow 2).aestronglyMeasurable hnn).1
      (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hB t))
  refine ⟨(memLp_two_iff_integrable_sq hc.aestronglyMeasurable).2 hi, ?_⟩
  have hle : ENNReal.ofReal
      (∫ γ, compensatedTest (reducedGenerator i ω lam) f t γ ^ 2 ∂μ) ≤
      ENNReal.ofReal (max B 0 * t) := by
    rw [ofReal_integral_eq_lintegral_ofReal hi hnn]
    exact (hB t).trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (le_max_left _ _) t.coe_nonneg))
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (le_max_right B 0) t.coe_nonneg)).1 hle

/-- The variance estimate applies to each actual coordinate, although a
coordinate is not a compactly supported test function. -/
theorem response_coordinate_second_moment {d : ℕ} {Λ₀ : ℝ}
    (hΛ : 0 < Λ₀) {ω : FieldPair d} (hω : IsRegular Λ₀ ω)
    (hs : IsSmoothFieldPair ω) (i : Fin d) (lam : ℝ)
    {μ : Measure (Path d)}
    (hμ : SolvesMartingaleProblem (reducedGenerator i ω lam) 0 μ) (j : Fin d) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t : ℝ≥0,
      MemLp (compensatedTest (reducedGenerator i ω lam) (fun y => y j) t) 2 μ ∧
      (∫ γ, compensatedTest (reducedGenerator i ω lam) (fun y => y j) t γ ^ 2 ∂μ)
        ≤ B * t := by
  apply response_compensatedTest_second_moment hΛ hω hs i lam hμ
    (contDiff_apply ℝ ℝ j) (G := 1) (a := 0) (b := 1)
  · intro y k
    rw [(hasFDerivAt_apply j y).fderiv]
    simp only [ContinuousLinearMap.proj_apply]
    by_cases h : j = k <;> simp [unitVector, h]
  · intro y
    simpa only [zero_add, one_mul, Real.norm_eq_abs] using norm_le_pi_norm y j
  · exact le_rfl
  · exact zero_le_one

/-- The actual reduced generator applied to a coordinate is its actual drift. -/
theorem response_reducedGenerator_coordinate {d : ℕ} {ω : FieldPair d}
    (hs : IsSmoothFieldPair ω) (i j : Fin d) (lam : ℝ) (y : Vec d) :
    reducedGenerator i ω lam (fun z => z j) y =
      forcedDrift (reducedCoefficient ω) i lam y j := by
  rw [reducedGenerator_eq_svGenerator hs i lam
    (contDiff_two_of_top (contDiff_apply ℝ ℝ j))]
  have he : ∀ z : Vec d, fderiv ℝ (fun x : Vec d => x j) z =
      ContinuousLinearMap.proj j := fun z => (hasFDerivAt_apply j z).fderiv
  simp [External.Draft.svGenerator, he, ContinuousLinearMap.proj_apply,
    unitVector, Pi.single_apply]

/-- The quenched mean of the actual integrated coordinate drift has the
actual velocity as its rate. The martingale variance is proved from the
compact-test martingale problem, rather than assumed as a decomposition. -/
theorem response_quenched_drift_mean_rate {d : ℕ} {Λ₀ : ℝ}
    (hΛ : 0 < Λ₀) {ω : FieldPair d} (hω : IsRegular Λ₀ ω)
    (hs : IsSmoothFieldPair ω) (i : Fin d) (lam : ℝ)
    {μ : Measure (Path d)}
    (hμ : SolvesMartingaleProblem (reducedGenerator i ω lam) 0 μ)
    {v : Vec d} (hv : ∀ᵐ γ ∂μ, HasPathVelocity γ v) (j : Fin d) :
    Tendsto (fun T : ℝ =>
      (∫ γ, (∫ u in (0 : ℝ)..T,
        reducedGenerator i ω lam (fun z => z j) (γ u.toNNReal)) ∂μ) / T)
      atTop (𝓝 (v j)) := by
  have : IsProbabilityMeasure μ := hμ.1
  let b : Vec d → ℝ := reducedGenerator i ω lam (fun z => z j)
  have hbc : Continuous b := continuous_reducedGenerator_apply hs i lam (contDiff_apply ℝ ℝ j)
  obtain ⟨_, _, _, _, _, K, hK⟩ := reduced_svHypotheses hΛ hω i lam
  have hb : ∀ y, |b y| ≤ K := fun y => by
    dsimp only [b]
    rw [response_reducedGenerator_coordinate hs]
    exact hK y j
  obtain ⟨B, _, hB⟩ := response_coordinate_second_moment hΛ hω hs i lam hμ j
  have hMeq : ∀ T : ℝ, 0 ≤ T →
      (fun γ : Path d => (γ T.toNNReal j - pathInt b γ T) ^ 2) =ᵐ[μ]
      (fun γ => compensatedTest (reducedGenerator i ω lam)
        (fun z => z j) T.toNNReal γ ^ 2) := by
    intro T hT
    filter_upwards [hμ.2.1] with γ hγ
    simp [compensatedTest, pathInt, b, hγ, Real.coe_toNNReal T hT]
  have hcoord : ∀ᵐ γ ∂μ, Tendsto (fun T : ℝ => γ T.toNNReal j / T)
      atTop (𝓝 (v j)) := by
    filter_upwards [hv] with γ hγ
    have hc : Tendsto (fun T : ℝ => ((T.toNNReal : ℝ))⁻¹ * γ T.toNNReal j)
        atTop (𝓝 (v j)) := by
      simpa [Function.comp_def] using
        (((continuous_apply j).tendsto v).comp (hγ.comp tendsto_real_toNNReal_atTop))
    apply hc.congr'
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
    simp [Real.coe_toNNReal T hT, div_eq_inv_mul]
  have hprob : ∀ δ : ℝ, 0 < δ → Tendsto (fun T : ℝ =>
      μ.real {γ : Path d | δ ≤ |γ T.toNNReal j / T - v j|}) atTop (𝓝 0) := by
    intro δ hδ
    let S : ℝ → Set (Path d) := fun T => {γ | δ ≤ |γ T.toNNReal j / T - v j|}
    have hS : ∀ T, MeasurableSet (S T) := by
      intro T
      have heval : Continuous (fun γ : Path d => γ T.toNNReal j) :=
        (continuous_apply j).comp (continuous_eval_const T.toNNReal)
      have hc : Continuous (fun γ : Path d => γ T.toNNReal j / T - v j) :=
        (heval.div_const T).sub continuous_const
      exact measurableSet_le measurable_const hc.abs.measurable
    have hlim : Tendsto (fun T => ∫⁻ γ, (S T).indicator (fun _ => (1 : ℝ≥0∞)) γ ∂μ)
        atTop (𝓝 0) := by
      rw [show (0 : ℝ≥0∞) = ∫⁻ (_ : Path d), 0 ∂μ by simp]
      apply tendsto_lintegral_filter_of_dominated_convergence (fun _ => 1)
        (Eventually.of_forall fun T => measurable_one.indicator (hS T))
        (Eventually.of_forall fun T => ae_of_all _ fun γ =>
          Set.indicator_le_self' (fun _ _ => zero_le_one) γ)
        (by simp)
      filter_upwards [hcoord] with γ hγ
      have hev : ∀ᶠ T : ℝ in atTop, |γ T.toNNReal j / T - v j| < δ := by
        simpa only [Real.dist_eq] using (Metric.tendsto_nhds.mp hγ) δ hδ
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hev] with T hT
      exact (Set.indicator_of_notMem (show γ ∉ S T from not_le.mpr hT) _).symm
    have hm : (fun T => ∫⁻ γ, (S T).indicator (fun _ => (1 : ℝ≥0∞)) γ ∂μ) =
        fun T => μ (S T) := by
      funext T
      exact lintegral_indicator_one (hS T)
    rw [hm] at hlim
    simpa only [Measure.real, Function.comp_def, ENNReal.toReal_zero] using
      (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hlim
  apply tendsto_integral_div_of_sq_le
    (fun T γ => γ T.toNNReal j) (fun T γ => pathInt b γ T)
    (B := K) (C := B)
  · intro T
    exact (continuous_pathInt_path hbc T).measurable
  · intro T hT
    exact ae_of_all _ fun γ => abs_pathInt_le hb γ hT
  · intro T hT
    have hi := (memLp_two_iff_integrable_sq
      (continuous_compensatedTest_path (continuous_apply j) hbc
        T.toNNReal).aestronglyMeasurable).1 (hB T.toNNReal).1
    exact hi.congr (hMeq T hT).symm
  · intro T hT
    rw [integral_congr_ae (hMeq T hT)]
    simpa only [Real.coe_toNNReal T hT] using (hB T.toNNReal).2
  · exact hprob

/-- Joint measurability of the bounded coefficient-family time integral. -/
theorem response_measurable_family_pathInt {d : ℕ} (Λ : ℝ) (i : Fin d)
    (lam : ℝ) (j : Fin d) (T : ℝ) :
    Measurable (fun z : FieldPair d × Path d =>
      pathInt (fun y => famB Λ i lam z.1 y j) z.2 T) := by
  have he : Measurable (fun p : ℝ × (FieldPair d × Path d) =>
      (p.2.1, p.2.2 p.1.toNNReal)) :=
    (measurable_fst.comp measurable_snd).prodMk
      ((continuous_pathEval d).measurable.comp
        ((measurable_snd.comp measurable_snd).prodMk measurable_fst))
  have hf := ((measurable_famB Λ i lam j).comp he).stronglyMeasurable
  exact (hf.integral_prod_left' (μ := volume.restrict (Set.Ioc 0 T))).measurable.sub
    (hf.integral_prod_left' (μ := volume.restrict (Set.Ioc T 0))).measurable

/-- An almost surely probabilistic origin law admits an almost surely equal
finite kernel, sufficient for measurable parameterized integration. -/
theorem response_finite_originLaw {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (Y : QuenchedPathLaws d)
    (hprob : ∀ᵐ ω ∂Q.measure, IsProbabilityMeasure (originLaw Y ω)) :
    ∃ κ : ProbabilityTheory.Kernel (FieldPair d) (Path d),
      ProbabilityTheory.IsFiniteKernel κ ∧ ∀ᵐ ω ∂Q.measure, κ ω = Y (0, ω) := by
  classical
  let s : Set (FieldPair d) := {ω | originLaw Y ω Set.univ ≤ 1}
  have hs : MeasurableSet s :=
    measurableSet_le ((originLaw Y).measurable_coe MeasurableSet.univ) measurable_const
  let κ := ProbabilityTheory.Kernel.piecewise hs (originLaw Y) 0
  refine ⟨κ, ⟨⟨1, ENNReal.one_lt_top, fun ω => ?_⟩⟩, ?_⟩
  · dsimp only [κ]
    rw [ProbabilityTheory.Kernel.piecewise_apply]
    split_ifs with h
    · exact h
    · simp
  · filter_upwards [hprob] with ω hω
    have : IsProbabilityMeasure (originLaw Y ω) := hω
    have hmem : ω ∈ s := by simpa only [s, Set.mem_ofPred_eq, measure_univ] using
      (le_refl (1 : ℝ≥0∞))
    exact ite_eq_left hmem

/-- Averaging the quenched drift rate gives the annealed drift rate. The
coefficient-family bound is uniform in the environment and the force is signed. -/
theorem response_annealed_drift_mean_rate {d : ℕ} (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q)
    (i : Fin d) (lam : ℝ) (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator i ω lam) 0 (Y (0, ω)))
    {v : Vec d} (hv : HasQuenchedVelocity Q.measure (originLaw Y) v) (j : Fin d) :
    Tendsto (fun T : ℝ =>
      (∫ ω, ∫ γ, (∫ u in (0 : ℝ)..T,
        reducedGenerator i ω lam (fun z => z j) (γ u.toNNReal))
          ∂Y (0, ω) ∂Q.measure) / T) atTop (𝓝 (v j)) := by
  classical
  have hΛ : 0 < D.ellipticity := zero_lt_one.trans_le D.one_le_ellipticity
  obtain ⟨κ, hfinite, hκ⟩ := response_finite_originLaw Q Y (hY.mono fun _ h => h.1)
  have : ProbabilityTheory.IsFiniteKernel κ := hfinite
  let A : ℝ → FieldPair d → ℝ := fun T ω =>
    (∫ γ, pathInt (fun y => famB D.ellipticity i lam ω y j) γ T ∂κ ω) / T
  have hA : ∀ T, AEStronglyMeasurable (A T) Q.measure := by
    intro T
    have hm := (response_measurable_family_pathInt D.ellipticity i lam j T).stronglyMeasurable
    have hk := hm.integral_kernel_prod_right' (κ := κ)
    exact (hk.measurable.div_const T).aestronglyMeasurable
  have heq : ∀ᵐ ω ∂Q.measure, ∀ T, A T ω =
      (∫ γ, (∫ u in (0 : ℝ)..T,
        reducedGenerator i ω lam (fun z => z j) (γ u.toNNReal)) ∂Y (0, ω)) / T := by
    filter_upwards [Q.regular, hQ, hκ] with ω hreg hsm hκω
    intro T
    dsimp only [A]
    rw [hκω]
    congr 1
    apply integral_congr_ae
    exact ae_of_all _ fun γ => by
      apply intervalIntegral.integral_congr
      intro u _
      simp only [famB, ite_eq_left hreg, response_reducedGenerator_coordinate hsm.1]
  obtain ⟨M, _, hM⟩ := family_bounds hΛ i lam
  have hbound : ∀ᶠ T : ℝ in atTop, ∀ᵐ ω ∂Q.measure, ‖A T ω‖ ≤ |M| := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    filter_upwards [hY, hκ] with ω hω hκω
    have : IsProbabilityMeasure (Y (0, ω)) := hω.1
    have hb : ∀ y, |famB D.ellipticity i lam ω y j| ≤ |M| :=
      fun y => (hM ω y j).trans (le_abs_self M)
    dsimp only [A]
    rw [hκω, norm_div, Real.norm_eq_abs T, abs_of_pos hT]
    apply (div_le_iff₀ hT).2
    simpa only [Measure.real, measure_univ, ENNReal.toReal_one, mul_one] using
      (norm_integral_le_of_norm_le_const
        (μ := Y (0, ω)) (f := fun γ => pathInt
          (fun y => famB D.ellipticity i lam ω y j) γ T) (C := |M| * T)
        (ae_of_all _ fun γ => by
          simpa only [Real.norm_eq_abs] using abs_pathInt_le hb γ hT.le))
  have hlim : ∀ᵐ ω ∂Q.measure, Tendsto (fun T => A T ω) atTop (𝓝 (v j)) := by
    filter_upwards [Q.regular, hQ, hY, hv, heq] with ω hreg hsm hmp hvω heqω
    exact (response_quenched_drift_mean_rate hΛ hreg hsm.1 i lam hmp hvω j).congr
      (fun T => (heqω T).symm)
  have h := tendsto_integral_filter_of_dominated_convergence (fun _ => |M|)
    (Eventually.of_forall hA) hbound (integrable_const _) hlim
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at h
  apply h.congr
  intro T
  rw [← integral_div]
  exact integral_congr_ae (heq.mono fun ω hω => hω T)

/-- Time Fubini for the actual coordinate drift of the supplied martingale law. -/
theorem response_annealed_drift_time_swap {d : ℕ} (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q)
    (i : Fin d) (lam : ℝ) (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator i ω lam) 0 (Y (0, ω)))
    (j : Fin d) {T : ℝ} (hT : 0 ≤ T) :
    (∫ ω, ∫ γ, (∫ u in (0 : ℝ)..T,
      reducedGenerator i ω lam (fun z => z j) (γ u.toNNReal)) ∂Y (0, ω) ∂Q.measure) =
    ∫ u in (0 : ℝ)..T, ∫ ω, ∫ γ,
      reducedGenerator i ω lam (fun z => z j) (γ u.toNNReal) ∂Y (0, ω) ∂Q.measure := by
  obtain ⟨κ, hfinite, hκ⟩ := response_finite_originLaw Q Y (hY.mono fun _ h => h.1)
  have : ProbabilityTheory.IsFiniteKernel κ := hfinite
  let J := Q.measure.compProd κ
  let f : (FieldPair d × Path d) → ℝ → ℝ := fun z u =>
    famB D.ellipticity i lam z.1 (z.2 u.toNNReal) j
  have hf : Measurable (Function.uncurry f) :=
    (measurable_famB D.ellipticity i lam j).comp
      ((measurable_fst.comp measurable_fst).prodMk
        ((continuous_pathEval d).measurable.comp
          ((measurable_snd.comp measurable_fst).prodMk measurable_snd)))
  have hΛ : 0 < D.ellipticity := zero_lt_one.trans_le D.one_le_ellipticity
  obtain ⟨M, _, hM⟩ := family_bounds hΛ i lam
  have hb : ∀ z u, |f z u| ≤ |M| :=
    fun z u => (hM z.1 (z.2 u.toNNReal) j).trans (le_abs_self M)
  have : IsFiniteMeasure (volume.restrict (Set.Ioc (0 : ℝ) T)) := by
    rw [isFiniteMeasure_restrict]
    exact measure_Ioc_lt_top.ne
  have hint : Integrable (Function.uncurry f)
      (J.prod (volume.restrict (Set.Ioc (0 : ℝ) T))) :=
    (integrable_const |M|).mono' hf.aestronglyMeasurable
      (ae_of_all _ fun p => by simpa only [Real.norm_eq_abs, Function.uncurry] using hb p.1 p.2)
  have hprim : Integrable (fun z : FieldPair d × Path d =>
      pathInt (fun y => famB D.ellipticity i lam z.1 y j) z.2 T) J :=
    (integrable_const (|M| * T)).mono'
      (response_measurable_family_pathInt D.ellipticity i lam j T).aestronglyMeasurable
      (ae_of_all _ fun z => by
        rw [Real.norm_eq_abs]
        exact abs_pathInt_le (fun y => (hM z.1 y j).trans (le_abs_self M)) z.2 hT)
  have hp : ∀ u, Integrable (fun z => f z u) J := fun u =>
    (integrable_const |M|).mono'
      (hf.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
      (ae_of_all _ fun z => by simpa only [Real.norm_eq_abs] using hb z u)
  have heq : ∀ᵐ ω ∂Q.measure, κ ω = Y (0, ω) ∧ ∀ y,
      famB D.ellipticity i lam ω y j = reducedGenerator i ω lam (fun z => z j) y := by
    filter_upwards [Q.regular, hQ, hκ] with ω hreg hsm hκω
    exact ⟨hκω, fun y => by
      simp only [famB, ite_eq_left hreg, response_reducedGenerator_coordinate hsm.1]⟩
  calc
    _ = ∫ z, pathInt (fun y => famB D.ellipticity i lam z.1 y j) z.2 T ∂J := by
      rw [Measure.integral_compProd hprim]
      apply integral_congr_ae
      filter_upwards [heq] with ω hω
      rw [hω.1]
      apply integral_congr_ae
      exact ae_of_all _ fun γ => by simp only [pathInt, hω.2]
    _ = ∫ u in (0 : ℝ)..T, ∫ z, f z u ∂J := by
      simpa only [pathInt, intervalIntegral.integral_of_le hT] using integral_integral_swap hint
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro u _
      change (∫ z, f z u ∂Q.measure.compProd κ) = _
      rw [Measure.integral_compProd (hp u)]
      apply integral_congr_ae
      filter_upwards [heq] with ω hω
      rw [hω.1]
      apply integral_congr_ae
      exact ae_of_all _ fun γ => hω.2 _

/-- The actual drift primitive has the complex Cesàro normalization required
by the response formula, for every signed force and every supplied velocity. -/
theorem response_complex_drift_primitive_cesaro {d : ℕ} (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q)
    (i : Fin d) (lam : ℝ) (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator i ω lam) 0 (Y (0, ω)))
    {v : Vec d} (hv : HasQuenchedVelocity Q.measure (originLaw Y) v) (j : Fin d) :
    Tendsto (fun T : ℝ => (T : ℂ)⁻¹ *
      ∫ u in (0 : ℝ)..T, ∫ ω, ∫ γ,
        (reducedGenerator i ω lam (fun z => z j) (γ u.toNNReal) : ℂ)
          ∂Y (0, ω) ∂Q.measure) atTop (𝓝 (v j : ℂ)) := by
  have hr : Tendsto (fun T : ℝ =>
      (∫ u in (0 : ℝ)..T, ∫ ω, ∫ γ,
        reducedGenerator i ω lam (fun z => z j) (γ u.toNNReal)
          ∂Y (0, ω) ∂Q.measure) / T) atTop (𝓝 (v j)) := by
    apply (response_annealed_drift_mean_rate D Q hQ i lam Y hY hv j).congr'
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
    exact congrArg (fun x : ℝ => x / T)
      (response_annealed_drift_time_swap D Q hQ i lam Y hY j hT)
  have h := Complex.continuous_ofReal.continuousAt.tendsto.comp hr
  simpa only [Function.comp_def, Complex.ofReal_div, div_eq_mul_inv,
    mul_comm, integral_complex_ofReal, intervalIntegral.integral_ofReal,
    Complex.ofReal_mul, Complex.ofReal_inv] using h

/- SUPERVISOR EXACT CONTRACT (not a declaration/proof):
theorem response_velocity_cesaro_of_rate
    (hreal : node_e_u3A_generators_u23_real_u2D_semigroupStmt)
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (hQ : HasSmoothBounds D Q)
    (β : Fin d → Lp ℂ 2 (reducedLaw Q))
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q))
    (hβ : IsReducedDriftObservation Q hQ β)
    (ha : IsReducedCoefficientObservation Q a)
    (lam : ℝ)
    (P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (hP : IsComplexEnvironmentSemigroup Q (⟨0, by omega⟩ : Fin d) (lam : ℂ) P)
    (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator (⟨0, by omega⟩ : Fin d) ω lam)
        0 (Y (0, ω)))
    (velocity : Vec d)
    (hv : HasQuenchedVelocity Q.measure (originLaw Y) velocity) :
    ∀ i : Fin d,
      Tendsto (fun T : ℝ => (T : ℂ)⁻¹ *
        ∫ t in (0 : ℝ)..T, ∫ ω,
          (P t.toNNReal (β i + (lam : ℂ) • a (⟨0, by omega⟩ : Fin d) i)) ω
            ∂reducedLaw Q) atTop (𝓝 (velocity i : ℂ))
-/
end EinsteinFull.Blueprint
