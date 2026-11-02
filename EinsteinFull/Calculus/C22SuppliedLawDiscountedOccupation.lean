import EinsteinFull.Calculus.C2ReducedEnvironmentKernel
import EinsteinFull.Calculus.C17UnforcedEnvironmentInvariant
import EinsteinFull.Calculus.C17UnforcedBoundedTests

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal BigOperators Topology

noncomputable section
namespace EinsteinFull
open EinsteinRelation

/-- Bounded nonnegative truncations of an L² observation retain its L² bound. -/
theorem c22_truncation_memLp_bound {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (r : FieldPair d → ℝ) (hm : Measurable r)
    (hr : MemLp r 2 (reducedLaw Q)) (n : ℕ) :
    ∃ ht : MemLp (fun w => min |r w| (n : ℝ)) 2 (reducedLaw Q),
      ‖ht.toLp (fun w => min |r w| (n : ℝ))‖ ≤ ‖hr.toLp r‖ := by
  have hmeas : Measurable (fun w => min |r w| (n : ℝ)) := (continuous_abs.measurable.comp hm).min measurable_const
  have hle : ∀ w, ‖min |r w| (n : ℝ)‖ ≤ ‖r w‖ := by
    intro w
    rw [Real.norm_eq_abs, abs_of_nonneg (le_min (abs_nonneg _) (Nat.cast_nonneg _)),
      Real.norm_eq_abs]
    exact min_le_left _ _
  have ht : MemLp (fun w => min |r w| (n : ℝ)) 2 (reducedLaw Q) :=
    hr.mono hmeas.aestronglyMeasurable (Filter.Eventually.of_forall hle)
  refine ⟨ht, ?_⟩
  rw [Lp.norm_toLp, Lp.norm_toLp]
  exact ENNReal.toReal_mono hr.eLpNorm_ne_top
    (eLpNorm_mono_ae hmeas.aestronglyMeasurable (Filter.Eventually.of_forall hle))

/-- A bound on bounded observations applies uniformly to the L² truncations. -/
theorem c22_truncated_occupation_bound {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (K : Kernel (FieldPair d) (Path d))
    (s C : ℝ) (hC : 0 ≤ C)
    (hbounded : ∀ (r : FieldPair d → ℝ), Measurable r →
      (∃ B : ℝ, ∀ w, |r w| ≤ B) → ∀ hr : MemLp r 2 (reducedLaw Q),
      (∫ p, Real.exp (-s * p.1) * |r (translate (p.2.2 p.1.toNNReal) (reduce p.2.1))|
        ∂((volume.restrict (Set.Ioi 0)).prod (Q.measure ⊗ₘ K))) ≤ C * ‖hr.toLp r‖)
    (r : FieldPair d → ℝ) (hm : Measurable r) (hr : MemLp r 2 (reducedLaw Q))
    (n : ℕ) :
    (∫ p, Real.exp (-s * p.1) *
      |min |r (translate (p.2.2 p.1.toNNReal) (reduce p.2.1))| (n : ℝ)|
      ∂((volume.restrict (Set.Ioi 0)).prod (Q.measure ⊗ₘ K))) ≤ C * ‖hr.toLp r‖ := by
  obtain ⟨ht, hnorm⟩ := c22_truncation_memLp_bound Q r hm hr n
  have hb : ∃ B : ℝ, ∀ w, |min |r w| (n : ℝ)| ≤ B := by
    refine ⟨n, fun w => ?_⟩
    rw [abs_of_nonneg (le_min (abs_nonneg _) (Nat.cast_nonneg _))]
    exact min_le_right _ _
  exact (hbounded _ ((continuous_abs.measurable.comp hm).min measurable_const) hb ht).trans
    (mul_le_mul_of_nonneg_left hnorm hC)

/-- A uniform integral bound on increasing nonnegative functions yields an
integrable limit and the same bound. -/
theorem c22_integrable_of_monotone_integral_bound
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : ℕ → α → ℝ} {F : α → ℝ} {B : ℝ}
    (hf : ∀ n, Integrable (f n) μ) (hF : AEStronglyMeasurable F μ)
    (hnonneg : ∀ n, 0 ≤ᵐ[μ] f n)
    (hmono : ∀ᵐ x ∂μ, Monotone (fun n => f n x))
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (F x)))
    (hbound : ∀ n, (∫ x, f n x ∂μ) ≤ B) :
    Integrable F μ ∧ (∫ x, F x ∂μ) ≤ B := by
  have hFn : 0 ≤ᵐ[μ] F := by
    have hn : ∀ᵐ x ∂μ, ∀ n, 0 ≤ f n x := ae_all_iff.mpr hnonneg
    filter_upwards [hn, hlim] with x hx hl
    exact ge_of_tendsto hl (Filter.Eventually.of_forall hx)
  have hL : Tendsto (fun n => ∫⁻ x, ENNReal.ofReal (f n x) ∂μ) atTop
      (𝓝 (∫⁻ x, ENNReal.ofReal (F x) ∂μ)) := by
    apply lintegral_tendsto_of_tendsto_of_monotone
    · exact fun n => (hf n).aemeasurable.ennreal_ofReal
    · filter_upwards [hmono] with x hx i j hij
      exact ENNReal.ofReal_le_ofReal (hx hij)
    · filter_upwards [hlim] with x hx
      exact ENNReal.continuous_ofReal.tendsto (F x) |>.comp hx
  have hLbound : (∫⁻ x, ENNReal.ofReal (F x) ∂μ) ≤ ENNReal.ofReal B := by
    apply le_of_tendsto hL
    exact Filter.Eventually.of_forall fun n => by
      rw [← ofReal_integral_eq_lintegral_ofReal (hf n) (hnonneg n)]
      exact ENNReal.ofReal_le_ofReal (hbound n)
  have hFi : Integrable F μ := ⟨hF, (hasFiniteIntegral_iff_ofReal hFn).2
    (hLbound.trans_lt ENNReal.ofReal_lt_top)⟩
  exact ⟨hFi, le_of_tendsto (integral_tendsto_of_tendsto_of_monotone hf hFi hmono hlim)
    (Filter.Eventually.of_forall hbound)⟩

/-- Increasing absolute-value truncations converge to the original magnitude. -/
theorem c22_truncation_monotone_tendsto (a b : ℝ) (ha : 0 ≤ a) :
    Monotone (fun n : ℕ => a * min |b| (n : ℝ)) ∧
      Tendsto (fun n : ℕ => a * min |b| (n : ℝ)) atTop (𝓝 (a * |b|)) := by
  constructor
  · intro i j hij
    exact mul_le_mul_of_nonneg_left (min_le_min_left _ (Nat.cast_le.mpr hij)) ha
  · have hevent : ∀ᶠ n : ℕ in atTop, a * min |b| (n : ℝ) = a * |b| := by
      obtain ⟨N, hN⟩ := exists_nat_gt |b|
      filter_upwards [eventually_ge_atTop N] with n hn
      have hle : |b| ≤ (n : ℝ) := (le_of_lt hN).trans (Nat.cast_le.mpr hn)
      rw [min_eq_left hle]
    apply tendsto_const_nhds.congr'
    filter_upwards [hevent] with n hn
    exact hn.symm

/-- Bounded-test estimates give joint integrability and the corresponding bound
for an arbitrary measurable square-integrable observation. -/
theorem c22_discounted_occupation_joint_of_bounded_tests {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (K : Kernel (FieldPair d) (Path d)) [IsMarkovKernel K]
    (s : ℝ) (hs : 0 < s) (C : ℝ) (hC : 0 ≤ C)
    (hbounded : ∀ (r : FieldPair d → ℝ), Measurable r →
      (∃ B : ℝ, ∀ w, |r w| ≤ B) → ∀ hr : MemLp r 2 (reducedLaw Q),
      (∫ p, Real.exp (-s * p.1) * |r (translate (p.2.2 p.1.toNNReal) (reduce p.2.1))|
        ∂((volume.restrict (Set.Ioi 0)).prod (Q.measure ⊗ₘ K))) ≤ C * ‖hr.toLp r‖)
    (r : FieldPair d → ℝ) (hm : Measurable r) (hr : MemLp r 2 (reducedLaw Q)) :
    Integrable (fun p : ℝ × (FieldPair d × Path d) => Real.exp (-s * p.1) *
      |r (translate (p.2.2 p.1.toNNReal) (reduce p.2.1))|)
      ((volume.restrict (Set.Ioi 0)).prod (Q.measure ⊗ₘ K)) ∧
    (∫ p, Real.exp (-s * p.1) * |r (translate (p.2.2 p.1.toNNReal) (reduce p.2.1))|
      ∂((volume.restrict (Set.Ioi 0)).prod (Q.measure ⊗ₘ K))) ≤ C * ‖hr.toLp r‖ := by
  let : IsProbabilityMeasure Q.measure := Q.probability
  let μ := ((volume : Measure ℝ).restrict (Set.Ioi 0)).prod (Q.measure ⊗ₘ K)
  let env : ℝ × (FieldPair d × Path d) → FieldPair d :=
    fun p => translate (p.2.2 p.1.toNNReal) (reduce p.2.1)
  have heval : Continuous (fun p : ℝ × (FieldPair d × Path d) =>
      p.2.2 p.1.toNNReal) :=
    continuous_eval.comp (continuous_snd.snd.prodMk
      (continuous_real_toNNReal.comp continuous_fst))
  have henv : Measurable env :=
    (Probability.continuous_translate.comp
      (heval.prodMk (Probability.continuous_reduce.comp continuous_snd.fst))).measurable
  let f : ℕ → ℝ × (FieldPair d × Path d) → ℝ :=
    fun n p => Real.exp (-s * p.1) * min |r (env p)| (n : ℝ)
  let F : ℝ × (FieldPair d × Path d) → ℝ :=
    fun p => Real.exp (-s * p.1) * |r (env p)|
  have hexp : Measurable (fun p : ℝ × (FieldPair d × Path d) => Real.exp (-s * p.1)) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_fst)).measurable
  have hF : Measurable F := hexp.mul (continuous_abs.measurable.comp (hm.comp henv))
  have hfmeas : ∀ n, Measurable (f n) := fun n =>
    hexp.mul ((continuous_abs.measurable.comp (hm.comp henv)).min measurable_const)
  have hfi : ∀ n, Integrable (f n) μ := by
    intro n
    apply (((integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hs) 0).mul_const (n : ℝ)).comp_fst
      (Q.measure ⊗ₘ K)).mono' (hfmeas n).aestronglyMeasurable
    exact ae_of_all _ fun p => by
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_nonneg _)
        (le_min (abs_nonneg _) (Nat.cast_nonneg _)))]
      exact mul_le_mul_of_nonneg_left (min_le_right _ _) (Real.exp_nonneg _)
  apply c22_integrable_of_monotone_integral_bound (f := f) (F := F) (μ := μ) hfi hF.aestronglyMeasurable
  · intro n
    exact ae_of_all _ fun p => mul_nonneg (Real.exp_nonneg _)
      (le_min (abs_nonneg _) (Nat.cast_nonneg _))
  · exact ae_of_all _ fun p => (c22_truncation_monotone_tendsto _ _ (Real.exp_nonneg _)).1
  · exact ae_of_all _ fun p => (c22_truncation_monotone_tendsto _ _ (Real.exp_nonneg _)).2
  · intro n
    have hn : ∀ x : ℝ, |min |x| (n : ℝ)| = min |x| (n : ℝ) :=
      fun x => abs_of_nonneg (le_min (abs_nonneg x) (Nat.cast_nonneg n))
    simpa only [f, env, μ, hn] using
      c22_truncated_occupation_bound Q K s C hC hbounded r hm hr n

/-- Associate a product time measure with an environment-dependent kernel. -/
theorem c22_prod_compProd_assoc {α β γ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (μ : Measure α) (ν : Measure β) [SFinite μ] [SFinite ν]
    (κ : Kernel β γ) [IsSFiniteKernel κ] :
    (((μ.prod ν) ⊗ₘ Kernel.prodMkLeft α κ).map MeasurableEquiv.prodAssoc) =
      μ.prod (ν ⊗ₘ κ) := by
  have hk : (Kernel.const α ν ⊗ₖ Kernel.prodMkLeft α κ) =
      Kernel.const α (ν ⊗ₘ κ) := by
    ext a s hs
    rw [Kernel.compProd_apply hs]
    simp only [Kernel.const_apply, Kernel.prodMkLeft_apply]
    rw [Measure.compProd_apply hs]
  calc
    _ = (μ ⊗ₘ Kernel.const α ν ⊗ₘ Kernel.prodMkLeft α κ).map
        MeasurableEquiv.prodAssoc := by rw [Measure.compProd_const]
    _ = μ ⊗ₘ (Kernel.const α ν ⊗ₖ Kernel.prodMkLeft α κ) := Measure.compProd_assoc'
    _ = μ.prod (ν ⊗ₘ κ) := by rw [hk, Measure.compProd_const]

/-- Fubini for a nonnegative observation of time, environment, and path. -/
theorem c22_integral_prod_compProd_swap {α β γ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (μ : Measure α) (ν : Measure β) [SFinite μ] [SFinite ν]
    (κ : Kernel β γ) [IsSFiniteKernel κ]
    (F : α × (β × γ) → ℝ) (hpos : ∀ p, 0 ≤ F p)
    (hF : Integrable F (μ.prod (ν ⊗ₘ κ))) :
    (∫ p, F p ∂μ.prod (ν ⊗ₘ κ)) =
      ∫ b, ∫ a, ∫ c, F (a, b, c) ∂κ b ∂μ ∂ν := by
  let G : (α × β) × γ → ℝ := fun p => F (p.1.1, p.1.2, p.2)
  have hG : Integrable G ((μ.prod ν) ⊗ₘ Kernel.prodMkLeft α κ) := by
    apply (integrable_map_equiv MeasurableEquiv.prodAssoc F).mp
    rw [c22_prod_compProd_assoc]
    exact hF
  have hI : Integrable (fun p : α × β => ∫ c, G (p, c) ∂κ p.2) (μ.prod ν) := by
    have h := (Measure.integrable_compProd_iff hG.aestronglyMeasurable).mp hG
    have hnorm : ∀ p, ‖G p‖ = G p := fun p =>
      (Real.norm_eq_abs _).trans (abs_of_nonneg (hpos _))
    simpa only [Kernel.prodMkLeft_apply, hnorm] using h.2
  calc
    _ = ∫ p, G p ∂((μ.prod ν) ⊗ₘ Kernel.prodMkLeft α κ) := by
      rw [← c22_prod_compProd_assoc, integral_map_equiv]
      rfl
    _ = ∫ p, ∫ c, G (p, c) ∂κ p.2 ∂(μ.prod ν) := by
      simpa only [Kernel.prodMkLeft_apply] using Measure.integral_compProd hG
    _ = ∫ b, ∫ a, ∫ c, F (a, b, c) ∂κ b ∂μ ∂ν := by
      exact integral_prod_symm _ hI

/-- The bounded-test estimate extends to square-integrable observations. -/
theorem c22_discounted_occupation_L2_of_bounded_tests {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (K : Kernel (FieldPair d) (Path d)) [IsMarkovKernel K]
    (s : ℝ) (hs : 0 < s) (C : ℝ) (hC : 0 ≤ C)
    (hbounded : ∀ (r : FieldPair d → ℝ), Measurable r →
      (∃ B : ℝ, ∀ w, |r w| ≤ B) → ∀ hr : MemLp r 2 (reducedLaw Q),
      (∫ p, Real.exp (-s * p.1) * |r (translate (p.2.2 p.1.toNNReal) (reduce p.2.1))| ∂((volume.restrict (Set.Ioi 0)).prod (Q.measure ⊗ₘ K))) ≤ C * ‖hr.toLp r‖) :
    ∀ (r : FieldPair d → ℝ), Measurable r → ∀ hr : MemLp r 2 (reducedLaw Q),
      Integrable (fun p : ℝ × (FieldPair d × Path d) => Real.exp (-s * p.1) * |r (translate (p.2.2 p.1.toNNReal) (reduce p.2.1))|) ((volume.restrict (Set.Ioi 0)).prod (Q.measure ⊗ₘ K)) ∧
      (∫ ω, (∫ t : ℝ in Set.Ioi 0, Real.exp (-s*t) * (∫ γ : Path d, |r (translate (γ t.toNNReal) (reduce ω))| ∂K ω)) ∂Q.measure) ≤ C * ‖hr.toLp r‖ := by
  intro r hm hr
  let : IsProbabilityMeasure Q.measure := Q.probability
  obtain ⟨hi, hb⟩ := c22_discounted_occupation_joint_of_bounded_tests Q K s hs C hC hbounded r hm hr
  refine ⟨hi, ?_⟩
  have heq := c22_integral_prod_compProd_swap (volume.restrict (Set.Ioi 0)) Q.measure K
    (fun p : ℝ × (FieldPair d × Path d) => Real.exp (-s * p.1) *
      |r (translate (p.2.2 p.1.toNNReal) (reduce p.2.1))|)
    (fun p => mul_nonneg (Real.exp_nonneg _) (abs_nonneg _)) hi
  simp_rw [integral_const_mul] at heq
  rw [← heq]
  exact hb

/-- Finite-time Dynkin identity for bounded C² tests of the supplied law. -/
theorem c22_reduced_bounded_C2_dynkin {d : ℕ} {Λ₀ : ℝ}
    (hΛ : 0 < Λ₀) {ω : FieldPair d} (hω : IsRegular Λ₀ ω)
    (i : Fin d) {x : Vec d} {P : Measure (Path d)}
    (hP : SolvesMartingaleProblem (External.Draft.svGenerator
      (reducedCoefficient ω) (forcedDrift (reducedCoefficient ω) i 0)) x P)
    (f : Vec d → ℝ) (hf : ContDiff ℝ 2 f)
    (hb : ∃ M : ℝ, 0 ≤ M ∧ ∀ y : Vec d, |f y| ≤ M ∧
      (∀ j : Fin d, |coordinateDerivative j f y| ≤ M) ∧
      ∀ j k : Fin d, |coordinateDerivative k (coordinateDerivative j f) y| ≤ M)
    (T : ℝ≥0) :
    Integrable (fun γ : Path d => ∫ u in Set.Ioc (0 : ℝ) (T : ℝ),
      External.Draft.svGenerator (reducedCoefficient ω)
        (forcedDrift (reducedCoefficient ω) i 0) f (γ u.toNNReal)) P ∧
    (∫ γ : Path d, (∫ u in Set.Ioc (0 : ℝ) (T : ℝ),
      External.Draft.svGenerator (reducedCoefficient ω)
        (forcedDrift (reducedCoefficient ω) i 0) f (γ u.toNNReal)) ∂P) =
      (∫ γ : Path d, f (γ T) ∂P) - f x :=
  c17_reduced_bounded_C2_dynkin hΛ hω i hP f hf hb T

/-- Finite-time weak equation for a horizontal test under the supplied unforced
path kernel: the annealed increment equals the time integral of the annealed
environment generator. -/
theorem c22_unforced_horizontal_core_dynkin
    (hpath : Blueprint.node_eq_u2E_reduced_u2D_generator_u23_pathwiseStmt)
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (K : Kernel (FieldPair d) (Path d)) [IsMarkovKernel K]
    (hK : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ ω 0) 0 (K ω))
    (F : FieldPair d → ℝ) (hF : IsHorizontalTest F) (T : ℝ≥0) :
    (∫ ω, (∫ γ : Path d, F (translate (γ T) (reduce ω)) ∂K ω) ∂Q.measure) -
      (∫ ρ, F ρ ∂reducedLaw Q) =
    ∫ u in Set.Ioc (0 : ℝ) (T : ℝ),
      (∫ ω, (∫ γ : Path d,
        envGenerator hd 0 F (translate (γ u.toNNReal) (reduce ω))
          ∂K ω) ∂Q.measure) := by
  let : IsProbabilityMeasure Q.measure := Q.probability
  have hΛ : 0 < Λ₀ := lt_of_lt_of_le zero_lt_one Q.ellipticity_parameter
  let i : Fin d := ⟨0, by omega⟩
  obtain ⟨Y, _, hY⟩ := foundation_reduced_textbook_kernel hΛ i 0
  have hred : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator i ω 0) 0 (Y (0, ω)) := by
    filter_upwards [Q.regular] with ω hω
    exact c16_reduced_solves_of_textbook_and_averaged_occupation hΛ hω i 0
      (hY ω hω)
      (foundation_reduced_textbook_averaged_occupation_ac_of_two_le hd hΛ hω i 0 (hY ω hω))
  let X : QuenchedPathLaws d := K.comap Prod.snd measurable_snd
  have huniq := reducedOriginLaw_ae_unique_of_pathwise (hpath := pathwiseAt_of_pathwise hpath hd) Q i 0 X Y hK hred
  have hsv : ∀ᵐ ω ∂Q.measure, IsRegular Λ₀ ω ∧ SolvesMartingaleProblem
      (External.Draft.svGenerator (reducedCoefficient ω)
        (forcedDrift (reducedCoefficient ω) i 0)) 0 (K ω) := by
    filter_upwards [huniq, Q.regular] with ω hωeq hω
    change K ω = Y (0, ω) at hωeq
    rw [hωeq]
    exact ⟨hω, hY ω hω⟩
  obtain ⟨M0, M1, M2, hM1, hM2, hM0, -, -⟩ := hF.exists_bounds
  obtain ⟨B, hB0, hB⟩ := exists_abs_envGenerator_le hd 0 hF (Entropy.sourceReducedBound_pos' Λ₀)
  let Φ : FieldPair d → Path d → ℝ → ℝ := fun ω γ u =>
    envGenerator hd 0 F (translate (γ u.toNNReal) (reduce ω))
  have hΦB : ∀ ω, IsRegular Λ₀ ω → ∀ γ u, |Φ ω γ u| ≤ B := fun ω hω γ u =>
    hB (zeroPotentialReducedPair ω) (reduce ω)
      (isRegular_zeroPotentialReducedPair Q.ellipticity_parameter hω) rfl _
  have heval : Continuous (fun p : (FieldPair d × ℝ) × Path d => p.2 p.1.2.toNNReal) :=
    continuous_eval.comp (continuous_snd.prodMk
      (continuous_real_toNNReal.comp (continuous_snd.comp continuous_fst)))
  have henv : Measurable (fun p : (FieldPair d × ℝ) × Path d =>
      translate (p.2 p.1.2.toNNReal) (reduce p.1.1)) :=
    (Probability.continuous_translate.comp
      (heval.prodMk (Probability.continuous_reduce.comp
        (continuous_fst.comp continuous_fst)))).measurable
  have hΦm : Measurable (fun p : (FieldPair d × ℝ) × Path d => Φ p.1.1 p.2 p.1.2) :=
    (measurable_envGenerator hd 0 hF).comp henv
  have hper : ∀ᵐ ω ∂Q.measure,
      (∫ γ : Path d, F (translate (γ T) (reduce ω)) ∂K ω) - F (reduce ω) =
        ∫ u in Set.Ioc (0 : ℝ) (T : ℝ), ∫ γ : Path d, Φ ω γ u ∂K ω := by
    filter_upwards [hsv] with ω ⟨hω, hP⟩
    have hsym : ∀ x j k, (reduce ω).1 x j k = (reduce ω).1 x k j := fun x j k => by
      have := congrFun (congrFun (reducedCoefficient_symm hω x) k) j
      exact (by simpa [Matrix.transpose_apply] using this : reducedCoefficient ω x j k = reducedCoefficient ω x k j)
    obtain ⟨-, hdyn⟩ := c17_horizontal_test_dynkin hΛ hω i hP F hF T
    have hcongr : ∀ (γ : Path d) (u : ℝ), External.Draft.svGenerator (reducedCoefficient ω)
        (forcedDrift (reducedCoefficient ω) i 0) (orbit F (reduce ω)) (γ u.toNNReal) =
        Φ ω γ u := fun γ u =>
      (c17_envGenerator_eq_svGenerator hd (reduce ω) F i hsym _).symm
    simp_rw [hcongr] at hdyn
    have hfin : IsFiniteMeasure (volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ))) :=
      ⟨by rw [Measure.restrict_apply_univ]; simp⟩
    have hint : Integrable (Function.uncurry fun (γ : Path d) (u : ℝ) => Φ ω γ u)
        ((K ω).prod (volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ)))) := by
      refine (integrable_const B).mono'
        (hΦm.comp ((measurable_const.prodMk measurable_snd).prodMk measurable_fst)).aestronglyMeasurable
        (ae_of_all _ fun p => ?_)
      rw [Real.norm_eq_abs]
      exact hΦB ω hω _ _
    have hswap := integral_integral_swap hint
    rw [hswap] at hdyn
    simpa [orbit] using hdyn.symm
  have hFm : Measurable F := hF.1
  have hFb : ∀ w, |F w| ≤ M0 := fun w => by simpa using hM0 w 0
  have hmapF : ∫ ρ, F ρ ∂reducedLaw Q = ∫ ω, F (reduce ω) ∂Q.measure :=
    integral_map Probability.measurable_reduce.aemeasurable hFm.aestronglyMeasurable
  have hF1 : Integrable (fun ω => F (reduce ω)) Q.measure :=
    (integrable_const M0).mono' (hFm.comp Probability.measurable_reduce).aestronglyMeasurable
      (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hFb _)
  have hF2 : Integrable (fun ω => ∫ γ : Path d, F (translate (γ T) (reduce ω)) ∂K ω)
      Q.measure := by
    refine (integrable_const M0).mono' ?_ (ae_of_all _ fun ω => ?_)
    · exact ((hFm.comp (measurable_c2EnvironmentAt (d := d) T)).stronglyMeasurable.integral_kernel_prod_right'
        (κ := K)).aestronglyMeasurable
    · have := norm_integral_le_of_norm_le_const (μ := K ω)
        (f := fun γ : Path d => F (translate (γ T) (reduce ω))) (C := M0)
        (ae_of_all _ fun γ => by rw [Real.norm_eq_abs]; exact hFb _)
      simpa using this
  have hfin : IsFiniteMeasure (volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ))) :=
    ⟨by rw [Measure.restrict_apply_univ]; simp⟩
  let K' : Kernel (FieldPair d × ℝ) (Path d) := K.comap Prod.fst measurable_fst
  have hgm : StronglyMeasurable (fun x : FieldPair d × ℝ => ∫ γ : Path d, Φ x.1 γ x.2 ∂K x.1) :=
    hΦm.stronglyMeasurable.integral_kernel_prod_right' (κ := K')
  have hgint : Integrable (Function.uncurry fun (ω : FieldPair d) (u : ℝ) =>
      ∫ γ : Path d, Φ ω γ u ∂K ω)
      (Q.measure.prod (volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ)))) := by
    refine (integrable_const B).mono' hgm.aestronglyMeasurable ?_
    have hae : ∀ᵐ x ∂(Q.measure.prod (volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ)))),
        IsRegular Λ₀ x.1 :=
      (Measure.quasiMeasurePreserving_fst (μ := Q.measure)
        (ν := volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ)))).ae Q.regular
    refine hae.mono fun x hx => ?_
    have := norm_integral_le_of_norm_le_const (μ := K x.1)
      (f := fun γ : Path d => Φ x.1 γ x.2) (C := B)
      (ae_of_all _ fun γ => by rw [Real.norm_eq_abs]; exact hΦB _ hx _ _)
    simpa [Function.uncurry] using this
  rw [hmapF, ← integral_sub hF2 hF1, integral_congr_ae hper]
  exact integral_integral_swap hgint

end EinsteinFull
