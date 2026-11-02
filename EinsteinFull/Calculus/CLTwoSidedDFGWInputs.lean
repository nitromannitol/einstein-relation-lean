import EinsteinFull.Calculus.CLTwoSidedForward
import EinsteinFull.Calculus.CLUniformMoments
import EinsteinFull.Calculus.CLReducedCoordinateMartingale

/-!
# The hypotheses of DFGW for the two-sided environment process

The marginal laws of the two-sided process are the environment law, the Markov property holds for
every bounded measurable observable, and the coordinates of the reduced diffusion have second
moments bounded uniformly in the environment, so the displacement between two times is
integrable under the two-sided law.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology ENNReal

noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinFull EinsteinRelation

variable {d : ℕ}

/-- Uniform bound for the drift of the unforced reduced generator. -/
theorem abs_reducedDrift_le {Λ₀ : ℝ} (hΛ : 0 < Λ₀) {ω : FieldPair d} (hω : IsRegular Λ₀ ω)
    (i : Fin d) (y : Vec d) (j : Fin d) :
    |forcedDrift (reducedCoefficient ω) i 0 y j| ≤
      (1 / 2 : ℝ) * (d * Real.toNNReal (Real.exp (2 * Λ₀) * (2 * Λ₀ ^ 2 + Λ₀) * Real.sqrt d)) := by
  have h := abs_forcedDrift_le (reducedCoefficient ω) (reducedCoefficient_lipschitz hΛ hω)
    (abs_reducedCoefficient_le hΛ hω) i 0 y j
  simpa only [abs_zero, zero_mul, add_zero] using h

/-- Second moments of the coordinates of the unforced reduced diffusion, uniformly in the
environment. -/
theorem coordinate_second_moment_uniform {Λ₀ : ℝ} (hΛ : 0 < Λ₀) (i : Fin d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ω : FieldPair d, IsRegular Λ₀ ω → IsSmoothFieldPair ω →
      ∀ P : Measure (Path d), SolvesMartingaleProblem (reducedGenerator i ω 0) 0 P →
        ∀ (u : ℝ≥0) (j : Fin d), Integrable (fun γ : Path d => (γ u j) ^ 2) P ∧
          ∫ γ, (γ u j) ^ 2 ∂P ≤ C * (u + u ^ 2) := by
  have hf : ∀ j : Fin d, ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec d => y j) :=
    fun j => contDiff_apply ℝ ℝ j
  have hG0 : ∀ (j : Fin d) (y : Vec d) (k : Fin d),
      |fderiv ℝ (fun y : Vec d => y j) y (unitVector k)| ≤ 1 := by
    intro j y k
    rw [(hasFDerivAt_apply j y).fderiv]
    simp only [ContinuousLinearMap.proj_apply]
    by_cases h : j = k <;> simp [unitVector, h]
  have hgrow : ∀ (j : Fin d) (y : Vec d), |(fun y : Vec d => y j) y| ≤ 0 + 1 * ‖y‖ :=
    fun j y => by simpa only [zero_add, one_mul, Real.norm_eq_abs] using norm_le_pi_norm y j
  choose B hB0 hB using fun j => lintegral_sq_reduced_le_uniform hΛ i 0 (hf j) (hG0 j)
    (hgrow j) le_rfl zero_le_one
  let Mb : ℝ := (1 / 2 : ℝ) *
    (d * Real.toNNReal (Real.exp (2 * Λ₀) * (2 * Λ₀ ^ 2 + Λ₀) * Real.sqrt d))
  have hMb : 0 ≤ Mb := by positivity
  let Bm : ℝ := ∑ j, B j
  have hBm : ∀ j, B j ≤ Bm := fun j =>
    Finset.single_le_sum (f := B) (fun k _ => hB0 k) (Finset.mem_univ j)
  have hBm0 : 0 ≤ Bm := Finset.sum_nonneg fun k _ => hB0 k
  refine ⟨2 * Bm + 2 * Mb ^ 2, by positivity, fun ω hω hs P hP u j => ?_⟩
  have : IsProbabilityMeasure P := hP.1
  let M : Path d → ℝ := compensatedTest (reducedGenerator i ω 0) (fun y => y j) u
  obtain ⟨B', _, hB'⟩ := response_coordinate_second_moment hΛ hω hs i 0 hP j
  have hMm : MemLp M 2 P := (hB' u).1
  have hMi : Integrable (fun γ => M γ ^ 2) P := hMm.integrable_sq
  have hMint : ∫ γ, M γ ^ 2 ∂P ≤ Bm * u := by
    have h := hB j ω hω hs P hP u
    rw [← ofReal_integral_eq_lintegral_ofReal hMi (ae_of_all _ fun _ => sq_nonneg _)] at h
    exact ((ENNReal.ofReal_le_ofReal_iff (mul_nonneg (hB0 j) u.coe_nonneg)).1 h).trans
      (mul_le_mul_of_nonneg_right (hBm j) u.coe_nonneg)
  have hdecomp : ∀ᵐ γ ∂P, γ u j = M γ +
      ∫ τ in (0 : ℝ)..(u : ℝ), reducedGenerator i ω 0 (fun y => y j) (γ τ.toNNReal) := by
    filter_upwards [hP.2.1] with γ hγ
    simp only [M, compensatedTest, hγ]
    simp
  have hLb : ∀ y, |reducedGenerator i ω 0 (fun y => y j) y| ≤ Mb := by
    intro y
    rw [response_reducedGenerator_coordinate hs i j 0 y]
    exact abs_reducedDrift_le hΛ hω i y j
  have hdrift : ∀ γ : Path d, |∫ τ in (0 : ℝ)..(u : ℝ),
      reducedGenerator i ω 0 (fun y => y j) (γ τ.toNNReal)| ≤ Mb * u := by
    intro γ
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := (u : ℝ))
      (C := Mb) (f := fun τ => reducedGenerator i ω 0 (fun y => y j) (γ τ.toNNReal))
      fun τ _ => by rw [Real.norm_eq_abs]; exact hLb _
    rw [Real.norm_eq_abs, sub_zero, abs_of_nonneg u.coe_nonneg] at h
    exact h
  have hpt : ∀ᵐ γ ∂P, (γ u j) ^ 2 ≤ 2 * M γ ^ 2 + 2 * (Mb * u) ^ 2 := by
    filter_upwards [hdecomp] with γ hγ
    rw [hγ]
    have hd := hdrift γ
    have habs := abs_le.1 hd
    nlinarith [sq_nonneg (M γ - ∫ τ in (0 : ℝ)..(u : ℝ),
      reducedGenerator i ω 0 (fun y => y j) (γ τ.toNNReal))]
  have hRi : Integrable (fun γ => 2 * M γ ^ 2 + 2 * (Mb * u) ^ 2) P :=
    (hMi.const_mul 2).add (integrable_const _)
  have hcont : Continuous fun γ : Path d => (γ u j) ^ 2 :=
    ((continuous_apply j).comp (continuous_eval_const u)).pow 2
  have hint : Integrable (fun γ : Path d => (γ u j) ^ 2) P :=
    Integrable.mono' hRi hcont.aestronglyMeasurable (hpt.mono fun γ hγ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hγ)
  refine ⟨hint, ?_⟩
  calc ∫ γ, (γ u j) ^ 2 ∂P ≤ ∫ γ, (2 * M γ ^ 2 + 2 * (Mb * u) ^ 2) ∂P :=
        integral_mono_ae hint hRi hpt
    _ = 2 * ∫ γ, M γ ^ 2 ∂P + 2 * (Mb * u) ^ 2 := by
        rw [integral_add (hMi.const_mul 2) (integrable_const _), integral_const_mul,
          integral_const, probReal_univ, one_smul]
    _ ≤ 2 * (Bm * u) + 2 * (Mb * u) ^ 2 := by gcongr
    _ ≤ (2 * Bm + 2 * Mb ^ 2) * (u + u ^ 2) := by
        have hu : (0 : ℝ) ≤ u := u.coe_nonneg
        nlinarith [sq_nonneg (u : ℝ), mul_nonneg hBm0 (sq_nonneg (u : ℝ)),
          mul_nonneg (sq_nonneg Mb) hu]


theorem continuous_reducedCoefficient_uncurry (k j : Fin d) :
    Continuous fun p : FieldPair d × Vec d => reducedCoefficient p.1 p.2 k j := by
  have h1 : Continuous fun p : FieldPair d × Vec d => p.1.2 p.2 :=
    continuous_eval.comp ((continuous_snd.comp continuous_fst).prodMk continuous_snd)
  have h2 : Continuous fun p : FieldPair d × Vec d => p.1.1 p.2 :=
    continuous_eval.comp ((continuous_fst.comp continuous_fst).prodMk continuous_snd)
  have h3 : Continuous fun p : FieldPair d × Vec d => p.1.1 p.2 k j :=
    (continuous_apply j).comp ((continuous_apply k).comp h2)
  simp only [reducedCoefficient_apply]
  exact (Real.continuous_exp.comp (continuous_const.mul h1)).mul h3

/-- The drift of the unforced reduced generator at the origin is a measurable function of the
environment. -/
theorem measurable_reducedDrift (i : Fin d) :
    Measurable fun ω : FieldPair d => forcedDrift (reducedCoefficient ω) i 0 0 := by
  refine measurable_pi_iff.2 fun j => ?_
  simp only [forcedDrift, matrixDivDrift, zero_mul, add_zero]
  refine Measurable.const_mul (Finset.measurable_sum _ fun k _ => ?_) _
  have h := measurable_fderiv_apply_const_with_param ℝ
    (f := fun (ω : FieldPair d) (z : Vec d) => reducedCoefficient ω z k j)
    (continuous_reducedCoefficient_uncurry k j) (unitVector k)
  exact h.comp (measurable_id.prodMk measurable_const)


/-- The constant bounding the unforced reduced drift. -/
def driftBound (d : ℕ) (Λ₀ : ℝ) : ℝ :=
  (1 / 2 : ℝ) * (d * Real.toNNReal (Real.exp (2 * Λ₀) * (2 * Λ₀ ^ 2 + Λ₀) * Real.sqrt d))

theorem driftBound_nonneg (Λ₀ : ℝ) : 0 ≤ driftBound d Λ₀ := by
  unfold driftBound
  positivity

/-- DFGW's velocity: the drift of the unforced reduced generator at the origin. -/
def envDrift (hd : 2 ≤ d) (x : FieldPair d) : Vec d :=
  forcedDrift (reducedCoefficient x) ⟨0, by omega⟩ 0 0

theorem measurable_envDrift (hd : 2 ≤ d) : Measurable (envDrift (d := d) hd) :=
  measurable_reducedDrift _

/-- The mean of a coordinate of the unforced reduced diffusion grows at most linearly. -/
theorem abs_integral_coord_le {Λ₀ : ℝ} (hΛ : 0 < Λ₀) {x : FieldPair d} (hx : IsRegular Λ₀ x)
    (hs : IsSmoothFieldPair x) (i : Fin d) {P : Measure (Path d)}
    (hP : SolvesMartingaleProblem (reducedGenerator i x 0) 0 P) (u : ℝ≥0) (j : Fin d) :
    |∫ γ, γ u j ∂P| ≤ driftBound d Λ₀ * u := by
  have : IsProbabilityMeasure P := hP.1
  let f : Vec d → ℝ := fun y => y j
  have hf : ContDiff ℝ (⊤ : ℕ∞) f := contDiff_apply ℝ ℝ j
  let M : Path d → ℝ := compensatedTest (reducedGenerator i x 0) f u
  have hmart := reduced_coordinate_martingale hΛ hx hs i 0 hP j
  have hmean : ∫ γ, M γ ∂P = 0 := by
    have h := hmart.setIntegral_eq (bot_le : (0 : ℝ≥0) ≤ u) MeasurableSet.univ
    simp only [Measure.restrict_univ] at h
    show ∫ γ, compensatedTest (reducedGenerator i x 0) f u γ ∂P = 0
    rw [← h]
    simp [compensatedTest]
  obtain ⟨B', _, hB'⟩ := response_coordinate_second_moment hΛ hx hs i 0 hP j
  have hMi : Integrable M P := (hB' u).1.integrable one_le_two
  have hLc := continuous_reducedGenerator_apply hs i 0 hf
  have hMc : Continuous M := continuous_compensatedTest_path hf.continuous hLc u
  let Dr : Path d → ℝ := fun γ => f (γ u) - f (γ 0) - M γ
  have hDc : Continuous Dr :=
    ((hf.continuous.comp (continuous_eval_const u)).sub
      (hf.continuous.comp (continuous_eval_const 0))).sub hMc
  have hLb : ∀ y, |reducedGenerator i x 0 f y| ≤ driftBound d Λ₀ := by
    intro y
    rw [response_reducedGenerator_coordinate hs i j 0 y]
    exact abs_reducedDrift_le hΛ hx i y j
  have hDb : ∀ γ, |Dr γ| ≤ driftBound d Λ₀ * u := by
    intro γ
    have e : Dr γ = ∫ τ in (0 : ℝ)..(u : ℝ), reducedGenerator i x 0 f (γ τ.toNNReal) := by
      simp only [Dr, M, compensatedTest]
      ring
    rw [e]
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := (u : ℝ))
      (C := driftBound d Λ₀) (f := fun τ => reducedGenerator i x 0 f (γ τ.toNNReal))
      fun τ _ => by rw [Real.norm_eq_abs]; exact hLb _
    rw [Real.norm_eq_abs, sub_zero, abs_of_nonneg u.coe_nonneg] at h
    exact h
  have hDi : Integrable Dr P := Integrable.of_bound hDc.aestronglyMeasurable
    (driftBound d Λ₀ * u) (ae_of_all _ fun γ => by rw [Real.norm_eq_abs]; exact hDb γ)
  have hsplit : ∀ᵐ γ ∂P, γ u j = M γ + Dr γ := by
    filter_upwards [hP.2.1] with γ hγ
    simp only [Dr, f, hγ]
    simp
  rw [integral_congr_ae hsplit, integral_add hMi hDi, hmean, zero_add]
  refine (abs_integral_le_integral_abs).trans ?_
  calc ∫ γ, |Dr γ| ∂P ≤ ∫ _γ, driftBound d Λ₀ * u ∂P :=
        integral_mono hDi.abs (integrable_const _) hDb
    _ = driftBound d Λ₀ * u := by rw [integral_const, probReal_univ, one_smul]

section Annealed

variable (hd : 2 ≤ d) (D : StructuralData d)
  (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q)
  (hunforced : UnforcedAt hd Q) (hpath : PathwiseAt Q)
  (hap : ∀ᵐ ω ∂Q.measure, ω ∈ aperiodicSet d)
  {K : Kernel (FieldPair d × Vec d) (Path d)} [IsMarkovKernel K]
  (hK : ∀ ω : FieldPair d, IsRegular D.ellipticity ω → ∀ x : Vec d,
    SolvesMartingaleProblem (External.Draft.svGenerator (reducedCoefficient ω)
      (forcedDrift (reducedCoefficient ω) (⟨0, by omega⟩ : Fin d) 0)) x (K (ω, x)))

include hap in
theorem tsLaw_map_tsState_zero : (tsLaw Q K).map (tsState 0) = Q.measure := by
  have := apLaw_isProbability Q hap
  rw [tsLaw, Measure.map_map (measurable_tsState 0) measurable_tsGlue]
  have h : (tsState 0 ∘ fun z : aperiodicSet d × (Path d × Path d) => (z.1, gluePath z.2)) =
      Subtype.val ∘ Prod.fst := by
    funext z
    simp [Function.comp, tsState_zero_glue]
  rw [h, ← Measure.map_map measurable_subtype_coe measurable_fst, ← Measure.fst,
    Measure.fst_compProd, map_val_apLaw Q hap]

include hQ hunforced hpath hap hK in
/-- Every marginal of the two-sided process is the environment law. -/
theorem tsLaw_map_tsState (t : ℝ) : (tsLaw Q K).map (tsState t) = Q.measure := by
  have h : tsState (d := d) t = tsState 0 ∘ tsShift t := by
    funext ω
    simp [Function.comp, tsState_shift]
  rw [h, ← Measure.map_map (measurable_tsState 0) (measurable_tsShift t),
    tsLaw_map_tsShift hd D Q hQ hunforced hpath hap hK t, tsLaw_map_tsState_zero D Q hap]

include hap hK in
/-- The Markov property for every bounded measurable observable. -/
theorem tsLaw_condExp_state_bdd (t : ℝ≥0) {f : FieldPair d → ℝ} (hf : Measurable f)
    (hfC : ∃ C, ∀ x, |f x| ≤ C) :
    (tsLaw Q K)[fun ω => f (tsState t ω) | tsPastSigma d] =ᵐ[tsLaw Q K]
      fun ω => ∫ y, f y ∂envKernel K t (tsState 0 ω) := by
  obtain ⟨C, hC⟩ := hfC
  set C' : ℝ := max C 1 with hC'
  have hC'pos : 0 < C' := lt_of_lt_of_le one_pos (le_max_right _ _)
  let g : FieldPair d → ℝ := fun x => f x / C'
  have hg : Measurable g := hf.div_const _
  have hgb : ∀ x, |g x| ≤ 1 := fun x => by
    simp only [g]
    rw [abs_div, abs_of_pos hC'pos, div_le_one hC'pos]
    exact (hC x).trans (le_max_left _ _)
  have h := tsLaw_condExp_state hd D Q hap hK t hg hgb
  have hfg : (fun ω => f (tsState t ω)) = C' • fun ω => g (tsState t ω) := by
    funext ω
    simp only [Pi.smul_apply, smul_eq_mul, g]
    field_simp
  rw [hfg]
  filter_upwards [condExp_smul (μ := tsLaw Q K) C' (fun ω => g (tsState t ω)) (tsPastSigma d),
    h] with ω h1 h2
  rw [h1, Pi.smul_apply, h2, smul_eq_mul, ← integral_const_mul]
  congr 1
  funext y
  simp only [g]
  field_simp


include hQ hunforced hpath hK in
/-- Ergodicity in the state-space form of DFGW (p.790). -/
theorem envKernel_ergodic {A : Set (FieldPair d)} (hA : MeasurableSet A)
    (hinv : ∀ t : ℝ≥0, ∀ᵐ x ∂Q.measure, x ∈ A → envKernel K t x A = 1) :
    Q.measure A = 0 ∨ Q.measure A = 1 := by
  have : IsProbabilityMeasure Q.measure := Q.probability
  let g : FieldPair d → ℝ := A.indicator fun _ => 1
  have hg : Measurable g := measurable_const.indicator hA
  have hgb : ∀ x, |g x| ≤ 1 := fun x => by by_cases h : x ∈ A <;> simp [g, h]
  refine kernelPhys_ergodic hd D Q hQ hunforced hpath hK hA fun t => ?_
  let T : FieldPair d → ℝ := kernelPhysMean K g t
  have hTm : Measurable T := measurable_kernelPhysMean K hg t
  have hTb : ∀ x, |T x| ≤ 1 := abs_kernelPhysMean_le K hgb t
  have hTi : Integrable T Q.measure := Integrable.of_bound hTm.aestronglyMeasurable 1
    (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hTb x)
  have hT0 : ∀ x, 0 ≤ T x := fun x => integral_nonneg fun γ => by
    simp only [g]
    by_cases h : translate (γ t) x ∈ A <;> simp [h]
  have hTA : ∀ x, T x = (envKernel K t x A).toReal := by
    intro x
    have h1 := integral_indicator_one (μ := envKernel K t x) hA
    rw [integral_envKernel K t (f := A.indicator 1) (measurable_one.indicator hA)] at h1
    exact h1
  have h1 : ∀ᵐ x ∂Q.measure, x ∈ A → T x = 1 := by
    filter_upwards [hinv t] with x hx hxA
    rw [hTA, hx hxA, ENNReal.toReal_one]
  have hint : ∫ x, T x ∂Q.measure = (Q.measure A).toReal := by
    rw [integral_kernelPhysMean hd D Q hQ hunforced hpath hK hg hgb t]
    exact integral_indicator_one hA
  have hintA : ∫ x in A, T x ∂Q.measure = (Q.measure A).toReal := by
    rw [setIntegral_congr_ae hA (h1.mono fun x hx hxA => hx hxA), setIntegral_const, smul_eq_mul,
      mul_one]
    rfl
  have hcompl : ∫ x in Aᶜ, T x ∂Q.measure = 0 := by
    have h := integral_add_compl hA hTi
    rw [hint, hintA] at h
    linarith
  have h0 : ∀ᵐ x ∂Q.measure, x ∈ Aᶜ → T x = 0 := by
    have h := (setIntegral_eq_zero_iff_of_nonneg_ae (ae_of_all _ hT0) hTi.integrableOn).1 hcompl
    exact (ae_restrict_iff' hA.compl).1 h
  filter_upwards [h1, h0] with x hx1 hx0
  by_cases hxA : x ∈ A
  · simp only [Set.indicator_of_mem hxA]
    exact hx1 hxA
  · simp only [Set.indicator_of_notMem hxA]
    exact hx0 hxA


private theorem abs_le_sq_add_one (y : ℝ) : |y| ≤ y ^ 2 + 1 := by
  nlinarith [abs_nonneg y, sq_abs y, sq_nonneg (|y| - 1)]

include hQ hK in
/-- The coordinates of the forward path are integrable for the annealed origin law. -/
theorem integrable_coord_compProd (u : ℝ≥0) (j : Fin d) :
    Integrable (fun z : FieldPair d × Path d => z.2 u j) (Q.measure ⊗ₘ originKernel K) := by
  have : IsProbabilityMeasure Q.measure := Q.probability
  have hΛ : 0 < D.ellipticity := lt_of_lt_of_le zero_lt_one Q.ellipticity_parameter
  obtain ⟨C, hC0, hC⟩ := coordinate_second_moment_uniform hΛ (⟨0, by omega⟩ : Fin d)
  have hcont : Continuous fun γ : Path d => γ u j :=
    (continuous_apply j).comp (continuous_eval_const u)
  have hmeas : Measurable fun z : FieldPair d × Path d => z.2 u j :=
    hcont.measurable.comp measurable_snd
  rw [Measure.integrable_compProd_iff hmeas.aestronglyMeasurable]
  have hgood : ∀ᵐ x ∂Q.measure, SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ x 0) 0
      (originKernel K x) ∧ IsRegular D.ellipticity x ∧ IsSmoothFieldPair x := by
    filter_upwards [Q.regular, hQ] with x hx hsm
    exact ⟨(reducedGenerator_solves_iff hsm.1 _ 0 0 _).2 (hK x hx 0), hx, hsm.1⟩
  have hint : ∀ᵐ x ∂Q.measure, Integrable (fun γ : Path d => γ u j) (originKernel K x) := by
    filter_upwards [hgood] with x ⟨hP, hx, hs⟩
    have := hP.1
    obtain ⟨hsq, -⟩ := hC x hx hs _ hP u j
    refine Integrable.mono' (hsq.add (integrable_const 1)) hcont.aestronglyMeasurable
      (ae_of_all _ fun γ => ?_)
    rw [Real.norm_eq_abs]
    exact abs_le_sq_add_one _
  refine ⟨hint, Integrable.of_bound (C := C * (u + u ^ 2) + 1)
    (hmeas.norm.stronglyMeasurable.integral_kernel_prod_right' (κ := originKernel K)).aestronglyMeasurable
    ?_⟩
  filter_upwards [hgood, hint] with x ⟨hP, hx, hs⟩ hix
  have := hP.1
  obtain ⟨hsq, hle⟩ := hC x hx hs _ hP u j
  rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
  calc ∫ γ, ‖γ u j‖ ∂originKernel K x ≤ ∫ γ, ((γ u j) ^ 2 + 1) ∂originKernel K x :=
        integral_mono hix.norm (hsq.add (integrable_const 1)) fun γ => by
          rw [Real.norm_eq_abs]
          exact abs_le_sq_add_one _
    _ = ∫ γ, (γ u j) ^ 2 ∂originKernel K x + 1 := by
        rw [integral_add hsq (integrable_const 1), integral_const, probReal_univ, one_smul]
    _ ≤ C * (u + u ^ 2) + 1 := by linarith

include hQ hunforced hpath hap hK in
/-- The displacement between two times is integrable under the two-sided law (DFGW A.1). -/
theorem integrable_tsDisp {a b : ℝ} (hab : a ≤ b) : Integrable (tsDisp a b) (tsLaw Q K) := by
  have := tsLaw_isProbability Q hap K
  have hshift : tsDisp (d := d) a b = tsDisp 0 (b - a) ∘ tsShift a := by
    funext ω
    simp only [Function.comp, tsDisp_shift, zero_add, sub_add_cancel]
  have h0 : Integrable (tsDisp (d := d) 0 (b - a)) (tsLaw Q K) := by
    refine integrable_pi_iff.2 fun j => ?_
    have hfun : (fun ω => tsDisp (d := d) 0 (b - a) ω j) =
        fun ω => (fun z : FieldPair d × Path d => z.2 (b - a).toNNReal j)
          (tsState 0 ω, tsFwdPath ω) := by
      funext ω
      simp only [tsDisp, tsFwdPath, ContinuousMap.coe_mk, Real.coe_toNNReal _ (sub_nonneg.2 hab)]
    rw [hfun]
    have h := integrable_tsLaw_split_fwd hd D Q hap hK (F₀ := fun _ => 1) measurable_const
      (fun _ => by simp) (Lb := []) (fun _ h => (List.not_mem_nil h).elim)
      (G := fun z : FieldPair d × Path d => z.2 (b - a).toNNReal j)
      (by
        have hc : Continuous fun γ : Path d => γ (b - a).toNNReal j :=
          (continuous_apply j).comp (continuous_eval_const _)
        exact hc.measurable.comp measurable_snd)
      (integrable_coord_compProd hd D Q hQ hK _ j)
    simpa only [tsBwdProd, one_mul] using h
  rw [hshift]
  have hm : Measurable (tsDisp (d := d) 0 (b - a)) := by
    refine measurable_pi_iff.2 fun j => ?_
    exact ((ContinuousMap.measurable_eval _).comp measurable_snd |>.eval).sub
      ((ContinuousMap.measurable_eval _).comp measurable_snd |>.eval)
  rw [← integrable_map_measure hm.aestronglyMeasurable (measurable_tsShift a).aemeasurable,
    tsLaw_map_tsShift hd D Q hQ hunforced hpath hap hK a]
  exact h0


/-- The kernel mean of the forward displacement at time `δ`. -/
def meanDisp (K : Kernel (FieldPair d × Vec d) (Path d)) (δ : ℝ) (x : FieldPair d) : Vec d :=
  fun j => ∫ γ, γ δ.toNNReal j ∂K (x, 0)

theorem measurable_meanDisp (K : Kernel (FieldPair d × Vec d) (Path d)) [IsMarkovKernel K]
    (δ : ℝ) : Measurable (meanDisp K δ) := by
  refine measurable_pi_iff.2 fun j => ?_
  have hc : Continuous fun γ : Path d => γ δ.toNNReal j :=
    (continuous_apply j).comp (continuous_eval_const _)
  exact ((hc.measurable.comp measurable_snd).stronglyMeasurable.integral_kernel_prod_right'
    (κ := originKernel K)).measurable

include hQ hunforced hpath hap hK in
/-- The conditional mean displacement given the past is the kernel mean from the state at time
zero. -/
theorem tsLaw_condExp_disp {δ : ℝ} (hδ : 0 < δ) :
    (tsLaw Q K)[tsDisp 0 δ | tsPastSigma d] =ᵐ[tsLaw Q K]
      fun ω => meanDisp K δ (tsState 0 ω) := by
  have hint := integrable_tsDisp hd D Q hQ hunforced hpath hap hK hδ.le
  have hj : ∀ j : Fin d, ∀ᵐ ω ∂tsLaw Q K,
      ((tsLaw Q K)[tsDisp 0 δ | tsPastSigma d]) ω j = meanDisp K δ (tsState 0 ω) j := by
    intro j
    let T : Vec d →L[ℝ] ℝ := ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) j
    have h1 := T.comp_condExp_comm (m := tsPastSigma d) hint
    have hc : Continuous fun γ : Path d => γ δ.toNNReal j :=
      (continuous_apply j).comp (continuous_eval_const _)
    have h2 := tsLaw_condExp_fwd hd D Q hap hK
      (G := fun z : FieldPair d × Path d => z.2 δ.toNNReal j) (hc.measurable.comp measurable_snd)
      (integrable_coord_compProd hd D Q hQ hK _ j)
    have hfun : (T ∘ tsDisp 0 δ) = fun ω => (fun z : FieldPair d × Path d => z.2 δ.toNNReal j)
        (tsState 0 ω, tsFwdPath ω) := by
      funext ω
      show tsDisp 0 δ ω j = tsFwdPath ω δ.toNNReal j
      simp only [tsDisp, tsFwdPath, ContinuousMap.coe_mk, Real.coe_toNNReal _ hδ.le, Pi.sub_apply]
    rw [hfun] at h1
    filter_upwards [h1, h2] with ω h1 h2
    exact h1.trans h2
  filter_upwards [ae_all_iff.2 hj] with ω hω
  funext j
  exact hω j

include hQ hK in
/-- The mean displacement over a short time, divided by the time, converges in `L¹` to the
drift. -/
theorem tendsto_integral_meanDisp :
    Tendsto (fun δ : ℝ => ∫ x, ‖δ⁻¹ • meanDisp K δ x - envDrift hd x‖ ∂Q.measure) (𝓝[>] 0)
      (𝓝 0) := by
  have : IsProbabilityMeasure Q.measure := Q.probability
  have hΛ : 0 < D.ellipticity := lt_of_lt_of_le zero_lt_one Q.ellipticity_parameter
  have hFm : ∀ δ : ℝ, Measurable fun x => ‖δ⁻¹ • meanDisp K δ x - envDrift hd x‖ := fun δ =>
    (((measurable_meanDisp K δ).const_smul δ⁻¹).sub (measurable_envDrift hd)).norm
  suffices h : Tendsto (fun δ : ℝ => ∫ x, ‖δ⁻¹ • meanDisp K δ x - envDrift hd x‖ ∂Q.measure)
      (𝓝[>] 0) (𝓝 (∫ _x, (0 : ℝ) ∂Q.measure)) by simpa only [integral_zero] using h
  have hgood : ∀ᵐ x ∂Q.measure, SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ x 0) 0
      (K (x, 0)) ∧ IsRegular D.ellipticity x ∧ IsSmoothFieldPair x := by
    filter_upwards [Q.regular, hQ] with x hx hsm
    exact ⟨(reducedGenerator_solves_iff hsm.1 _ 0 0 _).2 (hK x hx 0), hx, hsm.1⟩
  have hB := driftBound_nonneg (d := d) D.ellipticity
  refine tendsto_integral_filter_of_dominated_convergence (fun _ => 2 * driftBound d D.ellipticity)
    (Eventually.of_forall fun δ => (hFm δ).aestronglyMeasurable) ?_ (integrable_const _) ?_
  · filter_upwards [self_mem_nhdsWithin] with δ hδ
    filter_upwards [hgood] with x ⟨hP, hx, hs⟩
    have hδ' : (0 : ℝ) < δ := hδ
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    refine (norm_sub_le _ _).trans ?_
    have h1 : ‖δ⁻¹ • meanDisp K δ x‖ ≤ driftBound d D.ellipticity := by
      refine (pi_norm_le_iff_of_nonneg hB).2 fun j => ?_
      rw [Pi.smul_apply, smul_eq_mul, Real.norm_eq_abs, abs_mul, abs_inv, abs_of_pos hδ']
      have h := abs_integral_coord_le hΛ hx hs _ hP δ.toNNReal j
      rw [Real.coe_toNNReal _ hδ'.le] at h
      calc δ⁻¹ * |meanDisp K δ x j| ≤ δ⁻¹ * (driftBound d D.ellipticity * δ) :=
            mul_le_mul_of_nonneg_left h (inv_nonneg.2 hδ'.le)
        _ = driftBound d D.ellipticity := by field_simp
    have h2 : ‖envDrift hd x‖ ≤ driftBound d D.ellipticity :=
      (pi_norm_le_iff_of_nonneg hB).2 fun j => by
        rw [Real.norm_eq_abs]
        exact abs_reducedDrift_le hΛ hx _ 0 j
    linarith
  · filter_upwards [hgood] with x ⟨hP, hx, hs⟩
    have hlim : Tendsto (fun δ : ℝ => δ⁻¹ • meanDisp K δ x) (𝓝[>] 0) (𝓝 (envDrift hd x)) := by
      refine tendsto_pi_nhds.2 fun j => ?_
      have h := tendsto_mean_displacement_div hΛ hx hs _ 0 hP j
      exact h
    exact tendsto_iff_norm_sub_tendsto_zero.1 hlim

include hQ hunforced hpath hap hK in
/-- DFGW (2.39): the conditional mean forward velocity converges in `L¹` to the drift. -/
theorem tsLaw_velocity :
    Tendsto (fun δ : ℝ => ∫ ω, ‖δ⁻¹ • ((tsLaw Q K)[tsDisp 0 δ | tsPastSigma d]) ω -
      envDrift hd (tsState 0 ω)‖ ∂tsLaw Q K) (𝓝[>] 0) (𝓝 0) := by
  refine Tendsto.congr' ?_ (tendsto_integral_meanDisp hd D Q hQ hK)
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  have hFm : Measurable fun x => ‖δ⁻¹ • meanDisp K δ x - envDrift hd x‖ :=
    (((measurable_meanDisp K δ).const_smul δ⁻¹).sub (measurable_envDrift hd)).norm
  rw [integral_congr_ae ((tsLaw_condExp_disp hd D Q hQ hunforced hpath hap hK hδ).mono
    fun ω hω => by rw [hω])]
  have h := integral_map (μ := tsLaw Q K) (measurable_tsState 0).aemeasurable
    (f := fun x => ‖δ⁻¹ • meanDisp K δ x - envDrift hd x‖)
    (by rw [tsLaw_map_tsState_zero D Q hap]; exact hFm.aestronglyMeasurable)
  rw [tsLaw_map_tsState_zero D Q hap] at h
  exact h

end Annealed

end EinsteinFull.Blueprint
