import EinsteinFull.Calculus.CLTwoSidedMartingale
import EinsteinFull.Calculus.CLQuadraticVariationLinear

/-!
# The annealed covariance of the compensated displacement

The second moment of `e · M_t`, for the compensated displacement `M` of the two-sided process, is
`t E[e · a(0) e]`, the annealed mean of the reduced coefficient at the origin: under each
environment the compensated linear test function has quadratic variation `∫ e · a e` along the
path, and the environment seen from the particle is stationary.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology ENNReal

noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinFull EinsteinRelation

variable {d : ℕ}

theorem reducedCoefficient_translate (y : Vec d) (ω : FieldPair d) (z : Vec d) :
    reducedCoefficient (translate y ω) z = reducedCoefficient ω (y + z) := rfl

theorem tsState_eq_translate_fwd {τ : ℝ} (hτ : 0 ≤ τ) (ω : TwoSidedSpace d) :
    tsState τ ω = translate (tsFwdPath ω τ.toNNReal) (tsState 0 ω) := by
  simp only [tsState, tsFwdPath, ContinuousMap.coe_mk, Real.coe_toNNReal _ hτ]
  rw [translate_add, sub_add_cancel]

theorem dot_sub_right (e u v : Vec d) : dot e (u - v) = dot e u - dot e v := by
  simp only [dot, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem dot_zero_right (e : Vec d) : dot e 0 = 0 := by
  simp [dot]

/-- The reduced generator of a linear function is the drift in that direction. -/
theorem reducedGenerator_dot {ω : FieldPair d} (hs : IsSmoothFieldPair ω) (i : Fin d) (lam : ℝ)
    (e y : Vec d) :
    reducedGenerator i ω lam (fun z => dot e z) y =
      dot e (forcedDrift (reducedCoefficient ω) i lam y) := by
  rw [reducedGenerator_eq_svGenerator hs i lam (contDiff_two_of_top (contDiff_dot e))]
  have h0 : ∀ (c : ℝ) (z : Vec d), fderiv ℝ (fun _ : Vec d => c) z = 0 := fun c z => by simp
  simp only [External.Draft.svGenerator, fderiv_dot_apply, h0, zero_apply, mul_zero,
    Finset.sum_const_zero, zero_add]
  simp only [dot]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

/-- On a smooth environment, `e · compFn` along a path from the origin is the compensated linear
test function `e · y` of the reduced martingale problem. -/
theorem dot_compFn_eq_compensatedTest (hd : 2 ≤ d) {x : FieldPair d} (hs : IsSmoothFieldPair x)
    (t : ℝ≥0) {γ : Path d} (hγ : γ 0 = 0) (e : Vec d) :
    dot e (compFn hd t (x, γ)) =
      compensatedTest (reducedGenerator ⟨0, by omega⟩ x 0) (fun y => dot e y) t γ := by
  have hcov : ∀ y : Vec d, envDrift hd (translate y x) =
      forcedDrift (reducedCoefficient x) ⟨0, by omega⟩ 0 y := by
    intro y
    have h := forcedDrift_reduced_translate (⟨0, by omega⟩ : Fin d) 0 y x
    simp only [envDrift, h, add_zero]
  have hLf : ∀ (k : Fin d) (y : Vec d), reducedGenerator ⟨0, by omega⟩ x 0 (fun y => y k) y =
      forcedDrift (reducedCoefficient x) ⟨0, by omega⟩ 0 y k := fun k y =>
    response_reducedGenerator_coordinate hs _ k 0 y
  have hbc : Continuous fun y : Vec d => forcedDrift (reducedCoefficient x) ⟨0, by omega⟩ 0 y := by
    refine continuous_pi fun k => ?_
    have h := continuous_reducedGenerator_apply hs (⟨0, by omega⟩ : Fin d) 0 (contDiff_apply ℝ ℝ k)
    exact h.congr fun y => hLf k y
  have hF : Continuous fun τ : ℝ => envDrift hd (translate (γ τ.toNNReal) x) := by
    simp_rw [hcov]
    exact hbc.comp (γ.continuous.comp continuous_real_toNNReal)
  have hcomm := (dotCLM e).intervalIntegral_comp_comm
    (hF.intervalIntegrable (μ := volume) 0 (t : ℝ))
  simp only [dotCLM_apply] at hcomm
  have e1 : dot e (compFn hd t (x, γ)) = dot e (γ t) - dot e (∫ τ in (0 : ℝ)..(t : ℝ),
      envDrift hd (translate (γ τ.toNNReal) x)) := by
    simp only [compFn, Real.toNNReal_coe, dot_sub_right]
  rw [e1, ← hcomm]
  simp only [compensatedTest, hγ, dot_zero_right, sub_zero]
  congr 1
  refine intervalIntegral.integral_congr fun τ _ => ?_
  simp only [hcov, reducedGenerator_dot hs]

section Annealed

variable (hd : 2 ≤ d) (D : StructuralData d)
  (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q)
  (hunforced : UnforcedAt hd Q) (hpath : PathwiseAt Q)
  (hap : ∀ᵐ ω ∂Q.measure, ω ∈ aperiodicSet d)
  {K : Kernel (FieldPair d × Vec d) (Path d)} [IsMarkovKernel K]
  (hK : ∀ ω : FieldPair d, IsRegular D.ellipticity ω → ∀ x : Vec d,
    SolvesMartingaleProblem (External.Draft.svGenerator (reducedCoefficient ω)
      (forcedDrift (reducedCoefficient ω) (⟨0, by omega⟩ : Fin d) 0)) x (K (ω, x)))

include hQ hunforced hpath hap hK in
/-- The second moment of `e · M_t` is `t E[e · a(0) e]`. -/
theorem integral_sq_dot_tsComp (e : Vec d) (t : ℝ≥0) :
    ∫ ω, dot e (tsComp hd t ω) ^ 2 ∂tsLaw Q K =
      t * ∫ x, dot e ((reducedCoefficient x 0).mulVec e) ∂Q.measure := by
  have : IsProbabilityMeasure Q.measure := Q.probability
  have := tsLaw_isProbability Q hap K
  have hΛ : 0 < D.ellipticity := lt_of_lt_of_le zero_lt_one Q.ellipticity_parameter
  set B : ℝ := (d : ℝ) * d * (Real.exp (2 * D.ellipticity) * D.ellipticity *
    ((∑ k, |e k|) * (∑ k, |e k|))) with hB
  have hB0 : 0 ≤ B := mul_nonneg (by positivity)
    (mul_nonneg (mul_nonneg (Real.exp_pos _).le hΛ.le) (mul_self_nonneg _))
  have hqb : ∀ x : FieldPair d, IsRegular D.ellipticity x → ∀ y : Vec d,
      |dot e ((reducedCoefficient x y).mulVec e)| ≤ B := by
    intro x hx y
    rw [← carreDuChamp_dot, abs_of_nonneg (carreDuChamp_nonneg hΛ hx _ y)]
    refine carreDuChamp_le hΛ hx (fun z k => ?_) y
    rw [fderiv_dot_apply]
    exact Finset.single_le_sum (f := fun k => |e k|) (fun k _ => abs_nonneg _)
      (Finset.mem_univ k)
  let q : FieldPair d → ℝ := fun x => dot e ((reducedCoefficient x 0).mulVec e)
  have hq : Continuous q := by
    simp only [q, dot, Matrix.mulVec, dotProduct]
    refine continuous_finsetSum _ fun k _ => continuous_const.mul
      (continuous_finsetSum _ fun l _ => ?_)
    exact ((continuous_reducedCoefficient_uncurry k l).comp
      (continuous_id.prodMk continuous_const)).mul continuous_const
  -- the quadratic form clamped at its bound on regular environments
  let hc : FieldPair d → ℝ := fun x => max (-B) (min B (q x))
  have hcm : Measurable hc := (continuous_const.max (continuous_const.min hq)).measurable
  have hcb : ∀ x, |hc x| ≤ B := fun x =>
    abs_le.2 ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩
  have hclamp : ∀ {v : ℝ}, |v| ≤ B → max (-B) (min B v) = v := fun h => by
    rw [min_eq_right (abs_le.1 h).2, max_eq_right (abs_le.1 h).1]
  have hc_tr : ∀ x : FieldPair d, IsRegular D.ellipticity x → ∀ y : Vec d,
      hc (translate y x) = dot e ((reducedCoefficient x y).mulVec e) := by
    intro x hx y
    show max (-B) (min B (dot e ((reducedCoefficient (translate y x) 0).mulVec e))) = _
    rw [reducedCoefficient_translate, add_zero]
    exact hclamp (hqb x hx y)
  have hsplit : ∀ {G : FieldPair d × Path d → ℝ}, Measurable G →
      Integrable G (Q.measure ⊗ₘ originKernel K) →
      ∫ ω, G (tsState 0 ω, tsFwdPath ω) ∂tsLaw Q K =
        ∫ x, ∫ γ, G (x, γ) ∂K (x, 0) ∂Q.measure := by
    intro G hGm hGi
    have h := integral_tsLaw_split_fwd hd D Q hap hK (F₀ := fun _ => 1) measurable_const
      (fun _ => by simp) (Lb := []) (fun _ h => (List.not_mem_nil h).elim) hGm hGi
    simpa only [tsBwdProd, one_mul, chainMean] using h
  -- the two functionals of the forward path
  let G1 : FieldPair d × Path d → ℝ := fun z => dot e (compFn hd t z) ^ 2
  let G2 : FieldPair d × Path d → ℝ := fun z =>
    ∫ s in (0 : ℝ)..(t : ℝ), hc (translate (z.2 s.toNNReal) z.1)
  have hG1m : Measurable G1 :=
    ((contDiff_dot e).continuous.measurable.comp (measurable_compFn hd t)).pow_const 2
  have hmemj : ∀ j, MemLp (fun z => compFn hd t z j) 2 (Q.measure ⊗ₘ originKernel K) := fun j =>
    (memLp_two_iff_integrable_sq
      ((measurable_pi_iff.1 (measurable_compFn hd t) j).aestronglyMeasurable)).2
      (integrable_compFn_compProd hd D Q hQ hK t j).2
  have hG1i : Integrable G1 (Q.measure ⊗ₘ originKernel K) := by
    have hmem : MemLp (fun z => dot e (compFn hd t z)) 2 (Q.measure ⊗ₘ originKernel K) := by
      have h : (fun z => dot e (compFn hd t z)) = fun z => ∑ j, e j * compFn hd t z j := rfl
      rw [h]
      exact memLp_finsetSum _ fun j _ => (hmemj j).const_mul (e j)
    exact hmem.integrable_sq
  have hG2m : Measurable G2 := by
    have hj : Measurable fun p : ℝ × (FieldPair d × Path d) =>
        hc (translate (p.2.2 p.1.toNNReal) p.2.1) := by
      refine hcm.comp (Localization.physicalTranslation_jointlyMeasurable.comp
        (Measurable.prodMk ?_ (measurable_fst.comp measurable_snd)))
      exact (measurable_uncurry_of_continuous_of_measurable
        (u := fun (τ : ℝ) (z : FieldPair d × Path d) => z.2 τ.toNNReal)
        (fun z => z.2.continuous.comp continuous_real_toNNReal)
        fun τ => (continuous_eval_const _).measurable.comp measurable_snd)
    have h := hj.stronglyMeasurable
    simp only [G2, intervalIntegral]
    exact ((h.integral_prod_left' (μ := volume.restrict (Set.Ioc 0 (t : ℝ)))).measurable).sub
      ((h.integral_prod_left' (μ := volume.restrict (Set.Ioc (t : ℝ) 0))).measurable)
  have hG2i : Integrable G2 (Q.measure ⊗ₘ originKernel K) := by
    refine Integrable.of_bound hG2m.aestronglyMeasurable (B * t) (ae_of_all _ fun z => ?_)
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := (t : ℝ)) (C := B)
      (f := fun s : ℝ => hc (translate (z.2 s.toNNReal) z.1))
      (fun s _ => by rw [Real.norm_eq_abs]; exact hcb _)
    rwa [sub_zero, abs_of_nonneg t.coe_nonneg] at this
  -- quenched identification
  have hinner : ∀ᵐ x ∂Q.measure, ∫ γ, G1 (x, γ) ∂K (x, 0) = ∫ γ, G2 (x, γ) ∂K (x, 0) := by
    filter_upwards [Q.regular, hQ] with x hx hsm
    have hP := (reducedGenerator_solves_iff hsm.1 _ 0 0 _).2 (hK x hx 0)
    have : IsProbabilityMeasure (K (x, 0)) := hP.1
    have e1 : ∫ γ, G1 (x, γ) ∂K (x, 0) = ∫ γ, compensatedTest
        (reducedGenerator ⟨0, by omega⟩ x 0) (fun y => dot e y) t γ ^ 2 ∂K (x, 0) := by
      refine integral_congr_ae ?_
      filter_upwards [hP.2.1] with γ hγ
      simp only [G1, dot_compFn_eq_compensatedTest hd hsm.1 t hγ e]
    rw [e1, (integral_sq_compensated_dot hΛ hx hsm.1 _ 0 hP e t).2]
    refine integral_congr_ae (ae_of_all _ fun γ => ?_)
    simp only [pathInt, G2]
    exact intervalIntegral.integral_congr fun s _ => (hc_tr x hx _).symm
  -- stationarity
  have hstate : ∀ ω : TwoSidedSpace d, G2 (tsState 0 ω, tsFwdPath ω) =
      ∫ s in (0 : ℝ)..(t : ℝ), hc (tsState s ω) := by
    intro ω
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [Set.uIcc_of_le t.coe_nonneg] at hs
    simp only [tsState_eq_translate_fwd hs.1 ω]
  have hjoint : Measurable fun p : TwoSidedSpace d × ℝ => hc (tsState p.2 p.1) :=
    hcm.comp (measurable_tsState_joint.comp measurable_swap)
  have hfin : IsFiniteMeasure (volume.restrict (Set.Ioc (0 : ℝ) t)) := by
    constructor
    rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, Real.volume_Ioc]
    exact ENNReal.ofReal_lt_top
  have hint : Integrable (fun p : TwoSidedSpace d × ℝ => hc (tsState p.2 p.1))
      ((tsLaw Q K).prod (volume.restrict (Set.Ioc 0 (t : ℝ)))) :=
    Integrable.of_bound hjoint.aestronglyMeasurable B (ae_of_all _ fun p => by
      rw [Real.norm_eq_abs]
      exact hcb _)
  have hmarg : ∀ s : ℝ, ∫ ω, hc (tsState s ω) ∂tsLaw Q K = ∫ x, hc x ∂Q.measure := by
    intro s
    have h := integral_map (μ := tsLaw Q K) (measurable_tsState s).aemeasurable
      hcm.aestronglyMeasurable
    rw [tsLaw_map_tsState hd D Q hQ hunforced hpath hap hK s] at h
    exact h.symm
  have hreg : ∫ x, hc x ∂Q.measure = ∫ x, q x ∂Q.measure := by
    refine integral_congr_ae ?_
    filter_upwards [Q.regular] with x hx
    exact hclamp (hqb x hx 0)
  calc ∫ ω, dot e (tsComp hd t ω) ^ 2 ∂tsLaw Q K
      = ∫ ω, G1 (tsState 0 ω, tsFwdPath ω) ∂tsLaw Q K := by
        refine integral_congr_ae (ae_of_all _ fun ω => ?_)
        simp only [G1, tsComp_eq_compFn hd t.coe_nonneg]
    _ = ∫ x, ∫ γ, G1 (x, γ) ∂K (x, 0) ∂Q.measure := hsplit hG1m hG1i
    _ = ∫ x, ∫ γ, G2 (x, γ) ∂K (x, 0) ∂Q.measure := integral_congr_ae hinner
    _ = ∫ ω, G2 (tsState 0 ω, tsFwdPath ω) ∂tsLaw Q K := (hsplit hG2m hG2i).symm
    _ = ∫ ω, (∫ s in (0 : ℝ)..(t : ℝ), hc (tsState s ω)) ∂tsLaw Q K := by
        simp only [hstate]
    _ = ∫ s in (0 : ℝ)..(t : ℝ), ∫ ω, hc (tsState s ω) ∂tsLaw Q K := by
        rw [intervalIntegral.integral_of_le t.coe_nonneg]
        simp_rw [intervalIntegral.integral_of_le t.coe_nonneg]
        exact integral_integral_swap hint
    _ = ∫ s in (0 : ℝ)..(t : ℝ), ∫ x, hc x ∂Q.measure := by
        simp only [hmarg]
    _ = t * ∫ x, q x ∂Q.measure := by
        rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul, hreg]

end Annealed

end EinsteinFull.Blueprint
