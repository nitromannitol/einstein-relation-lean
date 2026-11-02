import EinsteinFull.Calculus.U3ForcedMPTransport
import EinsteinFull.Calculus.U3RealForceBoundedTests
import EinsteinFull.Calculus.U3RealForceQuenchedAction
import MarkovProcess.Path.OptionalStopping
import Mathlib.Analysis.Calculus.DSlope
import EinsteinFull.Work.W4.HomogeneousForwardPairingTimeDerivativeSupport

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology BigOperators

namespace EinsteinFull
open EinsteinRelation EinsteinRelation.External.GantertSection7Support

/-- The signed exponential weight of the supplied zero-force law has unit mass. -/
theorem s8_reduced_force_exponential_weight_integral {d : ℕ}
    (hd : 1 ≤ d) {Λ₀ : ℝ} (hΛ : 0 < Λ₀)
    {ω : FieldPair d} (hω : IsRegular Λ₀ ω) (i : Fin d) (lam : ℝ)
    {x : Vec d} {P : Measure (Path d)}
    (hP : SolvesMartingaleProblem
      (External.Draft.svGenerator (reducedCoefficient ω)
        (forcedDrift (reducedCoefficient ω) i 0)) x P) (T : ℝ≥0) :
    let Z : Path d → ℝ := fun γ => Real.exp
      (lam * ((γ T) i - x i) - ∫ u in Set.Ioc (0 : ℝ) (T : ℝ),
        (lam * forcedDrift (reducedCoefficient ω) i 0 (γ u.toNNReal) i +
          (lam ^ 2 / 2) * reducedCoefficient ω (γ u.toNNReal) i i))
    Integrable Z P ∧ (∫ γ, Z γ ∂P) = 1 :=
  c27_reduced_force_exponential_weight_integral hd hΛ hω i lam hP T

/-- The signed exponential weight has equal integrals on every past event. -/
theorem s8_reduced_force_exponential_weight_event_martingale {d : ℕ}
    (hd : 1 ≤ d) {Λ₀ : ℝ} (hΛ : 0 < Λ₀)
    {ω : FieldPair d} (hω : IsRegular Λ₀ ω) (i : Fin d) (lam : ℝ)
    {x : Vec d} {P : Measure (Path d)}
    (hP : SolvesMartingaleProblem
      (External.Draft.svGenerator (reducedCoefficient ω)
        (forcedDrift (reducedCoefficient ω) i 0)) x P) (s t : ℝ≥0) (hst : s ≤ t)
    (A : Set (Path d)) (hA : MeasurableSet[(pathFiltration d) s] A) :
    let Z : ℝ≥0 → Path d → ℝ := fun T γ => Real.exp
      (lam * ((γ T) i - x i) - ∫ u in Set.Ioc (0 : ℝ) (T : ℝ),
        (lam * forcedDrift (reducedCoefficient ω) i 0 (γ u.toNNReal) i +
          (lam ^ 2 / 2) * reducedCoefficient ω (γ u.toNNReal) i i))
    Integrable (Z t) P ∧ Integrable (Z s) P ∧
      (∫ γ in A, Z t γ ∂P) = ∫ γ in A, Z s γ ∂P := by
  exact ⟨(s8_reduced_force_exponential_weight_integral hd hΛ hω i lam hP t).1,
    (s8_reduced_force_exponential_weight_integral hd hΛ hω i lam hP s).1,
    u3_reduced_force_density_integral_on_past_event hd hΛ hω i hP lam s t hst A hA⟩

/-- The signed weight at a bounded stopping time is integrable. -/
theorem s8_reduced_force_exponential_weight_stopped_integrable {d : ℕ}
    (hd : 1 ≤ d) {Λ₀ : ℝ} (hΛ : 0 < Λ₀)
    {ω : FieldPair d} (hω : IsRegular Λ₀ ω) (i : Fin d) (lam : ℝ)
    {x : Vec d} {P : Measure (Path d)}
    (hP : SolvesMartingaleProblem
      (External.Draft.svGenerator (reducedCoefficient ω)
        (forcedDrift (reducedCoefficient ω) i 0)) x P) (T : Path d → ℝ≥0)
    (hT : IsStoppingTime (MarkovProcess.ContinuousPath.canonicalFiltration (alpha := Vec d))
      (fun γ => (T γ : WithTop ℝ≥0)))
    (b : ℝ≥0) (hTb : ∀ γ, T γ ≤ b) :
    Integrable (fun γ => Real.exp
      (lam * ((γ (T γ)) i - x i) - ∫ u in Set.Ioc (0 : ℝ) (T γ : ℝ),
        (lam * forcedDrift (reducedCoefficient ω) i 0 (γ u.toNNReal) i +
          (lam ^ 2 / 2) * reducedCoefficient ω (γ u.toNNReal) i i))) P := by
  obtain ⟨hVm, K, hK⟩ := c2_reduced_force_potential_measurable_bounded hΛ hω i lam
  have ht : Measurable T := by
    have ht' : Measurable[hT.measurableSpace] T := by
      simpa only [Function.comp_def, WithTop.untopD_coe] using
        (WithTop.measurable_untopD (0 : ℝ≥0)).comp hT.measurable
    exact ht'.mono hT.measurableSpace_le le_rfl
  have hw := (c2_path_weight_joint_measurable hVm hK).comp
    ((measurable_coe_nnreal_real.comp ht).prodMk measurable_id)
  have hc : Measurable (fun γ : Path d => (γ (T γ)) i) :=
    (measurable_pi_apply i).comp ((continuous_fst.eval continuous_snd).measurable.comp
      (measurable_id.prodMk ht))
  have hm : Measurable (fun γ : Path d => Real.exp
      (lam * ((γ (T γ)) i - x i) - ∫ u in Set.Ioc (0 : ℝ) (T γ : ℝ),
        (lam * forcedDrift (reducedCoefficient ω) i 0 (γ u.toNNReal) i +
          (lam ^ 2 / 2) * reducedCoefficient ω (γ u.toNNReal) i i))) := by
    have heq : (fun γ : Path d => Real.exp
        (lam * ((γ (T γ)) i - x i) - ∫ u in Set.Ioc (0 : ℝ) (T γ : ℝ),
          (lam * forcedDrift (reducedCoefficient ω) i 0 (γ u.toNNReal) i +
            (lam ^ 2 / 2) * reducedCoefficient ω (γ u.toNNReal) i i))) =
        (fun γ : Path d => Real.exp (lam * ((γ (T γ)) i - x i)) *
          Real.exp (-(∫ u in Set.Ioc (0 : ℝ) (T γ : ℝ),
            (lam * forcedDrift (reducedCoefficient ω) i 0 (γ u.toNNReal) i +
              (lam ^ 2 / 2) * reducedCoefficient ω (γ u.toNNReal) i i)))) := by
      funext γ
      rw [← Real.exp_add]
      congr 1
    rw [heq]
    have he : Measurable (fun γ : Path d => Real.exp (lam * ((γ (T γ)) i - x i))) :=
      Real.measurable_exp.comp (measurable_const.mul (hc.sub measurable_const))
    simp only [Function.comp_def, Real.toNNReal_coe, id_eq] at hw
    exact he.mul hw
  obtain ⟨H, hH, hbound⟩ := u3_reduced_force_density_horizon_majorant hd hΛ hω i hP lam b
  refine hH.mono' hm.aestronglyMeasurable (Filter.Eventually.of_forall fun γ => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact hbound (T γ) (hTb γ) γ

/-- Optional stopping under an integrable horizon majorant. -/
theorem s8_integral_stopped_of_majorant {Ω : Type*} {m : MeasurableSpace Ω}
    {μ : Measure Ω} [IsFiniteMeasure μ] {F : Filtration ℝ≥0 m}
    {M : ℝ≥0 → Ω → ℝ} (hM : Martingale M F μ)
    (hright : ∀ ω v, ContinuousWithinAt (fun t => M t ω) (Set.Ici v) v)
    {T : Ω → ℝ≥0} (hT : IsStoppingTime F (fun ω => (T ω : WithTop ℝ≥0)))
    {b : ℝ≥0} (hTb : ∀ ω, T ω ≤ b)
    {H : Ω → ℝ} (hH : Integrable H μ)
    (hbound : ∀ t ≤ b + 1, ∀ ω, ‖M t ω‖ ≤ H ω) :
    ∫ ω, M (T ω) ω ∂μ = ∫ ω, M (b + 1) ω ∂μ := by
  have hceil (n : ℕ) : ∀ ω, MarkovProcess.dyadicCeiling n (T ω) ≤ b + 1 := by
    intro ω
    have hinv : ((2 : ℝ≥0) ^ n)⁻¹ ≤ 1 := by
      rw [← NNReal.coe_le_coe, NNReal.coe_inv, NNReal.coe_pow, NNReal.coe_ofNat, NNReal.coe_one]
      exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
    exact (MarkovProcess.dyadicCeiling_le_add n (T ω)).trans (add_le_add (hTb ω) hinv)
  have hfin (n : ℕ) : (Set.range fun ω => MarkovProcess.dyadicCeiling n (T ω)).Finite := by
    refine Set.Finite.subset ((Set.finite_Iic (⌈(2 ^ n : ℝ) * (b : ℝ)⌉₊)).image
      (MarkovProcess.dyadicGrid n)) ?_
    rintro _ ⟨ω, rfl⟩
    refine ⟨⌈(2 ^ n : ℝ) * (T ω : ℝ)⌉₊, Set.mem_Iic.mpr (Nat.ceil_le_ceil ?_), rfl⟩
    exact mul_le_mul_of_nonneg_left (NNReal.coe_le_coe.mpr (hTb ω)) (by positivity : (0 : ℝ) ≤ 2 ^ n)
  have hstep (n : ℕ) : (∫ ω, M (MarkovProcess.dyadicCeiling n (T ω)) ω ∂μ) =
      ∫ ω, M (b + 1) ω ∂μ :=
    MarkovProcess.integral_apply_eq_of_finite_range hM hM.integrable
      (MarkovProcess.isStoppingTime_dyadicCeiling hT n) (hfin n) (hceil n)
  have hptw : ∀ᵐ ω ∂μ, Tendsto (fun n => M (MarkovProcess.dyadicCeiling n (T ω)) ω) atTop
      (𝓝 (M (T ω) ω)) := by
    refine Filter.Eventually.of_forall fun ω => ?_
    have hn : Tendsto (fun n => MarkovProcess.dyadicCeiling n (T ω)) atTop (𝓝[≥] (T ω)) :=
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
        (MarkovProcess.tendsto_dyadicCeiling (T ω))
        (Filter.Eventually.of_forall fun n => Set.mem_Ici.mpr (MarkovProcess.le_dyadicCeiling n (T ω)))
    exact Tendsto.comp (hright ω (T ω)) hn
  have hlim := tendsto_integral_of_dominated_convergence (μ := μ) H
    (F := fun n ω => M (MarkovProcess.dyadicCeiling n (T ω)) ω)
    (f := fun ω => M (T ω) ω)
    (fun n => (MarkovProcess.stronglyMeasurable_apply_of_finite_range hM.1
      (MarkovProcess.isStoppingTime_dyadicCeiling hT n) (hfin n)).aestronglyMeasurable)
    hH (fun n => Filter.Eventually.of_forall fun ω => hbound _ (hceil n ω) ω) hptw
  exact tendsto_nhds_unique hlim (by simpa only [hstep] using tendsto_const_nhds)

/-- Each trajectory of the actual signed weight is continuous. -/
theorem s8_reduced_force_exponential_weight_continuous {d : ℕ} {Λ₀ : ℝ}
    (hΛ : 0 < Λ₀) {ω : FieldPair d} (hω : IsRegular Λ₀ ω)
    (i : Fin d) (lam : ℝ) (x : Vec d) (γ : Path d) :
    Continuous (fun t : ℝ≥0 => Real.exp
      (lam * ((γ t) i - x i) - ∫ u in Set.Ioc (0 : ℝ) (t : ℝ),
        (lam * forcedDrift (reducedCoefficient ω) i 0 (γ u.toNNReal) i +
          (lam ^ 2 / 2) * reducedCoefficient ω (γ u.toNNReal) i i))) := by
  obtain ⟨hVm, K, hK⟩ := c2_reduced_force_potential_measurable_bounded hΛ hω i lam
  let V : Vec d → ℝ := fun y => lam * forcedDrift (reducedCoefficient ω) i 0 y i +
    (lam ^ 2 / 2) * reducedCoefficient ω y i i
  have hm : Measurable (fun s : ℝ => V (γ s.toNNReal)) :=
    hVm.comp (γ.continuous.measurable.comp continuous_real_toNNReal.measurable)
  have hi : ∀ a b, IntervalIntegrable (fun s : ℝ => V (γ s.toNNReal)) volume a b := by
    intro a b
    apply intervalIntegrable_iff.mpr
    exact IntegrableOn.of_bound (by simp) hm.aestronglyMeasurable K
      (ae_of_all _ fun s => by simpa only [Real.norm_eq_abs] using hK (γ s.toNNReal))
  have hc : Continuous (fun t : ℝ≥0 => ∫ u in Set.Ioc (0 : ℝ) (t : ℝ), V (γ u.toNNReal)) := by
    convert (intervalIntegral.continuous_primitive hi 0).comp NNReal.continuous_coe using 1
    funext t
    exact (intervalIntegral.integral_of_le t.coe_nonneg).symm
  exact Real.continuous_exp.comp ((continuous_const.mul
    (((continuous_apply i).comp γ.continuous).sub continuous_const)).sub hc)

/-- The signed exponential weight has unit mass at a bounded stopping time. -/
theorem s8_reduced_force_exponential_weight_stopped_mass {d : ℕ}
    (hd : 1 ≤ d) {Λ₀ : ℝ} (hΛ : 0 < Λ₀)
    {ω : FieldPair d} (hω : IsRegular Λ₀ ω) (i : Fin d) (lam : ℝ)
    {x : Vec d} {P : Measure (Path d)}
    (hP : SolvesMartingaleProblem
      (External.Draft.svGenerator (reducedCoefficient ω)
        (forcedDrift (reducedCoefficient ω) i 0)) x P) (T : Path d → ℝ≥0)
    (hT : IsStoppingTime (MarkovProcess.ContinuousPath.canonicalFiltration (alpha := Vec d))
      (fun γ => (T γ : WithTop ℝ≥0)))
    (b : ℝ≥0) (hTb : ∀ γ, T γ ≤ b) :
    let Z : Path d → ℝ := fun γ => Real.exp
      (lam * ((γ (T γ)) i - x i) - ∫ u in Set.Ioc (0 : ℝ) (T γ : ℝ),
        (lam * forcedDrift (reducedCoefficient ω) i 0 (γ u.toNNReal) i +
          (lam ^ 2 / 2) * reducedCoefficient ω (γ u.toNNReal) i i))
    Integrable Z P ∧ (∫ γ, Z γ ∂P) = 1 := by
  intro Z
  letI : IsProbabilityMeasure P := hP.1
  let M : ℝ≥0 → Path d → ℝ := fun t γ => Real.exp
      (lam * ((γ t) i - x i) - ∫ u in Set.Ioc (0 : ℝ) (t : ℝ),
        (lam * forcedDrift (reducedCoefficient ω) i 0 (γ u.toNNReal) i +
          (lam ^ 2 / 2) * reducedCoefficient ω (γ u.toNNReal) i i))
  have hM : Martingale M (pathFiltration d) P :=
    u3_reduced_force_density_martingale hd hΛ hω i hP lam
  have hT' : IsStoppingTime (pathFiltration d) (fun γ => (T γ : WithTop ℝ≥0)) := by
    rw [pathFiltration_eq_canonical]
    exact hT
  obtain ⟨H, hH, hbound⟩ := u3_reduced_force_density_horizon_majorant hd hΛ hω i hP lam (b + 1)
  have hs := s8_integral_stopped_of_majorant hM
    (fun γ v => (s8_reduced_force_exponential_weight_continuous hΛ hω i lam x γ).continuousAt.continuousWithinAt)
    hT' hTb hH (fun t ht γ => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact hbound t ht γ)
  exact ⟨s8_reduced_force_exponential_weight_stopped_integrable hd hΛ hω i lam hP T hT b hTb,
    hs.trans (s8_reduced_force_exponential_weight_integral hd hΛ hω i lam hP (b + 1)).2⟩

/-- The signed exponential weight has unit mass for the supplied reduced law. -/
theorem s8_supplied_reduced_family_signed_weight_normalization
    {d : ℕ} (hd : 2 ≤ d) {Λ r : ℝ} (Q : EnvironmentLaw d Λ r)
    (hpath : PathwiseAt Q)
    (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure, SolvesMartingaleProblem
      (reducedGenerator (firstCoordinateIndex hd) ω 0) 0 (Y (0,ω)))
    (lam : ℝ) (t : ℝ≥0) :
    ∀ᵐ ω ∂Q.measure,
      let Z : Path d → ℝ := fun γ => Real.exp
        (lam * (γ t) (firstCoordinateIndex hd) -
          ∫ u in Set.Ioc (0 : ℝ) (t : ℝ),
            (lam * forcedDrift (reducedCoefficient ω) (firstCoordinateIndex hd) 0
              (γ u.toNNReal) (firstCoordinateIndex hd) +
            (lam ^ 2 / 2) * reducedCoefficient ω (γ u.toNNReal)
              (firstCoordinateIndex hd) (firstCoordinateIndex hd)))
      Integrable Z (Y (0,ω)) ∧ (∫ γ, Z γ ∂Y (0,ω)) = 1 := by
  have hΛ : 0 < Λ := lt_of_lt_of_le zero_lt_one Q.ellipticity_parameter
  filter_upwards [Q.regular, u3_supplied_reduced_law_solves_textbook_of_pathwise
    (hpath := hpath) hd Q (firstCoordinateIndex hd) 0 Y hY] with ω hω hP
  simpa only [Pi.zero_apply, sub_zero] using
    s8_reduced_force_exponential_weight_integral (by omega) hΛ hω
      (firstCoordinateIndex hd) lam hP t

/-- The supplied reduced family has normalized signed weights. -/
theorem s8_finish_supplied_reduced_family_signed_weight_normalization
    {d : ℕ} (hd : 2 ≤ d) {Λ r : ℝ} (Q : EnvironmentLaw d Λ r)
    (hpath : PathwiseAt Q)
    (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure, SolvesMartingaleProblem
      (reducedGenerator (firstCoordinateIndex hd) ω 0) 0 (Y (0,ω)))
    (lam : ℝ) (t : ℝ≥0) :
    ∀ᵐ ω ∂Q.measure,
      let Z : Path d → ℝ := fun γ => Real.exp
        (lam * (γ t) (firstCoordinateIndex hd) -
          ∫ u in Set.Ioc (0 : ℝ) (t : ℝ),
            (lam * forcedDrift (reducedCoefficient ω) (firstCoordinateIndex hd) 0
              (γ u.toNNReal) (firstCoordinateIndex hd) +
            (lam ^ 2 / 2) * reducedCoefficient ω (γ u.toNNReal)
              (firstCoordinateIndex hd) (firstCoordinateIndex hd)))
      Integrable Z (Y (0,ω)) ∧ (∫ γ, Z γ ∂Y (0,ω)) = 1 :=
  s8_supplied_reduced_family_signed_weight_normalization (hpath := hpath) hd Q Y hY lam t

/-- The signed weight is a martingale on each supplied reduced law, almost surely. -/
theorem s8_supplied_reduced_family_signed_weight_martingale_verified
    {d : ℕ} (hd : 2 ≤ d) {Λ r : ℝ} (Q : EnvironmentLaw d Λ r)
    (hpath : PathwiseAt Q)
    (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure, SolvesMartingaleProblem
      (reducedGenerator (firstCoordinateIndex hd) ω 0) 0 (Y (0,ω)))
    (lam : ℝ) :
    ∀ᵐ ω ∂Q.measure,
      Martingale (fun (t : ℝ≥0) γ => Real.exp
        (lam * (γ t) (firstCoordinateIndex hd) -
          ∫ u in Set.Ioc (0 : ℝ) (t : ℝ),
            (lam * forcedDrift (reducedCoefficient ω) (firstCoordinateIndex hd) 0
              (γ u.toNNReal) (firstCoordinateIndex hd) +
            (lam ^ 2 / 2) * reducedCoefficient ω (γ u.toNNReal)
              (firstCoordinateIndex hd) (firstCoordinateIndex hd))))
        (pathFiltration d) (Y (0,ω)) := by
  have hΛ : 0 < Λ := lt_of_lt_of_le zero_lt_one Q.ellipticity_parameter
  filter_upwards [Q.regular, u3_supplied_reduced_law_solves_textbook_of_pathwise
    (hpath := hpath) hd Q (firstCoordinateIndex hd) 0 Y hY] with ω hω hP
  simpa only [Pi.zero_apply, sub_zero] using
    u3_reduced_force_density_martingale (by omega) hΛ hω
      (firstCoordinateIndex hd) hP lam

/-- Conditional expectation of the signed weight on the supplied law. -/
theorem s8_supplied_signed_weight_condExp
    {d : ℕ} (hd : 2 ≤ d) {Λ r : ℝ} (Q : EnvironmentLaw d Λ r)
    (hpath : PathwiseAt Q)
    (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure, SolvesMartingaleProblem
      (reducedGenerator (firstCoordinateIndex hd) ω 0) 0 (Y (0,ω)))
    (lam : ℝ) (s t : ℝ≥0) (hst : s ≤ t) :
    ∀ᵐ ω ∂Q.measure,
      let Z : ℝ≥0 → Path d → ℝ := fun v γ => Real.exp
        (lam * (γ v) (firstCoordinateIndex hd) -
          ∫ u in Set.Ioc (0 : ℝ) (v : ℝ),
            (lam * forcedDrift (reducedCoefficient ω) (firstCoordinateIndex hd) 0
              (γ u.toNNReal) (firstCoordinateIndex hd) +
            (lam ^ 2 / 2) * reducedCoefficient ω (γ u.toNNReal)
              (firstCoordinateIndex hd) (firstCoordinateIndex hd)))
      (Y (0,ω))[Z t | pathFiltration d s] =ᵐ[Y (0,ω)] Z s := by
  filter_upwards [s8_supplied_reduced_family_signed_weight_martingale_verified
    (hpath := hpath) hd Q Y hY lam] with ω hM
  exact hM.condExp_ae_eq hst

/-- The signed weight stopped at a bounded stopping time is integrable on the supplied law. -/
theorem s8_supplied_signed_weight_stopped_integrable
    {d : ℕ} (hd : 2 ≤ d) {Λ r : ℝ} (Q : EnvironmentLaw d Λ r)
    (hpath : PathwiseAt Q)
    (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure, SolvesMartingaleProblem
      (reducedGenerator (firstCoordinateIndex hd) ω 0) 0 (Y (0,ω)))
    (lam : ℝ) (T : Path d → ℝ≥0)
    (hT : IsStoppingTime (MarkovProcess.ContinuousPath.canonicalFiltration (alpha := Vec d))
      (fun γ => (T γ : WithTop ℝ≥0)))
    (b : ℝ≥0) (hTb : ∀ γ, T γ ≤ b) :
    ∀ᵐ ω ∂Q.measure,
      Integrable (fun γ => Real.exp
        (lam * (γ (T γ)) (firstCoordinateIndex hd) -
          ∫ u in Set.Ioc (0 : ℝ) (T γ : ℝ),
            (lam * forcedDrift (reducedCoefficient ω) (firstCoordinateIndex hd) 0
              (γ u.toNNReal) (firstCoordinateIndex hd) +
            (lam ^ 2 / 2) * reducedCoefficient ω (γ u.toNNReal)
              (firstCoordinateIndex hd) (firstCoordinateIndex hd)))) (Y (0,ω)) := by
  have hΛ : 0 < Λ := lt_of_lt_of_le zero_lt_one Q.ellipticity_parameter
  filter_upwards [Q.regular, u3_supplied_reduced_law_solves_textbook_of_pathwise
    (hpath := hpath) hd Q (firstCoordinateIndex hd) 0 Y hY] with ω hω hP
  simpa only [Pi.zero_apply, sub_zero] using
    s8_reduced_force_exponential_weight_stopped_integrable (by omega) hΛ hω
      (firstCoordinateIndex hd) lam hP T hT b hTb






/-- The supplied signed law satisfies the complex-valued integrated Dynkin identity. -/
theorem s8_supplied_signed_complex_dynkin
    {d : ℕ} (hd : 2 ≤ d) {Λ r : ℝ} (Q : EnvironmentLaw d Λ r)
    (hunforced : UnforcedAt hd Q) (hpath : PathwiseAt Q)
    (lam : ℝ) (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure, SolvesMartingaleProblem
      (reducedGenerator ⟨0, by omega⟩ ω lam) 0 (Y (0,ω)))
    (T : ℝ≥0) (f g : Lp ℂ 2 (reducedLaw Q))
    (hfg : IsComplexGeneratorPair Q ⟨0, by omega⟩ (lam : ℂ) f g) :
    ∀ᵐ ω ∂Q.measure,
      (∫ γ : Path d, f (translate (γ T) (reduce ω)) ∂Y (0,ω)) - f (reduce ω) =
        ∫ t in Set.Ioc (0 : ℝ) (T : ℝ), ∫ γ : Path d,
          g (translate (γ t.toNNReal) (reduce ω)) ∂Y (0,ω) := by
  let W : FieldPair d → ℂ := fun w => g w
  have hWm : Measurable W := (Lp.stronglyMeasurable g).measurable
  have hr := u3_supplied_force_occupation_fubini_of_deps (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY T
    (fun w => (W w).re) (Complex.continuous_re.measurable.comp hWm)
    (Complex.reCLM.comp_memLp' (Lp.memLp g))
  have hi := u3_supplied_force_occupation_fubini_of_deps (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY T
    (fun w => (W w).im) (Complex.continuous_im.measurable.comp hWm)
    (Complex.imCLM.comp_memLp' (Lp.memLp g))
  filter_upwards [u3_signed_generator_pair_dynkin_of_deps (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY T f g hfg Complex.reCLM,
    u3_signed_generator_pair_dynkin_of_deps (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY T f g hfg Complex.imCLM,
    u3_supplied_force_endpoint_integrable_of_deps (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY T f, hr, hi, hY]
    with ω hre him hf hgr hgi hprob
  let : IsProbabilityMeasure (Y (0,ω)) := hprob.1
  have hprod : Integrable (fun p : Path d × ℝ =>
      g (translate (p.1 p.2.toNNReal) (reduce ω)))
      ((Y (0,ω)).prod (volume.restrict (Set.Ioc 0 (T : ℝ)))) := by
    exact Integrable.re_im_iff.mp ⟨hgr.1, hgi.1⟩
  have htime := hprod.integral_prod_right
  have hinnerR : (fun t : ℝ => ∫ γ : Path d,
      (g (translate (γ t.toNNReal) (reduce ω))).re ∂Y (0,ω)) =ᵐ[
        volume.restrict (Set.Ioc 0 (T : ℝ))] fun t =>
      (∫ γ : Path d, g (translate (γ t.toNNReal) (reduce ω)) ∂Y (0,ω)).re := by
    filter_upwards [hprod.prod_left_ae] with t ht
    exact integral_re ht
  have hinnerI : (fun t : ℝ => ∫ γ : Path d,
      (g (translate (γ t.toNNReal) (reduce ω))).im ∂Y (0,ω)) =ᵐ[
        volume.restrict (Set.Ioc 0 (T : ℝ))] fun t =>
      (∫ γ : Path d, g (translate (γ t.toNNReal) (reduce ω)) ∂Y (0,ω)).im := by
    filter_upwards [hprod.prod_left_ae] with t ht
    exact integral_im ht
  simp only [Complex.reCLM_apply] at hre
  simp only [Complex.imCLM_apply] at him
  rw [integral_congr_ae hinnerR] at hre
  rw [integral_congr_ae hinnerI] at him
  have hfr := integral_re hf
  have hfi := integral_im hf
  have htr := integral_re htime
  have hti := integral_im htime
  simp only [RCLike.re_eq_complex_re] at hfr htr
  simp only [RCLike.im_eq_complex_im] at hfi hti
  apply Complex.ext
  · rw [Complex.sub_re, ← hfr, ← htr]
    exact hre
  · rw [Complex.sub_im, ← hfi, ← hti]
    exact him



/-- The complex Dynkin identity on a fixed subinterval of a finite horizon. -/
theorem s8_supplied_signed_complex_dynkin_interval
    {d : ℕ} (hd : 2 ≤ d) {Λ r : ℝ} (Q : EnvironmentLaw d Λ r)
    (hunforced : UnforcedAt hd Q) (hpath : PathwiseAt Q)
    (lam : ℝ) (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure, SolvesMartingaleProblem
      (reducedGenerator ⟨0, by omega⟩ ω lam) 0 (Y (0,ω)))
    (a b : ℝ≥0) (hab : a ≤ b) (f g : Lp ℂ 2 (reducedLaw Q))
    (hfg : IsComplexGeneratorPair Q ⟨0, by omega⟩ (lam : ℂ) f g) :
    ∀ᵐ ω ∂Q.measure,
      (∫ γ : Path d, f (translate (γ b) (reduce ω)) ∂Y (0,ω)) -
        (∫ γ : Path d, f (translate (γ a) (reduce ω)) ∂Y (0,ω)) =
      ∫ t in Set.Ioc (a : ℝ) (b : ℝ), ∫ γ : Path d,
        g (translate (γ t.toNNReal) (reduce ω)) ∂Y (0,ω) := by
  exact u3_signed_generator_pair_complex_dynkin_interval_of_deps
    (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY a b hab f g hfg



/-- Joint finite-horizon occupation is integrable for complex L² data. -/
theorem s8_supplied_signed_complex_joint_integrable
    {d : ℕ} (hd : 2 ≤ d) {Λ r : ℝ} (Q : EnvironmentLaw d Λ r)
    (hunforced : UnforcedAt hd Q) (hpath : PathwiseAt Q)
    (lam : ℝ) (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure, SolvesMartingaleProblem
      (reducedGenerator ⟨0, by omega⟩ ω lam) 0 (Y (0,ω)))
    (T : ℝ≥0) (g : Lp ℂ 2 (reducedLaw Q)) :
    ∃ K : Kernel (FieldPair d) (Path d), IsMarkovKernel K ∧
      (∀ᵐ ω ∂Q.measure, Y (0,ω) = K ω) ∧
      Integrable (fun p : ℝ × (FieldPair d × Path d) =>
        g (translate (p.2.2 p.1.toNNReal) (reduce p.2.1)))
        ((volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ))).prod (Q.measure ⊗ₘ K)) := by
  obtain ⟨K, hmarkov, hK, hint⟩ :=
    u3_supplied_force_finite_time_joint_integrable_of_deps (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY T
      (fun w => ‖g w‖) (Lp.stronglyMeasurable g).measurable.norm (Lp.memLp g).norm
  refine ⟨K, hmarkov, hK, ?_⟩
  let E : ℝ × (FieldPair d × Path d) → FieldPair d := fun p =>
    translate (p.2.2 p.1.toNNReal) (reduce p.2.1)
  have hE : Measurable E := by
    exact (Probability.continuous_translate.comp
      ((continuous_eval.comp ((continuous_snd.comp continuous_snd).prodMk
        (continuous_real_toNNReal.comp continuous_fst))).prodMk
        (Probability.continuous_reduce.comp (continuous_fst.comp continuous_snd)))).measurable
  apply (integrable_norm_iff ((Lp.stronglyMeasurable g).measurable.comp hE).aestronglyMeasurable).mp
  simpa only [abs_norm, E, Function.comp_apply] using hint



/-- A jointly measurable version of the supplied endpoint action exists for all times. -/
theorem s8_supplied_signed_endpoint_jointly_measurable
    {d : ℕ} (hd : 2 ≤ d) {Λ r : ℝ} (Q : EnvironmentLaw d Λ r)
    (hunforced : UnforcedAt hd Q) (hpath : PathwiseAt Q)
    (lam : ℝ) (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure, SolvesMartingaleProblem
      (reducedGenerator ⟨0, by omega⟩ ω lam) 0 (Y (0,ω)))
    (T : ℝ≥0) (g : Lp ℂ 2 (reducedLaw Q)) :
    ∃ H : ℝ × FieldPair d → ℂ, StronglyMeasurable H ∧
      ∀ᵐ ω ∂Q.measure, ∀ t : ℝ,
        H (t, ω) = ∫ γ : Path d,
          g (translate (γ t.toNNReal) (reduce ω)) ∂Y (0,ω) := by
  obtain ⟨K, hmarkov, hK, _⟩ :=
    s8_supplied_signed_complex_joint_integrable (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY T g
  let : IsMarkovKernel K := hmarkov
  let K' : Kernel (ℝ × FieldPair d) (Path d) := K.comap Prod.snd measurable_snd
  let E : (ℝ × FieldPair d) × Path d → FieldPair d := fun p =>
    translate (p.2 p.1.1.toNNReal) (reduce p.1.2)
  have hE : Measurable E := by
    exact (Probability.continuous_translate.comp
      ((continuous_eval.comp (continuous_snd.prodMk
        (continuous_real_toNNReal.comp (continuous_fst.comp continuous_fst)))).prodMk
        (Probability.continuous_reduce.comp (continuous_snd.comp continuous_fst)))).measurable
  let H : ℝ × FieldPair d → ℂ := fun p => ∫ γ, g (E (p, γ)) ∂K' p
  have hH : StronglyMeasurable H :=
    ((Lp.stronglyMeasurable g).comp_measurable hE).integral_kernel_prod_right'
  refine ⟨H, hH, ?_⟩
  filter_upwards [hK] with ω hω
  intro t
  change (∫ γ, g (translate (γ t.toNNReal) (reduce ω)) ∂K ω) = _
  rw [hω]



/-- The L¹ endpoint-action orbit is integrable on every finite time interval. -/
theorem s8_supplied_signed_action_orbit_integrable
    {d : ℕ} (hd : 2 ≤ d) {Λ r : ℝ} (Q : EnvironmentLaw d Λ r)
    (hunforced : UnforcedAt hd Q) (hpath : PathwiseAt Q)
    (lam : ℝ) (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure, SolvesMartingaleProblem
      (reducedGenerator ⟨0, by omega⟩ ω lam) 0 (Y (0,ω)))
    (T : ℝ≥0) (g : Lp ℂ 2 (reducedLaw Q)) :
    IntegrableOn (fun t : ℝ =>
      u3SuppliedForceEndpointActionContinuousOfDeps
        (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY t.toNNReal g)
      (Set.Ioc 0 (T : ℝ)) := by
  have hc : Continuous (fun t : ℝ =>
      u3SuppliedForceEndpointActionContinuousOfDeps
        (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY t.toNNReal g) :=
    (u3_supplied_force_endpoint_action_orbit_continuous_of_deps
      (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY g).comp continuous_real_toNNReal
  exact hc.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self



/-- A jointly measurable endpoint version is integrable in time and environment. -/
theorem s8_supplied_signed_endpoint_jointly_integrable
    {d : ℕ} (hd : 2 ≤ d) {Λ r : ℝ} (Q : EnvironmentLaw d Λ r)
    (hunforced : UnforcedAt hd Q) (hpath : PathwiseAt Q)
    (lam : ℝ) (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure, SolvesMartingaleProblem
      (reducedGenerator ⟨0, by omega⟩ ω lam) 0 (Y (0,ω)))
    (T : ℝ≥0) (g : Lp ℂ 2 (reducedLaw Q)) :
    ∃ H : ℝ × FieldPair d → ℂ,
      Integrable H ((volume.restrict (Set.Ioc 0 (T : ℝ))).prod Q.measure) ∧
      ∀ᵐ ω ∂Q.measure, ∀ t : ℝ,
        H (t, ω) = ∫ γ : Path d,
          g (translate (γ t.toNNReal) (reduce ω)) ∂Y (0,ω) := by
  obtain ⟨H, hm, hH⟩ := s8_supplied_signed_endpoint_jointly_measurable
    (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY T g
  let A : ℝ → Lp ℂ 1 Q.measure := fun t =>
    u3SuppliedForceEndpointActionContinuousOfDeps
      (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY t.toNNReal g
  have hrep (t : ℝ) : (fun ω => A t ω) =ᵐ[Q.measure] fun ω => H (t, ω) := by
    have ha := (memLp_one_iff_integrable.mpr
      (u3_supplied_force_endpoint_action_integrable_of_deps
        (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY t.toNNReal g)).coeFn_toLp
    change (fun ω => A t ω) =ᵐ[Q.measure] _ at ha
    filter_upwards [ha, hH] with ω haω hHω
    exact haω.trans (hHω t).symm
  have hsec (t : ℝ) : Integrable (fun ω => H (t, ω)) Q.measure :=
    (L1.integrable_coeFn (A t)).congr (hrep t)
  have hnorm (t : ℝ) : (∫ ω, ‖H (t, ω)‖ ∂Q.measure) = ‖A t‖ := by
    rw [L1.norm_eq_integral_norm]
    exact integral_congr_ae ((hrep t).mono fun ω hω => congrArg norm hω.symm)
  have hA : IntegrableOn A (Set.Ioc 0 (T : ℝ)) :=
    s8_supplied_signed_action_orbit_integrable (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY T g
  refine ⟨H, ?_, hH⟩
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  refine ⟨Filter.Eventually.of_forall hsec, ?_⟩
  simpa only [hnorm] using hA.norm



/-- The time integral of the L¹ action has the expected quenched representative. -/
theorem s8_supplied_signed_action_integral_ae
    {d : ℕ} (hd : 2 ≤ d) {Λ r : ℝ} (Q : EnvironmentLaw d Λ r)
    (hunforced : UnforcedAt hd Q) (hpath : PathwiseAt Q)
    (lam : ℝ) (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure, SolvesMartingaleProblem
      (reducedGenerator ⟨0, by omega⟩ ω lam) 0 (Y (0,ω)))
    (T : ℝ≥0) (g : Lp ℂ 2 (reducedLaw Q)) :
    (∫ t in Set.Ioc (0 : ℝ) (T : ℝ),
      u3SuppliedForceEndpointActionContinuousOfDeps
        (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY t.toNNReal g : Lp ℂ 1 Q.measure) =ᵐ[Q.measure]
      fun ω => ∫ t in Set.Ioc (0 : ℝ) (T : ℝ), ∫ γ : Path d,
        g (translate (γ t.toNNReal) (reduce ω)) ∂Y (0,ω) := by
  obtain ⟨H, hH, hrep⟩ := s8_supplied_signed_endpoint_jointly_integrable
    (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY T g
  let μ := volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ))
  let A : ℝ → Lp ℂ 1 Q.measure := fun t =>
    u3SuppliedForceEndpointActionContinuousOfDeps
      (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY t.toNNReal g
  let B : FieldPair d → ℂ := fun ω => ∫ t, H (t, ω) ∂μ
  have hA : Integrable A μ :=
    s8_supplied_signed_action_orbit_integrable (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY T g
  have hB : Integrable B Q.measure := hH.integral_prod_right
  have hpoint (t : ℝ) : (fun ω => A t ω) =ᵐ[Q.measure] fun ω => H (t,ω) := by
    have ha := (memLp_one_iff_integrable.mpr
      (u3_supplied_force_endpoint_action_integrable_of_deps
        (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY t.toNNReal g)).coeFn_toLp
    change (fun ω => A t ω) =ᵐ[Q.measure] _ at ha
    filter_upwards [ha, hrep] with ω haω hω
    exact haω.trans (hω t).symm
  have heq : (∫ t, A t ∂μ : Lp ℂ 1 Q.measure) =ᵐ[Q.measure]
      (memLp_one_iff_integrable.mpr hB).toLp B := by
    apply Lp.ae_eq_of_forall_setIntegral_eq _ _ (by norm_num) (by norm_num)
      (fun s _ _ => (L1.integrable_coeFn _).integrableOn)
      (fun s _ _ => (L1.integrable_coeFn _).integrableOn)
    intro s hs hfinite
    let L : Lp ℂ 1 Q.measure →L[ℝ] ℂ :=
      L1.integralCLM.comp (LpToLpRestrictCLM (FieldPair d) ℂ ℝ Q.measure 1 s)
    have hL (z : Lp ℂ 1 Q.measure) : L z = ∫ ω in s, z ω ∂Q.measure := by
      change L1.integralCLM (LpToLpRestrictCLM (FieldPair d) ℂ ℝ Q.measure 1 s z) = _
      rw [← L1.integral_eq, L1.integral_eq_integral]
      exact integral_congr_ae (LpToLpRestrictCLM_coeFn ℝ s z)
    have hp : Integrable H (μ.prod (Q.measure.restrict s)) :=
      hH.mono_measure (Measure.prod_mono le_rfl Measure.restrict_le_self)
    calc
      _ = L (∫ t, A t ∂μ) := (hL _).symm
      _ = ∫ t, L (A t) ∂μ := (L.integral_comp_comm hA).symm
      _ = ∫ t, ∫ ω in s, H (t,ω) ∂Q.measure ∂μ := by
        apply integral_congr_ae
        filter_upwards [] with t
        rw [hL]
        exact integral_congr_ae (ae_restrict_of_ae (hpoint t))
      _ = ∫ ω in s, B ω ∂Q.measure := integral_integral_swap hp
      _ = _ := by
        apply integral_congr_ae
        exact ae_restrict_of_ae (memLp_one_iff_integrable.mpr hB).coeFn_toLp.symm
  filter_upwards [heq, (memLp_one_iff_integrable.mpr hB).coeFn_toLp, hrep] with ω he hb hω
  rw [he, hb]
  apply integral_congr_ae
  filter_upwards [] with t
  exact hω t



/-- Integrated Dynkin identity in the annealed L¹ space. -/
theorem s8_supplied_signed_dynkin_L1
    {d : ℕ} (hd : 2 ≤ d) {Λ r : ℝ} (Q : EnvironmentLaw d Λ r)
    (hunforced : UnforcedAt hd Q) (hpath : PathwiseAt Q)
    (lam : ℝ) (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure, SolvesMartingaleProblem
      (reducedGenerator ⟨0, by omega⟩ ω lam) 0 (Y (0,ω)))
    (T : ℝ≥0) (f g : Lp ℂ 2 (reducedLaw Q))
    (hfg : IsComplexGeneratorPair Q ⟨0, by omega⟩ (lam : ℂ) f g) :
    u3SuppliedForceEndpointActionContinuousOfDeps (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY T f -
      u3SuppliedForceEndpointActionContinuousOfDeps (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY 0 f =
    ∫ t in Set.Ioc (0 : ℝ) (T : ℝ),
      u3SuppliedForceEndpointActionContinuousOfDeps
        (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY t.toNNReal g := by
  let AT := u3SuppliedForceEndpointActionContinuousOfDeps (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY T f
  let A0 := u3SuppliedForceEndpointActionContinuousOfDeps (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY 0 f
  have hT : (fun ω => AT ω) =ᵐ[Q.measure] fun ω =>
      ∫ γ : Path d, f (translate (γ T) (reduce ω)) ∂Y (0,ω) := by
    exact (memLp_one_iff_integrable.mpr
      (u3_supplied_force_endpoint_action_integrable_of_deps
        (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY T f)).coeFn_toLp
  have h0 : (fun ω => A0 ω) =ᵐ[Q.measure] fun ω => f (reduce ω) :=
    u3_supplied_force_endpoint_action_zero_of_deps (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY f
  apply Lp.ext
  filter_upwards [Lp.coeFn_sub AT A0, hT, h0,
    s8_supplied_signed_action_integral_ae (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY T g,
    s8_supplied_signed_complex_dynkin (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY T f g hfg]
    with ω hsub hTω h0ω hiω hDω
  change (AT - A0) ω = _
  rw [hsub, Pi.sub_apply, hTω, h0ω, hiω]
  exact hDω


/-- The signed endpoint action has the generator derivative at positive times. -/
theorem s8_supplied_signed_action_hasDerivAt
    {d : ℕ} (hd : 2 ≤ d) {Λ r : ℝ} (Q : EnvironmentLaw d Λ r)
    (hunforced : UnforcedAt hd Q) (hpath : PathwiseAt Q)
    (lam : ℝ) (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure, SolvesMartingaleProblem
      (reducedGenerator ⟨0, by omega⟩ ω lam) 0 (Y (0,ω)))
    (f g : Lp ℂ 2 (reducedLaw Q))
    (hfg : IsComplexGeneratorPair Q ⟨0, by omega⟩ (lam : ℂ) f g)
    (t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun s : ℝ =>
      u3SuppliedForceEndpointActionContinuousOfDeps
        (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY s.toNNReal f)
      (u3SuppliedForceEndpointActionContinuousOfDeps
        (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY t.toNNReal g) t := by
  have hc : Continuous (fun s : ℝ =>
      u3SuppliedForceEndpointActionContinuousOfDeps
        (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY s.toNNReal g) :=
    (u3_supplied_force_endpoint_action_orbit_continuous_of_deps
      (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY g).comp continuous_real_toNNReal
  have hderiv := (hc.integral_hasStrictDerivAt 0 t).hasDerivAt
  have hderiv' := hderiv.add_const
    (u3SuppliedForceEndpointActionContinuousOfDeps (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY 0 f)
  apply hderiv'.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds ht] with s hs
  have hi := u3_supplied_force_dynkin_L1_interval_of_deps (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY
    0 s.toNNReal (by exact bot_le) f g hfg
  rw [Real.coe_toNNReal' , max_eq_left hs.le] at hi
  rw [intervalIntegral.integral_of_le hs.le]
  exact eq_add_of_sub_eq hi


/-- Differentiate a strongly continuous operator family on a varying input. -/
private theorem s8_hasDerivAt_varying_action
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : ℝ≥0 → E →L[ℝ] F)
    (hA : ∀ z : ℝ≥0 → E, Continuous z → Continuous (fun t => A t (z t)))
    (x : ℝ → E) (hx : Continuous x) (t : ℝ) (ht : 0 < t) (x' : E) (y : F)
    (hderiv : HasDerivAt x x' t)
    (hfixed : HasDerivAt (fun s : ℝ => A s.toNNReal (x t)) y t) :
    HasDerivAt (fun s : ℝ => A s.toNNReal (x s)) (y + A t.toNNReal x') t := by
  have hds : Continuous (dslope x t) := by
    rw [← continuousOn_univ]
    exact (continuousOn_dslope (by simp)).2 ⟨hx.continuousOn, hderiv.differentiableAt⟩
  have hv : ContinuousAt (fun s : ℝ => A s.toNNReal (dslope x t s)) t := by
    have h := (hA (fun s : ℝ≥0 => dslope x t s)
      (hds.comp continuous_subtype_val)).comp continuous_real_toNNReal
    apply h.continuousAt.congr_of_eventuallyEq
    filter_upwards [eventually_gt_nhds ht] with s hs
    simp [Function.comp_def, Real.coe_toNNReal', max_eq_left hs.le]
  have hlim : Tendsto (fun s : ℝ => A s.toNNReal (dslope x t s))
      (𝓝[≠] t) (𝓝 (A t.toNNReal x')) := by
    have ht' : Tendsto (fun s : ℝ => A s.toNNReal (dslope x t s))
        (𝓝[≠] t) (𝓝 (A t.toNNReal (dslope x t t))) :=
      hv.tendsto.mono_left nhdsWithin_le_nhds
    simpa only [dslope_same, hderiv.deriv] using ht'
  apply hasDerivAt_iff_tendsto_slope.mpr
  apply (hfixed.tendsto_slope.add hlim).congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hne : s ≠ t := hs
  rw [dslope_of_ne x hne]
  simp only [slope_def_module, map_sub, map_smul, smul_sub]
  abel

/-- The endpoint action and the backward forced evolution have cancelling derivatives. -/
private theorem s8_supplied_signed_interpolation_hasDerivAt
    {d : ℕ} (hd : 2 ≤ d) {Λ r : ℝ} (Q : EnvironmentLaw d Λ r)
    (hunforced : UnforcedAt hd Q) (hpath : PathwiseAt Q)
    (lam : ℝ) (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure, SolvesMartingaleProblem
      (reducedGenerator (firstCoordinateIndex hd) ω lam) 0 (Y (0,ω)))
    (f g : Lp ℂ 2 (reducedLaw Q))
    (hfg : IsComplexGeneratorPair Q (firstCoordinateIndex hd) (lam : ℂ) f g)
    (T t : ℝ) (ht : 0 < t) (htT : t < T) :
    HasDerivAt (fun s : ℝ =>
      u3SuppliedForceEndpointActionContinuousOfDeps (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY
        s.toNNReal (forcedComplexEvolution Q (firstCoordinateIndex hd) (lam : ℂ)
          (T - s).toNNReal f)) 0 t := by
  let P := forcedComplexEvolution Q (firstCoordinateIndex hd) (lam : ℂ)
  let A : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℝ] Lp ℂ 1 Q.measure := fun s =>
    (u3SuppliedForceEndpointActionContinuousOfDeps (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY s).restrictScalars ℝ
  let x : ℝ → Lp ℂ 2 (reducedLaw Q) := fun s => P (T - s).toNNReal f
  have hA (z : ℝ≥0 → Lp ℂ 2 (reducedLaw Q)) (hz : Continuous z) :
      Continuous (fun s => A s (z s)) :=
    u3_supplied_force_endpoint_action_continuous_varying_of_deps (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY z hz
  have hx : Continuous x :=
    (continuous_forcedComplexEvolution_apply Q (firstCoordinateIndex hd) (lam : ℂ) f).comp
      (continuous_real_toNNReal.comp (continuous_const.sub continuous_id))
  have hx' : HasDerivAt x (-P (T - t).toNNReal g) t := by
    have h := (hasDerivAt_forcedComplexEvolution_of_generator Q (firstCoordinateIndex hd)
      (lam : ℂ) hfg (T - t) (sub_pos.mpr htT)).comp_const_sub T t
    simpa only [x, P, zero_sub, one_smul, neg_smul] using h
  have hgraph := (isComplexEnvironmentSemigroup_forcedComplexEvolution Q
    (firstCoordinateIndex hd) (lam : ℂ)).map_generator hfg (T - t).toNNReal
  have hfixed : HasDerivAt (fun s : ℝ => A s.toNNReal (x t))
      (A t.toNNReal (P (T - t).toNNReal g)) t :=
    s8_supplied_signed_action_hasDerivAt (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY _ _ hgraph t ht
  have h := s8_hasDerivAt_varying_action A hA x hx t ht _ _ hx' hfixed
  simpa [map_neg, A, x, P] using h

/-- Generator-domain data give the same endpoint action and evolution. -/
private theorem s8_supplied_signed_action_eq_evolution_on_graph
    {d : ℕ} (hd : 2 ≤ d) {Λ r : ℝ} (Q : EnvironmentLaw d Λ r)
    (hunforced : UnforcedAt hd Q) (hpath : PathwiseAt Q)
    (lam : ℝ) (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure, SolvesMartingaleProblem
      (reducedGenerator (firstCoordinateIndex hd) ω lam) 0 (Y (0,ω)))
    (f g : Lp ℂ 2 (reducedLaw Q))
    (hfg : IsComplexGeneratorPair Q (firstCoordinateIndex hd) (lam : ℂ) f g)
    (T : ℝ≥0) :
    u3SuppliedForceEndpointActionContinuousOfDeps (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY T f =
      u3SuppliedForceEndpointActionContinuousOfDeps (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY 0
        (forcedComplexEvolution Q (firstCoordinateIndex hd) (lam : ℂ) T f) := by
  let P := forcedComplexEvolution Q (firstCoordinateIndex hd) (lam : ℂ)
  let A := u3SuppliedForceEndpointActionContinuousOfDeps (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY
  let v : ℝ → Lp ℂ 1 Q.measure := fun s => A s.toNNReal (P ((T : ℝ) - s).toNNReal f)
  let z : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) := fun s => P ((T : ℝ) - s).toNNReal f
  have hz : Continuous z :=
    (continuous_forcedComplexEvolution_apply Q (firstCoordinateIndex hd) (lam : ℂ) f).comp
      (continuous_real_toNNReal.comp (continuous_const.sub continuous_subtype_val))
  have hc : ContinuousOn v (Set.Icc 0 (T : ℝ)) := by
    have h := (u3_supplied_force_endpoint_action_continuous_varying_of_deps
      (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY z hz).comp continuous_real_toNNReal
    apply h.continuousOn.congr
    intro s hs
    simp [v, z, A, Function.comp_def, Real.coe_toNNReal', max_eq_left hs.1]
  have he := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le T.property hc
    (f' := fun _ : ℝ => (0 : Lp ℂ 1 Q.measure))
    (fun s hs => (s8_supplied_signed_interpolation_hasDerivAt
      (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY f g hfg T s hs.1 hs.2).hasDerivWithinAt)
    (intervalIntegrable_const)
  have he' : v (T : ℝ) = v 0 := by
    simp only [intervalIntegral.integral_zero] at he
    exact sub_eq_zero.mp he.symm
  simpa only [v, P, A, sub_self, Real.toNNReal_zero, forcedComplexEvolution_zero,
    ContinuousLinearMap.id_apply, sub_zero, Real.toNNReal_coe] using he'

/-- The graph comparison extends by density to all reduced-law L² data. -/
private theorem s8_supplied_signed_action_eq_evolution_L1
    {d : ℕ} (hd : 2 ≤ d) {Λ r : ℝ} (Q : EnvironmentLaw d Λ r)
    (hunforced : UnforcedAt hd Q) (hpath : PathwiseAt Q)
    (lam : ℝ) (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure, SolvesMartingaleProblem
      (reducedGenerator (firstCoordinateIndex hd) ω lam) 0 (Y (0,ω)))
    (f : Lp ℂ 2 (reducedLaw Q)) (T : ℝ≥0) :
    u3SuppliedForceEndpointActionContinuousOfDeps (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY T f =
      u3SuppliedForceEndpointActionContinuousOfDeps (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY 0
        (forcedComplexEvolution Q (firstCoordinateIndex hd) (lam : ℂ) T f) := by
  let P := forcedComplexEvolution Q (firstCoordinateIndex hd) (lam : ℂ)
  let A := u3SuppliedForceEndpointActionContinuousOfDeps (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY
  let D : Set (Lp ℂ 2 (reducedLaw Q)) :=
    {f | ∃ g, IsComplexGeneratorPair Q (firstCoordinateIndex hd) (lam : ℂ) f g}
  have hdense : Dense D := dense_complexGenerator_domain Q (firstCoordinateIndex hd) (lam : ℂ)
  have hclosed : IsClosed {f : Lp ℂ 2 (reducedLaw Q) | A T f = A 0 (P T f)} :=
    isClosed_eq (A T).continuous ((A 0).continuous.comp (P T).continuous)
  have hsub : D ⊆ {f : Lp ℂ 2 (reducedLaw Q) | A T f = A 0 (P T f)} := by
    rintro f ⟨g, hfg⟩
    exact s8_supplied_signed_action_eq_evolution_on_graph (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY f g hfg T
  exact closure_minimal hsub hclosed (hdense f)

/-- The supplied signed-force path action agrees with the actual L² evolution. -/
theorem s8_supplied_signed_bounded_endpoint_eq_evolution
    {d : ℕ} (hd : 2 ≤ d) {Λ r : ℝ} (Q : EnvironmentLaw d Λ r)
    (hunforced : UnforcedAt hd Q) (hpath : PathwiseAt Q)
    (lam : ℝ) (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure, SolvesMartingaleProblem
      (reducedGenerator (firstCoordinateIndex hd) ω lam) 0 (Y (0,ω)))
    (g : BoundedContinuousFunction (FieldPair d) ℂ)
    (F : Lp ℂ 2 (reducedLaw Q))
    (hF : F =ᵐ[reducedLaw Q] fun ρ => g ρ) (t : ℝ≥0) :
    ∀ᵐ ω ∂Q.measure,
      forcedComplexEvolution Q (firstCoordinateIndex hd) (lam : ℂ) t F (reduce ω) =
        ∫ γ : Path d, g (translate (γ t) (reduce ω)) ∂Y (0,ω) := by
  have he := u3_supplied_force_endpoint_ae_eq_of_deps (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY t
    (fun ρ => F ρ) (fun ρ => g ρ) (Lp.stronglyMeasurable F).measurable
    g.continuous.measurable hF
  have hrep := (memLp_one_iff_integrable.mpr
    (u3_supplied_force_endpoint_action_integrable_of_deps (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY t F)).coeFn_toLp
  change (u3SuppliedForceEndpointActionContinuousOfDeps (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY t F : Lp ℂ 1 Q.measure) =ᵐ[Q.measure] _ at hrep
  have hzero := u3_supplied_force_endpoint_action_zero_of_deps (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY
    (forcedComplexEvolution Q (firstCoordinateIndex hd) (lam : ℂ) t F)
  have hcomp := Lp.ext_iff.mp
    (s8_supplied_signed_action_eq_evolution_L1 (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY F t)
  filter_upwards [he, hrep, hzero, hcomp] with ω heω hrω hzω hcω
  rw [← hzω, ← hcω, hrω]
  exact integral_congr_ae heω


end EinsteinFull
