import EinsteinFull.Blueprint.Foundation.node_stationary_u2D_environment_u23_unforced_u2D_process
import EinsteinFull.Calculus.S2UnforcedSemigroupSupport
import EinsteinFull.Calculus.C16ReducedGeneratorAE
import EinsteinFull.Calculus.C25RealForcePathWeight

open MeasureTheory Filter Topology
open scoped NNReal BigOperators

noncomputable section
namespace EinsteinFull
open EinsteinRelation

/-- The clauses of `node_stationary_u2D_environment_u23_unforced_u2D_processStmt` for one
environment law `Q`. -/
def UnforcedAt {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) : Prop :=
  let i : Fin d := ⟨0, by omega⟩
  ∃ P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
    IsComplexEnvironmentSemigroup Q i 0 P ∧
    IsComplexTransposeSemigroup Q P P ∧
    (∀ (t : ℝ≥0) (f : Lp ℂ 2 (reducedLaw Q)),
      ‖P t f‖ ≤ ‖f‖ ∧
      (∫ ω, P t f ω ∂reducedLaw Q) = ∫ ω, f ω ∂reducedLaw Q) ∧
    (∀ f : Lp ℂ 2 (reducedLaw Q),
      (∀ t : ℝ≥0, P t f = f) ↔
        ∃ c : ℂ, f =ᵐ[reducedLaw Q] fun _ => c) ∧
    (∀ (f : Lp ℂ 2 (reducedLaw Q)) (G : Fin d → Lp ℂ 2 (reducedLaw Q)),
      HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) f G →
      (∫ ω, (∑ j : Fin d, ∑ k : Fin d,
        (ω.1 0 j k : ℂ) * G k ω * star (G j ω)).re ∂reducedLaw Q) = 0 →
      ∃ c : ℂ, f =ᵐ[reducedLaw Q] fun _ => c) ∧
    ∀ Y : QuenchedPathLaws d,
      (∀ᵐ ω ∂Q.measure,
        SolvesMartingaleProblem (reducedGenerator i ω 0) 0 (Y (0, ω))) →
      ∀ (t : ℝ≥0) (f : Lp ℂ 2 (reducedLaw Q)), ∀ᵐ ω ∂Q.measure,
        Integrable (fun γ : Path d => f (translate (γ t) (reduce ω))) (Y (0, ω)) ∧
        P t f (reduce ω) =
          ∫ γ : Path d, f (translate (γ t) (reduce ω)) ∂Y (0, ω)

/-- The unforced process node holds at every environment law. -/
theorem unforcedAt_of_unforced
    (hunforced : Blueprint.node_stationary_u2D_environment_u23_unforced_u2D_processStmt)
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} : UnforcedAt hd Q :=
  hunforced d hd Λ₀ r₀ Q

/-- The unforced graph dependency identifies the actual zero-force evolution
with the action of any supplied solution of the reduced martingale problem. -/
theorem c27_zero_force_quenched_action_of_unforced
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀)
    (hunforced : UnforcedAt hd Q) (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ ω 0) 0 (Y (0, ω)))
    (t : ℝ≥0) (f : Lp ℂ 2 (reducedLaw Q)) :
    ∀ᵐ ω ∂Q.measure,
      Integrable (fun γ : Path d => f (translate (γ t) (reduce ω))) (Y (0, ω)) ∧
      forcedComplexEvolution Q ⟨0, by omega⟩ 0 t f (reduce ω) =
        ∫ γ : Path d, f (translate (γ t) (reduce ω)) ∂Y (0, ω) := by
  obtain ⟨P, hP, _, _, _, _, haction⟩ := hunforced
  have heq := hP.unique (isComplexEnvironmentSemigroup_forcedComplexEvolution Q ⟨0, by omega⟩ 0)
  rw [heq] at haction
  exact haction Y hY t f

/-- At time zero, the signed-force action follows from the initial condition
of the supplied martingale-problem law. -/
theorem c27_real_force_quenched_action_zero_time
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ ω lam) 0 (Y (0, ω)))
    (f : Lp ℂ 2 (reducedLaw Q)) :
    ∀ᵐ ω ∂Q.measure,
      Integrable (fun γ : Path d => f (translate (γ 0) (reduce ω))) (Y (0, ω)) ∧
      forcedComplexEvolution Q ⟨0, by omega⟩ (lam : ℂ) 0 f (reduce ω) =
        ∫ γ : Path d, f (translate (γ 0) (reduce ω)) ∂Y (0, ω) := by
  filter_upwards [hY] with ω hω
  letI : IsProbabilityMeasure (Y (0, ω)) := hω.1
  have he : (fun γ : Path d => f (translate (γ 0) (reduce ω))) =ᵐ[Y (0, ω)]
      (fun _ => f (reduce ω)) := by
    filter_upwards [hω.2.1] with γ hγ
    rw [hγ, translate_zero]
  refine ⟨(integrable_const _).congr he.symm, ?_⟩
  rw [forcedComplexEvolution_zero, ContinuousLinearMap.id_apply, integral_congr_ae he]
  simp

private theorem c27_fderiv_product {d : ℕ} {f g : Vec d → ℝ}
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) (y v : Vec d) :
    fderiv ℝ (fun z => f z * g z) y v =
      f y * fderiv ℝ g y v + g y * fderiv ℝ f y v := by
  rw [show fderiv ℝ (fun z => f z * g z) y = _ from
    ((hf y).hasFDerivAt.mul (hg y).hasFDerivAt).fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul]

private theorem c27_fderiv_product_second {d : ℕ} {f g : Vec d → ℝ}
    (hf : ContDiff ℝ (2 : ℕ∞) f) (hg : ContDiff ℝ (2 : ℕ∞) g)
    (y : Vec d) (j k : Fin d) :
    fderiv ℝ (fun z => fderiv ℝ (fun w => f w * g w) z (unitVector k)) y
      (unitVector j) =
      f y * fderiv ℝ (fun z => fderiv ℝ g z (unitVector k)) y (unitVector j) +
      g y * fderiv ℝ (fun z => fderiv ℝ f z (unitVector k)) y (unitVector j) +
      fderiv ℝ f y (unitVector j) * fderiv ℝ g y (unitVector k) +
      fderiv ℝ g y (unitVector j) * fderiv ℝ f y (unitVector k) := by
  have hfd := hf.differentiable (by simp)
  have hgd := hg.differentiable (by simp)
  have hdF : Differentiable ℝ (fun z => fderiv ℝ f z (unitVector k)) :=
    ((hf.fderiv_right (by norm_num)).clm_apply
      contDiff_const).differentiable one_ne_zero
  have hdG : Differentiable ℝ (fun z => fderiv ℝ g z (unitVector k)) :=
    ((hg.fderiv_right (by norm_num)).clm_apply
      contDiff_const).differentiable one_ne_zero
  rw [show (fun z => fderiv ℝ (fun w => f w * g w) z (unitVector k)) =
    (fun z => f z * fderiv ℝ g z (unitVector k) +
      g z * fderiv ℝ f z (unitVector k)) from
    funext fun z => c27_fderiv_product hfd hgd z _]
  have hh := ((hfd y).hasFDerivAt.mul (hdG y).hasFDerivAt).add
    ((hgd y).hasFDerivAt.mul (hdF y).hasFDerivAt)
  rw [show fderiv ℝ (fun z => f z * fderiv ℝ g z (unitVector k) +
      g z * fderiv ℝ f z (unitVector k)) y = _ from hh.fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

/-- The generator product rule holds on a single spatial event for regular fields. -/
theorem c27_reduced_generator_product_ae {d : ℕ} {Λ₀ : ℝ}
    (hΛ : 0 < Λ₀) {ω : FieldPair d} (hω : IsRegular Λ₀ ω)
    (i : Fin d) (lam : ℝ) (f g : Vec d → ℝ)
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) :
    ∀ᵐ y ∂(volume : Measure (Vec d)),
      reducedGenerator i ω lam (fun z => f z * g z) y =
        f y * reducedGenerator i ω lam g y + g y * reducedGenerator i ω lam f y +
        (1 / 2 : ℝ) * ∑ j, ∑ k, reducedCoefficient ω y j k *
          (fderiv ℝ f y (unitVector j) * fderiv ℝ g y (unitVector k) +
            fderiv ℝ g y (unitVector j) * fderiv ℝ f y (unitVector k)) := by
  filter_upwards [c16_reduced_generator_ae_textbook hΛ hω] with y hy
  rw [hy i lam _ (hf.mul hg), hy i lam f hf, hy i lam g hg]
  unfold External.Draft.svGenerator
  simp only [c27_fderiv_product_second hf hg]
  simp only [c27_fderiv_product (hf.differentiable (by simp))
    (hg.differentiable (by simp))]
  simp only [mul_add, Finset.sum_add_distrib]
  simp only [mul_left_comm _ (f y), mul_left_comm _ (g y), ← Finset.mul_sum]
  ring

/-- Exponential conjugation of the reduced generator, at almost every spatial point. -/
theorem c27_reduced_generator_exponential_conjugation_ae {d : ℕ}
    {Λ₀ : ℝ} (hΛ : 0 < Λ₀) {ω : FieldPair d} (hω : IsRegular Λ₀ ω)
    (i : Fin d) (lam : ℝ) (f : Vec d → ℝ) (hf : ContDiff ℝ 2 f) :
    let h : Vec d → ℝ := fun y => Real.exp (lam * y i)
    ∀ᵐ x ∂(volume : Measure (Vec d)),
      reducedGenerator i ω 0 (fun y => h y * f y) x -
        f x * reducedGenerator i ω 0 h x = h x * reducedGenerator i ω lam f x := by
  let h : Vec d → ℝ := fun y => Real.exp (lam * y i)
  have hh : ContDiff ℝ 2 h := (contDiff_const.mul (contDiff_apply ℝ ℝ i)).exp
  have hderiv (x : Vec d) (j : Fin d) :
      fderiv ℝ h x (unitVector j) = h x * lam * unitVector i j := by
    have hd := ((hasFDerivAt_apply (𝕜 := ℝ) i x).const_mul lam).exp
    change fderiv ℝ (fun y : Vec d => Real.exp (lam * y i)) x (unitVector j) = _
    simp only [hd.fderiv, ContinuousLinearMap.smul_apply, smul_eq_mul,
      ContinuousLinearMap.proj_apply]
    have he : unitVector j i = unitVector i j := by
      simp only [unitVector, Pi.single_apply, eq_comm]
    rw [he]
    ring
  filter_upwards [c27_reduced_generator_product_ae hΛ hω i 0 h f hh hf] with x hx
  have hsym (j k : Fin d) : reducedCoefficient ω x j k = reducedCoefficient ω x k j := by
    have hs := congrArg (fun M : Mat d => M j k) (reducedCoefficient_symm hω x)
    exact hs.symm
  have hsum :
      (∑ j, ∑ k, reducedCoefficient ω x j k *
        (fderiv ℝ h x (unitVector j) * fderiv ℝ f x (unitVector k) +
          fderiv ℝ f x (unitVector j) * fderiv ℝ h x (unitVector k))) =
      2 * (h x * lam * dot ((reducedCoefficient ω x).mulVec (unitVector i))
        (gradient f x)) := by
    simp_rw [hderiv]
    simp only [mul_add, Finset.sum_add_distrib]
    conv_lhs => lhs; rw [Finset.sum_comm]
    simp only [dot, gradient, coordinateDerivative, unitVector, Pi.single_apply,
      Matrix.mulVec, dotProduct, mul_ite, ite_mul, mul_one, mul_zero, zero_mul,
      Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]
    simp only [Finset.mul_sum]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    rw [hsym i j]
    ring
  rw [hsum] at hx
  change _ - _ = h x * _
  have hforce : reducedGenerator i ω lam f x = reducedGenerator i ω 0 f x +
      lam * dot ((reducedCoefficient ω x).mulVec (unitVector i)) (gradient f x) := by
    simp only [reducedGenerator, zero_mul, add_zero]
  rw [hforce]
  linarith [hx]

/-- The exponential conjugating function has the actual reduced-force potential. -/
theorem c27_reduced_generator_exponential_potential_ae {d : ℕ}
    {Λ₀ : ℝ} (hΛ : 0 < Λ₀) {ω : FieldPair d} (hω : IsRegular Λ₀ ω)
    (i : Fin d) (lam : ℝ) :
    let h : Vec d → ℝ := fun y => Real.exp (lam * y i)
    ∀ᵐ x ∂(volume : Measure (Vec d)),
      reducedGenerator i ω 0 h x = h x *
        (lam * forcedDrift (reducedCoefficient ω) i 0 x i +
          (lam ^ 2 / 2) * reducedCoefficient ω x i i) := by
  let h : Vec d → ℝ := fun y => Real.exp (lam * y i)
  have hh : ContDiff ℝ 2 h := (contDiff_const.mul (contDiff_apply ℝ ℝ i)).exp
  have hderiv (x : Vec d) (j : Fin d) :
      fderiv ℝ h x (unitVector j) = h x * lam * unitVector i j := by
    have hd := ((hasFDerivAt_apply (𝕜 := ℝ) i x).const_mul lam).exp
    change fderiv ℝ (fun y : Vec d => Real.exp (lam * y i)) x (unitVector j) = _
    simp only [hd.fderiv, ContinuousLinearMap.smul_apply, smul_eq_mul,
      ContinuousLinearMap.proj_apply]
    have he : unitVector j i = unitVector i j := by
      simp only [unitVector, Pi.single_apply, eq_comm]
    rw [he]
    ring
  have hsecond (x : Vec d) (j k : Fin d) :
      fderiv ℝ (fun y => fderiv ℝ h y (unitVector k)) x (unitVector j) =
        h x * lam * unitVector i j * lam * unitVector i k := by
    rw [show (fun y => fderiv ℝ h y (unitVector k)) =
      (fun y => h y * (lam * unitVector i k)) from
      funext fun y => by rw [hderiv]; ring]
    rw [show fderiv ℝ (fun y => h y * (lam * unitVector i k)) x = _ from
      ((hh.differentiable (by simp) x).hasFDerivAt.mul_const _).fderiv]
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, hderiv]
    ring
  filter_upwards [c16_reduced_generator_ae_textbook hΛ hω] with x hx
  rw [hx i 0 h hh]
  unfold External.Draft.svGenerator
  simp_rw [hsecond, hderiv]
  simp only [unitVector, Pi.single_apply, mul_ite, ite_mul, mul_one, mul_zero,
    zero_mul, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]
  ring

/-- The finite-time signed weight is measurable on the actual path space. -/
theorem c27_reduced_force_exponential_weight_measurable {d : ℕ} {Λ₀ : ℝ}
    (hΛ : 0 < Λ₀) {ω : FieldPair d} (hω : IsRegular Λ₀ ω)
    (i : Fin d) (lam : ℝ) (x : Vec d) (T : ℝ≥0) :
    Measurable (fun γ : Path d => Real.exp
      (lam * ((γ T) i - x i) - ∫ u in Set.Ioc (0 : ℝ) (T : ℝ),
        (lam * forcedDrift (reducedCoefficient ω) i 0 (γ u.toNNReal) i +
          (lam ^ 2 / 2) * reducedCoefficient ω (γ u.toNNReal) i i))) := by
  have hp := (c25_reduced_force_path_weight_measurable hΛ hω i lam T).1
  have he : Measurable (fun γ : Path d => Real.exp (lam * ((γ T) i - x i))) := by
    apply Real.continuous_exp.measurable.comp
    have ht : Continuous (fun γ : Path d => γ T i) :=
      (continuous_apply i).comp (continuous_eval_const T)
    exact measurable_const.mul (ht.measurable.sub measurable_const)
  convert he.mul hp using 1
  ext γ
  simp only [Pi.mul_apply]
  rw [← Real.exp_add]
  congr 1

/-- The signed path weight is normalized when the force parameter vanishes. -/
theorem c27_reduced_force_exponential_weight_integral_zero_force {d : ℕ}
    {ω : FieldPair d} (i : Fin d) {x : Vec d} {P : Measure (Path d)}
    (hP : SolvesMartingaleProblem
      (External.Draft.svGenerator (reducedCoefficient ω)
        (forcedDrift (reducedCoefficient ω) i 0)) x P) (T : ℝ≥0) :
    let Z : Path d → ℝ := fun γ => Real.exp
      (0 * ((γ T) i - x i) - ∫ u in Set.Ioc (0 : ℝ) (T : ℝ),
        (0 * forcedDrift (reducedCoefficient ω) i 0 (γ u.toNNReal) i +
          (0 ^ 2 / 2) * reducedCoefficient ω (γ u.toNNReal) i i))
    Integrable Z P ∧ (∫ γ, Z γ ∂P) = 1 := by
  letI : IsProbabilityMeasure P := hP.1
  simp

/-- A maximal exponential moment controls the actual signed endpoint weight. -/
theorem c27_reduced_force_weight_integrable_of_max {d : ℕ} {Λ₀ : ℝ}
    (hΛ : 0 < Λ₀) {ω : FieldPair d} (hω : IsRegular Λ₀ ω)
    (i : Fin d) (lam : ℝ) (x : Vec d) (T : ℝ≥0) (P : Measure (Path d))
    (hmax : Integrable (fun γ : Path d => Real.exp (|lam| *
      sSup ((fun t : ℝ≥0 => |(γ t) i - x i|) '' Set.Icc 0 T))) P) :
    Integrable (fun γ : Path d => Real.exp
      (lam * ((γ T) i - x i) - ∫ u in Set.Ioc (0 : ℝ) (T : ℝ),
        (lam * forcedDrift (reducedCoefficient ω) i 0 (γ u.toNNReal) i +
          (lam ^ 2 / 2) * reducedCoefficient ω (γ u.toNNReal) i i))) P := by
  obtain ⟨M, hM, hb⟩ := c25_reduced_force_path_potential_integrable hΛ hω i lam
  apply (hmax.const_mul (Real.exp (M * (T : ℝ)))).mono'
    (c27_reduced_force_exponential_weight_measurable hΛ hω i lam x T).aestronglyMeasurable
  filter_upwards [] with γ
  have hc : Continuous (fun t : ℝ≥0 => |(γ t) i - x i|) :=
    (((continuous_apply i).comp γ.continuous).sub continuous_const).abs
  have hs : |(γ T) i - x i| ≤
      sSup ((fun t : ℝ≥0 => |(γ t) i - x i|) '' Set.Icc 0 T) :=
    le_csSup (isCompact_Icc.bddAbove_image hc.continuousOn)
      ⟨T, ⟨zero_le, le_rfl⟩, rfl⟩
  have he : lam * ((γ T) i - x i) ≤ |lam| *
      sSup ((fun t : ℝ≥0 => |(γ t) i - x i|) '' Set.Icc 0 T) :=
    (le_abs_self _).trans (by rw [abs_mul]; exact mul_le_mul_of_nonneg_left hs (abs_nonneg _))
  have hp := (abs_le.mp (hb γ T).2).1
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← Real.exp_add]
  exact Real.exp_le_exp.mpr (by linarith)

/-- A smooth compactly supported cutoff equal to one on the unit ball. -/
theorem c27_exists_cutoff (d : ℕ) : ∃ χ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ ∧
    HasCompactSupport χ ∧ (∀ y : Vec d, ‖y‖ ≤ 1 → χ y = 1) ∧
      ∀ y : Vec d, 0 ≤ χ y ∧ χ y ≤ 1 := by
  let b : ContDiffBump (0 : ℝ) := ⟨1, 2, one_pos, one_lt_two⟩
  refine ⟨fun y => ∏ k, b (y k), ?_, ?_, ?_, ?_⟩
  · exact contDiff_prod (fun k _ => b.contDiff.comp (contDiff_apply ℝ ℝ k))
  · apply HasCompactSupport.of_support_subset_isCompact
      (K := Set.pi Set.univ fun _ : Fin d => Metric.closedBall (0 : ℝ) 2)
    · exact isCompact_univ_pi fun _ => isCompact_closedBall _ _
    · intro y hy k _
      have hk : b (y k) ≠ 0 := fun h => hy (Finset.prod_eq_zero (Finset.mem_univ k) h)
      by_contra hc
      apply hk
      apply b.zero_of_le_dist
      rw [Metric.mem_closedBall, not_le] at hc
      exact hc.le
  · intro y hy
    apply Finset.prod_eq_one
    intro k _
    apply b.one_of_mem_closedBall
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (norm_le_pi_norm y k).trans hy
  · intro y
    exact ⟨Finset.prod_nonneg fun k _ => b.nonneg, Finset.prod_le_one₀ (fun k _ => b.nonneg)
      fun k _ => b.le_one⟩

/-- First- and second-derivative bounds for the dilated cutoffs, uniformly in the dilation. -/
theorem c27_cutoff_derivative_bounds {d : ℕ} {χ : Vec d → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ c : ℝ, 0 < c → c ≤ 1 → ∀ (y : Vec d) (i j : Fin d),
      |fderiv ℝ (fun z => χ (c • z)) y (unitVector j)| ≤ M ∧
      |fderiv ℝ (fun z => fderiv ℝ (fun z => χ (c • z)) z (unitVector j)) y
        (unitVector i)| ≤ M := by
  have hF : ∀ j : Fin d, ContDiff ℝ (⊤ : ℕ∞) (fun w => fderiv ℝ χ w (unitVector j)) := fun j =>
    (hχ.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiff_const
  have h1 : ∀ j : Fin d, ∃ B : ℝ, ∀ w, |fderiv ℝ χ w (unitVector j)| ≤ B := fun j => by
    obtain ⟨B, hB⟩ := (hF j).continuous.bounded_above_of_compact_support
      (hc.fderiv_apply ℝ (unitVector j))
    exact ⟨B, fun w => by simpa only [Real.norm_eq_abs] using hB w⟩
  have h2 : ∀ i j : Fin d, ∃ B : ℝ, ∀ w,
      |fderiv ℝ (fun w => fderiv ℝ χ w (unitVector j)) w (unitVector i)| ≤ B := fun i j => by
    have hcs : HasCompactSupport (fun w => fderiv ℝ χ w (unitVector j)) :=
      hc.fderiv_apply ℝ (unitVector j)
    have hcont : Continuous (fun w => fderiv ℝ (fun w => fderiv ℝ χ w (unitVector j)) w
        (unitVector i)) :=
      ((hF j).fderiv_right (m := (⊤ : ℕ∞)) (by simp)).continuous.clm_apply continuous_const
    obtain ⟨B, hB⟩ := hcont.bounded_above_of_compact_support (hcs.fderiv_apply ℝ (unitVector i))
    exact ⟨B, fun w => by simpa only [Real.norm_eq_abs] using hB w⟩
  choose B1 hB1 using h1
  choose B2 hB2 using h2
  refine ⟨∑ j, |B1 j| + ∑ i, ∑ j, |B2 i j|, by positivity, fun c hc0 hc1 y i j => ?_⟩
  have hfd : ∀ z, fderiv ℝ (fun z => χ (c • z)) z (unitVector j) =
      c * fderiv ℝ χ (c • z) (unitVector j) := fun z => by
    rw [fderiv_comp_smul]; simp
  have hs1 : |B1 j| ≤ ∑ j, |B1 j| := Finset.single_le_sum (f := fun j => |B1 j|)
    (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
  have hs2 : |B2 i j| ≤ ∑ i, ∑ j, |B2 i j| :=
    (Finset.single_le_sum (f := fun j => |B2 i j|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ j)).trans (Finset.single_le_sum (f := fun i => ∑ j, |B2 i j|)
      (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ i))
  have hn1 : 0 ≤ ∑ j, |B1 j| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hn2 : 0 ≤ ∑ i, ∑ j, |B2 i j| := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  constructor
  · rw [hfd, abs_mul, abs_of_pos hc0]
    calc c * |fderiv ℝ χ (c • y) (unitVector j)| ≤ 1 * |B1 j| := by
          apply mul_le_mul hc1 ((hB1 j _).trans (le_abs_self _)) (abs_nonneg _) zero_le_one
      _ ≤ _ := by linarith
  · have : (fun z => fderiv ℝ (fun z => χ (c • z)) z (unitVector j)) =
        fun z => c * (fun w => fderiv ℝ χ w (unitVector j)) (c • z) := funext hfd
    have hdiff : DifferentiableAt ℝ (fun z => (fun w => fderiv ℝ χ w (unitVector j)) (c • z)) y :=
      (((hF j).differentiable (by simp)).comp (differentiable_id.const_smul c)) y
    have h3 : fderiv ℝ (fun z => (fun w => fderiv ℝ χ w (unitVector j)) (c • z)) y =
        c • fderiv ℝ (fun w => fderiv ℝ χ w (unitVector j)) (c • y) := fderiv_comp_smul (f := fun w => fderiv ℝ χ w (unitVector j)) (x := y) c
    rw [this, fderiv_const_mul hdiff, h3]
    simp only [smul_apply, smul_eq_mul, abs_mul, abs_of_pos hc0]
    calc c * (c * |fderiv ℝ (fun w => fderiv ℝ χ w (unitVector j)) (c • y) (unitVector i)|)
        ≤ 1 * (1 * |B2 i j|) := by
          apply mul_le_mul hc1 _ (by positivity) zero_le_one
          exact mul_le_mul hc1 ((hB2 i j _).trans (le_abs_self _)) (abs_nonneg _) zero_le_one
      _ ≤ _ := by linarith

/-- Exact first derivative of a function times a coordinate exponential. -/
theorem c27_fderiv_first_mul_exp {d : ℕ} (i0 : Fin d) (lam : ℝ) (x0 : Vec d) {u : Vec d → ℝ}
    (hu : Differentiable ℝ u) (z : Vec d) (j : Fin d) :
    fderiv ℝ (fun z => u z * Real.exp (lam * (z i0 - x0 i0))) z (unitVector j) =
      Real.exp (lam * (z i0 - x0 i0)) *
        (fderiv ℝ u z (unitVector j) + lam * (if j = i0 then 1 else 0) * u z) := by
  have h : HasFDerivAt (fun z : Vec d => lam * (z i0 - x0 i0))
      (lam • (ContinuousLinearMap.proj i0 : Vec d →L[ℝ] ℝ)) z :=
    ((hasFDerivAt_apply i0 z).sub_const _).const_mul lam
  have h2 : HasFDerivAt (fun z => u z * Real.exp (lam * (z i0 - x0 i0))) _ z :=
    (hu z).hasFDerivAt.mul h.exp
  rw [h2.fderiv]
  have hv : unitVector j i0 = if j = i0 then 1 else 0 := by
    by_cases hk : j = i0
    · subst hk; simp [unitVector]
    · simp [unitVector, hk, Ne.symm hk]
  simp only [add_apply, smul_apply, smul_eq_mul, ContinuousLinearMap.proj_apply, hv]
  ring

/-- Exact second derivative of a smooth function times a coordinate exponential. -/
theorem c27_fderiv_second_mul_exp {d : ℕ} (i0 : Fin d) (lam : ℝ) (x0 : Vec d) {u : Vec d → ℝ}
    (hu : ContDiff ℝ 2 u) (y : Vec d) (i j : Fin d) :
    fderiv ℝ (fun z => fderiv ℝ (fun z => u z * Real.exp (lam * (z i0 - x0 i0))) z
        (unitVector j)) y (unitVector i) =
      Real.exp (lam * (y i0 - x0 i0)) *
        (fderiv ℝ (fun z => fderiv ℝ u z (unitVector j)) y (unitVector i) +
          lam * (if i = i0 then 1 else 0) * fderiv ℝ u y (unitVector j) +
          lam * (if j = i0 then 1 else 0) * fderiv ℝ u y (unitVector i) +
          lam ^ 2 * (if i = i0 then 1 else 0) * (if j = i0 then 1 else 0) * u y) := by
  set g : Vec d → ℝ := fun z => Real.exp (lam * (z i0 - x0 i0)) with hgdef
  have hgd : ∀ z, HasFDerivAt g ((g z * lam) • (ContinuousLinearMap.proj i0 : Vec d →L[ℝ] ℝ)) z :=
    fun z => by
      have h : HasFDerivAt (fun z : Vec d => lam * (z i0 - x0 i0))
          (lam • (ContinuousLinearMap.proj i0 : Vec d →L[ℝ] ℝ)) z :=
        ((hasFDerivAt_apply i0 z).sub_const _).const_mul lam
      have := h.exp
      convert this using 1
      ext v; simp [hgdef]; ring
  have hge : ∀ z (k : Fin d), fderiv ℝ g z (unitVector k) = g z * (lam * if k = i0 then 1 else 0) := by
    intro z k
    rw [(hgd z).fderiv]
    by_cases hk : k = i0
    · subst hk; simp [unitVector]
    · simp [unitVector, hk, Ne.symm hk]
  have hu1 : ContDiff ℝ 1 (fderiv ℝ u) := hu.fderiv_right (m := 1) (by norm_num)
  have hA : ∀ k : Fin d, Differentiable ℝ (fun z => fderiv ℝ u z (unitVector k)) := fun k =>
    (hu1.clm_apply contDiff_const).differentiable (by norm_num)
  have hud : Differentiable ℝ u := hu.differentiable (by norm_num)
  have hfun : (fun z => fderiv ℝ (fun z => u z * g z) z (unitVector j)) =
      fun z => fderiv ℝ u z (unitVector j) * g z + u z * (g z * (lam * if j = i0 then 1 else 0)) := by
    funext z
    have hdu : DifferentiableAt ℝ u z := hud z
    have hdg : DifferentiableAt ℝ g z := (hgd z).differentiableAt
    rw [fderiv_fun_mul hdu hdg]
    simp only [add_apply, smul_apply, smul_eq_mul]
    rw [hge z j]; ring
  have hdA : HasFDerivAt (fun z => fderiv ℝ u z (unitVector j))
      (fderiv ℝ (fun z => fderiv ℝ u z (unitVector j)) y) y := (hA j y).hasFDerivAt
  have hdu : HasFDerivAt u (fderiv ℝ u y) y := (hud y).hasFDerivAt
  have h1 := (hdA.mul (hgd y))
  have h2 := hdu.mul ((hgd y).mul_const (lam * if j = i0 then 1 else 0))
  have h4 : HasFDerivAt (fun z => fderiv ℝ u z (unitVector j) * g z +
      u z * (g z * (lam * if j = i0 then 1 else 0))) _ y := h1.add h2
  show fderiv ℝ (fun z => fderiv ℝ (fun z => u z * g z) z (unitVector j)) y (unitVector i) = _
  rw [hfun, h4.fderiv]
  have hv : ∀ k : Fin d, unitVector k i0 = if k = i0 then 1 else 0 := fun k => by
    by_cases hk : k = i0
    · subst hk; simp [unitVector]
    · simp [unitVector, hk, Ne.symm hk]
  simp only [add_apply, smul_apply, smul_eq_mul,
    ContinuousLinearMap.proj_apply, hv]
  by_cases h1 : i = i0 <;> by_cases h2 : j = i0 <;> simp [h1, h2, hgdef] <;> ring


/-- The Stroock–Varadhan generator of a smooth function times a coordinate exponential. -/
theorem c27_svGenerator_mul_exp {d : ℕ} (a : Vec d → Mat d) (b : Vec d → Vec d) (i0 : Fin d)
    (lam : ℝ) (x0 : Vec d) {u : Vec d → ℝ} (hu : ContDiff ℝ 2 u) (y : Vec d) :
    External.Draft.svGenerator a b (fun z => u z * Real.exp (lam * (z i0 - x0 i0))) y =
      Real.exp (lam * (y i0 - x0 i0)) *
        ((1 / 2 : ℝ) * ∑ i, ∑ j, a y i j *
          (fderiv ℝ (fun z => fderiv ℝ u z (unitVector j)) y (unitVector i) +
            lam * (if i = i0 then 1 else 0) * fderiv ℝ u y (unitVector j) +
            lam * (if j = i0 then 1 else 0) * fderiv ℝ u y (unitVector i)) +
          ∑ i, b y i * fderiv ℝ u y (unitVector i)) +
      (lam * b y i0 + lam ^ 2 / 2 * a y i0 i0) *
        (u y * Real.exp (lam * (y i0 - x0 i0))) := by
  unfold External.Draft.svGenerator
  simp_rw [c27_fderiv_second_mul_exp i0 lam x0 hu,
    c27_fderiv_first_mul_exp i0 lam x0 (hu.differentiable (by norm_num)) y]
  set g := Real.exp (lam * (y i0 - x0 i0))
  set D2 : Fin d → Fin d → ℝ := fun i j =>
    fderiv ℝ (fun z => fderiv ℝ u z (unitVector j)) y (unitVector i) with hD2
  set D1 : Fin d → ℝ := fun i => fderiv ℝ u y (unitVector i) with hD1
  set δ : Fin d → ℝ := fun i => if i = i0 then 1 else 0 with hδ
  have hq : ∑ i, ∑ j, a y i j * (g * (lam ^ 2 * δ i * δ j * u y)) =
      g * (lam ^ 2 * u y * a y i0 i0) := by
    rw [Finset.sum_eq_single i0 (fun i _ hi => by simp [hδ, hi]) (by simp)]
    rw [Finset.sum_eq_single i0 (fun j _ hj => by simp [hδ, hj]) (by simp)]
    simp only [hδ, ↓reduceIte]; ring
  have hb : ∑ i, b y i * (g * (lam * δ i * u y)) = g * (lam * u y * b y i0) := by
    rw [Finset.sum_eq_single i0 (fun i _ hi => by simp [hδ, hi]) (by simp)]
    simp only [hδ, ↓reduceIte]; ring
  have h1 : ∑ i, ∑ j, a y i j * (g * (D2 i j + lam * δ i * D1 j + lam * δ j * D1 i +
      lam ^ 2 * δ i * δ j * u y)) =
      g * ∑ i, ∑ j, a y i j * (D2 i j + lam * δ i * D1 j + lam * δ j * D1 i) +
        ∑ i, ∑ j, a y i j * (g * (lam ^ 2 * δ i * δ j * u y)) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have h2 : ∑ i, b y i * (g * (D1 i + lam * δ i * u y)) =
      g * ∑ i, b y i * D1 i + ∑ i, b y i * (g * (lam * δ i * u y)) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  show 1 / 2 * ∑ i, ∑ j, a y i j * (g * (D2 i j + lam * δ i * D1 j + lam * δ j * D1 i +
      lam ^ 2 * δ i * δ j * u y)) + ∑ i, b y i * (g * (D1 i + lam * δ i * u y)) = _
  rw [h1, h2, hq, hb]
  ring

/-- The dilated cutoff has vanishing first and second derivatives inside its unit region. -/
theorem c27_cutoff_derivatives_zero {d : ℕ} {χ : Vec d → ℝ}
    (h1 : ∀ y : Vec d, ‖y‖ ≤ 1 → χ y = 1) (c : ℝ) (y : Vec d) (hy : ‖c • y‖ < 1)
    (i j : Fin d) :
    fderiv ℝ (fun z => χ (c • z)) y (unitVector j) = 0 ∧
    fderiv ℝ (fun z => fderiv ℝ (fun z => χ (c • z)) z (unitVector j)) y (unitVector i) = 0 := by
  have hopen : IsOpen {z : Vec d | ‖c • z‖ < 1} :=
    isOpen_lt (continuous_norm.comp (continuous_const_smul c)) continuous_const
  have hev : ∀ᶠ z in 𝓝 y, (fun z => χ (c • z)) z = 1 :=
    Filter.eventually_of_mem (hopen.mem_nhds hy) fun z hz => h1 _ (le_of_lt hz)
  have hD : ∀ᶠ z in 𝓝 y, fderiv ℝ (fun z => χ (c • z)) z = 0 := by
    filter_upwards [hev.eventually_nhds] with z hz
    have hz' : (fun z => χ (c • z)) =ᶠ[𝓝 z] fun _ => (1 : ℝ) := hz
    rw [hz'.fderiv_eq]
    simp
  have hD0 : fderiv ℝ (fun z => χ (c • z)) y = 0 := hD.self_of_nhds
  refine ⟨by simp [hD0], ?_⟩
  have : (fun z => fderiv ℝ (fun z => χ (c • z)) z (unitVector j)) =ᶠ[𝓝 y] fun _ => (0 : ℝ) :=
    hD.mono fun z hz => by simp [hz]
  rw [this.fderiv_eq]
  simp

end EinsteinFull
