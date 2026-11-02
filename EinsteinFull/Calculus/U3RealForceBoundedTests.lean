import EinsteinFull.Calculus.U3RealForceQuenchedAction
import EinsteinRelation.Correctors.StationaryWeightedOrbit

/-! Boundary cases of the signed-force bounded-test identification. -/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology

noncomputable section
namespace EinsteinFull
open EinsteinRelation

/-- At zero force, the supplied unforced process identifies bounded tests. -/
theorem u3_real_force_bounded_tests_zero_force
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀)
    (hunforced : UnforcedAt hd Q) (hpath : PathwiseAt Q) (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ ω 0) 0 (Y (0, ω)))
    (t : ℝ≥0) (g : BoundedContinuousFunction (FieldPair d) ℂ)
    (F : Lp ℂ 2 (reducedLaw Q)) (hF : F =ᵐ[reducedLaw Q] (fun ρ => g ρ)) :
    (fun ω => forcedComplexEvolution Q ⟨0, by omega⟩ 0 t F (reduce ω)) =ᵐ[Q.measure]
      fun ω => ∫ γ : Path d, g (translate (γ t) (reduce ω)) ∂Y (0, ω) := by
  have ha := c27_zero_force_quenched_action_of_unforced (hunforced := hunforced) hd Q Y hY t F
  have he := u3_supplied_force_endpoint_ae_eq_of_deps (hunforced := hunforced) (hpath := hpath) hd Q 0 Y hY t
    (fun ρ => F ρ) (fun ρ => g ρ) (Lp.stronglyMeasurable F).measurable g.continuous.measurable hF
  filter_upwards [ha, he] with ω hω heω
  exact hω.2.trans (integral_congr_ae heω)

/-- At time zero, the supplied initial condition identifies bounded tests. -/
theorem u3_real_force_bounded_tests_zero_time
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀)
    (hunforced : UnforcedAt hd Q) (hpath : PathwiseAt Q) (lam : ℝ) (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ ω lam) 0 (Y (0, ω)))
    (g : BoundedContinuousFunction (FieldPair d) ℂ)
    (F : Lp ℂ 2 (reducedLaw Q)) (hF : F =ᵐ[reducedLaw Q] (fun ρ => g ρ)) :
    (fun ω => forcedComplexEvolution Q ⟨0, by omega⟩ (lam : ℂ) 0 F (reduce ω)) =ᵐ[Q.measure]
      fun ω => ∫ γ : Path d, g (translate (γ 0) (reduce ω)) ∂Y (0, ω) := by
  have ha := c27_real_force_quenched_action_zero_time hd Q lam Y hY F
  have he := u3_supplied_force_endpoint_ae_eq_of_deps (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY 0
    (fun ρ => F ρ) (fun ρ => g ρ) (Lp.stronglyMeasurable F).measurable g.continuous.measurable hF
  filter_upwards [ha, he] with ω hω heω
  exact hω.2.trans (integral_congr_ae heω)

/-- The finite-horizon density converges quantitatively to one in mean square.
The estimate is uniform in the regular environment. -/
theorem u3_supplied_force_density_centered_second_moment_of_pathwise
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hpath : PathwiseAt Q)
    (i : Fin d) (lam : ℝ) (Y₀ : QuenchedPathLaws d)
    (hY₀ : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator i ω 0) 0 (Y₀ (0, ω)))
    (t : ℝ≥0) :
    ∀ᵐ ω ∂Q.measure,
      (∫ γ : Path d, (Real.exp
        (lam * ((γ t) i - (0 : Vec d) i) - ∫ u in Set.Ioc (0 : ℝ) (t : ℝ),
          (lam * forcedDrift (reducedCoefficient ω) i 0 (γ u.toNNReal) i +
            (lam ^ 2 / 2) * reducedCoefficient ω (γ u.toNNReal) i i)) - 1) ^ 2 ∂Y₀ (0, ω)) ≤
      Real.exp (lam ^ 2 * (Real.exp (2 * Λ₀) * Λ₀) * (t : ℝ)) - 1 := by
  have hΛ : 0 < Λ₀ := lt_of_lt_of_le zero_lt_one Q.ellipticity_parameter
  obtain ⟨Y, _, hactual⟩ := foundation_reduced_actual_kernel hd hΛ i lam
  have hY : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator i ω lam) 0 (Y (0, ω)) := by
    filter_upwards [Q.regular] with ω hω
    exact hactual ω hω
  filter_upwards [hY₀,
    u3_supplied_reduced_force_density_memLp_two_of_pathwise (hpath := hpath) hd Q i lam Y₀ hY₀ t,
    u3_supplied_force_density_lintegral_eq_one_of_pathwise (hpath := hpath) hd Q i lam Y₀ Y hY₀ hY t,
    u3_supplied_force_density_second_moment_bound_of_pathwise (hpath := hpath) hd Q i lam Y₀ hY₀ t]
    with ω hprob hmem hmass hbound
  let : IsProbabilityMeasure (Y₀ (0, ω)) := hprob.1
  let Z : Path d → ℝ := fun γ => Real.exp
    (lam * ((γ t) i - (0 : Vec d) i) - ∫ u in Set.Ioc (0 : ℝ) (t : ℝ),
      (lam * forcedDrift (reducedCoefficient ω) i 0 (γ u.toNNReal) i +
        (lam ^ 2 / 2) * reducedCoefficient ω (γ u.toNNReal) i i))
  change MemLp Z 2 (Y₀ (0, ω)) at hmem
  change (∫⁻ γ, ENNReal.ofReal (Z γ) ∂Y₀ (0, ω)) = 1 at hmass
  change (∫⁻ γ, ENNReal.ofReal (Z γ ^ 2) ∂Y₀ (0, ω)) ≤ _ at hbound
  have hi : Integrable Z (Y₀ (0, ω)) := hmem.integrable (by norm_num)
  have hs : Integrable (fun γ => Z γ ^ 2) (Y₀ (0, ω)) := hmem.integrable_sq
  have hm : ∫ γ, Z γ ∂Y₀ (0, ω) = 1 := by
    rw [← ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall fun γ => (Real.exp_pos _).le)] at hmass
    exact ENNReal.ofReal_eq_one.mp hmass
  have hb : (∫ γ, Z γ ^ 2 ∂Y₀ (0, ω)) ≤
      Real.exp (lam ^ 2 * (Real.exp (2 * Λ₀) * Λ₀) * (t : ℝ)) := by
    rw [← ofReal_integral_eq_lintegral_ofReal hs (Filter.Eventually.of_forall fun γ => sq_nonneg _)] at hbound
    exact (ENNReal.ofReal_le_ofReal_iff (Real.exp_pos _).le).mp hbound
  have he : (fun γ => (Z γ - 1) ^ 2) = fun γ => Z γ ^ 2 - 2 * Z γ + 1 := by
    funext γ
    ring
  change (∫ γ, (Z γ - 1) ^ 2 ∂Y₀ (0, ω)) ≤ _
  rw [he]
  change (∫ γ, (((fun γ : Path d => Z γ ^ 2) - (fun γ : Path d => 2 * Z γ)) : Path d → ℝ) γ + (1 : ℝ) ∂Y₀ (0, ω)) ≤ _
  rw [integral_add (hs.sub (hi.const_mul 2)) (integrable_const 1)]
  change (∫ γ, Z γ ^ 2 - 2 * Z γ ∂Y₀ (0, ω)) + _ ≤ _
  rw [integral_sub hs (hi.const_mul 2), integral_const_mul, hm]
  simp only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]
  linarith

/-- The centered signed density has a uniform extended L² bound. -/
theorem u3_supplied_force_density_centered_eLpNorm_two_bound_of_pathwise
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hpath : PathwiseAt Q)
    (i : Fin d) (lam : ℝ) (Y₀ : QuenchedPathLaws d)
    (hY₀ : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator i ω 0) 0 (Y₀ (0, ω)))
    (t : ℝ≥0) :
    ∀ᵐ ω ∂Q.measure, eLpNorm (fun γ : Path d => Real.exp
      (lam * ((γ t) i - (0 : Vec d) i) - ∫ u in Set.Ioc (0 : ℝ) (t : ℝ),
        (lam * forcedDrift (reducedCoefficient ω) i 0 (γ u.toNNReal) i +
          (lam ^ 2 / 2) * reducedCoefficient ω (γ u.toNNReal) i i)) - 1) 2 (Y₀ (0, ω)) ≤
      ENNReal.ofReal (Real.exp (lam ^ 2 * (Real.exp (2 * Λ₀) * Λ₀) * (t : ℝ)) - 1) ^
        (1 / 2 : ℝ) := by
  filter_upwards [hY₀,
    u3_supplied_reduced_force_density_memLp_two_of_pathwise (hpath := hpath) hd Q i lam Y₀ hY₀ t,
    u3_supplied_force_density_centered_second_moment_of_pathwise (hpath := hpath) hd Q i lam Y₀ hY₀ t]
    with ω hprob hZ hbound
  let : IsProbabilityMeasure (Y₀ (0, ω)) := hprob.1
  let Z : Path d → ℝ := fun γ => Real.exp
    (lam * ((γ t) i - (0 : Vec d) i) - ∫ u in Set.Ioc (0 : ℝ) (t : ℝ),
      (lam * forcedDrift (reducedCoefficient ω) i 0 (γ u.toNNReal) i +
        (lam ^ 2 / 2) * reducedCoefficient ω (γ u.toNNReal) i i)) - 1
  have hmem : MemLp Z 2 (Y₀ (0, ω)) := hZ.sub (memLp_const 1)
  change (∫ γ, Z γ ^ 2 ∂Y₀ (0, ω)) ≤ _ at hbound
  change eLpNorm Z 2 (Y₀ (0, ω)) ≤ _
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hmem.aestronglyMeasurable]
  apply ENNReal.rpow_le_rpow _ (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hz : ∀ γ, ‖Z γ‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (Z γ ^ 2) := by
    intro γ
    rw [ENNReal.rpow_two, Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
  simp only [ENNReal.toReal_ofNat, hz]
  rw [← ofReal_integral_eq_lintegral_ofReal hmem.integrable_sq
    (Filter.Eventually.of_forall fun γ => sq_nonneg _)]
  exact ENNReal.ofReal_le_ofReal hbound

/-- The signed and unforced endpoint actions differ by a quantity controlled
by the centered density and the unforced endpoint L² norm. -/
theorem u3_supplied_force_endpoint_difference_enorm_bound_of_deps
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hunforced : UnforcedAt hd Q) (hpath : PathwiseAt Q)
    (lam : ℝ) (Y₀ Y : QuenchedPathLaws d)
    (hY₀ : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ ω 0) 0 (Y₀ (0, ω)))
    (hY : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ ω lam) 0 (Y (0, ω)))
    (t : ℝ≥0) (f : Lp ℂ 2 (reducedLaw Q)) :
    ∀ᵐ ω ∂Q.measure,
      ‖(∫ γ : Path d, f (translate (γ t) (reduce ω)) ∂Y (0, ω)) -
        (∫ γ : Path d, f (translate (γ t) (reduce ω)) ∂Y₀ (0, ω))‖ₑ ≤
        ENNReal.ofReal (Real.exp (lam ^ 2 * (Real.exp (2 * Λ₀) * Λ₀) * (t : ℝ)) - 1) ^
          (1 / 2 : ℝ) *
          eLpNorm (fun γ : Path d => f (translate (γ t) (reduce ω))) 2 (Y₀ (0, ω)) := by
  filter_upwards [hY₀,
    u3_supplied_force_endpoint_integral_eq_tilt_of_pathwise (hpath := hpath) hd Q
      ⟨0, by omega⟩ lam Y₀ Y hY₀ hY t f (Lp.stronglyMeasurable f),
    u3_supplied_reduced_force_density_memLp_two_of_pathwise (hpath := hpath) hd Q
      ⟨0, by omega⟩ lam Y₀ hY₀ t,
    u3_supplied_unforced_endpoint_memLp_two_of_deps (hunforced := hunforced) (hpath := hpath) hd Q Y₀ hY₀ t f,
    u3_supplied_force_density_centered_eLpNorm_two_bound_of_pathwise (hpath := hpath) hd Q
      ⟨0, by omega⟩ lam Y₀ hY₀ t] with ω hprob heq hZ hU hbound
  let : IsProbabilityMeasure (Y₀ (0, ω)) := hprob.1
  let Z : Path d → ℝ := fun γ => Real.exp
    (lam * ((γ t) ⟨0, by omega⟩ - (0 : Vec d) ⟨0, by omega⟩) - ∫ u in Set.Ioc (0 : ℝ) (t : ℝ),
      (lam * forcedDrift (reducedCoefficient ω) ⟨0, by omega⟩ 0 (γ u.toNNReal) ⟨0, by omega⟩ +
        (lam ^ 2 / 2) * reducedCoefficient ω (γ u.toNNReal) ⟨0, by omega⟩ ⟨0, by omega⟩))
  let V : Path d → ℝ := fun γ => Z γ - 1
  let U : Path d → ℂ := fun γ => f (translate (γ t) (reduce ω))
  change MemLp Z 2 (Y₀ (0, ω)) at hZ
  change MemLp U 2 (Y₀ (0, ω)) at hU
  have hV : MemLp V 2 (Y₀ (0, ω)) := hZ.sub (memLp_const 1)
  change eLpNorm V 2 (Y₀ (0, ω)) ≤ _ at hbound
  have hh := ENNReal.lintegral_mul_le_Lp_mul_Lq (Y₀ (0, ω))
    Real.HolderConjugate.two_two hV.aemeasurable.enorm hU.aemeasurable.enorm
  have hholder : (∫⁻ γ, ‖V γ‖ₑ * ‖U γ‖ₑ ∂Y₀ (0, ω)) ≤
      eLpNorm V 2 (Y₀ (0, ω)) * eLpNorm U 2 (Y₀ (0, ω)) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hV.aestronglyMeasurable,
      eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hU.aestronglyMeasurable]
    simpa only [Pi.mul_apply, ENNReal.toReal_ofNat] using hh
  rw [heq]
  change ‖(∫ γ, (Z γ : ℂ) * U γ ∂Y₀ (0, ω)) - ∫ γ, U γ ∂Y₀ (0, ω)‖ₑ ≤ _
  have hid : (∫ γ, (Z γ : ℂ) * U γ ∂Y₀ (0, ω)) - (∫ γ, U γ ∂Y₀ (0, ω)) =
      ∫ γ, ((Z γ : ℂ) * U γ - U γ) ∂Y₀ (0, ω) := by
    symm
    exact integral_sub (f := fun γ : Path d => (Z γ : ℂ) * U γ) (g := U)
      (hZ.ofReal.integrable_mul hU) (hU.integrable (by norm_num))
  rw [hid]
  have he : (fun γ => (Z γ : ℂ) * U γ - U γ) = fun γ => (V γ : ℂ) * U γ := by
    funext γ
    simp only [V, Complex.ofReal_sub, Complex.ofReal_one, sub_mul, one_mul]
  rw [he]
  calc
    _ ≤ ∫⁻ γ, ‖(V γ : ℂ) * U γ‖ₑ ∂Y₀ (0, ω) := enorm_integral_le_lintegral_enorm _
    _ = ∫⁻ γ, ‖V γ‖ₑ * ‖U γ‖ₑ ∂Y₀ (0, ω) := by
      apply lintegral_congr
      intro γ
      rw [enorm_mul]
      congr 1
      apply enorm_eq_iff_norm_eq.mpr
      simpa only [Real.norm_eq_abs] using Complex.norm_real (V γ)
    _ ≤ eLpNorm V 2 (Y₀ (0, ω)) * eLpNorm U 2 (Y₀ (0, ω)) := hholder
    _ ≤ _ := mul_le_mul' hbound le_rfl

/-- Signed Dynkin formula for bounded C² observables of the reduced diffusion. -/
theorem u3_reduced_signed_bounded_C2_dynkin {d : ℕ} {Λ₀ : ℝ}
    (hΛ : 0 < Λ₀) {ω : FieldPair d} (hω : IsRegular Λ₀ ω)
    (i : Fin d) (lam : ℝ) {x : Vec d} {P : Measure (Path d)}
    (hP : SolvesMartingaleProblem (External.Draft.svGenerator
      (reducedCoefficient ω) (forcedDrift (reducedCoefficient ω) i lam)) x P)
    (f : Vec d → ℝ) (hf : ContDiff ℝ 2 f)
    (hb : ∃ M : ℝ, 0 ≤ M ∧ ∀ y : Vec d, |f y| ≤ M ∧
      (∀ j : Fin d, |coordinateDerivative j f y| ≤ M) ∧
      ∀ j k : Fin d, |coordinateDerivative k (coordinateDerivative j f) y| ≤ M)
    (T : ℝ≥0) :
    Integrable (fun γ : Path d => ∫ u in Set.Ioc (0 : ℝ) (T : ℝ),
      External.Draft.svGenerator (reducedCoefficient ω)
        (forcedDrift (reducedCoefficient ω) i lam) f (γ u.toNNReal)) P ∧
    (∫ γ : Path d, (∫ u in Set.Ioc (0 : ℝ) (T : ℝ),
      External.Draft.svGenerator (reducedCoefficient ω)
        (forcedDrift (reducedCoefficient ω) i lam) f (γ u.toNNReal)) ∂P) =
      (∫ γ : Path d, f (γ T) ∂P) - f x := by
  letI : IsProbabilityMeasure P := hP.1
  let A := reducedCoefficient ω
  let b := forcedDrift A i lam
  let L := External.Draft.svGenerator A b
  obtain ⟨hA, _, ⟨Ma, hAb⟩, _, hbm, ⟨Mb, hbb⟩⟩ := reduced_svHypotheses hΛ hω i lam
  obtain ⟨M, _, hfbd⟩ := hb
  obtain ⟨C, hC⟩ := c17_bounded_svGenerator_of_bounded_derivatives A b hAb hbb f
    (fun y j => (hfbd y).2.1 j) (fun y j k => (hfbd y).2.2 j k)
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
  have hcoef : BddCoef A b (max Ma Mb) :=
    ⟨fun k j => (hA.matrix_elem k j).measurable,
      fun k => (measurable_pi_apply k).comp hbm,
      fun y k j => (hAb y k j).trans (le_max_left _ _),
      fun y k => (hbb y k).trans (le_max_right _ _)⟩
  have hsource := External.Bass.solves_of_frozen hP hA.measurable hbm hAb hbb
  have hmart := (hsource.2.2 f hf).2.martingale_of_bounded (by
    intro t
    refine ⟨2 * M + C * t, fun s hs γ => ?_⟩
    calc
      ‖External.Bass.compensatedTest A b f s γ‖ ≤ 2 * M + C * s :=
        norm_compensatedTest_le L f (fun y => by simpa only [Real.norm_eq_abs] using (hfbd y).1)
          hC s (External.Bass.pathMeasurableEquiv d γ)
      _ ≤ 2 * M + C * t := add_le_add_right
        (mul_le_mul_of_nonneg_left (NNReal.coe_le_coe.mpr hs) hC0) _)
  have had := stronglyAdapted_compensatedTest_of_measurable L f hf.continuous
    (hcoef.measurable_gen f)
  have hm : Martingale (compensatedTest L f) (pathFiltration d) P := by
    have h := External.Bass.martingale_map_pathMeasurableEquiv hmart had
    simpa only [External.Bass.map_pathMeasurableEquiv_symm_roundtrip] using h
  have hF (t : ℝ≥0) : Integrable (fun γ : Path d => f (γ t)) P :=
    Integrable.of_bound (hf.continuous.measurable.comp (measurable_pathPosition t)).aestronglyMeasurable
      M (ae_of_all _ fun γ => by simpa only [Real.norm_eq_abs] using (hfbd (γ t)).1)
  have hsub : Integrable (fun γ : Path d => f (γ T) - f (γ 0)) P := (hF T).sub (hF 0)
  have heq : (fun γ : Path d => ∫ u in (0 : ℝ)..(T : ℝ), L f (γ u.toNNReal)) =
      fun γ => f (γ T) - f (γ 0) - compensatedTest L f T γ := by
    funext γ
    dsimp only [compensatedTest]
    ring
  have hstart : (∫ γ : Path d, f (γ 0) ∂P) = f x := by
    calc
      _ = ∫ _ : Path d, f x ∂P := integral_congr_ae (hP.2.1.mono fun _ h => congrArg f h)
      _ = f x := by simp
  have hz : (∫ γ : Path d, compensatedTest L f T γ ∂P) = 0 := by
    have hzero : compensatedTest L f 0 = fun _ => (0 : ℝ) := by
      funext γ
      simp only [compensatedTest, NNReal.coe_zero, intervalIntegral.integral_same, sub_self]
    have h := hm.setIntegral_eq (show (0 : ℝ≥0) ≤ T from bot_le) MeasurableSet.univ
    simpa only [Measure.restrict_univ, hzero, integral_zero] using h.symm
  simp_rw [← intervalIntegral.integral_of_le T.coe_nonneg]
  change Integrable (fun γ : Path d => ∫ u in (0 : ℝ)..(T : ℝ), L f (γ u.toNNReal)) P ∧
    (∫ γ : Path d, (∫ u in (0 : ℝ)..(T : ℝ), L f (γ u.toNNReal)) ∂P) =
      (∫ γ : Path d, f (γ T) ∂P) - f x
  refine ⟨?_, ?_⟩
  · rw [heq]
    exact hsub.sub (hm.integrable T)
  · rw [heq, integral_sub hsub (hm.integrable T), integral_sub (hF T) (hF 0),
      hstart, hz, sub_zero]

/-- The actual supplied signed law satisfies Dynkin's formula on horizontal
 test orbits, for almost every environment. -/
theorem u3_supplied_signed_horizontal_test_dynkin_of_pathwise
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hpath : PathwiseAt Q)
    (i : Fin d) (lam : ℝ) (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator i ω lam) 0 (Y (0, ω)))
    (F : FieldPair d → ℝ) (hF : IsHorizontalTest F) (T : ℝ≥0) :
    ∀ᵐ ω ∂Q.measure,
      Integrable (fun γ : Path d => ∫ u in Set.Ioc (0 : ℝ) (T : ℝ),
        External.Draft.svGenerator (reducedCoefficient ω)
          (forcedDrift (reducedCoefficient ω) i lam) (orbit F (reduce ω)) (γ u.toNNReal)) (Y (0, ω)) ∧
      (∫ γ : Path d, (∫ u in Set.Ioc (0 : ℝ) (T : ℝ),
        External.Draft.svGenerator (reducedCoefficient ω)
          (forcedDrift (reducedCoefficient ω) i lam) (orbit F (reduce ω)) (γ u.toNNReal)) ∂Y (0, ω)) =
        (∫ γ : Path d, orbit F (reduce ω) (γ T) ∂Y (0, ω)) - orbit F (reduce ω) 0 := by
  have hΛ : 0 < Λ₀ := lt_of_lt_of_le zero_lt_one Q.ellipticity_parameter
  filter_upwards [Q.regular, u3_supplied_reduced_law_solves_textbook_of_pathwise
    (hpath := hpath) hd Q i lam Y hY] with ω hω hP
  exact u3_reduced_signed_bounded_C2_dynkin hΛ hω i lam hP (orbit F (reduce ω))
    (contDiff_two_of_top (hF.2.1 (reduce ω)))
    (c17_horizontal_test_bounded_C2 F hF (reduce ω)) T

/-- The signed environment generator agrees with the spatial generator along an orbit. -/
theorem u3_signed_envGenerator_eq_svGenerator {d : ℕ} (hd : 2 ≤ d)
    (w : FieldPair d) (F : FieldPair d → ℝ) (lam : ℝ)
    (hsym : ∀ x j k, w.1 x j k = w.1 x k j) (x : Vec d) :
    envGenerator hd lam F (translate x w) =
      External.Draft.svGenerator (fun y => w.1 y)
        (forcedDrift (fun y => w.1 y) (EinsteinRelation.External.GantertSection7Support.firstCoordinateIndex hd) lam) (orbit F w) x := by
  rw [envGenerator_translate]
  simp only [External.Draft.svGenerator, forcedDrift,
    matrixDivDrift, coordinateDerivative]
  have hmul (j : Fin d) : (w.1 x).mulVec
      (unitVector (EinsteinRelation.External.GantertSection7Support.firstCoordinateIndex hd)) j =
      w.1 x j (EinsteinRelation.External.GantertSection7Support.firstCoordinateIndex hd) := by
    simp [Matrix.mulVec, dotProduct, unitVector, Pi.single_apply]
  simp only [hmul]
  have hcoeff (j k : Fin d) :
      (fun y => w.1 y j k) = (fun y => w.1 y k j) := funext fun y => hsym y j k
  have hsecond :
      (∑ k, ∑ j, w.1 x j k *
        fderiv ℝ (fun y => fderiv ℝ (orbit F w) y (unitVector j)) x (unitVector k)) =
      ∑ k, ∑ j, w.1 x k j *
        fderiv ℝ (fun y => fderiv ℝ (orbit F w) y (unitVector j)) x (unitVector k) := by
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hsym x j k]
  have hfirst :
      (∑ k, ∑ j, fderiv ℝ (fun y => w.1 y j k) x (unitVector k) *
        fderiv ℝ (orbit F w) x (unitVector j)) =
      ∑ j, (∑ k, fderiv ℝ (fun y => w.1 y k j) x (unitVector k)) *
        fderiv ℝ (orbit F w) x (unitVector j) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hcoeff j k]
  have hdrift :
      (∑ j, ((1 / 2 : ℝ) * ∑ k, fderiv ℝ (fun y => w.1 y k j) x (unitVector k)) *
        fderiv ℝ (orbit F w) x (unitVector j)) =
      (1 / 2 : ℝ) * ∑ j, (∑ k, fderiv ℝ (fun y => w.1 y k j) x (unitVector k)) *
        fderiv ℝ (orbit F w) x (unitVector j) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  simp_rw [add_mul, Finset.sum_add_distrib]
  rw [hsecond, hfirst, hdrift, Finset.mul_sum]
  ring


/-- Dynkin's formula in the environment-generator form for the supplied signed law. -/
theorem u3_supplied_signed_environment_test_dynkin_of_pathwise
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hpath : PathwiseAt Q)
    (lam : ℝ) (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ ω lam) 0 (Y (0, ω)))
    (F : FieldPair d → ℝ) (hF : IsHorizontalTest F) (T : ℝ≥0) :
    ∀ᵐ ω ∂Q.measure,
      Integrable (fun γ : Path d => ∫ u in Set.Ioc (0 : ℝ) (T : ℝ),
        envGenerator hd lam F (translate (γ u.toNNReal) (reduce ω))) (Y (0, ω)) ∧
      (∫ γ : Path d, (∫ u in Set.Ioc (0 : ℝ) (T : ℝ),
        envGenerator hd lam F (translate (γ u.toNNReal) (reduce ω))) ∂Y (0, ω)) =
        (∫ γ : Path d, F (translate (γ T) (reduce ω)) ∂Y (0, ω)) - F (reduce ω) := by
  filter_upwards [Q.regular, u3_supplied_signed_horizontal_test_dynkin_of_pathwise
    (hpath := hpath) hd Q ⟨0, by omega⟩ lam Y hY F hF T] with ω hω h
  have hs : ∀ x j k, (reduce ω).1 x j k = (reduce ω).1 x k j := by
    intro x j k
    have he := congrArg (fun M : Mat d => M j k) (reducedCoefficient_symm hω x)
    exact he.symm
  have he (x : Vec d) : envGenerator hd lam F (translate x (reduce ω)) =
      External.Draft.svGenerator (reducedCoefficient ω)
        (forcedDrift (reducedCoefficient ω) ⟨0, by omega⟩ lam)
          (orbit F (reduce ω)) x := by
    exact u3_signed_envGenerator_eq_svGenerator hd (reduce ω) F lam hs x
  simp_rw [← he] at h
  simpa only [orbit, translate_zero] using h

/-- Integral evolution equation on horizontal tests for the supplied signed law. -/
theorem u3_supplied_signed_environment_test_integral_equation_of_pathwise
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hpath : PathwiseAt Q)
    (lam : ℝ) (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ ω lam) 0 (Y (0, ω)))
    (F : FieldPair d → ℝ) (hF : IsHorizontalTest F) (T : ℝ≥0) :
    ∀ᵐ ω ∂Q.measure,
      (∫ γ : Path d, F (translate (γ T) (reduce ω)) ∂Y (0, ω)) - F (reduce ω) =
        ∫ u in Set.Ioc (0 : ℝ) (T : ℝ),
          ∫ γ : Path d, envGenerator hd lam F (translate (γ u.toNNReal) (reduce ω)) ∂Y (0, ω) := by
  obtain ⟨B, hB0, hB⟩ := exists_abs_envGenerator_le hd lam hF (Entropy.sourceReducedBound_pos' Λ₀)
  let Φ : FieldPair d → Path d → ℝ → ℝ := fun ω γ u =>
    envGenerator hd lam F (translate (γ u.toNNReal) (reduce ω))
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
    (measurable_envGenerator hd lam hF).comp henv
  filter_upwards [Q.regular, hY,
    u3_supplied_signed_environment_test_dynkin_of_pathwise (hpath := hpath) hd Q lam Y hY F hF T]
    with ω hω hprob hdyn
  letI : IsProbabilityMeasure (Y (0, ω)) := hprob.1
  have hfin : IsFiniteMeasure (volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ))) :=
    ⟨by rw [Measure.restrict_apply_univ]; simp⟩
  have hint : Integrable (Function.uncurry fun (γ : Path d) (u : ℝ) => Φ ω γ u)
      ((Y (0, ω)).prod (volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ)))) := by
    refine (integrable_const B).mono'
      (hΦm.comp ((measurable_const.prodMk measurable_snd).prodMk measurable_fst)).aestronglyMeasurable
      (ae_of_all _ fun p => ?_)
    rw [Real.norm_eq_abs]
    exact hΦB ω hω _ _
  have hswap := integral_integral_swap hint
  rw [hswap] at hdyn
  exact hdyn.2.symm

/-- Reduced-law L² residuals vanish in annealed absolute endpoint occupation
for the supplied signed law. This transfers generator approximations through
fixed-time path evaluation. -/
theorem u3_supplied_force_endpoint_residual_tendsto_of_deps
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hunforced : UnforcedAt hd Q) (hpath : PathwiseAt Q)
    (lam : ℝ) (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ ω lam) 0 (Y (0, ω)))
    (t : ℝ≥0) (f : ℕ → Lp ℂ 2 (reducedLaw Q))
    (hf : Filter.Tendsto (fun n => eLpNorm (fun ρ => f n ρ) 2 (reducedLaw Q))
      Filter.atTop (𝓝 0)) :
    Filter.Tendsto (fun n => ∫⁻ ω, ∫⁻ γ : Path d,
      ‖f n (translate (γ t) (reduce ω))‖ₑ ∂Y (0, ω) ∂Q.measure)
      Filter.atTop (𝓝 0) := by
  let C : ℝ≥0∞ := ENNReal.ofReal (Real.exp
    (lam ^ 2 * (Real.exp (2 * Λ₀) * Λ₀) * (t : ℝ))) ^ (1 / 2 : ℝ)
  have hC : C ≠ ∞ := by
    exact ne_of_lt (ENNReal.rpow_lt_top_of_nonneg (by norm_num) ENNReal.ofReal_lt_top.ne)
  have hb : ∀ n, (∫⁻ ω, ∫⁻ γ : Path d,
      ‖f n (translate (γ t) (reduce ω))‖ₑ ∂Y (0, ω) ∂Q.measure) ≤
      C * eLpNorm (fun ρ => f n ρ) 2 (reducedLaw Q) :=
    fun n => u3_supplied_force_endpoint_annealed_absolute_bound_of_deps
      (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY t (f n)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa only [mul_zero] using (ENNReal.Tendsto.const_mul hf (Or.inr hC)))
    (fun _ => bot_le) hb

/-- Every actual signed graph pair admits the existing unforced resolvent
mollification, with the actual signed drift included in the right-hand side. -/
theorem u3_signed_graph_unforced_residual_representatives
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (i : Fin d) (ζ : ℂ) (s : ℝ) (hs : 0 < s)
    (f g : Lp ℂ 2 (reducedLaw Q))
    (hfg : IsComplexGeneratorPair Q i ζ f g)
    {G : Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hG : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) f G)
    (L : ℂ →L[ℝ] ℝ) :
    ∃ (r : ℕ → FieldPair d → ℝ) (hr : ∀ n, MemLp (r n) 2 (reducedLaw Q)),
      (∀ n, Measurable (r n)) ∧
      (∀ n, r n =ᵐ[reducedLaw Q] fun w =>
        s * horizontalMollify (Calculus.unitMassScaledMollifier d (Entropy.scaleSeq n))
          (fun v => L (f v)) w -
        envGenerator hd 0 (horizontalMollify
          (Calculus.unitMassScaledMollifier d (Entropy.scaleSeq n))
          (fun v => L (f v))) w -
        L (((s : ℂ) • f - (g + (0 - ζ) •
          complexForceDrift Q i (WithLp.toLp 2 G))) w)) ∧
      Filter.Tendsto (fun n => ‖(hr n).toLp (r n)‖) Filter.atTop (𝓝 0) := by
  let rhs := (s : ℂ) • f - (g + (0 - ζ) • complexForceDrift Q i (WithLp.toLp 2 G))
  have hzero := hfg.change_force 0 hG
  have hres : unforcedComplexResolvent Q i s hs rhs = f :=
    (isComplexGeneratorPair_iff_resolvent Q i s hs f _).mp hzero
  have hGrad : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
      (unforcedComplexResolvent Q i s hs rhs) G := by
    rw [hres]
    exact hG
  obtain ⟨r, hr, hm, he, ht⟩ :=
    c17_resolvent_residual_representatives hd Q i s hs rhs hGrad L
  refine ⟨r, hr, hm, ?_, ht⟩
  intro n
  simpa only [hres] using he n

/-- The coefficient-column drift of a mollified horizontal gradient converges
in reduced-law L² to the actual projected drift. -/
theorem u3_mollified_projected_drift_tendsto
    {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d)
    (G : Fin d → Lp ℂ 2 (reducedLaw Q)) (L : ℂ →L[ℝ] ℝ) :
    Filter.Tendsto (fun δ : ℝ => eLpNorm (fun w =>
      ∑ j, w.1 0 j i * (horizontalMollify
        (Calculus.unitMassScaledMollifier d δ) (fun v => L (G j v)) w - L (G j w)))
      2 (reducedLaw Q)) (𝓝[>] 0) (𝓝 0) := by
  letI : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  have hB : ∀ᵐ w ∂reducedLaw Q, ∀ j, |w.1 0 j i| ≤ Real.exp (2 * Λ₀) * Λ₀ := by
    apply (Probability.measurableEmbedding_reduce d).ae_map_iff.mpr
    filter_upwards [Q.regular] with ω hω
    exact fun j => abs_reducedCoefficient_le
      (lt_of_lt_of_le zero_lt_one Q.ellipticity_parameter) hω 0 j i
  have hlim (j : Fin d) : Filter.Tendsto (fun δ : ℝ => eLpNorm (fun w =>
      w.1 0 j i * (horizontalMollify (Calculus.unitMassScaledMollifier d δ)
        (fun v => L (G j v)) w - L (G j w))) 2 (reducedLaw Q)) (𝓝[>] 0) (𝓝 0) := by
    let V : FieldPair d → ℝ := fun v => L (G j v)
    have hVm : Measurable V := L.continuous.measurable.comp (Lp.stronglyMeasurable (G j)).measurable
    have hV : MemLp V 2 (reducedLaw Q) := L.comp_memLp' (Lp.memLp (G j))
    have hconv := Calculus.tendsto_eLpNorm_horizontalMollify_unitMassScaledMollifier
      (reducedLaw Q) (reducedLaw_stationary Q) 2 ENNReal.ofNat_ne_top hVm hV
    let C : ℝ := Real.exp (2 * Λ₀) * Λ₀
    have hb (δ : ℝ) : eLpNorm (fun w => w.1 0 j i *
        (horizontalMollify (Calculus.unitMassScaledMollifier d δ) V w - V w)) 2 (reducedLaw Q) ≤
        ‖C‖ₑ * eLpNorm (fun w => horizontalMollify
          (Calculus.unitMassScaledMollifier d δ) V w - V w) 2 (reducedLaw Q) := by
      have hm : Measurable (fun w => w.1 0 j i *
          (horizontalMollify (Calculus.unitMassScaledMollifier d δ) V w - V w)) :=
        ((((continuous_eval_const (0 : Vec d)).comp continuous_fst).matrix_elem j i).measurable).mul
          ((measurable_horizontalMollify _
            (Entropy.contDiff_unitMassScaledMollifier δ).continuous.measurable hVm).sub hVm)
      calc
        _ ≤ eLpNorm (fun w => C * (horizontalMollify
              (Calculus.unitMassScaledMollifier d δ) V w - V w)) 2 (reducedLaw Q) :=
          eLpNorm_mono_ae hm.aestronglyMeasurable (hB.mono fun w hw => by
            simp only [Real.norm_eq_abs, abs_mul]
            exact mul_le_mul_of_nonneg_right ((hw j).trans (le_abs_self C)) (abs_nonneg _))
        _ = _ := eLpNorm_const_smul C _ _ _
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (by simpa only [mul_zero] using (ENNReal.Tendsto.const_mul hconv
        (Or.inr (by simp : ‖C‖ₑ ≠ ∞)))) (fun _ => bot_le) hb
  have hsum (s : Finset (Fin d)) : Filter.Tendsto (fun δ : ℝ => eLpNorm (fun w =>
      ∑ j ∈ s, w.1 0 j i * (horizontalMollify
        (Calculus.unitMassScaledMollifier d δ) (fun v => L (G j v)) w - L (G j w)))
      2 (reducedLaw Q)) (𝓝[>] 0) (𝓝 0) := by
    induction s using Finset.induction_on with
    | empty => simpa using (tendsto_const_nhds : Filter.Tendsto (fun _ : ℝ => (0 : ℝ≥0∞)) (𝓝[>] 0) (𝓝 0))
    | @insert j s hj ih =>
      simp only [Finset.sum_insert hj]
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
        (by simpa only [add_zero] using (hlim j).add ih) (fun _ => bot_le)
        (fun _ => eLpNorm_add_le (by norm_num))
  simpa using hsum Finset.univ

/-- The spatial derivatives of the mollified graph function recover its
actual projected coefficient drift in reduced-law L². -/
theorem u3_mollified_graph_drift_tendsto
    {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d)
    {f : Lp ℂ 2 (reducedLaw Q)} {G : Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hG : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) f G)
    (L : ℂ →L[ℝ] ℝ) :
    Filter.Tendsto (fun δ : ℝ => eLpNorm (fun w => ∑ j, w.1 0 j i *
      (coordinateDerivative j (orbit (horizontalMollify
        (Calculus.unitMassScaledMollifier d δ) (fun v => L (f v))) w) 0 - L (G j w)))
      2 (reducedLaw Q)) (𝓝[>] 0) (𝓝 0) := by
  letI : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  have hlim := u3_mollified_projected_drift_tendsto Q i G L
  apply hlim.congr'
  have hδ1 : ∀ᶠ δ : ℝ in 𝓝[>] 0, δ ≤ 1 :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds (eventually_le_nhds zero_lt_one)
  filter_upwards [self_mem_nhdsWithin, hδ1] with δ (hδ : 0 < δ) hδ1
  apply eLpNorm_congr_ae
  filter_upwards [c17_complex_gradient_mollified_orbit_derivative (reducedLaw Q)
    (reducedLaw_stationary Q) hG L hδ hδ1] with w hw
  simp only [hw]

/-- The mollified coefficient drift converges to the actual complex graph drift
under every real-linear scalar projection. -/
theorem u3_mollified_actual_graph_drift_tendsto
    {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d)
    {f : Lp ℂ 2 (reducedLaw Q)} {G : Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hG : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) f G)
    (L : ℂ →L[ℝ] ℝ) :
    Filter.Tendsto (fun δ : ℝ => eLpNorm (fun w =>
      (∑ j, w.1 0 j i * coordinateDerivative j (orbit (horizontalMollify
        (Calculus.unitMassScaledMollifier d δ) (fun v => L (f v))) w) 0) -
      L (complexForceDrift Q i (WithLp.toLp 2 G) w)) 2 (reducedLaw Q))
      (𝓝[>] 0) (𝓝 0) := by
  have hlim := u3_mollified_graph_drift_tendsto Q i hG L
  apply hlim.congr'
  filter_upwards [] with δ
  apply eLpNorm_congr_ae
  filter_upwards [complexForceDrift_coe Q i (WithLp.toLp 2 G)] with w hw
  rw [hw, map_sum]
  simp only [← Complex.real_smul, map_smul, smul_eq_mul,
    ← Finset.sum_sub_distrib]
  congr 1
  funext j
  ring

/-- The mollified actual signed graph has a vanishing generator residual in L². -/
theorem u3_signed_graph_mollified_residual_tendsto
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam s : ℝ) (hs : 0 < s) (f g : Lp ℂ 2 (reducedLaw Q))
    (hfg : IsComplexGeneratorPair Q ⟨0, by omega⟩ (lam : ℂ) f g)
    {G : Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hG : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) f G)
    (L : ℂ →L[ℝ] ℝ) :
    Filter.Tendsto (fun n : ℕ => eLpNorm (fun w =>
      s * horizontalMollify (Calculus.unitMassScaledMollifier d (Entropy.scaleSeq n))
        (fun v => L (f v)) w -
      envGenerator hd lam (horizontalMollify
        (Calculus.unitMassScaledMollifier d (Entropy.scaleSeq n)) (fun v => L (f v))) w -
      L (((s : ℂ) • f - g) w)) 2 (reducedLaw Q)) Filter.atTop (𝓝 0) := by
  let i : Fin d := ⟨0, by omega⟩
  let D := complexForceDrift Q i (WithLp.toLp 2 G)
  let V (n : ℕ) := horizontalMollify
    (Calculus.unitMassScaledMollifier d (Entropy.scaleSeq n)) (fun v => L (f v))
  let b (n : ℕ) (w : FieldPair d) :=
    (∑ j, w.1 0 j i * coordinateDerivative j (orbit (V n) w) 0) - L (D w)
  obtain ⟨r, hr, hm, he, ht⟩ :=
    u3_signed_graph_unforced_residual_representatives hd Q i (lam : ℂ) s hs f g hfg hG L
  have hr_lim : Filter.Tendsto (fun n => eLpNorm (r n) 2 (reducedLaw Q)) Filter.atTop (𝓝 0) := by
    have ht' := ENNReal.tendsto_ofReal ht
    simp only [ENNReal.ofReal_zero] at ht'
    apply ht'.congr
    intro n
    rw [Lp.norm_def, eLpNorm_congr_ae (hr n).coeFn_toLp,
      ENNReal.ofReal_toReal (hr n).eLpNorm_ne_top]
  have hb_lim : Filter.Tendsto (fun n => eLpNorm (b n) 2 (reducedLaw Q)) Filter.atTop (𝓝 0) :=
    (u3_mollified_actual_graph_drift_tendsto Q i hG L).comp Entropy.tendsto_scaleSeq
  have heq (n : ℕ) : (fun w => s * V n w - envGenerator hd lam (V n) w -
      L (((s : ℂ) • f - g) w)) =ᵐ[reducedLaw Q] (fun w => r n w - lam * b n w) := by
    filter_upwards [he n, Lp.coeFn_sub ((s : ℂ) • f) (g + (0 - (lam : ℂ)) • D),
      Lp.coeFn_add g ((0 - (lam : ℂ)) • D), Lp.coeFn_smul (0 - (lam : ℂ)) D,
      Lp.coeFn_sub ((s : ℂ) • f) g] with w hw h1 h2 h3 h4
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply] at h1 h2 h3 h4
    have hL : L ((0 - (lam : ℂ)) • D w) = -lam * L (D w) := by
      simp only [zero_sub, neg_smul, map_neg]
      have h := L.map_smul lam (D w)
      simp only [Complex.real_smul, smul_eq_mul] at h
      simp only [smul_eq_mul]
      rw [h]
      ring
    have hgen : envGenerator hd lam (V n) w = envGenerator hd 0 (V n) w +
        lam * ∑ j, w.1 0 j i * coordinateDerivative j (orbit (V n) w) 0 := by
      simp only [envGenerator, zero_mul, add_zero, horizontalDerivative]
      rfl
    rw [hw, h1, h2, h3, h4]
    simp only [map_sub, map_add]
    rw [hL, hgen]
    dsimp [b, V]
    ring
  have hbound (n : ℕ) : eLpNorm (fun w => s * V n w - envGenerator hd lam (V n) w -
      L (((s : ℂ) • f - g) w)) 2 (reducedLaw Q) ≤
      eLpNorm (r n) 2 (reducedLaw Q) + ‖lam‖ₑ * eLpNorm (b n) 2 (reducedLaw Q) := by
    rw [eLpNorm_congr_ae (heq n)]
    calc
      _ ≤ eLpNorm (r n) 2 (reducedLaw Q) + eLpNorm (fun w => lam * b n w) 2 (reducedLaw Q) :=
        eLpNorm_sub_le (by norm_num)
      _ = _ := by
        change eLpNorm (r n) 2 (reducedLaw Q) + eLpNorm (lam • b n) 2 (reducedLaw Q) = _
        rw [eLpNorm_const_smul]
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ (fun _ => bot_le) hbound
  change Filter.Tendsto _ _ (𝓝 (0 : ℝ≥0∞))
  simpa only [mul_zero, add_zero] using hr_lim.add
    (ENNReal.Tendsto.const_mul hb_lim (Or.inr (by simp : ‖lam‖ₑ ≠ ∞)))

/-- Measurable L² representatives for the error in the mollified actual drift. -/
theorem u3_mollified_graph_drift_representatives
    {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d)
    {f : Lp ℂ 2 (reducedLaw Q)} {G : Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hG : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) f G)
    (L : ℂ →L[ℝ] ℝ) :
    ∃ (r : ℕ → FieldPair d → ℝ) (hr : ∀ n, MemLp (r n) 2 (reducedLaw Q)),
      (∀ n, Measurable (r n)) ∧
      (∀ n, r n =ᵐ[reducedLaw Q] fun w =>
        (∑ j, w.1 0 j i * coordinateDerivative j (orbit (horizontalMollify
          (Calculus.unitMassScaledMollifier d (Entropy.scaleSeq n)) (fun v => L (f v))) w) 0) -
        L (complexForceDrift Q i (WithLp.toLp 2 G) w)) ∧
      Filter.Tendsto (fun n => ‖(hr n).toLp (r n)‖) Filter.atTop (𝓝 0) := by
  letI : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  let D := complexForceDrift Q i (WithLp.toLp 2 G)
  let V (j : Fin d) (w : FieldPair d) := L (G j w)
  let r (n : ℕ) (w : FieldPair d) :=
    (∑ j, w.1 0 j i * horizontalMollify
      (Calculus.unitMassScaledMollifier d (Entropy.scaleSeq n)) (V j) w) - L (D w)
  have hVm (j : Fin d) : Measurable (V j) :=
    L.continuous.measurable.comp (Lp.stronglyMeasurable (G j)).measurable
  have hV (j : Fin d) : MemLp (V j) 2 (reducedLaw Q) :=
    L.comp_memLp' (Lp.memLp (G j))
  have hcoef (j : Fin d) : MemLp (fun w : FieldPair d => w.1 0 j i) ∞ (reducedLaw Q) := by
    simpa using (memLp_reduced_coefficient_complex Q j i).re
  have hm (n : ℕ) : Measurable (r n) := by
    apply Measurable.sub
    · exact Finset.measurable_sum _ fun j _ =>
        ((((continuous_eval_const (0 : Vec d)).comp continuous_fst).matrix_elem j i).measurable).mul
          (measurable_horizontalMollify _
            (Entropy.contDiff_unitMassScaledMollifier _).continuous.measurable (hVm j))
    · exact L.continuous.measurable.comp (Lp.stronglyMeasurable D).measurable
  have hr (n : ℕ) : MemLp (r n) 2 (reducedLaw Q) := by
    apply MemLp.sub
    · apply memLp_finset_sum
      intro j _
      have hM := Entropy.memLp_horizontalMollify_unitMass (reducedLaw_stationary Q)
        (Entropy.scaleSeq_pos n) ENNReal.ofNat_ne_top (hVm j) (hV j)
      simpa only [mul_comm] using hM.mul' (r := 2) (hcoef j)
    · exact L.comp_memLp' (Lp.memLp D)
  have he (n : ℕ) : r n =ᵐ[reducedLaw Q] fun w =>
      (∑ j, w.1 0 j i * coordinateDerivative j (orbit (horizontalMollify
        (Calculus.unitMassScaledMollifier d (Entropy.scaleSeq n)) (fun v => L (f v))) w) 0) -
      L (D w) := by
    filter_upwards [c17_complex_gradient_mollified_orbit_derivative (reducedLaw Q)
      (reducedLaw_stationary Q) hG L (Entropy.scaleSeq_pos n) (Entropy.scaleSeq_le_one n)] with w hw
    simp only [r, V, hw]
  refine ⟨r, hr, hm, he, ?_⟩
  have ht := (u3_mollified_actual_graph_drift_tendsto Q i hG L).comp Entropy.tendsto_scaleSeq
  have htr := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp ht
  simp only [ENNReal.toReal_zero] at htr
  apply htr.congr
  intro n
  rw [Lp.norm_def, eLpNorm_congr_ae (hr n).coeFn_toLp, eLpNorm_congr_ae (he n)]
  rfl

/-- The actual signed graph residual has measurable L² representatives whose
norms vanish under horizontal mollification. -/
theorem u3_signed_graph_mollified_residual_representatives
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam s : ℝ) (hs : 0 < s) (f g : Lp ℂ 2 (reducedLaw Q))
    (hfg : IsComplexGeneratorPair Q ⟨0, by omega⟩ (lam : ℂ) f g)
    {G : Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hG : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) f G)
    (L : ℂ →L[ℝ] ℝ) :
    ∃ (r : ℕ → FieldPair d → ℝ) (hr : ∀ n, MemLp (r n) 2 (reducedLaw Q)),
      (∀ n, Measurable (r n)) ∧
      (∀ n, r n =ᵐ[reducedLaw Q] fun w =>
        s * horizontalMollify (Calculus.unitMassScaledMollifier d (Entropy.scaleSeq n))
          (fun v => L (f v)) w -
        envGenerator hd lam (horizontalMollify
          (Calculus.unitMassScaledMollifier d (Entropy.scaleSeq n)) (fun v => L (f v))) w -
        L (((s : ℂ) • f - g) w)) ∧
      Filter.Tendsto (fun n => ‖(hr n).toLp (r n)‖) Filter.atTop (𝓝 0) := by
  let i : Fin d := ⟨0, by omega⟩
  let D := complexForceDrift Q i (WithLp.toLp 2 G)
  let V (n : ℕ) := horizontalMollify
    (Calculus.unitMassScaledMollifier d (Entropy.scaleSeq n)) (fun v => L (f v))
  obtain ⟨a, ha, ham, hae, _⟩ :=
    u3_signed_graph_unforced_residual_representatives hd Q i (lam : ℂ) s hs f g hfg hG L
  obtain ⟨b, hb, hbm, hbe, _⟩ := u3_mollified_graph_drift_representatives Q i hG L
  let r (n : ℕ) (w : FieldPair d) := a n w - lam * b n w
  have hr (n : ℕ) : MemLp (r n) 2 (reducedLaw Q) := (ha n).sub ((hb n).const_mul lam)
  have hm (n : ℕ) : Measurable (r n) := (ham n).sub (measurable_const.mul (hbm n))
  have he (n : ℕ) : r n =ᵐ[reducedLaw Q] fun w =>
      s * V n w - envGenerator hd lam (V n) w - L (((s : ℂ) • f - g) w) := by
    filter_upwards [hae n, hbe n, Lp.coeFn_sub ((s : ℂ) • f) (g + (0 - (lam : ℂ)) • D),
      Lp.coeFn_add g ((0 - (lam : ℂ)) • D), Lp.coeFn_smul (0 - (lam : ℂ)) D,
      Lp.coeFn_sub ((s : ℂ) • f) g] with w h₁ h₂ h₃ h₄ h₅ h₆
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply] at h₃ h₄ h₅ h₆
    have hL : L ((0 - (lam : ℂ)) • D w) = -lam * L (D w) := by
      simp only [zero_sub, neg_smul, map_neg]
      have h := L.map_smul lam (D w)
      simp only [Complex.real_smul, smul_eq_mul] at h
      simp only [smul_eq_mul]
      rw [h]
      ring
    have hgen : envGenerator hd lam (V n) w = envGenerator hd 0 (V n) w +
        lam * ∑ j, w.1 0 j i * coordinateDerivative j (orbit (V n) w) 0 := by
      simp only [envGenerator, zero_mul, add_zero, horizontalDerivative]
      rfl
    change a n w - lam * b n w = s * V n w - envGenerator hd lam (V n) w -
      L (((s : ℂ) • f - g) w)
    rw [h₆, h₁, h₂, h₃, h₄, h₅]
    simp only [map_sub, map_add]
    rw [hL, hgen]
    dsimp [V]
    ring
  refine ⟨r, hr, hm, he, ?_⟩
  have ht := u3_signed_graph_mollified_residual_tendsto hd Q lam s hs f g hfg hG L
  have htr := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp ht
  simp only [ENNReal.toReal_zero] at htr
  apply htr.congr
  intro n
  rw [Lp.norm_def, eLpNorm_congr_ae (hr n).coeFn_toLp, eLpNorm_congr_ae (he n)]
  rfl

/-- Each literal signed generator of the mollified graph function has a
measurable reduced-law L² representative. -/
theorem u3_signed_graph_mollified_generator_representatives
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam s : ℝ) (hs : 0 < s) (f g : Lp ℂ 2 (reducedLaw Q))
    (hfg : IsComplexGeneratorPair Q ⟨0, by omega⟩ (lam : ℂ) f g)
    {G : Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hG : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) f G)
    (L : ℂ →L[ℝ] ℝ) :
    ∃ a : ℕ → FieldPair d → ℝ,
      (∀ n, Measurable (a n)) ∧ (∀ n, MemLp (a n) 2 (reducedLaw Q)) ∧
      ∀ n, a n =ᵐ[reducedLaw Q] fun w =>
        envGenerator hd lam (horizontalMollify
          (Calculus.unitMassScaledMollifier d (Entropy.scaleSeq n)) (fun v => L (f v))) w := by
  obtain ⟨r, hr, hm, he, _⟩ :=
    u3_signed_graph_mollified_residual_representatives hd Q lam s hs f g hfg hG L
  let V : FieldPair d → ℝ := fun w => L (f w)
  let R : Lp ℂ 2 (reducedLaw Q) := (s : ℂ) • f - g
  let M (n : ℕ) := horizontalMollify
    (Calculus.unitMassScaledMollifier d (Entropy.scaleSeq n)) V
  let a (n : ℕ) (w : FieldPair d) := s * M n w - r n w - L (R w)
  have hVm : Measurable V := L.continuous.measurable.comp (Lp.stronglyMeasurable f).measurable
  have hV : MemLp V 2 (reducedLaw Q) := L.comp_memLp' (Lp.memLp f)
  have hMm (n : ℕ) : Measurable (M n) :=
    measurable_horizontalMollify _
      (Entropy.contDiff_unitMassScaledMollifier _).continuous.measurable hVm
  have hM (n : ℕ) : MemLp (M n) 2 (reducedLaw Q) :=
    Entropy.memLp_horizontalMollify_unitMass (reducedLaw_stationary Q)
      (Entropy.scaleSeq_pos n) ENNReal.ofNat_ne_top hVm hV
  refine ⟨a, ?_, ?_, ?_⟩
  · intro n
    exact ((measurable_const.mul (hMm n)).sub (hm n)).sub
      (L.continuous.measurable.comp (Lp.stronglyMeasurable R).measurable)
  · intro n
    exact (((hM n).const_mul s).sub (hr n)).sub (L.comp_memLp' (Lp.memLp R))
  · intro n
    filter_upwards [he n] with w hw
    change s * M n w - r n w - L (R w) = envGenerator hd lam (M n) w
    change r n w = s * M n w - envGenerator hd lam (M n) w - L (R w) at hw
    linarith

#print axioms u3_signed_graph_mollified_generator_representatives

/-- Every reduced-law L² observation has finite annealed absolute occupation
on a finite horizon under the original supplied signed path laws. -/
theorem u3_supplied_force_finite_time_occupation_bound_of_deps
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hunforced : UnforcedAt hd Q) (hpath : PathwiseAt Q)
    (lam : ℝ) (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ ω lam) 0 (Y (0, ω)))
    (T : ℝ≥0) (f : Lp ℂ 2 (reducedLaw Q)) :
    (∫⁻ t in Set.Ioc (0 : ℝ) (T : ℝ),
      ∫⁻ ω, ∫⁻ γ : Path d, ‖f (translate (γ t.toNNReal) (reduce ω))‖ₑ
        ∂Y (0, ω) ∂Q.measure) ≤
      (ENNReal.ofReal (Real.exp (lam ^ 2 * (Real.exp (2 * Λ₀) * Λ₀) * (T : ℝ))) ^
        (1 / 2 : ℝ) * eLpNorm (fun ρ => f ρ) 2 (reducedLaw Q)) *
          (volume : Measure ℝ) (Set.Ioc 0 (T : ℝ)) := by
  let C : ℝ≥0∞ := ENNReal.ofReal (Real.exp
    (lam ^ 2 * (Real.exp (2 * Λ₀) * Λ₀) * (T : ℝ))) ^ (1 / 2 : ℝ)
  have hk : 0 ≤ lam ^ 2 * (Real.exp (2 * Λ₀) * Λ₀) := by
    have hΛ : 0 < Λ₀ := lt_of_lt_of_le zero_lt_one Q.ellipticity_parameter
    positivity
  calc
    _ ≤ ∫⁻ _ in Set.Ioc (0 : ℝ) (T : ℝ), C * eLpNorm (fun ρ => f ρ) 2 (reducedLaw Q) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      apply (u3_supplied_force_endpoint_annealed_absolute_bound_of_deps
        (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY t.toNNReal f).trans
      apply mul_le_mul' _ le_rfl
      apply ENNReal.rpow_le_rpow _ (by norm_num)
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      apply mul_le_mul_of_nonneg_left _ hk
      simpa only [Real.coe_toNNReal _ (le_of_lt ht.1)] using ht.2
    _ = _ := by rw [lintegral_const, Measure.restrict_apply_univ]

#print axioms u3_supplied_force_finite_time_occupation_bound_of_deps

/-- Finite-horizon annealed occupation of an actual L² observable is finite. -/
theorem u3_supplied_force_finite_time_occupation_lt_top_of_deps
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hunforced : UnforcedAt hd Q) (hpath : PathwiseAt Q)
    (lam : ℝ) (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ ω lam) 0 (Y (0, ω)))
    (T : ℝ≥0) (f : Lp ℂ 2 (reducedLaw Q)) :
    (∫⁻ t in Set.Ioc (0 : ℝ) (T : ℝ),
      ∫⁻ ω, ∫⁻ γ : Path d, ‖f (translate (γ t.toNNReal) (reduce ω))‖ₑ
        ∂Y (0, ω) ∂Q.measure) < ∞ := by
  apply lt_of_le_of_lt (u3_supplied_force_finite_time_occupation_bound_of_deps
    (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY T f)
  exact ENNReal.mul_lt_top
    (ENNReal.mul_lt_top
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num) ENNReal.ofReal_lt_top.ne)
      (Lp.eLpNorm_lt_top f)) measure_Ioc_lt_top

#print axioms u3_supplied_force_finite_time_occupation_lt_top_of_deps

/-- A measurable real reduced-law L² observable also has finite absolute
occupation under the same signed path laws. -/
theorem u3_supplied_force_finite_time_real_occupation_lt_top_of_deps
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hunforced : UnforcedAt hd Q) (hpath : PathwiseAt Q)
    (lam : ℝ) (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ ω lam) 0 (Y (0, ω)))
    (T : ℝ≥0) (r : FieldPair d → ℝ) (hm : Measurable r)
    (hr : MemLp r 2 (reducedLaw Q)) :
    (∫⁻ t in Set.Ioc (0 : ℝ) (T : ℝ),
      ∫⁻ ω, ∫⁻ γ : Path d, ‖r (translate (γ t.toNNReal) (reduce ω))‖ₑ
        ∂Y (0, ω) ∂Q.measure) < ∞ := by
  let R : FieldPair d → ℂ := fun w => (r w : ℂ)
  have hR : MemLp R 2 (reducedLaw Q) := hr.ofReal
  let F : Lp ℂ 2 (reducedLaw Q) := hR.toLp R
  have ht := u3_supplied_force_finite_time_occupation_lt_top_of_deps
    (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY T F
  have heq : (∫⁻ t in Set.Ioc (0 : ℝ) (T : ℝ),
      ∫⁻ ω, ∫⁻ γ : Path d, ‖F (translate (γ t.toNNReal) (reduce ω))‖ₑ
        ∂Y (0, ω) ∂Q.measure) =
      ∫⁻ t in Set.Ioc (0 : ℝ) (T : ℝ),
      ∫⁻ ω, ∫⁻ γ : Path d, ‖r (translate (γ t.toNNReal) (reduce ω))‖ₑ
        ∂Y (0, ω) ∂Q.measure := by
    apply lintegral_congr
    intro t
    have he := u3_supplied_force_endpoint_ae_eq_of_deps (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY
      t.toNNReal (fun w => F w) R (Lp.stronglyMeasurable F).measurable
      (Complex.continuous_ofReal.measurable.comp hm) hR.coeFn_toLp
    apply lintegral_congr_ae
    filter_upwards [he] with ω hω
    apply lintegral_congr_ae
    filter_upwards [hω] with γ hγ
    rw [hγ]
    apply enorm_eq_iff_norm_eq.mpr
    simpa only [R, Real.norm_eq_abs] using Complex.norm_real (r (translate (γ t.toNNReal) (reduce ω)))
  rwa [heq] at ht

#print axioms u3_supplied_force_finite_time_real_occupation_lt_top_of_deps

/-- L²-small observations have vanishing annealed absolute occupation on any
finite time interval for the same supplied signed path laws. -/
theorem u3_supplied_force_finite_time_residual_tendsto_of_deps
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hunforced : UnforcedAt hd Q) (hpath : PathwiseAt Q)
    (lam : ℝ) (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ ω lam) 0 (Y (0, ω)))
    (T : ℝ≥0) (f : ℕ → Lp ℂ 2 (reducedLaw Q))
    (hf : Filter.Tendsto (fun n => eLpNorm (fun ρ => f n ρ) 2 (reducedLaw Q))
      Filter.atTop (𝓝 0)) :
    Filter.Tendsto (fun n => ∫⁻ t in Set.Ioc (0 : ℝ) (T : ℝ),
      ∫⁻ ω, ∫⁻ γ : Path d, ‖f n (translate (γ t.toNNReal) (reduce ω))‖ₑ
        ∂Y (0, ω) ∂Q.measure) Filter.atTop (𝓝 0) := by
  let C : ℝ≥0∞ := ENNReal.ofReal (Real.exp
    (lam ^ 2 * (Real.exp (2 * Λ₀) * Λ₀) * (T : ℝ))) ^ (1 / 2 : ℝ)
  let M : ℝ≥0∞ := (volume : Measure ℝ) (Set.Ioc 0 (T : ℝ))
  have hC : C ≠ ∞ :=
    ne_of_lt (ENNReal.rpow_lt_top_of_nonneg (by norm_num) ENNReal.ofReal_lt_top.ne)
  have hM : M ≠ ∞ := measure_Ioc_lt_top.ne
  have hk : 0 ≤ lam ^ 2 * (Real.exp (2 * Λ₀) * Λ₀) := by
    have hΛ : 0 < Λ₀ := lt_of_lt_of_le zero_lt_one Q.ellipticity_parameter
    positivity
  have hb (n : ℕ) :
      (∫⁻ t in Set.Ioc (0 : ℝ) (T : ℝ),
        ∫⁻ ω, ∫⁻ γ : Path d, ‖f n (translate (γ t.toNNReal) (reduce ω))‖ₑ
          ∂Y (0, ω) ∂Q.measure) ≤
        (C * eLpNorm (fun ρ => f n ρ) 2 (reducedLaw Q)) * M := by
    calc
      _ ≤ ∫⁻ _ in Set.Ioc (0 : ℝ) (T : ℝ),
          C * eLpNorm (fun ρ => f n ρ) 2 (reducedLaw Q) := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
        apply (u3_supplied_force_endpoint_annealed_absolute_bound_of_deps
          (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY t.toNNReal (f n)).trans
        apply mul_le_mul' _ le_rfl
        apply ENNReal.rpow_le_rpow _ (by norm_num)
        apply ENNReal.ofReal_le_ofReal
        apply Real.exp_le_exp.mpr
        apply mul_le_mul_of_nonneg_left _ hk
        simpa only [Real.coe_toNNReal _ (le_of_lt ht.1)] using ht.2
      _ = _ := by rw [lintegral_const, Measure.restrict_apply_univ]
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds _
    (fun _ => bot_le) hb
  have h := ENNReal.Tendsto.const_mul hf (Or.inr hC)
  have h' := ENNReal.Tendsto.mul_const (b := M) h (Or.inr hM)
  simpa using h'

/-- The same occupation convergence applies to measurable real representatives
whose reduced-law L² norms tend to zero. -/
theorem u3_supplied_force_finite_time_real_residual_tendsto_of_deps
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hunforced : UnforcedAt hd Q) (hpath : PathwiseAt Q)
    (lam : ℝ) (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ ω lam) 0 (Y (0, ω)))
    (T : ℝ≥0) (r : ℕ → FieldPair d → ℝ)
    (hm : ∀ n, Measurable (r n)) (hr : ∀ n, MemLp (r n) 2 (reducedLaw Q))
    (hlim : Filter.Tendsto (fun n => ‖(hr n).toLp (r n)‖) Filter.atTop (𝓝 0)) :
    Filter.Tendsto (fun n => ∫⁻ t in Set.Ioc (0 : ℝ) (T : ℝ),
      ∫⁻ ω, ∫⁻ γ : Path d, ‖r n (translate (γ t.toNNReal) (reduce ω))‖ₑ
        ∂Y (0, ω) ∂Q.measure) Filter.atTop (𝓝 0) := by
  let R (n : ℕ) : FieldPair d → ℂ := fun w => (r n w : ℂ)
  have hR (n : ℕ) : MemLp (R n) 2 (reducedLaw Q) := (hr n).ofReal
  let F (n : ℕ) : Lp ℂ 2 (reducedLaw Q) := (hR n).toLp (R n)
  have hnorm (n : ℕ) : eLpNorm (fun w => F n w) 2 (reducedLaw Q) =
      ENNReal.ofReal ‖(hr n).toLp (r n)‖ := by
    rw [eLpNorm_congr_ae (hR n).coeFn_toLp]
    have heq : eLpNorm (R n) 2 (reducedLaw Q) = eLpNorm (r n) 2 (reducedLaw Q) := by
      apply eLpNorm_congr_enorm_ae (hR n).aestronglyMeasurable (hr n).aestronglyMeasurable
      filter_upwards [] with w
      apply enorm_eq_iff_norm_eq.mpr
      simpa only [R, Real.norm_eq_abs] using Complex.norm_real (r n w)
    rw [heq, ← eLpNorm_congr_ae (hr n).coeFn_toLp, ← Lp.enorm_def, ← ofReal_norm]
  have hF : Filter.Tendsto (fun n => eLpNorm (fun w => F n w) 2 (reducedLaw Q))
      Filter.atTop (𝓝 0) := by
    have heq : (fun n => eLpNorm (fun w => F n w) 2 (reducedLaw Q)) =
        (fun n => ENNReal.ofReal ‖(hr n).toLp (r n)‖) := funext hnorm
    rw [heq]
    simpa using ENNReal.tendsto_ofReal hlim
  have ht := u3_supplied_force_finite_time_residual_tendsto_of_deps
    (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY T F hF
  apply ht.congr
  intro n
  apply lintegral_congr
  intro t
  have he := u3_supplied_force_endpoint_ae_eq_of_deps (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY
    t.toNNReal (fun w => F n w) (R n) (Lp.stronglyMeasurable (F n)).measurable
    (Complex.continuous_ofReal.measurable.comp (hm n)) (hR n).coeFn_toLp
  apply lintegral_congr_ae
  filter_upwards [he] with ω hω
  apply lintegral_congr_ae
  filter_upwards [hω] with γ hγ
  rw [hγ]
  apply enorm_eq_iff_norm_eq.mpr
  simpa only [R, Real.norm_eq_abs] using Complex.norm_real (r n (translate (γ t.toNNReal) (reduce ω)))

/-- The signed generator graph residual admits representatives with vanishing
absolute occupation under the same supplied path laws on every finite horizon. -/
theorem u3_signed_graph_finite_time_residual_representatives_of_deps
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hunforced : UnforcedAt hd Q) (hpath : PathwiseAt Q)
    (lam s : ℝ) (hs : 0 < s) (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ ω lam) 0 (Y (0, ω)))
    (T : ℝ≥0) (f g : Lp ℂ 2 (reducedLaw Q))
    (hfg : IsComplexGeneratorPair Q ⟨0, by omega⟩ (lam : ℂ) f g)
    {G : Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hG : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) f G)
    (L : ℂ →L[ℝ] ℝ) :
    ∃ (r : ℕ → FieldPair d → ℝ) (hr : ∀ n, MemLp (r n) 2 (reducedLaw Q)),
      (∀ n, Measurable (r n)) ∧
      (∀ n, r n =ᵐ[reducedLaw Q] fun w =>
        s * horizontalMollify (Calculus.unitMassScaledMollifier d (Entropy.scaleSeq n))
          (fun v => L (f v)) w -
        envGenerator hd lam (horizontalMollify
          (Calculus.unitMassScaledMollifier d (Entropy.scaleSeq n)) (fun v => L (f v))) w -
        L (((s : ℂ) • f - g) w)) ∧
      Filter.Tendsto (fun n => ‖(hr n).toLp (r n)‖) Filter.atTop (𝓝 0) ∧
      Filter.Tendsto (fun n => ∫⁻ t in Set.Ioc (0 : ℝ) (T : ℝ),
        ∫⁻ ω, ∫⁻ γ : Path d, ‖r n (translate (γ t.toNNReal) (reduce ω))‖ₑ
          ∂Y (0, ω) ∂Q.measure) Filter.atTop (𝓝 0) := by
  obtain ⟨r, hr, hm, he, hlim⟩ :=
    u3_signed_graph_mollified_residual_representatives hd Q lam s hs f g hfg hG L
  exact ⟨r, hr, hm, he, hlim,
    u3_supplied_force_finite_time_real_residual_tendsto_of_deps
      (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY T r hm hr hlim⟩

/-- Tonelli's theorem identifies the joint finite-horizon occupation with the
nested occupation of the original supplied path law. -/
theorem u3_supplied_force_finite_time_joint_occupation
    {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (Y : QuenchedPathLaws d) (K : Kernel (FieldPair d) (Path d))
    [IsMarkovKernel K] (hK : ∀ᵐ ω ∂Q.measure, Y (0, ω) = K ω)
    (T : ℝ≥0) (r : FieldPair d → ℝ) (hr : Measurable r) :
    (∫⁻ p : ℝ × (FieldPair d × Path d),
      ‖r (translate (p.2.2 p.1.toNNReal) (reduce p.2.1))‖ₑ
        ∂((volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ))).prod (Q.measure ⊗ₘ K))) =
      ∫⁻ t in Set.Ioc (0 : ℝ) (T : ℝ),
        ∫⁻ ω, ∫⁻ γ : Path d, ‖r (translate (γ t.toNNReal) (reduce ω))‖ₑ
          ∂Y (0, ω) ∂Q.measure := by
  let E : ℝ × (FieldPair d × Path d) → FieldPair d := fun p =>
    translate (p.2.2 p.1.toNNReal) (reduce p.2.1)
  have hE : Measurable E := by
    exact (Probability.continuous_translate.comp
      ((continuous_eval.comp ((continuous_snd.comp continuous_snd).prodMk
        (continuous_real_toNNReal.comp continuous_fst))).prodMk
        (Probability.continuous_reduce.comp (continuous_fst.comp continuous_snd)))).measurable
  let F : ℝ × (FieldPair d × Path d) → ℝ≥0∞ := fun p => ‖r (E p)‖ₑ
  have hF : Measurable F := (hr.comp hE).enorm
  rw [lintegral_prod F hF.aemeasurable]
  apply lintegral_congr
  intro t
  have ht : Measurable (fun p : FieldPair d × Path d => F (t, p)) :=
    hF.comp (measurable_const.prodMk measurable_id)
  rw [Measure.lintegral_compProd ht]
  apply lintegral_congr_ae
  filter_upwards [hK] with ω hω
  change (∫⁻ γ : Path d, ‖r (translate (γ t.toNNReal) (reduce ω))‖ₑ ∂K ω) = _
  rw [hω]

/-- Joint absolute occupation is integrable for every measurable real L²
observable under a kernel version of the same supplied path law. -/
theorem u3_supplied_force_finite_time_joint_integrable_of_deps
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hunforced : UnforcedAt hd Q) (hpath : PathwiseAt Q)
    (lam : ℝ) (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ ω lam) 0 (Y (0, ω)))
    (T : ℝ≥0) (r : FieldPair d → ℝ) (hm : Measurable r)
    (hr : MemLp r 2 (reducedLaw Q)) :
    ∃ K : Kernel (FieldPair d) (Path d), IsMarkovKernel K ∧
      (∀ᵐ ω ∂Q.measure, Y (0, ω) = K ω) ∧
      Integrable (fun p : ℝ × (FieldPair d × Path d) =>
        |r (translate (p.2.2 p.1.toNNReal) (reduce p.2.1))|)
        ((volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ))).prod (Q.measure ⊗ₘ K)) := by
  let : IsProbabilityMeasure Q.measure := Q.probability
  have hprob : ∀ᵐ ω ∂Q.measure, IsProbabilityMeasure (originLaw Y ω) :=
    hY.mono fun _ h => h.1
  obtain ⟨K, hK, hmarkov⟩ := Kernel.exists_ae_eq_isMarkovKernel hprob
    (IsProbabilityMeasure.ne_zero Q.measure)
  let : IsMarkovKernel K := hmarkov
  have hK' : ∀ᵐ ω ∂Q.measure, Y (0, ω) = K ω := hK
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
  have hfin := u3_supplied_force_finite_time_real_occupation_lt_top_of_deps
    (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY T r hm hr
  rw [← u3_supplied_force_finite_time_joint_occupation Q Y K hK' T r hm] at hfin
  simpa only [Real.enorm_eq_ofReal_abs, abs_abs] using hfin

#print axioms u3_supplied_force_finite_time_joint_integrable_of_deps

/-- The same supplied signed law has a Markov-kernel version whose joint
finite-horizon occupation vanishes for L²-small real observations. -/
theorem u3_supplied_force_finite_time_joint_residual_tendsto_of_deps
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hunforced : UnforcedAt hd Q) (hpath : PathwiseAt Q)
    (lam : ℝ) (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ ω lam) 0 (Y (0, ω)))
    (T : ℝ≥0) (r : ℕ → FieldPair d → ℝ)
    (hm : ∀ n, Measurable (r n)) (hr : ∀ n, MemLp (r n) 2 (reducedLaw Q))
    (hlim : Filter.Tendsto (fun n => ‖(hr n).toLp (r n)‖) Filter.atTop (𝓝 0)) :
    ∃ K : Kernel (FieldPair d) (Path d), IsMarkovKernel K ∧
      (∀ᵐ ω ∂Q.measure, Y (0, ω) = K ω) ∧
      Filter.Tendsto (fun n => ∫⁻ p : ℝ × (FieldPair d × Path d),
        ‖r n (translate (p.2.2 p.1.toNNReal) (reduce p.2.1))‖ₑ
          ∂((volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ))).prod (Q.measure ⊗ₘ K)))
        Filter.atTop (𝓝 0) := by
  let : IsProbabilityMeasure Q.measure := Q.probability
  have hprob : ∀ᵐ ω ∂Q.measure, IsProbabilityMeasure (originLaw Y ω) :=
    hY.mono fun _ h => h.1
  obtain ⟨K, hK, hmarkov⟩ := Kernel.exists_ae_eq_isMarkovKernel hprob
    (IsProbabilityMeasure.ne_zero Q.measure)
  let : IsMarkovKernel K := hmarkov
  have hK' : ∀ᵐ ω ∂Q.measure, Y (0, ω) = K ω := hK
  refine ⟨K, hmarkov, hK', ?_⟩
  have ht := u3_supplied_force_finite_time_real_residual_tendsto_of_deps
    (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY T r hm hr hlim
  apply ht.congr
  intro n
  exact (u3_supplied_force_finite_time_joint_occupation Q Y K hK' T (r n) (hm n)).symm

/-- Joint L¹ convergence yields a quenched subsequence of finite-horizon
absolute occupation integrals. -/
theorem u3_finite_time_occupation_quenched_subsequence
    {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (K : Kernel (FieldPair d) (Path d)) [IsMarkovKernel K]
    (T : ℝ≥0) (r : ℕ → FieldPair d → ℝ)
    (hi : ∀ n, Integrable (fun p : ℝ × (FieldPair d × Path d) =>
      |r n (translate (p.2.2 p.1.toNNReal) (reduce p.2.1))|)
      ((volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ))).prod (Q.measure ⊗ₘ K)))
    (hlim : Filter.Tendsto (fun n => ∫ p : ℝ × (FieldPair d × Path d),
      |r n (translate (p.2.2 p.1.toNNReal) (reduce p.2.1))|
      ∂((volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ))).prod (Q.measure ⊗ₘ K)))
      Filter.atTop (𝓝 0)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∀ᵐ ω ∂Q.measure,
      Filter.Tendsto (fun n => ∫ t in Set.Ioc (0 : ℝ) (T : ℝ),
        ∫ γ : Path d, |r (ns n) (translate (γ t.toNNReal) (reduce ω))| ∂K ω)
        Filter.atTop (𝓝 0) := by
  let : IsProbabilityMeasure Q.measure := Q.probability
  let μ := (volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) (T : ℝ))
  let F : ℕ → ℝ × (FieldPair d × Path d) → ℝ := fun n p =>
    |r n (translate (p.2.2 p.1.toNNReal) (reduce p.2.1))|
  let G : ℕ → (ℝ × FieldPair d) × Path d → ℝ := fun n p => F n (p.1.1, p.1.2, p.2)
  let H : ℕ → ℝ × FieldPair d → ℝ := fun n p => ∫ γ, G n (p, γ) ∂K p.2
  let R : ℕ → FieldPair d → ℝ := fun n ω => ∫ t, H n (t, ω) ∂μ
  have hpos : ∀ n p, 0 ≤ F n p := fun n p => abs_nonneg _
  have hG : ∀ n, Integrable (G n) ((μ.prod Q.measure) ⊗ₘ Kernel.prodMkLeft ℝ K) := by
    intro n
    apply (integrable_map_equiv MeasurableEquiv.prodAssoc (F n)).mp
    rw [c22_prod_compProd_assoc]
    exact hi n
  have hH : ∀ n, Integrable (H n) (μ.prod Q.measure) := by
    intro n
    have h := (Measure.integrable_compProd_iff (hG n).aestronglyMeasurable).mp (hG n)
    have hn : ∀ p, ‖G n p‖ = G n p := fun p =>
      (Real.norm_eq_abs _).trans (abs_of_nonneg (hpos n _))
    simpa only [H, Kernel.prodMkLeft_apply, hn] using h.2
  have hHpos : ∀ n p, 0 ≤ H n p := fun n p => integral_nonneg (fun γ => hpos n _)
  have hR : ∀ n, Integrable (R n) Q.measure := by
    intro n
    have h := (hH n).integral_norm_prod_right
    have hn : ∀ p, ‖H n p‖ = H n p := fun p =>
      (Real.norm_eq_abs _).trans (abs_of_nonneg (hHpos n p))
    simpa only [R, hn] using h
  have hRpos : ∀ n ω, 0 ≤ R n ω := fun n ω => integral_nonneg fun t => hHpos n _
  have heq : ∀ n, (∫ ω, R n ω ∂Q.measure) = ∫ p, F n p ∂(μ.prod (Q.measure ⊗ₘ K)) := by
    intro n
    exact (c22_integral_prod_compProd_swap μ Q.measure K (F n) (hpos n) (hi n)).symm
  have heLp : Filter.Tendsto (fun n => eLpNorm (R n - 0) 1 Q.measure) Filter.atTop (𝓝 0) := by
    have heq' : ∀ n, eLpNorm (R n - 0) 1 Q.measure =
        ENNReal.ofReal (∫ p, F n p ∂(μ.prod (Q.measure ⊗ₘ K))) := by
      intro n
      simp only [sub_zero]
      rw [eLpNorm_one_eq_lintegral_enorm (hR n).aestronglyMeasurable,
        ← ofReal_integral_norm_eq_lintegral_enorm (hR n)]
      simp_rw [Real.norm_eq_abs, abs_of_nonneg (hRpos n _)]
      rw [heq n]
    simp_rw [heq']
    simpa only [F, μ, Function.comp_def, ENNReal.ofReal_zero] using
      (ENNReal.continuous_ofReal.tendsto 0).comp hlim
  obtain ⟨ns, hns, ha⟩ :=
    (tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (1 : ℝ≥0∞) ≠ 0) heLp).exists_seq_tendsto_ae
  refine ⟨ns, hns, ?_⟩
  filter_upwards [ha] with ω hω
  simpa only [R, H, G, F, Pi.zero_apply] using hω

/-- L²-small observations have a quenched subsequence with vanishing absolute
finite-horizon occupation for the original supplied signed law. -/
theorem u3_supplied_force_finite_time_quenched_subsequence_of_deps
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hunforced : UnforcedAt hd Q) (hpath : PathwiseAt Q)
    (lam : ℝ) (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ ω lam) 0 (Y (0, ω)))
    (T : ℝ≥0) (r : ℕ → FieldPair d → ℝ)
    (hm : ∀ n, Measurable (r n)) (hr : ∀ n, MemLp (r n) 2 (reducedLaw Q))
    (hlim : Filter.Tendsto (fun n => ‖(hr n).toLp (r n)‖) Filter.atTop (𝓝 0)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∀ᵐ ω ∂Q.measure,
      Filter.Tendsto (fun n => ∫ t in Set.Ioc (0 : ℝ) (T : ℝ),
        ∫ γ : Path d, |r (ns n) (translate (γ t.toNNReal) (reduce ω))| ∂Y (0, ω))
        Filter.atTop (𝓝 0) := by
  obtain ⟨K, hmarkov, hK, hJ⟩ :=
    u3_supplied_force_finite_time_joint_residual_tendsto_of_deps
      (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY T r hm hr hlim
  let : IsMarkovKernel K := hmarkov
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
  have hJ' : Filter.Tendsto J Filter.atTop (𝓝 0) := hJ
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1
    (hJ'.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ≥0∞) < 1)))
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
    hJ'.comp (Filter.tendsto_add_atTop_nat N)
  have hreal : Filter.Tendsto (fun n => ∫ p, F n p ∂ν) Filter.atTop (𝓝 0) := by
    have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hshift
    simp only [ENNReal.toReal_zero] at h
    apply h.congr
    intro n
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun p => abs_nonneg _) (hF n).aestronglyMeasurable]
    simp only [R, Real.enorm_eq_ofReal_abs, J, Function.comp_def]
  obtain ⟨ns, hns, ha⟩ := u3_finite_time_occupation_quenched_subsequence Q K T R hi hreal
  refine ⟨fun n => ns n + N, fun i j hij => Nat.add_lt_add_right (hns hij) N, ?_⟩
  filter_upwards [ha, hK] with ω hω hKω
  simpa only [R, hKω] using hω

/-- A signed generator graph pair has mollified residual representatives whose
absolute occupation vanishes along a quenched subsequence of the supplied law. -/
theorem u3_signed_graph_quenched_residual_subsequence_of_deps
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hunforced : UnforcedAt hd Q) (hpath : PathwiseAt Q)
    (lam s : ℝ) (hs : 0 < s) (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ ω lam) 0 (Y (0, ω)))
    (T : ℝ≥0) (f g : Lp ℂ 2 (reducedLaw Q))
    (hfg : IsComplexGeneratorPair Q ⟨0, by omega⟩ (lam : ℂ) f g)
    {G : Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hG : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) f G)
    (L : ℂ →L[ℝ] ℝ) :
    ∃ (r : ℕ → FieldPair d → ℝ) (ns : ℕ → ℕ), StrictMono ns ∧
      (∀ n, Measurable (r n)) ∧
      (∀ n, r n =ᵐ[reducedLaw Q] fun w =>
        s * horizontalMollify (Calculus.unitMassScaledMollifier d (Entropy.scaleSeq n))
          (fun v => L (f v)) w -
        envGenerator hd lam (horizontalMollify
          (Calculus.unitMassScaledMollifier d (Entropy.scaleSeq n)) (fun v => L (f v))) w -
        L (((s : ℂ) • f - g) w)) ∧
      ∀ᵐ ω ∂Q.measure,
        Filter.Tendsto (fun n => ∫ t in Set.Ioc (0 : ℝ) (T : ℝ),
          ∫ γ : Path d, |r (ns n) (translate (γ t.toNNReal) (reduce ω))| ∂Y (0, ω))
          Filter.atTop (𝓝 0) := by
  obtain ⟨r, hr, hm, he, hlim, _⟩ :=
    u3_signed_graph_finite_time_residual_representatives_of_deps
      (hunforced := hunforced) (hpath := hpath) hd Q lam s hs Y hY T f g hfg hG L
  obtain ⟨ns, hns, hocc⟩ :=
    u3_supplied_force_finite_time_quenched_subsequence_of_deps
      (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY T r hm hr hlim
  exact ⟨r, ns, hns, hm, he, hocc⟩

/-- Reduced-law almost-everywhere equality transfers to signed paths even
when the given representatives are not themselves measurable. -/
theorem u3_supplied_force_ae_eq_occupation_of_pathwise
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hpath : PathwiseAt Q)
    (i : Fin d) (lam : ℝ) (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator i ω lam) 0 (Y (0, ω)))
    (f g : FieldPair d → ℝ) (hfg : f =ᵐ[reducedLaw Q] g) :
    ∀ᵐ ω ∂Q.measure, ∀ᵐ γ ∂Y (0, ω),
      ∀ᵐ t ∂volume.restrict (Set.Ioi (0 : ℝ)),
        f (translate (γ t.toNNReal) (reduce ω)) =
          g (translate (γ t.toNNReal) (reduce ω)) := by
  obtain ⟨N, hsub, hNm, hN⟩ := exists_measurable_superset_of_null (ae_iff.mp hfg)
  filter_upwards [u3_supplied_force_environment_null_occupation_of_pathwise
    (hpath := hpath) hd Q i lam Y hY N hNm hN] with ω hω
  filter_upwards [hω] with γ hγ
  filter_upwards [hγ] with t ht
  by_contra hne
  exact ht (hsub hne)


#print axioms u3_supplied_force_ae_eq_occupation_of_pathwise

/-- The literal signed generator along the supplied path has integrable
absolute occupation on every fixed finite horizon. -/
theorem u3_signed_graph_generator_path_occupation_integrable_of_deps
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hunforced : UnforcedAt hd Q) (hpath : PathwiseAt Q)
    (lam s : ℝ) (hs : 0 < s) (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ ω lam) 0 (Y (0, ω)))
    (f g : Lp ℂ 2 (reducedLaw Q))
    (hfg : IsComplexGeneratorPair Q ⟨0, by omega⟩ (lam : ℂ) f g)
    {G : Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hG : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) f G)
    (L : ℂ →L[ℝ] ℝ) (T : ℝ≥0) (n : ℕ) :
    ∀ᵐ ω ∂Q.measure, ∀ᵐ γ ∂Y (0, ω),
      IntegrableOn (fun t : ℝ => |envGenerator hd lam (horizontalMollify
        (Calculus.unitMassScaledMollifier d (Entropy.scaleSeq n)) (fun v => L (f v)))
          (translate (γ t.toNNReal) (reduce ω))|) (Set.Ioc 0 (T : ℝ)) volume := by
  obtain ⟨a, ham, ha, hae⟩ :=
    u3_signed_graph_mollified_generator_representatives hd Q lam s hs f g hfg hG L
  obtain ⟨K, hmarkov, hK, hi⟩ :=
    u3_supplied_force_finite_time_joint_integrable_of_deps
      (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY T (a n) (ham n) (ha n)
  let : IsMarkovKernel K := hmarkov
  have hsections := Measure.ae_ae_of_ae_compProd hi.prod_left_ae
  have heq := u3_supplied_force_ae_eq_occupation_of_pathwise (hpath := hpath) hd Q
    ⟨0, by omega⟩ lam Y hY (a n) _ (hae n)
  filter_upwards [hK, hsections, heq] with ω hKω hsectionω heqω
  rw [← hKω] at hsectionω
  filter_upwards [hsectionω, heqω] with γ hsectionγ heqγ
  have ht := ae_restrict_of_ae_restrict_of_subset
    (fun t (ht : t ∈ Set.Ioc (0 : ℝ) (T : ℝ)) => ht.1) heqγ
  apply hsectionγ.congr
  filter_upwards [ht] with t ht
  exact congrArg abs ht

#print axioms u3_signed_graph_generator_path_occupation_integrable_of_deps

/-- The literal signed generator has integrable absolute occupation as a
random variable under the original supplied quenched path law. -/
theorem u3_signed_graph_generator_quenched_occupation_integrable_of_deps
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hunforced : UnforcedAt hd Q) (hpath : PathwiseAt Q)
    (lam s : ℝ) (hs : 0 < s) (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ ω lam) 0 (Y (0, ω)))
    (f g : Lp ℂ 2 (reducedLaw Q))
    (hfg : IsComplexGeneratorPair Q ⟨0, by omega⟩ (lam : ℂ) f g)
    {G : Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hG : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) f G)
    (L : ℂ →L[ℝ] ℝ) (T : ℝ≥0) (n : ℕ) :
    ∀ᵐ ω ∂Q.measure, Integrable (fun γ : Path d =>
      ∫ t in Set.Ioc 0 (T : ℝ), |envGenerator hd lam (horizontalMollify
        (Calculus.unitMassScaledMollifier d (Entropy.scaleSeq n)) (fun v => L (f v)))
          (translate (γ t.toNNReal) (reduce ω))|) (Y (0, ω)) := by
  obtain ⟨a, ham, ha, hae⟩ :=
    u3_signed_graph_mollified_generator_representatives hd Q lam s hs f g hfg hG L
  obtain ⟨K, hmarkov, hK, hi⟩ :=
    u3_supplied_force_finite_time_joint_integrable_of_deps
      (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY T (a n) (ham n) (ha n)
  let : IsMarkovKernel K := hmarkov
  have hn := hi.integral_norm_prod_right
  have hn' : Integrable (fun p : FieldPair d × Path d =>
      ∫ t in Set.Ioc 0 (T : ℝ), |a n (translate (p.2 t.toNNReal) (reduce p.1))|)
      (Q.measure ⊗ₘ K) := by
    simpa only [Real.norm_eq_abs, abs_abs] using hn
  have hsections := (Measure.integrable_compProd_iff hn'.aestronglyMeasurable).mp hn'
  have heq := u3_supplied_force_ae_eq_occupation_of_pathwise (hpath := hpath) hd Q
    ⟨0, by omega⟩ lam Y hY (a n) _ (hae n)
  filter_upwards [hK, hsections.1, heq] with ω hKω hsectionω heqω
  rw [← hKω] at hsectionω
  apply hsectionω.congr
  filter_upwards [heqω] with γ heqγ
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae_restrict_of_subset (fun _ ht => ht.1) heqγ] with t ht
  exact congrArg abs ht

#print axioms u3_signed_graph_generator_quenched_occupation_integrable_of_deps

/-- The actual signed-generator compensator is integrable under the supplied
quenched path law on every fixed finite horizon. -/
theorem u3_signed_graph_generator_compensator_integrable_of_deps
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hunforced : UnforcedAt hd Q) (hpath : PathwiseAt Q)
    (lam s : ℝ) (hs : 0 < s) (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ ω lam) 0 (Y (0, ω)))
    (f g : Lp ℂ 2 (reducedLaw Q))
    (hfg : IsComplexGeneratorPair Q ⟨0, by omega⟩ (lam : ℂ) f g)
    {G : Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hG : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) f G)
    (L : ℂ →L[ℝ] ℝ) (T : ℝ≥0) (n : ℕ) :
    ∀ᵐ ω ∂Q.measure, Integrable (fun γ : Path d =>
      ∫ t in Set.Ioc 0 (T : ℝ), envGenerator hd lam (horizontalMollify
        (Calculus.unitMassScaledMollifier d (Entropy.scaleSeq n)) (fun v => L (f v)))
          (translate (γ t.toNNReal) (reduce ω))) (Y (0, ω)) := by
  obtain ⟨a, ham, ha, hae⟩ :=
    u3_signed_graph_mollified_generator_representatives hd Q lam s hs f g hfg hG L
  obtain ⟨K, hmarkov, hK, hi⟩ :=
    u3_supplied_force_finite_time_joint_integrable_of_deps
      (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY T (a n) (ham n) (ha n)
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
  have heq := u3_supplied_force_ae_eq_occupation_of_pathwise (hpath := hpath) hd Q
    ⟨0, by omega⟩ lam Y hY (a n) _ (hae n)
  filter_upwards [hK, hsections.1, heq] with ω hKω hsectionω heqω
  rw [← hKω] at hsectionω
  apply hsectionω.congr
  filter_upwards [heqω] with γ heqγ
  apply integral_congr_ae
  exact ae_restrict_of_ae_restrict_of_subset (fun _ ht => ht.1) heqγ

#print axioms u3_signed_graph_generator_compensator_integrable_of_deps

/-- A real reduced-law L² observable is integrable at each fixed time under
the actual supplied signed path law. -/
theorem u3_supplied_force_real_endpoint_integrable_of_deps
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hunforced : UnforcedAt hd Q) (hpath : PathwiseAt Q)
    (lam : ℝ) (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ ω lam) 0 (Y (0, ω)))
    (t : ℝ≥0) (a : FieldPair d → ℝ) (ham : Measurable a)
    (ha : MemLp a 2 (reducedLaw Q)) :
    ∀ᵐ ω ∂Q.measure, Integrable
      (fun γ : Path d => a (translate (γ t) (reduce ω))) (Y (0, ω)) := by
  let A : FieldPair d → ℂ := fun w => (a w : ℂ)
  have hA : MemLp A 2 (reducedLaw Q) := ha.ofReal
  let F : Lp ℂ 2 (reducedLaw Q) := hA.toLp A
  have hi := u3_supplied_force_endpoint_integrable_of_deps (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY t F
  have he := u3_supplied_force_endpoint_ae_eq_of_deps (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY t
    (fun w => F w) A (Lp.stronglyMeasurable F).measurable
    (Complex.continuous_ofReal.measurable.comp ham) hA.coeFn_toLp
  filter_upwards [hi, he] with ω hiω heω
  have hr := Complex.reCLM.integrable_comp hiω
  apply hr.congr
  filter_upwards [heω] with γ hγ
  simpa only [A, Complex.ofReal_re, Complex.reCLM_apply] using congrArg Complex.re hγ

#print axioms u3_supplied_force_real_endpoint_integrable_of_deps

/-- Each fixed-time value of the literal mollified compensated orbit is
integrable under the same supplied signed path law. -/
theorem u3_signed_graph_compensated_orbit_integrable_of_deps
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hunforced : UnforcedAt hd Q) (hpath : PathwiseAt Q)
    (lam s : ℝ) (hs : 0 < s) (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ ω lam) 0 (Y (0, ω)))
    (f g : Lp ℂ 2 (reducedLaw Q))
    (hfg : IsComplexGeneratorPair Q ⟨0, by omega⟩ (lam : ℂ) f g)
    {G : Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hG : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) f G)
    (L : ℂ →L[ℝ] ℝ) (t : ℝ≥0) (n : ℕ) :
    ∀ᵐ ω ∂Q.measure, Integrable (fun γ : Path d =>
      horizontalMollify (Calculus.unitMassScaledMollifier d (Entropy.scaleSeq n))
        (fun v => L (f v)) (translate (γ t) (reduce ω)) -
      horizontalMollify (Calculus.unitMassScaledMollifier d (Entropy.scaleSeq n))
        (fun v => L (f v)) (translate (γ 0) (reduce ω)) -
      ∫ u in Set.Ioc 0 (t : ℝ), envGenerator hd lam (horizontalMollify
        (Calculus.unitMassScaledMollifier d (Entropy.scaleSeq n)) (fun v => L (f v)))
          (translate (γ u.toNNReal) (reduce ω))) (Y (0, ω)) := by
  let V : FieldPair d → ℝ := fun v => L (f v)
  let M := horizontalMollify (Calculus.unitMassScaledMollifier d (Entropy.scaleSeq n)) V
  have hVm : Measurable V := L.continuous.measurable.comp (Lp.stronglyMeasurable f).measurable
  have hV : MemLp V 2 (reducedLaw Q) := L.comp_memLp' (Lp.memLp f)
  have hMm : Measurable M := measurable_horizontalMollify _
    (Entropy.contDiff_unitMassScaledMollifier _).continuous.measurable hVm
  have hM : MemLp M 2 (reducedLaw Q) :=
    Entropy.memLp_horizontalMollify_unitMass (reducedLaw_stationary Q)
      (Entropy.scaleSeq_pos n) ENNReal.ofNat_ne_top hVm hV
  filter_upwards [u3_supplied_force_real_endpoint_integrable_of_deps
      (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY t M hMm hM,
    u3_supplied_force_real_endpoint_integrable_of_deps
      (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY 0 M hMm hM,
    u3_signed_graph_generator_compensator_integrable_of_deps
      (hunforced := hunforced) (hpath := hpath) hd Q lam s hs Y hY f g hfg hG L t n] with ω ht h0 hc
  exact (ht.sub h0).sub hc

#print axioms u3_signed_graph_compensated_orbit_integrable_of_deps

/-- Stationary integrable observations have almost surely integrable orbits
against an exponentially decaying coordinate weight. -/
theorem u3_stationary_exponential_weighted_orbit_integrable
    {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (a : FieldPair d → ℝ) (ham : Measurable a)
    (ha : MemLp a 2 (reducedLaw Q)) :
    ∀ᵐ w ∂reducedLaw Q, Integrable (fun x : Vec d =>
      (∏ j : Fin d, Real.exp (-|x j|)) * |a (translate x w)|) volume := by
  letI : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  have h1 : Integrable (fun x : ℝ => Real.exp (-|x|)) volume := by
    have hn : IntegrableOn (fun x : ℝ => Real.exp (-|x|)) (Set.Iic 0) := by
      apply (integrableOn_exp_Iic 0).congr_fun _ measurableSet_Iic
      intro x hx
      have hx' : x ≤ 0 := hx
      simp only [abs_of_nonpos hx', neg_neg]
    have hp : IntegrableOn (fun x : ℝ => Real.exp (-|x|)) (Set.Ioi 0) := by
      apply (integrableOn_exp_neg_Ioi 0).congr_fun _ measurableSet_Ioi
      intro x hx
      have hx' : 0 < x := hx
      simp only [abs_of_pos hx']
    have h := hn.union hp
    simpa only [Set.Iic_union_Ioi, integrableOn_univ] using h
  have hw : Integrable (fun x : Vec d => ∏ j : Fin d, Real.exp (-|x j|)) volume := by
    have h : Integrable (fun x : Vec d => ∏ j : Fin d, Real.exp (-|x j|))
        (Measure.pi fun _ : Fin d => (volume : Measure ℝ)) :=
      Integrable.fintype_prod (fun _ : Fin d => h1)
    exact h
  have hwm : Measurable (fun x : Vec d => ∏ j : Fin d, Real.exp (-|x j|)) := by
    fun_prop
  have hi := EinsteinRelation.Correctors.integrable_weighted_orbit
    (reducedLaw Q) (reducedLaw_stationary Q) hwm hw ham.abs (ha.integrable (by norm_num)).abs
  exact hi.prod_left_ae

#print axioms u3_stationary_exponential_weighted_orbit_integrable

/-- Reduced-law almost-everywhere equality also holds in time-first order
on the finite-horizon occupation of the supplied signed law. -/
theorem u3_supplied_force_ae_eq_time_first_occupation_of_pathwise
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hpath : PathwiseAt Q)
    (i : Fin d) (lam : ℝ) (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator i ω lam) 0 (Y (0, ω)))
    (T : ℝ≥0) (f g : FieldPair d → ℝ) (hfg : f =ᵐ[reducedLaw Q] g) :
    ∀ᵐ ω ∂Q.measure, ∀ᵐ t ∂volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ)),
      ∀ᵐ γ ∂Y (0, ω),
        f (translate (γ t.toNNReal) (reduce ω)) =
          g (translate (γ t.toNNReal) (reduce ω)) := by
  obtain ⟨N, hsub, hNm, hN⟩ := exists_measurable_superset_of_null (ae_iff.mp hfg)
  filter_upwards [u3_supplied_force_environment_null_occupation_of_pathwise
    (hpath := hpath) hd Q i lam Y hY N hNm hN, hY] with ω hω hprob
  let : IsProbabilityMeasure (Y (0, ω)) := hprob.1
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

#print axioms u3_supplied_force_ae_eq_time_first_occupation_of_pathwise

/-- Equal reduced-law representatives have equal absolute finite-horizon
occupation integrals under the supplied signed law. -/
theorem u3_supplied_force_absolute_occupation_eq_of_pathwise
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hpath : PathwiseAt Q)
    (i : Fin d) (lam : ℝ) (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator i ω lam) 0 (Y (0, ω)))
    (T : ℝ≥0) (f g : FieldPair d → ℝ) (hfg : f =ᵐ[reducedLaw Q] g) :
    ∀ᵐ ω ∂Q.measure,
      (∫ t in Set.Ioc (0 : ℝ) (T : ℝ), ∫ γ : Path d,
        |f (translate (γ t.toNNReal) (reduce ω))| ∂Y (0, ω)) =
      ∫ t in Set.Ioc (0 : ℝ) (T : ℝ), ∫ γ : Path d,
        |g (translate (γ t.toNNReal) (reduce ω))| ∂Y (0, ω) := by
  filter_upwards [u3_supplied_force_ae_eq_time_first_occupation_of_pathwise
    (hpath := hpath) hd Q i lam Y hY T f g hfg] with ω hω
  apply integral_congr_ae
  filter_upwards [hω] with t ht
  apply integral_congr_ae
  filter_upwards [ht] with γ hγ
  rw [hγ]

#print axioms u3_supplied_force_absolute_occupation_eq_of_pathwise

/-- The literal signed generator residual has vanishing absolute occupation
along a subsequence for almost every supplied environment law. -/
theorem u3_signed_graph_literal_residual_occupation_subsequence_of_deps
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hunforced : UnforcedAt hd Q) (hpath : PathwiseAt Q)
    (lam s : ℝ) (hs : 0 < s) (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ ω lam) 0 (Y (0, ω)))
    (T : ℝ≥0) (f g : Lp ℂ 2 (reducedLaw Q))
    (hfg : IsComplexGeneratorPair Q ⟨0, by omega⟩ (lam : ℂ) f g)
    {G : Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hG : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) f G)
    (L : ℂ →L[ℝ] ℝ) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∀ᵐ ω ∂Q.measure,
      Filter.Tendsto (fun n => ∫ t in Set.Ioc (0 : ℝ) (T : ℝ),
        ∫ γ : Path d, |s * horizontalMollify
            (Calculus.unitMassScaledMollifier d (Entropy.scaleSeq (ns n)))
            (fun v => L (f v)) (translate (γ t.toNNReal) (reduce ω)) -
          envGenerator hd lam (horizontalMollify
            (Calculus.unitMassScaledMollifier d (Entropy.scaleSeq (ns n))) (fun v => L (f v)))
            (translate (γ t.toNNReal) (reduce ω)) -
          L (((s : ℂ) • f - g) (translate (γ t.toNNReal) (reduce ω)))| ∂Y (0, ω))
        Filter.atTop (𝓝 0) := by
  obtain ⟨r, ns, hns, _, he, hocc⟩ :=
    u3_signed_graph_quenched_residual_subsequence_of_deps
      (hunforced := hunforced) (hpath := hpath) hd Q lam s hs Y hY T f g hfg hG L
  have ha := fun n => u3_supplied_force_absolute_occupation_eq_of_pathwise
    (hpath := hpath) hd Q ⟨0, by omega⟩ lam Y hY T (r (ns n)) _ (he (ns n))
  refine ⟨ns, hns, ?_⟩
  filter_upwards [ae_all_iff.mpr ha, hocc] with ω hω hωocc
  apply hωocc.congr
  intro n
  exact hω n

#print axioms u3_signed_graph_literal_residual_occupation_subsequence_of_deps

/-- A local martingale is a martingale when each finite horizon admits an
integrable pathwise dominator. -/
theorem u3_local_martingale_of_integrable_horizon_bound
    {d : ℕ} {M : ℝ≥0 → External.Bass.Path d → ℝ}
    {P : Measure (External.Bass.Path d)} [IsFiniteMeasure P]
    (hM : External.Bass.IsLocalMartingale M P)
    (hbound : ∀ T : ℝ≥0, ∃ H : External.Bass.Path d → ℝ,
      Integrable H P ∧ ∀ᵐ γ ∂P, ∀ t ≤ T, ‖M t γ‖ ≤ H γ) :
    Martingale M (External.Bass.filtration d) P := by
  obtain ⟨hadapted, τ, hτ, hstop⟩ := hM
  have hint (t : ℝ≥0) : Integrable (M t) P := by
    obtain ⟨H, hH, hb⟩ := hbound t
    apply hH.mono' ((hadapted t).mono ((External.Bass.filtration d).le t)).aestronglyMeasurable
    filter_upwards [hb] with γ hγ
    exact hγ t le_rfl
  have hlim (t : ℝ≥0) : ∀ᵐ γ ∂P,
      Filter.Tendsto (fun n => stoppedProcess M (τ n) t γ)
        Filter.atTop (𝓝 (M t γ)) := by
    filter_upwards [hτ.tendsto_top] with γ hγ
    apply tendsto_const_nhds.congr'
    filter_upwards [hγ.eventually (eventually_gt_nhds
      (show (t : WithTop ℝ≥0) < ⊤ from WithTop.coe_lt_top t))] with n hn
    exact (stoppedProcess_eq_of_le hn.le).symm
  have hconv (t : ℝ≥0) (A : Set (External.Bass.Path d)) :
      Filter.Tendsto (fun n => ∫ γ in A, stoppedProcess M (τ n) t γ ∂P)
        Filter.atTop (𝓝 (∫ γ in A, M t γ ∂P)) := by
    obtain ⟨H, hH, hb⟩ := hbound t
    refine tendsto_integral_of_dominated_convergence H
      (fun n => ((hstop n).1 t).aestronglyMeasurable.restrict)
      hH.integrableOn (fun n => ?_) (ae_restrict_of_ae (hlim t))
    filter_upwards [ae_restrict_of_ae hb] with γ hγ
    exact hγ _ (WithTop.untopA_le (min_le_left (t : WithTop ℝ≥0) (τ n γ)))
  refine ⟨hadapted, fun s t hst => ?_⟩
  symm
  refine ae_eq_condExp_of_forall_setIntegral_eq ((External.Bass.filtration d).le s) (hint t)
    (fun _ _ _ => (hint s).integrableOn) (fun A hA _ => ?_)
    (hadapted s).aestronglyMeasurable
  have hconv_s := hconv s A
  have hconv_t := hconv t A
  have heq (n : ℕ) : (∫ γ in A, stoppedProcess M (τ n) s γ ∂P) =
      ∫ γ in A, stoppedProcess M (τ n) t γ ∂P :=
    ((hstop n).2).setIntegral_eq hst hA
  simp_rw [heq] at hconv_s
  exact tendsto_nhds_unique hconv_s hconv_t

#print axioms u3_local_martingale_of_integrable_horizon_bound

/-- The literal mollified signed graph orbit satisfies the all-C² local
martingale problem for the same supplied path law. -/
theorem u3_signed_graph_mollified_orbit_local_martingale_of_pathwise
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hpath : PathwiseAt Q)
    (lam s : ℝ) (hs : 0 < s) (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ ω lam) 0 (Y (0, ω)))
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
    u3_supplied_reduced_law_solves_textbook_of_pathwise (hpath := hpath) hd Q i lam Y hY]
    with ω hω htestsω hP
  obtain ⟨ψ, hψ, hlocal⟩ := htestsω
  have hφ : ContDiff ℝ 2 (orbit (horizontalMollify
      (Calculus.unitMassScaledMollifier d δ) (fun v => L (f v))) (reduce ω)) := by
    rw [contDiff_iff_contDiffAt]
    intro x
    obtain ⟨n, hn⟩ := (hlocal x).exists
    exact ((contDiff_two_of_top (hψ n).1).contDiffAt).congr_of_eventuallyEq hn.1.symm
  obtain ⟨hA, _, ⟨Ma, hAb⟩, _, hbm, ⟨Mb, hbb⟩⟩ := reduced_svHypotheses hΛ hω i lam
  have hsource := External.Bass.solves_of_frozen hP hA.measurable hbm hAb hbb
  exact hsource.2.2 _ hφ

#print axioms u3_signed_graph_mollified_orbit_local_martingale_of_pathwise

#print axioms u3_signed_graph_quenched_residual_subsequence_of_deps

#print axioms u3_supplied_force_finite_time_quenched_subsequence_of_deps

#print axioms u3_finite_time_occupation_quenched_subsequence

#print axioms u3_supplied_force_finite_time_joint_residual_tendsto_of_deps

#print axioms u3_supplied_force_finite_time_joint_occupation

#print axioms u3_signed_graph_finite_time_residual_representatives_of_deps

#print axioms u3_supplied_force_finite_time_real_residual_tendsto_of_deps

#print axioms u3_supplied_force_finite_time_residual_tendsto_of_deps

#print axioms u3_signed_graph_mollified_residual_representatives

#print axioms u3_mollified_graph_drift_representatives

#print axioms u3_signed_graph_mollified_residual_tendsto

#print axioms u3_mollified_actual_graph_drift_tendsto

#print axioms u3_mollified_graph_drift_tendsto

#print axioms u3_mollified_projected_drift_tendsto

#print axioms u3_signed_graph_unforced_residual_representatives

#print axioms u3_supplied_force_endpoint_residual_tendsto_of_deps

#print axioms u3_supplied_signed_environment_test_integral_equation_of_pathwise

#print axioms u3_supplied_signed_environment_test_dynkin_of_pathwise

#print axioms u3_signed_envGenerator_eq_svGenerator
#print axioms u3_reduced_signed_bounded_C2_dynkin
#print axioms u3_supplied_signed_horizontal_test_dynkin_of_pathwise

#print axioms u3_supplied_force_endpoint_difference_enorm_bound_of_deps

#print axioms u3_supplied_force_density_centered_eLpNorm_two_bound_of_pathwise

#print axioms u3_supplied_force_density_centered_second_moment_of_pathwise

#print axioms u3_real_force_bounded_tests_zero_force
#print axioms u3_real_force_bounded_tests_zero_time


/-- The coordinate maximum up to a horizon depends only on the stopped prefix. -/
theorem u3_coordinate_max_measurable_past {d : ℕ} (j : Fin d) (T : ℝ≥0) :
    Measurable[pathFiltration d T] (fun γ : Path d =>
      sSup ((fun t : ℝ≥0 => |(γ t) j - (0 : Vec d) j|) '' Set.Icc 0 T)) := by
  let M : Path d → ℝ := fun γ =>
    sSup ((fun t : ℝ≥0 => |(γ t) j - (0 : Vec d) j|) '' Set.Icc 0 T)
  have heq : ∀ γ, M (gmpPrefixPath T γ) = M γ := by
    intro γ
    apply congrArg sSup
    apply Set.image_congr
    intro t ht
    simp [gmpPrefixPath, min_eq_left ht.2]
  rw [u3_pathFiltration_eq_prefix]
  have hm := (c16_continuous_coordinate_max j (0 : Vec d) T).measurable
  have hp : Measurable[MeasurableSpace.comap
      (gmpPrefixPath (d := d) T) inferInstance]
      (fun γ => M (gmpPrefixPath T γ)) :=
    hm.comp (Measurable.of_comap_le le_rfl)
  convert hp using 1
  funext γ
  exact (heq γ).symm

#print axioms u3_coordinate_max_measurable_past


/-- Exponential coordinate maxima are integrable under the supplied signed law. -/
theorem u3_supplied_force_exp_coordinate_max_integrable_of_pathwise
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hpath : PathwiseAt Q)
    (i j : Fin d) (lam : ℝ) (Y₀ Y : QuenchedPathLaws d)
    (hY₀ : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator i ω 0) 0 (Y₀ (0, ω)))
    (hY : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator i ω lam) 0 (Y (0, ω)))
    (a : ℝ) (T : ℝ≥0) :
    ∀ᵐ ω ∂Q.measure, Integrable (fun γ : Path d => Real.exp (a *
      sSup ((fun t : ℝ≥0 => |(γ t) j - (0 : Vec d) j|) '' Set.Icc 0 T))) (Y (0, ω)) := by
  have hΛ : 0 < Λ₀ := lt_of_lt_of_le zero_lt_one Q.ellipticity_parameter
  filter_upwards [Q.regular, u3_supplied_reduced_law_solves_textbook_of_pathwise
      (hpath := hpath) hd Q i 0 Y₀ hY₀,
    u3_supplied_reduced_force_density_memLp_two_of_pathwise (hpath := hpath) hd Q i lam Y₀ hY₀ T,
    u3_supplied_reduced_force_finite_horizon_of_pathwise (hpath := hpath) hd Q i lam Y₀ Y hY₀ hY T]
    with ω hω h₀ hZ htilt
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

#print axioms u3_supplied_force_exp_coordinate_max_integrable_of_pathwise


/-- The same supplied signed law has exponential coordinate-maximum moments,
without requiring an additional unforced-law hypothesis. -/
theorem u3_supplied_force_exp_coordinate_max_integrable_of_deps
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hpath : PathwiseAt Q)
    (i j : Fin d) (lam : ℝ) (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator i ω lam) 0 (Y (0, ω)))
    (a : ℝ) (T : ℝ≥0) :
    ∀ᵐ ω ∂Q.measure, Integrable (fun γ : Path d => Real.exp (a *
      sSup ((fun t : ℝ≥0 => |(γ t) j - (0 : Vec d) j|) '' Set.Icc 0 T))) (Y (0, ω)) := by
  have hΛ : 0 < Λ₀ := lt_of_lt_of_le zero_lt_one Q.ellipticity_parameter
  obtain ⟨Y₀, _, hactual⟩ := foundation_reduced_actual_kernel hd hΛ i 0
  have hY₀ : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator i ω 0) 0 (Y₀ (0, ω)) := by
    filter_upwards [Q.regular] with ω hω
    exact hactual ω hω
  exact u3_supplied_force_exp_coordinate_max_integrable_of_pathwise
    (hpath := hpath) hd Q i j lam Y₀ Y hY₀ hY a T

#print axioms u3_supplied_force_exp_coordinate_max_integrable_of_deps


/-- The exponential of the sum of all coordinate maxima is integrable
under the same supplied signed path law. -/
theorem u3_supplied_force_exp_sum_coordinate_max_integrable_of_deps
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hpath : PathwiseAt Q)
    (i : Fin d) (lam : ℝ) (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator i ω lam) 0 (Y (0, ω)))
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
  have heach := fun j : Fin d => u3_supplied_force_exp_coordinate_max_integrable_of_deps
    (hpath := hpath) hd Q i j lam Y hY ((d : ℝ) * a) T
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

#print axioms u3_supplied_force_exp_sum_coordinate_max_integrable_of_deps


/-- Coordinate maxima dominate the exponential growth at every time in the horizon. -/
theorem u3_exp_coordinate_sum_le_horizon_max {d : ℕ} (a : ℝ) (ha : 0 ≤ a)
    (T s : ℝ≥0) (hs : s ≤ T) (γ : Path d) :
    Real.exp (∑ j : Fin d, a * |(γ s) j|) ≤
      Real.exp (∑ j : Fin d, a *
        sSup ((fun t : ℝ≥0 => |(γ t) j - (0 : Vec d) j|) '' Set.Icc 0 T)) := by
  apply Real.exp_le_exp.mpr
  apply Finset.sum_le_sum
  intro j hj
  apply mul_le_mul_of_nonneg_left _ ha
  have hc : Continuous (fun t : ℝ≥0 => |(γ t) j - (0 : Vec d) j|) :=
    (((continuous_apply j).comp γ.continuous).sub continuous_const).abs
  have h := le_csSup (isCompact_Icc.bddAbove_image hc.continuousOn)
    ⟨s, ⟨zero_le, hs⟩, rfl⟩
  simpa using h

#print axioms u3_exp_coordinate_sum_le_horizon_max


/-- Translating the coordinate exponential weight costs at most the
exponential of the coordinate absolute-value sum of the shift. -/
theorem u3_exponential_weight_translate_le {d : ℕ} (z x : Vec d) :
    (∏ j : Fin d, Real.exp (-|z j|)) ≤
      Real.exp (∑ j : Fin d, |x j|) * (∏ j : Fin d, Real.exp (-|(z + x) j|)) := by
  rw [← Real.exp_sum, ← Real.exp_sum, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  simp only [Finset.sum_neg_distrib]
  have h : (∑ j : Fin d, |(z + x) j|) ≤
      (∑ j : Fin d, |z j|) + ∑ j : Fin d, |x j| := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun j _ => abs_add_le (z j) (x j)
  linarith

#print axioms u3_exponential_weight_translate_le


/-- A weighted spatial orbit controls every translate of a mollification. -/
theorem u3_horizontalMollify_weighted_orbit_bound {d : ℕ}
    (ζ : Vec d → ℝ) (hζm : Measurable ζ) (a : FieldPair d → ℝ) (ham : Measurable a)
    (w : FieldPair d) (C : ℝ) (hC : 0 ≤ C)
    (hζ : ∀ z, |ζ z| ≤ C * ∏ j : Fin d, Real.exp (-|z j|))
    (hi : Integrable (fun z : Vec d =>
      (∏ j : Fin d, Real.exp (-|z j|)) * |a (translate z w)|) volume)
    (x : Vec d) :
    |horizontalMollify ζ a (translate x w)| ≤
      C * Real.exp (∑ j : Fin d, |x j|) *
        ∫ z : Vec d, (∏ j : Fin d, Real.exp (-|z j|)) * |a (translate z w)| := by
  let H : Vec d → ℝ := fun z =>
    (∏ j : Fin d, Real.exp (-|z j|)) * |a (translate z w)|
  let K : ℝ := C * Real.exp (∑ j : Fin d, |x j|)
  have hH : Integrable (fun z : Vec d => H (z + x)) volume := by
    exact ((measurePreserving_add_right (volume : Measure (Vec d)) x).integrable_comp_emb
      (Homeomorph.addRight x).measurableEmbedding).mpr hi
  have hfm : Measurable (fun z : Vec d => ζ z * a (translate z (translate x w))) :=
    hζm.mul (ham.comp (Probability.continuous_translate.measurable.comp
      (measurable_id.prodMk measurable_const)))
  have hb (z : Vec d) : |ζ z * a (translate z (translate x w))| ≤ K * H (z + x) := by
    rw [abs_mul, translate_add]
    have h₁ := mul_le_mul_of_nonneg_right (hζ z) (abs_nonneg (a (translate (z + x) w)))
    have h₂ := mul_le_mul_of_nonneg_left (u3_exponential_weight_translate_le z x) hC
    have h₃ := mul_le_mul_of_nonneg_right h₂ (abs_nonneg (a (translate (z + x) w)))
    simpa only [K, H, Pi.add_apply, mul_assoc] using h₁.trans h₃
  have hf : Integrable (fun z : Vec d => ζ z * a (translate z (translate x w))) volume := by
    refine (hH.const_mul K).mono' hfm.aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun z => by simpa only [Real.norm_eq_abs] using hb z
  calc
    |horizontalMollify ζ a (translate x w)| ≤
        ∫ z : Vec d, |ζ z * a (translate z (translate x w))| :=
      abs_integral_le_integral_abs
    _ ≤ ∫ z : Vec d, K * H (z + x) :=
      integral_mono hf.abs (hH.const_mul K) hb
    _ = K * ∫ z : Vec d, H z := by
      rw [integral_const_mul, integral_add_right_eq_self]
    _ = _ := rfl

#print axioms u3_horizontalMollify_weighted_orbit_bound


/-- Every continuous compactly supported kernel is dominated by the
coordinate exponential weight. -/
theorem u3_compact_kernel_exponential_weight_bound {d : ℕ} (ζ : Vec d → ℝ)
    (hζ : Continuous ζ) (hc : HasCompactSupport ζ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z, |ζ z| ≤ C * ∏ j : Fin d, Real.exp (-|z j|) := by
  let b : Vec d → ℝ := fun z => ζ z * Real.exp (∑ j : Fin d, |z j|)
  have hb : Continuous b := hζ.mul (Real.continuous_exp.comp
    (continuous_finset_sum _ fun j _ => (continuous_apply j).abs))
  have hbc : HasCompactSupport b := hc.mul_right
  obtain ⟨B, hB⟩ := (hbc.isCompact_range hb).isBounded.exists_norm_le
  refine ⟨max B 0, le_max_right _ _, fun z => ?_⟩
  have hbound : |ζ z| * Real.exp (∑ j : Fin d, |z j|) ≤ max B 0 := by
    have h := hB (b z) ⟨z, rfl⟩
    dsimp [b] at h
    rw [abs_mul, abs_of_pos (Real.exp_pos _)] at h
    exact h.trans (le_max_left _ _)
  rw [← Real.exp_sum, Finset.sum_neg_distrib]
  calc
    |ζ z| = (|ζ z| * Real.exp (∑ j : Fin d, |z j|)) *
        Real.exp (-(∑ j : Fin d, |z j|)) := by
      rw [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
    _ ≤ max B 0 * Real.exp (-(∑ j : Fin d, |z j|)) :=
      mul_le_mul_of_nonneg_right hbound (Real.exp_pos _).le

#print axioms u3_compact_kernel_exponential_weight_bound


/-- Compact horizontal mollifications of reduced-law L² observations admit
an integrable bound over every finite horizon of the supplied signed law. -/
theorem u3_supplied_force_mollified_orbit_integrable_horizon_bound_of_deps
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hpath : PathwiseAt Q)
    (i : Fin d) (lam : ℝ) (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator i ω lam) 0 (Y (0, ω)))
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
  filter_upwards [hiw, u3_supplied_force_exp_sum_coordinate_max_integrable_of_deps
    (hpath := hpath) hd Q i lam Y hY 1 T] with ω hi hs
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

#print axioms u3_supplied_force_mollified_orbit_integrable_horizon_bound_of_deps

/-- Integrable orbit and absolute-generator occupation bounds upgrade a
source compensated local martingale to a true martingale. -/
theorem u3_compensated_local_martingale_of_occupation_bound
    {d : ℕ} {a : Vec d → Mat d} {b : Vec d → Vec d} {φ : Vec d → ℝ}
    {P : Measure (External.Bass.Path d)} [IsFiniteMeasure P]
    (hlocal : External.Bass.IsLocalMartingale (External.Bass.compensatedTest a b φ) P)
    (horbit : ∀ T : ℝ≥0, ∃ H : External.Bass.Path d → ℝ, Integrable H P ∧
      ∀ᵐ γ ∂P, ∀ t ≤ T, |φ (γ t)| ≤ H γ)
    (hocc : ∀ T : ℝ≥0, Integrable (fun γ : External.Bass.Path d =>
      ∫ u in Set.Ioc (0 : ℝ) (T : ℝ), |External.Bass.generator a b φ (γ u.toNNReal)|) P)
    (hpath : ∀ T : ℝ≥0, ∀ᵐ γ ∂P, IntegrableOn
      (fun u : ℝ => |External.Bass.generator a b φ (γ u.toNNReal)|)
      (Set.Ioc 0 (T : ℝ)) volume) :
    Martingale (External.Bass.compensatedTest a b φ) (External.Bass.filtration d) P := by
  apply u3_local_martingale_of_integrable_horizon_bound hlocal
  intro T
  obtain ⟨H, hH, hb⟩ := horbit T
  refine ⟨fun γ => H γ + H γ + ∫ u in Set.Ioc (0 : ℝ) (T : ℝ),
    |External.Bass.generator a b φ (γ u.toNNReal)|, (hH.add hH).add (hocc T), ?_⟩
  filter_upwards [hb, hpath T] with γ hbγ hi
  intro t ht
  have hint : ‖∫ u in (0 : ℝ)..(t : ℝ), External.Bass.generator a b φ (γ u.toNNReal)‖ ≤
      ∫ u in Set.Ioc (0 : ℝ) (T : ℝ), |External.Bass.generator a b φ (γ u.toNNReal)| := by
    have heq : (∫ u in (0 : ℝ)..(t : ℝ), External.Bass.generator a b φ (γ u.toNNReal)) =
        ∫ u in Set.Ioc (0 : ℝ) (t : ℝ), External.Bass.generator a b φ (γ u.toNNReal) :=
      intervalIntegral.integral_of_le t.property
    rw [heq]
    calc
      _ ≤ ∫ u in Set.Ioc (0 : ℝ) (t : ℝ), |External.Bass.generator a b φ (γ u.toNNReal)| := by
        simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
          (fun u : ℝ => External.Bass.generator a b φ (γ u.toNNReal))
      _ ≤ _ := setIntegral_mono_set hi (ae_of_all _ fun _ => abs_nonneg _)
        (ae_of_all _ fun _ hu => ⟨hu.1, le_trans hu.2 (by exact_mod_cast ht)⟩)
  change |φ (γ t) - φ (γ 0) - ∫ u in (0 : ℝ)..(t : ℝ),
    External.Bass.generator a b φ (γ u.toNNReal)| ≤ _
  have h1 := hbγ t ht
  have h0 := hbγ 0 bot_le
  rw [Real.norm_eq_abs] at hint
  calc
    _ ≤ |φ (γ t)| + |φ (γ 0)| + |∫ u in (0 : ℝ)..(t : ℝ),
        External.Bass.generator a b φ (γ u.toNNReal)| := by
      exact (abs_sub _ _).trans (add_le_add (abs_sub _ _) le_rfl)
    _ ≤ _ := add_le_add (add_le_add h1 h0) hint

#print axioms u3_compensated_local_martingale_of_occupation_bound

/-- Integer horizon bounds suffice for the compensated martingale upgrade. -/
theorem u3_compensated_local_martingale_of_natural_occupation_bound
    {d : ℕ} {a : Vec d → Mat d} {b : Vec d → Vec d} {φ : Vec d → ℝ}
    {P : Measure (External.Bass.Path d)} [IsFiniteMeasure P]
    (hlocal : External.Bass.IsLocalMartingale (External.Bass.compensatedTest a b φ) P)
    (horbit : ∀ N : ℕ, ∃ H : External.Bass.Path d → ℝ, Integrable H P ∧
      ∀ᵐ γ ∂P, ∀ t ≤ (N : ℝ≥0), |φ (γ t)| ≤ H γ)
    (hocc : ∀ N : ℕ, Integrable (fun γ : External.Bass.Path d =>
      ∫ u in Set.Ioc (0 : ℝ) (N : ℝ), |External.Bass.generator a b φ (γ u.toNNReal)|) P)
    (hpath : ∀ N : ℕ, ∀ᵐ γ ∂P, IntegrableOn
      (fun u : ℝ => |External.Bass.generator a b φ (γ u.toNNReal)|)
      (Set.Ioc 0 (N : ℝ)) volume) :
    Martingale (External.Bass.compensatedTest a b φ) (External.Bass.filtration d) P := by
  apply u3_local_martingale_of_integrable_horizon_bound hlocal
  intro T
  obtain ⟨N, hN⟩ := exists_nat_ge T
  obtain ⟨H, hH, hb⟩ := horbit N
  refine ⟨fun γ => H γ + H γ + ∫ u in Set.Ioc (0 : ℝ) (N : ℝ),
    |External.Bass.generator a b φ (γ u.toNNReal)|, (hH.add hH).add (hocc N), ?_⟩
  filter_upwards [hb, hpath N] with γ hbγ hi
  intro t ht
  have htN : t ≤ (N : ℝ≥0) := ht.trans hN
  have hint : ‖∫ u in (0 : ℝ)..(t : ℝ), External.Bass.generator a b φ (γ u.toNNReal)‖ ≤
      ∫ u in Set.Ioc (0 : ℝ) (N : ℝ), |External.Bass.generator a b φ (γ u.toNNReal)| := by
    have heq : (∫ u in (0 : ℝ)..(t : ℝ), External.Bass.generator a b φ (γ u.toNNReal)) =
        ∫ u in Set.Ioc (0 : ℝ) (t : ℝ), External.Bass.generator a b φ (γ u.toNNReal) :=
      intervalIntegral.integral_of_le t.property
    rw [heq]
    calc
      _ ≤ ∫ u in Set.Ioc (0 : ℝ) (t : ℝ), |External.Bass.generator a b φ (γ u.toNNReal)| := by
        simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
          (fun u : ℝ => External.Bass.generator a b φ (γ u.toNNReal))
      _ ≤ _ := setIntegral_mono_set hi (ae_of_all _ fun _ => abs_nonneg _)
        (ae_of_all _ fun _ hu => ⟨hu.1, le_trans hu.2 (by exact_mod_cast htN)⟩)
  change |φ (γ t) - φ (γ 0) - ∫ u in (0 : ℝ)..(t : ℝ),
    External.Bass.generator a b φ (γ u.toNNReal)| ≤ _
  have h1 := hbγ t htN
  have h0 := hbγ 0 bot_le
  rw [Real.norm_eq_abs] at hint
  calc
    _ ≤ |φ (γ t)| + |φ (γ 0)| + |∫ u in (0 : ℝ)..(t : ℝ),
        External.Bass.generator a b φ (γ u.toNNReal)| := by
      exact (abs_sub _ _).trans (add_le_add (abs_sub _ _) le_rfl)
    _ ≤ _ := add_le_add (add_le_add h1 h0) hint

#print axioms u3_compensated_local_martingale_of_natural_occupation_bound

/-- Each mollified signed generator-graph orbit is a true source martingale
under the Bass transport of the same supplied quenched law. -/
theorem u3_signed_graph_mollified_orbit_martingale_of_deps
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hunforced : UnforcedAt hd Q) (hpath : PathwiseAt Q)
    (lam s : ℝ) (hs : 0 < s) (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ ω lam) 0 (Y (0, ω)))
    (f g : Lp ℂ 2 (reducedLaw Q))
    (hfg : IsComplexGeneratorPair Q ⟨0, by omega⟩ (lam : ℂ) f g)
    {G : Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hG : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) f G)
    (L : ℂ →L[ℝ] ℝ) (n : ℕ) :
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
  have hb := fun N : ℕ => u3_supplied_force_mollified_orbit_integrable_horizon_bound_of_deps
    (hpath := hpath) hd Q ⟨0, by omega⟩ lam Y hY _
    (Entropy.contDiff_unitMassScaledMollifier _).continuous
    (Entropy.hasCompactSupport_unitMassScaledMollifier (Entropy.scaleSeq_pos n))
    V hVm hV (N : ℝ≥0)
  have ho := fun N : ℕ => u3_signed_graph_generator_quenched_occupation_integrable_of_deps
    (hunforced := hunforced) (hpath := hpath) hd Q lam s hs Y hY f g hfg hG L (N : ℝ≥0) n
  have hp := fun N : ℕ => u3_signed_graph_generator_path_occupation_integrable_of_deps
    (hunforced := hunforced) (hpath := hpath) hd Q lam s hs Y hY f g hfg hG L (N : ℝ≥0) n
  filter_upwards [Q.regular, hY, ae_all_iff.mpr hb, ae_all_iff.mpr ho,
    ae_all_iff.mpr hp, u3_signed_graph_mollified_orbit_local_martingale_of_pathwise
      (hpath := hpath) hd Q lam s hs Y hY f g hfg hG L (Entropy.scaleSeq_pos n)]
    with ω hω hP hbω hoω hpω hlocal
  let : IsProbabilityMeasure (Y (0, ω)) := hP.1
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

#print axioms u3_signed_graph_mollified_orbit_martingale_of_deps

/-- Dynkin's formula for each signed mollified graph orbit under the same
supplied quenched law. -/
theorem u3_signed_graph_mollified_dynkin_of_deps
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hunforced : UnforcedAt hd Q) (hpath : PathwiseAt Q)
    (lam s : ℝ) (hs : 0 < s) (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ ω lam) 0 (Y (0, ω)))
    (f g : Lp ℂ 2 (reducedLaw Q))
    (hfg : IsComplexGeneratorPair Q ⟨0, by omega⟩ (lam : ℂ) f g)
    {G : Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hG : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) f G)
    (L : ℂ →L[ℝ] ℝ) (n : ℕ) (T : ℝ≥0) :
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
  filter_upwards [Q.regular, hY,
    u3_signed_graph_mollified_orbit_martingale_of_deps (hunforced := hunforced) (hpath := hpath) hd Q lam s hs Y hY f g hfg hG L n,
    u3_supplied_force_real_endpoint_integrable_of_deps (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY T M hMm hM,
    u3_supplied_force_real_endpoint_integrable_of_deps (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY 0 M hMm hM,
    u3_signed_graph_generator_compensator_integrable_of_deps (hunforced := hunforced) (hpath := hpath) hd Q lam s hs Y hY f g hfg hG L T n]
    with ω hω hP hmart ht h0 hc
  let : IsProbabilityMeasure (Y (0, ω)) := hP.1
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
        (hP.2.1.mono fun _ h => by simp only [h, translate_zero])
      _ = M (reduce ω) := by simp
  change (∫ γ : Path d, M (translate (γ T) (reduce ω)) ∂Y (0, ω)) - M (reduce ω) = _
  have hc' : Integrable (fun γ : Path d => ∫ u in Set.Ioc (0 : ℝ) (T : ℝ),
      envGenerator hd lam M (translate (γ u.toNNReal) (reduce ω))) (Y (0, ω)) := hc
  change (∫ γ : Path d, ((fun γ : Path d => M (translate (γ T) (reduce ω))) -
    (fun γ : Path d => M (translate (γ 0) (reduce ω)))) γ -
      (∫ u in Set.Ioc (0 : ℝ) (T : ℝ), envGenerator hd lam M
        (translate (γ u.toNNReal) (reduce ω))) ∂Y (0, ω)) = 0 at hz''
  rw [integral_sub (ht.sub h0) hc'] at hz''
  simp only [Pi.sub_apply] at hz''
  rw [integral_sub ht h0, hstart] at hz''
  exact sub_eq_zero.mp hz''

#print axioms u3_signed_graph_mollified_dynkin_of_deps

/-- Horizontal mollification converges along a quenched occupation subsequence
for the same supplied signed law. -/
theorem u3_supplied_force_mollification_occupation_subsequence_of_deps
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hunforced : UnforcedAt hd Q) (hpath : PathwiseAt Q)
    (lam : ℝ) (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ ω lam) 0 (Y (0, ω)))
    (T : ℝ≥0) (f : FieldPair d → ℝ) (hf : Measurable f)
    (hflp : MemLp f 2 (reducedLaw Q)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∀ᵐ ω ∂Q.measure,
      Filter.Tendsto (fun n => ∫ t in Set.Ioc (0 : ℝ) (T : ℝ),
        ∫ γ : Path d, |horizontalMollify
          (Calculus.unitMassScaledMollifier d (Entropy.scaleSeq (ns n))) f
          (translate (γ t.toNNReal) (reduce ω)) -
          f (translate (γ t.toNNReal) (reduce ω))| ∂Y (0, ω))
        Filter.atTop (𝓝 0) := by
  let r (n : ℕ) := fun w => horizontalMollify
    (Calculus.unitMassScaledMollifier d (Entropy.scaleSeq n)) f w - f w
  have hm (n : ℕ) : Measurable (r n) :=
    (measurable_horizontalMollify _
      (Entropy.contDiff_unitMassScaledMollifier _).continuous.measurable hf).sub hf
  have hr (n : ℕ) : MemLp (r n) 2 (reducedLaw Q) :=
    (Entropy.memLp_horizontalMollify_unitMass (reducedLaw_stationary Q)
      (Entropy.scaleSeq_pos n) ENNReal.ofNat_ne_top hf hflp).sub hflp
  have ht := (Calculus.tendsto_eLpNorm_horizontalMollify_unitMassScaledMollifier
    (reducedLaw Q) (reducedLaw_stationary Q) 2 ENNReal.ofNat_ne_top hf hflp).comp
      Entropy.tendsto_scaleSeq
  have htr := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp ht
  simp only [ENNReal.toReal_zero] at htr
  have hlim : Filter.Tendsto (fun n => ‖(hr n).toLp (r n)‖) Filter.atTop (𝓝 0) := by
    apply htr.congr
    intro n
    rw [Lp.norm_def, eLpNorm_congr_ae (hr n).coeFn_toLp]
    rfl
  exact u3_supplied_force_finite_time_quenched_subsequence_of_deps
    (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY T r hm hr hlim

#print axioms u3_supplied_force_mollification_occupation_subsequence_of_deps

/-- L²-small real observables have vanishing annealed absolute endpoint
expectation for the same supplied signed law. -/
theorem u3_supplied_force_real_endpoint_residual_tendsto_of_deps
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hunforced : UnforcedAt hd Q) (hpath : PathwiseAt Q)
    (lam : ℝ) (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ ω lam) 0 (Y (0, ω)))
    (t : ℝ≥0) (r : ℕ → FieldPair d → ℝ)
    (hm : ∀ n, Measurable (r n)) (hr : ∀ n, MemLp (r n) 2 (reducedLaw Q))
    (hlim : Filter.Tendsto (fun n => ‖(hr n).toLp (r n)‖) Filter.atTop (𝓝 0)) :
    Filter.Tendsto (fun n => ∫⁻ ω, ∫⁻ γ : Path d,
      ‖r n (translate (γ t) (reduce ω))‖ₑ ∂Y (0, ω) ∂Q.measure)
      Filter.atTop (𝓝 0) := by
  let R (n : ℕ) : FieldPair d → ℂ := fun w => (r n w : ℂ)
  have hR (n : ℕ) : MemLp (R n) 2 (reducedLaw Q) := (hr n).ofReal
  let F (n : ℕ) : Lp ℂ 2 (reducedLaw Q) := (hR n).toLp (R n)
  have hnorm (n : ℕ) : eLpNorm (fun w => F n w) 2 (reducedLaw Q) =
      ENNReal.ofReal ‖(hr n).toLp (r n)‖ := by
    rw [eLpNorm_congr_ae (hR n).coeFn_toLp]
    have heq : eLpNorm (R n) 2 (reducedLaw Q) = eLpNorm (r n) 2 (reducedLaw Q) := by
      apply eLpNorm_congr_enorm_ae (hR n).aestronglyMeasurable (hr n).aestronglyMeasurable
      filter_upwards [] with w
      apply enorm_eq_iff_norm_eq.mpr
      simpa only [R, Real.norm_eq_abs] using Complex.norm_real (r n w)
    rw [heq, ← eLpNorm_congr_ae (hr n).coeFn_toLp, ← Lp.enorm_def, ← ofReal_norm]
  have hF : Filter.Tendsto (fun n => eLpNorm (fun w => F n w) 2 (reducedLaw Q))
      Filter.atTop (𝓝 0) := by
    simp_rw [hnorm]
    simpa using ENNReal.tendsto_ofReal hlim
  have ht := u3_supplied_force_endpoint_residual_tendsto_of_deps
    (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY t F hF
  apply ht.congr
  intro n
  have he := u3_supplied_force_endpoint_ae_eq_of_deps (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY
    t (fun w => F n w) (R n) (Lp.stronglyMeasurable (F n)).measurable
    (Complex.continuous_ofReal.measurable.comp (hm n)) (hR n).coeFn_toLp
  apply lintegral_congr_ae
  filter_upwards [he] with ω hω
  apply lintegral_congr_ae
  filter_upwards [hω] with γ hγ
  rw [hγ]
  apply enorm_eq_iff_norm_eq.mpr
  simpa only [R, Real.norm_eq_abs] using Complex.norm_real (r n (translate (γ t) (reduce ω)))

#print axioms u3_supplied_force_real_endpoint_residual_tendsto_of_deps

/-- L²-small real observables have a quenched subsequence with vanishing
absolute endpoint expectation under the original supplied law. -/
theorem u3_supplied_force_endpoint_quenched_subsequence_of_deps
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hunforced : UnforcedAt hd Q) (hpath : PathwiseAt Q)
    (lam : ℝ) (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ ω lam) 0 (Y (0, ω)))
    (t : ℝ≥0) (r : ℕ → FieldPair d → ℝ)
    (hm : ∀ n, Measurable (r n)) (hr : ∀ n, MemLp (r n) 2 (reducedLaw Q))
    (hlim : Filter.Tendsto (fun n => ‖(hr n).toLp (r n)‖) Filter.atTop (𝓝 0)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∀ᵐ ω ∂Q.measure,
      Filter.Tendsto (fun n => ∫ γ : Path d,
        |r (ns n) (translate (γ t) (reduce ω))| ∂Y (0, ω)) Filter.atTop (𝓝 0) := by
  let : IsProbabilityMeasure Q.measure := Q.probability
  have hprob : ∀ᵐ ω ∂Q.measure, IsProbabilityMeasure (originLaw Y ω) :=
    hY.mono fun _ h => h.1
  obtain ⟨K, hK, hmarkov⟩ := Kernel.exists_ae_eq_isMarkovKernel hprob
    (IsProbabilityMeasure.ne_zero Q.measure)
  let : IsMarkovKernel K := hmarkov
  have hK' : ∀ᵐ ω ∂Q.measure, Y (0, ω) = K ω := hK
  let E : FieldPair d × Path d → FieldPair d := fun p =>
    translate (p.2 t) (reduce p.1)
  have hE : Measurable E := by
    exact (Probability.continuous_translate.comp
      ((continuous_eval.comp (continuous_snd.prodMk continuous_const)).prodMk
        (Probability.continuous_reduce.comp continuous_fst))).measurable
  let J (n : ℕ) : ℝ≥0∞ := ∫⁻ p, ‖r n (E p)‖ₑ ∂(Q.measure ⊗ₘ K)
  have hJ : Filter.Tendsto J Filter.atTop (𝓝 0) := by
    have ht := u3_supplied_force_real_endpoint_residual_tendsto_of_deps
      (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY t r hm hr hlim
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

#print axioms u3_supplied_force_endpoint_quenched_subsequence_of_deps

/-- A single subsequence controls a small observable along the whole finite
horizon and at both endpoints of the supplied path law. -/
theorem u3_supplied_force_occupation_endpoints_subsequence_of_deps
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hunforced : UnforcedAt hd Q) (hpath : PathwiseAt Q)
    (lam : ℝ) (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ ω lam) 0 (Y (0, ω)))
    (T : ℝ≥0) (r : ℕ → FieldPair d → ℝ)
    (hm : ∀ n, Measurable (r n)) (hr : ∀ n, MemLp (r n) 2 (reducedLaw Q))
    (hlim : Filter.Tendsto (fun n => ‖(hr n).toLp (r n)‖) Filter.atTop (𝓝 0)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∀ᵐ ω ∂Q.measure,
      Filter.Tendsto (fun n => ∫ t in Set.Ioc (0 : ℝ) (T : ℝ),
        ∫ γ : Path d, |r (ns n) (translate (γ t.toNNReal) (reduce ω))| ∂Y (0, ω))
        Filter.atTop (𝓝 0) ∧
      Filter.Tendsto (fun n => ∫ γ : Path d,
        |r (ns n) (translate (γ 0) (reduce ω))| ∂Y (0, ω)) Filter.atTop (𝓝 0) ∧
      Filter.Tendsto (fun n => ∫ γ : Path d,
        |r (ns n) (translate (γ T) (reduce ω))| ∂Y (0, ω)) Filter.atTop (𝓝 0) := by
  obtain ⟨a, ha, hocc⟩ := u3_supplied_force_finite_time_quenched_subsequence_of_deps
    (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY T r hm hr hlim
  obtain ⟨b, hb, hzero⟩ := u3_supplied_force_endpoint_quenched_subsequence_of_deps
    (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY 0 (r ∘ a) (fun n => hm (a n))
      (fun n => hr (a n)) (hlim.comp ha.tendsto_atTop)
  obtain ⟨c, hc, hend⟩ := u3_supplied_force_endpoint_quenched_subsequence_of_deps
    (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY T (r ∘ a ∘ b) (fun n => hm (a (b n)))
      (fun n => hr (a (b n))) (hlim.comp (ha.comp hb).tendsto_atTop)
  refine ⟨a ∘ b ∘ c, (ha.comp hb).comp hc, ?_⟩
  filter_upwards [hocc, hzero, hend] with ω hωocc hωzero hωend
  exact ⟨hωocc.comp (hb.comp hc).tendsto_atTop,
    hωzero.comp hc.tendsto_atTop, hωend⟩

#print axioms u3_supplied_force_occupation_endpoints_subsequence_of_deps

/-- One subsequence simultaneously controls the literal signed graph residual
and the mollified observable at both endpoints and throughout the horizon. -/
theorem u3_signed_graph_mollification_joint_subsequence_of_deps
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hunforced : UnforcedAt hd Q) (hpath : PathwiseAt Q)
    (lam s : ℝ) (hs : 0 < s) (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ ω lam) 0 (Y (0, ω)))
    (T : ℝ≥0) (f g : Lp ℂ 2 (reducedLaw Q))
    (hfg : IsComplexGeneratorPair Q ⟨0, by omega⟩ (lam : ℂ) f g)
    {G : Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hG : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) f G)
    (L : ℂ →L[ℝ] ℝ) :
    let V : FieldPair d → ℝ := fun w => L (f w)
    let M (n : ℕ) := horizontalMollify
      (Calculus.unitMassScaledMollifier d (Entropy.scaleSeq n)) V
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∀ᵐ ω ∂Q.measure,
      Filter.Tendsto (fun n => ∫ t in Set.Ioc (0 : ℝ) (T : ℝ),
        ∫ γ : Path d, |s * M (ns n) (translate (γ t.toNNReal) (reduce ω)) -
          envGenerator hd lam (M (ns n)) (translate (γ t.toNNReal) (reduce ω)) -
          L (((s : ℂ) • f - g) (translate (γ t.toNNReal) (reduce ω)))| ∂Y (0, ω))
        Filter.atTop (𝓝 0) ∧
      Filter.Tendsto (fun n => ∫ t in Set.Ioc (0 : ℝ) (T : ℝ),
        ∫ γ : Path d, |M (ns n) (translate (γ t.toNNReal) (reduce ω)) -
          V (translate (γ t.toNNReal) (reduce ω))| ∂Y (0, ω)) Filter.atTop (𝓝 0) ∧
      Filter.Tendsto (fun n => ∫ γ : Path d,
        |M (ns n) (translate (γ 0) (reduce ω)) - V (translate (γ 0) (reduce ω))|
          ∂Y (0, ω)) Filter.atTop (𝓝 0) ∧
      Filter.Tendsto (fun n => ∫ γ : Path d,
        |M (ns n) (translate (γ T) (reduce ω)) - V (translate (γ T) (reduce ω))|
          ∂Y (0, ω)) Filter.atTop (𝓝 0) := by
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
  obtain ⟨a, ha, hgraph⟩ := u3_signed_graph_literal_residual_occupation_subsequence_of_deps
    (hunforced := hunforced) (hpath := hpath) hd Q lam s hs Y hY T f g hfg hG L
  obtain ⟨b, hb, hboth⟩ := u3_supplied_force_occupation_endpoints_subsequence_of_deps
    (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY T (r ∘ a) (fun n => hm (a n))
      (fun n => hr (a n)) (hlim.comp ha.tendsto_atTop)
  refine ⟨a ∘ b, ha.comp hb, ?_⟩
  filter_upwards [hgraph, hboth] with ω hωgraph hωboth
  exact ⟨hωgraph.comp hb.tendsto_atTop, hωboth⟩

#print axioms u3_signed_graph_mollification_joint_subsequence_of_deps

/-- For an L² observable, finite-horizon path and time integration may be
interchanged for almost every supplied signed law. -/
theorem u3_supplied_force_occupation_fubini_of_deps
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hunforced : UnforcedAt hd Q) (hpath : PathwiseAt Q)
    (lam : ℝ) (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ ω lam) 0 (Y (0, ω)))
    (T : ℝ≥0) (r : FieldPair d → ℝ) (hm : Measurable r)
    (hr : MemLp r 2 (reducedLaw Q)) :
    ∀ᵐ ω ∂Q.measure,
      Integrable (fun p : Path d × ℝ =>
        r (translate (p.1 p.2.toNNReal) (reduce ω)))
          ((Y (0, ω)).prod (volume.restrict (Set.Ioc 0 (T : ℝ)))) ∧
      (∫ γ : Path d, (∫ t in Set.Ioc 0 (T : ℝ),
        r (translate (γ t.toNNReal) (reduce ω))) ∂Y (0, ω)) =
      ∫ t in Set.Ioc 0 (T : ℝ), ∫ γ : Path d,
        r (translate (γ t.toNNReal) (reduce ω)) ∂Y (0, ω) := by
  obtain ⟨K, hmarkov, hK, hi⟩ :=
    u3_supplied_force_finite_time_joint_integrable_of_deps
      (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY T r hm hr
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
  let : IsProbabilityMeasure (Y (0, ω)) := by rw [hKω]; infer_instance
  rw [← hKω] at htimeω hnormω
  have hmeas : Measurable (fun p : Path d × ℝ =>
      r (translate (p.1 p.2.toNNReal) (reduce ω))) := by
    apply hm.comp
    exact (Probability.continuous_translate.comp
      ((continuous_eval.comp (continuous_fst.prodMk
        (continuous_real_toNNReal.comp continuous_snd))).prodMk continuous_const)).measurable
  have hp : Integrable (fun p : Path d × ℝ =>
      r (translate (p.1 p.2.toNNReal) (reduce ω)))
      ((Y (0, ω)).prod (volume.restrict (Set.Ioc 0 (T : ℝ)))) := by
    apply (integrable_prod_iff hmeas.aestronglyMeasurable).mpr
    exact ⟨htimeω, hnormω⟩
  exact ⟨hp, (integral_prod _ hp).symm.trans (integral_prod_symm _ hp)⟩

#print axioms u3_supplied_force_occupation_fubini_of_deps

/-- A quenched compensator is bounded by its absolute occupation. -/
theorem u3_supplied_force_compensator_abs_le_occupation_of_deps
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hunforced : UnforcedAt hd Q) (hpath : PathwiseAt Q)
    (lam : ℝ) (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ ω lam) 0 (Y (0, ω)))
    (T : ℝ≥0) (r : FieldPair d → ℝ) (hm : Measurable r)
    (hr : MemLp r 2 (reducedLaw Q)) :
    ∀ᵐ ω ∂Q.measure,
      |∫ γ : Path d, (∫ t in Set.Ioc 0 (T : ℝ),
        r (translate (γ t.toNNReal) (reduce ω))) ∂Y (0, ω)| ≤
      ∫ t in Set.Ioc 0 (T : ℝ), ∫ γ : Path d,
        |r (translate (γ t.toNNReal) (reduce ω))| ∂Y (0, ω) := by
  filter_upwards [hY, u3_supplied_force_occupation_fubini_of_deps
    (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY T r hm hr] with ω hω hp
  let : IsProbabilityMeasure (Y (0, ω)) := hω.1
  let F : Path d × ℝ → ℝ := fun p => r (translate (p.1 p.2.toNNReal) (reduce ω))
  have hi : Integrable F ((Y (0, ω)).prod (volume.restrict (Set.Ioc 0 (T : ℝ)))) := hp.1
  calc
    _ = ‖∫ p, F p ∂((Y (0, ω)).prod (volume.restrict (Set.Ioc 0 (T : ℝ))))‖ := by
      rw [integral_prod _ hi, Real.norm_eq_abs]
    _ ≤ ∫ p, ‖F p‖ ∂((Y (0, ω)).prod (volume.restrict (Set.Ioc 0 (T : ℝ)))) :=
      norm_integral_le_integral_norm F
    _ = _ := by
      simpa only [F, Real.norm_eq_abs] using integral_prod_symm (fun p => ‖F p‖) hi.norm

#print axioms u3_supplied_force_compensator_abs_le_occupation_of_deps


/-- Vanishing reduced-law L² errors have a common subsequence whose signed
path expectations and finite-horizon compensators vanish quenched. -/
theorem u3_supplied_force_expectation_compensator_subsequence_of_deps
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hunforced : UnforcedAt hd Q) (hpath : PathwiseAt Q)
    (lam : ℝ) (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ ω lam) 0 (Y (0, ω)))
    (T : ℝ≥0) (r : ℕ → FieldPair d → ℝ)
    (hm : ∀ n, Measurable (r n)) (hr : ∀ n, MemLp (r n) 2 (reducedLaw Q))
    (hlim : Filter.Tendsto (fun n => ‖(hr n).toLp (r n)‖) Filter.atTop (𝓝 0)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∀ᵐ ω ∂Q.measure,
      Filter.Tendsto (fun n => ∫ γ : Path d, (∫ t in Set.Ioc (0 : ℝ) (T : ℝ),
        r (ns n) (translate (γ t.toNNReal) (reduce ω))) ∂Y (0, ω)) Filter.atTop (𝓝 0) ∧
      Filter.Tendsto (fun n => ∫ γ : Path d,
        r (ns n) (translate (γ 0) (reduce ω)) ∂Y (0, ω)) Filter.atTop (𝓝 0) ∧
      Filter.Tendsto (fun n => ∫ γ : Path d,
        r (ns n) (translate (γ T) (reduce ω)) ∂Y (0, ω)) Filter.atTop (𝓝 0) := by
  obtain ⟨ns, hns, hconv⟩ := u3_supplied_force_occupation_endpoints_subsequence_of_deps
    (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY T r hm hr hlim
  have hbound : ∀ᵐ ω ∂Q.measure, ∀ n,
      |∫ γ : Path d, (∫ t in Set.Ioc (0 : ℝ) (T : ℝ),
        r (ns n) (translate (γ t.toNNReal) (reduce ω))) ∂Y (0, ω)| ≤
      ∫ t in Set.Ioc (0 : ℝ) (T : ℝ), ∫ γ : Path d,
        |r (ns n) (translate (γ t.toNNReal) (reduce ω))| ∂Y (0, ω) := by
    exact ae_all_iff.mpr fun n => u3_supplied_force_compensator_abs_le_occupation_of_deps
      (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY T (r (ns n)) (hm (ns n)) (hr (ns n))
  refine ⟨ns, hns, ?_⟩
  filter_upwards [hconv, hbound] with ω hc hb
  refine ⟨?_, ?_, ?_⟩
  · apply squeeze_zero_norm (a := fun n => ∫ t in Set.Ioc (0 : ℝ) (T : ℝ),
        ∫ γ : Path d, |r (ns n) (translate (γ t.toNNReal) (reduce ω))| ∂Y (0, ω))
    · intro n
      simpa only [Real.norm_eq_abs] using hb n
    · exact hc.1
  · apply squeeze_zero_norm (a := fun n => ∫ γ : Path d,
        |r (ns n) (translate (γ 0) (reduce ω))| ∂Y (0, ω))
    · intro n
      simpa only [Real.norm_eq_abs] using
        (norm_integral_le_integral_norm (fun γ : Path d =>
          r (ns n) (translate (γ 0) (reduce ω))))
    · exact hc.2.1
  · apply squeeze_zero_norm (a := fun n => ∫ γ : Path d,
        |r (ns n) (translate (γ T) (reduce ω))| ∂Y (0, ω))
    · intro n
      simpa only [Real.norm_eq_abs] using
        (norm_integral_le_integral_norm (fun γ : Path d =>
          r (ns n) (translate (γ T) (reduce ω))))
    · exact hc.2.2

#print axioms u3_supplied_force_expectation_compensator_subsequence_of_deps


/-- The actual signed graph residual has vanishing quenched compensator
along a subsequence for the supplied path law. -/
theorem u3_signed_graph_residual_compensator_subsequence_of_deps
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hunforced : UnforcedAt hd Q) (hpath : PathwiseAt Q)
    (lam s : ℝ) (hs : 0 < s) (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ ω lam) 0 (Y (0, ω)))
    (T : ℝ≥0) (f g : Lp ℂ 2 (reducedLaw Q))
    (hfg : IsComplexGeneratorPair Q ⟨0, by omega⟩ (lam : ℂ) f g)
    {G : Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hG : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) f G)
    (L : ℂ →L[ℝ] ℝ) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∀ᵐ ω ∂Q.measure,
      Filter.Tendsto (fun n => ∫ γ : Path d, (∫ t in Set.Ioc (0 : ℝ) (T : ℝ),
        (s * horizontalMollify (Calculus.unitMassScaledMollifier d (Entropy.scaleSeq (ns n)))
          (fun v => L (f v)) (translate (γ t.toNNReal) (reduce ω)) -
        envGenerator hd lam (horizontalMollify
          (Calculus.unitMassScaledMollifier d (Entropy.scaleSeq (ns n))) (fun v => L (f v)))
          (translate (γ t.toNNReal) (reduce ω)) -
        L (((s : ℂ) • f - g) (translate (γ t.toNNReal) (reduce ω))))) ∂Y (0, ω))
        Filter.atTop (𝓝 0) := by
  obtain ⟨r, hr, hm, he, hlim⟩ :=
    u3_signed_graph_mollified_residual_representatives hd Q lam s hs f g hfg hG L
  obtain ⟨ns, hns, hconv⟩ := u3_supplied_force_expectation_compensator_subsequence_of_deps
    (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY T r hm hr hlim
  have ha := fun n => u3_supplied_force_ae_eq_occupation_of_pathwise (hpath := hpath) hd Q
    ⟨0, by omega⟩ lam Y hY (r (ns n)) _ (he (ns n))
  refine ⟨ns, hns, ?_⟩
  filter_upwards [hconv, ae_all_iff.mpr ha] with ω hc heq
  apply hc.1.congr
  intro n
  apply integral_congr_ae
  filter_upwards [heq n] with γ hγ
  apply integral_congr_ae
  exact ae_restrict_of_ae_restrict_of_subset (fun _ ht => ht.1) hγ

#print axioms u3_signed_graph_residual_compensator_subsequence_of_deps


/-- The signed graph residual and the mollification error both vanish in
quenched compensators, while the latter also vanishes at both endpoints. -/
theorem u3_signed_graph_joint_compensator_subsequence_of_deps
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hunforced : UnforcedAt hd Q) (hpath : PathwiseAt Q)
    (lam s : ℝ) (hs : 0 < s) (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ ω lam) 0 (Y (0, ω)))
    (T : ℝ≥0) (f g : Lp ℂ 2 (reducedLaw Q))
    (hfg : IsComplexGeneratorPair Q ⟨0, by omega⟩ (lam : ℂ) f g)
    {G : Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hG : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) f G)
    (L : ℂ →L[ℝ] ℝ) :
    let V : FieldPair d → ℝ := fun w => L (f w)
    let M (n : ℕ) := horizontalMollify
      (Calculus.unitMassScaledMollifier d (Entropy.scaleSeq n)) V
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∀ᵐ ω ∂Q.measure,
      Filter.Tendsto (fun n => ∫ γ : Path d, (∫ t in Set.Ioc (0 : ℝ) (T : ℝ),
        (s * M (ns n) (translate (γ t.toNNReal) (reduce ω)) -
          envGenerator hd lam (M (ns n)) (translate (γ t.toNNReal) (reduce ω)) -
          L (((s : ℂ) • f - g) (translate (γ t.toNNReal) (reduce ω))))) ∂Y (0, ω))
        Filter.atTop (𝓝 0) ∧
      Filter.Tendsto (fun n => ∫ γ : Path d, (∫ t in Set.Ioc (0 : ℝ) (T : ℝ),
        (M (ns n) (translate (γ t.toNNReal) (reduce ω)) -
          V (translate (γ t.toNNReal) (reduce ω)))) ∂Y (0, ω)) Filter.atTop (𝓝 0) ∧
      Filter.Tendsto (fun n => ∫ γ : Path d,
        (M (ns n) (translate (γ 0) (reduce ω)) - V (translate (γ 0) (reduce ω)))
          ∂Y (0, ω)) Filter.atTop (𝓝 0) ∧
      Filter.Tendsto (fun n => ∫ γ : Path d,
        (M (ns n) (translate (γ T) (reduce ω)) - V (translate (γ T) (reduce ω)))
          ∂Y (0, ω)) Filter.atTop (𝓝 0) := by
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
  obtain ⟨a, ha, hgraph⟩ := u3_signed_graph_residual_compensator_subsequence_of_deps
    (hunforced := hunforced) (hpath := hpath) hd Q lam s hs Y hY T f g hfg hG L
  obtain ⟨b, hb, herror⟩ := u3_supplied_force_expectation_compensator_subsequence_of_deps
    (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY T (r ∘ a) (fun n => hm (a n))
      (fun n => hr (a n)) (hlim.comp ha.tendsto_atTop)
  refine ⟨a ∘ b, ha.comp hb, ?_⟩
  filter_upwards [hgraph, herror] with ω hg he
  exact ⟨hg.comp hb.tendsto_atTop, he⟩

#print axioms u3_signed_graph_joint_compensator_subsequence_of_deps



/-- Real-linear evaluation of the graph resolvent holds for L² representatives. -/
theorem u3_real_linear_graph_representative_ae
    {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (s : ℝ) (f g : Lp ℂ 2 (reducedLaw Q)) (L : ℂ →L[ℝ] ℝ) :
    (fun w => L (((s : ℂ) • f - g) w)) =ᵐ[reducedLaw Q]
      fun w => s * L (f w) - L (g w) := by
  filter_upwards [Lp.coeFn_sub ((s : ℂ) • f) g, Lp.coeFn_smul (s : ℂ) f] with w hsub hsmul
  simp only [Pi.sub_apply, Pi.smul_apply] at hsub hsmul
  have hL : L ((s : ℂ) • f w) = s * L (f w) := by
    have h := L.map_smul s (f w)
    simpa only [Complex.real_smul, smul_eq_mul] using h
  rw [hsub, hsmul, map_sub, hL]

/-- The graph resolvent representative identity holds along almost every
supplied path at almost every positive time. -/
theorem u3_real_linear_graph_representative_occupation_of_pathwise
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hpath : PathwiseAt Q)
    (lam s : ℝ) (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ ω lam) 0 (Y (0, ω)))
    (f g : Lp ℂ 2 (reducedLaw Q)) (L : ℂ →L[ℝ] ℝ) :
    ∀ᵐ ω ∂Q.measure, ∀ᵐ γ ∂Y (0, ω),
      ∀ᵐ t ∂volume.restrict (Set.Ioi (0 : ℝ)),
        L (((s : ℂ) • f - g) (translate (γ t.toNNReal) (reduce ω))) =
          s * L (f (translate (γ t.toNNReal) (reduce ω))) -
            L (g (translate (γ t.toNNReal) (reduce ω))) := by
  exact u3_supplied_force_ae_eq_occupation_of_pathwise (hpath := hpath) hd Q
    ⟨0, by omega⟩ lam Y hY
    (fun w => L (((s : ℂ) • f - g) w))
    (fun w => s * L (f w) - L (g w))
    (u3_real_linear_graph_representative_ae Q s f g L)

#print axioms u3_real_linear_graph_representative_occupation_of_pathwise


/-- Quenched finite-horizon compensators respect subtraction for L² observables. -/
theorem u3_supplied_force_compensator_sub_of_deps
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hunforced : UnforcedAt hd Q) (hpath : PathwiseAt Q)
    (lam : ℝ) (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ ω lam) 0 (Y (0, ω)))
    (T : ℝ≥0) (f g : FieldPair d → ℝ) (hf : Measurable f) (hg : Measurable g)
    (hflp : MemLp f 2 (reducedLaw Q)) (hglp : MemLp g 2 (reducedLaw Q)) :
    ∀ᵐ ω ∂Q.measure,
      (∫ γ : Path d, (∫ t in Set.Ioc (0 : ℝ) (T : ℝ),
        (f (translate (γ t.toNNReal) (reduce ω)) -
          g (translate (γ t.toNNReal) (reduce ω)))) ∂Y (0, ω)) =
      (∫ γ : Path d, (∫ t in Set.Ioc (0 : ℝ) (T : ℝ),
        f (translate (γ t.toNNReal) (reduce ω))) ∂Y (0, ω)) -
      (∫ γ : Path d, (∫ t in Set.Ioc (0 : ℝ) (T : ℝ),
        g (translate (γ t.toNNReal) (reduce ω))) ∂Y (0, ω)) := by
  filter_upwards [hY, u3_supplied_force_occupation_fubini_of_deps
    (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY T f hf hflp,
    u3_supplied_force_occupation_fubini_of_deps
      (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY T g hg hglp] with ω hP hfi hgi
  let : IsProbabilityMeasure (Y (0, ω)) := hP.1
  let F : Path d × ℝ → ℝ := fun p => f (translate (p.1 p.2.toNNReal) (reduce ω))
  let G : Path d × ℝ → ℝ := fun p => g (translate (p.1 p.2.toNNReal) (reduce ω))
  have hF : Integrable F ((Y (0, ω)).prod (volume.restrict (Set.Ioc 0 (T : ℝ)))) := hfi.1
  have hG : Integrable G ((Y (0, ω)).prod (volume.restrict (Set.Ioc 0 (T : ℝ)))) := hgi.1
  change (∫ γ : Path d, (∫ t in Set.Ioc (0 : ℝ) (T : ℝ),
    ((F - G) (γ, t))) ∂Y (0, ω)) =
    (∫ γ : Path d, (∫ t in Set.Ioc (0 : ℝ) (T : ℝ), F (γ, t)) ∂Y (0, ω)) -
    (∫ γ : Path d, (∫ t in Set.Ioc (0 : ℝ) (T : ℝ), G (γ, t)) ∂Y (0, ω))
  rw [← integral_prod _ (hF.sub hG), ← integral_prod _ hF, ← integral_prod _ hG]
  exact integral_sub hF hG

#print axioms u3_supplied_force_compensator_sub_of_deps


/-- Algebraic relation between the literal graph residual, mollification
error and generator error under the supplied quenched law. -/
theorem u3_signed_graph_compensator_algebra_of_deps
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hunforced : UnforcedAt hd Q) (hpath : PathwiseAt Q)
    (lam s : ℝ) (hs : 0 < s) (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ ω lam) 0 (Y (0, ω)))
    (T : ℝ≥0) (f g : Lp ℂ 2 (reducedLaw Q))
    (hfg : IsComplexGeneratorPair Q ⟨0, by omega⟩ (lam : ℂ) f g)
    {G : Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hG : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) f G)
    (L : ℂ →L[ℝ] ℝ) (n : ℕ) :
    let V : FieldPair d → ℝ := fun w => L (f w)
    let W : FieldPair d → ℝ := fun w => L (g w)
    let M := horizontalMollify (Calculus.unitMassScaledMollifier d (Entropy.scaleSeq n)) V
    ∀ᵐ ω ∂Q.measure,
      (∫ γ : Path d, (∫ t in Set.Ioc (0 : ℝ) (T : ℝ),
        (s * M (translate (γ t.toNNReal) (reduce ω)) -
          envGenerator hd lam M (translate (γ t.toNNReal) (reduce ω)) -
          L (((s : ℂ) • f - g) (translate (γ t.toNNReal) (reduce ω))))) ∂Y (0, ω)) =
      s * (∫ γ : Path d, (∫ t in Set.Ioc (0 : ℝ) (T : ℝ),
        (M (translate (γ t.toNNReal) (reduce ω)) -
          V (translate (γ t.toNNReal) (reduce ω)))) ∂Y (0, ω)) -
      ((∫ γ : Path d, (∫ t in Set.Ioc (0 : ℝ) (T : ℝ),
        envGenerator hd lam M (translate (γ t.toNNReal) (reduce ω))) ∂Y (0, ω)) -
       (∫ γ : Path d, (∫ t in Set.Ioc (0 : ℝ) (T : ℝ),
        W (translate (γ t.toNNReal) (reduce ω))) ∂Y (0, ω))) := by
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
    u3_signed_graph_mollified_generator_representatives hd Q lam s hs f g hfg hG L
  let B : FieldPair d → ℝ := fun w => s * (M w - V w)
  let H : FieldPair d → ℝ := fun w => a n w - W w
  have hBm : Measurable B := measurable_const.mul (hMm.sub hVm)
  have hHm : Measurable H := (ham n).sub hWm
  have hB : MemLp B 2 (reducedLaw Q) := (hM.sub hV).const_mul s
  have hH : MemLp H 2 (reducedLaw Q) := (ha n).sub hW
  have he : (fun w => B w - H w) =ᵐ[reducedLaw Q]
      fun w => s * M w - envGenerator hd lam M w - L (((s : ℂ) • f - g) w) := by
    filter_upwards [hae n, u3_real_linear_graph_representative_ae Q s f g L] with w hgen hgraph
    change a n w = envGenerator hd lam M w at hgen
    change L (((s : ℂ) • f - g) w) = s * V w - W w at hgraph
    dsimp only [B, H]
    rw [hgen, hgraph]
    ring
  have hepath := u3_supplied_force_ae_eq_occupation_of_pathwise (hpath := hpath) hd Q
    ⟨0, by omega⟩ lam Y hY (fun w => B w - H w)
      (fun w => s * M w - envGenerator hd lam M w - L (((s : ℂ) • f - g) w)) he
  have hgpath := u3_supplied_force_ae_eq_occupation_of_pathwise (hpath := hpath) hd Q
    ⟨0, by omega⟩ lam Y hY (a n) (envGenerator hd lam M) (hae n)
  filter_upwards [hepath, hgpath,
    u3_supplied_force_compensator_sub_of_deps (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY T B H hBm hHm hB hH,
    u3_supplied_force_compensator_sub_of_deps (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY T (a n) W
      (ham n) hWm (ha n) hW] with ω heω hgω hsub hsub'
  have heq : (∫ γ : Path d, (∫ t in Set.Ioc (0 : ℝ) (T : ℝ),
      (B (translate (γ t.toNNReal) (reduce ω)) - H (translate (γ t.toNNReal) (reduce ω)))) ∂Y (0, ω)) =
      ∫ γ : Path d, (∫ t in Set.Ioc (0 : ℝ) (T : ℝ),
        (s * M (translate (γ t.toNNReal) (reduce ω)) -
          envGenerator hd lam M (translate (γ t.toNNReal) (reduce ω)) -
          L (((s : ℂ) • f - g) (translate (γ t.toNNReal) (reduce ω))))) ∂Y (0, ω) := by
    apply integral_congr_ae
    filter_upwards [heω] with γ hγ
    apply integral_congr_ae
    exact ae_restrict_of_ae_restrict_of_subset (fun _ ht => ht.1) hγ
  have hgen : (∫ γ : Path d, (∫ t in Set.Ioc (0 : ℝ) (T : ℝ),
      a n (translate (γ t.toNNReal) (reduce ω))) ∂Y (0, ω)) =
      ∫ γ : Path d, (∫ t in Set.Ioc (0 : ℝ) (T : ℝ),
        envGenerator hd lam M (translate (γ t.toNNReal) (reduce ω))) ∂Y (0, ω) := by
    apply integral_congr_ae
    filter_upwards [hgω] with γ hγ
    apply integral_congr_ae
    exact ae_restrict_of_ae_restrict_of_subset (fun _ ht => ht.1) hγ
  dsimp only [H] at hsub
  rw [hsub', hgen] at hsub
  rw [← heq, hsub]
  simp only [B, integral_const_mul]
  rfl

#print axioms u3_signed_graph_compensator_algebra_of_deps


/-- The literal mollified generator compensators converge to the graph
output compensator along a common quenched subsequence. -/
theorem u3_signed_graph_generator_compensator_subsequence_of_deps
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hunforced : UnforcedAt hd Q) (hpath : PathwiseAt Q)
    (lam s : ℝ) (hs : 0 < s) (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ ω lam) 0 (Y (0, ω)))
    (T : ℝ≥0) (f g : Lp ℂ 2 (reducedLaw Q))
    (hfg : IsComplexGeneratorPair Q ⟨0, by omega⟩ (lam : ℂ) f g)
    {G : Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hG : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) f G)
    (L : ℂ →L[ℝ] ℝ) :
    let V : FieldPair d → ℝ := fun w => L (f w)
    let W : FieldPair d → ℝ := fun w => L (g w)
    let M (n : ℕ) := horizontalMollify
      (Calculus.unitMassScaledMollifier d (Entropy.scaleSeq n)) V
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∀ᵐ ω ∂Q.measure,
      Filter.Tendsto (fun n => ∫ γ : Path d, (∫ t in Set.Ioc (0 : ℝ) (T : ℝ),
        envGenerator hd lam (M (ns n)) (translate (γ t.toNNReal) (reduce ω))) ∂Y (0, ω))
        Filter.atTop (𝓝 (∫ γ : Path d, (∫ t in Set.Ioc (0 : ℝ) (T : ℝ),
          W (translate (γ t.toNNReal) (reduce ω))) ∂Y (0, ω))) ∧
      Filter.Tendsto (fun n => ∫ γ : Path d,
        (M (ns n) (translate (γ 0) (reduce ω)) - V (translate (γ 0) (reduce ω)))
          ∂Y (0, ω)) Filter.atTop (𝓝 0) ∧
      Filter.Tendsto (fun n => ∫ γ : Path d,
        (M (ns n) (translate (γ T) (reduce ω)) - V (translate (γ T) (reduce ω)))
          ∂Y (0, ω)) Filter.atTop (𝓝 0) := by
  obtain ⟨ns, hns, hc⟩ := u3_signed_graph_joint_compensator_subsequence_of_deps
    (hunforced := hunforced) (hpath := hpath) hd Q lam s hs Y hY T f g hfg hG L
  have halg := fun n => u3_signed_graph_compensator_algebra_of_deps
    (hunforced := hunforced) (hpath := hpath) hd Q lam s hs Y hY T f g hfg hG L (ns n)
  refine ⟨ns, hns, ?_⟩
  filter_upwards [hc, ae_all_iff.mpr halg] with ω hc ha
  refine ⟨?_, hc.2.2⟩
  have ht := (hc.2.1.const_mul s).sub hc.1
  have ht' := ht.const_add (∫ γ : Path d, (∫ t in Set.Ioc (0 : ℝ) (T : ℝ),
    L (g (translate (γ t.toNNReal) (reduce ω)))) ∂Y (0, ω))
  simp only [mul_zero, sub_self, add_zero] at ht'
  apply ht'.congr
  intro n
  have hn := ha n
  linarith

#print axioms u3_signed_graph_generator_compensator_subsequence_of_deps


/-- Dynkin's formula for an arbitrary signed generator graph pair, under
the supplied quenched path laws. -/
theorem u3_signed_graph_dynkin_of_deps
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hunforced : UnforcedAt hd Q) (hpath : PathwiseAt Q)
    (lam s : ℝ) (hs : 0 < s) (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ ω lam) 0 (Y (0, ω)))
    (T : ℝ≥0) (f g : Lp ℂ 2 (reducedLaw Q))
    (hfg : IsComplexGeneratorPair Q ⟨0, by omega⟩ (lam : ℂ) f g)
    {G : Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hG : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) f G)
    (L : ℂ →L[ℝ] ℝ) :
    ∀ᵐ ω ∂Q.measure,
      (∫ γ : Path d, L (f (translate (γ T) (reduce ω))) ∂Y (0, ω)) -
        L (f (reduce ω)) =
      ∫ γ : Path d, (∫ t in Set.Ioc (0 : ℝ) (T : ℝ),
        L (g (translate (γ t.toNNReal) (reduce ω)))) ∂Y (0, ω) := by
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
  obtain ⟨ns, hns, hc⟩ := u3_signed_graph_generator_compensator_subsequence_of_deps
    (hunforced := hunforced) (hpath := hpath) hd Q lam s hs Y hY T f g hfg hG L
  have hdyn (n : ℕ) := u3_signed_graph_mollified_dynkin_of_deps
    (hunforced := hunforced) (hpath := hpath) hd Q lam s hs Y hY f g hfg hG L (ns n) T
  have hMi (n : ℕ) := u3_supplied_force_real_endpoint_integrable_of_deps
    (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY T (M (ns n)) (hMm (ns n)) (hM (ns n))
  filter_upwards [hc, hY, ae_all_iff.mpr hdyn, ae_all_iff.mpr hMi,
    u3_supplied_force_real_endpoint_integrable_of_deps (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY T V hVm hV]
    with ω hc hP hdyn hMi hVi
  let : IsProbabilityMeasure (Y (0, ω)) := hP.1
  have hstart (n : ℕ) : (∫ γ : Path d,
      (M (ns n) (translate (γ 0) (reduce ω)) - V (translate (γ 0) (reduce ω))) ∂Y (0, ω)) =
      M (ns n) (reduce ω) - V (reduce ω) := by
    calc
      _ = ∫ _ : Path d, (M (ns n) (reduce ω) - V (reduce ω)) ∂Y (0, ω) :=
        integral_congr_ae (hP.2.1.mono fun _ h => by simp only [h, translate_zero])
      _ = _ := by simp
  have ht := (hc.2.2.sub hc.2.1).const_add
    ((∫ γ : Path d, V (translate (γ T) (reduce ω)) ∂Y (0, ω)) - V (reduce ω))
  simp only [sub_self, add_zero] at ht
  have hlim : Filter.Tendsto (fun n =>
      (∫ γ : Path d, M (ns n) (translate (γ T) (reduce ω)) ∂Y (0, ω)) -
        M (ns n) (reduce ω)) Filter.atTop
      (𝓝 ((∫ γ : Path d, V (translate (γ T) (reduce ω)) ∂Y (0, ω)) - V (reduce ω))) := by
    apply ht.congr
    intro n
    rw [integral_sub (hMi n) hVi, hstart n]
    linarith
  have hlim' := hlim.congr (fun n => hdyn n)
  exact tendsto_nhds_unique hlim' hc.1

#print axioms u3_signed_graph_dynkin_of_deps


/-- Time-integrated form of the signed graph Dynkin identity. -/
theorem u3_signed_graph_dynkin_fubini_of_deps
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hunforced : UnforcedAt hd Q) (hpath : PathwiseAt Q)
    (lam s : ℝ) (hs : 0 < s) (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ ω lam) 0 (Y (0, ω)))
    (T : ℝ≥0) (f g : Lp ℂ 2 (reducedLaw Q))
    (hfg : IsComplexGeneratorPair Q ⟨0, by omega⟩ (lam : ℂ) f g)
    {G : Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hG : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) f G)
    (L : ℂ →L[ℝ] ℝ) :
    ∀ᵐ ω ∂Q.measure,
      (∫ γ : Path d, L (f (translate (γ T) (reduce ω))) ∂Y (0, ω)) -
        L (f (reduce ω)) =
      ∫ t in Set.Ioc (0 : ℝ) (T : ℝ), ∫ γ : Path d,
        L (g (translate (γ t.toNNReal) (reduce ω))) ∂Y (0, ω) := by
  let W : FieldPair d → ℝ := fun w => L (g w)
  have hWm : Measurable W := L.continuous.measurable.comp (Lp.stronglyMeasurable g).measurable
  have hW : MemLp W 2 (reducedLaw Q) := L.comp_memLp' (Lp.memLp g)
  filter_upwards [u3_signed_graph_dynkin_of_deps (hunforced := hunforced) (hpath := hpath) hd Q lam s hs Y hY T f g hfg hG L,
    u3_supplied_force_occupation_fubini_of_deps (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY T W hWm hW]
    with ω hdyn hfub
  exact hdyn.trans hfub.2

#print axioms u3_signed_graph_dynkin_fubini_of_deps


/-- The time-integrated Dynkin identity depends only on the full generator
pair: its horizontal gradient witness is supplied by the graph itself. -/
theorem u3_signed_generator_pair_dynkin_of_deps
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hunforced : UnforcedAt hd Q) (hpath : PathwiseAt Q)
    (lam : ℝ) (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ ω lam) 0 (Y (0, ω)))
    (T : ℝ≥0) (f g : Lp ℂ 2 (reducedLaw Q))
    (hfg : IsComplexGeneratorPair Q ⟨0, by omega⟩ (lam : ℂ) f g)
    (L : ℂ →L[ℝ] ℝ) :
    ∀ᵐ ω ∂Q.measure,
      (∫ γ : Path d, L (f (translate (γ T) (reduce ω))) ∂Y (0, ω)) -
        L (f (reduce ω)) =
      ∫ t in Set.Ioc (0 : ℝ) (T : ℝ), ∫ γ : Path d,
        L (g (translate (γ t.toNNReal) (reduce ω))) ∂Y (0, ω) := by
  obtain ⟨G, hG, hform⟩ := hfg
  exact u3_signed_graph_dynkin_fubini_of_deps (hunforced := hunforced) (hpath := hpath) hd Q lam 1 (by norm_num)
    Y hY T f g ⟨G, hG, hform⟩ hG L

#print axioms u3_signed_generator_pair_dynkin_of_deps


/-- The supplied path action respects subtraction of reduced-law L² data. -/
theorem u3_supplied_force_endpoint_action_sub_of_deps
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hunforced : UnforcedAt hd Q) (hpath : PathwiseAt Q)
    (lam : ℝ) (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ ω lam) 0 (Y (0, ω)))
    (t : ℝ≥0) (f g : Lp ℂ 2 (reducedLaw Q)) :
    ∀ᵐ ω ∂Q.measure,
      (∫ γ : Path d, (f - g) (translate (γ t) (reduce ω)) ∂Y (0, ω)) =
      (∫ γ : Path d, f (translate (γ t) (reduce ω)) ∂Y (0, ω)) -
        ∫ γ : Path d, g (translate (γ t) (reduce ω)) ∂Y (0, ω) := by
  have he := u3_supplied_force_endpoint_ae_eq_of_deps (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY t
    (fun w => (f - g) w) (fun w => f w - g w)
    (Lp.stronglyMeasurable (f - g)).measurable
    ((Lp.stronglyMeasurable f).measurable.sub (Lp.stronglyMeasurable g).measurable)
    (Lp.coeFn_sub f g)
  filter_upwards [he,
    u3_supplied_force_endpoint_integrable_of_deps (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY t f,
    u3_supplied_force_endpoint_integrable_of_deps (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY t g]
    with ω he hf hg
  rw [integral_congr_ae he]
  exact integral_sub hf hg

/-- The annealed L¹ distance between supplied path actions is controlled by
the reduced-law L² distance of their inputs. -/
theorem u3_supplied_force_endpoint_action_sub_bound_of_deps
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hunforced : UnforcedAt hd Q) (hpath : PathwiseAt Q)
    (lam : ℝ) (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ ω lam) 0 (Y (0, ω)))
    (t : ℝ≥0) (f g : Lp ℂ 2 (reducedLaw Q)) :
    (∫⁻ ω, ‖(∫ γ : Path d, f (translate (γ t) (reduce ω)) ∂Y (0, ω)) -
      (∫ γ : Path d, g (translate (γ t) (reduce ω)) ∂Y (0, ω))‖ₑ ∂Q.measure) ≤
      ENNReal.ofReal (Real.exp (lam ^ 2 * (Real.exp (2 * Λ₀) * Λ₀) * (t : ℝ))) ^ (1 / 2 : ℝ) *
        eLpNorm (fun ρ => (f - g) ρ) 2 (reducedLaw Q) := by
  have he := u3_supplied_force_endpoint_action_sub_of_deps (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY t f g
  calc
    _ = ∫⁻ ω, ‖∫ γ : Path d, (f - g) (translate (γ t) (reduce ω)) ∂Y (0, ω)‖ₑ ∂Q.measure := by
      apply lintegral_congr_ae
      filter_upwards [he] with ω hω
      rw [hω]
    _ ≤ _ := u3_supplied_force_endpoint_annealed_lintegral_bound_of_deps
      (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY t (f - g)

#print axioms u3_supplied_force_endpoint_action_sub_of_deps
#print axioms u3_supplied_force_endpoint_action_sub_bound_of_deps

/-- A single annealed action bound applies throughout a fixed time horizon. -/
theorem u3_supplied_force_endpoint_action_sub_horizon_bound_of_deps
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hunforced : UnforcedAt hd Q) (hpath : PathwiseAt Q)
    (lam : ℝ) (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ ω lam) 0 (Y (0, ω)))
    (t T : ℝ≥0) (ht : t ≤ T) (f g : Lp ℂ 2 (reducedLaw Q)) :
    (∫⁻ ω, ‖(∫ γ : Path d, f (translate (γ t) (reduce ω)) ∂Y (0, ω)) -
      (∫ γ : Path d, g (translate (γ t) (reduce ω)) ∂Y (0, ω))‖ₑ ∂Q.measure) ≤
      ENNReal.ofReal (Real.exp (lam ^ 2 * (Real.exp (2 * Λ₀) * Λ₀) * (T : ℝ))) ^ (1 / 2 : ℝ) *
        eLpNorm (fun ρ => (f - g) ρ) 2 (reducedLaw Q) := by
  refine (u3_supplied_force_endpoint_action_sub_bound_of_deps (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY t f g).trans ?_
  apply mul_le_mul' _ le_rfl
  apply ENNReal.rpow_le_rpow _ (by norm_num : (0 : ℝ) ≤ 1 / 2)
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  apply mul_le_mul_of_nonneg_left (show (t : ℝ) ≤ (T : ℝ) from ht)
  exact mul_nonneg (sq_nonneg lam)
    (mul_nonneg (Real.exp_pos _).le (zero_le_one.trans Q.ellipticity_parameter))

#print axioms u3_supplied_force_endpoint_action_sub_horizon_bound_of_deps

/-- The supplied signed path action satisfies the generator identity on every
fixed subinterval of a finite horizon. -/
theorem u3_signed_generator_pair_dynkin_interval_of_deps
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hunforced : UnforcedAt hd Q) (hpath : PathwiseAt Q)
    (lam : ℝ) (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ ω lam) 0 (Y (0, ω)))
    (a b : ℝ≥0) (hab : a ≤ b) (f g : Lp ℂ 2 (reducedLaw Q))
    (hfg : IsComplexGeneratorPair Q ⟨0, by omega⟩ (lam : ℂ) f g)
    (L : ℂ →L[ℝ] ℝ) :
    ∀ᵐ ω ∂Q.measure,
      (∫ γ : Path d, L (f (translate (γ b) (reduce ω))) ∂Y (0, ω)) -
        (∫ γ : Path d, L (f (translate (γ a) (reduce ω))) ∂Y (0, ω)) =
      ∫ t in Set.Ioc (a : ℝ) (b : ℝ), ∫ γ : Path d,
        L (g (translate (γ t.toNNReal) (reduce ω))) ∂Y (0, ω) := by
  let W : FieldPair d → ℝ := fun w => L (g w)
  have hWm : Measurable W := L.continuous.measurable.comp (Lp.stronglyMeasurable g).measurable
  have hW : MemLp W 2 (reducedLaw Q) := L.comp_memLp' (Lp.memLp g)
  filter_upwards [u3_signed_generator_pair_dynkin_of_deps (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY a f g hfg L,
    u3_signed_generator_pair_dynkin_of_deps (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY b f g hfg L,
    u3_supplied_force_occupation_fubini_of_deps (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY b W hWm hW, hY]
    with ω ha hb hfub hP
  let : IsProbabilityMeasure (Y (0, ω)) := hP.1
  have hi : IntegrableOn (fun t : ℝ => ∫ γ : Path d,
      W (translate (γ t.toNNReal) (reduce ω)) ∂Y (0, ω)) (Set.Ioc 0 (b : ℝ)) :=
    hfub.1.integral_prod_right
  have hab' : (a : ℝ) ≤ (b : ℝ) := hab
  have hsplit := setIntegral_union (Set.Ioc_disjoint_Ioc_of_le (a := (0 : ℝ))
    (b := (a : ℝ)) (c := (a : ℝ)) (d := (b : ℝ)) le_rfl) measurableSet_Ioc
    (hi.mono_set (Set.Ioc_subset_Ioc_right hab'))
    (hi.mono_set (Set.Ioc_subset_Ioc_left a.property))
  have hu : Set.Ioc (0 : ℝ) (a : ℝ) ∪ Set.Ioc (a : ℝ) (b : ℝ) =
      Set.Ioc (0 : ℝ) (b : ℝ) := Set.Ioc_union_Ioc_eq_Ioc a.property hab'
  rw [hu] at hsplit
  dsimp only [W] at hsplit
  linarith

#print axioms u3_signed_generator_pair_dynkin_interval_of_deps

/-- L²-close data have asymptotically equal supplied path actions even when
the evaluation time varies within a fixed finite horizon. -/
theorem u3_supplied_force_endpoint_action_sub_tendsto_of_deps
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hunforced : UnforcedAt hd Q) (hpath : PathwiseAt Q)
    (lam : ℝ) (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ ω lam) 0 (Y (0, ω)))
    (T : ℝ≥0) (t : ℕ → ℝ≥0) (ht : ∀ n, t n ≤ T)
    (f g : ℕ → Lp ℂ 2 (reducedLaw Q))
    (hlim : Filter.Tendsto (fun n => ‖f n - g n‖) Filter.atTop (𝓝 0)) :
    Filter.Tendsto (fun n => ∫⁻ ω,
      ‖(∫ γ : Path d, f n (translate (γ (t n)) (reduce ω)) ∂Y (0, ω)) -
       (∫ γ : Path d, g n (translate (γ (t n)) (reduce ω)) ∂Y (0, ω))‖ₑ ∂Q.measure)
      Filter.atTop (𝓝 0) := by
  let C : ℝ≥0∞ := ENNReal.ofReal (Real.exp
    (lam ^ 2 * (Real.exp (2 * Λ₀) * Λ₀) * (T : ℝ))) ^ (1 / 2 : ℝ)
  have hC : C ≠ ∞ :=
    ne_of_lt (ENNReal.rpow_lt_top_of_nonneg (by norm_num) ENNReal.ofReal_lt_top.ne)
  have hnorm : Filter.Tendsto
      (fun n => eLpNorm (fun w => (f n - g n) w) 2 (reducedLaw Q))
      Filter.atTop (𝓝 0) := by
    have h := ENNReal.tendsto_ofReal hlim
    simp only [ENNReal.ofReal_zero] at h
    apply h.congr
    intro n
    rw [← Lp.enorm_def, ← ofReal_norm]
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds _ (fun _ => bot_le)
    (fun n => u3_supplied_force_endpoint_action_sub_horizon_bound_of_deps
      (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY (t n) T (ht n) (f n) (g n))
  change Filter.Tendsto _ Filter.atTop (𝓝 (0 : ℝ≥0∞))
  simpa only [C, mul_zero] using ENNReal.Tendsto.const_mul hnorm (Or.inr hC)

#print axioms u3_supplied_force_endpoint_action_sub_tendsto_of_deps


/-- Every supplied signed endpoint action is an annealed L¹ observable. -/
theorem u3_supplied_force_endpoint_action_integrable_of_deps
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hunforced : UnforcedAt hd Q) (hpath : PathwiseAt Q)
    (lam : ℝ) (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ ω lam) 0 (Y (0, ω)))
    (t : ℝ≥0) (f : Lp ℂ 2 (reducedLaw Q)) :
    Integrable (fun ω => ∫ γ : Path d, f (translate (γ t) (reduce ω)) ∂Y (0, ω))
      Q.measure := by
  let : IsProbabilityMeasure Q.measure := Q.probability
  have hprob : ∀ᵐ ω ∂Q.measure, IsProbabilityMeasure (originLaw Y ω) :=
    hY.mono fun _ h => h.1
  obtain ⟨K, hK, hmarkov⟩ := Kernel.exists_ae_eq_isMarkovKernel hprob
    (IsProbabilityMeasure.ne_zero Q.measure)
  let : IsMarkovKernel K := hmarkov
  let E : FieldPair d × Path d → FieldPair d := fun z => translate (z.2 t) (reduce z.1)
  have hE : Measurable E := (Probability.continuous_translate.comp
    ((continuous_eval.comp (continuous_snd.prodMk continuous_const)).prodMk
      (Probability.continuous_reduce.comp continuous_fst))).measurable
  have hm : StronglyMeasurable (fun ω => ∫ γ : Path d, f (E (ω, γ)) ∂K ω) :=
    ((Lp.stronglyMeasurable f).comp_measurable hE).integral_kernel_prod_right'
  have hae : (fun ω => ∫ γ : Path d, f (E (ω, γ)) ∂K ω) =ᵐ[Q.measure]
      (fun ω => ∫ γ : Path d, f (translate (γ t) (reduce ω)) ∂Y (0, ω)) := by
    filter_upwards [hK] with ω hω
    change Y (0, ω) = K ω at hω
    rw [hω]
  refine ⟨hm.aestronglyMeasurable.congr hae, ?_⟩
  apply hasFiniteIntegral_iff_enorm.mpr
  apply lt_of_le_of_lt (u3_supplied_force_endpoint_annealed_lintegral_bound_of_deps
    (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY t f)
  exact ENNReal.mul_lt_top
    (ENNReal.rpow_lt_top_of_nonneg (by norm_num) ENNReal.ofReal_lt_top.ne)
    (Lp.eLpNorm_lt_top f)

#print axioms u3_supplied_force_endpoint_action_integrable_of_deps


/-- The supplied endpoint expectations form an L²-to-L¹ linear map. -/
def u3SuppliedForceEndpointActionLinearOfDeps
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hunforced : UnforcedAt hd Q) (hpath : PathwiseAt Q)
    (lam : ℝ) (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ ω lam) 0 (Y (0, ω)))
    (t : ℝ≥0) : Lp ℂ 2 (reducedLaw Q) →ₗ[ℂ] Lp ℂ 1 Q.measure where
  toFun f := (memLp_one_iff_integrable.mpr (u3_supplied_force_endpoint_action_integrable_of_deps
    (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY t f)).toLp
      (fun ω => ∫ γ : Path d, f (translate (γ t) (reduce ω)) ∂Y (0, ω))
  map_add' f g := by
    have he := u3_supplied_force_endpoint_ae_eq_of_deps (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY t
      (fun w => (f + g) w) (fun w => f w + g w)
      (Lp.stronglyMeasurable (f + g)).measurable
      ((Lp.stronglyMeasurable f).measurable.add (Lp.stronglyMeasurable g).measurable)
      (Lp.coeFn_add f g)
    apply Lp.ext
    filter_upwards [he,
      u3_supplied_force_endpoint_integrable_of_deps (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY t f,
      u3_supplied_force_endpoint_integrable_of_deps (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY t g,
      (memLp_one_iff_integrable.mpr (u3_supplied_force_endpoint_action_integrable_of_deps (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY t (f + g))).coeFn_toLp,
      (memLp_one_iff_integrable.mpr (u3_supplied_force_endpoint_action_integrable_of_deps (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY t f)).coeFn_toLp,
      (memLp_one_iff_integrable.mpr (u3_supplied_force_endpoint_action_integrable_of_deps (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY t g)).coeFn_toLp,
      Lp.coeFn_add
        ((memLp_one_iff_integrable.mpr (u3_supplied_force_endpoint_action_integrable_of_deps (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY t f)).toLp _)
        ((memLp_one_iff_integrable.mpr (u3_supplied_force_endpoint_action_integrable_of_deps (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY t g)).toLp _)]
      with ω he hf hg hfg hf' hg' hadd
    rw [hfg, hadd]
    simp only [Pi.add_apply]
    rw [hf', hg', integral_congr_ae he, integral_add hf hg]
  map_smul' c f := by
    have he := u3_supplied_force_endpoint_ae_eq_of_deps (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY t
      (fun w => (c • f) w) (fun w => c • f w)
      (Lp.stronglyMeasurable (c • f)).measurable
      ((Lp.stronglyMeasurable f).measurable.const_smul c) (Lp.coeFn_smul c f)
    apply Lp.ext
    filter_upwards [he,
      (memLp_one_iff_integrable.mpr (u3_supplied_force_endpoint_action_integrable_of_deps (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY t (c • f))).coeFn_toLp,
      (memLp_one_iff_integrable.mpr (u3_supplied_force_endpoint_action_integrable_of_deps (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY t f)).coeFn_toLp,
      Lp.coeFn_smul c
        ((memLp_one_iff_integrable.mpr (u3_supplied_force_endpoint_action_integrable_of_deps (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY t f)).toLp _)]
      with ω he hcf hf hsmul
    simp only [RingHom.id_apply]
    rw [hcf, hsmul]
    simp only [Pi.smul_apply]
    rw [hf, integral_congr_ae he, integral_smul]

#print axioms u3SuppliedForceEndpointActionLinearOfDeps


/-- The supplied endpoint action is a bounded linear map into annealed L¹. -/
def u3SuppliedForceEndpointActionContinuousOfDeps
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hunforced : UnforcedAt hd Q) (hpath : PathwiseAt Q)
    (lam : ℝ) (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ ω lam) 0 (Y (0, ω)))
    (t : ℝ≥0) : Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 1 Q.measure :=
  (u3SuppliedForceEndpointActionLinearOfDeps (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY t).mkContinuous
    ((ENNReal.ofReal (Real.exp (lam ^ 2 * (Real.exp (2 * Λ₀) * Λ₀) * (t : ℝ))) ^
      (1 / 2 : ℝ)).toReal) (by
      intro f
      let B : ℝ≥0∞ := ENNReal.ofReal (Real.exp
        (lam ^ 2 * (Real.exp (2 * Λ₀) * Λ₀) * (t : ℝ))) ^ (1 / 2 : ℝ)
      let A : FieldPair d → ℂ := fun ω =>
        ∫ γ : Path d, f (translate (γ t) (reduce ω)) ∂Y (0, ω)
      have hi : Integrable A Q.measure :=
        u3_supplied_force_endpoint_action_integrable_of_deps (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY t f
      have hb := u3_supplied_force_endpoint_annealed_lintegral_bound_of_deps
        (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY t f
      change (∫⁻ ω, ‖A ω‖ₑ ∂Q.measure) ≤ B * eLpNorm f 2 (reducedLaw Q) at hb
      have hfin : B * eLpNorm f 2 (reducedLaw Q) ≠ ∞ :=
        ENNReal.mul_ne_top
          (ENNReal.rpow_lt_top_of_nonneg (by norm_num) ENNReal.ofReal_lt_top.ne).ne
          (Lp.eLpNorm_ne_top f)
      have hr := ENNReal.toReal_mono hfin hb
      rw [← eLpNorm_one_eq_lintegral_enorm hi.1, ← Lp.norm_toLp A
        (memLp_one_iff_integrable.mpr hi), ENNReal.toReal_mul, ← Lp.norm_def] at hr
      exact hr)

#print axioms u3SuppliedForceEndpointActionContinuousOfDeps

/-- The supplied action operators are uniformly bounded on a finite horizon. -/
theorem u3_supplied_force_endpoint_action_opNorm_horizon_of_deps
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hunforced : UnforcedAt hd Q) (hpath : PathwiseAt Q)
    (lam : ℝ) (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ ω lam) 0 (Y (0, ω)))
    (t T : ℝ≥0) (ht : t ≤ T) :
    ‖u3SuppliedForceEndpointActionContinuousOfDeps (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY t‖ ≤
      (ENNReal.ofReal (Real.exp (lam ^ 2 * (Real.exp (2 * Λ₀) * Λ₀) * (T : ℝ))) ^
        (1 / 2 : ℝ)).toReal := by
  have hnorm : ‖u3SuppliedForceEndpointActionContinuousOfDeps
      (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY t‖ ≤
      (ENNReal.ofReal (Real.exp (lam ^ 2 * (Real.exp (2 * Λ₀) * Λ₀) * (t : ℝ))) ^
        (1 / 2 : ℝ)).toReal := by
    unfold u3SuppliedForceEndpointActionContinuousOfDeps
    exact LinearMap.mkContinuous_norm_le _ ENNReal.toReal_nonneg _
  refine hnorm.trans (ENNReal.toReal_mono ?_ ?_)
  · exact (ENNReal.rpow_lt_top_of_nonneg (by norm_num) ENNReal.ofReal_lt_top.ne).ne
  · apply ENNReal.rpow_le_rpow _ (by norm_num : (0 : ℝ) ≤ 1 / 2)
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    apply mul_le_mul_of_nonneg_left (show (t : ℝ) ≤ (T : ℝ) from ht)
    exact mul_nonneg (sq_nonneg lam)
      (mul_nonneg (Real.exp_pos _).le (zero_le_one.trans Q.ellipticity_parameter))

#print axioms u3_supplied_force_endpoint_action_opNorm_horizon_of_deps

/-- Averaging a bounded continuous observable over a probability law on
continuous paths is continuous in the observation time. -/
theorem u3_supplied_path_average_continuous
    {d : ℕ} (Y : QuenchedPathLaws d) (ω : FieldPair d)
    (hprob : IsProbabilityMeasure (Y (0, ω)))
    (g : BoundedContinuousFunction (FieldPair d) ℂ) :
    Continuous (fun t : ℝ≥0 => ∫ γ : Path d,
      g (translate (γ t) (reduce ω)) ∂Y (0, ω)) := by
  letI := hprob
  apply continuous_iff_continuousAt.mpr
  intro s
  have h : Filter.Tendsto (fun t : ℝ≥0 => ∫ γ : Path d,
      g (translate (γ t) (reduce ω)) ∂Y (0, ω)) (𝓝 s)
      (𝓝 (∫ γ : Path d, g (translate (γ s) (reduce ω)) ∂Y (0, ω))) :=
    tendsto_integral_filter_of_dominated_convergence (μ := Y (0, ω))
    (fun _ : Path d => ‖g‖)
    (Filter.Eventually.of_forall fun t : ℝ≥0 =>
      (g.continuous.comp (Probability.continuous_translate.comp
        ((continuous_eval_const t).prodMk (continuous_const (y := reduce ω))))).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun t : ℝ≥0 =>
      Filter.Eventually.of_forall fun γ : Path d => g.norm_coe_le_norm _)
    (integrable_const ‖g‖)
    (Filter.Eventually.of_forall fun γ : Path d =>
      (g.continuous.comp (Probability.continuous_translate.comp
        (γ.continuous.prodMk (continuous_const (y := reduce ω))))).tendsto s)
  exact h

#print axioms u3_supplied_path_average_continuous

/-- Bounded continuous observations have continuous annealed L¹ action orbits. -/
theorem u3_supplied_force_endpoint_action_continuous_bounded_of_deps
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hunforced : UnforcedAt hd Q) (hpath : PathwiseAt Q)
    (lam : ℝ) (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ ω lam) 0 (Y (0, ω)))
    (g : BoundedContinuousFunction (FieldPair d) ℂ)
    (F : Lp ℂ 2 (reducedLaw Q)) (hF : F =ᵐ[reducedLaw Q] fun ρ => g ρ) :
    Continuous (fun t : ℝ≥0 =>
      u3SuppliedForceEndpointActionContinuousOfDeps (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY t F) := by
  letI : IsProbabilityMeasure Q.measure := Q.probability
  let A := fun t : ℝ≥0 =>
    u3SuppliedForceEndpointActionContinuousOfDeps (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY t F
  let M := fun (t : ℝ≥0) (ω : FieldPair d) =>
    ∫ γ : Path d, g (translate (γ t) (reduce ω)) ∂Y (0, ω)
  have he (t : ℝ≥0) : A t =ᵐ[Q.measure] M t := by
    have heq := u3_supplied_force_endpoint_ae_eq_of_deps (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY t
      (fun ρ => F ρ) (fun ρ => g ρ) (Lp.stronglyMeasurable F).measurable
      g.continuous.measurable hF
    have hr := (memLp_one_iff_integrable.mpr
      (u3_supplied_force_endpoint_action_integrable_of_deps
        (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY t F)).coeFn_toLp
    change A t =ᵐ[Q.measure] _ at hr
    filter_upwards [hr, heq] with ω hω hωeq
    exact hω.trans (integral_congr_ae hωeq)
  have hi (t : ℝ≥0) : Integrable (M t) Q.measure :=
    (MeasureTheory.L1.integrable_coeFn (A t)).congr (he t)
  apply continuous_iff_continuousAt.mpr
  intro s
  have hb (ω : FieldPair d) (hω : IsProbabilityMeasure (Y (0, ω))) (t : ℝ≥0) :
      ‖M t ω‖ ≤ ‖g‖ := by
    let : IsProbabilityMeasure (Y (0, ω)) := hω
    simpa only [measureReal_def, measure_univ, ENNReal.toReal_one, mul_one] using
      (norm_integral_le_of_norm_le_const (μ := Y (0, ω))
        (Filter.Eventually.of_forall fun γ : Path d => g.norm_coe_le_norm _))
  have hlim : Filter.Tendsto (fun t : ℝ≥0 => ∫ ω,
      ‖M t ω - M s ω‖ ∂Q.measure) (𝓝 s) (𝓝 0) := by
    have ht := tendsto_integral_filter_of_dominated_convergence (μ := Q.measure)
      (fun _ : FieldPair d => 2 * ‖g‖)
      (Filter.Eventually.of_forall fun t : ℝ≥0 => ((hi t).sub (hi s)).norm.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun t : ℝ≥0 => by
        filter_upwards [hY] with ω hω
        simpa only [Pi.sub_apply, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using
          (norm_sub_le _ _).trans ((add_le_add (hb ω hω.1 t) (hb ω hω.1 s)).trans_eq
            (two_mul ‖g‖).symm))
      (integrable_const (2 * ‖g‖))
      (hY.mono fun ω hω => by
        have hc := ((u3_supplied_path_average_continuous Y ω hω.1 g).sub (continuous_const (y := M s ω))).norm
        have h := hc.tendsto s
        simpa only [M, Pi.sub_apply, sub_self, norm_zero] using h)
    simpa only [M, Pi.sub_apply, sub_self, norm_zero, integral_zero] using ht
  rw [ContinuousAt, tendsto_iff_dist_tendsto_zero]
  simp only [dist_eq_norm]
  apply hlim.congr
  intro t
  symm
  change ‖A t - A s‖ = ∫ ω, ‖M t ω - M s ω‖ ∂Q.measure
  rw [MeasureTheory.L1.norm_sub_eq_lintegral]
  change (∫⁻ ω, ‖((fun ω => A t ω - A s ω) ω)‖ₑ ∂Q.measure).toReal = _
  have hm : AEStronglyMeasurable (fun ω => A t ω - A s ω) Q.measure := by
    apply ((hi t).sub (hi s)).aestronglyMeasurable.congr
    filter_upwards [he t, he s] with ω ht hs
    change M t ω - M s ω = A t ω - A s ω
    rw [ht, hs]
  rw [← integral_norm_eq_lintegral_enorm hm]
  apply integral_congr_ae
  filter_upwards [he t, he s] with ω ht hs
  simp only [Pi.sub_apply, ht, hs]

#print axioms u3_supplied_force_endpoint_action_continuous_bounded_of_deps


/-- Supplied signed endpoint actions are continuous in time for all L² data. -/
theorem u3_supplied_force_endpoint_action_orbit_continuous_of_deps
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hunforced : UnforcedAt hd Q) (hpath : PathwiseAt Q)
    (lam : ℝ) (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ ω lam) 0 (Y (0, ω)))
    (F : Lp ℂ 2 (reducedLaw Q)) :
    Continuous (fun t : ℝ≥0 =>
      u3SuppliedForceEndpointActionContinuousOfDeps (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY t F) := by
  let _ : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  let _ : PolishSpace (CoefficientField d) := Localization.coefficientField_polish d
  let _ : PolishSpace (FieldPair d) := inferInstance
  let A := fun t : ℝ≥0 =>
    u3SuppliedForceEndpointActionContinuousOfDeps (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY t
  let D : Set (Lp ℂ 2 (reducedLaw Q)) := Set.range
    (BoundedContinuousFunction.toLp 2 (reducedLaw Q) ℂ)
  have hD : Dense D := BoundedContinuousFunction.toLp_denseRange ℂ (reducedLaw Q) ℂ (by norm_num)
  have hcont : ∀ G ∈ D, Continuous (fun t => A t G) := by
    rintro G ⟨g, rfl⟩
    exact u3_supplied_force_endpoint_action_continuous_bounded_of_deps
      (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY g _
      (BoundedContinuousFunction.coeFn_toLp 2 (reducedLaw Q) ℂ g)
  apply continuous_iff_continuousAt.mpr
  intro s
  let C : ℝ := (ENNReal.ofReal (Real.exp
    (lam ^ 2 * (Real.exp (2 * Λ₀) * Λ₀) * ((s + 1 : ℝ≥0) : ℝ))) ^
      (1 / 2 : ℝ)).toReal
  let B : ℝ := max 1 C
  have hB : 0 < B := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hs : ‖A s‖ ≤ B := by
    exact (u3_supplied_force_endpoint_action_opNorm_horizon_of_deps
      (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY s (s + 1) (le_add_of_nonneg_right (by positivity))).trans
        (le_max_right _ _)
  have hlocal : ∀ᶠ t in 𝓝 s, ‖A t‖ ≤ B := by
    filter_upwards [Iio_mem_nhds (show s < s + 1 by simp)] with t ht
    exact (u3_supplied_force_endpoint_action_opNorm_horizon_of_deps
      (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY t (s + 1) ht.le).trans (le_max_right _ _)
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨G, hG, hFG⟩ := hD.exists_dist_lt F (div_pos hε (by positivity : 0 < 3 * B))
  have hsmall : B * dist F G < ε / 3 := by
    have h := (lt_div_iff₀ (by positivity : 0 < 3 * B)).mp hFG
    nlinarith
  have hg := Metric.tendsto_nhds.mp ((hcont G hG).continuousAt (x := s)) (ε / 3) (by positivity)
  filter_upwards [hlocal, hg] with t ht htg
  have hfirst : dist (A t F) (A t G) ≤ B * dist F G := by
    rw [dist_eq_norm, dist_eq_norm, ← map_sub]
    exact ((A t).le_opNorm _).trans (mul_le_mul_of_nonneg_right ht (norm_nonneg _))
  have hlast : dist (A s G) (A s F) ≤ B * dist F G := by
    rw [dist_comm, dist_eq_norm, dist_eq_norm, ← map_sub]
    exact ((A s).le_opNorm _).trans (mul_le_mul_of_nonneg_right hs (norm_nonneg _))
  calc
    dist (A t F) (A s F) ≤ dist (A t F) (A t G) +
        (dist (A t G) (A s G) + dist (A s G) (A s F)) :=
      (dist_triangle (A t F) (A t G) (A s F)).trans
        (add_le_add le_rfl (dist_triangle (A t G) (A s G) (A s F)))
    _ < ε := by linarith

#print axioms u3_supplied_force_endpoint_action_orbit_continuous_of_deps


/-- The supplied action can be applied to a continuously varying L² input. -/
theorem u3_supplied_force_endpoint_action_continuous_varying_of_deps
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hunforced : UnforcedAt hd Q) (hpath : PathwiseAt Q)
    (lam : ℝ) (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ ω lam) 0 (Y (0, ω)))
    (F : ℝ≥0 → Lp ℂ 2 (reducedLaw Q)) (hF : Continuous F) :
    Continuous (fun t : ℝ≥0 =>
      u3SuppliedForceEndpointActionContinuousOfDeps (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY t (F t)) := by
  let A := fun t : ℝ≥0 =>
    u3SuppliedForceEndpointActionContinuousOfDeps (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY t
  apply continuous_iff_continuousAt.mpr
  intro s
  let C : ℝ := (ENNReal.ofReal (Real.exp
    (lam ^ 2 * (Real.exp (2 * Λ₀) * Λ₀) * ((s + 1 : ℝ≥0) : ℝ))) ^
      (1 / 2 : ℝ)).toReal
  let B : ℝ := max 1 C
  have hB : 0 < B := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hlocal : ∀ᶠ t in 𝓝 s, ‖A t‖ ≤ B := by
    filter_upwards [Iio_mem_nhds (show s < s + 1 by simp)] with t ht
    exact (u3_supplied_force_endpoint_action_opNorm_horizon_of_deps
      (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY t (s + 1) ht.le).trans (le_max_right _ _)
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hF' := Metric.tendsto_nhds.mp (hF.continuousAt (x := s))
    (ε / (2 * B)) (by positivity)
  have hA' := Metric.tendsto_nhds.mp
    ((u3_supplied_force_endpoint_action_orbit_continuous_of_deps
      (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY (F s)).continuousAt (x := s))
    (ε / 2) (by positivity)
  filter_upwards [hlocal, hF', hA'] with t ht hFt hAt
  have hsmall : B * dist (F t) (F s) < ε / 2 := by
    have h := (lt_div_iff₀ (by positivity : 0 < 2 * B)).mp hFt
    nlinarith
  have hfirst : dist (A t (F t)) (A t (F s)) ≤ B * dist (F t) (F s) := by
    rw [dist_eq_norm, dist_eq_norm, ← map_sub]
    exact ((A t).le_opNorm _).trans (mul_le_mul_of_nonneg_right ht (norm_nonneg _))
  exact (dist_triangle (A t (F t)) (A t (F s)) (A s (F s))).trans_lt (by linarith)

#print axioms u3_supplied_force_endpoint_action_continuous_varying_of_deps

/-- The L¹ action starts from the pullback of the reduced-law observable. -/
theorem u3_supplied_force_endpoint_action_zero_of_deps
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hunforced : UnforcedAt hd Q) (hpath : PathwiseAt Q)
    (lam : ℝ) (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ ω lam) 0 (Y (0, ω)))
    (f : Lp ℂ 2 (reducedLaw Q)) :
    (u3SuppliedForceEndpointActionContinuousOfDeps (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY 0 f :
      FieldPair d → ℂ) =ᵐ[Q.measure] fun ω => f (reduce ω) := by
  have hrep := (memLp_one_iff_integrable.mpr
    (u3_supplied_force_endpoint_action_integrable_of_deps (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY 0 f)).coeFn_toLp
  change (u3SuppliedForceEndpointActionContinuousOfDeps (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY 0 f :
    FieldPair d → ℂ) =ᵐ[Q.measure] _ at hrep
  filter_upwards [hrep, c27_real_force_quenched_action_zero_time hd Q lam Y hY f] with ω hr hzero
  rw [hr, ← hzero.2, forcedComplexEvolution_zero, ContinuousLinearMap.id_apply]

#print axioms u3_supplied_force_endpoint_action_zero_of_deps

/-- Complex L² observables admit the same quenched occupation Fubini
interchange as their real-valued norms. -/
theorem u3_supplied_force_complex_occupation_fubini_of_deps
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hunforced : UnforcedAt hd Q) (hpath : PathwiseAt Q)
    (lam : ℝ) (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ ω lam) 0 (Y (0, ω)))
    (T : ℝ≥0) (f : Lp ℂ 2 (reducedLaw Q)) :
    ∀ᵐ ω ∂Q.measure,
      Integrable (fun p : Path d × ℝ => f (translate (p.1 p.2.toNNReal) (reduce ω)))
        ((Y (0, ω)).prod (volume.restrict (Set.Ioc 0 (T : ℝ)))) ∧
      (∫ γ : Path d, (∫ t in Set.Ioc 0 (T : ℝ),
        f (translate (γ t.toNNReal) (reduce ω))) ∂Y (0, ω)) =
      ∫ t in Set.Ioc 0 (T : ℝ), ∫ γ : Path d,
        f (translate (γ t.toNNReal) (reduce ω)) ∂Y (0, ω) := by
  have hnorm := u3_supplied_force_occupation_fubini_of_deps (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY T
    (fun w => ‖f w‖) (Lp.stronglyMeasurable f).measurable.norm (Lp.memLp f).norm
  filter_upwards [hnorm, hY] with ω hnorm hprob
  let : IsProbabilityMeasure (Y (0, ω)) := hprob.1
  have hm : Measurable (fun p : Path d × ℝ =>
      f (translate (p.1 p.2.toNNReal) (reduce ω))) := by
    apply (Lp.stronglyMeasurable f).measurable.comp
    exact (Probability.continuous_translate.comp
      ((continuous_eval.comp (continuous_fst.prodMk
        (continuous_real_toNNReal.comp continuous_snd))).prodMk continuous_const)).measurable
  have hi : Integrable (fun p : Path d × ℝ =>
      f (translate (p.1 p.2.toNNReal) (reduce ω)))
      ((Y (0, ω)).prod (volume.restrict (Set.Ioc 0 (T : ℝ)))) := by
    apply hnorm.1.mono' hm.aestronglyMeasurable
    filter_upwards [] with p
    simp
  exact ⟨hi, (integral_prod _ hi).symm.trans (integral_prod_symm _ hi)⟩

#print axioms u3_supplied_force_complex_occupation_fubini_of_deps


/-- The signed supplied path action satisfies Dynkin's identity for complex
observables on every fixed interval. -/
theorem u3_signed_generator_pair_complex_dynkin_interval_of_deps
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hunforced : UnforcedAt hd Q) (hpath : PathwiseAt Q)
    (lam : ℝ) (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ ω lam) 0 (Y (0, ω)))
    (a b : ℝ≥0) (hab : a ≤ b) (f g : Lp ℂ 2 (reducedLaw Q))
    (hfg : IsComplexGeneratorPair Q ⟨0, by omega⟩ (lam : ℂ) f g) :
    ∀ᵐ ω ∂Q.measure,
      (∫ γ : Path d, f (translate (γ b) (reduce ω)) ∂Y (0, ω)) -
        (∫ γ : Path d, f (translate (γ a) (reduce ω)) ∂Y (0, ω)) =
      ∫ t in Set.Ioc (a : ℝ) (b : ℝ), ∫ γ : Path d,
        g (translate (γ t.toNNReal) (reduce ω)) ∂Y (0, ω) := by
  filter_upwards [u3_signed_generator_pair_dynkin_interval_of_deps (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY a b hab f g hfg Complex.reCLM,
    u3_signed_generator_pair_dynkin_interval_of_deps (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY a b hab f g hfg Complex.imCLM,
    u3_supplied_force_endpoint_integrable_of_deps (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY a f,
    u3_supplied_force_endpoint_integrable_of_deps (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY b f,
    u3_supplied_force_complex_occupation_fubini_of_deps (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY b g, hY]
    with ω hre him ha hb hocc hprob
  let : IsProbabilityMeasure (Y (0, ω)) := hprob.1
  have hi := hocc.1.mono_measure (Measure.prod_mono le_rfl
    (Measure.restrict_mono_set volume (Set.Ioc_subset_Ioc_left a.property)))
  have ht := hi.integral_prod_right
  have hae := hi.prod_left_ae
  have ht' : Integrable (fun t : ℝ => ∫ γ : Path d,
      g (translate (γ t.toNNReal) (reduce ω)) ∂Y (0, ω))
      (volume.restrict (Set.Ioc (a : ℝ) (b : ℝ))) := by simpa using ht
  have hri : (∫ t in Set.Ioc (a : ℝ) (b : ℝ), ∫ γ : Path d,
      (g (translate (γ t.toNNReal) (reduce ω))).re ∂Y (0, ω)) =
      (∫ t in Set.Ioc (a : ℝ) (b : ℝ), ∫ γ : Path d,
        g (translate (γ t.toNNReal) (reduce ω)) ∂Y (0, ω)).re := by
    calc
      _ = ∫ t in Set.Ioc (a : ℝ) (b : ℝ),
          (∫ γ : Path d, g (translate (γ t.toNNReal) (reduce ω)) ∂Y (0, ω)).re := by
        apply integral_congr_ae
        filter_upwards [hae] with t ht
        simpa only [Complex.reCLM_apply] using Complex.reCLM.integral_comp_comm ht
      _ = _ := by simpa only [Complex.reCLM_apply] using Complex.reCLM.integral_comp_comm ht'
  have hii : (∫ t in Set.Ioc (a : ℝ) (b : ℝ), ∫ γ : Path d,
      (g (translate (γ t.toNNReal) (reduce ω))).im ∂Y (0, ω)) =
      (∫ t in Set.Ioc (a : ℝ) (b : ℝ), ∫ γ : Path d,
        g (translate (γ t.toNNReal) (reduce ω)) ∂Y (0, ω)).im := by
    calc
      _ = ∫ t in Set.Ioc (a : ℝ) (b : ℝ),
          (∫ γ : Path d, g (translate (γ t.toNNReal) (reduce ω)) ∂Y (0, ω)).im := by
        apply integral_congr_ae
        filter_upwards [hae] with t ht
        simpa only [Complex.imCLM_apply] using Complex.imCLM.integral_comp_comm ht
      _ = _ := by simpa only [Complex.imCLM_apply] using Complex.imCLM.integral_comp_comm ht'
  have ha_re := Complex.reCLM.integral_comp_comm ha
  have hb_re := Complex.reCLM.integral_comp_comm hb
  have ha_im := Complex.imCLM.integral_comp_comm ha
  have hb_im := Complex.imCLM.integral_comp_comm hb
  simp only [Complex.reCLM_apply] at hre ha_re hb_re
  simp only [Complex.imCLM_apply] at him ha_im hb_im
  rw [hb_re, ha_re, hri] at hre
  rw [hb_im, ha_im, hii] at him
  apply Complex.ext
  · simpa only [Complex.sub_re] using hre
  · simpa only [Complex.sub_im] using him

#print axioms u3_signed_generator_pair_complex_dynkin_interval_of_deps


/-- A Markov-kernel version of the same supplied law has jointly integrable
complex L² occupations on every finite horizon. -/
theorem u3_supplied_force_complex_joint_integrable_of_deps
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hunforced : UnforcedAt hd Q) (hpath : PathwiseAt Q)
    (lam : ℝ) (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ ω lam) 0 (Y (0, ω)))
    (T : ℝ≥0) (f : Lp ℂ 2 (reducedLaw Q)) :
    ∃ K : Kernel (FieldPair d) (Path d), IsMarkovKernel K ∧
      (∀ᵐ ω ∂Q.measure, Y (0, ω) = K ω) ∧
      Integrable (fun p : ℝ × (FieldPair d × Path d) =>
        f (translate (p.2.2 p.1.toNNReal) (reduce p.2.1)))
        ((volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ))).prod (Q.measure ⊗ₘ K)) := by
  obtain ⟨K, hK, heq, hi⟩ := u3_supplied_force_finite_time_joint_integrable_of_deps
    (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY T (fun w => ‖f w‖)
    (Lp.stronglyMeasurable f).measurable.norm (Lp.memLp f).norm
  refine ⟨K, hK, heq, ?_⟩
  let E : ℝ × (FieldPair d × Path d) → FieldPair d := fun p =>
    translate (p.2.2 p.1.toNNReal) (reduce p.2.1)
  have hE : Measurable E := by
    exact (Probability.continuous_translate.comp
      ((continuous_eval.comp ((continuous_snd.comp continuous_snd).prodMk
        (continuous_real_toNNReal.comp continuous_fst))).prodMk
        (Probability.continuous_reduce.comp (continuous_fst.comp continuous_snd)))).measurable
  apply hi.mono' ((Lp.stronglyMeasurable f).measurable.comp hE).aestronglyMeasurable
  filter_upwards [] with p
  simp [E]

#print axioms u3_supplied_force_complex_joint_integrable_of_deps


/-- The L¹-valued supplied action has a Bochner-integrable orbit on every
finite time interval. -/
theorem u3_supplied_force_endpoint_action_orbit_integrable_of_deps
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hunforced : UnforcedAt hd Q) (hpath : PathwiseAt Q)
    (lam : ℝ) (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ ω lam) 0 (Y (0, ω)))
    (a b : ℝ) (f : Lp ℂ 2 (reducedLaw Q)) :
    IntegrableOn (fun t : ℝ =>
      u3SuppliedForceEndpointActionContinuousOfDeps (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY t.toNNReal f)
      (Set.Ioc a b) := by
  exact ((u3_supplied_force_endpoint_action_orbit_continuous_of_deps
    (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY f).comp continuous_real_toNNReal).integrableOn_Ioc

#print axioms u3_supplied_force_endpoint_action_orbit_integrable_of_deps


/-- Set integration commutes with the finite-time Bochner integral of the
supplied L¹-valued action. -/
theorem u3_supplied_force_endpoint_action_setIntegral_time_of_deps
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hunforced : UnforcedAt hd Q) (hpath : PathwiseAt Q)
    (lam : ℝ) (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ ω lam) 0 (Y (0, ω)))
    (a b : ℝ) (f : Lp ℂ 2 (reducedLaw Q)) (s : Set (FieldPair d)) :
    (∫ ω in s, (∫ t in Set.Ioc a b,
      u3SuppliedForceEndpointActionContinuousOfDeps (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY t.toNNReal f) ω ∂Q.measure) =
      ∫ t in Set.Ioc a b, ∫ ω in s,
        u3SuppliedForceEndpointActionContinuousOfDeps (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY t.toNNReal f ω ∂Q.measure := by
  let J : Lp ℂ 1 Q.measure →L[ℝ] ℂ :=
    (L1.integralCLM (α := FieldPair d) (E := ℂ) (μ := Q.measure.restrict s)).comp
      (LpToLpRestrictCLM (FieldPair d) ℂ ℝ Q.measure 1 s)
  have hJ (v : Lp ℂ 1 Q.measure) : J v = ∫ ω in s, v ω ∂Q.measure := by
    change L1.integralCLM (LpToLpRestrictCLM (FieldPair d) ℂ ℝ Q.measure 1 s v) = _
    rw [← L1.integral_eq, L1.integral_eq_integral]
    exact integral_congr_ae (LpToLpRestrictCLM_coeFn ℝ s v)
  have hi := u3_supplied_force_endpoint_action_orbit_integrable_of_deps
    (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY a b f
  calc
    _ = J (∫ t in Set.Ioc a b,
        u3SuppliedForceEndpointActionContinuousOfDeps (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY t.toNNReal f) := (hJ _).symm
    _ = ∫ t in Set.Ioc a b, J
        (u3SuppliedForceEndpointActionContinuousOfDeps (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY t.toNNReal f) :=
      (J.integral_comp_comm hi).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with t
      exact hJ _

#print axioms u3_supplied_force_endpoint_action_setIntegral_time_of_deps

/-- A jointly measurable version of the supplied endpoint action exists for all times. -/
theorem u3_supplied_force_endpoint_jointly_measurable_of_deps
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
    u3_supplied_force_complex_joint_integrable_of_deps (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY T g
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

#print axioms u3_supplied_force_endpoint_jointly_measurable_of_deps


/-- A jointly measurable endpoint version is integrable in time and environment. -/
theorem u3_supplied_force_endpoint_jointly_integrable_of_deps
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
  obtain ⟨H, hm, hH⟩ := u3_supplied_force_endpoint_jointly_measurable_of_deps
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
    u3_supplied_force_endpoint_action_orbit_integrable_of_deps (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY 0 T g
  refine ⟨H, ?_, hH⟩
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  refine ⟨Filter.Eventually.of_forall hsec, ?_⟩
  simpa only [hnorm] using hA.norm

#print axioms u3_supplied_force_endpoint_jointly_integrable_of_deps


/-- The time integral of the L¹ action has the expected quenched representative. -/
theorem u3_supplied_force_action_integral_ae_of_deps
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
  obtain ⟨H, hH, hrep⟩ := u3_supplied_force_endpoint_jointly_integrable_of_deps
    (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY T g
  let μ := volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ))
  let A : ℝ → Lp ℂ 1 Q.measure := fun t =>
    u3SuppliedForceEndpointActionContinuousOfDeps
      (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY t.toNNReal g
  let B : FieldPair d → ℂ := fun ω => ∫ t, H (t, ω) ∂μ
  have hA : Integrable A μ :=
    u3_supplied_force_endpoint_action_orbit_integrable_of_deps (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY 0 T g
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

#print axioms u3_supplied_force_action_integral_ae_of_deps


/-- Integrated Dynkin identity in the annealed L¹ space. -/
theorem u3_supplied_force_dynkin_L1_of_deps
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
  have h0 : (fun ω => A0 ω) =ᵐ[Q.measure] fun ω =>
      ∫ γ : Path d, f (translate (γ 0) (reduce ω)) ∂Y (0,ω) := by
    exact (memLp_one_iff_integrable.mpr
      (u3_supplied_force_endpoint_action_integrable_of_deps
        (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY 0 f)).coeFn_toLp
  apply Lp.ext
  filter_upwards [Lp.coeFn_sub AT A0, hT, h0,
    u3_supplied_force_action_integral_ae_of_deps (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY T g,
    u3_signed_generator_pair_complex_dynkin_interval_of_deps (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY 0 T (by exact bot_le) f g hfg]
    with ω hsub hTω h0ω hiω hDω
  change (AT - A0) ω = _
  rw [hsub, Pi.sub_apply, hTω, h0ω, hiω]
  exact hDω

#print axioms u3_supplied_force_dynkin_L1_of_deps


/-- The annealed L¹ Dynkin identity holds on any nonnegative interval. -/
theorem u3_supplied_force_dynkin_L1_interval_of_deps
    {d : ℕ} (hd : 2 ≤ d) {Λ r : ℝ} (Q : EnvironmentLaw d Λ r)
    (hunforced : UnforcedAt hd Q) (hpath : PathwiseAt Q)
    (lam : ℝ) (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure, SolvesMartingaleProblem
      (reducedGenerator ⟨0, by omega⟩ ω lam) 0 (Y (0,ω)))
    (a b : ℝ≥0) (hab : a ≤ b) (f g : Lp ℂ 2 (reducedLaw Q))
    (hfg : IsComplexGeneratorPair Q ⟨0, by omega⟩ (lam : ℂ) f g) :
    u3SuppliedForceEndpointActionContinuousOfDeps (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY b f -
      u3SuppliedForceEndpointActionContinuousOfDeps (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY a f =
    ∫ t : ℝ in Set.Ioc (a : ℝ) (b : ℝ),
      u3SuppliedForceEndpointActionContinuousOfDeps (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY t.toNNReal g := by
  let u : ℝ → Lp ℂ 1 Q.measure := fun t =>
    u3SuppliedForceEndpointActionContinuousOfDeps (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY t.toNNReal g
  have hu : Continuous u :=
    (u3_supplied_force_endpoint_action_orbit_continuous_of_deps
      (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY g).comp continuous_real_toNNReal
  have ha := u3_supplied_force_dynkin_L1_of_deps (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY a f g hfg
  have hb := u3_supplied_force_dynkin_L1_of_deps (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY b f g hfg
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (hu.intervalIntegrable (μ := volume) 0 a) (hu.intervalIntegrable (μ := volume) a b)
  have hai : (∫ t in (0 : ℝ)..(a : ℝ), u t) = ∫ t in Set.Ioc (0 : ℝ) (a : ℝ), u t :=
    intervalIntegral.integral_of_le a.property
  have habi : (∫ t in (a : ℝ)..(b : ℝ), u t) = ∫ t in Set.Ioc (a : ℝ) (b : ℝ), u t :=
    intervalIntegral.integral_of_le (by exact_mod_cast hab)
  have hbi : (∫ t in (0 : ℝ)..(b : ℝ), u t) = ∫ t in Set.Ioc (0 : ℝ) (b : ℝ), u t :=
    intervalIntegral.integral_of_le b.property
  rw [hai, habi, hbi] at hadd
  change _ + (∫ t in Set.Ioc (a : ℝ) (b : ℝ), u t) = _ at hadd
  change _ - _ = ∫ t in Set.Ioc (0 : ℝ) (a : ℝ), u t at ha
  change _ - _ = ∫ t in Set.Ioc (0 : ℝ) (b : ℝ), u t at hb
  rw [← ha, ← hb] at hadd
  have he := eq_sub_of_add_eq' hadd
  rw [he]
  abel

#print axioms u3_supplied_force_dynkin_L1_interval_of_deps

/-- Recover a complex integral from its real and imaginary projections. -/
theorem u3_complex_integral_eq_of_real_projections
    {α : Type*} [MeasurableSpace α] (μ : Measure α) (f : α → ℂ)
    (hf : Integrable f μ) (z : ℂ)
    (hre : ∫ a, (f a).re ∂μ = z.re)
    (him : ∫ a, (f a).im ∂μ = z.im) : (∫ a, f a ∂μ) = z := by
  apply Complex.ext
  · exact (integral_re hf).symm.trans hre
  · exact (integral_im hf).symm.trans him

#print axioms u3_complex_integral_eq_of_real_projections


/-- The supplied-law L¹ orbit has the generator orbit as its right derivative. -/
theorem u3_supplied_force_endpoint_L1_hasDerivWithinAt
    {d : ℕ} (hd : 2 ≤ d) {Λ r : ℝ} (Q : EnvironmentLaw d Λ r)
    (hunforced : UnforcedAt hd Q) (hpath : PathwiseAt Q)
    (lam : ℝ) (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure, SolvesMartingaleProblem
      (reducedGenerator ⟨0, by omega⟩ ω lam) 0 (Y (0,ω)))
    (f g : Lp ℂ 2 (reducedLaw Q))
    (hfg : IsComplexGeneratorPair Q ⟨0, by omega⟩ (lam : ℂ) f g)
    (t : ℝ) (ht : 0 ≤ t) :
    HasDerivWithinAt
      (fun s : ℝ => u3SuppliedForceEndpointActionContinuousOfDeps
        (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY s.toNNReal f)
      (u3SuppliedForceEndpointActionContinuousOfDeps
        (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY t.toNNReal g) (Set.Ici 0) t := by
  let u : ℝ → Lp ℂ 1 Q.measure := fun s =>
    u3SuppliedForceEndpointActionContinuousOfDeps (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY s.toNNReal g
  have hu : Continuous u :=
    (u3_supplied_force_endpoint_action_orbit_continuous_of_deps
      (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY g).comp continuous_real_toNNReal
  have hd' := (intervalIntegral.integral_hasDerivAt_right (hu.intervalIntegrable 0 t)
    hu.stronglyMeasurable.stronglyMeasurableAtFilter hu.continuousAt).add_const
      (u3SuppliedForceEndpointActionContinuousOfDeps (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY 0 f)
  apply hd'.hasDerivWithinAt.congr_of_mem _ ht
  intro s hs
  have he := u3_supplied_force_dynkin_L1_of_deps (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY s.toNNReal f g hfg
  rw [Real.coe_toNNReal s hs] at he
  have hi : (∫ x in (0 : ℝ)..s, u x) = ∫ x in Set.Ioc (0 : ℝ) s, u x :=
    intervalIntegral.integral_of_le hs
  change _ - _ = ∫ x in Set.Ioc (0 : ℝ) s, u x at he
  rw [← hi] at he
  exact sub_eq_iff_eq_add.mp he

#print axioms u3_supplied_force_endpoint_L1_hasDerivWithinAt

end EinsteinFull
