import EinsteinFull.Calculus.SbxAGMPUnforcedInvarianceR04
import EinsteinFull.Calculus.SbxS3JointReducedKernelR01
import EinsteinFull.Blueprint.G1.Proofs.SbxS4RemainderMoment
import EinsteinFull.Calculus.U3RealForceQuenchedAction

/-! Force-change primitives for the endpoint action of the supplied GMP kernel. -/

open EinsteinRelation MeasureTheory ProbabilityTheory
open EinsteinRelation.External.GantertSection7Support
open scoped NNReal ENNReal

noncomputable section
namespace EinsteinFull

/-- The actual GMP kernels obey the finite-horizon force-change equation. -/
theorem s9_gmp_force_finite_horizon
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (mu : ℝ) (h0 : 0 ≤ mu) (h1 : mu ≤ 1)
    (P₀ P : QuenchedPathLaws d)
    (hP₀ : IsGMPReducedKernel hd Q.ellipticity_parameter Q 0 (by norm_num) (by norm_num) P₀)
    (hP : IsGMPReducedKernel hd Q.ellipticity_parameter Q mu h0 h1 P)
    (t : ℝ≥0) :
    ∀ᵐ ω ∂Q.measure, ∀ A : Set (Path d), MeasurableSet[(pathFiltration d) t] A →
      P (0, ω) A = ∫⁻ γ in A, ENNReal.ofReal (Real.exp
        (mu * ((γ t) (firstCoordinateIndex hd) - (0 : Vec d) (firstCoordinateIndex hd)) -
          ∫ u in Set.Ioc (0 : ℝ) (t : ℝ),
            (mu * forcedDrift (reducedCoefficient ω) (firstCoordinateIndex hd) 0
              (γ u.toNNReal) (firstCoordinateIndex hd) +
              (mu ^ 2 / 2) * reducedCoefficient ω (γ u.toNNReal)
                (firstCoordinateIndex hd) (firstCoordinateIndex hd)))) ∂P₀ (0, ω) := by
  have hΛ : 0 < Λ₀ := lt_of_lt_of_le zero_lt_one Q.ellipticity_parameter
  filter_upwards [Q.regular, s5_gmp_textbook_at_every_start hd Q 0 (by norm_num)
    (by norm_num) P₀ hP₀, s5_gmp_textbook_at_every_start hd Q mu h0 h1 P hP]
    with ω hω hzero hforce
  exact u3_reduced_force_finite_horizon_law (by omega) hΛ hω (firstCoordinateIndex hd)
    (hzero 0) mu t (hforce 0)

/-- The force-change density is square-integrable under the actual unforced law. -/
theorem s9_gmp_force_density_memLp_two
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (mu : ℝ) (P₀ : QuenchedPathLaws d)
    (hP₀ : IsGMPReducedKernel hd Q.ellipticity_parameter Q 0 (by norm_num) (by norm_num) P₀)
    (t : ℝ≥0) :
    ∀ᵐ ω ∂Q.measure, MemLp (fun γ : Path d => Real.exp
      (mu * ((γ t) (firstCoordinateIndex hd) - (0 : Vec d) (firstCoordinateIndex hd)) -
        ∫ u in Set.Ioc (0 : ℝ) (t : ℝ),
          (mu * forcedDrift (reducedCoefficient ω) (firstCoordinateIndex hd) 0
            (γ u.toNNReal) (firstCoordinateIndex hd) +
            (mu ^ 2 / 2) * reducedCoefficient ω (γ u.toNNReal)
              (firstCoordinateIndex hd) (firstCoordinateIndex hd)))) 2 (P₀ (0, ω)) := by
  have hΛ : 0 < Λ₀ := lt_of_lt_of_le zero_lt_one Q.ellipticity_parameter
  filter_upwards [Q.regular, s5_gmp_textbook_at_every_start hd Q 0 (by norm_num)
    (by norm_num) P₀ hP₀] with ω hω hzero
  exact u3_reduced_force_density_memLp_two (by omega) hΛ hω (firstCoordinateIndex hd)
    (hzero 0) mu t

/-- Every bounded measurable observation is integrable at the actual endpoint. -/
theorem s9_gmp_bounded_endpoint_integrable
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (mu : ℝ) (h0 : 0 ≤ mu) (h1 : mu ≤ 1) (P : QuenchedPathLaws d)
    (hP : IsGMPReducedKernel hd Q.ellipticity_parameter Q mu h0 h1 P)
    (t : ℝ≥0) (f : FieldPair d → ℂ) (hf : StronglyMeasurable f)
    (C : ℝ) (hC : ∀ ρ, ‖f ρ‖ ≤ C) :
    ∀ᵐ ω ∂Q.measure,
      Integrable (fun γ : Path d => f (translate (γ t) (reduce ω))) (P (0, ω)) := by
  filter_upwards [hP] with ω hω
  obtain ⟨hreg, R, hR⟩ := hω
  have hp : IsProbabilityMeasure (P (0, ω)) := by
    rw [hR 0]
    letI := R.pathLaw_isMarkovKernel
    infer_instance
  letI := hp
  apply (integrable_const C).mono'
  · exact (hf.comp_measurable ((Probability.continuous_translate.comp
      ((continuous_eval.comp (continuous_id.prodMk continuous_const)).prodMk
        continuous_const)).measurable)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun γ => hC _)

/-- The actual force-change density has a structural second-moment bound. -/
theorem s9_gmp_force_density_second_moment
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (mu : ℝ) (P₀ : QuenchedPathLaws d)
    (hP₀ : IsGMPReducedKernel hd Q.ellipticity_parameter Q 0 (by norm_num) (by norm_num) P₀)
    (t : ℝ≥0) :
    ∀ᵐ ω ∂Q.measure,
      (∫⁻ γ : Path d, ENNReal.ofReal ((Real.exp
        (mu * ((γ t) (firstCoordinateIndex hd) - (0 : Vec d) (firstCoordinateIndex hd)) -
          ∫ u in Set.Ioc (0 : ℝ) (t : ℝ),
            (mu * forcedDrift (reducedCoefficient ω) (firstCoordinateIndex hd) 0
              (γ u.toNNReal) (firstCoordinateIndex hd) +
              (mu ^ 2 / 2) * reducedCoefficient ω (γ u.toNNReal)
                (firstCoordinateIndex hd) (firstCoordinateIndex hd)))) ^ 2) ∂P₀ (0, ω)) ≤
      ENNReal.ofReal (Real.exp (mu ^ 2 * (Real.exp (2 * Λ₀) * Λ₀) * (t : ℝ))) := by
  have hΛ : 0 < Λ₀ := lt_of_lt_of_le zero_lt_one Q.ellipticity_parameter
  filter_upwards [Q.regular, s5_gmp_textbook_at_every_start hd Q 0 (by norm_num)
    (by norm_num) P₀ hP₀] with ω hω hzero
  let i := firstCoordinateIndex hd
  let Z : ℝ → Path d → ℝ := fun a γ => Real.exp
    (a * ((γ t) i - (0 : Vec d) i) - ∫ u in Set.Ioc (0 : ℝ) (t : ℝ),
      (a * forcedDrift (reducedCoefficient ω) i 0 (γ u.toNNReal) i +
        (a ^ 2 / 2) * reducedCoefficient ω (γ u.toNNReal) i i))
  let B : ℝ := Real.exp (mu ^ 2 * (Real.exp (2 * Λ₀) * Λ₀) * (t : ℝ))
  have hmass : (∫⁻ γ, ENNReal.ofReal (Z (2 * mu) γ) ∂P₀ (0, ω)) = 1 := by
    letI := u3_reduced_force_tilt_probability (by omega) hΛ hω i (hzero 0) (2 * mu) t
    have hm := measure_univ (μ := (P₀ (0, ω)).withDensity (fun γ => ENNReal.ofReal (Z (2 * mu) γ)))
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at hm
    exact hm
  change (∫⁻ γ, ENNReal.ofReal (Z mu γ ^ 2) ∂P₀ (0, ω)) ≤ ENNReal.ofReal B
  calc
    _ ≤ ∫⁻ γ, ENNReal.ofReal (Z (2 * mu) γ * B) ∂P₀ (0, ω) := by
      apply lintegral_mono
      intro γ
      exact ENNReal.ofReal_le_ofReal (u3_reduced_force_density_sq_le_double_force hΛ hω i mu t γ)
    _ = (∫⁻ γ, ENNReal.ofReal (Z (2 * mu) γ) ∂P₀ (0, ω)) * ENNReal.ofReal B := by
      simp_rw [ENNReal.ofReal_mul (show 0 ≤ Z (2 * mu) _ from (Real.exp_pos _).le)]
      exact lintegral_mul_const' _ _ ENNReal.ofReal_ne_top
    _ = _ := by rw [hmass, one_mul]

/-- Under the unforced joint-marginal equation, L² observations remain L²
at almost every quenched endpoint. -/
theorem s9_unforced_endpoint_memLp_two_of_marginal
    {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (K : Kernel (FieldPair d) (Path d)) [IsMarkovKernel K]
    (t : ℝ≥0)
    (hmarginal : Measure.map
      (fun z : FieldPair d × Path d => translate (z.2 t) (reduce z.1))
      (Q.measure ⊗ₘ K) = reducedLaw Q)
    (f : Lp ℂ 2 (reducedLaw Q)) :
    ∀ᵐ ω ∂Q.measure,
      MemLp (fun γ : Path d => f (translate (γ t) (reduce ω))) 2 (K ω) := by
  let E : FieldPair d × Path d → FieldPair d := fun z => translate (z.2 t) (reduce z.1)
  have hE : Measurable E := (Probability.continuous_translate.comp
    ((continuous_eval.comp (continuous_snd.prodMk continuous_const)).prodMk
      (Probability.continuous_reduce.comp continuous_fst))).measurable
  have hjoint : MemLp (fun z => f (E z)) 2 (Q.measure ⊗ₘ K) := by
    have hf : MemLp (fun ρ => f ρ) 2 (Measure.map E (Q.measure ⊗ₘ K)) := by
      rw [hmarginal]
      exact Lp.memLp f
    exact hf.comp_of_map hE.aemeasurable
  have hsq := (memLp_two_iff_integrable_sq_norm hjoint.aestronglyMeasurable).mp hjoint
  have hsections := ((Measure.integrable_compProd_iff hsq.aestronglyMeasurable).mp hsq).1
  filter_upwards [hsections] with ω hω
  have hmeas : StronglyMeasurable (fun γ : Path d => f (translate (γ t) (reduce ω))) :=
    (Lp.stronglyMeasurable f).comp_measurable
      ((Probability.continuous_translate.comp
        ((continuous_eval.comp (continuous_id.prodMk continuous_const)).prodMk
          continuous_const)).measurable)
  exact (memLp_two_iff_integrable_sq_norm hmeas.aestronglyMeasurable).mpr hω

/-- The unforced joint-marginal equation implies quenched integrability of an
L² observation under the actual forced GMP endpoint. -/
theorem s9_gmp_endpoint_integrable_of_unforced_marginal
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (mu : ℝ) (h0 : 0 ≤ mu) (h1 : mu ≤ 1) (P₀ P : QuenchedPathLaws d)
    (hP₀ : IsGMPReducedKernel hd Q.ellipticity_parameter Q 0 (by norm_num) (by norm_num) P₀)
    (hP : IsGMPReducedKernel hd Q.ellipticity_parameter Q mu h0 h1 P)
    (K : Kernel (FieldPair d) (Path d)) [IsMarkovKernel K]
    (hK : ∀ᵐ ω ∂Q.measure, K ω = P₀ (0, ω))
    (t : ℝ≥0)
    (hmarginal : Measure.map
      (fun z : FieldPair d × Path d => translate (z.2 t) (reduce z.1))
      (Q.measure ⊗ₘ K) = reducedLaw Q)
    (f : Lp ℂ 2 (reducedLaw Q)) :
    ∀ᵐ ω ∂Q.measure,
      Integrable (fun γ : Path d => f (translate (γ t) (reduce ω))) (P (0, ω)) := by
  filter_upwards [s9_unforced_endpoint_memLp_two_of_marginal Q K t hmarginal f, hK,
    s9_gmp_force_density_memLp_two hd Q mu P₀ hP₀ t,
    s9_gmp_force_finite_horizon hd Q mu h0 h1 P₀ P hP₀ hP t] with ω hU hKω hZ htilt
  rw [hKω] at hU
  let i := firstCoordinateIndex hd
  let Z : Path d → ℝ := fun γ => Real.exp
    (mu * ((γ t) i - (0 : Vec d) i) - ∫ u in Set.Ioc (0 : ℝ) (t : ℝ),
      (mu * forcedDrift (reducedCoefficient ω) i 0 (γ u.toNNReal) i +
        (mu ^ 2 / 2) * reducedCoefficient ω (γ u.toNNReal) i i))
  let U : Path d → ℂ := fun γ => f (translate (γ t) (reduce ω))
  let R := (P₀ (0, ω)).withDensity (fun γ => ENNReal.ofReal (Z γ))
  change MemLp U 2 (P₀ (0, ω)) at hU
  change MemLp Z 2 (P₀ (0, ω)) at hZ
  have hmul : Integrable (fun γ => (Z γ : ℂ) * U γ) (P₀ (0, ω)) :=
    hZ.ofReal.integrable_mul hU
  have hR : Integrable U R := by
    apply (integrable_withDensity_iff_integrable_smul₀' hZ.aemeasurable.ennreal_ofReal
      (ae_of_all _ fun γ => ENNReal.ofReal_lt_top)).2
    convert hmul using 1
    funext γ
    simp only [ENNReal.toReal_ofReal (show 0 ≤ Z γ from (Real.exp_pos _).le), Complex.real_smul]
  have heq : Measure.map (fun γ : Path d => γ t) (P (0, ω)) =
      Measure.map (fun γ : Path d => γ t) R := by
    ext S hS
    change (Measure.map (pathPosition t) (P (0, ω))) S = (Measure.map (pathPosition t) R) S
    rw [Measure.map_apply (measurable_pathPosition t) hS,
      Measure.map_apply (measurable_pathPosition t) hS,
      withDensity_apply _ (hS.preimage (measurable_pathPosition t))]
    exact htilt _ ((Filtration.stronglyAdapted_natural
      (fun s => (measurable_pathPosition (d := d) s).stronglyMeasurable) t).measurable hS)
  let V : Vec d → ℂ := fun x => f (translate x (reduce ω))
  have hV : StronglyMeasurable V := (Lp.stronglyMeasurable f).comp_measurable
    (Probability.continuous_translate.measurable.comp (measurable_id.prodMk measurable_const))
  have hmap : Integrable V (Measure.map (fun γ : Path d => γ t) R) :=
    (integrable_map_measure hV.aestronglyMeasurable (measurable_pathPosition t).aemeasurable).2 hR
  rw [← heq] at hmap
  exact hmap.comp_measurable (measurable_pathPosition t)

/-- The actual forced endpoint expectation satisfies the quenched
Cauchy–Schwarz bound with the unforced endpoint norm. -/
theorem s9_gmp_endpoint_enorm_bound_of_unforced_marginal
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (mu : ℝ) (h0 : 0 ≤ mu) (h1 : mu ≤ 1) (P₀ P : QuenchedPathLaws d)
    (hP₀ : IsGMPReducedKernel hd Q.ellipticity_parameter Q 0 (by norm_num) (by norm_num) P₀)
    (hP : IsGMPReducedKernel hd Q.ellipticity_parameter Q mu h0 h1 P)
    (K : Kernel (FieldPair d) (Path d)) [IsMarkovKernel K]
    (hK : ∀ᵐ ω ∂Q.measure, K ω = P₀ (0, ω)) (t : ℝ≥0)
    (hmarginal : Measure.map
      (fun z : FieldPair d × Path d => translate (z.2 t) (reduce z.1))
      (Q.measure ⊗ₘ K) = reducedLaw Q)
    (f : Lp ℂ 2 (reducedLaw Q)) :
    ∀ᵐ ω ∂Q.measure,
      ‖∫ γ : Path d, f (translate (γ t) (reduce ω)) ∂P (0, ω)‖ₑ ≤
        ENNReal.ofReal (Real.exp (mu ^ 2 * (Real.exp (2 * Λ₀) * Λ₀) * (t : ℝ))) ^ (1 / 2 : ℝ) *
          eLpNorm (fun γ : Path d => f (translate (γ t) (reduce ω))) 2 (P₀ (0, ω)) := by
  filter_upwards [s9_unforced_endpoint_memLp_two_of_marginal Q K t hmarginal f, hK,
    s9_gmp_force_density_memLp_two hd Q mu P₀ hP₀ t,
    s9_gmp_force_density_second_moment hd Q mu P₀ hP₀ t,
    s9_gmp_force_finite_horizon hd Q mu h0 h1 P₀ P hP₀ hP t] with ω hU hKω hZ hsecond htilt
  rw [hKω] at hU
  let i := firstCoordinateIndex hd
  let Z : Path d → ℝ := fun γ => Real.exp
    (mu * ((γ t) i - (0 : Vec d) i) - ∫ u in Set.Ioc (0 : ℝ) (t : ℝ),
      (mu * forcedDrift (reducedCoefficient ω) i 0 (γ u.toNNReal) i +
        (mu ^ 2 / 2) * reducedCoefficient ω (γ u.toNNReal) i i))
  let U : Path d → ℂ := fun γ => f (translate (γ t) (reduce ω))
  let R := (P₀ (0, ω)).withDensity (fun γ => ENNReal.ofReal (Z γ))
  change MemLp Z 2 (P₀ (0, ω)) at hZ
  change MemLp U 2 (P₀ (0, ω)) at hU
  change (∫⁻ γ, ENNReal.ofReal (Z γ ^ 2) ∂P₀ (0, ω)) ≤ _ at hsecond
  have hZbound : eLpNorm Z 2 (P₀ (0, ω)) ≤
      ENNReal.ofReal (Real.exp (mu ^ 2 * (Real.exp (2 * Λ₀) * Λ₀) * (t : ℝ))) ^ (1 / 2 : ℝ) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hZ.aestronglyMeasurable]
    apply ENNReal.rpow_le_rpow _ (by norm_num : (0 : ℝ) ≤ 1 / 2)
    have hz : ∀ γ, ‖Z γ‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (Z γ ^ 2) := by
      intro γ
      rw [ENNReal.rpow_two, Real.enorm_eq_ofReal (show 0 ≤ Z γ from (Real.exp_pos _).le),
        ← ENNReal.ofReal_pow (show 0 ≤ Z γ from (Real.exp_pos _).le)]
    simpa only [ENNReal.toReal_ofNat, hz] using hsecond
  have heq : Measure.map (fun γ : Path d => γ t) (P (0, ω)) =
      Measure.map (fun γ : Path d => γ t) R := by
    ext S hS
    change (Measure.map (pathPosition t) (P (0, ω))) S = (Measure.map (pathPosition t) R) S
    rw [Measure.map_apply (measurable_pathPosition t) hS,
      Measure.map_apply (measurable_pathPosition t) hS,
      withDensity_apply _ (hS.preimage (measurable_pathPosition t))]
    exact htilt _ ((Filtration.stronglyAdapted_natural
      (fun s => (measurable_pathPosition (d := d) s).stronglyMeasurable) t).measurable hS)
  let V : Vec d → ℂ := fun x => f (translate x (reduce ω))
  have hV : StronglyMeasurable V := (Lp.stronglyMeasurable f).comp_measurable
    (Probability.continuous_translate.measurable.comp (measurable_id.prodMk measurable_const))
  have haction : (∫ γ : Path d, f (translate (γ t) (reduce ω)) ∂P (0, ω)) =
      ∫ γ : Path d, (Z γ : ℂ) * U γ ∂P₀ (0, ω) := by
    calc
      _ = ∫ x, V x ∂Measure.map (fun γ : Path d => γ t) (P (0, ω)) :=
        (integral_map (measurable_pathPosition t).aemeasurable hV.aestronglyMeasurable).symm
      _ = ∫ x, V x ∂Measure.map (fun γ : Path d => γ t) R := by rw [heq]
      _ = ∫ γ : Path d, V (γ t) ∂R :=
        integral_map (measurable_pathPosition t).aemeasurable hV.aestronglyMeasurable
      _ = _ := by
        rw [integral_withDensity_eq_integral_toReal_smul₀ hZ.aemeasurable.ennreal_ofReal
          (ae_of_all _ fun γ => ENNReal.ofReal_lt_top)]
        apply integral_congr_ae
        filter_upwards [] with γ
        simp only [U, V, ENNReal.toReal_ofReal (show 0 ≤ Z γ from (Real.exp_pos _).le), Complex.real_smul]
  have hh := ENNReal.lintegral_mul_le_Lp_mul_Lq (P₀ (0, ω))
    Real.HolderConjugate.two_two hZ.aemeasurable.enorm hU.aemeasurable.enorm
  have hholder : (∫⁻ γ, ‖Z γ‖ₑ * ‖U γ‖ₑ ∂P₀ (0, ω)) ≤
      eLpNorm Z 2 (P₀ (0, ω)) * eLpNorm U 2 (P₀ (0, ω)) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hZ.aestronglyMeasurable,
      eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hU.aestronglyMeasurable]
    simpa only [Pi.mul_apply, ENNReal.toReal_ofNat] using hh
  rw [haction]
  change ‖∫ γ, (Z γ : ℂ) * U γ ∂P₀ (0, ω)‖ₑ ≤ _
  calc
    _ ≤ ∫⁻ γ, ‖(Z γ : ℂ) * U γ‖ₑ ∂P₀ (0, ω) := enorm_integral_le_lintegral_enorm _
    _ = ∫⁻ γ, ‖Z γ‖ₑ * ‖U γ‖ₑ ∂P₀ (0, ω) := by
      apply lintegral_congr
      intro γ
      rw [enorm_mul]
      congr 1
      apply enorm_eq_iff_norm_eq.mpr
      simpa only [Real.norm_eq_abs] using Complex.norm_real (Z γ)
    _ ≤ eLpNorm Z 2 (P₀ (0, ω)) * eLpNorm U 2 (P₀ (0, ω)) := hholder
    _ ≤ _ := mul_le_mul' hZbound le_rfl

/-- The actual GMP endpoint action is bounded in annealed L¹, conditional only
on the unforced joint-marginal invariance equation. -/
theorem s9_gmp_endpoint_annealed_bound_of_unforced_marginal
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (mu : ℝ) (h0 : 0 ≤ mu) (h1 : mu ≤ 1) (P₀ P : QuenchedPathLaws d)
    (hP₀ : IsGMPReducedKernel hd Q.ellipticity_parameter Q 0 (by norm_num) (by norm_num) P₀)
    (hP : IsGMPReducedKernel hd Q.ellipticity_parameter Q mu h0 h1 P)
    (K : Kernel (FieldPair d) (Path d)) [IsMarkovKernel K]
    (hK : ∀ᵐ ω ∂Q.measure, K ω = P₀ (0, ω)) (t : ℝ≥0)
    (hmarginal : Measure.map
      (fun z : FieldPair d × Path d => translate (z.2 t) (reduce z.1))
      (Q.measure ⊗ₘ K) = reducedLaw Q)
    (f : Lp ℂ 2 (reducedLaw Q)) :
    (∫⁻ ω, ‖∫ γ : Path d, f (translate (γ t) (reduce ω)) ∂P (0, ω)‖ₑ ∂Q.measure) ≤
      ENNReal.ofReal (Real.exp (mu ^ 2 * (Real.exp (2 * Λ₀) * Λ₀) * (t : ℝ))) ^ (1 / 2 : ℝ) *
        eLpNorm (fun ρ => f ρ) 2 (reducedLaw Q) := by
  letI : IsProbabilityMeasure Q.measure := Q.probability
  let E : FieldPair d × Path d → FieldPair d := fun z => translate (z.2 t) (reduce z.1)
  have hE : Measurable E := (Probability.continuous_translate.comp
    ((continuous_eval.comp (continuous_snd.prodMk continuous_const)).prodMk
      (Probability.continuous_reduce.comp continuous_fst))).measurable
  let F : FieldPair d × Path d → ℝ≥0∞ := fun z => ‖f (E z)‖ₑ ^ (2 : ℝ)
  have hF : Measurable F := ((Lp.stronglyMeasurable f).measurable.comp hE).enorm.pow_const _
  let G : FieldPair d → ℝ≥0∞ := fun ω => ∫⁻ γ, F (ω, γ) ∂K ω
  have hG : Measurable G := hF.lintegral_kernel_prod_right
  have hGint : (∫⁻ ω, G ω ∂Q.measure) =
      ∫⁻ ρ, ‖f ρ‖ₑ ^ (2 : ℝ) ∂reducedLaw Q := by
    change (∫⁻ ω, ∫⁻ γ, F (ω, γ) ∂K ω ∂Q.measure) = _
    rw [← Measure.lintegral_compProd hF]
    calc
      _ = ∫⁻ ρ, ‖f ρ‖ₑ ^ (2 : ℝ) ∂Measure.map E (Q.measure ⊗ₘ K) :=
        (lintegral_map ((Lp.stronglyMeasurable f).measurable.enorm.pow_const _) hE).symm
      _ = _ := congrArg (fun ν : Measure (FieldPair d) => ∫⁻ ρ, ‖f ρ‖ₑ ^ (2 : ℝ) ∂ν) hmarginal
  have hholder := ENNReal.lintegral_mul_le_Lp_mul_Lq Q.measure
    Real.HolderConjugate.two_two (f := fun _ : FieldPair d => (1 : ℝ≥0∞))
    measurable_const.aemeasurable (hG.pow_const (1 / 2 : ℝ)).aemeasurable
  have hroot : (∫⁻ ω, G ω ^ (1 / 2 : ℝ) ∂Q.measure) ≤
      (∫⁻ ω, G ω ∂Q.measure) ^ (1 / 2 : ℝ) := by
    have hpow : ∀ ω, (G ω ^ (1 / 2 : ℝ)) ^ (2 : ℝ) = G ω := by
      intro ω
      rw [← ENNReal.rpow_mul]
      norm_num
    simpa only [Pi.mul_apply, one_mul, ENNReal.one_rpow, lintegral_one,
      measure_univ, hpow] using hholder
  let B : ℝ≥0∞ := ENNReal.ofReal (Real.exp
    (mu ^ 2 * (Real.exp (2 * Λ₀) * Λ₀) * (t : ℝ))) ^ (1 / 2 : ℝ)
  have hbound := s9_gmp_endpoint_enorm_bound_of_unforced_marginal hd Q mu h0 h1
    P₀ P hP₀ hP K hK t hmarginal f
  have hpoint : ∀ᵐ ω ∂Q.measure,
      ‖∫ γ : Path d, f (translate (γ t) (reduce ω)) ∂P (0, ω)‖ₑ ≤ B * G ω ^ (1 / 2 : ℝ) := by
    filter_upwards [hbound, hK] with ω hω hKω
    apply hω.trans
    apply mul_le_mul' le_rfl
    rw [← hKω]
    have hU : AEStronglyMeasurable (fun γ : Path d => f (translate (γ t) (reduce ω))) (K ω) :=
      ((Lp.stronglyMeasurable f).comp_measurable
        ((Probability.continuous_translate.comp
          ((continuous_eval.comp (continuous_id.prodMk continuous_const)).prodMk continuous_const)).measurable)).aestronglyMeasurable
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hU]
    simp only [ENNReal.toReal_ofNat]
    rfl
  calc
    _ ≤ ∫⁻ ω, B * G ω ^ (1 / 2 : ℝ) ∂Q.measure := lintegral_mono_ae hpoint
    _ = B * (∫⁻ ω, G ω ^ (1 / 2 : ℝ) ∂Q.measure) := lintegral_const_mul _ (hG.pow_const _)
    _ ≤ B * (∫⁻ ω, G ω ∂Q.measure) ^ (1 / 2 : ℝ) := mul_le_mul' le_rfl hroot
    _ = _ := by
      rw [hGint, eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)
        (Lp.stronglyMeasurable f).aestronglyMeasurable]
      simp only [ENNReal.toReal_ofNat]
      rfl

/-- The actual unforced joint path law has reduced-law endpoint marginal. -/
theorem s9_gmp_unforced_joint_endpoint_marginal
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (P₀ : QuenchedPathLaws d)
    (hP₀ : IsGMPReducedKernel hd Q.ellipticity_parameter Q 0 (by norm_num) (by norm_num) P₀)
    (K : Kernel (FieldPair d) (Path d)) [IsMarkovKernel K]
    (hK : ∀ᵐ ω ∂Q.measure, K ω = P₀ (0, ω)) (t : ℝ≥0) :
    Measure.map (fun z : FieldPair d × Path d => translate (z.2 t) (reduce z.1))
      (Q.measure ⊗ₘ K) = reducedLaw Q := by
  let E : FieldPair d × Path d → FieldPair d := fun z => translate (z.2 t) (reduce z.1)
  have hE : Measurable E := (Probability.continuous_translate.comp
    ((continuous_eval.comp (continuous_snd.prodMk continuous_const)).prodMk
      (Probability.continuous_reduce.comp continuous_fst))).measurable
  rw [← s12_gmp_unforced_environment_invariant hd Q P₀ hP₀ K hK t]
  ext s hs
  rw [Measure.map_apply hE hs, Measure.compProd_apply (hE hs),
    Measure.bind_apply hs (Kernel.aemeasurable _)]
  apply lintegral_congr
  intro ω
  rw [c2EnvironmentKernel_apply]
  have hm : Measurable (fun γ : Path d => translate (γ t) (reduce ω)) := by
    simpa [E, Function.comp_def] using hE.comp (measurable_const.prodMk measurable_id)
  rw [Measure.map_apply hm hs]
  rfl

/-- A structural constant controls the actual GMP endpoint action throughout
a finite horizon and the full auxiliary force range. -/
theorem s9_gmp_endpoint_annealed_horizon_bound
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (mu : ℝ) (h0 : 0 ≤ mu) (h1 : mu ≤ 1) (P₀ P : QuenchedPathLaws d)
    (hP₀ : IsGMPReducedKernel hd Q.ellipticity_parameter Q 0 (by norm_num) (by norm_num) P₀)
    (hP : IsGMPReducedKernel hd Q.ellipticity_parameter Q mu h0 h1 P)
    (K : Kernel (FieldPair d) (Path d)) [IsMarkovKernel K]
    (hK : ∀ᵐ ω ∂Q.measure, K ω = P₀ (0, ω)) (t T : ℝ≥0) (ht : t ≤ T)
    (f : Lp ℂ 2 (reducedLaw Q)) :
    (∫⁻ ω, ‖∫ γ : Path d, f (translate (γ t) (reduce ω)) ∂P (0, ω)‖ₑ ∂Q.measure) ≤
      ENNReal.ofReal (Real.exp ((Real.exp (2 * Λ₀) * Λ₀) * (T : ℝ))) ^ (1 / 2 : ℝ) *
        eLpNorm (fun ρ => f ρ) 2 (reducedLaw Q) := by
  refine (s9_gmp_endpoint_annealed_bound_of_unforced_marginal hd Q mu h0 h1 P₀ P hP₀ hP
    K hK t (s9_gmp_unforced_joint_endpoint_marginal hd Q P₀ hP₀ K hK t) f).trans ?_
  apply mul_le_mul' _ le_rfl
  apply ENNReal.rpow_le_rpow _ (by norm_num : (0 : ℝ) ≤ 1 / 2)
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  have hμ : mu ^ 2 ≤ 1 := by nlinarith
  have hΛ : 0 ≤ Real.exp (2 * Λ₀) * Λ₀ :=
    mul_nonneg (Real.exp_pos _).le (zero_le_one.trans Q.ellipticity_parameter)
  calc
    _ ≤ 1 * (Real.exp (2 * Λ₀) * Λ₀) * (t : ℝ) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hμ hΛ) t.coe_nonneg
    _ ≤ _ := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_left (show (t : ℝ) ≤ (T : ℝ) from ht) hΛ

/-- The supplied GMP endpoint action is Lipschitz from reduced-law L² to
annealed L¹, uniformly over the force interval and a finite time horizon. -/
theorem s9_gmp_endpoint_action_sub_horizon_bound
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (mu : ℝ) (h0 : 0 ≤ mu) (h1 : mu ≤ 1) (P : QuenchedPathLaws d)
    (hP : IsGMPReducedKernel hd Q.ellipticity_parameter Q mu h0 h1 P)
    (t T : ℝ≥0) (ht : t ≤ T) (f g : Lp ℂ 2 (reducedLaw Q)) :
    (∫⁻ ω, ‖(∫ γ : Path d, f (translate (γ t) (reduce ω)) ∂P (0, ω)) -
      (∫ γ : Path d, g (translate (γ t) (reduce ω)) ∂P (0, ω))‖ₑ ∂Q.measure) ≤
      ENNReal.ofReal (Real.exp ((Real.exp (2 * Λ₀) * Λ₀) * (T : ℝ))) ^ (1 / 2 : ℝ) *
        eLpNorm (fun ρ => (f - g) ρ) 2 (reducedLaw Q) := by
  obtain ⟨P₀, hP₀⟩ := SbxS3Section3R01.joint_reduced_kernel_exists hd Q 0
    (by norm_num) (by norm_num)
  obtain ⟨K, hmark, hK⟩ := s5_gmp_origin_markov_version hd Q 0
    (by norm_num) (by norm_num) P₀ hP₀
  letI : IsMarkovKernel K := hmark
  have hmarginal := s9_gmp_unforced_joint_endpoint_marginal hd Q P₀ hP₀ K hK t
  have he := SbxS4Dynkin.ae_eq_at_supplied_endpoint hd Q mu h0 h1 P hP t
    (Lp.stronglyMeasurable (f - g)).measurable
    ((Lp.stronglyMeasurable f).measurable.sub (Lp.stronglyMeasurable g).measurable)
    (Lp.coeFn_sub f g)
  have heq : ∀ᵐ ω ∂Q.measure,
      (∫ γ : Path d, (f - g) (translate (γ t) (reduce ω)) ∂P (0, ω)) =
      (∫ γ : Path d, f (translate (γ t) (reduce ω)) ∂P (0, ω)) -
        ∫ γ : Path d, g (translate (γ t) (reduce ω)) ∂P (0, ω) := by
    filter_upwards [he,
      s9_gmp_endpoint_integrable_of_unforced_marginal hd Q mu h0 h1 P₀ P hP₀ hP K hK t hmarginal f,
      s9_gmp_endpoint_integrable_of_unforced_marginal hd Q mu h0 h1 P₀ P hP₀ hP K hK t hmarginal g]
      with ω he hf hg
    rw [integral_congr_ae he]
    exact integral_sub hf hg
  calc
    _ = ∫⁻ ω, ‖∫ γ : Path d, (f - g) (translate (γ t) (reduce ω)) ∂P (0, ω)‖ₑ ∂Q.measure := by
      apply lintegral_congr_ae
      filter_upwards [heq] with ω hω
      rw [hω]
    _ ≤ _ := s9_gmp_endpoint_annealed_horizon_bound hd Q mu h0 h1 P₀ P hP₀ hP
      K hK t T ht (f - g)

/-- L² data are integrable at the actual supplied GMP endpoint. -/
theorem s9_gmp_endpoint_integrable
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (mu : ℝ) (h0 : 0 ≤ mu) (h1 : mu ≤ 1) (P : QuenchedPathLaws d)
    (hP : IsGMPReducedKernel hd Q.ellipticity_parameter Q mu h0 h1 P)
    (t : ℝ≥0) (f : Lp ℂ 2 (reducedLaw Q)) :
    ∀ᵐ ω ∂Q.measure,
      Integrable (fun γ : Path d => f (translate (γ t) (reduce ω))) (P (0, ω)) := by
  obtain ⟨P₀, hP₀⟩ := SbxS3Section3R01.joint_reduced_kernel_exists hd Q 0
    (by norm_num) (by norm_num)
  obtain ⟨K, hmark, hK⟩ := s5_gmp_origin_markov_version hd Q 0
    (by norm_num) (by norm_num) P₀ hP₀
  letI : IsMarkovKernel K := hmark
  exact s9_gmp_endpoint_integrable_of_unforced_marginal hd Q mu h0 h1 P₀ P hP₀ hP
    K hK t (s9_gmp_unforced_joint_endpoint_marginal hd Q P₀ hP₀ K hK t) f

/-- A single finite constant works for all environment laws and forces with
the given ellipticity bound and time horizon. -/
theorem s9_gmp_endpoint_action_uniform_constant
    {d : ℕ} (hd : 2 ≤ d) (Λ₀ : ℝ) (T : ℝ≥0) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ {r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
      (mu : ℝ) (h0 : 0 ≤ mu) (h1 : mu ≤ 1) (P : QuenchedPathLaws d),
      IsGMPReducedKernel hd Q.ellipticity_parameter Q mu h0 h1 P →
      ∀ (t : ℝ≥0), t ≤ T → ∀ (f g : Lp ℂ 2 (reducedLaw Q)),
        (∫⁻ ω, ‖(∫ γ : Path d, f (translate (γ t) (reduce ω)) ∂P (0, ω)) -
          (∫ γ : Path d, g (translate (γ t) (reduce ω)) ∂P (0, ω))‖ₑ ∂Q.measure) ≤
          C * eLpNorm (fun ρ => (f - g) ρ) 2 (reducedLaw Q) := by
  refine ⟨ENNReal.ofReal (Real.exp ((Real.exp (2 * Λ₀) * Λ₀) * (T : ℝ))) ^
    (1 / 2 : ℝ), ?_, ?_⟩
  · exact (ENNReal.rpow_lt_top_of_nonneg (by norm_num) ENNReal.ofReal_lt_top.ne).ne
  · intro r₀ Q mu h0 h1 P hP t ht f g
    exact s9_gmp_endpoint_action_sub_horizon_bound hd Q mu h0 h1 P hP t T ht f g

end EinsteinFull
