import EinsteinFull.Blueprint.G3.node_l_u3A_finite_u2D_xi_u23_potential_u2D_identification
import EinsteinFull.Blueprint.G3.node_l_u3A_finite_u2D_xi_u23_gradient_u2D_limit
import EinsteinFull.Blueprint.Foundation.node_corrector_u2D_construction
import EinsteinFull.Blueprint.Foundation.node_e_u3A_generators_u23_real_u2D_semigroup
import EinsteinFull.Calculus.ComplexZeroForceFluxSupport
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import EinsteinFull.Blueprint.Foundation.Draft.S2SmoothScopeRealSemigroup

/-! # Identification of the integrable unforced gradient with the variational corrector -/

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation

private instance reducedProbability {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) : IsProbabilityMeasure (reducedLaw Q) :=
  reducedLaw_probability Q

variable {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d}
  {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}

private theorem unforced_norm_apply_le (hP : IsComplexEnvironmentSemigroup Q i 0 P)
    (t : ℝ≥0) (f : Lp ℂ 2 (reducedLaw Q)) : ‖P t f‖ ≤ ‖f‖ := by
  have hb := hP.norm_le t
  norm_num [complexForceShift] at hb
  exact ((P t).le_opNorm f).trans (by
    simpa only [one_mul] using! mul_le_mul_of_nonneg_right hb (norm_nonneg f))

private theorem integrable_laplace_orbit (hP : IsComplexEnvironmentSemigroup Q i 0 P)
    (s : ℝ) (hs : 0 < s) (f : Lp ℂ 2 (reducedLaw Q)) :
    IntegrableOn (fun t : ℝ => Real.exp (-s*t) • P t.toNNReal f) (Ici 0) := by
  have he := (integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hs) 0).mul_const ‖f‖
  have he : IntegrableOn (fun t : ℝ => Real.exp (-s*t) * ‖f‖) (Ici 0) :=
    (integrableOn_Ici_iff_integrableOn_Ioi).mpr he
  apply he.mono'
  · exact ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).smul
      ((hP.2.2.1 f).comp continuous_real_toNNReal)).aestronglyMeasurable
  · filter_upwards [] with t
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_left (unforced_norm_apply_le hP _ f) (Real.exp_pos _).le

private theorem integral_Icc_tendsto_Ici {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : ℝ → E}
    (hf : IntegrableOn f (Ici 0)) :
    Tendsto (fun T : ℝ => ∫ t in Icc (0 : ℝ) T, f t) atTop
      (𝓝 (∫ t in Ici (0 : ℝ), f t)) := by
  have hsets : (⋃ T : ℝ, Icc (0 : ℝ) T) = Ici 0 := by
    ext t
    simp only [mem_iUnion, mem_Icc, mem_Ici]
    exact ⟨fun ⟨_, h, _⟩ => h, fun h => ⟨t, h, le_rfl⟩⟩
  have ht := tendsto_setIntegral_of_monotone
    (fun T : ℝ => measurableSet_Icc (a := 0) (b := T))
    (fun _ _ h => Icc_subset_Icc_right h) (hsets ▸ hf)
  simpa only [hsets] using! ht

private theorem laplace_orbit_eq_resolvent (hP : IsComplexEnvironmentSemigroup Q i 0 P)
    (s : ℝ) (hs : 0 < s) (f : Lp ℂ 2 (reducedLaw Q)) :
    (∫ t in Ici (0 : ℝ), Real.exp (-s*t) • P t.toNNReal f) =
      unforcedComplexResolvent Q i s hs f := by
  let u := unforcedComplexResolvent Q i s hs f
  have hu := unforcedComplexResolvent_spec Q i s hs f
  have hcont : Continuous (fun t : ℝ => Real.exp (-s*t) • P t.toNNReal u) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).smul
      ((hP.2.2.1 u).comp continuous_real_toNNReal)
  have hint := integrable_laplace_orbit hP s hs f
  have hlim : Tendsto (fun t : ℝ => Real.exp (-s*t) • P t.toNNReal u) atTop (𝓝 0) := by
    apply squeeze_zero_norm (a := fun t : ℝ => Real.exp (-s*t) * ‖u‖)
    · intro t
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul_of_nonneg_left (unforced_norm_apply_le hP _ u) (Real.exp_pos _).le
    · have ht := Real.tendsto_exp_atBot.comp
        (Filter.Tendsto.const_mul_atTop_of_neg (neg_lt_zero.mpr hs) tendsto_id)
      simpa only [zero_mul] using! ht.mul_const ‖u‖
  have hd (t : ℝ) (ht : 0 ≤ t) :
      HasDerivWithinAt (fun r : ℝ => Real.exp (-s*r) • P r.toNNReal u)
        (-(Real.exp (-s*t) • P t.toNNReal f)) (Ici t) t := by
    have he : HasDerivAt (fun r : ℝ => Real.exp (-s*r))
        ((-s) * Real.exp (-s*t)) t := by
      simpa only [id_eq, mul_one, mul_comm] using!
        (((hasDerivAt_id t).const_mul (-s)).exp)
    have h := he.hasDerivWithinAt.smul (hP.hasDerivWithinAt_orbit hu t ht)
    convert! h using 1
    change -(Real.exp (-s*t) • P t.toNNReal f) =
      Real.exp (-s*t) • P t.toNNReal ((s : ℂ) • u - f) +
        (-s * Real.exp (-s*t)) • P t.toNNReal u
    rw [map_sub, map_smul, Complex.coe_smul, smul_sub]
    module
  have hi (T : ℝ) (hT : 0 ≤ T) :=
    intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hT hcont.continuousOn
      (fun t ht => (hd t ht.1.le).mono Ioi_subset_Ici_self)
      ((intervalIntegrable_iff_integrableOn_Icc_of_le hT).mpr
        (hint.mono_set (fun _ h => h.1))).neg
  have hi' (T : ℝ) (hT : 0 ≤ T) :
      (∫ t in Icc (0 : ℝ) T, Real.exp (-s*t) • P t.toNNReal f) =
        u - Real.exp (-s*T) • P T.toNNReal u := by
    have h := hi T hT
    rw [intervalIntegral.integral_neg, intervalIntegral.integral_of_le hT,
      ← integral_Icc_eq_integral_Ioc] at h
    simp only [mul_zero, Real.exp_zero, one_smul, Real.toNNReal_zero, hP.1,
      ContinuousLinearMap.id_apply] at h
    exact (neg_eq_iff_eq_neg.mp h).trans (neg_sub _ _)
  have ht := integral_Icc_tendsto_Ici hint
  have ht' : Tendsto (fun T : ℝ => u - Real.exp (-s*T) • P T.toNNReal u)
      atTop (𝓝 u) := by
    simpa only [sub_zero] using! (tendsto_const_nhds (x := u)).sub hlim
  exact tendsto_nhds_unique ht (ht'.congr' (by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
    exact (hi' T hT).symm))

private theorem integrable_laplace_gradient {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (s : ℝ) (hs : 0 < s)
    {g : ℝ → E} (hg : IntegrableOn g (Ici 0)) :
    IntegrableOn (fun t : ℝ => Real.exp (-s*t) • g t) (Ici 0) := by
  apply hg.bdd_smul (φ := fun t : ℝ => Real.exp (-s*t)) 1
  · exact (Real.continuous_exp.comp (continuous_const.mul continuous_id)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hs.le) ht)

private theorem laplace_integral_tendsto {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {g : ℝ → E}
    (hg : IntegrableOn g (Ici 0)) (mass : ℕ → ℝ) (hm : ∀ n, 0 < mass n)
    (hm0 : Tendsto mass atTop (𝓝 0)) :
    Tendsto (fun n => ∫ t in Ici (0 : ℝ), Real.exp (-mass n*t) • g t)
      atTop (𝓝 (∫ t in Ici (0 : ℝ), g t)) := by
  apply tendsto_integral_of_dominated_convergence (fun t => ‖g t‖)
    (fun n => (integrable_laplace_gradient (mass n) (hm n) hg).aestronglyMeasurable)
    hg.norm
  · intro n
    filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact mul_le_of_le_one_left (norm_nonneg _) (Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (hm n).le) ht))
  · exact Eventually.of_forall fun t => by
      have he := Real.continuous_exp.continuousAt.tendsto.comp (hm0.neg.mul_const t)
      simpa only [neg_zero, zero_mul, Real.exp_zero, one_smul] using! he.smul_const (g t)

private theorem derivative_integral_Icc
    {f g : ℝ → Lp ℂ 2 (reducedLaw Q)}
    (hf : IntegrableOn f (Ici 0)) (hg : IntegrableOn g (Ici 0))
    (hfg : ∀ t, HasComplexHorizontalDerivative (reducedLaw Q) (reducedLaw_stationary Q)
      i (f t) (g t)) (T : ℝ) :
    HasComplexHorizontalDerivative (reducedLaw Q) (reducedLaw_stationary Q) i
      (∫ t in Icc (0 : ℝ) T, f t) (∫ t in Icc (0 : ℝ) T, g t) := by
  exact HasComplexHorizontalDerivative.integral_of_ae
    (μ := volume.restrict (Icc (0 : ℝ) T)) (f := f) (g := g)
    (hf.mono_set (fun _ ht => ht.1)) (hg.mono_set (fun _ ht => ht.1))
    (Eventually.of_forall hfg)

private theorem derivative_integral_Ici
    {f g : ℝ → Lp ℂ 2 (reducedLaw Q)}
    (hf : IntegrableOn f (Ici 0)) (hg : IntegrableOn g (Ici 0))
    (hfg : ∀ t, HasComplexHorizontalDerivative (reducedLaw Q) (reducedLaw_stationary Q)
      i (f t) (g t)) :
    HasComplexHorizontalDerivative (reducedLaw Q) (reducedLaw_stationary Q) i
      (∫ t in Ici (0 : ℝ), f t) (∫ t in Ici (0 : ℝ), g t) := by
  exact (isClosed_complexHorizontalDerivative_graph (reducedLaw Q)
    (reducedLaw_stationary Q) i).mem_of_tendsto
      ((integral_Icc_tendsto_Ici hf).prodMk_nhds (integral_Icc_tendsto_Ici hg))
      (Eventually.of_forall (derivative_integral_Icc hf hg hfg))

private theorem gradient_laplace_orbit
    (hP : IsComplexEnvironmentSemigroup Q i 0 P) (s : ℝ) (hs : 0 < s)
    (f : Lp ℂ 2 (reducedLaw Q)) (G : ℝ≥0 → Fin d → Lp ℂ 2 (reducedLaw Q))
    (hG : ∀ t, HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
      (P t f) (G t))
    (hGi : ∀ j, IntegrableOn (fun t : ℝ => G t.toNNReal j) (Ici 0)) :
    HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
      (unforcedComplexResolvent Q i s hs f)
      (fun j => ∫ t in Ici (0 : ℝ), Real.exp (-s*t) • G t.toNNReal j) := by
  rw [← laplace_orbit_eq_resolvent hP s hs f]
  intro j
  exact derivative_integral_Ici (integrable_laplace_orbit hP s hs f)
    (integrable_laplace_gradient s hs (hGi j)) (fun t => by
      simpa only [Complex.coe_smul] using! (hG t.toNNReal j).smul (Real.exp (-s*t) : ℂ))

private theorem integrated_gradient_eq_corrector
    {D : StructuralData d} {Q : EnvironmentLaw d D.ellipticity D.dependenceRange}
    {hQ : HasSmoothBounds D Q} {β : Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hβ : IsReducedDriftObservation Q hQ β)
    {i : Fin d} {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i 0 P)
    (k : Fin d) (G : ℝ≥0 → Fin d → Lp ℂ 2 (reducedLaw Q))
    (hG : ∀ t, HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
      (P t (β k)) (G t))
    (hGi : ∀ j, IntegrableOn (fun t : ℝ => G t.toNNReal j) (Ici 0)) (j : Fin d) :
    (∫ t in Ici (0 : ℝ), G t.toNNReal j : Lp ℂ 2 (reducedLaw Q)) =ᵐ[reducedLaw Q]
      fun ω => (correctorGradient Q k ω j : ℂ) := by
  let mass : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hm (n : ℕ) : 0 < mass n := by dsimp [mass]; positivity
  have hm0 : Tendsto mass atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let T := (PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin d => ℂ) j).compLpL 2 (reducedLaw Q)
  let L := T ((euclideanComplexify d).compLpL 2 (reducedLaw Q) (correctorGradient Q k))
  have hcoord (n : ℕ) : T (unforcedComplexResolventEuclideanGradient Q i
      (mass n) (hm n) (β k)) =
      ∫ t in Ici (0 : ℝ), Real.exp (-mass n*t) • G t.toNNReal j := by
    have he : T (unforcedComplexResolventEuclideanGradient Q i (mass n) (hm n) (β k)) =
        unforcedComplexResolventGradient Q i (mass n) (hm n) (β k) j := by
      apply Lp.ext
      filter_upwards [(PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin d => ℂ) j).coeFn_compLpL
          (unforcedComplexResolventEuclideanGradient Q i (mass n) (hm n) (β k)),
        unforcedComplexResolventEuclideanGradient_ae Q i (mass n) (hm n) (β k)] with ω hc hg
      exact hc.trans (hg j)
    rw [he]
    exact (hasComplexHorizontalGradient_unforcedComplexResolvent Q i (mass n) (hm n)
      (β k) j).unique (gradient_laplace_orbit hP (mass n) (hm n) (β k) G hG hGi j)
  have hcanonical : Tendsto
      (fun n => ∫ t in Ici (0 : ℝ), Real.exp (-mass n*t) • G t.toNNReal j)
      atTop (𝓝 L) := by
    have hh := (T.continuous.tendsto _).comp
      (hβ.tendsto_resolvent_gradient i k mass hm hm0)
    change Tendsto (fun n => T (unforcedComplexResolventEuclideanGradient Q i
      (mass n) (hm n) (β k))) atTop (𝓝 L) at hh
    simpa only [hcoord] using! hh
  have hdom := laplace_integral_tendsto (hGi j) mass hm hm0
  have heq : (∫ t in Ici (0 : ℝ), G t.toNNReal j) = L :=
    tendsto_nhds_unique hdom hcanonical
  rw [heq]
  filter_upwards [(PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin d => ℂ) j).coeFn_compLpL
      ((euclideanComplexify d).compLpL 2 (reducedLaw Q) (correctorGradient Q k)),
    (euclideanComplexify d).coeFn_compLpL (correctorGradient Q k)] with ω hc he
  exact hc.trans (congrArg (fun v : EuclideanSpace ℂ (Fin d) => v j) he)

/-- The integrable gradient limit is the literal canonical stationary corrector gradient.
The prescribed corrector-construction and real-semigroup premises are retained;
the adopted massive-gradient proof already supplies the facts needed from them. -/
@[nolint unusedArguments]
theorem node_l_u3A_finite_u2D_xi_u23_potential_u2D_identification_of_deps :
    node_l_u3A_finite_u2D_xi_u23_gradient_u2D_limitStmt →
    node_corrector_u2D_constructionStmt →
    node_e_u3A_generators_u23_real_u2D_semigroupStmtV2 →
    node_l_u3A_finite_u2D_xi_u23_potential_u2D_identificationStmt := by
  intro hGradient _hCorrector _hReal d hd D Q hQ β hβ P hP
  obtain ⟨_C, _hC, hGradient⟩ := hGradient d hd D
  obtain ⟨G, hG, _hDecay, hGi⟩ := hGradient Q hQ β hβ P hP
  refine ⟨G, hG, fun i => ?_⟩
  let L : Fin d → Lp ℂ 2 (reducedLaw Q) := fun j => ∫ t in Ici (0 : ℝ), G t.toNNReal i j
  refine ⟨L, fun j => integrated_gradient_eq_corrector hβ hP i (fun t => G t i)
    (fun t => hG t i) (hGi i).1 j, ?_, fun j => ?_⟩
  · intro τ j
    apply HasComplexHorizontalDerivative.integral_of_ae
      (integrableOn_comp_toNNReal_Icc _ (hP.2.2.1 (β i)) (τ : ℝ))
      ((hGi i).1 j |>.mono_set (fun _ ht => ht.1))
    exact Eventually.of_forall fun t => hG t.toNNReal i j
  · exact ⟨(hGi i).1 j, rfl, integral_Icc_tendsto_Ici ((hGi i).1 j)⟩

end EinsteinFull.Blueprint
