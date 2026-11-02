import EinsteinFull.Calculus.C2ReducedEnvironmentKernel
import EinsteinFull.Calculus.C16FoundationInstantiation
import EinsteinFull.Calculus.C16ReducedMPExistence
import EinsteinFull.Calculus.ComplexTransposeSpatialSupport
import EinsteinFull.Calculus.ComplexHorizontalMeanSupport
import EinsteinFull.Blueprint.Foundation.node_stationary_u2D_environment
import EinsteinFull.Blueprint.Foundation.node_eq_u2E_reduced_u2D_bounds
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import SubdiffusiveProcess.Processes.E7.FellerFromResolvent

/-! Initial marginal, uniqueness, a spatial resolvent equation, and bounded
discounted occupation estimates for the unforced environment. Identifying the
actual MP occupation with the analytic resolvent remains a separate step. -/

open MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators Topology

noncomputable section
namespace EinsteinFull
open EinsteinRelation

/-- The actual annealed environment law at time zero is the reduced law. -/
theorem c17_unforced_environment_zero
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀)
    (K : Kernel (FieldPair d) (Path d)) [IsMarkovKernel K]
    (hK : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ ω 0) 0 (K ω)) :
    c2EnvironmentKernel K 0 ∘ₘ Q.measure = reducedLaw Q := by
  have hzero : ∀ᵐ ω ∂Q.measure,
      c2EnvironmentKernel K 0 ω =
        Kernel.deterministic reduce Probability.measurable_reduce ω := by
    filter_upwards [hK] with ω hω
    exact c2EnvironmentKernel_zero_of_start K ω hω.2.1
  rw [Measure.comp_congr hzero, Measure.deterministic_comp_eq_map]
  rfl

/-- Origin-law uniqueness applies to arbitrary probability kernels on the
physical environment carrier, with one exceptional event for all times. -/
theorem c17_unforced_environment_kernel_ae_unique
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀)
    (hpath : PathwiseAt Q)
    (K K' : Kernel (FieldPair d) (Path d))
    [IsMarkovKernel K] [IsMarkovKernel K']
    (hK : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ ω 0) 0 (K ω))
    (hK' : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ ω 0) 0 (K' ω)) :
    ∀ᵐ ω ∂Q.measure, K ω = K' ω ∧
      ∀ t : ℝ≥0, c2EnvironmentKernel K t ω = c2EnvironmentKernel K' t ω := by
  let Y : QuenchedPathLaws d := K.comap Prod.snd measurable_snd
  let Y' : QuenchedPathLaws d := K'.comap Prod.snd measurable_snd
  have hu := reducedOriginLaw_ae_unique_of_pathwise (hpath := hpath) Q ⟨0, by omega⟩ 0
    Y Y' hK hK'
  filter_upwards [hu] with ω hω
  change K ω = K' ω at hω
  refine ⟨hω, fun t => ?_⟩
  rw [c2EnvironmentKernel_apply, c2EnvironmentKernel_apply, hω]

/-- The annealed marginal is independent of the choice of origin MP kernel. -/
theorem c17_unforced_environment_comp_unique
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀)
    (hpath : PathwiseAt Q)
    (K K' : Kernel (FieldPair d) (Path d))
    [IsMarkovKernel K] [IsMarkovKernel K']
    (hK : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ ω 0) 0 (K ω))
    (hK' : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ ω 0) 0 (K' ω))
    (t : ℝ≥0) :
    c2EnvironmentKernel K t ∘ₘ Q.measure =
      c2EnvironmentKernel K' t ∘ₘ Q.measure := by
  exact Measure.comp_congr
    ((c17_unforced_environment_kernel_ae_unique (hpath := hpath) hd Q K K' hK hK').mono
      fun _ hω => hω.2 t)

/-- The actual horizontal resolvent has its literal spatial weak equation on
one physical full event, before all smooth compact tests. This is a spatial
PDE statement; it does not evaluate a Sobolev representative along MP paths. -/
theorem c17_unforced_resolvent_spatial_equation
    {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d)
    (s : ℝ) (hs : 0 < s) (g : BoundedContinuousFunction (FieldPair d) ℂ) :
    let F := BoundedContinuousFunction.toLp 2 (reducedLaw Q) ℂ g
    let U := unforcedComplexResolvent Q i s hs F
    ∃ G : Fin d → Lp ℂ 2 (reducedLaw Q),
      HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) U G ∧
      ∀ᵐ ω ∂Q.measure,
        ∀ (φ : Vec d → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
          (∫ x, ((s : ℂ) * U (translate x (reduce ω)) -
            g (translate x (reduce ω))) * (φ x : ℂ)) =
              -(1 / 2 : ℂ) * (∫ x, ∑ j,
                (∑ k, ((reduce ω).1 x j k : ℂ) * G k (translate x (reduce ω))) *
                  (coordinateDerivative j φ x : ℂ)) := by
  let : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  dsimp only
  let F := BoundedContinuousFunction.toLp 2 (reducedLaw Q) ℂ g
  let U := unforcedComplexResolvent Q i s hs F
  let H : Lp ℂ 2 (reducedLaw Q) := (s : ℂ) • U - F
  have hgen : IsComplexGeneratorPair Q i 0 U H :=
    unforcedComplexResolvent_spec Q i s hs F
  have htrans := (isComplexTransposeGeneratorPair_zero_iff Q i U H).mpr hgen
  obtain ⟨G, hG, hflux⟩ := htrans.exists_spatial_flux_all_tests
  refine ⟨G, hG, ?_⟩
  have hH : (H : FieldPair d → ℂ) =ᵐ[reducedLaw Q]
      fun ρ => (s : ℂ) * U ρ - g ρ := by
    filter_upwards [Lp.coeFn_sub ((s : ℂ) • U) F,
      Lp.coeFn_smul (s : ℂ) U,
      BoundedContinuousFunction.coeFn_toLp 2 (reducedLaw Q) ℂ g] with ρ hsub hsmul hg
    change (F : FieldPair d → ℂ) ρ = g ρ at hg
    simp only [H, hsub, hsmul, hg, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  have horbit := ae_complex_spatial_orbit_congr (reducedLaw Q) (reducedLaw_stationary Q)
    (Lp.stronglyMeasurable H).measurable
    ((measurable_const.mul (Lp.stronglyMeasurable U).measurable).sub g.continuous.measurable) hH
  have hphysical := (Probability.measurableEmbedding_reduce d).ae_map_iff
    (μ := Q.measure) |>.mp (hflux.and horbit)
  filter_upwards [hphysical] with ω hω
  obtain ⟨hflux, hρ⟩ := hω
  intro φ hφ hφc
  calc
    _ = ∫ x, H (translate x (reduce ω)) * (φ x : ℂ) :=
      integral_congr_ae (hρ.mono fun x hx =>
        congrArg (fun z : ℂ => z * (φ x : ℂ)) hx.symm)
    _ = _ := by simpa only [mul_zero, zero_mul, sub_zero] using hflux φ hφ hφc

/-- Bounded continuous observations of the actual environment have continuous
quenched means in time, without an invariant-measure assumption. -/
theorem c17_continuous_environment_mean
    {d : ℕ} (K : Kernel (FieldPair d) (Path d)) [IsMarkovKernel K]
    (ω : FieldPair d) (g : BoundedContinuousFunction (FieldPair d) ℂ) :
    Continuous (fun t : ℝ =>
      ∫ γ : Path d, g (translate (γ t.toNNReal) (reduce ω)) ∂K ω) := by
  have hg : Continuous (fun x : Vec d => g (translate x (reduce ω))) :=
    g.continuous.comp (Probability.continuous_translate.comp
      (continuous_id.prodMk continuous_const))
  apply continuous_of_dominated (bound := fun _ : Path d => ‖g‖)
  · intro t
    exact (hg.comp (continuous_eval_const t.toNNReal)).aestronglyMeasurable
  · exact fun _ => ae_of_all _ fun γ => g.norm_coe_le_norm _
  · exact integrable_const ‖g‖
  · exact ae_of_all _ fun γ => hg.comp (γ.continuous.comp continuous_real_toNNReal)

/-- The discounted mean in the occupation-resolvent target is a genuine
Bochner integral on every positive-time tail. -/
theorem c17_integrable_discounted_environment_mean
    {d : ℕ} (K : Kernel (FieldPair d) (Path d)) [IsMarkovKernel K]
    (ω : FieldPair d) (g : BoundedContinuousFunction (FieldPair d) ℂ)
    (s : ℝ) (hs : 0 < s) (a : ℝ) :
    IntegrableOn (fun t : ℝ => (Real.exp (-s * t) : ℂ) *
      (∫ γ : Path d, g (translate (γ t.toNNReal) (reduce ω)) ∂K ω))
      (Set.Ioi a) := by
  have hb (t : ℝ) :
      ‖∫ γ : Path d, g (translate (γ t.toNNReal) (reduce ω)) ∂K ω‖ ≤ ‖g‖ := by
    simpa only [probReal_univ, mul_one] using
      norm_integral_le_of_norm_le_const (ae_of_all (K ω) fun γ => g.norm_coe_le_norm _)
  apply ((integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hs) a).mul_const ‖g‖).mono'
    (((Complex.continuous_ofReal.comp
      (Real.continuous_exp.comp (continuous_const.mul continuous_id))).mul
        (c17_continuous_environment_mean K ω g)).aestronglyMeasurable)
  exact ae_of_all _ fun t => by
    change ‖(Real.exp (-s * t) : ℂ) *
      (∫ γ : Path d, g (translate (γ t.toNNReal) (reduce ω)) ∂K ω)‖ ≤
        Real.exp (-s * t) * ‖g‖
    rw [norm_mul, Complex.norm_of_nonneg (Real.exp_nonneg _)]
    exact mul_le_mul_of_nonneg_left (hb t) (Real.exp_nonneg _)

/-- The actual discounted occupation has an explicit exponentially decaying
tail, uniform in the physical environment and the supplied origin kernel. -/
theorem c17_discounted_environment_tail_bound
    {d : ℕ} (K : Kernel (FieldPair d) (Path d)) [IsMarkovKernel K]
    (ω : FieldPair d) (g : BoundedContinuousFunction (FieldPair d) ℂ)
    (s : ℝ) (hs : 0 < s) (a : ℝ) :
    ‖∫ t : ℝ in Set.Ioi a, (Real.exp (-s * t) : ℂ) *
      (∫ γ : Path d, g (translate (γ t.toNNReal) (reduce ω)) ∂K ω)‖ ≤
        Real.exp (-s * a) * ‖g‖ / s := by
  calc
    _ ≤ ∫ t : ℝ in Set.Ioi a, Real.exp (-s * t) * ‖g‖ := by
      refine norm_integral_le_of_norm_le
        ((integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hs) a).mul_const ‖g‖) ?_
      exact ae_of_all _ fun t => by
        rw [norm_mul, Complex.norm_of_nonneg (Real.exp_nonneg _)]
        apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
        simpa only [probReal_univ, mul_one] using
          norm_integral_le_of_norm_le_const
            (ae_of_all (K ω) fun γ => g.norm_coe_le_norm _)
    _ = _ := by
      rw [integral_mul_const, integral_exp_mul_Ioi (neg_lt_zero.mpr hs) a,
        neg_div_neg_eq]
      ring

/-- Finite-horizon occupation means converge to the literal integral appearing
in the desired quenched resolvent identification. -/
theorem c17_discounted_environment_finite_horizon_limit
    {d : ℕ} (K : Kernel (FieldPair d) (Path d)) [IsMarkovKernel K]
    (ω : FieldPair d) (g : BoundedContinuousFunction (FieldPair d) ℂ)
    (s : ℝ) (hs : 0 < s) :
    Filter.Tendsto (fun T : ℝ => ∫ t in (0 : ℝ)..T, (Real.exp (-s * t) : ℂ) *
      (∫ γ : Path d, g (translate (γ t.toNNReal) (reduce ω)) ∂K ω))
      Filter.atTop (𝓝 (∫ t : ℝ in Set.Ioi 0, (Real.exp (-s * t) : ℂ) *
        (∫ γ : Path d, g (translate (γ t.toNNReal) (reduce ω)) ∂K ω))) := by
  exact intervalIntegral_tendsto_integral_Ioi 0
    (c17_integrable_discounted_environment_mean K ω g s hs 0) Filter.tendsto_id

/-- Discounted bounded observations may be integrated in either time-path
order under the actual supplied kernel. -/
theorem c17_discounted_environment_integral_swap
    {d : ℕ} (K : Kernel (FieldPair d) (Path d)) [IsMarkovKernel K]
    (ω : FieldPair d) (g : BoundedContinuousFunction (FieldPair d) ℂ)
    (s : ℝ) (hs : 0 < s) :
    (∫ t : ℝ in Set.Ioi 0, (Real.exp (-s * t) : ℂ) *
      (∫ γ : Path d, g (translate (γ t.toNNReal) (reduce ω)) ∂K ω)) =
      ∫ γ : Path d, (∫ t : ℝ in Set.Ioi 0, (Real.exp (-s * t) : ℂ) *
        g (translate (γ t.toNNReal) (reduce ω))) ∂K ω := by
  have hg : Continuous (fun x : Vec d => g (translate x (reduce ω))) :=
    g.continuous.comp (Probability.continuous_translate.comp
      (continuous_id.prodMk continuous_const))
  have heval : Continuous (fun z : ℝ × Path d => z.2 z.1.toNNReal) :=
    continuous_eval.comp
      (continuous_snd.prodMk (continuous_real_toNNReal.comp continuous_fst))
  have hi : Integrable (fun z : ℝ × Path d => (Real.exp (-s * z.1) : ℂ) *
      g (translate (z.2 z.1.toNNReal) (reduce ω)))
      ((volume.restrict (Set.Ioi 0)).prod (K ω)) := by
    apply (((integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hs) 0).mul_const ‖g‖).comp_fst
      (K ω)).mono'
      (((Complex.continuous_ofReal.comp
        (Real.continuous_exp.comp (continuous_const.mul continuous_fst))).mul
          (hg.comp heval)).aestronglyMeasurable)
    exact ae_of_all _ fun z => by
      change ‖(Real.exp (-s * z.1) : ℂ) *
        g (translate (z.2 z.1.toNNReal) (reduce ω))‖ ≤ Real.exp (-s * z.1) * ‖g‖
      rw [norm_mul, Complex.norm_of_nonneg (Real.exp_nonneg _)]
      exact mul_le_mul_of_nonneg_left (g.norm_coe_le_norm _) (Real.exp_nonneg _)
  calc
    _ = ∫ t : ℝ in Set.Ioi 0, ∫ γ : Path d, (Real.exp (-s * t) : ℂ) *
        g (translate (γ t.toNNReal) (reduce ω)) ∂K ω := by
      simp only [integral_const_mul]
    _ = _ := integral_integral_swap hi

/-- The supplied kernel gives a jointly measurable time-environment mean.
No continuity of the kernel in its environment parameter is required. -/
theorem c17_stronglyMeasurable_environment_mean
    {d : ℕ} (K : Kernel (FieldPair d) (Path d)) [IsSFiniteKernel K]
    (g : BoundedContinuousFunction (FieldPair d) ℂ) :
    StronglyMeasurable (fun z : ℝ × FieldPair d =>
      ∫ γ : Path d, g (translate (γ z.1.toNNReal) (reduce z.2)) ∂K z.2) := by
  let K' : Kernel (ℝ × FieldPair d) (Path d) :=
    K.comap Prod.snd measurable_snd
  have heval : Continuous (fun z : (ℝ × FieldPair d) × Path d =>
      z.2 z.1.1.toNNReal) :=
    continuous_eval.comp (continuous_snd.prodMk
      (continuous_real_toNNReal.comp continuous_fst.fst))
  have hobs : Continuous (fun z : (ℝ × FieldPair d) × Path d =>
      g (translate (z.2 z.1.1.toNNReal) (reduce z.1.2))) :=
    g.continuous.comp (Probability.continuous_translate.comp
      (heval.prodMk (Probability.continuous_reduce.comp continuous_fst.snd)))
  exact hobs.stronglyMeasurable.integral_kernel_prod_right' (κ := K')

/-- Annealed bounded continuous observations have continuous real-time means,
even before the invariant marginal is identified. -/
theorem c17_continuous_annealed_environment_mean
    {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (K : Kernel (FieldPair d) (Path d)) [IsMarkovKernel K]
    (g : BoundedContinuousFunction (FieldPair d) ℂ) :
    Continuous (fun t : ℝ => ∫ ω, ∫ γ : Path d,
      g (translate (γ t.toNNReal) (reduce ω)) ∂K ω ∂Q.measure) := by
  apply continuous_of_dominated (bound := fun _ : FieldPair d => ‖g‖)
  · intro t
    exact ((c17_stronglyMeasurable_environment_mean K g).comp_measurable
      (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  · intro t
    exact ae_of_all _ fun ω => by
      simpa only [probReal_univ, mul_one] using
        norm_integral_le_of_norm_le_const
          (ae_of_all (K ω) fun γ => g.norm_coe_le_norm _)
  · exact integrable_const ‖g‖
  · exact ae_of_all _ fun ω => c17_continuous_environment_mean K ω g

/-- The discounted quenched mean is integrable jointly in time and physical
environment. The bound uses only that the supplied laws are probabilities. -/
theorem c17_integrable_discounted_environment_product
    {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (K : Kernel (FieldPair d) (Path d)) [IsMarkovKernel K]
    (g : BoundedContinuousFunction (FieldPair d) ℂ)
    (s : ℝ) (hs : 0 < s) :
    Integrable (fun z : ℝ × FieldPair d => (Real.exp (-s * z.1) : ℂ) *
      (∫ γ : Path d, g (translate (γ z.1.toNNReal) (reduce z.2)) ∂K z.2))
      ((volume.restrict (Set.Ioi 0)).prod Q.measure) := by
  apply (((integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hs) 0).mul_const ‖g‖).comp_fst
    Q.measure).mono'
    ((((Complex.continuous_ofReal.comp
      (Real.continuous_exp.comp (continuous_const.mul continuous_fst))).stronglyMeasurable).mul
        (c17_stronglyMeasurable_environment_mean K g)).aestronglyMeasurable)
  exact ae_of_all _ fun z => by
    change ‖(Real.exp (-s * z.1) : ℂ) *
      (∫ γ : Path d, g (translate (γ z.1.toNNReal) (reduce z.2)) ∂K z.2)‖ ≤
        Real.exp (-s * z.1) * ‖g‖
    rw [norm_mul, Complex.norm_of_nonneg (Real.exp_nonneg _)]
    apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
    simpa only [probReal_univ, mul_one] using
      norm_integral_le_of_norm_le_const
        (ae_of_all (K z.2) fun γ => g.norm_coe_le_norm _)

/-- The literal discounted occupation admits the annealed Fubini step needed
for the Laplace argument, without presuming its resolvent identification. -/
theorem c17_discounted_annealed_environment_integral_swap
    {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (K : Kernel (FieldPair d) (Path d)) [IsMarkovKernel K]
    (g : BoundedContinuousFunction (FieldPair d) ℂ)
    (s : ℝ) (hs : 0 < s) :
    (∫ t : ℝ in Set.Ioi 0, (Real.exp (-s * t) : ℂ) *
      (∫ ω, ∫ γ : Path d, g (translate (γ t.toNNReal) (reduce ω)) ∂K ω ∂Q.measure)) =
      ∫ ω, (∫ t : ℝ in Set.Ioi 0, (Real.exp (-s * t) : ℂ) *
        (∫ γ : Path d, g (translate (γ t.toNNReal) (reduce ω)) ∂K ω)) ∂Q.measure := by
  calc
    _ = ∫ t : ℝ in Set.Ioi 0, ∫ ω, (Real.exp (-s * t) : ℂ) *
        (∫ γ : Path d, g (translate (γ t.toNNReal) (reduce ω)) ∂K ω) ∂Q.measure := by
      simp only [integral_const_mul]
    _ = _ := integral_integral_swap
      (c17_integrable_discounted_environment_product Q K g s hs)

/-- The mean of the actual horizontal resolvent is the reciprocal parameter
times the mean of its data. This uses its full weak generator equation. -/
theorem c17_integral_unforcedComplexResolvent
    {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d)
    (s : ℝ) (hs : 0 < s) (F : Lp ℂ 2 (reducedLaw Q)) :
    (∫ ρ, unforcedComplexResolvent Q i s hs F ρ ∂reducedLaw Q) =
      (s : ℂ)⁻¹ * ∫ ρ, F ρ ∂reducedLaw Q := by
  let U := unforcedComplexResolvent Q i s hs F
  have heq : (∫ ρ, ((s : ℂ) • U - F) ρ ∂reducedLaw Q) =
      (s : ℂ) * (∫ ρ, U ρ ∂reducedLaw Q) - ∫ ρ, F ρ ∂reducedLaw Q := by
    calc
      _ = ∫ ρ, ((s : ℂ) * U ρ - F ρ) ∂reducedLaw Q := by
        apply integral_congr_ae
        filter_upwards [Lp.coeFn_sub ((s : ℂ) • U) F,
          Lp.coeFn_smul (s : ℂ) U] with ρ hsub hsmul
        simp only [hsub, hsmul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      _ = _ := by
        rw [integral_sub ((integrable_complexLp Q U).const_mul _)
          (integrable_complexLp Q F), integral_const_mul]
  have hzero := (unforcedComplexResolvent_spec Q i s hs F).integral_eq_zero
  change (∫ ρ, ((s : ℂ) • U - F) ρ ∂reducedLaw Q) = 0 at hzero
  rw [heq] at hzero
  exact (eq_inv_mul_iff_mul_eq₀ (Complex.ofReal_ne_zero.mpr hs.ne')).mpr
    (sub_eq_zero.mp hzero)

/-- Pulling back the analytic resolvent to the actual physical environment
retains its mean formula for the bounded data in the occupation target. -/
theorem c17_integral_unforcedComplexResolvent_pullback
    {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d)
    (s : ℝ) (hs : 0 < s) (g : BoundedContinuousFunction (FieldPair d) ℂ) :
    let F := BoundedContinuousFunction.toLp 2 (reducedLaw Q) ℂ g
    let U := unforcedComplexResolvent Q i s hs F
    (∫ ω, U (reduce ω) ∂Q.measure) =
      (s : ℂ)⁻¹ * ∫ ρ, g ρ ∂reducedLaw Q := by
  dsimp only
  let F := BoundedContinuousFunction.toLp 2 (reducedLaw Q) ℂ g
  let U := unforcedComplexResolvent Q i s hs F
  have hmap : (∫ ρ, U ρ ∂reducedLaw Q) = ∫ ω, U (reduce ω) ∂Q.measure :=
    integral_map Probability.measurable_reduce.aemeasurable
      (Lp.stronglyMeasurable U).aestronglyMeasurable
  calc
    _ = ∫ ρ, U ρ ∂reducedLaw Q := hmap.symm
    _ = (s : ℂ)⁻¹ * ∫ ρ, F ρ ∂reducedLaw Q :=
      c17_integral_unforcedComplexResolvent Q i s hs F
    _ = _ := congrArg (fun z : ℂ => (s : ℂ)⁻¹ * z)
      (integral_congr_ae (BoundedContinuousFunction.coeFn_toLp 2 (reducedLaw Q) ℂ g))

/-- Under the two named, announced foundation inputs, averaged occupation
absolute continuity holds for the actual supplied origin kernel. The selected
textbook law is first transferred to the literal reduced generator, and only
then identified with the supplied law by the pathwise uniqueness node. -/
theorem c17_unforced_mp_averaged_occupation_ac
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hpath : PathwiseAt Q)
    (foundation_reduced_textbook_averaged_occupation_ac :
      ∀ (hd : 1 ≤ d) (hΛ : 0 < Λ₀) {ω : FieldPair d}, IsRegular Λ₀ ω →
        ∀ (i : Fin d) (lam : ℝ) {x : Vec d} {P : Measure (Path d)},
          SolvesMartingaleProblem
            (External.Draft.svGenerator (reducedCoefficient ω)
              (forcedDrift (reducedCoefficient ω) i lam)) x P →
          Measure.map (fun z : Path d × ℝ => z.1 z.2.toNNReal)
            (P.prod (volume.restrict (Set.Ioi 0))) ≪ (volume : Measure (Vec d)))
    (K : Kernel (FieldPair d) (Path d))
    (hK : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ ω 0) 0 (K ω)) :
    ∀ᵐ ω ∂Q.measure,
      Measure.map (fun z : Path d × ℝ => z.1 z.2.toNNReal)
        ((K ω).prod (volume.restrict (Set.Ioi 0))) ≪ (volume : Measure (Vec d)) := by
  have hΛ : 0 < Λ₀ := lt_of_lt_of_le zero_lt_one Q.ellipticity_parameter
  let i : Fin d := ⟨0, by omega⟩
  obtain ⟨Y, _, hY⟩ :=
    foundation_reduced_textbook_kernel hΛ i 0
  have hred : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator i ω 0) 0 (Y (0, ω)) := by
    filter_upwards [Q.regular] with ω hω
    exact c16_reduced_solves_of_textbook_and_averaged_occupation hΛ hω i 0
      (hY ω hω)
      (foundation_reduced_textbook_averaged_occupation_ac (by omega) hΛ hω i 0 (hY ω hω))
  let X : QuenchedPathLaws d := K.comap Prod.snd measurable_snd
  have huniq := reducedOriginLaw_ae_unique_of_pathwise (hpath := hpath) Q i 0 X Y hK hred
  filter_upwards [huniq, Q.regular] with ω hωeq hω
  change K ω = Y (0, ω) at hωeq
  rw [hωeq]
  exact foundation_reduced_textbook_averaged_occupation_ac (by omega) hΛ hω i 0 (hY ω hω)

/-- The actual supplied origin law has absolutely continuous averaged occupation in dimension at least two. -/
theorem c17_unforced_mp_averaged_occupation_ac_of_two_le
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hpath : PathwiseAt Q)
    (K : Kernel (FieldPair d) (Path d))
    (hK : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ ω 0) 0 (K ω)) :
    ∀ᵐ ω ∂Q.measure,
      Measure.map (fun z : Path d × ℝ => z.1 z.2.toNNReal)
        ((K ω).prod (volume.restrict (Set.Ioi 0))) ≪ (volume : Measure (Vec d)) := by
  have hΛ : 0 < Λ₀ := lt_of_lt_of_le zero_lt_one Q.ellipticity_parameter
  let i : Fin d := ⟨0, by omega⟩
  obtain ⟨Y, _, hY⟩ :=
    foundation_reduced_textbook_kernel hΛ i 0
  have hred : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator i ω 0) 0 (Y (0, ω)) := by
    filter_upwards [Q.regular] with ω hω
    exact c16_reduced_solves_of_textbook_and_averaged_occupation hΛ hω i 0
      (hY ω hω)
      (foundation_reduced_textbook_averaged_occupation_ac_of_two_le hd hΛ hω i 0 (hY ω hω))
  let X : QuenchedPathLaws d := K.comap Prod.snd measurable_snd
  have huniq := reducedOriginLaw_ae_unique_of_pathwise (hpath := hpath) Q i 0 X Y hK hred
  filter_upwards [huniq, Q.regular] with ω hωeq hω
  change K ω = Y (0, ω) at hωeq
  rw [hωeq]
  exact foundation_reduced_textbook_averaged_occupation_ac_of_two_le hd hΛ hω i 0 (hY ω hω)


/-- Spatial almost-everywhere representatives give the same discounted mean
under an actual path law with averaged occupation absolute continuity. No
pointwise identification of representatives along every path is presumed. -/
theorem c17_discounted_spatial_integral_congr_of_averaged_occupation
    {d : ℕ} (P : Measure (Path d)) [SFinite P]
    (hocc : Measure.map (fun z : Path d × ℝ => z.1 z.2.toNNReal)
      (P.prod (volume.restrict (Set.Ioi 0))) ≪ (volume : Measure (Vec d)))
    {f g : Vec d → ℂ} (hfg : f =ᵐ[(volume : Measure (Vec d))] g) (s : ℝ) :
    (∫ t : ℝ in Set.Ioi 0, (Real.exp (-s * t) : ℂ) *
      (∫ γ : Path d, f (γ t.toNNReal) ∂P)) =
      ∫ t : ℝ in Set.Ioi 0, (Real.exp (-s * t) : ℂ) *
        (∫ γ : Path d, g (γ t.toNNReal) ∂P) := by
  have heval : Measurable (fun z : Path d × ℝ => z.1 z.2.toNNReal) :=
    (continuous_eval.comp
      (continuous_fst.prodMk (continuous_real_toNNReal.comp continuous_snd))).measurable
  have hprod := ae_of_ae_map heval.aemeasurable (hocc.ae_le hfg)
  have hswap : ∀ᵐ t ∂volume.restrict (Set.Ioi (0 : ℝ)),
      ∀ᵐ γ ∂P, f (γ t.toNNReal) = g (γ t.toNNReal) :=
    Measure.ae_ae_of_ae_prod
      ((Measure.measurePreserving_swap
        (μ := volume.restrict (Set.Ioi (0 : ℝ))) (ν := P)).quasiMeasurePreserving.ae hprod)
  apply integral_congr_ae
  filter_upwards [hswap] with t ht
  rw [integral_congr_ae ht]

/-- Averaged occupation absolute continuity is enough to pass uniformly
bounded spatial approximations through the actual discounted occupation.
The spatial convergence need only hold almost everywhere for volume. -/
theorem c17_tendsto_discounted_spatial_integral_of_averaged_occupation
    {d : ℕ} (P : Measure (Path d)) [IsProbabilityMeasure P]
    (hocc : Measure.map (fun z : Path d × ℝ => z.1 z.2.toNNReal)
      (P.prod (volume.restrict (Set.Ioi 0))) ≪ (volume : Measure (Vec d)))
    {f : ℕ → Vec d → ℂ} {g : Vec d → ℂ}
    (hf : ∀ n, Measurable (f n)) (C : ℝ)
    (hbound : ∀ n x, ‖f n x‖ ≤ C)
    (hlim : ∀ᵐ x ∂(volume : Measure (Vec d)),
      Filter.Tendsto (fun n => f n x) Filter.atTop (𝓝 (g x)))
    (s : ℝ) (hs : 0 < s) :
    Filter.Tendsto (fun n => ∫ t : ℝ in Set.Ioi 0,
      (Real.exp (-s * t) : ℂ) * (∫ γ : Path d, f n (γ t.toNNReal) ∂P))
      Filter.atTop (𝓝 (∫ t : ℝ in Set.Ioi 0,
        (Real.exp (-s * t) : ℂ) * (∫ γ : Path d, g (γ t.toNNReal) ∂P))) := by
  have heval : Measurable (fun z : Path d × ℝ => z.1 z.2.toNNReal) :=
    (continuous_eval.comp
      (continuous_fst.prodMk (continuous_real_toNNReal.comp continuous_snd))).measurable
  have hprod := ae_of_ae_map heval.aemeasurable (hocc.ae_le hlim)
  have hswap : ∀ᵐ t ∂volume.restrict (Set.Ioi (0 : ℝ)),
      ∀ᵐ γ ∂P, Filter.Tendsto (fun n => f n (γ t.toNNReal))
        Filter.atTop (𝓝 (g (γ t.toNNReal))) :=
    Measure.ae_ae_of_ae_prod
      ((Measure.measurePreserving_swap
        (μ := volume.restrict (Set.Ioi (0 : ℝ))) (ν := P)).quasiMeasurePreserving.ae hprod)
  have hm (n : ℕ) : StronglyMeasurable
      (fun t : ℝ => ∫ γ : Path d, f n (γ t.toNNReal) ∂P) :=
    ((hf n).comp heval).stronglyMeasurable.integral_prod_left'
  apply tendsto_integral_of_dominated_convergence (fun t => Real.exp (-s * t) * C)
  · intro n
    exact (((Complex.continuous_ofReal.comp
      (Real.continuous_exp.comp (continuous_const.mul continuous_id))).stronglyMeasurable).mul
        (hm n)).aestronglyMeasurable
  · exact (integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hs) 0).mul_const C
  · intro n
    exact ae_of_all _ fun t => by
      rw [norm_mul, Complex.norm_of_nonneg (Real.exp_nonneg _)]
      apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
      simpa only [probReal_univ, mul_one] using
        norm_integral_le_of_norm_le_const (ae_of_all P fun γ => hbound n (γ t.toNNReal))
  · filter_upwards [hswap] with t ht
    apply Filter.Tendsto.mul tendsto_const_nhds
    exact tendsto_integral_of_dominated_convergence (fun _ : Path d => C)
      (fun n => ((hf n).comp (continuous_eval_const t.toNNReal).measurable).aestronglyMeasurable)
      (integrable_const C) (fun n => ae_of_all P fun γ => hbound n (γ t.toNNReal)) ht

/-- Laplace integration of a bounded measurable primitive, proved by
Fubini on the positive-time triangle. No continuity of the integrand is needed. -/
theorem c17_laplace_integral_primitive {g : ℝ → ℝ} (hg : Measurable g)
    (C : ℝ) (hC : ∀ t, ‖g t‖ ≤ C) (s : ℝ) (hs : 0 < s) :
    (∫ T : ℝ in Set.Ioi 0, Real.exp (-s * T) * (∫ u in (0 : ℝ)..T, g u)) =
      (∫ u : ℝ in Set.Ioi 0, Real.exp (-s * u) * g u) / s := by
  let H : ℝ × ℝ → ℝ := fun z =>
    if z.2 < z.1 then Real.exp (-s * z.1) * g z.2 else 0
  have hexp := integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hs) (0 : ℝ)
  have hslice (u a : ℝ) (hu : 0 < u) :
      (∫ T : ℝ in Set.Ioi 0, if u < T then Real.exp (-s * T) * a else 0) =
        Real.exp (-s * u) / s * a := by
    change (∫ T : ℝ in Set.Ioi 0,
      (Set.Ioi u).indicator (fun T => Real.exp (-s * T) * a) T) = _
    rw [setIntegral_indicator measurableSet_Ioi,
      Set.inter_eq_right.mpr (Set.Ioi_subset_Ioi hu.le), integral_mul_const,
      integral_exp_mul_Ioi (neg_lt_zero.mpr hs) u, neg_div_neg_eq]
  have hm : Measurable H :=
    Measurable.ite (measurableSet_lt measurable_snd measurable_fst)
      ((Real.continuous_exp.measurable.comp
        (measurable_const.mul measurable_fst)).mul (hg.comp measurable_snd)) measurable_const
  have hi : Integrable H
      ((volume.restrict (Set.Ioi 0)).prod (volume.restrict (Set.Ioi 0))) := by
    apply (integrable_prod_iff' hm.aestronglyMeasurable).mpr
    constructor
    · exact ae_of_all _ fun u => by
        change Integrable ((Set.Ioi u).indicator
          (fun T => Real.exp (-s * T) * g u)) _
        exact (hexp.mul_const (g u)).indicator measurableSet_Ioi
    · have heq : (fun u => ∫ T : ℝ in Set.Ioi 0, ‖H (T, u)‖) =ᵐ[
          volume.restrict (Set.Ioi 0)] fun u => Real.exp (-s * u) / s * ‖g u‖ := by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
        have hn (T : ℝ) : ‖H (T, u)‖ =
            if u < T then Real.exp (-s * T) * ‖g u‖ else 0 := by
          dsimp only [H]
          split_ifs <;> simp only [norm_mul, Real.norm_of_nonneg (Real.exp_nonneg _), norm_zero]
        simp_rw [hn]
        exact hslice u ‖g u‖ hu
      apply Integrable.congr _ heq.symm
      apply (hexp.mul_const (C / s)).mono'
        (((Real.continuous_exp.measurable.comp
          (measurable_const.mul measurable_id)).div_const s).mul hg.norm).aestronglyMeasurable
      exact ae_of_all _ fun u => by
        change ‖Real.exp (-s * u) / s * ‖g u‖‖ ≤ Real.exp (-s * u) * (C / s)
        rw [norm_mul, Real.norm_of_nonneg (div_nonneg (Real.exp_nonneg _) hs.le),
          norm_norm]
        calc
          Real.exp (-s * u) / s * ‖g u‖ ≤ Real.exp (-s * u) / s * C :=
            mul_le_mul_of_nonneg_left (hC u) (div_nonneg (Real.exp_nonneg _) hs.le)
          _ = Real.exp (-s * u) * (C / s) := by ring
  calc
    _ = ∫ T : ℝ in Set.Ioi 0, ∫ u : ℝ in Set.Ioi 0, H (T, u) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro T hT
      change _ = ∫ u : ℝ in Set.Ioi 0,
        (Set.Iio T).indicator (fun u => Real.exp (-s * T) * g u) u
      dsimp only
      rw [setIntegral_indicator measurableSet_Iio, Set.Ioi_inter_Iio,
        integral_const_mul, intervalIntegral.integral_of_le hT.le,
        integral_Ioc_eq_integral_Ioo]
    _ = ∫ u : ℝ in Set.Ioi 0, ∫ T : ℝ in Set.Ioi 0, H (T, u) :=
      integral_integral_swap hi
    _ = ∫ u : ℝ in Set.Ioi 0, Real.exp (-s * u) / s * g u := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro u hu
      exact hslice u (g u) hu
    _ = _ := by simp only [div_mul_eq_mul_div, integral_div]

/-- The literal compact-test generator of the supplied martingale law
satisfies the discounted Dynkin identity, without an occupation-density input. -/
theorem c17_discounted_sv_dynkin {d : ℕ} {Λ₀ : ℝ}
    (hΛ : 0 < Λ₀) {ω : FieldPair d} (hω : IsRegular Λ₀ ω)
    (i : Fin d) (lam : ℝ) {x : Vec d} {P : Measure (Path d)}
    (hP : SolvesMartingaleProblem
      (External.Draft.svGenerator (reducedCoefficient ω)
        (forcedDrift (reducedCoefficient ω) i lam)) x P)
    {f : Vec d → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f)
    (s : ℝ) (hs : 0 < s) :
    (∫ t : ℝ in Set.Ioi 0, Real.exp (-s*t) *
      (∫ γ : Path d, External.Draft.svGenerator (reducedCoefficient ω)
        (forcedDrift (reducedCoefficient ω) i lam) f (γ t.toNNReal) ∂P)) =
      s * (∫ t : ℝ in Set.Ioi 0, Real.exp (-s*t) *
        (∫ γ : Path d, f (γ t.toNNReal) ∂P)) - f x := by
  let _ : IsProbabilityMeasure P := hP.1
  let L := External.Draft.svGenerator (reducedCoefficient ω)
    (forcedDrift (reducedCoefficient ω) i lam)
  let F : ℝ → ℝ := fun t => ∫ γ : Path d, f (γ t.toNNReal) ∂P
  let G : ℝ → ℝ := fun t => ∫ γ : Path d, L f (γ t.toNNReal) ∂P
  obtain ⟨hA, _, ⟨Ma, hAb⟩, _, hb, ⟨Mb, hbb⟩⟩ := reduced_svHypotheses hΛ hω i lam
  have hcoef : BddCoef (reducedCoefficient ω)
      (forcedDrift (reducedCoefficient ω) i lam) (max Ma Mb) :=
    ⟨fun k j => (hA.matrix_elem k j).measurable,
      fun k => (measurable_pi_apply k).comp hb,
      fun y k j => (hAb y k j).trans (le_max_left _ _),
      fun y k => (hbb y k).trans (le_max_right _ _)⟩
  have hLg : Measurable (L f) := hcoef.measurable_gen f
  obtain ⟨Cg, hCg⟩ := bounded_svGenerator _ _ hAb hbb (contDiff_two_of_top hf) hc
  obtain ⟨Cf, hCf⟩ := hf.continuous.bounded_above_of_compact_support hc
  have heval : Measurable (fun z : ℝ × Path d => z.2 z.1.toNNReal) :=
    (continuous_eval.comp
      (continuous_snd.prodMk (continuous_real_toNNReal.comp continuous_fst))).measurable
  have hFm : Measurable F :=
    ((hf.continuous.measurable.comp heval).stronglyMeasurable.integral_prod_right').measurable
  have hGm : Measurable G :=
    ((hLg.comp heval).stronglyMeasurable.integral_prod_right').measurable
  have hFb (t : ℝ) : ‖F t‖ ≤ Cf := by
    simpa only [F, probReal_univ, mul_one] using
      norm_integral_le_of_norm_le_const (ae_of_all P fun γ => hCf (γ t.toNNReal))
  have hGb (t : ℝ) : ‖G t‖ ≤ Cg := by
    apply (norm_integral_le_of_norm_le_const (ae_of_all P fun γ =>
      show ‖L f (γ t.toNNReal)‖ ≤ Cg from hCg (γ t.toNNReal))).trans_eq
    simp only [probReal_univ, mul_one]
  have hfinite (T : ℝ) (hT : 0 < T) :
      (∫ u in (0 : ℝ)..T, G u) = F T - f x := by
    have hi : Integrable (fun z : ℝ × Path d => L f (z.2 z.1.toNNReal))
        ((volume.restrict (Set.Ioc 0 T)).prod P) :=
      Integrable.of_bound (hLg.comp heval).aestronglyMeasurable Cg
        (ae_of_all _ fun z => hCg (z.2 z.1.toNNReal))
    rw [intervalIntegral.integral_of_le hT.le]
    calc
      _ = ∫ γ : Path d, (∫ u : ℝ in Set.Ioc 0 T, L f (γ u.toNNReal)) ∂P :=
        integral_integral_swap hi
      _ = F T - f x := by
        have h := (c16_integral_generator_eq_sub hP hf hc T.toNNReal).2
        simpa only [Real.toNNReal_of_nonneg hT.le, NNReal.coe_mk,
          intervalIntegral.integral_of_le hT.le, F, L] using h
  have hexp := integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hs) (0 : ℝ)
  have hFi : IntegrableOn (fun t => Real.exp (-s * t) * F t) (Set.Ioi 0) := by
    apply (hexp.mul_const Cf).mono'
      ((Real.continuous_exp.measurable.comp
        (measurable_const.mul measurable_id)).mul hFm).aestronglyMeasurable
    exact ae_of_all _ fun t => by
      change ‖Real.exp (-s * t) * F t‖ ≤ Real.exp (-s * t) * Cf
      rw [norm_mul, Real.norm_of_nonneg (Real.exp_nonneg _)]
      exact mul_le_mul_of_nonneg_left (hFb t) (Real.exp_nonneg _)
  have heq : (∫ T : ℝ in Set.Ioi 0, Real.exp (-s * T) * (F T - f x)) =
      (∫ t : ℝ in Set.Ioi 0, Real.exp (-s * t) * G t) / s := by
    calc
      _ = ∫ T : ℝ in Set.Ioi 0, Real.exp (-s * T) * (∫ u in (0 : ℝ)..T, G u) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro T hT
        dsimp only
        rw [hfinite T hT]
      _ = _ := c17_laplace_integral_primitive hGm Cg hGb s hs
  simp_rw [mul_sub] at heq
  rw [integral_sub hFi (hexp.mul_const (f x)), integral_mul_const,
    integral_exp_mul_Ioi (neg_lt_zero.mpr hs) 0] at heq
  simp only [mul_zero, Real.exp_zero, neg_div_neg_eq] at heq
  have h := (eq_div_iff hs.ne').mp heq
  change (∫ t : ℝ in Set.Ioi 0, Real.exp (-s * t) * G t) =
    s * (∫ t : ℝ in Set.Ioi 0, Real.exp (-s * t) * F t) - f x
  have hcancel : (1 / s * f x) * s = f x := by field_simp
  rw [sub_mul, hcancel] at h
  linarith only [h]

/-- The discounted observation is jointly measurable for the actual physical
environment and path. This is independent of occupation estimates. -/
theorem c17_measurable_discounted_occupation_integrand {d : ℕ}
    (r : FieldPair d → ℝ) (hr : Measurable r) (s : ℝ) :
    Measurable (fun p : ℝ × (FieldPair d × Path d) =>
      Real.exp (-s * p.1) *
        |r (translate (p.2.2 p.1.toNNReal) (reduce p.2.1))|) := by
  have heval : Continuous (fun p : ℝ × (FieldPair d × Path d) =>
      p.2.2 p.1.toNNReal) :=
    continuous_eval.comp (continuous_snd.snd.prodMk
      (continuous_real_toNNReal.comp continuous_fst))
  have henv : Measurable (fun p : ℝ × (FieldPair d × Path d) =>
      translate (p.2.2 p.1.toNNReal) (reduce p.2.1)) :=
    (Probability.continuous_translate.comp
      (heval.prodMk (Probability.continuous_reduce.comp continuous_snd.fst))).measurable
  exact ((Real.continuous_exp.comp (continuous_const.mul continuous_fst)).measurable).mul
    (continuous_abs.measurable.comp (hr.comp henv))

/-- Bounded measurable observations have finite discounted occupation under
the supplied environment-path law. -/
theorem c17_integrable_discounted_occupation_of_bounded
    {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (K : Kernel (FieldPair d) (Path d)) [IsMarkovKernel K]
    (r : FieldPair d → ℝ) (hr : Measurable r) (B : ℝ)
    (hB : ∀ w, |r w| ≤ B) (s : ℝ) (hs : 0 < s) :
    Integrable (fun p : ℝ × (FieldPair d × Path d) =>
      Real.exp (-s * p.1) * |r (translate (p.2.2 p.1.toNNReal) (reduce p.2.1))|)
      ((volume.restrict (Set.Ioi 0)).prod (Q.measure ⊗ₘ K)) := by
  let : IsProbabilityMeasure Q.measure := Q.probability
  apply (((integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hs) 0).mul_const B).comp_fst
    (Q.measure ⊗ₘ K)).mono'
    (c17_measurable_discounted_occupation_integrand r hr s).aestronglyMeasurable
  exact ae_of_all _ fun p => by
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_nonneg _) (abs_nonneg _))]
    exact mul_le_mul_of_nonneg_left (hB _) (Real.exp_nonneg _)

/-- The annealed mean of a bounded observation is uniformly bounded. -/
theorem c17_norm_annealed_environment_mean_le
    {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (K : Kernel (FieldPair d) (Path d)) [IsMarkovKernel K]
    (g : BoundedContinuousFunction (FieldPair d) ℂ) (t : ℝ) :
    ‖∫ ω, ∫ γ : Path d,
      g (translate (γ t.toNNReal) (reduce ω)) ∂K ω ∂Q.measure‖ ≤ ‖g‖ := by
  simpa only [probReal_univ, mul_one] using
    norm_integral_le_of_norm_le_const (ae_of_all Q.measure fun ω => by
      simpa only [probReal_univ, mul_one] using
        norm_integral_le_of_norm_le_const
          (ae_of_all (K ω) fun γ => g.norm_coe_le_norm _))

/-- A Laplace identity for the supplied process determines its annealed means. -/
theorem c17_unforced_annealed_mean_of_laplace
    {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (K : Kernel (FieldPair d) (Path d)) [IsMarkovKernel K]
    (g : BoundedContinuousFunction (FieldPair d) ℂ)
    (c17_unforced_annealed_laplace : ∀ (s : ℝ), 0 < s →
      (∫ t : ℝ in Set.Ioi 0, (Real.exp (-s * t) : ℂ) *
        (∫ ω, ∫ γ : Path d,
          g (translate (γ t.toNNReal) (reduce ω)) ∂K ω ∂Q.measure)) =
        (s : ℂ)⁻¹ * ∫ ω, g ω ∂reducedLaw Q) :
    ∀ t : ℝ≥0, (∫ ω, ∫ γ : Path d,
      g (translate (γ t) (reduce ω)) ∂K ω ∂Q.measure) =
      ∫ ω, g ω ∂reducedLaw Q := by
  let F : ℝ → ℂ := fun t => ∫ ω, ∫ γ : Path d,
    g (translate (γ t.toNNReal) (reduce ω)) ∂K ω ∂Q.measure
  let c : ℂ := ∫ ω, g ω ∂reducedLaw Q
  have hF : Continuous F := c17_continuous_annealed_environment_mean Q K g
  have hb : ∀ t, ‖F t - c‖ ≤ ‖g‖ + ‖c‖ := fun t =>
    (norm_sub_le _ _).trans (add_le_add (c17_norm_annealed_environment_mean_le Q K g t) le_rfl)
  have hi (s : ℝ) (hs : 0 < s) : IntegrableOn
      (fun t => (Real.exp (-s * t) : ℂ) * (F t - c)) (Set.Ioi 0) := by
    apply (((integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hs) 0).mul_const
      (‖g‖ + ‖c‖))).mono'
      (((Complex.continuous_ofReal.comp (Real.continuous_exp.comp
        (continuous_const.mul continuous_id))).mul (hF.sub continuous_const)).aestronglyMeasurable)
    exact ae_of_all _ fun t => by
      change ‖(Real.exp (-s * t) : ℂ) * (F t - c)‖ ≤ _
      rw [norm_mul, Complex.norm_of_nonneg (Real.exp_nonneg _)]
      exact mul_le_mul_of_nonneg_left (hb t) (Real.exp_nonneg _)
  have hz (s : ℝ) (hs : 0 < s) :
      ∫ t : ℝ in Set.Ioi 0, (Real.exp (-s * t) : ℂ) * (F t - c) = 0 := by
    have hconst : (∫ t : ℝ in Set.Ioi 0, (Real.exp (-s * t) : ℂ) * c) =
        (s : ℂ)⁻¹ * c := by
      rw [integral_mul_const, integral_complex_ofReal, integral_exp_mul_Ioi (neg_lt_zero.mpr hs) 0]
      simp [Complex.ofReal_div, Complex.ofReal_neg]
    have hfi : IntegrableOn (fun t => (Real.exp (-s * t) : ℂ) * F t) (Set.Ioi 0) := by
      apply (((integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hs) 0).mul_const ‖g‖)).mono'
        (((Complex.continuous_ofReal.comp (Real.continuous_exp.comp
          (continuous_const.mul continuous_id))).mul hF).aestronglyMeasurable)
      exact ae_of_all _ fun t => by
        change ‖(Real.exp (-s * t) : ℂ) * F t‖ ≤ _
        rw [norm_mul, Complex.norm_of_nonneg (Real.exp_nonneg _)]
        exact mul_le_mul_of_nonneg_left (c17_norm_annealed_environment_mean_le Q K g t)
          (Real.exp_nonneg _)
    have hci : IntegrableOn (fun t => (Real.exp (-s * t) : ℂ) * c) (Set.Ioi 0) := by
      exact (Complex.ofRealCLM.integrable_comp (integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hs) 0)).mul_const c
    simp_rw [mul_sub]
    rw [integral_sub hfi hci, hconst, c17_unforced_annealed_laplace s hs, sub_self]
  have hre : ∀ t : ℝ, 0 ≤ t → (F t - c).re = 0 := by
    apply SubdiffusiveProcess.E7.laplace_unique ((Complex.continuous_re.comp (hF.sub continuous_const)))
      (C := ‖g‖ + ‖c‖)
    · intro t
      exact (Complex.abs_re_le_norm _).trans (hb t)
    · intro n hn
      have hs : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
      have h := integral_re (hi n hs)
      change (∫ t : ℝ in Set.Ioi 0, ((Real.exp (-(n : ℝ) * t) : ℂ) * (F t - c)).re) = _ at h
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at h
      change (∫ t : ℝ in Set.Ioi 0, Real.exp (-(n : ℝ) * t) * (F t - c).re) = 0
      rw [h, hz n hs]
      rfl
  have him : ∀ t : ℝ, 0 ≤ t → (F t - c).im = 0 := by
    apply SubdiffusiveProcess.E7.laplace_unique ((Complex.continuous_im.comp (hF.sub continuous_const)))
      (C := ‖g‖ + ‖c‖)
    · intro t
      exact (Complex.abs_im_le_norm _).trans (hb t)
    · intro n hn
      have hs : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
      have h := integral_im (hi n hs)
      change (∫ t : ℝ in Set.Ioi 0, ((Real.exp (-(n : ℝ) * t) : ℂ) * (F t - c)).im) = _ at h
      simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, zero_add, add_zero] at h
      change (∫ t : ℝ in Set.Ioi 0, Real.exp (-(n : ℝ) * t) * (F t - c).im) = 0
      rw [h, hz n hs]
      rfl
  intro t
  have h : F t - c = 0 := Complex.ext (hre t t.coe_nonneg) (him t t.coe_nonneg)
  simpa [F, c] using sub_eq_zero.mp h

/-- Uniformly bounded first and second coordinate derivatives give a bounded
Stroock–Varadhan generator for bounded coefficients. -/
theorem c17_bounded_svGenerator_of_bounded_derivatives {d : ℕ}
    (A : Vec d → Mat d) (b : Vec d → Vec d) {M1 M2 M : ℝ}
    (hA : ∀ x i j, |A x i j| ≤ M1) (hb : ∀ x i, |b x i| ≤ M2)
    (f : Vec d → ℝ)
    (hf1 : ∀ x j, |coordinateDerivative j f x| ≤ M)
    (hf2 : ∀ x j k, |coordinateDerivative k (coordinateDerivative j f) x| ≤ M) :
    ∃ C : ℝ, ∀ x, |External.Draft.svGenerator A b f x| ≤ C := by
  refine ⟨(1 / 2 : ℝ) * ∑ i : Fin d, ∑ j : Fin d, M1 * M +
    ∑ i : Fin d, M2 * M, fun x => ?_⟩
  unfold External.Draft.svGenerator
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [abs_mul]
    have hderiv := hf2 x j i
    unfold coordinateDerivative at hderiv
    exact mul_le_mul (hA x i j) hderiv
      (abs_nonneg _) ((abs_nonneg _).trans (hA x i j))
  · refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [abs_mul]
    exact mul_le_mul (hb x i) (by simpa only [coordinateDerivative] using hf1 x i)
      (abs_nonneg _) ((abs_nonneg _).trans (hb x i))

/-- Finite-time Dynkin identity for bounded C² tests of the supplied law. -/
theorem c17_reduced_bounded_C2_dynkin {d : ℕ} {Λ₀ : ℝ}
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
      (∫ γ : Path d, f (γ T) ∂P) - f x := by
  letI : IsProbabilityMeasure P := hP.1
  let A := reducedCoefficient ω
  let b := forcedDrift A i 0
  let L := External.Draft.svGenerator A b
  obtain ⟨hA, _, ⟨Ma, hAb⟩, _, hbm, ⟨Mb, hbb⟩⟩ := reduced_svHypotheses hΛ hω i 0
  obtain ⟨M, hM, hfbd⟩ := hb
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

/-- Horizontal test orbits have uniformly bounded derivatives through order two. -/
theorem c17_horizontal_test_bounded_C2 {d : ℕ} (F : FieldPair d → ℝ)
    (hF : IsHorizontalTest F) (w : FieldPair d) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ y : Vec d, |orbit F w y| ≤ M ∧
      (∀ j : Fin d, |coordinateDerivative j (orbit F w) y| ≤ M) ∧
      ∀ j k : Fin d, |coordinateDerivative k (coordinateDerivative j (orbit F w)) y| ≤ M := by
  obtain ⟨B0, hB0, hval⟩ := hF.bound_orbit
  have hfirst : ∀ j : Fin d, ∃ B : ℝ, ∀ w y,
      |coordinateDerivative j (orbit F w) y| ≤ B := by
    intro j
    simpa only [coordinateIterate] using hF.2.2 [j]
  have hsecond : ∀ j k : Fin d, ∃ B : ℝ, ∀ w y,
      |coordinateDerivative k (coordinateDerivative j (orbit F w)) y| ≤ B := by
    intro j k
    simpa only [coordinateIterate] using hF.2.2 [k, j]
  choose B1 hB1 using hfirst
  choose B2 hB2 using hsecond
  let M : ℝ := B0 + (∑ j, |B1 j|) + ∑ j, ∑ k, |B2 j k|
  have hs1 : 0 ≤ ∑ j, |B1 j| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hs2 : 0 ≤ ∑ j, ∑ k, |B2 j k| :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hj (j : Fin d) : |B1 j| ≤ ∑ j, |B1 j| :=
    Finset.single_le_sum (f := fun j : Fin d => |B1 j|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
  have hjk (j k : Fin d) : |B2 j k| ≤ ∑ j, ∑ k, |B2 j k| :=
    (Finset.single_le_sum (f := fun k : Fin d => |B2 j k|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ k)).trans
      (Finset.single_le_sum (f := fun j : Fin d => ∑ k, |B2 j k|)
        (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _)
        (Finset.mem_univ j))
  refine ⟨M, by dsimp [M]; linarith, fun y => ⟨?_, ?_, ?_⟩⟩
  · dsimp [M]; linarith [hval w y]
  · intro j
    dsimp [M]; linarith [hB1 j w y, le_abs_self (B1 j), hj j]
  · intro j k
    dsimp [M]; linarith [hB2 j k w y, le_abs_self (B2 j k), hjk j k]


/-- The orbit of a horizontal test satisfies the bounded C² hypotheses of
finite-time Dynkin's formula for the actual supplied law. -/
theorem c17_horizontal_test_dynkin {d : ℕ} {Λ₀ : ℝ}
    (hΛ : 0 < Λ₀) {ω : FieldPair d} (hω : IsRegular Λ₀ ω)
    (i : Fin d) {x : Vec d} {P : Measure (Path d)}
    (hP : SolvesMartingaleProblem (External.Draft.svGenerator
      (reducedCoefficient ω) (forcedDrift (reducedCoefficient ω) i 0)) x P)
    (F : FieldPair d → ℝ) (hF : IsHorizontalTest F) (T : ℝ≥0) :
    Integrable (fun γ : Path d => ∫ u in Set.Ioc (0 : ℝ) (T : ℝ),
      External.Draft.svGenerator (reducedCoefficient ω)
        (forcedDrift (reducedCoefficient ω) i 0) (orbit F (reduce ω)) (γ u.toNNReal)) P ∧
    (∫ γ : Path d, (∫ u in Set.Ioc (0 : ℝ) (T : ℝ),
      External.Draft.svGenerator (reducedCoefficient ω)
        (forcedDrift (reducedCoefficient ω) i 0) (orbit F (reduce ω)) (γ u.toNNReal)) ∂P) =
      (∫ γ : Path d, orbit F (reduce ω) (γ T) ∂P) - orbit F (reduce ω) x := by
  exact c17_reduced_bounded_C2_dynkin hΛ hω i hP (orbit F (reduce ω))
    (contDiff_two_of_top (hF.2.1 (reduce ω)))
    (c17_horizontal_test_bounded_C2 F hF (reduce ω)) T

/-- Discounted Dynkin identity for the actual law and bounded C² tests. -/
theorem c17_discounted_bounded_C2_dynkin {d : ℕ} {Λ₀ : ℝ}
    (hΛ : 0 < Λ₀) {ω : FieldPair d} (hω : IsRegular Λ₀ ω)
    (i : Fin d) {x : Vec d} {P : Measure (Path d)}
    (hP : SolvesMartingaleProblem
      (External.Draft.svGenerator (reducedCoefficient ω)
        (forcedDrift (reducedCoefficient ω) i 0)) x P)
    {f : Vec d → ℝ} (hf : ContDiff ℝ 2 f)
    (hbnd : ∃ M : ℝ, 0 ≤ M ∧ ∀ y : Vec d, |f y| ≤ M ∧
      (∀ j : Fin d, |coordinateDerivative j f y| ≤ M) ∧
      ∀ j k : Fin d, |coordinateDerivative k (coordinateDerivative j f) y| ≤ M)
    (s : ℝ) (hs : 0 < s) :
    (∫ t : ℝ in Set.Ioi 0, Real.exp (-s*t) *
      (∫ γ : Path d, External.Draft.svGenerator (reducedCoefficient ω)
        (forcedDrift (reducedCoefficient ω) i 0) f (γ t.toNNReal) ∂P)) =
      s * (∫ t : ℝ in Set.Ioi 0, Real.exp (-s*t) *
        (∫ γ : Path d, f (γ t.toNNReal) ∂P)) - f x := by
  let _ : IsProbabilityMeasure P := hP.1
  let L := External.Draft.svGenerator (reducedCoefficient ω)
    (forcedDrift (reducedCoefficient ω) i 0)
  let F : ℝ → ℝ := fun t => ∫ γ : Path d, f (γ t.toNNReal) ∂P
  let G : ℝ → ℝ := fun t => ∫ γ : Path d, L f (γ t.toNNReal) ∂P
  obtain ⟨hA, _, ⟨Ma, hAb⟩, _, hb, ⟨Mb, hbb⟩⟩ := reduced_svHypotheses hΛ hω i 0
  have hcoef : BddCoef (reducedCoefficient ω)
      (forcedDrift (reducedCoefficient ω) i 0) (max Ma Mb) :=
    ⟨fun k j => (hA.matrix_elem k j).measurable,
      fun k => (measurable_pi_apply k).comp hb,
      fun y k j => (hAb y k j).trans (le_max_left _ _),
      fun y k => (hbb y k).trans (le_max_right _ _)⟩
  have hLg : Measurable (L f) := hcoef.measurable_gen f
  obtain ⟨Cf, hCf0, hCf⟩ := hbnd
  obtain ⟨Cg, hCg⟩ := c17_bounded_svGenerator_of_bounded_derivatives _ _ hAb hbb f
    (fun y j => (hCf y).2.1 j) (fun y j k => (hCf y).2.2 j k)
  have heval : Measurable (fun z : ℝ × Path d => z.2 z.1.toNNReal) :=
    (continuous_eval.comp
      (continuous_snd.prodMk (continuous_real_toNNReal.comp continuous_fst))).measurable
  have hFm : Measurable F :=
    ((hf.continuous.measurable.comp heval).stronglyMeasurable.integral_prod_right').measurable
  have hGm : Measurable G :=
    ((hLg.comp heval).stronglyMeasurable.integral_prod_right').measurable
  have hFb (t : ℝ) : ‖F t‖ ≤ Cf := by
    simpa only [F, probReal_univ, mul_one] using
      norm_integral_le_of_norm_le_const (ae_of_all P fun γ => by simpa only [Real.norm_eq_abs] using (hCf (γ t.toNNReal)).1)
  have hGb (t : ℝ) : ‖G t‖ ≤ Cg := by
    apply (norm_integral_le_of_norm_le_const (ae_of_all P fun γ =>
      show ‖L f (γ t.toNNReal)‖ ≤ Cg from hCg (γ t.toNNReal))).trans_eq
    simp only [probReal_univ, mul_one]
  have hfinite (T : ℝ) (hT : 0 < T) :
      (∫ u in (0 : ℝ)..T, G u) = F T - f x := by
    have hi : Integrable (fun z : ℝ × Path d => L f (z.2 z.1.toNNReal))
        ((volume.restrict (Set.Ioc 0 T)).prod P) :=
      Integrable.of_bound (hLg.comp heval).aestronglyMeasurable Cg
        (ae_of_all _ fun z => hCg (z.2 z.1.toNNReal))
    rw [intervalIntegral.integral_of_le hT.le]
    calc
      _ = ∫ γ : Path d, (∫ u : ℝ in Set.Ioc 0 T, L f (γ u.toNNReal)) ∂P :=
        integral_integral_swap hi
      _ = F T - f x := by
        have h := (c17_reduced_bounded_C2_dynkin hΛ hω i hP f hf ⟨Cf, hCf0, hCf⟩ T.toNNReal).2
        simpa only [Real.toNNReal_of_nonneg hT.le, NNReal.coe_mk,
          F, L] using h
  have hexp := integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hs) (0 : ℝ)
  have hFi : IntegrableOn (fun t => Real.exp (-s * t) * F t) (Set.Ioi 0) := by
    apply (hexp.mul_const Cf).mono'
      ((Real.continuous_exp.measurable.comp
        (measurable_const.mul measurable_id)).mul hFm).aestronglyMeasurable
    exact ae_of_all _ fun t => by
      change ‖Real.exp (-s * t) * F t‖ ≤ Real.exp (-s * t) * Cf
      rw [norm_mul, Real.norm_of_nonneg (Real.exp_nonneg _)]
      exact mul_le_mul_of_nonneg_left (hFb t) (Real.exp_nonneg _)
  have heq : (∫ T : ℝ in Set.Ioi 0, Real.exp (-s * T) * (F T - f x)) =
      (∫ t : ℝ in Set.Ioi 0, Real.exp (-s * t) * G t) / s := by
    calc
      _ = ∫ T : ℝ in Set.Ioi 0, Real.exp (-s * T) * (∫ u in (0 : ℝ)..T, G u) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro T hT
        dsimp only
        rw [hfinite T hT]
      _ = _ := c17_laplace_integral_primitive hGm Cg hGb s hs
  simp_rw [mul_sub] at heq
  rw [integral_sub hFi (hexp.mul_const (f x)), integral_mul_const,
    integral_exp_mul_Ioi (neg_lt_zero.mpr hs) 0] at heq
  simp only [mul_zero, Real.exp_zero, neg_div_neg_eq] at heq
  have h := (eq_div_iff hs.ne').mp heq
  change (∫ t : ℝ in Set.Ioi 0, Real.exp (-s * t) * G t) =
    s * (∫ t : ℝ in Set.Ioi 0, Real.exp (-s * t) * F t) - f x
  have hcancel : (1 / s * f x) * s = f x := by field_simp
  rw [sub_mul, hcancel] at h
  linarith only [h]

/-- Discounted Dynkin identity for horizontal test orbits under the supplied law. -/
theorem c17_discounted_horizontal_test_dynkin {d : ℕ} {Λ₀ : ℝ}
    (hΛ : 0 < Λ₀) {ω : FieldPair d} (hω : IsRegular Λ₀ ω)
    (i : Fin d) {x : Vec d} {P : Measure (Path d)}
    (hP : SolvesMartingaleProblem (External.Draft.svGenerator
      (reducedCoefficient ω) (forcedDrift (reducedCoefficient ω) i 0)) x P)
    (F : FieldPair d → ℝ) (hF : IsHorizontalTest F) (s : ℝ) (hs : 0 < s) :
    (∫ t : ℝ in Set.Ioi 0, Real.exp (-s*t) *
      (∫ γ : Path d, External.Draft.svGenerator (reducedCoefficient ω)
        (forcedDrift (reducedCoefficient ω) i 0) (orbit F (reduce ω))
          (γ t.toNNReal) ∂P)) =
      s * (∫ t : ℝ in Set.Ioi 0, Real.exp (-s*t) *
        (∫ γ : Path d, orbit F (reduce ω) (γ t.toNNReal) ∂P)) -
          orbit F (reduce ω) x :=
  c17_discounted_bounded_C2_dynkin hΛ hω i hP
    (contDiff_two_of_top (hF.2.1 (reduce ω)))
    (c17_horizontal_test_bounded_C2 F hF (reduce ω)) s hs

end EinsteinFull
