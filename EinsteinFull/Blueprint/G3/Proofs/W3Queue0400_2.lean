import EinsteinFull.Blueprint.G3.node_stationary_u2D_analytic_u2D_semigroup_u23_flux
import EinsteinFull.Blueprint.Foundation.node_stationary_u2D_analytic_u2D_semigroup
import EinsteinFull.Blueprint.G3.node_e_u3A_time_u2D_flux
import EinsteinFull.Calculus.ComplexGradientAnalyticSupport
import EinsteinFull.Calculus.IsotropicGaussianSupport
import EinsteinFull.Calculus.ComplexOperatorAnalyticSupport
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import EinsteinFull.Blueprint.G3.Proofs.W3Queue0400_1

open MeasureTheory Filter Set
open scoped NNReal Topology BoundedContinuousFunction

noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation

variable {d : ℕ} {hd : 2 ≤ d} {Λ r : ℝ} {Q : EnvironmentLaw d Λ r}
  {β : Fin d → Lp ℂ 2 (reducedLaw Q)}
  {a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)} {μ : Lp ℂ 2 (reducedLaw Q)}
  {P T : ℂ → ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
  {G F : ℂ → ℝ≥0 → FluxIndex d → Fin d → Lp ℂ 2 (reducedLaw Q)}

/-- The actual finite-time flux predicate uniquely determines both its endpoint
horizontal gradients and its literal time-integrated flux classes. -/
theorem analyticFlux_unique {ζ : ℂ}
    {G₁ G₂ F₁ F₂ : ℝ≥0 → FluxIndex d → Fin d → Lp ℂ 2 (reducedLaw Q)}
    (h₁ : IsFiniteTimeFlux hd Q ζ (P ζ) (T ζ) β a μ G₁ F₁)
    (h₂ : IsFiniteTimeFlux hd Q ζ (P ζ) (T ζ) β a μ G₂ F₂) :
    G₁ = G₂ ∧ F₁ = F₂ := by
  obtain ⟨hc₁, hu₁, hg₁, hf₁⟩ := h₁
  obtain ⟨hc₂, hu₂, hg₂, hf₂⟩ := h₂
  have he : G₁ = G₂ := funext fun t => funext fun ν => (hg₁ t ν).unique (hg₂ t ν)
  refine ⟨he, ?_⟩
  subst G₂
  funext t ν j
  apply Lp.ext
  exact (hf₁ t ν j).trans (hf₂ t ν j).symm

/-- For any witnesses of the literal flux predicate, every forward endpoint
gradient at positive time is entire in force. Uniqueness identifies the
witnesses with the actual bounded gradient operator; no analytic selection
of witnesses is assumed. -/
theorem analyticAt_finiteTimeFlux_forward_gradient
    (hP : ∀ ζ, IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ (P ζ))
    (hF : ∀ ζ, IsFiniteTimeFlux hd Q ζ (P ζ) (T ζ) β a μ (G ζ) (F ζ))
    (t : ℝ≥0) (ht : 0 < t) (i j : Fin d) (z₀ : ℂ) :
    AnalyticAt ℂ (fun ζ => G ζ t (.inl i) j) z₀ := by
  have hd : AnalyticAt ℂ (fun ζ : ℂ => β i + ζ • a ⟨0, by omega⟩ i) z₀ :=
    analyticAt_const.add (analyticAt_id.fun_smul analyticAt_const)
  have ha := ((ContinuousLinearMap.apply ℂ _).analyticAt_bilinear _).comp₂ hd
    (analyticAt_forcedGradient hP t ht z₀)
  have hc := ((PiLp.proj 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q)) j).analyticAt _).comp ha
  apply hc.congr
  apply Eventually.of_forall
  intro ζ
  obtain ⟨_, _, hg, _⟩ := hF ζ
  have he := (hg t (.inl i)).unique
    (((hP ζ).forcedGradient_spec t ht (β i + ζ • a ⟨0, by omega⟩ i)).centered)
  exact (congrFun he j).symm

/-- Gaussian averaging on the actual stationary L2 carrier is a contraction.
The kernel uses physical variance `s`, with the explicit Euclidean norm. -/
theorem norm_fluxGaussianAverage_le (s : ℝ) (hs : 0 < s)
    (u : Lp ℂ 2 (reducedLaw Q)) :
    ‖∫ x : Vec d, (Correctors.euclideanHeatKernel s x : ℂ) •
      complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x u‖ ≤ ‖u‖ := by
  calc
    _ ≤ ∫ x : Vec d, ‖(Correctors.euclideanHeatKernel s x : ℂ) •
        complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x u‖ :=
      norm_integral_le_integral_norm _
    _ = ∫ x : Vec d, Correctors.euclideanHeatKernel s x * ‖u‖ := by
      congr 1
      funext x
      rw [norm_smul, norm_complexTranslation, Complex.norm_real,
        Real.norm_of_nonneg (Correctors.euclideanHeatKernel_nonneg hs.le x)]
    _ = ‖u‖ := by
      rw [integral_mul_const, Correctors.integral_euclideanHeatKernel hs, one_mul]

/-- The literal isotropic average, bundled on stationary complex L2. -/
def fluxGaussianAverageCLM (Q : EnvironmentLaw d Λ r) (s : ℝ) (hs : 0 < s) :
    Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q) :=
  ({ toFun := fun u => ∫ x : Vec d, (Correctors.euclideanHeatKernel s x : ℂ) •
        complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x u
     map_add' := fun u v => by
       simp only [map_add, smul_add]
       exact integral_add (integrable_isotropicGaussian_integrand Q s hs u)
         (integrable_isotropicGaussian_integrand Q s hs v)
     map_smul' := fun c u => by
       change (∫ x : Vec d, (Correctors.euclideanHeatKernel s x : ℂ) •
         complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x (c • u)) =
           c • ∫ x : Vec d, (Correctors.euclideanHeatKernel s x : ℂ) •
             complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x u
       simp only [map_smul, smul_comm (Correctors.euclideanHeatKernel s _ : ℂ) c]
       exact integral_smul c _ } : Lp ℂ 2 (reducedLaw Q) →ₗ[ℂ]
         Lp ℂ 2 (reducedLaw Q)).mkContinuous 1
    (fun u => by simpa only [one_mul] using! norm_fluxGaussianAverage_le s hs u)

/-- Evaluation of the bundled average is the literal spatial Bochner integral. -/
theorem fluxGaussianAverageCLM_apply (Q : EnvironmentLaw d Λ r) (s : ℝ) (hs : 0 < s)
    (u : Lp ℂ 2 (reducedLaw Q)) :
    fluxGaussianAverageCLM Q s hs u =
      ∫ x : Vec d, (Correctors.euclideanHeatKernel s x : ℂ) •
        complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x u := rfl

/-- The Gaussian averaging operator has norm at most one at every positive variance. -/
theorem norm_fluxGaussianAverageCLM_le (Q : EnvironmentLaw d Λ r) (s : ℝ) (hs : 0 < s) :
    ‖fluxGaussianAverageCLM Q s hs‖ ≤ 1 :=
  (fluxGaussianAverageCLM Q s hs).opNorm_le_bound zero_le_one
    (fun u => by simpa only [one_mul] using! norm_fluxGaussianAverage_le s hs u)

/-- Holomorphy passes to the exact centered Gaussian average used by the
flux contract. This is a bounded linear operation on the reduced joint law. -/
theorem analyticAt_fluxGaussianAverage {f : ℂ → Lp ℂ 2 (reducedLaw Q)}
    {z₀ : ℂ} (hf : AnalyticAt ℂ f z₀) (ρ : ℝ) (hρ : 1 ≤ ρ) :
    AnalyticAt ℂ (fun ζ => ∫ x : Vec d,
      (Correctors.euclideanHeatKernel (ρ ^ 2) x : ℂ) •
        complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x
          (centeredComplexLp Q (f ζ))) z₀ := by
  have hs : 0 < ρ ^ 2 := sq_pos_of_pos (lt_of_lt_of_le zero_lt_one hρ)
  have ha := (((fluxGaussianAverageCLM Q (ρ ^ 2) hs).comp
    (centeredComplexLpCLM Q)).analyticAt _).comp hf
  simpa only [Function.comp_def, ContinuousLinearMap.comp_apply,
    centeredComplexLpCLM_apply, fluxGaussianAverageCLM_apply] using! ha

/-- The force derivative commutes with the exact centered Gaussian average. -/
theorem deriv_fluxGaussianAverage {f : ℂ → Lp ℂ 2 (reducedLaw Q)}
    {z₀ : ℂ} (hf : DifferentiableAt ℂ f z₀) (ρ : ℝ) (hρ : 1 ≤ ρ) :
    deriv (fun ζ => ∫ x : Vec d,
      (Correctors.euclideanHeatKernel (ρ ^ 2) x : ℂ) •
        complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x
          (centeredComplexLp Q (f ζ))) z₀ =
      ∫ x : Vec d, (Correctors.euclideanHeatKernel (ρ ^ 2) x : ℂ) •
        complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x
          (centeredComplexLp Q (deriv f z₀)) := by
  have hs : 0 < ρ ^ 2 := sq_pos_of_pos (lt_of_lt_of_le zero_lt_one hρ)
  let L := (fluxGaussianAverageCLM Q (ρ ^ 2) hs).comp (centeredComplexLpCLM Q)
  have he := (L.hasFDerivAt.comp_hasDerivAt z₀ hf.hasDerivAt).deriv
  simpa only [L, Function.comp_def, ContinuousLinearMap.comp_apply,
    centeredComplexLpCLM_apply, fluxGaussianAverageCLM_apply] using! he

/-- Centering is an orthogonal projection on the actual reduced probability
law, so it does not enlarge the L2 norm. -/
theorem norm_fluxCentered_le (f : Lp ℂ 2 (reducedLaw Q)) :
    ‖centeredComplexLp Q f‖ ≤ ‖f‖ := by
  letI := reducedLaw_probability Q
  let c := ∫ ω, f ω ∂reducedLaw Q
  have ho : inner ℂ (Lp.const 2 (reducedLaw Q) c) (centeredComplexLp Q f) = 0 := by
    rw [MeasureTheory.L2.inner_def]
    change (∫ ω, inner ℂ (Lp.const 2 (reducedLaw Q) c ω)
      (centeredComplexLp Q f ω) ∂reducedLaw Q) = 0
    rw [integral_congr_ae (Filter.Eventually.mono
      (Lp.coeFn_const 2 (reducedLaw Q) c) (fun ω h => by rw [h]))]
    simp only [Function.const_apply, RCLike.inner_apply]
    rw [integral_mul_const, integral_centeredComplexLp, zero_mul]
  have he : Lp.const 2 (reducedLaw Q) c + centeredComplexLp Q f = f := by
    change _ + (f - Lp.const 2 (reducedLaw Q) c) = f
    abel
  have hh := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
    (Lp.const 2 (reducedLaw Q) c) (centeredComplexLp Q f) ho
  rw [he] at hh
  nlinarith [sq_nonneg ‖Lp.const 2 (reducedLaw Q) c‖, norm_nonneg f,
    norm_nonneg (centeredComplexLp Q f)]

/-- The centered average appearing in the flux statement is a contraction,
uniformly in every permitted spatial scale. -/
theorem norm_centered_fluxGaussianAverage_le (f : Lp ℂ 2 (reducedLaw Q))
    (ρ : ℝ) (hρ : 1 ≤ ρ) :
    ‖∫ x : Vec d, (Correctors.euclideanHeatKernel (ρ ^ 2) x : ℂ) •
      complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x
        (centeredComplexLp Q f)‖ ≤ ‖f‖ :=
  (norm_fluxGaussianAverage_le (ρ ^ 2)
    (sq_pos_of_pos (lt_of_lt_of_le zero_lt_one hρ)) _).trans (norm_fluxCentered_le f)

/-- Cauchy's estimate on the source force discs. A radius `1 / sqrt t`
around a force in the unit disc stays in the radius-two disc, inside the
open radius-three holomorphy domain. The bound loses exactly `sqrt t`. -/
theorem norm_deriv_le_on_flux_force_disc
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : ℂ → E} {t B : ℝ} (ht : 0 < t)
    (hf : DifferentiableOn ℂ f {z | ‖z‖ * Real.sqrt t < 3})
    (hB : ∀ z, ‖z‖ * Real.sqrt t ≤ 2 → ‖f z‖ ≤ B)
    {ζ : ℂ} (hζ : ‖ζ‖ * Real.sqrt t ≤ 1) :
    ‖deriv f ζ‖ ≤ B * Real.sqrt t := by
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
  have hball : Metric.closedBall ζ (Real.sqrt t)⁻¹ ⊆
      {z : ℂ | ‖z‖ * Real.sqrt t ≤ 2} := by
    intro z hz
    change ‖z‖ * Real.sqrt t ≤ 2
    have hd : ‖z - ζ‖ ≤ (Real.sqrt t)⁻¹ := by
      simpa only [Metric.mem_closedBall, dist_eq_norm] using! hz
    have hn : ‖z‖ ≤ ‖z - ζ‖ + ‖ζ‖ := by
      calc
        ‖z‖ = ‖(z - ζ) + ζ‖ := by rw [sub_add_cancel]
        _ ≤ ‖z - ζ‖ + ‖ζ‖ := norm_add_le _ _
    have hm := mul_le_mul_of_nonneg_right hd hs.le
    rw [inv_mul_cancel₀ hs.ne'] at hm
    nlinarith [mul_le_mul_of_nonneg_right hn hs.le]
  have hinside : Metric.closedBall ζ (Real.sqrt t)⁻¹ ⊆
      {z : ℂ | ‖z‖ * Real.sqrt t < 3} := by
    intro z hz
    have hz' : ‖z‖ * Real.sqrt t ≤ 2 := hball hz
    change ‖z‖ * Real.sqrt t < 3
    linarith
  have hc := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (inv_pos.2 hs)
    (hf.diffContOnCl_ball hinside)
    (fun z hz => hB z (hball (Metric.sphere_subset_closedBall hz)))
  simpa only [div_inv_eq_mul] using! hc

/-- Once the literal flux has its source holomorphy and size estimates,
Cauchy's estimate applies to its exact centered spatial average with no
scale-dependent constant. -/
theorem norm_deriv_fluxGaussianAverage_le
    {f : ℂ → Lp ℂ 2 (reducedLaw Q)} {t B : ℝ} (ht : 0 < t)
    (hf : DifferentiableOn ℂ f {z | ‖z‖ * Real.sqrt t < 3})
    (hB : ∀ z, ‖z‖ * Real.sqrt t ≤ 2 → ‖f z‖ ≤ B)
    (ρ : ℝ) (hρ : 1 ≤ ρ) {ζ : ℂ} (hζ : ‖ζ‖ * Real.sqrt t ≤ 1) :
    ‖deriv (fun z => ∫ x : Vec d,
      (Correctors.euclideanHeatKernel (ρ ^ 2) x : ℂ) •
        complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x
          (centeredComplexLp Q (f z))) ζ‖ ≤ B * Real.sqrt t := by
  have hopen : IsOpen {z : ℂ | ‖z‖ * Real.sqrt t < 3} :=
    isOpen_lt (continuous_norm.mul continuous_const) continuous_const
  have hd := hf.differentiableAt (hopen.mem_nhds (lt_of_le_of_lt hζ (by norm_num)))
  rw [deriv_fluxGaussianAverage hd ρ hρ]
  exact (norm_centered_fluxGaussianAverage_le _ ρ hρ).trans
    (norm_deriv_le_on_flux_force_disc ht hf hB hζ)

/-- The source Cauchy step in the actual Euclidean vector norm. Applying
Cauchy in `PiLp 2` preserves the flux bound's constant and exponent, uniformly
in the averaging scale, without a coordinate-count factor. -/
theorem norm_deriv_fluxGaussianAverage_vector_le
    {f : ℂ → Fin d → Lp ℂ 2 (reducedLaw Q)} {t B : ℝ} (ht : 0 < t)
    (hf : ∀ j, DifferentiableOn ℂ (fun z => f z j) {z | ‖z‖ * Real.sqrt t < 3})
    (hB : ∀ z, ‖z‖ * Real.sqrt t ≤ 2 →
      Real.sqrt (∑ j, ‖f z j‖ ^ 2) ≤ B)
    (ρ : ℝ) (hρ : 1 ≤ ρ) {ζ : ℂ} (hζ : ‖ζ‖ * Real.sqrt t ≤ 1) :
    Real.sqrt (∑ j, ‖deriv (fun z => ∫ x : Vec d,
      (Correctors.euclideanHeatKernel (ρ ^ 2) x : ℂ) •
        complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x
          (centeredComplexLp Q (f z j))) ζ‖ ^ 2) ≤ B * Real.sqrt t := by
  let g := fun z j => ∫ x : Vec d,
    (Correctors.euclideanHeatKernel (ρ ^ 2) x : ℂ) •
      complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x
        (centeredComplexLp Q (f z j))
  let v := fun z => WithLp.toLp 2 (g z)
  have hg : ∀ j, DifferentiableOn ℂ (fun z => g z j)
      {z | ‖z‖ * Real.sqrt t < 3} := by
    intro j
    have hs : 0 < ρ ^ 2 := sq_pos_of_pos (lt_of_lt_of_le zero_lt_one hρ)
    have hh := ((fluxGaussianAverageCLM Q (ρ ^ 2) hs).comp
      (centeredComplexLpCLM Q)).differentiable.comp_differentiableOn (hf j)
    simpa only [Function.comp_def, ContinuousLinearMap.comp_apply,
      centeredComplexLpCLM_apply, fluxGaussianAverageCLM_apply, g] using! hh
  have hv : DifferentiableOn ℂ v {z | ‖z‖ * Real.sqrt t < 3} :=
    (differentiableOn_piLp 2).2 hg
  have hb : ∀ z, ‖z‖ * Real.sqrt t ≤ 2 → ‖v z‖ ≤ B := by
    intro z hz
    rw [PiLp.norm_eq_of_L2]
    apply le_trans (Real.sqrt_le_sqrt (Finset.sum_le_sum (fun j _ => ?_))) (hB z hz)
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_centered_fluxGaussianAverage_le _ ρ hρ) 2
  have hc := norm_deriv_le_on_flux_force_disc ht hv hb hζ
  have hopen : IsOpen {z : ℂ | ‖z‖ * Real.sqrt t < 3} :=
    isOpen_lt (continuous_norm.mul continuous_const) continuous_const
  have hd := hv.differentiableAt (hopen.mem_nhds (lt_of_le_of_lt hζ (by norm_num)))
  have he (j : Fin d) : deriv (fun z => g z j) ζ = deriv v ζ j := by
    let L := PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q)) j
    exact (L.hasFDerivAt.comp_hasDerivAt ζ hd.hasDerivAt).deriv
  rw [PiLp.norm_eq_of_L2] at hc
  simpa only [← he] using! hc

private def fluxWeightedIntegrand {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (t : ℝ≥0) (g : Ioc (0 : ℝ) (t : ℝ) →ᵇ E) (s : ℝ) : E :=
  if hs : s ∈ Ioc (0 : ℝ) (t : ℝ) then (Real.sqrt s)⁻¹ • g ⟨s, hs⟩ else 0

private theorem fluxWeightedIntegrand_continuousOn {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (t : ℝ≥0) (g : Ioc (0 : ℝ) (t : ℝ) →ᵇ E) :
    ContinuousOn (fluxWeightedIntegrand t g) (Ioc (0 : ℝ) (t : ℝ)) := by
  rw [continuousOn_iff_continuous_restrict]
  have hi : Continuous (fun s : Ioc (0 : ℝ) (t : ℝ) => (Real.sqrt s.1)⁻¹) :=
    (Real.continuous_sqrt.comp continuous_subtype_val).inv₀
      (fun s => ne_of_gt (Real.sqrt_pos.2 s.2.1))
  apply Continuous.congr (hi.smul g.continuous)
  intro s
  change (Real.sqrt s.1)⁻¹ • g s = fluxWeightedIntegrand t g s.1
  simp only [fluxWeightedIntegrand, dif_pos s.2]

private theorem norm_fluxWeightedIntegrand_le {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (t : ℝ≥0) (g : Ioc (0 : ℝ) (t : ℝ) →ᵇ E)
    {s : ℝ} (hs : s ∈ Ioc (0 : ℝ) (t : ℝ)) :
    ‖fluxWeightedIntegrand t g s‖ ≤ ‖g‖ * (Real.sqrt s)⁻¹ := by
  rw [fluxWeightedIntegrand, dif_pos hs, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.2 (Real.sqrt_nonneg _))]
  exact (mul_le_mul_of_nonneg_left (g.norm_coe_le_norm _) (by positivity)).trans_eq
    (mul_comm _ _)

private theorem fluxWeightedIntegrand_intervalIntegrable {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (t : ℝ≥0) (g : Ioc (0 : ℝ) (t : ℝ) →ᵇ E) :
    IntervalIntegrable (fluxWeightedIntegrand t g) volume 0 t := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (show (0 : ℝ) ≤ (t : ℝ) from t.property)]
  apply ((intervalIntegrable_inv_sqrt t.property).const_mul ‖g‖).1.mono'
  · letI : SecondCountableTopologyEither ℝ E := secondCountableTopologyEither_of_left ℝ E
    exact (fluxWeightedIntegrand_continuousOn t g).aestronglyMeasurable measurableSet_Ioc
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    exact norm_fluxWeightedIntegrand_le t g hs

private theorem norm_integral_fluxWeightedIntegrand_le {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (t : ℝ≥0) (g : Ioc (0 : ℝ) (t : ℝ) →ᵇ E) :
    ‖∫ s in (0 : ℝ)..(t : ℝ), fluxWeightedIntegrand t g s‖ ≤
      (2 * Real.sqrt (t : ℝ)) * ‖g‖ := by
  calc
    _ ≤ ∫ s in (0 : ℝ)..(t : ℝ), ‖g‖ * (Real.sqrt s)⁻¹ :=
      intervalIntegral.norm_integral_le_of_norm_le t.property
        (Eventually.of_forall fun s hs => norm_fluxWeightedIntegrand_le t g hs)
        ((intervalIntegrable_inv_sqrt t.property).const_mul _)
    _ = _ := by
      rw [intervalIntegral.integral_const_mul, integral_inv_sqrt (t := (t : ℝ)) t.property]
      ring

/-- Bochner integration after removing the square-root time weight is bounded
on the actual weighted-orbit space, including its integrable singularity at zero. -/
def fluxWeightedIntegralCLM (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    (t : ℝ≥0) : (Ioc (0 : ℝ) (t : ℝ) →ᵇ E) →L[ℂ] E :=
  let L : (Ioc (0 : ℝ) (t : ℝ) →ᵇ E) →ₗ[ℂ] E :=
    { toFun := fun g => ∫ s in (0 : ℝ)..(t : ℝ), fluxWeightedIntegrand t g s
      map_add' := fun g h => by
        have he : fluxWeightedIntegrand t (g + h) = fun s =>
            fluxWeightedIntegrand t g s + fluxWeightedIntegrand t h s := by
          funext s
          by_cases hs : s ∈ Ioc (0 : ℝ) (t : ℝ)
          · simp only [fluxWeightedIntegrand, dif_pos hs,
              BoundedContinuousFunction.coe_add, Pi.add_apply, smul_add]
          · simp only [fluxWeightedIntegrand, dif_neg hs, add_zero]
        rw [he, intervalIntegral.integral_add (fluxWeightedIntegrand_intervalIntegrable t g)
          (fluxWeightedIntegrand_intervalIntegrable t h)]
      map_smul' := fun c g => by
        have he : fluxWeightedIntegrand t (c • g) = fun s =>
            c • fluxWeightedIntegrand t g s := by
          funext s
          by_cases hs : s ∈ Ioc (0 : ℝ) (t : ℝ)
          · simp only [fluxWeightedIntegrand, dif_pos hs,
              BoundedContinuousFunction.coe_smul]
            exact smul_comm _ _ _
          · simp only [fluxWeightedIntegrand, dif_neg hs, smul_zero]
        change _ = c • _
        rw [he, intervalIntegral.integral_smul] }
  L.mkContinuous (2 * Real.sqrt (t : ℝ)) (norm_integral_fluxWeightedIntegrand_le t)

/-- The weighted time integration map has the exact square-root horizon bound. -/
theorem norm_fluxWeightedIntegralCLM_le (E : Type*) [NormedAddCommGroup E]
    [NormedSpace ℂ E] (t : ℝ≥0) :
    ‖fluxWeightedIntegralCLM E t‖ ≤ 2 * Real.sqrt (t : ℝ) :=
  (fluxWeightedIntegralCLM E t).opNorm_le_bound (by positivity)
    (norm_integral_fluxWeightedIntegrand_le t)

/-- The literal forward primitive gradient is the bounded weighted time integral.
This identification holds for every force and every actual flux witness. -/
theorem finiteTimeFlux_forward_integral_gradient_eq {ζ : ℂ}
    (hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ (P ζ))
    (hF : IsFiniteTimeFlux hd Q ζ (P ζ) (T ζ) β a μ (G ζ) (F ζ))
    (t : ℝ≥0) (i j : Fin d) :
    (∫ s in Icc (0 : ℝ) (t : ℝ), G ζ s.toNNReal (.inl i) j) =
      (PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q)) j)
        (fluxWeightedIntegralCLM _ t (hP.weightedGradientOrbit (t : ℝ)
          (β i + ζ • a ⟨0, by omega⟩ i))) := by
  obtain ⟨_, _, hg, _⟩ := hF
  symm
  change (PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q)) j)
    (fluxWeightedIntegralCLM _ t (hP.weightedGradientOrbit (t : ℝ)
      (β i + ζ • a ⟨0, by omega⟩ i))) =
    ∫ s in Icc (0 : ℝ) (t : ℝ), G ζ s.toNNReal (.inl i) j
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (show (0 : ℝ) ≤ (t : ℝ) from t.property)]
  change (PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q)) j)
    (∫ s in (0 : ℝ)..(t : ℝ), fluxWeightedIntegrand t
      (hP.weightedGradientOrbit (t : ℝ) (β i + ζ • a ⟨0, by omega⟩ i)) s) = _
  rw [← ContinuousLinearMap.intervalIntegral_comp_comm _
    (fluxWeightedIntegrand_intervalIntegrable t _)]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [] with s hs
  rw [uIoc_of_le (show (0 : ℝ) ≤ (t : ℝ) from t.property)] at hs
  rw [fluxWeightedIntegrand, dif_pos hs, hP.weightedGradientOrbit_apply,
    smul_smul, inv_mul_cancel₀ (ne_of_gt (Real.sqrt_pos.2 hs.1)), one_smul]
  have he := (hg s.toNNReal (.inl i)).unique
    ((hP.gradientOrbit_spec (β i + ζ • a ⟨0, by omega⟩ i) hs.1).centered)
  exact (congrFun he j).symm

/-- Euclidean forward primitive gradient estimate with explicit structural
constants and the actual parabolic force shift. -/
theorem norm_finiteTimeFlux_forward_integral_gradient_le {ζ : ℂ}
    (hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ (P ζ))
    (hF : IsFiniteTimeFlux hd Q ζ (P ζ) (T ζ) β a μ (G ζ) (F ζ))
    (t : ℝ≥0) (i : Fin d) :
    Real.sqrt (∑ j, ‖∫ s in Icc (0 : ℝ) (t : ℝ),
      G ζ s.toNNReal (.inl i) j‖ ^ 2) ≤
      4 * Real.sqrt (Real.exp (2 * Λ) * Λ) * Real.sqrt (t : ℝ) *
        Real.exp (65 * complexForceShift d Λ ζ * (t : ℝ)) *
          ‖β i + ζ • a ⟨0, by omega⟩ i‖ := by
  let L := fluxWeightedIntegralCLM (PiLp 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q))) t
  let W := hP.weightedGradientOrbit (t : ℝ)
  let f := β i + ζ • a ⟨0, by omega⟩ i
  have he : WithLp.toLp 2 (fun j => ∫ s in Icc (0 : ℝ) (t : ℝ),
      G ζ s.toNNReal (.inl i) j) = L (W f) := by
    apply PiLp.ext
    intro j
    exact finiteTimeFlux_forward_integral_gradient_eq hP hF t i j
  rw [← PiLp.norm_eq_of_L2 (WithLp.toLp 2 (fun j =>
    ∫ s in Icc (0 : ℝ) (t : ℝ), G ζ s.toNNReal (.inl i) j)), he]
  calc
    ‖L (W f)‖ ≤ (2 * Real.sqrt (t : ℝ)) * ‖W f‖ :=
      (L.le_opNorm _).trans (mul_le_mul_of_nonneg_right
        (norm_fluxWeightedIntegralCLM_le _ t) (norm_nonneg _))
    _ ≤ (2 * Real.sqrt (t : ℝ)) *
        ((2 * Real.sqrt (Real.exp (2 * Λ) * Λ) *
          Real.exp (65 * complexForceShift d Λ ζ * (t : ℝ))) * ‖f‖) :=
      mul_le_mul_of_nonneg_left ((W.le_opNorm _).trans
        (mul_le_mul_of_nonneg_right (hP.norm_weightedGradientOrbit_le (t : ℝ))
          (norm_nonneg _))) (by positivity)
    _ = _ := by dsimp only [f]; ring

/-- The actual forward primitive gradients are force analytic on the
short-time force disc. This includes the entire time integral down to zero,
and applies to every choice of witnesses of the literal flux predicate. -/
theorem analyticAt_finiteTimeFlux_forward_integral_gradient_of_small_force
    (hP : ∀ ζ, IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ (P ζ))
    (hF : ∀ ζ, IsFiniteTimeFlux hd Q ζ (P ζ) (T ζ) β a μ (G ζ) (F ζ))
    (t : ℝ≥0) (i j : Fin d) (z₀ : ℂ)
    (hs : ‖z₀‖ * (4 * Real.sqrt (Real.exp (2 * Λ) * Λ) *
      ((d : ℝ) * (Real.exp (2 * Λ) * Λ)) * Real.sqrt (t : ℝ)) < 1) :
    AnalyticAt ℂ (fun ζ => ∫ s in Icc (0 : ℝ) (t : ℝ),
      G ζ s.toNNReal (.inl i) j) z₀ := by
  let E := PiLp 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q))
  let L := (PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q)) j).comp
    (fluxWeightedIntegralCLM E t)
  have hd : AnalyticAt ℂ (fun ζ : ℂ => β i + ζ • a ⟨0, by omega⟩ i) z₀ :=
    analyticAt_const.add (analyticAt_id.fun_smul analyticAt_const)
  have ha := ((ContinuousLinearMap.apply ℂ _).analyticAt_bilinear _).comp₂ hd
    (analyticAt_weightedGradientOrbit_of_small_force hP (t : ℝ) z₀ hs)
  have hc := (L.analyticAt _).comp ha
  apply hc.congr
  apply Eventually.of_forall
  intro ζ
  exact (finiteTimeFlux_forward_integral_gradient_eq (hP ζ) (hF ζ) t i j).symm

variable {i₀ : Fin d}

/-- The actual forward gradient primitive as a bounded complex linear map. -/
def fluxForwardGradientPrimitiveCLM {ζ : ℂ}
    (hP : IsComplexEnvironmentSemigroup Q i₀ ζ (P ζ)) (t : ℝ≥0) :
    Lp ℂ 2 (reducedLaw Q) →L[ℂ] PiLp 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q)) :=
  (fluxWeightedIntegralCLM _ t).comp (hP.weightedGradientOrbit (t : ℝ))

private theorem fluxWeightedIntegrand_orbit_eq {ζ : ℂ}
    (hP : IsComplexEnvironmentSemigroup Q i₀ ζ (P ζ))
    (t : ℝ≥0) (f : Lp ℂ 2 (reducedLaw Q)) {s : ℝ}
    (hs : s ∈ Ioc (0 : ℝ) (t : ℝ)) :
    fluxWeightedIntegrand t (hP.weightedGradientOrbit (t : ℝ) f) s =
      hP.gradientOrbit f s := by
  rw [fluxWeightedIntegrand, dif_pos hs, hP.weightedGradientOrbit_apply,
    smul_smul, inv_mul_cancel₀ (ne_of_gt (Real.sqrt_pos.2 hs.1)), one_smul]

private theorem intervalIntegrable_fluxGradientOrbit {ζ : ℂ}
    (hP : IsComplexEnvironmentSemigroup Q i₀ ζ (P ζ))
    (t : ℝ≥0) (f : Lp ℂ 2 (reducedLaw Q)) :
    IntervalIntegrable (hP.gradientOrbit f) volume 0 (t : ℝ) := by
  apply (fluxWeightedIntegrand_intervalIntegrable t
    (hP.weightedGradientOrbit (t : ℝ) f)).congr
  intro s hs
  rw [uIoc_of_le (show (0 : ℝ) ≤ (t : ℝ) from t.property)] at hs
  exact fluxWeightedIntegrand_orbit_eq hP t f hs

/-- Evaluation is the genuine Bochner integral of the actual gradient orbit. -/
theorem fluxForwardGradientPrimitiveCLM_apply {ζ : ℂ}
    (hP : IsComplexEnvironmentSemigroup Q i₀ ζ (P ζ))
    (t : ℝ≥0) (f : Lp ℂ 2 (reducedLaw Q)) :
    fluxForwardGradientPrimitiveCLM hP t f =
      ∫ s in (0 : ℝ)..(t : ℝ), hP.gradientOrbit f s := by
  change (∫ s in (0 : ℝ)..(t : ℝ),
    fluxWeightedIntegrand t (hP.weightedGradientOrbit (t : ℝ) f) s) = _
  apply intervalIntegral.integral_congr_ae
  filter_upwards [] with s hs
  rw [uIoc_of_le (show (0 : ℝ) ≤ (t : ℝ) from t.property)] at hs
  exact fluxWeightedIntegrand_orbit_eq hP t f hs

private theorem fluxGradientOrbit_add {ζ : ℂ}
    (hP : IsComplexEnvironmentSemigroup Q i₀ ζ (P ζ))
    (f : Lp ℂ 2 (reducedLaw Q)) (t : ℝ≥0) {s : ℝ} (hs : 0 < s) :
    hP.gradientOrbit f (s + (t : ℝ)) = hP.gradientOrbit (P ζ t f) s := by
  have hst : 0 < s + (t : ℝ) := add_pos_of_pos_of_nonneg hs t.property
  have ht : (s + (t : ℝ)).toNNReal = s.toNNReal + t := by
    simp only [Real.toNNReal_add hs.le (show (0 : ℝ) ≤ (t : ℝ) from t.property),
      Real.toNNReal_coe]
  apply WithLp.ofLp_injective 2
  apply (hP.gradientOrbit_spec f hst).unique
  rw [ht, hP.2.1, ContinuousLinearMap.comp_apply]
  exact hP.gradientOrbit_spec (P ζ t f) hs

/-- The integrated actual gradient obeys the semigroup time splitting law. -/
theorem fluxForwardGradientPrimitiveCLM_add {ζ : ℂ}
    (hP : IsComplexEnvironmentSemigroup Q i₀ ζ (P ζ)) (s t : ℝ≥0) :
    fluxForwardGradientPrimitiveCLM hP (s + t) =
      fluxForwardGradientPrimitiveCLM hP s +
        (fluxForwardGradientPrimitiveCLM hP t).comp (P ζ s) := by
  apply ContinuousLinearMap.ext
  intro f
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    fluxForwardGradientPrimitiveCLM_apply, NNReal.coe_add]
  have htail : IntervalIntegrable (hP.gradientOrbit f) volume (s : ℝ) ((s : ℝ) + t) := by
    apply (intervalIntegrable_fluxGradientOrbit hP (s + t) f).mono_set
    rw [uIcc_of_le (show (s : ℝ) ≤ (s : ℝ) + t from le_add_of_nonneg_right t.property),
      uIcc_of_le (show (0 : ℝ) ≤ ((s + t : ℝ≥0) : ℝ) from (s + t).property)]
    exact Icc_subset_Icc s.property le_rfl
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_fluxGradientOrbit hP s f) htail]
  congr 1
  have he := intervalIntegral.integral_comp_add_right (a := (0 : ℝ)) (b := (t : ℝ))
    (hP.gradientOrbit f) (s : ℝ)
  simp only [zero_add, add_comm (t : ℝ) (s : ℝ)] at he
  rw [← he]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [] with r hr
  rw [uIoc_of_le (show (0 : ℝ) ≤ (t : ℝ) from t.property)] at hr
  exact fluxGradientOrbit_add hP f s hr.1

/-- Short-time force analyticity holds in operator norm for the integrated
actual forward gradient. -/
theorem analyticAt_fluxForwardGradientPrimitiveCLM_of_small_force
    (hP : ∀ ζ, IsComplexEnvironmentSemigroup Q i₀ ζ (P ζ))
    (t : ℝ≥0) (z₀ : ℂ)
    (hs : ‖z₀‖ * (4 * Real.sqrt (Real.exp (2 * Λ) * Λ) *
      ((d : ℝ) * (Real.exp (2 * Λ) * Λ)) * Real.sqrt (t : ℝ)) < 1) :
    AnalyticAt ℂ (fun ζ => fluxForwardGradientPrimitiveCLM (hP ζ) t) z₀ := by
  let X := Lp ℂ 2 (reducedLaw Q)
  let Y := PiLp 2 (fun _ : Fin d => X)
  let L : (Ioc (0 : ℝ) (t : ℝ) →ᵇ Y) →L[ℂ] Y := fluxWeightedIntegralCLM Y t
  have ha := (((ContinuousLinearMap.compL ℂ X (Ioc (0 : ℝ) (t : ℝ) →ᵇ Y) Y) L).analyticAt _).comp
    (analyticAt_weightedGradientOrbit_of_small_force hP (t : ℝ) z₀ hs)
  exact ha

/-- A finite partition into short intervals gives entire force dependence of
 the actual forward gradient primitive, in operator norm. -/
theorem analyticAt_fluxForwardGradientPrimitiveCLM
    (hP : ∀ ζ, IsComplexEnvironmentSemigroup Q i₀ ζ (P ζ))
    (t : ℝ≥0) (z₀ : ℂ) :
    AnalyticAt ℂ (fun ζ => fluxForwardGradientPrimitiveCLM (hP ζ) t) z₀ := by
  obtain ⟨n, hn, hs⟩ := exists_pos_nat_mul_sqrt_div_lt_one
    (‖z₀‖ * (4 * Real.sqrt (Real.exp (2 * Λ) * Λ) *
      ((d : ℝ) * (Real.exp (2 * Λ) * Λ)))) (t : ℝ)
  let s : ℝ≥0 := t / n
  have hsmall : ‖z₀‖ * (4 * Real.sqrt (Real.exp (2 * Λ) * Λ) *
      ((d : ℝ) * (Real.exp (2 * Λ) * Λ)) * Real.sqrt (s : ℝ)) < 1 := by
    simpa only [s, NNReal.coe_div, NNReal.coe_natCast, mul_assoc] using! hs
  have ha := analyticAt_fluxForwardGradientPrimitiveCLM_of_small_force hP s z₀ hsmall
  have hm : ∀ m : ℕ, AnalyticAt ℂ
      (fun ζ => fluxForwardGradientPrimitiveCLM (hP ζ) (m * s)) z₀ := by
    intro m
    induction m with
    | zero =>
      have he : (fun ζ => fluxForwardGradientPrimitiveCLM (hP ζ) ((0 : ℕ) * s)) =
          fun _ : ℂ => (0 : Lp ℂ 2 (reducedLaw Q) →L[ℂ]
            PiLp 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q))) := by
        funext ζ
        apply ContinuousLinearMap.ext
        intro f
        simp only [Nat.cast_zero, zero_mul, fluxForwardGradientPrimitiveCLM_apply,
          NNReal.coe_zero, intervalIntegral.integral_same, ContinuousLinearMap.zero_apply]
      rw [he]
      exact analyticAt_const
    | succ m ih =>
      have hb := ((ContinuousLinearMap.compL ℂ _ _ _).analyticAt_bilinear _).comp₂
        ih (analyticAt_complexEnvironmentSemigroup hP s z₀)
      have hc := ha.add hb
      apply hc.congr
      apply Eventually.of_forall
      intro ζ
      change fluxForwardGradientPrimitiveCLM (hP ζ) s +
        (fluxForwardGradientPrimitiveCLM (hP ζ) ((m : ℝ≥0) * s)).comp (P ζ s) =
          fluxForwardGradientPrimitiveCLM (hP ζ) (((m + 1 : ℕ) : ℝ≥0) * s)
      rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul,
        add_comm ((m : ℝ≥0) * s) s, fluxForwardGradientPrimitiveCLM_add]
  have he : (n : ℝ≥0) * s = t := by
    dsimp only [s]
    exact mul_div_cancel₀ t (by exact_mod_cast (Nat.ne_of_gt hn))
  simpa only [he] using! hm n

/-- Every coordinate of the literal forward primitive gradient is entire in
force, for every positive or zero horizon and every actual flux witness. -/
theorem analyticAt_finiteTimeFlux_forward_integral_gradient
    (hP : ∀ ζ, IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ (P ζ))
    (hF : ∀ ζ, IsFiniteTimeFlux hd Q ζ (P ζ) (T ζ) β a μ (G ζ) (F ζ))
    (t : ℝ≥0) (i j : Fin d) (z₀ : ℂ) :
    AnalyticAt ℂ (fun ζ => ∫ s in Icc (0 : ℝ) (t : ℝ),
      G ζ s.toNNReal (.inl i) j) z₀ := by
  have hd : AnalyticAt ℂ (fun ζ : ℂ => β i + ζ • a ⟨0, by omega⟩ i) z₀ :=
    analyticAt_const.add (analyticAt_id.fun_smul analyticAt_const)
  have ha := ((ContinuousLinearMap.apply ℂ _).analyticAt_bilinear _).comp₂ hd
    (analyticAt_fluxForwardGradientPrimitiveCLM hP t z₀)
  have hc := ((PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q)) j).analyticAt _).comp ha
  apply hc.congr
  apply Eventually.of_forall
  intro ζ
  exact (finiteTimeFlux_forward_integral_gradient_eq (hP ζ) (hF ζ) t i j).symm


private theorem fluxCoeFn_sum {α : Type*} [MeasurableSpace α] (m : Measure α)
    {ι : Type*} (s : Finset ι) (f : ι → Lp ℂ 2 m) :
    (∑ k ∈ s, f k : Lp ℂ 2 m) =ᵐ[m] fun ω => ∑ k ∈ s, f k ω := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using! Lp.coeFn_zero ℂ 2 m
  | @insert k s hk ih =>
    simp only [Finset.sum_insert hk]
    filter_upwards [Lp.coeFn_add (f k) (∑ b ∈ s, f b), ih] with ω ha hb
    simpa only [Pi.add_apply, hb] using! ha

/-- Every literal forward flux is the actual anisotropic coefficient row
applied to the integrated horizontal gradient, plus its initial entry. -/
theorem finiteTimeFlux_forward_eq {ζ : ℂ}
    (ha : IsReducedCoefficientObservation Q a)
    (hF : IsFiniteTimeFlux hd Q ζ (P ζ) (T ζ) β a μ (G ζ) (F ζ))
    (t : ℝ≥0) (i j : Fin d) :
    F ζ t (.inl i) j = a j i + ∑ k, complexCoefficientMul Q j k
      (∫ s in Icc (0 : ℝ) (t : ℝ), G ζ s.toNNReal (.inl i) k) := by
  obtain ⟨hG, hU, _, hf⟩ := hF
  apply Lp.ext
  let H (k : Fin d) := ∫ s in Icc (0 : ℝ) (t : ℝ), G ζ s.toNNReal (.inl i) k
  filter_upwards [hf t (.inl i) j,
    Lp.coeFn_add (a j i) (∑ k, complexCoefficientMul Q j k (H k)),
    fluxCoeFn_sum (reducedLaw Q) Finset.univ (fun k => complexCoefficientMul Q j k (H k)),
    ae_all_iff.mpr (fun k => complexCoefficientMul_coe Q j k (H k)),
    ae_all_iff.mpr (fun k => ha j k)] with ω hfω hadd hsum hmul haω
  simp only [finiteTimeFluxObservation, Sum.elim_inl, sub_zero] at hfω
  rw [hfω, hadd]
  change a j i ω + ∑ k, a j k ω * H k ω = _
  simp only [Pi.add_apply]
  rw [hsum]
  simp only [hmul, haω]

/-- Every literal forward finite-time flux is entire in complex force.
The anisotropic multipliers and the selected flux witnesses are the actual
ones from the frozen meaning predicates. -/
theorem analyticAt_finiteTimeFlux_forward
    (hP : ∀ ζ, IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ (P ζ))
    (ha : IsReducedCoefficientObservation Q a)
    (hF : ∀ ζ, IsFiniteTimeFlux hd Q ζ (P ζ) (T ζ) β a μ (G ζ) (F ζ))
    (t : ℝ≥0) (i j : Fin d) (z₀ : ℂ) :
    AnalyticAt ℂ (fun ζ => F ζ t (.inl i) j) z₀ := by
  have hs := Finset.univ.analyticAt_fun_sum (fun k _ =>
    ((complexCoefficientMul Q j k).analyticAt _).comp
      (analyticAt_finiteTimeFlux_forward_integral_gradient hP hF t i k z₀))
  have hc := (analyticAt_const (v := a j i)).add hs
  apply hc.congr
  apply Eventually.of_forall
  intro ζ
  exact (finiteTimeFlux_forward_eq ha (hF ζ) t i j).symm


private def fluxGradientEnergy (Q : EnvironmentLaw d Λ r)
    (G H : Fin d → Lp ℂ 2 (reducedLaw Q)) : ℂ :=
  ∫ ω, ∑ j, ∑ k, star (G j ω) * (ω.1 0 j k : ℂ) * H k ω ∂reducedLaw Q

private theorem fluxGradientEnergy_sub_right
    (G H K : Fin d → Lp ℂ 2 (reducedLaw Q)) :
    fluxGradientEnergy Q G (fun k => H k - K k) =
      fluxGradientEnergy Q G H - fluxGradientEnergy Q G K := by
  unfold fluxGradientEnergy
  rw [← integral_sub (integrable_reduced_complex_energy Q G H)
    (integrable_reduced_complex_energy Q G K)]
  apply integral_congr_ae
  filter_upwards [ae_all_iff.mpr fun k => Lp.coeFn_sub (H k) (K k)] with ω hω
  simp only [Pi.sub_apply] at hω
  simp only [hω, mul_sub, Finset.sum_sub_distrib]

private theorem fluxTransposeForcePair_le (ζ : ℂ) (f : Lp ℂ 2 (reducedLaw Q))
    (G : PiLp 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q))) :
    (ζ * inner ℂ (complexForceDrift Q i₀ G) f).re ≤
      ((Real.exp (2 * Λ) * Λ)⁻¹ / 4) * ‖G‖ ^ 2 +
        complexForceShift d Λ ζ * ‖f‖ ^ 2 := by
  have h := re_complexForceDrift_pair_le Q i₀ (star ζ) f G
  have he : (star ζ * inner ℂ f (complexForceDrift Q i₀ G)).re =
      (ζ * inner ℂ (complexForceDrift Q i₀ G) f).re := by
    rw [← inner_conj_symm f (complexForceDrift Q i₀ G)]
    change (star ζ * star (inner ℂ (complexForceDrift Q i₀ G) f)).re = _
    rw [← star_mul]
    simp only [Complex.star_def, Complex.conj_re, mul_comm]
  simpa only [he, complexForceShift, norm_star, PiLp.norm_sq_eq_of_L2] using! h

private theorem fluxTransposeGradient_difference_energy
    {ζ η : ℂ} {f g u v : Lp ℂ 2 (reducedLaw Q)}
    (hfg : IsComplexTransposeGeneratorPair Q i₀ ζ f g)
    (huv : IsComplexTransposeGeneratorPair Q i₀ η u v)
    {G H : PiLp 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q))}
    (hG : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) f G)
    (hH : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) u H) :
    ((Real.exp (2 * Λ) * Λ)⁻¹ / 4) * ‖G-H‖ ^ 2 ≤
      ‖f-u‖ * ‖g-v‖ + complexForceShift d Λ ζ * ‖f-u‖ ^ 2 +
        (‖ζ-η‖ * ((d : ℝ) * (Real.exp (2 * Λ) * Λ)) * ‖u‖) * ‖G-H‖ := by
  let D := G-H
  have hD : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) (f-u) D := by
    intro j
    simpa only [D, PiLp.sub_apply, neg_one_smul, ← sub_eq_add_neg] using!
      (hG j).add ((hH j).smul (-1))
  have h₁ := hfg.conjugate_test hG (f-u) D hD
  have h₂ := huv.conjugate_test hH (f-u) D hD
  change inner ℂ (f-u) g = -(1/2 : ℂ) * fluxGradientEnergy Q D G +
    ζ * inner ℂ (complexForceDrift Q i₀ D) f at h₁
  change inner ℂ (f-u) v = -(1/2 : ℂ) * fluxGradientEnergy Q D H +
    η * inner ℂ (complexForceDrift Q i₀ D) u at h₂
  have he : fluxGradientEnergy Q D D =
      fluxGradientEnergy Q D G - fluxGradientEnergy Q D H := by
    change fluxGradientEnergy Q D (fun k => G k-H k) = _
    exact fluxGradientEnergy_sub_right D G H
  have ht : inner ℂ (f-u) (g-v) = -(1/2 : ℂ) * fluxGradientEnergy Q D D +
      ζ * inner ℂ (complexForceDrift Q i₀ D) (f-u) +
      (ζ-η) * inner ℂ (complexForceDrift Q i₀ D) u := by
    rw [he, inner_sub_right, h₁, h₂, inner_sub_right]
    ring
  have hb := reduced_complex_energy_lowerBound Q (fun j => D j)
  change (Real.exp (2 * Λ) * Λ)⁻¹ * (∑ j, ‖D j‖ ^ 2) ≤
    (fluxGradientEnergy Q D D).re at hb
  rw [← PiLp.norm_sq_eq_of_L2] at hb
  have hy := fluxTransposeForcePair_le (i₀ := i₀) ζ (f-u) D
  have hi : -(inner ℂ (f-u) (g-v)).re ≤ ‖f-u‖ * ‖g-v‖ :=
    ((neg_le_abs _).trans (Complex.abs_re_le_norm _)).trans (norm_inner_le_norm _ _)
  have herr : ((ζ-η) * inner ℂ (complexForceDrift Q i₀ D) u).re ≤
      (‖ζ-η‖ * ((d : ℝ) * (Real.exp (2 * Λ) * Λ)) * ‖u‖) * ‖D‖ := by
    calc
      _ ≤ ‖(ζ-η) * inner ℂ (complexForceDrift Q i₀ D) u‖ := Complex.re_le_norm _
      _ = ‖ζ-η‖ * ‖inner ℂ (complexForceDrift Q i₀ D) u‖ := norm_mul _ _
      _ ≤ ‖ζ-η‖ * (‖complexForceDrift Q i₀ D‖ * ‖u‖) :=
        mul_le_mul_of_nonneg_left (norm_inner_le_norm _ _) (norm_nonneg _)
      _ ≤ ‖ζ-η‖ * (((d : ℝ) * (Real.exp (2 * Λ) * Λ) * ‖D‖) * ‖u‖) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (norm_complexForceDrift_apply_le Q i₀ D) (norm_nonneg _))
          (norm_nonneg _)
      _ = _ := by ring
  have hr := congrArg Complex.re ht
  simp only [Complex.add_re] at hr
  have hre : (-(1/2 : ℂ) * fluxGradientEnergy Q D D).re =
      -(1/2 : ℝ) * (fluxGradientEnergy Q D D).re := by
    norm_num [Complex.mul_re]
  rw [hre] at hr
  change ((Real.exp (2 * Λ) * Λ)⁻¹ / 4) * ‖D‖ ^ 2 ≤
    ‖f-u‖ * ‖g-v‖ + complexForceShift d Λ ζ * ‖f-u‖ ^ 2 +
      (‖ζ-η‖ * ((d : ℝ) * (Real.exp (2 * Λ) * Λ)) * ‖u‖) * ‖D‖
  linarith only [hb, hy, hi, herr, hr]

private theorem flux_absorb_linear (c A b x : ℝ) (hc : 0 < c)
    (h : c * x ^ 2 ≤ A + b*x) : x ^ 2 ≤ 2*A/c + (b/c)^2 := by
  have ht : x^2 ≤ A/c + (b/c)*x := by
    rw [div_mul_eq_mul_div, ← add_div]
    exact (le_div_iff₀ hc).mpr (by simpa only [mul_comm] using! h)
  rw [mul_div_assoc]
  nlinarith only [ht, sq_nonneg (x-b/c)]

/-- Actual full transpose generator graphs varying with force have continuous
Euclidean gradients whenever their value and generator coordinates are
continuous. The changing-force contribution is controlled explicitly. -/
theorem continuous_horizontalGradient_of_transpose_generator
    {f g : ℂ → Lp ℂ 2 (reducedLaw Q)}
    {G : ℂ → PiLp 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q))}
    (hfg : ∀ ζ, IsComplexTransposeGeneratorPair Q i₀ ζ (f ζ) (g ζ))
    (hG : ∀ ζ, HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
      (f ζ) (G ζ)) (hf : Continuous f) (hg : Continuous g) : Continuous G := by
  apply continuous_iff_continuousAt.mpr
  intro z₀
  change Tendsto G (𝓝 z₀) (𝓝 (G z₀))
  let c := (Real.exp (2 * Λ) * Λ)⁻¹ / 4
  let C := (d : ℝ) * (Real.exp (2 * Λ) * Λ)
  have hc : 0 < c := div_pos (inv_pos.mpr (mul_pos (Real.exp_pos _)
    (lt_of_lt_of_le zero_lt_one Q.ellipticity_parameter))) (by norm_num)
  have hb (ζ : ℂ) : ‖G ζ-G z₀‖ ^ 2 ≤
      2*(‖f ζ-f z₀‖*‖g ζ-g z₀‖ + complexForceShift d Λ ζ * ‖f ζ-f z₀‖^2)/c +
        ((‖ζ-z₀‖*C*‖f z₀‖)/c)^2 :=
    flux_absorb_linear c _ _ _ hc
      (fluxTransposeGradient_difference_energy (hfg ζ) (hfg z₀) (hG ζ) (hG z₀))
  have hfu : Tendsto (fun ζ => ‖f ζ-f z₀‖) (𝓝 z₀) (𝓝 0) := by
    simpa only [sub_self, norm_zero] using! ((hf.tendsto z₀).sub (tendsto_const_nhds (x := f z₀))).norm
  have hgu : Tendsto (fun ζ => ‖g ζ-g z₀‖) (𝓝 z₀) (𝓝 0) := by
    simpa only [sub_self, norm_zero] using! ((hg.tendsto z₀).sub (tendsto_const_nhds (x := g z₀))).norm
  have hzu : Tendsto (fun ζ : ℂ => ‖ζ-z₀‖) (𝓝 z₀) (𝓝 0) := by
    simpa only [sub_self, norm_zero] using!
      ((tendsto_id : Tendsto (fun ζ : ℂ => ζ) (𝓝 z₀) (𝓝 z₀)).sub (tendsto_const_nhds (x := z₀))).norm
  have hs : Continuous (fun ζ : ℂ => complexForceShift d Λ ζ) := by
    unfold complexForceShift
    fun_prop
  have he : Tendsto (fun ζ : ℂ =>
      2*(‖f ζ-f z₀‖*‖g ζ-g z₀‖ + complexForceShift d Λ ζ * ‖f ζ-f z₀‖^2)/c +
        ((‖ζ-z₀‖*C*‖f z₀‖)/c)^2) (𝓝 z₀) (𝓝 0) := by
    simpa only [zero_mul, mul_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
      add_zero, zero_div] using!
      (((hfu.mul hgu).add ((hs.tendsto z₀).mul (hfu.pow 2))).const_mul 2).div_const c |>.add
        ((((hzu.mul_const C).mul_const ‖f z₀‖).div_const c).pow 2)
  have ht := (squeeze_zero (fun ζ => sq_nonneg ‖G ζ-G z₀‖) hb he).sqrt
  simp only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] at ht
  exact tendsto_iff_norm_sub_tendsto_zero.mpr ht

/-- A continuous family of actual horizontal derivatives of an entire L2
family is itself entire. The proof transfers Cauchy's formula through the
closed horizontal derivative graph; no differentiability of the derivatives
is assumed. -/
theorem analyticAt_horizontalDerivative_of_continuous
    {f g : ℂ → Lp ℂ 2 (reducedLaw Q)} (i : Fin d)
    (hf : ∀ z, AnalyticAt ℂ f z) (hg : Continuous g)
    (hD : ∀ z, HasComplexHorizontalDerivative (reducedLaw Q)
      (reducedLaw_stationary Q) i (f z) (g z)) (z₀ : ℂ) :
    AnalyticAt ℂ g z₀ := by
  have hfc : Continuous f := continuous_iff_continuousAt.mpr fun z => (hf z).continuousAt
  have hp := hasFPowerSeriesOn_cauchy_integral
    (c := z₀) (R := (1 : ℝ≥0)) (hg.continuousOn.circleIntegrable (by norm_num)) (by norm_num)
  apply hp.analyticAt.congr
  filter_upwards [Metric.ball_mem_nhds z₀ (by norm_num : (0 : ℝ) < 1)] with w hw
  have hn : ∀ z ∈ Metric.sphere z₀ 1, z - w ≠ 0 := by
    intro z hz he
    have heq : z = w := sub_eq_zero.mp he
    subst z
    have hdist := Metric.mem_sphere.mp hz
    have hlt := Metric.mem_ball.mp hw
    linarith only [hdist, hlt]
  have hi : ContinuousOn (fun z : ℂ => (z - w)⁻¹) (Metric.sphere z₀ 1) :=
    (continuous_id.sub continuous_const).continuousOn.inv₀ hn
  have hfi := (hi.smul hfc.continuousOn).circleIntegrable (by norm_num : (0 : ℝ) ≤ 1)
  have hgi := (hi.smul hg.continuousOn).circleIntegrable (by norm_num : (0 : ℝ) ≤ 1)
  have hgraph : HasComplexHorizontalDerivative (reducedLaw Q) (reducedLaw_stationary Q) i
      (∮ z in C(z₀, 1), (z - w)⁻¹ • f z)
      (∮ z in C(z₀, 1), (z - w)⁻¹ • g z) := by
    rw [circleIntegral, circleIntegral,
      intervalIntegral.integral_of_le Real.two_pi_pos.le,
      intervalIntegral.integral_of_le Real.two_pi_pos.le]
    exact HasComplexHorizontalDerivative.integral_of_ae hfi.out.1 hgi.out.1
      (Eventually.of_forall fun θ =>
        ((hD (circleMap z₀ 1 θ)).smul ((circleMap z₀ 1 θ - w)⁻¹)).smul
          (deriv (circleMap z₀ 1) θ))
  have hcauchy := Complex.two_pi_I_inv_smul_circleIntegral_sub_inv_smul_of_differentiable_on_off_countable
    (s := (∅ : Set ℂ)) countable_empty hw hfc.continuousOn
    (fun z _ => (hf z).differentiableAt)
  have hs := hgraph.smul ((2 * Real.pi * Complex.I : ℂ)⁻¹)
  rw [hcauchy] at hs
  exact hs.unique (hD w)

/-- Entire value families with continuous full transpose generator coordinates
have entire actual horizontal gradients. -/
theorem analyticAt_horizontalGradient_of_transpose_generator
    {f g : ℂ → Lp ℂ 2 (reducedLaw Q)}
    {H : ℂ → PiLp 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q))}
    (hfg : ∀ ζ, IsComplexTransposeGeneratorPair Q i₀ ζ (f ζ) (g ζ))
    (hH : ∀ ζ, HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
      (f ζ) (H ζ)) (hf : ∀ ζ, AnalyticAt ℂ f ζ) (hg : Continuous g)
    (j : Fin d) (z₀ : ℂ) : AnalyticAt ℂ (fun ζ => H ζ j) z₀ := by
  have hc := continuous_horizontalGradient_of_transpose_generator hfg hH
    (continuous_iff_continuousAt.mpr fun ζ => (hf ζ).continuousAt) hg
  exact analyticAt_horizontalDerivative_of_continuous j hf
    ((PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q)) j).continuous.comp hc)
    (fun ζ => hH ζ j) z₀

/-- The Foundation primitive holomorphy contract applies to every actual
semigroup and its true bilinear transpose, by their uniqueness. -/
theorem analyticAt_finiteTimeFlux_transpose_primitive
    (hA : node_stationary_u2D_analytic_u2D_semigroupStmt)
    (D : StructuralData d) {Q : EnvironmentLaw d D.ellipticity D.dependenceRange}
    (hQ : HasSmoothBounds D Q)
    {P T : ℂ → ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : ∀ ζ, IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ (P ζ))
    (hT : ∀ ζ, IsComplexTransposeSemigroup Q (P ζ) (T ζ))
    (f : Lp ℂ 2 (reducedLaw Q)) (t : ℝ≥0) (z₀ : ℂ) :
    AnalyticAt ℂ (fun ζ => ∫ s in Icc (0 : ℝ) (t : ℝ), T ζ s.toNNReal f) z₀ := by
  have ha := ((hA d hd D).1 Q hQ).2.2 t f z₀ |>.2
  apply ha.congr
  apply Eventually.of_forall
  intro ζ
  change (∫ s in Icc (0 : ℝ) (t : ℝ),
    complexL2Transpose (reducedLaw Q) (forcedComplexEvolution Q ⟨0, by omega⟩ ζ s.toNNReal) f) = _
  simp only [(hT ζ).eq_complexL2Transpose]
  rw [(hP ζ).eq_forcedComplexEvolution]

/-- Every coordinate of the literal transpose primitive gradient is entire.
The argument uses its full conservative generator, including its force term. -/
theorem analyticAt_finiteTimeFlux_transpose_integral_gradient
    (hA : node_stationary_u2D_analytic_u2D_semigroupStmt)
    (D : StructuralData d) {Q : EnvironmentLaw d D.ellipticity D.dependenceRange}
    (hQ : HasSmoothBounds D Q)
    {β : Fin d → Lp ℂ 2 (reducedLaw Q)}
    {a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)} {μ : Lp ℂ 2 (reducedLaw Q)}
    {P T : ℂ → ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    {G F : ℂ → ℝ≥0 → FluxIndex d → Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hP : ∀ ζ, IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ (P ζ))
    (hT : ∀ ζ, IsComplexTransposeSemigroup Q (P ζ) (T ζ))
    (hF : ∀ ζ, IsFiniteTimeFlux hd Q ζ (P ζ) (T ζ) β a μ (G ζ) (F ζ))
    (t : ℝ≥0) (j : Fin d) (z₀ : ℂ) :
    AnalyticAt ℂ (fun ζ => ∫ s in Icc (0 : ℝ) (t : ℝ),
      G ζ s.toNNReal (.inr ()) j) z₀ := by
  let U := fun ζ => ∫ s in Icc (0 : ℝ) (t : ℝ), T ζ s.toNNReal (β ⟨0, by omega⟩)
  let H := fun ζ => WithLp.toLp 2 (fun k => ∫ s in Icc (0 : ℝ) (t : ℝ),
    G ζ s.toNNReal (.inr ()) k)
  have hH (ζ : ℂ) : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
      (U ζ) (H ζ) := by
    obtain ⟨hGc, hUc, hG, _⟩ := hF ζ
    have he (s : ℝ≥0) : HasComplexHorizontalGradient (reducedLaw Q)
        (reducedLaw_stationary Q) (T ζ s (β ⟨0, by omega⟩)) (G ζ s (.inr ())) := by
      simpa only [indexedEndpoint, Sum.elim_inr, transposeEndpoint] using! hG s (.inr ())
    have hi := timeFlux_integral_gradient (fun s => T ζ s (β ⟨0, by omega⟩))
      (fun s => G ζ s (.inr ())) (hUc _) (hGc (.inr ())) he t
    exact hi
  have hg : Continuous (fun ζ => T ζ t (β ⟨0, by omega⟩) - β ⟨0, by omega⟩) := by
    apply continuous_iff_continuousAt.mpr
    intro ζ
    have hop : AnalyticAt ℂ (fun z => T z t) ζ :=
      analyticAt_complexTransposeSemigroup (Q := Q) (i := ⟨0, by omega⟩) hP hT t ζ
    have happ : AnalyticAt ℂ (fun z => T z t (β ⟨0, by omega⟩)) ζ :=
      ((ContinuousLinearMap.apply ℂ _).analyticAt_bilinear _).comp₂
        (analyticAt_const (v := β ⟨0, by omega⟩)) hop
    exact happ.continuousAt.sub continuousAt_const
  exact analyticAt_horizontalGradient_of_transpose_generator
    (fun ζ => timeFlux_transpose_primitive_graph (hP ζ) (hT ζ) _ t) hH
    (fun ζ => analyticAt_finiteTimeFlux_transpose_primitive (hd := hd) hA D hQ hP hT (β ⟨0, by omega⟩) t ζ) hg j z₀
/-- The literal transpose flux includes its conservative force correction,
with the full anisotropic coefficient column. -/
theorem finiteTimeFlux_transpose_eq {ζ : ℂ}
    (ha : IsReducedCoefficientObservation Q a)
    (hF : IsFiniteTimeFlux hd Q ζ (P ζ) (T ζ) β a μ (G ζ) (F ζ))
    (t : ℝ≥0) (j : Fin d) :
    F ζ t (.inr ()) j = a j ⟨0, by omega⟩ + ∑ k, complexCoefficientMul Q j k
      (∫ s in Icc (0 : ℝ) (t : ℝ), G ζ s.toNNReal (.inr ()) k) -
        (2*ζ) • complexCoefficientMul Q j ⟨0, by omega⟩
          (∫ s in Icc (0 : ℝ) (t : ℝ), T ζ s.toNNReal (β ⟨0, by omega⟩)) := by
  obtain ⟨hG, hU, _, hf⟩ := hF
  let H (k : Fin d) := ∫ s in Icc (0 : ℝ) (t : ℝ), G ζ s.toNNReal (.inr ()) k
  let U := ∫ s in Icc (0 : ℝ) (t : ℝ), T ζ s.toNNReal (β ⟨0, by omega⟩)
  let B := ∑ k, complexCoefficientMul Q j k (H k)
  let V := complexCoefficientMul Q j ⟨0, by omega⟩ U
  apply Lp.ext
  filter_upwards [hf t (.inr ()) j,
    Lp.coeFn_sub (a j ⟨0, by omega⟩ + B) ((2*ζ) • V),
    Lp.coeFn_add (a j ⟨0, by omega⟩) B,
    Lp.coeFn_smul (2*ζ) V,
    fluxCoeFn_sum (reducedLaw Q) Finset.univ (fun k => complexCoefficientMul Q j k (H k)),
    ae_all_iff.mpr (fun k => complexCoefficientMul_coe Q j k (H k)),
    complexCoefficientMul_coe Q j ⟨0, by omega⟩ U,
    ae_all_iff.mpr (fun k => ha j k)] with ω hfω hsub hadd hsmul hsum hmul hv haω
  simp only [finiteTimeFluxObservation, Sum.elim_inr, transposeEndpoint] at hfω
  rw [hfω, hsub]
  simp only [Pi.sub_apply]
  rw [hadd, hsmul]
  change a j ⟨0, by omega⟩ ω + ∑ k, a j k ω * H k ω -
    2*ζ*a j ⟨0, by omega⟩ ω * U ω = _
  change _ = a j ⟨0, by omega⟩ ω + B ω - (2*ζ) * V ω
  rw [show B ω = ∑ k, (complexCoefficientMul Q j k (H k)) ω from hsum]
  simp only [hmul, V, hv, haω]
  ring

/-- The true transpose flux is entire in complex force, including its
additional conservative term. -/
theorem analyticAt_finiteTimeFlux_transpose
    (hA : node_stationary_u2D_analytic_u2D_semigroupStmt)
    (D : StructuralData d) {Q : EnvironmentLaw d D.ellipticity D.dependenceRange}
    (hQ : HasSmoothBounds D Q)
    {β : Fin d → Lp ℂ 2 (reducedLaw Q)}
    {a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)} {μ : Lp ℂ 2 (reducedLaw Q)}
    {P T : ℂ → ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    {G F : ℂ → ℝ≥0 → FluxIndex d → Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hP : ∀ ζ, IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ (P ζ))
    (hT : ∀ ζ, IsComplexTransposeSemigroup Q (P ζ) (T ζ))
    (ha : IsReducedCoefficientObservation Q a)
    (hF : ∀ ζ, IsFiniteTimeFlux hd Q ζ (P ζ) (T ζ) β a μ (G ζ) (F ζ))
    (t : ℝ≥0) (j : Fin d) (z₀ : ℂ) :
    AnalyticAt ℂ (fun ζ => F ζ t (.inr ()) j) z₀ := by
  have hs := Finset.univ.analyticAt_fun_sum (fun k _ =>
    ((complexCoefficientMul Q j k).analyticAt _).comp
      (analyticAt_finiteTimeFlux_transpose_integral_gradient hA D hQ hP hT hF t k z₀))
  have hu := ((complexCoefficientMul Q j ⟨0, by omega⟩).analyticAt _).comp
    (analyticAt_finiteTimeFlux_transpose_primitive (hd := hd) hA D hQ hP hT (β ⟨0, by omega⟩) t z₀)
  have hc := ((analyticAt_const (v := a j ⟨0, by omega⟩)).add hs).sub
    (((analyticAt_const (v := (2 : ℂ))).mul analyticAt_id).fun_smul hu)
  apply hc.congr
  apply Eventually.of_forall
  intro ζ
  exact (finiteTimeFlux_transpose_eq ha (hF ζ) t j).symm

/-- Every actual finite-time flux coordinate is entire in force. -/
theorem analyticAt_finiteTimeFlux
    (hA : node_stationary_u2D_analytic_u2D_semigroupStmt)
    (D : StructuralData d) {Q : EnvironmentLaw d D.ellipticity D.dependenceRange}
    (hQ : HasSmoothBounds D Q)
    {β : Fin d → Lp ℂ 2 (reducedLaw Q)}
    {a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)} {μ : Lp ℂ 2 (reducedLaw Q)}
    {P T : ℂ → ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    {G F : ℂ → ℝ≥0 → FluxIndex d → Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hP : ∀ ζ, IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ (P ζ))
    (hT : ∀ ζ, IsComplexTransposeSemigroup Q (P ζ) (T ζ))
    (ha : IsReducedCoefficientObservation Q a)
    (hF : ∀ ζ, IsFiniteTimeFlux hd Q ζ (P ζ) (T ζ) β a μ (G ζ) (F ζ))
    (t : ℝ≥0) (ν : FluxIndex d) (j : Fin d) (z₀ : ℂ) :
    AnalyticAt ℂ (fun ζ => F ζ t ν j) z₀ := by
  cases ν with
  | inl i => exact analyticAt_finiteTimeFlux_forward hP ha hF t i j z₀
  | inr u => exact analyticAt_finiteTimeFlux_transpose hA D hQ hP hT ha hF t j z₀

/-- Coercivity of the full transpose graph controls its actual Euclidean
horizontal gradient, with only structural constants. -/
theorem norm_sq_horizontalGradient_transpose_generator_le
    {ζ : ℂ} {f g : Lp ℂ 2 (reducedLaw Q)}
    (hfg : IsComplexTransposeGeneratorPair Q i₀ ζ f g)
    {H : PiLp 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q))}
    (hH : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) f H) :
    ((Real.exp (2 * Λ) * Λ)⁻¹ / 4) * ‖H‖ ^ 2 ≤
      ‖f‖ * ‖g‖ + complexForceShift d Λ ζ * ‖f‖ ^ 2 := by
  have ht := hfg.conjugate_test hH f H hH
  have hb := reduced_complex_energy_lowerBound Q (fun j => H j)
  rw [← PiLp.norm_sq_eq_of_L2] at hb
  have hy := fluxTransposeForcePair_le (i₀ := i₀) ζ f H
  have hi : -(inner ℂ f g).re ≤ ‖f‖ * ‖g‖ :=
    ((neg_le_abs _).trans (Complex.abs_re_le_norm _)).trans (norm_inner_le_norm _ _)
  have hr : (inner ℂ f g).re = -(1 / 2 : ℝ) *
      (∫ ω, ∑ j, ∑ k, star (H j ω) * (ω.1 0 j k : ℂ) * H k ω
        ∂reducedLaw Q).re +
      (ζ * inner ℂ (complexForceDrift Q i₀ H) f).re := by
    rw [ht, Complex.add_re, Complex.mul_re]
    norm_num
  linarith only [hb, hy, hi, hr]

/-- The actual transpose shares the structural L2 semigroup bound. -/
theorem norm_finiteTimeFlux_transpose_operator_le {ζ : ℂ}
    (hP : IsComplexEnvironmentSemigroup Q i₀ ζ (P ζ))
    (hT : IsComplexTransposeSemigroup Q (P ζ) (T ζ)) (t : ℝ≥0) :
    ‖T ζ t‖ ≤ Real.exp (complexForceShift d Λ ζ * (t : ℝ)) := by
  rw [congrFun hT.eq_complexL2Transpose t, norm_complexL2Transpose]
  exact hP.norm_le t

/-- The literal transpose primitive has an explicit finite-horizon L2 bound. -/
theorem norm_finiteTimeFlux_transpose_primitive_le {ζ : ℂ}
    (hP : IsComplexEnvironmentSemigroup Q i₀ ζ (P ζ))
    (hT : IsComplexTransposeSemigroup Q (P ζ) (T ζ))
    (f : Lp ℂ 2 (reducedLaw Q)) (t : ℝ≥0) :
    ‖∫ s in Icc (0 : ℝ) (t : ℝ), T ζ s.toNNReal f‖ ≤
      (t : ℝ) * Real.exp (complexForceShift d Λ ζ * (t : ℝ)) * ‖f‖ := by
  have hb (s : ℝ) (hs : s ∈ Icc (0 : ℝ) (t : ℝ)) :
      ‖T ζ s.toNNReal f‖ ≤ Real.exp (complexForceShift d Λ ζ * (t : ℝ)) * ‖f‖ := by
    apply ((T ζ s.toNNReal).le_opNorm f).trans
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    apply (norm_finiteTimeFlux_transpose_operator_le hP hT s.toNNReal).trans
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left
      (by simpa only [Real.toNNReal_of_nonneg hs.1] using! hs.2)
      (complexForceShift_nonneg Q ζ)
  calc
    _ ≤ (t : ℝ) * (Real.exp (complexForceShift d Λ ζ * (t : ℝ)) * ‖f‖) := by
      have hv : volume.real (Icc (0 : ℝ) (t : ℝ)) = (t : ℝ) := by
        rw [Measure.real, Real.volume_Icc, sub_zero]
        exact ENNReal.toReal_ofReal t.property
      have hi := norm_setIntegral_le_of_norm_le_const
        (measure_Icc_lt_top (μ := (volume : Measure ℝ))) hb
      rw [hv] at hi
      simpa only [mul_comm] using! hi
    _ = _ := by ring

/-- Explicit coercive control of the actual transpose primitive gradient,
without force derivatives or arbitrary horizon constants. -/
theorem norm_sq_finiteTimeFlux_transpose_integral_gradient_le {ζ : ℂ}
    (hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ (P ζ))
    (hT : IsComplexTransposeSemigroup Q (P ζ) (T ζ))
    (hF : IsFiniteTimeFlux hd Q ζ (P ζ) (T ζ) β a μ (G ζ) (F ζ))
    (t : ℝ≥0) :
    ((Real.exp (2 * Λ) * Λ)⁻¹ / 4) *
      (∑ j, ‖∫ s in Icc (0 : ℝ) (t : ℝ), G ζ s.toNNReal (.inr ()) j‖ ^ 2) ≤
      ((t : ℝ) * Real.exp (complexForceShift d Λ ζ * (t : ℝ)) * ‖β ⟨0, by omega⟩‖) *
        ((Real.exp (complexForceShift d Λ ζ * (t : ℝ)) + 1) * ‖β ⟨0, by omega⟩‖) +
      complexForceShift d Λ ζ *
        ((t : ℝ) * Real.exp (complexForceShift d Λ ζ * (t : ℝ)) * ‖β ⟨0, by omega⟩‖)^2 := by
  obtain ⟨hGc, hUc, hG, _⟩ := hF
  have he (s : ℝ≥0) : HasComplexHorizontalGradient (reducedLaw Q)
      (reducedLaw_stationary Q) (T ζ s (β ⟨0, by omega⟩)) (G ζ s (.inr ())) := by
    simpa only [indexedEndpoint, Sum.elim_inr, transposeEndpoint] using! hG s (.inr ())
  have hH := timeFlux_integral_gradient _ (fun s => G ζ s (.inr ()))
    (hUc _) (hGc (.inr ())) he t
  have hc := norm_sq_horizontalGradient_transpose_generator_le
    (timeFlux_transpose_primitive_graph hP hT (β ⟨0, by omega⟩) t)
    (H := WithLp.toLp 2 (fun j => ∫ s in Icc (0 : ℝ) (t : ℝ),
      G ζ s.toNNReal (.inr ()) j)) hH
  rw [PiLp.norm_sq_eq_of_L2] at hc
  have hu := norm_finiteTimeFlux_transpose_primitive_le hP hT (β ⟨0, by omega⟩) t
  have hv : ‖T ζ t (β ⟨0, by omega⟩) - β ⟨0, by omega⟩‖ ≤
      (Real.exp (complexForceShift d Λ ζ * (t : ℝ)) + 1) * ‖β ⟨0, by omega⟩‖ := by
    apply (norm_sub_le _ _).trans
    have hh := ((T ζ t).le_opNorm (β ⟨0, by omega⟩)).trans
      (mul_le_mul_of_nonneg_right (norm_finiteTimeFlux_transpose_operator_le hP hT t)
        (norm_nonneg _))
    nlinarith only [hh]
  exact hc.trans (add_le_add (mul_le_mul hu hv (norm_nonneg _) (by positivity))
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hu 2)
      (complexForceShift_nonneg Q ζ)))

/-- The literal flux and its force derivative are holomorphic on the full
plane, so in particular on the required radius-three force disc. -/
theorem differentiableOn_finiteTimeFlux_force_disc
    (hA : node_stationary_u2D_analytic_u2D_semigroupStmt)
    (D : StructuralData d) {Q : EnvironmentLaw d D.ellipticity D.dependenceRange}
    (hQ : HasSmoothBounds D Q)
    {β : Fin d → Lp ℂ 2 (reducedLaw Q)}
    {a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)} {μ : Lp ℂ 2 (reducedLaw Q)}
    {P T : ℂ → ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    {G F : ℂ → ℝ≥0 → FluxIndex d → Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hP : ∀ ζ, IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ (P ζ))
    (hT : ∀ ζ, IsComplexTransposeSemigroup Q (P ζ) (T ζ))
    (ha : IsReducedCoefficientObservation Q a)
    (hF : ∀ ζ, IsFiniteTimeFlux hd Q ζ (P ζ) (T ζ) β a μ (G ζ) (F ζ))
    (t : ℝ≥0) (ν : FluxIndex d) (j : Fin d) :
    DifferentiableOn ℂ (fun ζ => F ζ t ν j) {ζ | ‖ζ‖ * Real.sqrt (t : ℝ) < 3} ∧
    DifferentiableOn ℂ (fun ζ => deriv (fun z => F z t ν j) ζ)
      {ζ | ‖ζ‖ * Real.sqrt (t : ℝ) < 3} := by
  have hh := analyticAt_finiteTimeFlux hA D hQ hP hT ha hF t ν j
  exact ⟨fun ζ _ => (hh ζ).differentiableAt.differentiableWithinAt,
    fun ζ _ => (hh ζ).deriv.differentiableAt.differentiableWithinAt⟩

/-- The identical centered Gaussian average used in the target and its force
derivative are holomorphic on the required disc, uniformly in the scale. -/
theorem differentiableOn_finiteTimeFlux_gaussian_force_disc
    (hA : node_stationary_u2D_analytic_u2D_semigroupStmt)
    (D : StructuralData d) {Q : EnvironmentLaw d D.ellipticity D.dependenceRange}
    (hQ : HasSmoothBounds D Q)
    {β : Fin d → Lp ℂ 2 (reducedLaw Q)}
    {a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)} {μ : Lp ℂ 2 (reducedLaw Q)}
    {P T : ℂ → ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    {G F : ℂ → ℝ≥0 → FluxIndex d → Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hP : ∀ ζ, IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ (P ζ))
    (hT : ∀ ζ, IsComplexTransposeSemigroup Q (P ζ) (T ζ))
    (ha : IsReducedCoefficientObservation Q a)
    (hF : ∀ ζ, IsFiniteTimeFlux hd Q ζ (P ζ) (T ζ) β a μ (G ζ) (F ζ))
    (t : ℝ≥0) (ν : FluxIndex d) (ρ : ℝ) (hρ : 1 ≤ ρ) (j : Fin d) :
    let A := fun ζ => ∫ x : Vec d, (Correctors.euclideanHeatKernel (ρ ^ 2) x : ℂ) •
      complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x
        (centeredComplexLp Q (F ζ t ν j))
    DifferentiableOn ℂ A {ζ | ‖ζ‖ * Real.sqrt (t : ℝ) < 3} ∧
    DifferentiableOn ℂ (fun ζ => deriv A ζ) {ζ | ‖ζ‖ * Real.sqrt (t : ℝ) < 3} := by
  have hh := fun ζ => analyticAt_fluxGaussianAverage
    (analyticAt_finiteTimeFlux hA D hQ hP hT ha hF t ν j ζ) ρ hρ
  exact ⟨fun ζ _ => (hh ζ).differentiableAt.differentiableWithinAt,
    fun ζ _ => (hh ζ).deriv.differentiableAt.differentiableWithinAt⟩

private theorem flux_drift_norm_bound {d : ℕ}
    (D : StructuralData d) (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (hQ : HasSmoothBounds D Q) (β : Fin d → Lp ℂ 2 (reducedLaw Q))
    (hβ : IsReducedDriftObservation Q hQ β) (j : Fin d) :
    ‖β j‖ ≤ (1 / 2 : ℝ) * d * reducedLipschitzConstant D.ellipticity := by
  letI := reducedLaw_probability Q
  have hD := D.one_le_ellipticity
  have hB : 0 ≤ (1 / 2 : ℝ) * d *
      reducedLipschitzConstant D.ellipticity := by
    unfold reducedLipschitzConstant
    positivity
  have hb := Lp.norm_le_of_ae_bound (f := β j) hB (by
    filter_upwards [hβ.ae_eq_cdiv j, ae_abs_cdiv_le_reduced Q j] with ω hω hbound
    rw [hω]
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos (by norm_num :
      (0 : ℝ) < 1 / 2)]
    nlinarith only [hbound])
  simpa only [measureUnivNNReal, measure_univ, ENNReal.toNNReal_one, NNReal.coe_one,
    Real.one_rpow, one_mul] using! hb


private theorem flux_coefficient_norm_bound
    (ha : IsReducedCoefficientObservation Q a) (j k : Fin d) :
    ‖a j k‖ ≤ Real.exp (2 * Λ) * Λ := by
  letI := reducedLaw_probability Q
  have hK : 0 ≤ Real.exp (2 * Λ) * Λ :=
    mul_nonneg (Real.exp_pos _).le (zero_le_one.trans Q.ellipticity_parameter)
  have hb := Lp.norm_le_of_ae_bound (f := a j k) hK (by
    filter_upwards [ha j k, Correctors.ae_reducedEnvironmentLaw_origin_elliptic Q]
      with ω hω he
    rw [hω, Complex.norm_real, Real.norm_eq_abs]
    apply abs_entry_le_of_quadratic_bounds hK (ω.1 0) (he 0).1
    · intro ξ
      exact (mul_nonneg (inv_nonneg.mpr hK) (euclideanSq_nonneg_coords ξ)).trans
        ((he 0).2 ξ).1
    · exact fun ξ => ((he 0).2 ξ).2)
  simpa only [measureUnivNNReal, measure_univ, ENNReal.toNNReal_one, NNReal.coe_one,
    Real.one_rpow, one_mul] using! hb

omit d in
private theorem flux_force_disc_bounds {ζ : ℂ} {t : ℝ}
    (ht : 2 ≤ t) (hζ : ‖ζ‖ * Real.sqrt t ≤ 2) :
    ‖ζ‖ ≤ 2 ∧ ‖ζ‖ ^ 2 * t ≤ 4 := by
  have hs : 1 ≤ Real.sqrt t := (Real.le_sqrt (by norm_num) (by linarith)).2 (by linarith)
  have hsq := Real.sq_sqrt (show 0 ≤ t by linarith)
  constructor
  · nlinarith only [mul_le_mul_of_nonneg_left hs (norm_nonneg ζ), hζ]
  · nlinarith only [sq_nonneg (‖ζ‖ * Real.sqrt t - 2),
      mul_self_le_mul_self (by positivity : 0 ≤ ‖ζ‖ * Real.sqrt t) hζ, hsq]

/-- The quadratic force shift stays bounded on the shrinking parabolic disc. -/
theorem flux_force_shift_mul_time_le (Q : EnvironmentLaw d Λ r) {ζ : ℂ} {t : ℝ}
    (ht : 2 ≤ t) (hζ : ‖ζ‖ * Real.sqrt t ≤ 2) :
    complexForceShift d Λ ζ * t ≤
      4 * (Real.exp (2 * Λ) * Λ) * ((d : ℝ) * (Real.exp (2 * Λ) * Λ)) ^ 2 := by
  have hK : 0 ≤ Real.exp (2 * Λ) * Λ :=
    mul_nonneg (Real.exp_pos _).le (zero_le_one.trans Q.ellipticity_parameter)
  have hb := (flux_force_disc_bounds ht hζ).2
  unfold complexForceShift
  nlinarith only [mul_le_mul_of_nonneg_left hb
    (mul_nonneg hK (sq_nonneg ((d : ℝ) * (Real.exp (2 * Λ) * Λ))))]

private theorem flux_row_norm_bound (j : Fin d)
    (H : PiLp 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q))) :
    ‖∑ k, complexCoefficientMul Q j k (H k)‖ ≤
      (d : ℝ) * (Real.exp (2 * Λ) * Λ) * ‖H‖ := by
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _ : Fin d, (Real.exp (2 * Λ) * Λ) * ‖H‖ := by
      apply Finset.sum_le_sum
      intro k _
      exact ((complexCoefficientMul Q j k).le_opNorm _).trans
        (mul_le_mul (norm_complexCoefficientMul_le Q j k) (PiLp.norm_apply_le H k)
          (norm_nonneg _) (mul_nonneg (Real.exp_pos _).le
            (zero_le_one.trans Q.ellipticity_parameter)))
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]; ring

end EinsteinFull.Blueprint

namespace EinsteinFull.Blueprint
open EinsteinRelation

/-- A deterministic polynomial bound for every literal flux, with the constant
chosen before the law and the common exponent two. -/
theorem exists_finiteTimeFlux_polynomial_bound (d : ℕ) (hd : 2 ≤ d)
    (D : StructuralData d) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
    ∀ (ζ : ℂ) (P T : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
      (G F : ℝ≥0 → FluxIndex d → Fin d → Lp ℂ 2 (reducedLaw Q)),
      IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P →
      IsComplexTransposeSemigroup Q P T →
      IsFiniteTimeFlux hd Q ζ P T β a μ G F →
    ∀ (t : ℝ≥0), 2 ≤ (t : ℝ) → ‖ζ‖ * Real.sqrt (t : ℝ) ≤ 2 →
    ∀ ν, Real.sqrt (∑ j, ‖F t ν j‖ ^ 2) ≤ C * (2 + (t : ℝ)) ^ 2 := by
  let K := Real.exp (2 * D.ellipticity) * D.ellipticity
  let B := (1 / 2 : ℝ) * d * reducedLipschitzConstant D.ellipticity
  let S := 4 * K * ((d : ℝ) * K)^2
  let E := Real.exp S
  let c := K⁻¹ / 4
  let L := E * B * ((E + 1) * B) + S * (E * B)^2
  let H := 1 + L / c
  let J := 4 * Real.sqrt K * Real.exp (65 * S) * (B + 2 * K)
  let C := (d : ℝ) * (K + (d : ℝ) * K * (H + J) + 4 * K * E * B) + 1
  have hK : 0 < K := mul_pos (Real.exp_pos _) (lt_of_lt_of_le zero_lt_one D.one_le_ellipticity)
  have hD := D.one_le_ellipticity
  have hB : 0 ≤ B := by dsimp [B, reducedLipschitzConstant]; positivity
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hE : 0 < E := Real.exp_pos _
  have hc : 0 < c := by dsimp [c]; positivity
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hJ : 0 ≤ J := by dsimp [J]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro Q hQ β a μ hβ ha ζ P T G F hP hT hF t ht hζ ν
  have hb (i : Fin d) : ‖β i‖ ≤ B := flux_drift_norm_bound D Q hQ β hβ i
  have ha' (i j : Fin d) : ‖a i j‖ ≤ K := flux_coefficient_norm_bound ha i j
  have hz : ‖ζ‖ ≤ 2 := (flux_force_disc_bounds ht hζ).1
  let σ := complexForceShift d D.ellipticity ζ
  have hs0 : 0 ≤ σ := complexForceShift_nonneg Q ζ
  have hst : σ * (t : ℝ) ≤ S := flux_force_shift_mul_time_le Q ht hζ
  have hs : σ ≤ S := by nlinarith only [mul_le_mul_of_nonneg_left ht hs0, hst, hs0]
  have he : Real.exp (σ * (t : ℝ)) ≤ E := Real.exp_le_exp.mpr hst
  have he65 : Real.exp (65 * σ * (t : ℝ)) ≤ Real.exp (65 * S) := by
    apply Real.exp_le_exp.mpr; linarith only [hst]
  let p := (2 + (t : ℝ)) ^ 2
  have hp : 1 ≤ p := by dsimp [p]; nlinarith only [ht, sq_nonneg (t : ℝ)]
  have htp : (t : ℝ) ≤ p := by dsimp [p]; nlinarith only [ht, sq_nonneg (t : ℝ)]
  have ht2p : (t : ℝ)^2 ≤ p := by dsimp [p]; nlinarith only [ht]
  have hsp : Real.sqrt (t : ℝ) ≤ p := by
    have hsq : (t : ℝ) ≤ p ^ 2 := by nlinarith only [htp, hp, sq_nonneg (p - 1)]
    exact (Real.sqrt_le_iff).2 ⟨by positivity, hsq⟩
  let V (ν : FluxIndex d) : PiLp 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q)) :=
    WithLp.toLp 2 (fun j => ∫ s in Icc (0 : ℝ) (t : ℝ), G s.toNNReal ν j)
  have hVf (i : Fin d) : ‖V (.inl i)‖ ≤ J * p := by
    have hg := norm_finiteTimeFlux_forward_integral_gradient_le
      (P := fun _ => P) (T := fun _ => T) (G := fun _ => G) (F := fun _ => F) hP hF t i
    have hf : ‖β i + ζ • a ⟨0, by omega⟩ i‖ ≤ B + 2 * K := by
      apply (norm_add_le _ _).trans
      rw [norm_smul]
      exact add_le_add (hb i) (mul_le_mul hz (ha' _ _) (norm_nonneg _) (by norm_num))
    rw [← PiLp.norm_eq_of_L2 (V (.inl i))] at hg
    apply hg.trans
    dsimp [J]
    calc
      _ ≤ 4 * Real.sqrt K * p * Real.exp (65 * S) * (B + 2 * K) :=
        mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left hsp (by positivity))
          he65 (Real.exp_pos _).le (by positivity)) hf (norm_nonneg _) (by positivity)
      _ = _ := by ring
  have hVt : ‖V (.inr ())‖ ≤ H * p := by
    have hg := norm_sq_finiteTimeFlux_transpose_integral_gradient_le
      (P := fun _ => P) (T := fun _ => T) (G := fun _ => G) (F := fun _ => F) hP hT hF t
    rw [← PiLp.norm_sq_eq_of_L2 _ (V (.inr ()))] at hg
    have hu : (t : ℝ) * Real.exp (σ * (t : ℝ)) * ‖β ⟨0, by omega⟩‖ ≤
        (t : ℝ) * (E * B) := by
      simpa only [mul_assoc] using! mul_le_mul_of_nonneg_left
        (mul_le_mul he (hb _) (norm_nonneg _) hE.le) t.property
    have hv : (Real.exp (σ * (t : ℝ)) + 1) * ‖β ⟨0, by omega⟩‖ ≤ (E + 1) * B :=
      mul_le_mul (by linarith only [he] : Real.exp (σ * (t : ℝ)) + 1 ≤ E + 1) (hb _) (norm_nonneg _) (by positivity)
    have henergy : c * ‖V (.inr ())‖^2 ≤ L * p := by
      apply hg.trans
      calc
        _ ≤ ((t : ℝ) * (E * B)) * ((E + 1) * B) + S * ((t : ℝ) * (E * B))^2 :=
          add_le_add (mul_le_mul hu hv (by positivity) (by positivity))
            (mul_le_mul hs (pow_le_pow_left₀ (by positivity) hu 2) (by positivity) hS)
        _ = (E * B * ((E + 1) * B)) * (t : ℝ) +
            (S * (E * B)^2) * (t : ℝ)^2 := by ring
        _ ≤ L * p := by
          dsimp [L]
          nlinarith only [mul_le_mul_of_nonneg_left htp (by positivity :
            0 ≤ E * B * ((E + 1) * B)),
            mul_le_mul_of_nonneg_left ht2p (by positivity : 0 ≤ S * (E * B)^2)]
    have hn : ‖V (.inr ())‖ ≤ 1 + ‖V (.inr ())‖^2 := by nlinarith only [sq_nonneg (‖V (.inr ())‖ - 1)]
    have hsq : ‖V (.inr ())‖^2 ≤ L / c * p := by
      rw [div_mul_eq_mul_div]
      exact (le_div_iff₀ hc).2 (by nlinarith only [henergy])
    dsimp [H]
    nlinarith only [hn, hsq, hp]
  have hu : ‖∫ s in Icc (0 : ℝ) (t : ℝ), T s.toNNReal (β ⟨0, by omega⟩)‖ ≤
      (E * B) * p := by
    apply (norm_finiteTimeFlux_transpose_primitive_le (P := fun _ => P)
      (T := fun _ => T) hP hT _ t).trans
    calc
      _ ≤ (t : ℝ) * (E * B) := by
        simpa only [mul_assoc] using! mul_le_mul_of_nonneg_left
          (mul_le_mul he (hb _) (norm_nonneg _) hE.le) t.property
      _ ≤ _ := by nlinarith only [mul_le_mul_of_nonneg_right htp (mul_nonneg hE.le hB)]
  have hcoord (j : Fin d) : ‖F t ν j‖ ≤
      (K + (d : ℝ) * K * (H + J) + 4 * K * E * B) * p := by
    cases ν with
    | inl i =>
      rw [finiteTimeFlux_forward_eq (P := fun _ => P) (T := fun _ => T)
        (G := fun _ => G) (F := fun _ => F) ha hF t i j]
      apply (norm_add_le _ _).trans
      have hr := flux_row_norm_bound j (V (.inl i))
      change ‖∑ k, complexCoefficientMul Q j k (∫ s in Icc (0 : ℝ) (t : ℝ),
        G s.toNNReal (.inl i) k)‖ ≤ (d : ℝ) * K * ‖V (.inl i)‖ at hr
      have hm := mul_le_mul_of_nonneg_left (hVf i) (show 0 ≤ (d : ℝ) * K by positivity)
      have hkp := mul_le_mul_of_nonneg_left hp hK.le
      nlinarith only [hr, hm, hkp, ha' j i,
        mul_nonneg (show 0 ≤ (d : ℝ) * K * H by positivity) (show 0 ≤ p by positivity),
        mul_nonneg (show 0 ≤ 4 * K * E * B by positivity) (show 0 ≤ p by positivity)]
    | inr u =>
      cases u
      rw [finiteTimeFlux_transpose_eq (P := fun _ => P) (T := fun _ => T)
        (G := fun _ => G) (F := fun _ => F) ha hF t j]
      apply (norm_sub_le _ _).trans
      have hr := flux_row_norm_bound j (V (.inr ()))
      change ‖∑ k, complexCoefficientMul Q j k (∫ s in Icc (0 : ℝ) (t : ℝ),
        G s.toNNReal (.inr ()) k)‖ ≤ (d : ℝ) * K * ‖V (.inr ())‖ at hr
      have hm := mul_le_mul_of_nonneg_left hVt (show 0 ≤ (d : ℝ) * K by positivity)
      have hkp := mul_le_mul_of_nonneg_left hp hK.le
      have hx : ‖(2 * ζ) • complexCoefficientMul Q j ⟨0, by omega⟩
          (∫ s in Icc (0 : ℝ) (t : ℝ), T s.toNNReal (β ⟨0, by omega⟩))‖ ≤
          4 * K * (E * B * p) := by
        rw [norm_smul, norm_mul, Complex.norm_ofNat]
        have hm' := ((complexCoefficientMul Q j ⟨0, by omega⟩).le_opNorm _).trans
          (mul_le_mul (norm_complexCoefficientMul_le Q _ _) hu (norm_nonneg _) hK.le)
        calc
          _ ≤ 4 * (K * (E * B * p)) := mul_le_mul
            (by linarith only [hz] : 2 * ‖ζ‖ ≤ 4) hm' (norm_nonneg _) (by norm_num)
          _ = _ := by ring
      have hh := norm_add_le (a j ⟨0, by omega⟩)
        (∑ k, complexCoefficientMul Q j k ((V (.inr ())) k))
      nlinarith only [hr, hm, hkp, hx, hh, ha' j ⟨0, by omega⟩,
        mul_nonneg (show 0 ≤ (d : ℝ) * K by positivity) hJ,
        mul_nonneg (show 0 ≤ (d : ℝ) * K * J by positivity) (show 0 ≤ p by positivity)]
  have hn : Real.sqrt (∑ j, ‖F t ν j‖ ^ 2) ≤ ∑ j, ‖F t ν j‖ := by
    exact Real.sqrt_le_iff.mpr ⟨Finset.sum_nonneg (fun j _ => norm_nonneg _),
      Finset.sum_sq_le_sq_sum_of_nonneg (fun j _ => norm_nonneg _)⟩
  apply hn.trans
  calc
    _ ≤ ∑ _ : Fin d, (K + (d : ℝ) * K * (H + J) + 4 * K * E * B) * p :=
      Finset.sum_le_sum fun j _ => hcoord j
    _ ≤ C * p := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      dsimp [C]
      nlinarith only [show 0 ≤ p by positivity]

/-- Entire force dependence of the literal flux, together with structural
polynomial control and Cauchy's bound for its centered Gaussian averages. -/
theorem node_stationary_u2D_analytic_u2D_semigroup_u23_flux_of_deps
    (hA : node_stationary_u2D_analytic_u2D_semigroupStmt)
    (hflux : node_e_u3A_time_u2D_fluxStmt) :
    node_stationary_u2D_analytic_u2D_semigroup_u23_fluxStmt := by
  intro d hd D
  obtain ⟨C, hC, hb⟩ := exists_finiteTimeFlux_polynomial_bound d hd D
  refine ⟨C, 2, hC, ?_⟩
  intro Q hQ β a μ hβ ha hμ P T hP hT
  classical
  have hex (ζ : ℂ) := hflux d hd D Q hQ β a μ hβ ha hμ ζ (P ζ) (T ζ) (hP ζ) (hT ζ)
  choose G F hF using hex
  have hF' : ∀ ζ, IsFiniteTimeFlux hd Q ζ (P ζ) (T ζ) β a μ (G ζ) (F ζ) :=
    fun ζ => (hF ζ).1
  refine ⟨G, F, hF', ?_, ?_, ?_⟩
  · intro t _ht ν j
    exact differentiableOn_finiteTimeFlux_force_disc hA D hQ hP hT ha hF' t ν j
  · intro t _ht ν ρ hρ j
    exact differentiableOn_finiteTimeFlux_gaussian_force_disc hA D hQ hP hT ha hF' t ν ρ hρ j
  · intro t ht ν
    have hbound (ζ : ℂ) (hz : ‖ζ‖ * Real.sqrt (t : ℝ) ≤ 2) :=
      hb Q hQ β a μ hβ ha ζ (P ζ) (T ζ) (G ζ) (F ζ)
        (hP ζ) (hT ζ) (hF' ζ) t ht hz ν
    refine ⟨hbound, ?_⟩
    intro ρ hρ ζ hζ
    have hh := norm_deriv_fluxGaussianAverage_vector_le (Q := Q)
      (f := fun z => F z t ν) (by linarith only [ht] : 0 < (t : ℝ))
      (fun j => (differentiableOn_finiteTimeFlux_force_disc hA D hQ hP hT ha hF' t ν j).1)
      hbound ρ hρ hζ
    simpa only [mul_right_comm C ((2 + (t : ℝ)) ^ 2) (Real.sqrt (t : ℝ))] using! hh

end EinsteinFull.Blueprint
