import EinsteinFull.Calculus.C2EndpointTransposeLocalObservation
import EinsteinFull.Calculus.C6ShortTimeTransposeEndpointProjection

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators
noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinFull EinsteinRelation

/-- At zero time the actual transpose endpoint is already local. -/
theorem c25_transpose_endpoint_zero_local {d : ℕ} {D : StructuralData d}
    {Q : EnvironmentLaw d D.ellipticity D.dependenceRange}
    {hQ : HasSmoothBounds D Q} {β : Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hβ : IsReducedDriftObservation Q hQ β) (i : Fin d) {ζ : ℂ}
    {P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (hPdag : IsComplexTransposeSemigroup Q P Pdag) (ρ : ℝ) (hρ : 1 ≤ ρ) :
    IsComplexLocalObservation Q ρ (transposeEndpoint Q i Pdag β 0) := by
  simpa only [transposeEndpoint, hPdag.zero hP, ContinuousLinearMap.id_apply] using
    c6_short_time_initial_drift_local hβ i hρ

/-- The Gaussian weight in the local maximum at half scale is the squared
weight in the retained transpose comparison. -/
theorem c25_half_scale_gaussian_weight (x L : ℝ) (hL : 0 < L) :
    Real.exp (-x / (L / 2)) = Real.exp (-x / L) ^ 2 := by
  rw [pow_two, ← Real.exp_add]
  congr 1
  field_simp [ne_of_gt hL]
  <;> ring

/-- Transfer the squared-weight decay to the weight used by the local
maximum estimate, preserving the same residual and measure. -/
theorem c25_gaussian_decay_half_scale {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (q : α → ℝ) (Z : α → ℂ) (L K c ρ : ℝ) (hL : 0 < L)
    (hdecay : (∫⁻ z, ENNReal.ofReal
      (Real.exp (-q z / L) ^ 2 * ‖Z z‖ ^ 2) ∂μ) ≤
        ENNReal.ofReal (K * Real.exp (-c * ρ ^ 2))) :
    (∫⁻ z, ENNReal.ofReal
      (Real.exp (-q z / (L / 2)) * ‖Z z‖ ^ 2) ∂μ) ≤
        ENNReal.ofReal (K * Real.exp (-c * ρ ^ 2)) := by
  simpa only [c25_half_scale_gaussian_weight _ _ hL] using hdecay

/-- The retained drift comparison in the Gaussian convention of the local
maximum estimate, with constants fixed before the environment law. -/
theorem c25_transpose_actual_gaussian_spacetime_decay_half_scale
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) (B Cχ : ℝ) (hCχ : 0 ≤ Cχ) :
    let Λ := Real.exp (2 * D.ellipticity) * D.ellipticity
    ∃ L K c : ℝ, 32 * Λ ^ 3 ≤ L ∧ 0 < L ∧ 0 < K ∧ 0 < c ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q) (β : Fin d → Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → ∀ (i : Fin d) (ζ : ℂ), ‖ζ‖ ≤ B →
    ∀ P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      IsComplexEnvironmentSemigroup Q i ζ P → IsComplexTransposeSemigroup Q P Pdag →
    ∀ (g : Lp ℂ 2 (reducedLaw Q)), IsComplexTransposeGeneratorPair Q i ζ (β i) g →
    ∀ F : ℝ × FieldPair d → ℂ, Measurable F →
      (∀ s, (fun ω => F (s, ω)) =ᵐ[reducedLaw Q] Pdag s.toNNReal (β i)) →
    ∀ᵐ ω ∂reducedLaw Q,
      ∀ (χ : C(Vec d, ℝ)), ContDiff ℝ (⊤ : ℕ∞) χ →
      ∀ ρ : ℝ, 1 ≤ ρ → (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) →
      (∀ x, ρ / 2 ≤ euclideanNorm x → χ x = 0) →
      (∀ j x, |coordinateDerivative j χ x| ≤ Cχ / ρ) →
      (∀ x, euclideanNorm x ≤ ρ / 4 → χ x = 1) →
      ∀ fr : Lp ℂ 2 (volume : Measure (Vec d)),
        (fr : Vec d → ℂ) =ᵐ[volume] (fun x =>
          (((1 / 2 : ℝ) * ∑ j : Fin d, coordinateDerivative j
            (fun y => (ForcedLocality.retainedPair χ ω).1 y j i) x : ℝ) : ℂ)) →
      ∀ Pr Tr : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
        Lp ℂ 2 (volume : Measure (Vec d)),
        IsPhysicalComplexTransposeSemigroup (ForcedLocality.retainedPair χ ω).1 i ζ Pr Tr →
      ∀ V : ℝ × Vec d → ℂ, Measurable V →
        (∀ s, (fun x => V (s, x)) =ᵐ[volume] Tr s.toNNReal fr) →
        (∫⁻ z in Icc (0 : ℝ) 1 ×ˢ (univ : Set (Vec d)),
          ENNReal.ofReal (Real.exp (-euclideanSq z.2 / L) *
            ‖F (z.1, translate z.2 ω) - V z‖ ^ 2)) ≤
              ENNReal.ofReal (K * Real.exp (-c * ρ ^ 2)) := by
  intro Λ
  obtain ⟨L, K, c, hscale, hL, hK, hc, hdecay⟩ :=
    short_time_transpose_actual_gaussian_spacetime_decay d hd D B Cχ hCχ
  refine ⟨L / 2, K, c, ?_, by positivity, hK, hc, ?_⟩
  · linarith
  intro Q hQ β hβ i ζ hζ P Pdag hP hPdag g hg F hF heF
  filter_upwards [hdecay Q hQ β hβ i ζ hζ P Pdag hP hPdag g hg F hF heF] with ω hω
  intro χ hχ ρ hρ hχb hχzero hχder hχone fr hfr Pr Tr hPr V hV heV
  exact c25_gaussian_decay_half_scale _ (fun z => euclideanSq z.2)
    (fun z => F (z.1, translate z.2 ω) - V z) L K c ρ hL
    (hω χ hχ ρ hρ hχb hχzero hχder hχone fr hfr Pr Tr hPr V hV heV)

/-- Finite-volume physical averages are continuous linear functionals of the
retained L² state, hence preserve its local measurability. -/
private theorem c25_local_physical_average_measurable
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    {V : Ω → Lp ℂ 2 (volume : Measure (Vec d))}
    (hV : @Measurable Ω (Lp ℂ 2 (volume : Measure (Vec d))) _ (borel _) V)
    {A : Set (Vec d)} (hA : MeasurableSet A) (hμA : volume A ≠ ∞) :
    Measurable (fun ω => ⨍ x in A, (V ω) x) := by
  let : MeasurableSpace (Lp ℂ 2 (volume : Measure (Vec d))) := borel _
  let : BorelSpace (Lp ℂ 2 (volume : Measure (Vec d))) := ⟨rfl⟩
  have hm := (innerSL ℂ (indicatorConstLp 2 hA hμA (1 : ℂ))).continuous.measurable.comp hV
  have hs := hm.const_smul ((volume.restrict A).real univ)⁻¹
  change Measurable (fun ω => ((volume.restrict A).real univ)⁻¹ •
    innerSL ℂ (indicatorConstLp 2 hA hμA (1 : ℂ)) (V ω)) at hs
  simpa only [average_eq, innerSL_apply_apply, L2.inner_indicatorConstLp_one] using hs

private theorem c25_unit_ball_probability (d : ℕ) :
    IsProbabilityMeasure (PDE.normalizedVolumeOn (PDE.euclideanBall (0 : PDE.Vec d) 1)) :=
  PDE.isProbabilityMeasure_normalizedVolumeOn_of_pos_of_lt_top
    (PDE.volume_euclideanBall_pos _ (by norm_num))
    (lt_top_iff_ne_top.mpr (PDE.volume_euclideanBall_ne_top _ (by norm_num)))

/-- Positive dilation turns normalized unit-ball integration into the literal
average on the smaller physical ball. This holds for every representative. -/
private theorem c25_scaled_unit_ball_average {d : ℕ} {r : ℝ} (hr : 0 < r)
    (f : Vec d → ℂ) :
    (⨍ x, f (r • x) ∂PDE.normalizedVolumeOn (PDE.euclideanBall (0 : PDE.Vec d) 1)) =
      ⨍ x in PDE.euclideanBall (0 : PDE.Vec d) r, f x := by
  let := c25_unit_ball_probability d
  rw [average_eq_integral]
  have hp := PDE.measurePreserving_smul_addRight_normalizedVolumeOn_euclideanBall hr
    (0 : PDE.Vec d)
  have hm : MeasurableEmbedding (fun x : Vec d => r • x + (0 : Vec d)) := by
    convert (Homeomorph.smulOfNeZero r hr.ne' : Vec d ≃ₜ Vec d).measurableEmbedding using 1
    ext x
    simp
  have he := hp.integral_comp hm f
  simp only [add_zero] at he
  rw [he, PDE.normalizedVolumeOn, integral_smul_measure, ENNReal.toReal_inv, setAverage_eq]
  rfl

/-- The actual shrinking-ball averages of a local L²-valued family are local
measurable functions; no spatial point value is selected. -/
theorem c25_local_retained_average_measurable
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    {V : Ω → Lp ℂ 2 (volume : Measure (Vec d))}
    (hV : @Measurable Ω (Lp ℂ 2 (volume : Measure (Vec d))) _ (borel _) V)
    {r : ℝ} (hr : 0 < r) :
    Measurable (fun ω => ⨍ x, (V ω) (r • x)
      ∂PDE.normalizedVolumeOn (PDE.euclideanBall (0 : PDE.Vec d) 1)) := by
  simp_rw [c25_scaled_unit_ball_average hr]
  exact c25_local_physical_average_measurable hV
    (PDE.isOpen_euclideanBall _ _).measurableSet (PDE.volume_euclideanBall_ne_top _ hr.le)


/-- A literal stationary spatial average inherits the same residual error as
the actual retained L² state on every smaller physical ball. -/
theorem c25_stationary_retained_average_error {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (f : Lp ℂ 2 (reducedLaw Q))
    (F : FieldPair d → ℂ) (hF : Measurable F) (heF : F =ᵐ[reducedLaw Q] f)
    (V : FieldPair d → Lp ℂ 2 (volume : Measure (Vec d)))
    {R r ε : ℝ} (hr : 0 < r) (hrR : r ≤ R)
    (herr : ∀ᵐ ω ∂reducedLaw Q,
      ∀ᵐ x ∂volume.restrict (PDE.euclideanBall (0 : PDE.Vec d) R),
        ‖F (translate x ω) - (V ω) x‖ ≤ ε) :
    ∀ᵐ ω ∂reducedLaw Q,
      ‖(⨍ x, f (translate (r • x) ω)
          ∂PDE.normalizedVolumeOn (PDE.euclideanBall (0 : PDE.Vec d) 1)) -
        (⨍ x, (V ω) (r • x)
          ∂PDE.normalizedVolumeOn (PDE.euclideanBall (0 : PDE.Vec d) 1))‖ ≤ ε := by
  let := reducedLaw_probability Q
  have hsp := ae_spatial_complex_orbit_congr (reducedLaw Q) (reducedLaw_stationary Q)
    hF (Lp.stronglyMeasurable f).measurable heF
  let A := PDE.euclideanBall (0 : PDE.Vec d) r
  have hApos := PDE.volume_euclideanBall_pos (0 : PDE.Vec d) hr
  have hAtop := PDE.volume_euclideanBall_ne_top (0 : PDE.Vec d) hr.le
  let : IsProbabilityMeasure (PDE.normalizedVolumeOn A) :=
    PDE.isProbabilityMeasure_normalizedVolumeOn_of_pos_of_lt_top hApos
      (lt_top_iff_ne_top.mpr hAtop)
  have hsub : A ⊆ PDE.euclideanBall (0 : PDE.Vec d) R := by
    intro x hx
    change PDE.euclideanSqDist x 0 < r ^ 2 at hx
    change PDE.euclideanSqDist x 0 < R ^ 2
    nlinarith
  filter_upwards [herr, hsp] with ω hω hsω
  rw [c25_scaled_unit_ball_average hr (fun y => f (translate y ω)),
    c25_scaled_unit_ball_average hr (V ω)]
  have he : (fun x => F (translate x ω)) =ᵐ[volume.restrict A]
      (fun x => f (translate x ω)) := ae_restrict_of_ae hsω
  rw [← average_congr he]
  have hb : ∀ᵐ x ∂PDE.normalizedVolumeOn A, ‖F (translate x ω) - (V ω) x‖ ≤ ε := by
    exact Measure.ae_smul_measure
      (hω.filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl))) (volume A)⁻¹
  have hVi : Integrable (V ω) (PDE.normalizedVolumeOn A) :=
    PDE.integrable_normalizedVolumeOn_of_integrableOn
      (integrableOn_Lp_of_measure_ne_top (V ω) (by norm_num) hAtop) hApos
  have hFm : Measurable (fun x : Vec d => F (translate x ω)) :=
    hF.comp (Probability.continuous_translate.measurable.comp
      (measurable_id.prodMk measurable_const))
  have hDi : Integrable (fun x => F (translate x ω) - (V ω) x)
      (PDE.normalizedVolumeOn A) :=
    (integrable_const ε).mono'
      (hFm.aestronglyMeasurable.sub (Lp.stronglyMeasurable (V ω)).aestronglyMeasurable) hb
  have hFi : Integrable (fun x => F (translate x ω)) (PDE.normalizedVolumeOn A) := by
    exact (hDi.add hVi).congr (Filter.Eventually.of_forall fun x =>
      sub_add_cancel (F (translate x ω)) ((V ω) x))
  have hn := norm_integral_le_of_norm_le_const hb
  have heq (g : Vec d → ℂ) : (⨍ x in A, g x) = ∫ x, g x ∂PDE.normalizedVolumeOn A := by
    rw [setAverage_eq', PDE.normalizedVolumeOn]
  rw [heq, heq, ← integral_sub hFi hVi]
  simpa only [probReal_univ, mul_one] using hn



/-- The normalized two-phase bound controls every physical short-time trace
of the supplied residual. Its almost-everywhere continuous time paths retain
both endpoints, including the upper boundary of the Moser cylinder. -/
private theorem c25_complex_bound_of_normalized_lift_trace {d : ℕ}
    {X : ℝ × Vec d → ℂ} (hX : Measurable X)
    {q M : ℝ} (hq : 0 < q) (hM : 0 ≤ M)
    (hθ : 0 < Real.sin (q * (3 / 32)))
    (hc : ∀ᵐ x ∂volume.restrict (PDE.euclideanBall (0 : PDE.Vec d) (q * (3 / 16))),
      ContinuousOn (fun s => X (s, x)) (Icc (-1 : ℝ) 1))
    (hb : essSup (fun z : PDE.Vec (d + 2) × ℝ =>
        ENNReal.ofReal |(Complex.exp ⟨q * z.1 (Fin.natAdd d (0 : Fin 2)),
            q * z.1 (Fin.natAdd d (1 : Fin 2))⟩ *
            X (1 + 2 * z.2, q • (PDE.vecAppendEquiv d 2 z.1).1)).re|)
        (volume.restrict
          (EinsteinFull.SignedLocalMax.moserCylZ (d + 2) (3 / 8) (-11 / 16))) ≤
        ENNReal.ofReal M) :
    ∀ s ∈ Icc (0 : ℝ) 1,
      ∀ᵐ x ∂volume.restrict (PDE.euclideanBall (0 : PDE.Vec d) (q * (3 / 16))),
        ‖X (s, x)‖ ≤ (1 + 2 / Real.sin (q * (3 / 32))) * M := by
  have hZ : Measurable (fun z : PDE.Vec d × ℝ => X (1 + 2 * z.2, q • z.1)) :=
    hX.comp (by fun_prop)
  have he := short_time_transpose_complex_bound_of_lift_essSup hZ
    (by norm_num : (0 : ℝ) < 3 / 8) hM (by convert hθ using 1; ring) hb
  simp only [show (3 / 8 : ℝ) / 2 = 3 / 16 by norm_num,
    show (3 / 16 : ℝ) / 2 = 3 / 32 by norm_num] at he
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict] at he
  have hslice := Measure.ae_ae_of_ae_prod he
  have hmaps : MapsTo (fun x : Vec d => q⁻¹ • x)
      (PDE.euclideanBall (0 : PDE.Vec d) (q * (3 / 16)))
      (PDE.euclideanBall (0 : PDE.Vec d) (3 / 16)) := by
    intro x hx
    rw [PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt (by norm_num : (0 : ℝ) < 3 / 16),
      sub_zero, PDE.vecEuclideanNorm_smul, abs_of_pos (inv_pos.mpr hq)]
    apply (inv_mul_lt_iff₀ hq).2
    simpa only [sub_zero] using
      (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt (by positivity : (0 : ℝ) < q * (3 / 16))).1 hx
  have hp := ((Measure.quasiMeasurePreserving_smul
    (volume : Measure (Vec d)) (inv_ne_zero hq.ne')).restrict hmaps).ae hslice
  intro s hs
  filter_upwards [hc, hp] with x hcx hx
  simp only [smul_inv_smul₀ hq.ne'] at hx
  have hcont : ContinuousOn (fun t : ℝ => ‖X (1 + 2 * t, x)‖)
      (Icc (-11 / 16 : ℝ) 0) := by
    apply hcx.norm.comp (by fun_prop)
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  have hopen := PDE.Parabolic.Moser.continuousOn_le_of_ae_restrict_le
    isOpen_Ioo (hcont.mono Ioo_subset_Icc_self) hx
  have hcl : closure (Ioo (-11 / 16 : ℝ) 0) = Icc (-11 / 16 : ℝ) 0 :=
    closure_Ioo (by norm_num)
  have ht : (s - 1) / 2 ∈ closure (Ioo (-11 / 16 : ℝ) 0) := by
    rw [hcl]
    constructor <;> linarith [hs.1, hs.2]
  have hb' := le_on_closure hopen (by simpa only [hcl] using hcont) continuousOn_const ht
  simpa only [show 1 + 2 * ((s - 1) / 2) = s by ring] using hb'

/-- Taking the Moser square root halves the Gaussian decay exponent; all
normalization factors remain deterministic and independent of the law. -/
private theorem c25_gaussian_energy_moser_bound {d : ℕ}
    {q L C K c ρ : ℝ} (hq : 0 < q) (hC : 0 ≤ C) (hK : 0 ≤ K)
    {E : ℝ≥0∞} (hE : E ≤ ENNReal.ofReal (K * Real.exp (-c * ρ ^ 2))) :
    ENNReal.ofReal C *
      (ENNReal.ofReal ((1 : ℝ) / q ^ (d + 2)) *
        (ENNReal.ofReal (Real.exp (2 * q ^ 2 / L)) * E)) ^ (2 : ℝ)⁻¹ ≤
      ENNReal.ofReal
        ((C * (((1 : ℝ) / q ^ (d + 2)) * Real.exp (2 * q ^ 2 / L) * K) ^ (2 : ℝ)⁻¹) *
          Real.exp (-(c / 2) * ρ ^ 2)) := by
  refine (mul_le_mul' le_rfl (ENNReal.rpow_le_rpow
    (mul_le_mul' le_rfl (mul_le_mul' le_rfl hE))
      (by positivity : (0 : ℝ) ≤ (2 : ℝ)⁻¹))).trans_eq ?_
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le,
    ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 1 / q ^ (d + 2)),
    ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity),
    ← ENNReal.ofReal_mul hC]
  congr 1
  rw [show (1 / q ^ (d + 2)) *
      (Real.exp (2 * q ^ 2 / L) * (K * Real.exp (-c * ρ ^ 2))) =
      ((1 / q ^ (d + 2)) * Real.exp (2 * q ^ 2 / L) * K) *
        Real.exp (-c * ρ ^ 2) by ring,
    Real.mul_rpow (by positivity) (Real.exp_pos _).le, ← Real.exp_mul]
  rw [show -c * ρ ^ 2 * (2 : ℝ)⁻¹ = -(c / 2) * ρ ^ 2 by ring]
  ring


/-- Absorb the deterministic lift-energy constant into the Gaussian prefactor. -/
private theorem c25_normalized_gaussian_moser_bound {d : ℕ}
    {q L C C₁ K c ρ : ℝ} (hq : 0 < q) (hC : 0 ≤ C)
    (hC₁ : 0 ≤ C₁) (hK : 0 ≤ K) {E : ℝ≥0∞}
    (hE : E ≤ ENNReal.ofReal (K * Real.exp (-c * ρ ^ 2))) :
    ENNReal.ofReal C *
      (ENNReal.ofReal (C₁ * Real.exp (2 * q ^ 2 / L) / q ^ (d + 2)) * E) ^
        (2 : ℝ)⁻¹ ≤
      ENNReal.ofReal
        ((C * (((1 : ℝ) / q ^ (d + 2)) * Real.exp (2 * q ^ 2 / L) *
          (C₁ * K)) ^ (2 : ℝ)⁻¹) * Real.exp (-(c / 2) * ρ ^ 2)) := by
  have hE' : ENNReal.ofReal C₁ * E ≤
      ENNReal.ofReal ((C₁ * K) * Real.exp (-c * ρ ^ 2)) := by
    calc
      ENNReal.ofReal C₁ * E ≤
          ENNReal.ofReal C₁ * ENNReal.ofReal (K * Real.exp (-c * ρ ^ 2)) :=
        mul_le_mul' le_rfl hE
      _ = ENNReal.ofReal ((C₁ * K) * Real.exp (-c * ρ ^ 2)) := by
        rw [← ENNReal.ofReal_mul hC₁]
        congr 1
        ring
  have hb := c25_gaussian_energy_moser_bound (d := d) (L := L) hq hC
    (mul_nonneg hC₁ hK) hE'
  have hf : ENNReal.ofReal (C₁ * Real.exp (2 * q ^ 2 / L) / q ^ (d + 2)) =
      ENNReal.ofReal ((1 : ℝ) / q ^ (d + 2)) *
        (ENNReal.ofReal (Real.exp (2 * q ^ 2 / L)) * ENNReal.ofReal C₁) := by
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le,
      ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 1 / q ^ (d + 2))]
    congr 1
    ring
  rw [hf]
  simpa only [mul_assoc] using hb

/-- A locally measurable retained state with a spatial residual bound
provides a local observation of the stationary class. -/
theorem c25_local_observation_of_retained_spatial_bound {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (ρ ε R : ℝ) (hε : 0 ≤ ε) (hR : 0 < R)
    (f : Lp ℂ 2 (reducedLaw Q)) (F : FieldPair d → ℂ) (hF : Measurable F)
    (heF : F =ᵐ[reducedLaw Q] f)
    (V : FieldPair d → Lp ℂ 2 (volume : Measure (Vec d)))
    (hV : @Measurable _ _ (localSigma {x : Vec d | euclideanNorm x < ρ})
      (borel _) V)
    (herr : ∀ᵐ ω ∂reducedLaw Q,
      ∀ᵐ x ∂volume.restrict (PDE.euclideanBall (0 : PDE.Vec d) R),
        ‖F (translate x ω) - (V ω) x‖ ≤ ε) :
    ∃ W : Lp ℂ 2 (reducedLaw Q), IsComplexLocalObservation Q ρ W ∧
      ∀ᵐ ω ∂reducedLaw Q, ‖f ω - W ω‖ ≤ 2 * ε := by
  let r : ℕ → ℝ := fun n => R / ((n : ℝ) + 1)
  have hrpos (n : ℕ) : 0 < r n := by dsimp only [r]; positivity
  have hrle (n : ℕ) : r n ≤ R := by
    apply div_le_self hR.le
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have hr : Tendsto r atTop (𝓝 0) := by
    have hh := (tendsto_const_nhds (x := R)).mul
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    simpa only [mul_zero, mul_one_div] using hh
  let A : ℕ → FieldPair d → ℂ := fun n ω =>
    ⨍ x, (V ω) (r n • x)
      ∂PDE.normalizedVolumeOn (PDE.euclideanBall (0 : PDE.Vec d) 1)
  have hA (n : ℕ) : Measurable[localSigma {x : Vec d | euclideanNorm x < ρ}] (A n) := by
    let : MeasurableSpace (FieldPair d) := localSigma {x : Vec d | euclideanNorm x < ρ}
    exact c25_local_retained_average_measurable hV (hrpos n)
  let := c25_unit_ball_probability d
  exact short_time_local_observation_of_shrinking_averages Q ρ hε
    (PDE.normalizedVolumeOn (PDE.euclideanBall (0 : PDE.Vec d) 1)) f r hr A hA
    (fun n => c25_stationary_retained_average_error Q f F hF heF V
      (hrpos n) (hrle n) herr)

/-- Absolute continuity of both scalar projections gives continuous complex
paths on the time interval. -/
private theorem c25_continuous_of_scalar_absolute_continuity {X : ℝ → ℂ}
    (h : ∀ L : ℂ →L[ℝ] ℝ,
      AbsolutelyContinuousOnInterval (fun s => L (X s)) (-1) 1) :
    ContinuousOn X (Icc (-1 : ℝ) 1) := by
  have hr : ContinuousOn (fun s => (X s).re) (Icc (-1 : ℝ) 1) := by
    simpa only [Complex.reCLM_apply, uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using
      (h Complex.reCLM).continuousOn
  have hi : ContinuousOn (fun s => (X s).im) (Icc (-1 : ℝ) 1) := by
    simpa only [Complex.imCLM_apply, uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using
      (h Complex.imCLM).continuousOn
  have hsum := (Complex.continuous_ofReal.comp_continuousOn hr).add
    ((Complex.continuous_ofReal.comp_continuousOn hi).mul
      (continuousOn_const : ContinuousOn (fun _ : ℝ => Complex.I) (Icc (-1 : ℝ) 1)))
  change ContinuousOn (fun s => ((X s).re : ℂ) + ((X s).im : ℂ) * Complex.I)
    (Icc (-1 : ℝ) 1) at hsum
  simpa only [Complex.re_add_im] using hsum

/-- A deterministic parabolic scale covers the whole unit time interval. -/
private theorem c25_normalization_scale {Λ : ℝ} (hΛ : 1 ≤ Λ) :
    let q := (Real.sqrt (2 * Λ))⁻¹
    0 < q ∧ q ≤ 1 ∧ 4 * Λ * q ^ 2 = 2 ∧ 0 < Real.sin (q * (3 / 32)) := by
  intro q
  have hroot : 0 < Real.sqrt (2 * Λ) := Real.sqrt_pos.2 (by positivity)
  have hroot2 : Real.sqrt (2 * Λ) ^ 2 = 2 * Λ := Real.sq_sqrt (by positivity)
  have hq : 0 < q := inv_pos.mpr hroot
  have hq1 : q ≤ 1 := (inv_le_one₀ hroot).2 (by nlinarith [Real.sqrt_nonneg (2 * Λ)])
  have hscale : 4 * Λ * q ^ 2 = 2 := by
    change 4 * Λ * ((Real.sqrt (2 * Λ))⁻¹) ^ 2 = 2
    rw [inv_pow, hroot2]
    field_simp
    ring
  have hθ : 0 < Real.sin (q * (3 / 32)) := by
    apply Real.sin_pos_of_pos_of_lt_pi (by positivity)
    nlinarith [Real.pi_gt_three]
  exact ⟨hq, hq1, hscale, hθ⟩

theorem c25_transpose_retained_joint_weak_equations
    {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    {i : Fin d} {ζ : ℂ}
    {P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (hPdag : IsComplexTransposeSemigroup Q P Pdag)
    {f g : Lp ℂ 2 (reducedLaw Q)} (hfg : IsComplexTransposeGeneratorPair Q i ζ f g) :
    ∃ F U : ℝ × FieldPair d → ℂ, ∃ D : Fin d → ℝ × FieldPair d → ℂ,
      Measurable F ∧ Measurable U ∧ (∀ j, Measurable (D j)) ∧
      (∀ s, (fun ω => F (s, ω)) =ᵐ[reducedLaw Q] Pdag s.toNNReal f) ∧
      (∀ s, (fun ω => U (s, ω)) =ᵐ[reducedLaw Q] Pdag s.toNNReal g) ∧
      (∀ j s, (fun ω => D j (s, ω)) =ᵐ[reducedLaw Q] (complexTransposeGradientOrbit Q Pdag f s) j) ∧
      ∀ᵐ ω ∂reducedLaw Q,
      (∀ K : Set (Vec d), IsCompact K →
        Integrable (fun p : ℝ × Vec d => ‖F (p.1, translate p.2 ω)‖ ^ 2)
          ((volume.restrict (Icc (0 : ℝ) 1)).prod (volume.restrict K)) ∧
        Integrable (fun p : ℝ × Vec d => ‖U (p.1, translate p.2 ω)‖ ^ 2)
          ((volume.restrict (Icc (0 : ℝ) 1)).prod (volume.restrict K)) ∧
        ∀ j, Integrable (fun p : ℝ × Vec d => ‖D j (p.1, translate p.2 ω)‖ ^ 2)
          ((volume.restrict (Icc (0 : ℝ) 1)).prod (volume.restrict K))) ∧
      ∀ χ : C(Vec d, ℝ),
      (∀ j k, MemLp (fun x => ((ForcedLocality.retainedPair χ ω).1 x j k : ℂ))
        ∞ volume) →
      ∀ Λ : ℝ, 0 < Λ →
      (∀ᵐ x ∂volume, S5Elliptic ((ForcedLocality.retainedPair χ ω).1 x) Λ) →
      ∀ (Pr Tr : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
          Lp ℂ 2 (volume : Measure (Vec d))),
      IsPhysicalComplexTransposeSemigroup (ForcedLocality.retainedPair χ ω).1 i ζ Pr Tr →
      ∀ fr gr : Lp ℂ 2 (volume : Measure (Vec d)),
      IsPhysicalComplexTransposeGeneratorPair (ForcedLocality.retainedPair χ ω).1 i ζ fr gr →
      ∃ V Z X Y : ℝ × Vec d → ℂ,
      ∃ H : ℝ → Fin d → Lp ℂ 2 (volume : Measure (Vec d)),
      ∃ W : Fin d → ℝ × Vec d → ℂ,
        (∀ j, Measurable (W j)) ∧
        (∀ j s, (fun x => W j (s, x)) =ᵐ[volume] H s j) ∧
        (∀ (j : Fin d) (l r : ℝ), Integrable (fun p => ‖W j p‖ ^ 2)
          ((volume.restrict (Icc l r)).prod volume)) ∧
        Measurable V ∧ Measurable Z ∧ Measurable X ∧ Measurable Y ∧
        (∀ s, (fun x => V (s, x)) =ᵐ[volume] Tr s.toNNReal fr) ∧
        (∀ s, (fun x => Z (s, x)) =ᵐ[volume] Tr s.toNNReal gr) ∧
        (∀ p, Y p = (Ioc (0 : ℝ) 1).indicator
          (fun s => U (s, translate p.2 ω) - Z (s, p.2)) p.1) ∧
        (∀ s : ℝ, s ≤ 0 → ∀ x, X (s, x) = 0) ∧
        (∀ j, Continuous (fun s => H s j)) ∧
        (∀ s, IsPhysicalH1Graph volume (Or.inl rfl) (Tr s.toNNReal fr) (H s)) ∧
        (∀ᵐ s ∂volume.restrict (Ioc (0 : ℝ) 1), ∀ L : ℂ →L[ℝ] ℝ,
          HasWeakGradient Set.univ (fun x => L (F (s, translate x ω)))
            (fun x j => L (D j (s, translate x ω))) ∧
          ∀ O : Set (Vec d), IsOpen O → (∀ x ∈ O, χ x = 1) →
          HasWeakDivergence O
            (fun x j => L ((∑ k, (ω.1 x j k : ℂ) *
              (D k (s, translate x ω) - H s k x)) -
              2 * ζ * (ω.1 x j i : ℂ) * (F (s, translate x ω) - V (s, x))))
            (fun x => L (2 * Y (s, x)))) ∧
        ∀ K : Set (Vec d), IsCompact K →
        (fun x => f (translate x ω)) =ᵐ[volume.restrict K] fr →
          (∀ s : ℝ, 0 ≤ s → s ≤ 1 →
            (fun x => X (s, x)) =ᵐ[volume.restrict K]
              (fun x => F (s, translate x ω) - V (s, x))) ∧
          (∀ᵐ x ∂volume.restrict K, ∀ L : ℂ →L[ℝ] ℝ,
            AbsolutelyContinuousOnInterval (fun s => L (X (s, x))) (-1) 1 ∧
            ∀ ψ : ℝ → ℝ, ContDiff ℝ 1 ψ → ψ (-1) = 0 → ψ 1 = 0 →
              (∫ s in (-1 : ℝ)..1,
                deriv ψ s * L (X (s, x)) + ψ s * L (Y (s, x))) = 0 ) ∧
          MemLp X 2 ((volume.restrict (Icc (-1 : ℝ) 1)).prod (volume.restrict K)) ∧
          MemLp Y 2 ((volume.restrict (Icc (-1 : ℝ) 1)).prod (volume.restrict K)) ∧
          ∀ j, MemLp (fun p : ℝ × Vec d => (Ioc (0 : ℝ) 1).indicator
            (fun t => D j (t, translate p.2 ω) - W j (t, p.2)) p.1) 2
            ((volume.restrict (Icc (-1 : ℝ) 1)).prod (volume.restrict K)) := by
  obtain ⟨F, U, D, hF, hU, hD, heF, heU, heD, hcoh⟩ :=
    short_time_transpose_retained_coherent_weak_equations Q hP hPdag hfg
  have hint := short_time_transpose_orbit_representatives_local_sq_integrable
    Q hP hPdag hfg F U D hF hU hD heF heU heD
  refine ⟨F, U, D, hF, hU, hD, heF, heU, heD, ?_⟩
  filter_upwards [hcoh, hint] with ω hω hi
  refine ⟨hi, ?_⟩
  intro χ ha Λ hΛ hA Pr Tr hPr fr gr hfr
  obtain ⟨V, Z, X, Y, H, hV, hZ, hX, hY, heV, heZ, heY, hX0, hHc, hH, hres, hlocal⟩ :=
    hω χ ha Λ hΛ hA Pr Tr hPr fr gr hfr
  obtain ⟨W, hW, heW, hw, hforce⟩ :=
    short_time_transpose_coherent_forcing_gradient_memLp ω U D hU hD
      (fun K hK => (hi K hK).2.1) (fun K hK => (hi K hK).2.2)
      ha hΛ hA hPr hfr Z Y hZ heZ heY H hHc hH
  refine ⟨V, Z, X, Y, H, W, hW, heW, hw, hV, hZ, hX, hY,
    heV, heZ, heY, hX0, hHc, hH, ?_, ?_⟩
  · filter_upwards [hres] with s hs
    intro L
    exact ⟨(hs L).1, fun O hO hχO => (hs L).2 O hO.measurableSet hχO⟩
  · intro K hK hinit
    obtain ⟨hmatch, htime⟩ := hlocal K hK hinit
    have hv : Integrable (fun p => ‖V p‖ ^ 2)
        ((volume.restrict (Icc (0 : ℝ) 1)).prod volume) :=
      short_time_joint_sq_integrable
        ((((hPr.2.2.1 fr).comp continuous_real_toNNReal).norm.pow 2).continuousOn.integrableOn_compact
          isCompact_Icc) hV heV
    have hXm := short_time_transpose_difference_zero_extension_memLp ω K F V
      hF hV (hi K hK).1 hv
    refine ⟨hmatch, htime, ?_, (hforce K hK).1, (hforce K hK).2⟩
    apply hXm.ae_eq
    have hshift : Measurable (fun p : ℝ × Vec d => (p.1, translate p.2 ω)) :=
      measurable_fst.prodMk (Probability.continuous_translate.measurable.comp
        (measurable_snd.prodMk measurable_const))
    have hq : Measurable (fun p : ℝ × Vec d => (Ioc (0 : ℝ) 1).indicator
        (fun s => F (s, translate p.2 ω) - V (s, p.2)) p.1) :=
      Measurable.ite (measurableSet_Ioc.preimage measurable_fst)
        ((hF.comp hshift).sub hV) measurable_const
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun hq hX)).mpr
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    by_cases ht : s ∈ Ioc (0 : ℝ) 1
    · filter_upwards [hmatch s ht.1.le ht.2] with x hx
      simpa only [indicator_of_mem ht, Pi.sub_apply] using hx.symm
    · have hs0 : s ≤ 0 := by
        by_contra hn
        exact ht ⟨lt_of_not_ge hn, hs.2⟩
      exact ae_of_all _ fun x => by rw [indicator_of_notMem ht, hX0 s hs0 x]

/-- The common retained witnesses satisfy the zero-extended spatial equations
on every region contained in an open plateau of the cutoff. -/
theorem c25_transpose_retained_residual_spatial_equations {d : ℕ}
    (ω : FieldPair d) (χ : C(Vec d, ℝ)) (O K : Set (Vec d))
    (hO : IsOpen O) (hKO : K ⊆ O) (hχ : ∀ x ∈ O, χ x = 1)
    (i : Fin d) (ζ : ℂ) (F U : ℝ × FieldPair d → ℂ)
    (D : Fin d → ℝ × FieldPair d → ℂ) (V Z X Y : ℝ × Vec d → ℂ)
    (W : Fin d → ℝ × Vec d → ℂ)
    (v : ℝ → Lp ℂ 2 (volume : Measure (Vec d)))
    (H : ℝ → Fin d → Lp ℂ 2 (volume : Measure (Vec d)))
    (heV : ∀ s, (fun x => V (s, x)) =ᵐ[volume] v s)
    (heW : ∀ j s, (fun x => W j (s, x)) =ᵐ[volume] H s j)
    (hH : ∀ s, IsPhysicalH1Graph volume (Or.inl rfl) (v s) (H s))
    (hX0 : ∀ s : ℝ, s ≤ 0 → ∀ x, X (s, x) = 0)
    (hY : ∀ p, Y p = (Ioc (0 : ℝ) 1).indicator
      (fun s => U (s, translate p.2 ω) - Z (s, p.2)) p.1)
    (hmatch : ∀ s : ℝ, 0 < s → s ≤ 1 →
      (fun x => X (s, x)) =ᵐ[volume.restrict K]
        (fun x => F (s, translate x ω) - V (s, x)))
    (hres : ∀ᵐ s ∂volume.restrict (Ioc (0 : ℝ) 1), ∀ L : ℂ →L[ℝ] ℝ,
      HasWeakGradient univ (fun x => L (F (s, translate x ω)))
        (fun x j => L (D j (s, translate x ω))) ∧
      ∀ O : Set (Vec d), IsOpen O → (∀ x ∈ O, χ x = 1) →
      HasWeakDivergence O
        (fun x j => L ((∑ k, (ω.1 x j k : ℂ) *
          (D k (s, translate x ω) - H s k x)) -
          2 * ζ * (ω.1 x j i : ℂ) * (F (s, translate x ω) - V (s, x))))
        (fun x => L (2 * Y (s, x)))) :
    let J := fun s x j => (Ioc (0 : ℝ) 1).indicator
      (fun t => D j (t, translate x ω) - W j (t, x)) s
    (∀ᵐ s ∂volume.restrict (Ioo (-1 : ℝ) 1),
      HasWeakGradient K (fun x => (X (s, x)).re) (fun x j => (J s x j).re) ∧
      HasWeakGradient K (fun x => (X (s, x)).im) (fun x j => (J s x j).im)) ∧
    ∀ᵐ s ∂volume.restrict (Ioo (-1 : ℝ) 1), ∀ L : ℂ →L[ℝ] ℝ,
      HasWeakDivergence K
        (fun x j => L ((∑ k, (ω.1 x j k : ℂ) * J s x k) -
          2 * ζ * (ω.1 x j i : ℂ) * X (s, x)))
        (fun x => L (2 * Y (s, x))) := by
  have hY0 : ∀ s : ℝ, s ≤ 0 → ∀ x, Y (s, x) = 0 := by
    intro s hs x
    rw [hY, indicator_of_notMem]
    exact fun ht => (not_lt_of_ge hs) ht.1
  have hg : ∀ᵐ s ∂volume.restrict (Ioc (0 : ℝ) 1), ∀ L : ℂ →L[ℝ] ℝ,
      HasWeakGradient univ (fun x => L (F (s, translate x ω)))
        (fun x j => L (D j (s, translate x ω))) :=
    hres.mono fun _ hs L => (hs L).1
  have hd : ∀ᵐ s ∂volume.restrict (Ioc (0 : ℝ) 1), ∀ L : ℂ →L[ℝ] ℝ,
      HasWeakDivergence O
        (fun x j => L ((∑ k, (ω.1 x j k : ℂ) *
          (D k (s, translate x ω) - H s k x)) -
          2 * ζ * (ω.1 x j i : ℂ) * (F (s, translate x ω) - V (s, x))))
        (fun x => L (2 * Y (s, x))) :=
    hres.mono fun _ hs L => (hs L).2 O hO hχ
  exact short_time_transpose_joint_residual_spatial_equations O K hO hKO ω.1 i ζ
    (fun p => F (p.1, translate p.2 ω)) V X Y
    (fun j p => D j (p.1, translate p.2 ω)) W v H
    heV heW hH hX0 hY0 hmatch hg hd

/-- A single dimension-dependent derivative constant gives cutoffs with the
quarter-radius plateau and half-radius support required by the comparison. -/
theorem c25_transpose_cutoff_family (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ ρ : ℝ, 1 ≤ ρ →
    ∃ χ : C(Vec d, ℝ), ContDiff ℝ (⊤ : ℕ∞) χ ∧ HasCompactSupport χ ∧
      (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) ∧
      (∀ x, ρ / 2 ≤ euclideanNorm x → χ x = 0) ∧
      (∀ j x, |coordinateDerivative j χ x| ≤ C / ρ) ∧
      (∀ x, euclideanNorm x ≤ ρ / 4 → χ x = 1) := by
  obtain ⟨B, hB, hcut⟩ := exists_physical_euclidean_cutoff d
  refine ⟨4 * B, by positivity, ?_⟩
  intro ρ hρ
  have hρpos : 0 < ρ := by linarith
  obtain ⟨φ, hφ, hφb, hφone, hφzero, hφder⟩ :=
    hcut 0 (ρ / 4) (by positivity)
  let χ : C(Vec d, ℝ) := ⟨φ, hφ.1.continuous⟩
  refine ⟨χ, hφ.1, hφ.2.1, hφb, ?_, ?_, ?_⟩
  · intro x hx
    apply hφzero x
    simpa only [sub_zero, show 2 * (ρ / 4) = ρ / 2 by ring] using hx
  · intro j x
    have h := hφder j x
    have he : B / (ρ / 4) = 4 * B / ρ := by field_simp
    simpa only [χ, ContinuousMap.coe_mk, he] using h
  · intro x hx
    apply hφone x
    simpa only [sub_zero] using hx

/-- On one sample event, the retained initial drift agrees locally with the
actual stationary drift for every open cutoff plateau. -/
theorem c25_transpose_retained_initial_match {d : ℕ} {D : StructuralData d}
    {Q : EnvironmentLaw d D.ellipticity D.dependenceRange}
    {hQ : HasSmoothBounds D Q} {β : Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hβ : IsReducedDriftObservation Q hQ β) (i : Fin d) :
    ∀ᵐ ω ∂reducedLaw Q, ∀ (χ : C(Vec d, ℝ)) (O K : Set (Vec d)),
      IsOpen O → (∀ x ∈ O, χ x = 1) → IsCompact K → K ⊆ O →
      ∀ fr : Lp ℂ 2 (volume : Measure (Vec d)),
      (fr : Vec d → ℂ) =ᵐ[volume] (fun x =>
        (((1 / 2 : ℝ) * ∑ j : Fin d, coordinateDerivative j
          (fun y => (ForcedLocality.retainedPair χ ω).1 y j i) x : ℝ) : ℂ)) →
      (fun x => β i (translate x ω)) =ᵐ[volume.restrict K] fr := by
  filter_upwards [short_time_transpose_drift_spatial_identification hβ i] with ω hβω
  intro χ O K hO hχO hK hKO fr hfr
  filter_upwards [ae_restrict_of_ae hβω, ae_restrict_of_ae hfr,
    ae_restrict_mem hK.measurableSet] with x hxβ hxfr hxK
  rw [hxβ, hxfr]
  exact congrArg (fun r : ℝ => (r : ℂ))
    (ForcedLocality.retainedPair_drift χ ω hO hχO (hKO hxK) i).symm

/-- A cutoff with a sufficiently large plateau contains a compact unit-ball
neighborhood suitable for the normalized local maximum. -/
theorem c25_transpose_cutoff_unit_plateau {d : ℕ} (ρ : ℝ) (hρ : 8 ≤ ρ)
    (χ : C(Vec d, ℝ)) (hχ : ∀ x, euclideanNorm x ≤ ρ / 4 → χ x = 1) :
    ∃ O K : Set (Vec d), IsOpen O ∧ IsCompact K ∧
      PDE.euclideanBall (0 : PDE.Vec d) 1 ⊆ K ∧ K ⊆ O ∧
      ∀ x ∈ O, χ x = 1 := by
  let O : Set (Vec d) := PDE.euclideanBall (0 : PDE.Vec d) (ρ / 4)
  let K : Set (Vec d) := {x | euclideanNorm (x - 0) ≤ 1}
  have hρ4 : 0 < ρ / 4 := by linarith
  refine ⟨O, K, PDE.isOpen_euclideanBall _ _, isCompact_physical_euclidean_closedBall 0 1,
    ?_, ?_, ?_⟩
  · intro x hx
    have hx' := (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt (by norm_num : (0 : ℝ) < 1)).1 hx
    change euclideanNorm (x - 0) ≤ 1
    exact le_of_lt hx'
  · intro x hx
    have hx' : euclideanNorm x ≤ 1 := by simpa only [K, mem_setOf_eq, sub_zero] using hx
    apply (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt hρ4).2
    simp only [sub_zero]
    change euclideanNorm x < ρ / 4
    linarith
  · intro x hx
    apply hχ x
    have hx' := (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt hρ4).1 hx
    change euclideanNorm (x - 0) < ρ / 4 at hx'
    simpa only [sub_zero] using le_of_lt hx'

/-- The normalized lift bound controls the actual retained residual at every
time when the zero extension agrees with it on the compact spatial region. -/
theorem c25_transpose_residual_bound_of_lift_trace {d : ℕ}
    {X Z : ℝ × Vec d → ℂ} (hX : Measurable X)
    {q M : ℝ} (hq : 0 < q) (hM : 0 ≤ M)
    (hθ : 0 < Real.sin (q * (3 / 32))) (K : Set (Vec d))
    (hball : PDE.euclideanBall (0 : PDE.Vec d) (q * (3 / 16)) ⊆ K)
    (hmatch : ∀ s ∈ Icc (0 : ℝ) 1,
      (fun x => X (s, x)) =ᵐ[volume.restrict K] (fun x => Z (s, x)))
    (hc : ∀ᵐ x ∂volume.restrict (PDE.euclideanBall (0 : PDE.Vec d) (q * (3 / 16))),
      ContinuousOn (fun s => X (s, x)) (Icc (-1 : ℝ) 1))
    (hb : essSup (fun z : PDE.Vec (d + 2) × ℝ =>
        ENNReal.ofReal |(Complex.exp ⟨q * z.1 (Fin.natAdd d (0 : Fin 2)),
            q * z.1 (Fin.natAdd d (1 : Fin 2))⟩ *
            X (1 + 2 * z.2, q • (PDE.vecAppendEquiv d 2 z.1).1)).re|)
        (volume.restrict
          (EinsteinFull.SignedLocalMax.moserCylZ (d + 2) (3 / 8) (-11 / 16))) ≤
        ENNReal.ofReal M) :
    ∀ s ∈ Icc (0 : ℝ) 1,
      ∀ᵐ x ∂volume.restrict (PDE.euclideanBall (0 : PDE.Vec d) (q * (3 / 16))),
        ‖Z (s, x)‖ ≤ (1 + 2 / Real.sin (q * (3 / 32))) * M := by
  intro s hs
  filter_upwards [c25_complex_bound_of_normalized_lift_trace hX hq hM hθ hc hb s hs,
    ae_restrict_of_ae_restrict_of_subset hball (hmatch s hs)] with x hx he
  simpa only [he] using hx


/-- The normalized maximum, Gaussian energy, and time trace give a spatial
residual estimate at every time of the unit interval. -/
private theorem c25_spatial_bound_of_normalized_max {d : ℕ}
    (Λ B : ℝ) (hΛ : 1 ≤ Λ) (hB : 0 ≤ B) :
    ∃ C₀ C₁ : ℝ, 0 < C₀ ∧ 0 < C₁ ∧
    ∀ (K : Set (Vec d)), IsCompact K →
      PDE.euclideanBall (0 : PDE.Vec d) 1 ⊆ K →
    ∀ (A : EinsteinRelation.CoefficientField d), Continuous A →
      (∀ x, S5Elliptic (A x) Λ) → ∀ (i : Fin d) (ζ : ℂ), ‖ζ‖ ≤ B →
    ∀ (X Y Z : ℝ × Vec d → ℂ) (J : ℝ → Vec d → Fin d → ℂ),
      Measurable X → Measurable Y → Measurable Z →
      MemLp X 2 ((volume.restrict (Icc (-1 : ℝ) 1)).prod (volume.restrict K)) →
      MemLp Y 2 ((volume.restrict (Icc (-1 : ℝ) 1)).prod (volume.restrict K)) →
      (∀ j, MemLp (fun p : ℝ × Vec d => J p.1 p.2 j) 2
        ((volume.restrict (Icc (-1 : ℝ) 1)).prod (volume.restrict K))) →
      (∀ s : ℝ, s ≤ 0 → ∀ x, X (s, x) = 0) →
      (∀ᵐ x ∂volume.restrict K, ∀ L : ℂ →L[ℝ] ℝ,
        AbsolutelyContinuousOnInterval (fun s => L (X (s, x))) (-1) 1 ∧
        ∀ ψ : ℝ → ℝ, ContDiff ℝ 1 ψ → ψ (-1) = 0 → ψ 1 = 0 →
          (∫ s in (-1 : ℝ)..1, deriv ψ s * L (X (s, x)) + ψ s * L (Y (s, x))) = 0) →
      (∀ᵐ s ∂volume.restrict (Ioo (-1 : ℝ) 1),
        HasWeakGradient K (fun x => (X (s, x)).re) (fun x j => (J s x j).re) ∧
        HasWeakGradient K (fun x => (X (s, x)).im) (fun x j => (J s x j).im) ) →
      (∀ᵐ s ∂volume.restrict (Ioo (-1 : ℝ) 1), ∀ L : ℂ →L[ℝ] ℝ,
        HasWeakDivergence K
          (fun x j => L ((∑ k, (A x j k : ℂ) * J s x k) -
            2 * ζ * (A x j i : ℂ) * X (s, x))) (fun x => L (2 * Y (s, x)))) →
      (∀ s : ℝ, 0 ≤ s → s ≤ 1 →
        (fun x => X (s, x)) =ᵐ[volume.restrict K] (fun x => Z (s, x))) →
    ∀ (L G c ρ : ℝ), 0 < L → 0 ≤ G →
      (∫⁻ z in Icc (0 : ℝ) 1 ×ˢ (Set.univ : Set (Vec d)),
        ENNReal.ofReal (Real.exp (-euclideanSq z.2 / L) * ‖Z z‖ ^ 2)) ≤
          ENNReal.ofReal (G * Real.exp (-c * ρ ^ 2)) →
      let q := (Real.sqrt (2 * Λ))⁻¹
      ∀ s ∈ Icc (0 : ℝ) 1,
        ∀ᵐ x ∂volume.restrict (PDE.euclideanBall (0 : PDE.Vec d) (q * (3 / 16))),
          ‖Z (s, x)‖ ≤ (1 + 2 / Real.sin (q * (3 / 32))) *
            ((C₀ * (((1 : ℝ) / q ^ (d + 2)) * Real.exp (2 * q ^ 2 / L) *
              (C₁ * G)) ^ (2 : ℝ)⁻¹) * Real.exp (-(c / 2) * ρ ^ 2)) := by
  obtain ⟨C₀, C₁, hC₀, hC₁, hmax⟩ :=
    short_time_transpose_residual_normalized_gaussian_max Λ B hΛ hB
  refine ⟨C₀, C₁, hC₀, hC₁, ?_⟩
  intro K hK hball A hA hEll i ζ hζ X Y Z J hX hY hZ hX2 hY2 hJ2 hX0 htime hgrad hspace hmatch L G c ρ hL hG hE q
  obtain ⟨hq, hq1, hscale, hθ⟩ := c25_normalization_scale hΛ
  change 4 * Λ * q ^ 2 = 2 at hscale
  have hsmall : PDE.euclideanBall (0 : PDE.Vec d) (q * (3 / 16)) ⊆ K := by
    apply (PDE.euclideanBall_mono (by positivity) (by nlinarith)).trans hball
  have hc : ∀ᵐ x ∂volume.restrict (PDE.euclideanBall (0 : PDE.Vec d) (q * (3 / 16))),
      ContinuousOn (fun s => X (s, x)) (Icc (-1 : ℝ) 1) := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hsmall htime] with x hx
    exact c25_continuous_of_scalar_absolute_continuity (fun L => (hx L).1)
  have hb := (hmax K hK hball A hA hEll i ζ hζ X Y Z J hX hY hZ hX2 hY2 hJ2
    hX0 htime hgrad hspace hmatch q hq hq1 1 (by linarith) (by norm_num) L hL).2
  have he := c25_normalized_gaussian_moser_bound (d := d) (q := q) (L := L)
    (C := C₀) (C₁ := C₁) hq hC₀.le hC₁.le hG hE
  have hM : 0 ≤ (C₀ * (((1 : ℝ) / q ^ (d + 2)) * Real.exp (2 * q ^ 2 / L) *
      (C₁ * G)) ^ (2 : ℝ)⁻¹) * Real.exp (-(c / 2) * ρ ^ 2) := by positivity
  apply c25_transpose_residual_bound_of_lift_trace (q := q) hX hq hM hθ K hsmall
    (fun s hs => hmatch s hs.1 hs.2) hc
  simpa only [hscale] using hb.trans he


/-- Local observation of the actual transpose drift from the retained cutoff. -/
theorem short_time_transpose_local_observation_of_graph_deps
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) (B : ℝ) (hB : 0 < B) :
    ∃ R K c : ℝ, 1 ≤ R ∧ 0 < K ∧ 0 < c ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q)), IsReducedDriftObservation Q hQ β →
    ∀ ζ : ℂ, ‖ζ‖ ≤ B →
    ∀ P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P →
      IsComplexTransposeSemigroup Q P Pdag →
    ∀ t : ℝ≥0, (t : ℝ) ≤ 1 → ∀ ρ : ℝ, R ≤ ρ →
    ∃ V : Lp ℂ 2 (reducedLaw Q), IsComplexLocalObservation Q ρ V ∧
      ∀ᵐ ω ∂reducedLaw Q,
        ‖transposeEndpoint Q ⟨0, by omega⟩ Pdag β t ω - V ω‖ ≤
          K * Real.exp (-c * ρ ^ 2) := by
  let Λ := Real.exp (2 * D.ellipticity) * D.ellipticity
  have hΛ : 1 ≤ Λ := by
    dsimp only [Λ]
    have he : 1 ≤ Real.exp (2 * D.ellipticity) :=
      Real.one_le_exp_iff.mpr (by linarith [D.one_le_ellipticity])
    exact (one_mul (1 : ℝ)).symm.trans_le
      (mul_le_mul he D.one_le_ellipticity zero_le_one (Real.exp_nonneg _))
  obtain ⟨Cχ, hCχ, hcut⟩ := c25_transpose_cutoff_family d
  obtain ⟨L, G, c, _, hL, hG, hc, hdecay⟩ :=
    c25_transpose_actual_gaussian_spacetime_decay_half_scale d hd D B Cχ hCχ.le
  obtain ⟨C₀, C₁, hC₀, hC₁, hmax⟩ := c25_spatial_bound_of_normalized_max Λ B hΛ hB.le
  let q := (Real.sqrt (2 * Λ))⁻¹
  obtain ⟨hq, hq1, hscale, hθ⟩ := c25_normalization_scale hΛ
  let M := C₀ * (((1 : ℝ) / q ^ (d + 2)) * Real.exp (2 * q ^ 2 / L) * (C₁ * G)) ^ (2 : ℝ)⁻¹
  let K := 2 * (1 + 2 / Real.sin (q * (3 / 32))) * M
  have hM : 0 < M := by dsimp only [M]; positivity
  have hK : 0 < K := by dsimp only [K]; positivity
  refine ⟨8, K, c / 2, by norm_num, hK, by positivity, ?_⟩
  intro Q hQ β hβ ζ hζ P Pdag hP hPdag t ht ρ hρ
  let i : Fin d := ⟨0, by omega⟩
  have hρ1 : 1 ≤ ρ := by linarith
  obtain ⟨χ, hχ, hχc, hχb, hχzero, hχder, hχone⟩ := hcut ρ hρ1
  obtain ⟨O, Kspace, hO, hKspace, hball, hKO, hχO⟩ :=
    c25_transpose_cutoff_unit_plateau ρ hρ χ hχone
  let U : Set (Vec d) := {x | euclideanNorm x < ρ}
  have hsupport : ∀ x, x ∉ U → χ x = 0 := by
    intro x hx
    apply hχzero x
    change ¬ euclideanNorm x < ρ at hx
    linarith [le_of_not_gt hx]
  obtain ⟨fr, Vlocal, hmfr, hmV, hfr, hVlocal⟩ :=
    short_time_transpose_cutoff_measurable_evolution χ hχ hχc U hsupport Λ hΛ i ζ
  obtain ⟨g, hg⟩ := timeFlux_transpose_initial_generator (i := i) (ζ := ζ) hβ i
  obtain ⟨F, Fg, Dg, hF, hFg, hDg, heF, heFg, heDg, hwitness⟩ :=
    c25_transpose_retained_joint_weak_equations Q hP hPdag hg
  obtain ⟨Mseq, _, hsmooth⟩ := node_eq_u2E_reduced_u2D_bounds_u23_derivatives_of_deps
    node_eq_u2E_reduced_u2D_bounds_of_deps d D
  have hlocalV : @Measurable _ _ (localSigma U) (borel _) (fun ω => Vlocal ω t) := by
    exact hmV.comp (measurable_id.prodMk measurable_const)
  have herr : ∀ᵐ ω ∂reducedLaw Q,
      ∀ᵐ x ∂volume.restrict (PDE.euclideanBall (0 : PDE.Vec d) (q * (3 / 16))),
        ‖F ((t : ℝ), translate x ω) - (Vlocal ω t) x‖ ≤
          (1 + 2 / Real.sin (q * (3 / 32))) * (M * Real.exp (-(c / 2) * ρ ^ 2)) := by
    filter_upwards [hwitness, hsmooth Q hQ, c4_ae_reduced_physical_elliptic Q,
      c25_transpose_retained_initial_match hβ i,
      hdecay Q hQ β hβ i ζ hζ P Pdag hP hPdag g hg F hF heF] with ω hw hs ha hi hgauss
    have hell (x : Vec d) : S5Elliptic (ω.1 x) Λ := s5Elliptic_of_isElliptic hΛ ha x
    have hret (x : Vec d) : S5Elliptic ((ForcedLocality.retainedPair χ ω).1 x) Λ :=
      short_time_retained_cutoff_elliptic χ ω x (hell x) (hχb x).1 (hχb x).2
    have hcoeff (j k : Fin d) : MemLp (fun x => ((ForcedLocality.retainedPair χ ω).1 x j k : ℂ)) ∞ volume := by
      apply memLp_top_of_bound
        (Complex.continuous_ofReal.comp
          ((ForcedLocality.retainedPair χ ω).1.continuous.matrix_elem j k)).aestronglyMeasurable Λ
      exact ae_of_all _ fun x => by
        change ‖(((ForcedLocality.retainedPair χ ω).1 x j k : ℝ) : ℂ)‖ ≤ Λ
        rw [Complex.norm_real, Real.norm_eq_abs]
        exact (hret x).entry_abs_le j k
    obtain ⟨Pr, Tr, hPr, hTr, _, _, heVlocal⟩ := hVlocal ω hret
    obtain ⟨gr, hgr⟩ := short_time_retained_transpose_drift_generator χ hχ hχc ω hs.1 i ζ (fr ω) (hfr ω hs.1)
    obtain ⟨V, Z, X, Y, H, W, hW, heW, hw2, hV, hZ, hX, hY, heV, heZ,
      heY, hX0, hHc, hH, hres, hjoint⟩ := hw.2 χ hcoeff Λ (by positivity)
        (ae_of_all _ hret) Pr Tr hTr (fr ω) gr hgr
    have hinit := hi χ O Kspace hO hχO hKspace hKO (fr ω) (hfr ω hs.1)
    obtain ⟨hmatch, htime, hX2, hY2, hJ2⟩ := hjoint Kspace hKspace hinit
    obtain ⟨hgrad, hspace⟩ := c25_transpose_retained_residual_spatial_equations ω χ O Kspace hO hKO hχO
      i ζ F Fg Dg V Z X Y W (fun s => Tr s.toNNReal (fr ω)) H heV heW hH hX0 heY
      (fun s hs hs1 => hmatch s hs.le hs1) hres
    let Zactual : ℝ × Vec d → ℂ := fun p => F (p.1, translate p.2 ω) - V p
    let J := fun s x j => (Ioc (0 : ℝ) 1).indicator (fun r => Dg j (r, translate x ω) - W j (r, x)) s
    have hZactual : Measurable Zactual := by
      have hshift : Measurable (fun p : ℝ × Vec d => (p.1, translate p.2 ω)) :=
        measurable_fst.prodMk (Probability.continuous_translate.measurable.comp
          (measurable_snd.prodMk measurable_const))
      exact (hF.comp hshift).sub hV
    have henergy := hgauss χ hχ ρ hρ1 hχb hχzero hχder hχone (fr ω) (hfr ω hs.1)
      Pr Tr hTr V hV heV
    have hbound := hmax Kspace hKspace hball ω.1 ω.1.continuous hell i ζ hζ X Y Zactual J
      hX hY hZactual hX2 hY2 hJ2 hX0 htime hgrad hspace hmatch L G c ρ hL hG.le henergy
      (t : ℝ) ⟨t.coe_nonneg, ht⟩
    filter_upwards [hbound, ae_restrict_of_ae (heV (t : ℝ))] with x hx hv
    have ht' : (t : ℝ).toNNReal = t := by simp
    rw [ht', ← heVlocal t] at hv
    simpa only [Zactual, hv, M, mul_assoc] using hx
  have hFtime : Measurable (fun ω => F ((t : ℝ), ω)) := hF.comp (measurable_const.prodMk measurable_id)
  have heFtime : (fun ω => F ((t : ℝ), ω)) =ᵐ[reducedLaw Q]
      transposeEndpoint Q i Pdag β t := by
    simpa only [transposeEndpoint, Real.toNNReal_coe] using heF (t : ℝ)
  obtain ⟨V, hV, herror⟩ := c25_local_observation_of_retained_spatial_bound Q ρ
    ((1 + 2 / Real.sin (q * (3 / 32))) * (M * Real.exp (-(c / 2) * ρ ^ 2)))
    (q * (3 / 16)) (by positivity) (by positivity)
    (transposeEndpoint Q i Pdag β t) (fun ω => F ((t : ℝ), ω)) hFtime heFtime
    (fun ω => Vlocal ω t) hlocalV herr
  refine ⟨V, hV, ?_⟩
  filter_upwards [herror] with ω hω
  simpa only [K, mul_assoc] using hω

end EinsteinFull.Blueprint
