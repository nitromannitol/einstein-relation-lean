import EinsteinFull.Calculus.C6SublinearSmoothFlux
import EinsteinFull.Calculus.C5TestCLTSupport
import EinsteinFull.Calculus.C3JointLocalizationSupport
import EinsteinRelation.Correctors.P53SourceSkewStationaryRepresentative
import EinsteinRelation.Correctors.AKMHeatSpatialDilation
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import EinsteinRelation.Correctors.P53SourceSkewMollifyAlgebra
import EinsteinRelation.Correctors.P53SourceSkewHeatSmoothedDivergence
import EinsteinRelation.Correctors.HeatGradientConvolution
import EinsteinRelation.Correctors.HeatGradientTranslation
import EinsteinRelation.Correctors.HeatGradientJointMeasurability
import EinsteinRelation.Correctors.HeatHessianUniformL1
import EinsteinRelation.Correctors.HeatHessianUnitIntegrability
import EinsteinRelation.Correctors.StationaryConvolutionFubini
import EinsteinRelation.Correctors.HeatTransferConvolution
import EinsteinRelation.Correctors.HeatTransferMoments
import EinsteinRelation.Correctors.HeatTransferIdentity
import EinsteinRelation.Correctors.HeatKernelMixedHessian
import EinsteinRelation.Correctors.IntegratedHeatTransfer
import EinsteinRelation.Correctors.HeatTransferTimeIntegrability
import EinsteinRelation.Correctors.SpatialDivergenceFixedTest
import EinsteinRelation.Correctors.StationarySpatialWeakDivergence
import EinsteinRelation.Environment.TranslationErgodicitySupport
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators Convolution
noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation EinsteinFull EinsteinRelation.External.AKM EinsteinRelation.Correctors
open EinsteinRelation.Environment.AKMTestIntegralSupport ReductionImageV3
open EinsteinRelation.Correctors.HeatSelectedSkewMeaning

/-- Every characterized unit-slope source corrector has the actual canonical
centered flux. Scalar uniqueness supplies the identification, with no extra
stationarity or normalization premise. -/
theorem c6_actualSourceCenteredFlux_canonical
    {d : ℕ} [Fact (2 ≤ d)] {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) (i : Fin d)
    (φ : Corrector (actualCoefficientLaw Q) (correctorUnitVector i).ofLp) :
    ∀ᵐ ω ∂physicalReferenceLaw Q, ∀ᵐ y ∂(volume : Measure (Vec d)),
      centeredFlux φ (project (r₀ := r₀) Q.ellipticity_parameter ω) y =
        ellipticityScale L •
          ((canonicalCorrectorFlux Q i (translate (r₀ • y) (reduce ω.1))).ofLp -
            (expectedCorrectorFlux Q i).ofLp) := by
  exact c6_unitCenteredFlux_eq_canonical Q i φ
    (EinsteinFull.Calculus.C5TestCLT.sourceCorrector_canonical_grad_identification
      Q i φ.toSourceCorrector)

/-- The actual centered source flux is covariant under every real translation,
as a consequence of scalar uniqueness rather than an added stationarity clause. -/
theorem c6_actualSourceCenteredFlux_real_covariant
    {d : ℕ} [Fact (2 ≤ d)] {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) (i : Fin d)
    (φ : Corrector (actualCoefficientLaw Q) (correctorUnitVector i).ofLp)
    (z : Vec d) :
    ∀ᵐ ω ∂physicalReferenceLaw Q, ∀ᵐ x ∂(volume : Measure (Vec d)),
      centeredFlux φ (project (r₀ := r₀) Q.ellipticity_parameter ω) (x + z) =
        centeredFlux φ (project (r₀ := r₀) Q.ellipticity_parameter
          (physicalTranslate (r₀ • z) ω)) x := by
  have hmp : MeasurePreserving (physicalTranslate (r₀ • z))
      (physicalReferenceLaw Q) (physicalReferenceLaw Q) :=
    ⟨measurable_physicalTranslate _, physicalReferenceLaw_translation_invariant Q _⟩
  have hid := c6_actualSourceCenteredFlux_canonical Q i φ
  filter_upwards [hid, hmp.quasiMeasurePreserving.ae hid] with ω hω hzω
  have hx := (measurePreserving_add_right (volume : Measure (Vec d)) z).quasiMeasurePreserving.ae hω
  filter_upwards [hx, hzω] with x hxx hzx
  rw [hxx, hzx]
  simp only [physicalTranslate, reduce_translate, translate_add, smul_add]

/-- Spatial translation preserves every clause of the literal heat selection. -/
private theorem c6_traceHeatSelection_translate {d : ℕ}
    {g : Vec d → Vec d} {G : Fin d → Fin d → Vec d → Vec d}
    (h : IsHeatSelectedFluxGradient g G) (z : Vec d) :
    IsHeatSelectedFluxGradient (fun x => g (x + z))
      (fun j k x => G j k (x + z)) := by
  intro j k l R
  obtain ⟨N, hN⟩ := exists_nat_gt ((R : ℝ) + 1 + euclideanNorm z)
  have hRS : (R : ℝ) + 1 + euclideanNorm z ≤ (N : ℝ) + 1 := by linarith
  have hsub : ball z ((R : ℝ) + 1) ⊆ ball (0 : Vec d) ((N : ℝ) + 1) := by
    intro x hx
    have htri := TimeChange.euclideanNorm_add_le (x - z) z
    rw [sub_add_cancel] at htri
    change euclideanNorm (x - z) < (R : ℝ) + 1 at hx
    change euclideanNorm (x - 0) < (N : ℝ) + 1
    rw [sub_zero]
    linarith
  have hm := Measure.restrict_mono_set (volume : Measure (Vec d)) hsub
  have hmp := measurePreserving_add_center_ball z ((R : ℝ) + 1)
  obtain ⟨hi, hT, hG, hlim⟩ := h j k l N
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro m n
    filter_upwards [hmp.quasiMeasurePreserving.ae (ae_mono hm (hi m n))] with x hx
    refine ⟨?_, ?_⟩
    · filter_upwards [hx.1] with t ht
      have hc := ((measurePreserving_add_right (volume : Measure (Vec d)) z).integrable_comp_emb
        (Homeomorph.addRight z).measurableEmbedding).mpr ht
      change Integrable (fun y => akmHeatGradientDensity g t j k l (x + z) (y + z))
        volume at hc
      simpa only [← akmHeatGradientDensity_translation] using hc
    · simpa only [akmHeatGradientSpaceIntegral_translation] using hx.2
  · intro m n
    simpa only [Function.comp_def, iteratedAKMHeatGradientTruncation_translation] using
      ((hT m n).mono_measure hm).comp_measurePreserving hmp
  · exact (hG.mono_measure hm).comp_measurePreserving hmp
  · apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
      (fun _ => zero_le) ?_
    intro mn
    simpa only [iteratedAKMHeatGradientTruncation_translation] using
      eLpNorm_add_center_ball_le
        (fun x => iteratedAKMHeatGradientTruncation g mn.1 mn.2 j k l x - G j k x l)
        z ((R : ℝ) + 1) ((N : ℝ) + 1) hRS ((hT mn.1 mn.2).sub hG).aestronglyMeasurable

/-- Heat selection upgrades the actual flux gradient's covariance from lattice
translations to every real translation. -/
theorem c6_actualSourceFluxGradient_real_covariant
    {d : ℕ} [Fact (2 ≤ d)] {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) (i : Fin d)
    {φ : Corrector (actualCoefficientLaw Q) (correctorUnitVector i).ofLp}
    (S : FluxCorrector φ) (z : Vec d) :
    ∀ᵐ ω ∂physicalReferenceLaw Q, ∀ᵐ x ∂(volume : Measure (Vec d)), ∀ j k l,
      S.grad (project (r₀ := r₀) Q.ellipticity_parameter ω) j k (x + z) l =
        S.grad (project (r₀ := r₀) Q.ellipticity_parameter
          (physicalTranslate (r₀ • z) ω)) j k x l := by
  have hmp : MeasurePreserving (physicalTranslate (r₀ • z))
      (physicalReferenceLaw Q) (physicalReferenceLaw Q) :=
    ⟨measurable_physicalTranslate _, physicalReferenceLaw_translation_invariant Q _⟩
  have hsel := (measurePreserving_akmProject Q).quasiMeasurePreserving.ae S.heat_selected
  filter_upwards [hsel, hmp.quasiMeasurePreserving.ae hsel,
    c6_actualSourceCenteredFlux_real_covariant Q i φ z] with ω hs hzs hflux
  exact c6_isHeatSelectedFluxGradient_ae_unique
    (c6_isHeatSelectedFluxGradient_congr_ae hflux (c6_traceHeatSelection_translate hs z)) hzs

/-- The row trace inherits real translation covariance from its selected gradient. -/
theorem c6_actualSourceRowDivergence_real_covariant
    {d : ℕ} [Fact (2 ≤ d)] {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) (i : Fin d)
    {φ : Corrector (actualCoefficientLaw Q) (correctorUnitVector i).ofLp}
    (S : FluxCorrector φ) (z : Vec d) :
    ∀ᵐ ω ∂physicalReferenceLaw Q, ∀ᵐ x ∂(volume : Measure (Vec d)),
      c6SourceRowDivergence S (project (r₀ := r₀) Q.ellipticity_parameter ω) (x + z) =
        c6SourceRowDivergence S (project (r₀ := r₀) Q.ellipticity_parameter
          (physicalTranslate (r₀ • z) ω)) x := by
  filter_upwards [c6_actualSourceFluxGradient_real_covariant Q i S z] with ω hω
  filter_upwards [hω] with x hx
  funext j
  exact Finset.sum_congr rfl fun k _ => hx j k k

/-- Real covariance holds on the actual coefficient law itself, retaining
the spatial almost-everywhere qualifier. -/
theorem c6_actualSourceRowDivergence_real_stationary
    {d : ℕ} [Fact (2 ≤ d)] {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) (i : Fin d)
    {φ : Corrector (actualCoefficientLaw Q) (correctorUnitVector i).ofLp}
    (S : FluxCorrector φ) (z : Vec d) :
    ∀ᵐ a ∂actualCoefficientLaw Q, ∀ᵐ x ∂(volume : Measure (Vec d)),
      c6SourceRowDivergence S a (x + z) =
        c6SourceRowDivergence S (translateCoefficient z a) x := by
  have hm : Measurable (fun p : Coefficient d (AKMUpperEllipticity L) × Vec d =>
      c6SourceRowDivergence S p.1 p.2) :=
    c6SourceRowDivergence_measurable S
  let s : Set (Coefficient d (AKMUpperEllipticity L) × Vec d) := {p |
    c6SourceRowDivergence S p.1 (p.2 + z) =
      c6SourceRowDivergence S (translateCoefficient z p.1) p.2}
  have hs : MeasurableSet s := measurableSet_eq_fun
    (hm.comp (measurable_fst.prodMk (measurable_snd.add_const z)))
    (hm.comp (((measurable_translateCoefficient z).comp measurable_fst).prodMk measurable_snd))
  have hset : MeasurableSet {a : Coefficient d (AKMUpperEllipticity L) |
      ∀ᵐ x ∂(volume : Measure (Vec d)), (a, x) ∈ s} := by
    have h := measurable_measure_prodMk_left (ν := (volume : Measure (Vec d))) hs.compl
    have heq : {a : Coefficient d (AKMUpperEllipticity L) |
        ∀ᵐ x ∂(volume : Measure (Vec d)), (a, x) ∈ s} =
        (fun a => (volume : Measure (Vec d)) (Prod.mk a ⁻¹' sᶜ)) ⁻¹' {0} := by
      ext a
      simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_singleton_iff, ae_iff]
      rfl
    rw [heq]
    exact h (measurableSet_singleton 0)
  apply (ae_map_iff (measurable_project Q.ellipticity_parameter).aemeasurable hset).mpr
  filter_upwards [c6_actualSourceRowDivergence_real_covariant Q i S z] with ω hω
  simpa only [s, Set.mem_ofPred_eq, project_translation_covariant] using hω

/-- A measurable source-law observable obtained from smooth origin averages
of the actual row trace. Its orbit identity is proved almost everywhere below. -/
def c6SourceTraceObservable {d : ℕ} {K : ℝ} {P : Measure (Coefficient d K)}
    {e : Vec d} {φ : Corrector P e} (S : FluxCorrector φ) (j : Fin d)
    (a : Coefficient d K) : ℝ :=
  limsup (fun n => originBumpAverage (fun x => c6SourceRowDivergence S a x j) n) atTop

theorem c6SourceTraceObservable_measurable {d : ℕ} {K : ℝ}
    {P : Measure (Coefficient d K)} {e : Vec d} {φ : Corrector P e}
    (S : FluxCorrector φ) (j : Fin d) : Measurable (c6SourceTraceObservable S j) := by
  apply Measurable.limsup
  intro n
  have hb : Measurable (fun y : Vec d => (representativeBump d n).normed volume (-y)) :=
    ((representativeBump d n).continuous_normed.comp continuous_neg).measurable
  have hm := (measurable_pi_apply j).comp (c6SourceRowDivergence_measurable S)
  exact (((hb.comp measurable_snd).mul hm).stronglyMeasurable).integral_prod_right'.measurable

/-- The actual selected row trace is the orbit of a measurable environment
observable. No point evaluation or annealed gradient moment is assumed. -/
theorem c6_actualSourceTraceObservable_orbit
    {d : ℕ} [Fact (2 ≤ d)] {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) (i : Fin d)
    {φ : Corrector (actualCoefficientLaw Q) (correctorUnitVector i).ofLp}
    (S : FluxCorrector φ) (j : Fin d) :
    ∀ᵐ a ∂actualCoefficientLaw Q, ∀ᵐ x ∂(volume : Measure (Vec d)),
      c6SourceTraceObservable S j (translateCoefficient x a) =
        c6SourceRowDivergence S a x j := by
  let : IsProbabilityMeasure (actualCoefficientLaw Q) :=
    (lawHypotheses_actualCoefficientLaw Q).1
  have hm := (measurable_pi_apply j).comp (c6SourceRowDivergence_measurable S)
  let s : Set ((Vec d × Coefficient d (AKMUpperEllipticity L)) × Vec d) := {p |
    c6SourceRowDivergence S (translateCoefficient p.1.1 p.1.2) p.2 j =
      c6SourceRowDivergence S p.1.2 (p.2 + p.1.1) j}
  have hs : MeasurableSet s := measurableSet_eq_fun
    (hm.comp ((measurable_translateCoefficient_joint.comp measurable_fst).prodMk measurable_snd))
    (hm.comp ((measurable_snd.comp measurable_fst).prodMk
      (measurable_snd.add (measurable_fst.comp measurable_fst))))
  have hset : MeasurableSet {p : Vec d × Coefficient d (AKMUpperEllipticity L) |
      ∀ᵐ y ∂(volume : Measure (Vec d)), (p, y) ∈ s} := by
    have h := measurable_measure_prodMk_left (ν := (volume : Measure (Vec d))) hs.compl
    have heq : {p : Vec d × Coefficient d (AKMUpperEllipticity L) |
        ∀ᵐ y ∂(volume : Measure (Vec d)), (p, y) ∈ s} =
        (fun p => (volume : Measure (Vec d)) (Prod.mk p ⁻¹' sᶜ)) ⁻¹' {0} := by
      ext p
      simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_singleton_iff, ae_iff]
      rfl
    rw [heq]
    exact h (measurableSet_singleton 0)
  have hcov : ∀ z : Vec d, ∀ᵐ a ∂actualCoefficientLaw Q,
      ∀ᵐ y ∂(volume : Measure (Vec d)), ((z, a), y) ∈ s := by
    intro z
    filter_upwards [c6_actualSourceRowDivergence_real_stationary Q i S z] with a ha
    filter_upwards [ha] with y hy
    exact (congrFun hy j).symm
  have hae := (Measure.ae_ae_comm (μ := (volume : Measure (Vec d)))
    (ν := actualCoefficientLaw Q) hset).mp (ae_of_all _ hcov)
  filter_upwards [hae, c6SourceRowDivergence_divergence_free S] with a ha hdiv
  have hloc := locallyIntegrableOn_univ.mp (hdiv.1 j)
  filter_upwards [ha, ae_tendsto_originBumpAverage hloc] with x hx hlim
  change ∀ᵐ y ∂(volume : Measure (Vec d)),
    c6SourceRowDivergence S (translateCoefficient x a) y j =
      c6SourceRowDivergence S a (y + x) j at hx
  unfold c6SourceTraceObservable
  simp_rw [originBumpAverage_translate_eq
    (f := fun y => c6SourceRowDivergence S a y j)
    (h := fun y => c6SourceRowDivergence S (translateCoefficient x a) y j) x hx]
  exact hlim.limsup_eq

/-- Dilation of the actual spatial-then-temporal heat integral on a
positive closed time window. This does not assume a limiting formula. -/
theorem c6_akmHeatGradientTimeIntegral_dilation {d : ℕ}
    (g : Vec d → Vec d) (c b a h : ℝ) (hc : 0 < c)
    (ha : 0 < a) (hah : a ≤ h) (j k l : Fin d) (x : Vec d) :
    (∫ t in Icc (c ^ 2 * a) (c ^ 2 * h),
      akmHeatGradientSpaceIntegral (fun z => b • g (c⁻¹ • z)) t j k l (c • x)) =
        b * ∫ t in Icc a h, akmHeatGradientSpaceIntegral g t j k l x := by
  have hscaled : c ^ 2 * a ≤ c ^ 2 * h := mul_le_mul_of_nonneg_left hah (sq_nonneg c)
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hscaled,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hah]
  have hcomp : (∫ t in a..h,
      akmHeatGradientSpaceIntegral (fun z => b • g (c⁻¹ • z))
        (c ^ 2 * t) j k l (c • x)) =
      (b * (c⁻¹) ^ 2) * ∫ t in a..h,
        akmHeatGradientSpaceIntegral g t j k l x := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr_ae_restrict
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
    have ht' : t ∈ Ioc a h := by simpa only [uIoc_of_le hah] using ht
    exact akmHeatGradientSpaceIntegral_dilation g c b t hc
      (lt_of_lt_of_le ha ht'.1.le) j k l x
  have hchange := intervalIntegral.smul_integral_comp_mul_left
    (a := a) (b := h)
    (fun t => akmHeatGradientSpaceIntegral (fun z => b • g (c⁻¹ • z))
      t j k l (c • x)) (c ^ 2)
  rw [hcomp, smul_eq_mul] at hchange
  rw [← hchange]
  field_simp

/-- The exact time window required after physical dilation. Its endpoints
are positive real numbers; they need not be natural-number cutoffs. -/
theorem c6_iteratedAKMHeatGradientTruncation_dilation {d : ℕ}
    (g : Vec d → Vec d) (c b : ℝ) (hc : 0 < c)
    (m n : ℕ) (j k l : Fin d) (x : Vec d) :
    iteratedAKMHeatGradientTruncation (fun z => b • g (c⁻¹ • z))
        m n j k l (c • x) =
      b * ∫ t in Icc ((c ^ 2)⁻¹ * ((m + 1 : ℕ) : ℝ)⁻¹)
        ((c ^ 2)⁻¹ * ((n + 1 : ℕ) : ℝ)),
          akmHeatGradientSpaceIntegral g t j k l x := by
  have hca : 0 < (c ^ 2)⁻¹ * ((m + 1 : ℕ) : ℝ)⁻¹ := by positivity
  have hlow : ((m + 1 : ℕ) : ℝ)⁻¹ ≤ 1 := by
    apply inv_le_one_of_one_le₀
    norm_cast
    omega
  have hhigh : 1 ≤ ((n + 1 : ℕ) : ℝ) := by norm_cast; omega
  have hah := mul_le_mul_of_nonneg_left (hlow.trans hhigh)
    (inv_nonneg.mpr (sq_nonneg c))
  have h := c6_akmHeatGradientTimeIntegral_dilation g c b
    ((c ^ 2)⁻¹ * ((m + 1 : ℕ) : ℝ)⁻¹)
    ((c ^ 2)⁻¹ * ((n + 1 : ℕ) : ℝ)) hc hca hah j k l x
  change (∫ t in Icc (((m + 1 : ℕ) : ℝ)⁻¹) ((n + 1 : ℕ) : ℝ),
    akmHeatGradientSpaceIntegral (fun z => b • g (c⁻¹ • z)) t j k l (c • x)) = _
  simpa only [mul_inv_cancel_left₀ (pow_ne_zero 2 hc.ne')] using h

/-- The finite heat truncations depend only on the spatial almost-everywhere
class of their source; this preserves the literal order of integration. -/
theorem c6_heatTruncation_congr_ae {d : ℕ} {g h : Vec d → Vec d}
    (hgh : g =ᵐ[volume] h) (m n : ℕ) (j k l : Fin d) (x : Vec d) :
    iteratedAKMHeatGradientTruncation g m n j k l x =
      iteratedAKMHeatGradientTruncation h m n j k l x := by
  have hspace (t : ℝ) : akmHeatGradientSpaceIntegral g t j k l x =
      akmHeatGradientSpaceIntegral h t j k l x := by
    apply integral_congr_ae
    filter_upwards [hgh] with y hy
    simp only [akmHeatGradientDensity, hy]
  simp only [iteratedAKMHeatGradientTruncation, hspace]

/-- Exact spatial Jacobian for a tested dilated field, with no integrability
premise hidden in a change of variables. -/
theorem c6_testPairing_dilation {d : ℕ} (f ψ : Vec d → ℝ) (r : ℝ) (hr : 0 < r) :
    (∫ y, f (r • y) * ψ y) =
      (r ^ d)⁻¹ * ∫ x, f x * ψ (r⁻¹ • x) := by
  have h := Measure.integral_comp_smul (volume : Measure (Vec d))
    (fun x => f x * ψ (r⁻¹ • x)) r
  simpa only [smul_smul, inv_mul_cancel₀ hr.ne', one_smul,
    Module.finrank_pi, Fintype.card_fin, smul_eq_mul,
    abs_of_pos (inv_pos.mpr (pow_pos hr d))] using h

/-- The actual source heat truncation has the exact reduced time endpoints.
Only the canonical identification of the given source corrector is used. -/
theorem c6_actualSource_heatTruncation_scaled
    {d : ℕ} [Fact (2 ≤ d)] {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) (i : Fin d)
    (φ : Corrector (actualCoefficientLaw Q) (correctorUnitVector i).ofLp) :
    ∀ᵐ ω ∂physicalReferenceLaw Q, ∀ (m n : ℕ) (j k l : Fin d) (x : Vec d),
      iteratedAKMHeatGradientTruncation
        (centeredFlux φ (project (r₀ := r₀) Q.ellipticity_parameter ω)) m n j k l x =
      ellipticityScale L * ∫ t in Icc (r₀ ^ 2 * ((m + 1 : ℕ) : ℝ)⁻¹)
        (r₀ ^ 2 * ((n + 1 : ℕ) : ℝ)), akmHeatGradientSpaceIntegral
          (fun y => (canonicalCorrectorFlux Q i (translate y (reduce ω.1))).ofLp -
            (expectedCorrectorFlux Q i).ofLp) t j k l (r₀ • x) := by
  have hr : 0 < r₀ := zero_lt_one.trans_le Q.range_parameter
  filter_upwards [c6_actualSourceCenteredFlux_canonical Q i φ] with ω hω
  intro m n j k l x
  rw [c6_heatTruncation_congr_ae hω]
  have h := c6_iteratedAKMHeatGradientTruncation_dilation
    (fun y => (canonicalCorrectorFlux Q i (translate y (reduce ω.1))).ofLp -
      (expectedCorrectorFlux Q i).ofLp)
    r₀⁻¹ (ellipticityScale L) (inv_pos.mpr hr) m n j k l (r₀ • x)
  simpa only [inv_inv, inv_pow, inv_smul_smul₀ hr.ne'] using h

/-- Pairing the actual diagonal truncation with a spatial test retains the
source amplitude, the spatial Jacobian, and both reduced cutoff endpoints. -/
theorem c6_actualSource_diagonalPairing_scaled
    {d : ℕ} [Fact (2 ≤ d)] {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) (i : Fin d)
    (φ : Corrector (actualCoefficientLaw Q) (correctorUnitVector i).ofLp) :
    ∀ᵐ ω ∂physicalReferenceLaw Q, ∀ (m n : ℕ) (j : Fin d) (ψ : Vec d → ℝ),
      (∫ x, (∑ k : Fin d, iteratedAKMHeatGradientTruncation
        (centeredFlux φ (project (r₀ := r₀) Q.ellipticity_parameter ω)) m n j k k x) * ψ x) =
      ellipticityScale L * (r₀ ^ d)⁻¹ * ∫ y,
        (∑ k : Fin d, ∫ t in Icc (r₀ ^ 2 * ((m + 1 : ℕ) : ℝ)⁻¹)
          (r₀ ^ 2 * ((n + 1 : ℕ) : ℝ)), akmHeatGradientSpaceIntegral
            (fun z => (canonicalCorrectorFlux Q i (translate z (reduce ω.1))).ofLp -
              (expectedCorrectorFlux Q i).ofLp) t j k k y) * ψ (r₀⁻¹ • y) := by
  have hr : 0 < r₀ := zero_lt_one.trans_le Q.range_parameter
  filter_upwards [c6_actualSource_heatTruncation_scaled Q i φ] with ω hω
  intro m n j ψ
  let f : Vec d → ℝ := fun y => ∑ k : Fin d,
    ∫ t in Icc (r₀ ^ 2 * ((m + 1 : ℕ) : ℝ)⁻¹)
      (r₀ ^ 2 * ((n + 1 : ℕ) : ℝ)), akmHeatGradientSpaceIntegral
        (fun z => (canonicalCorrectorFlux Q i (translate z (reduce ω.1))).ofLp -
          (expectedCorrectorFlux Q i).ofLp) t j k k y
  have heq (x : Vec d) : (∑ k : Fin d, iteratedAKMHeatGradientTruncation
      (centeredFlux φ (project (r₀ := r₀) Q.ellipticity_parameter ω)) m n j k k x) =
      ellipticityScale L * f (r₀ • x) := by
    simp_rw [hω m n j]
    exact (Finset.mul_sum _ _ _).symm
  calc
    _ = ∫ x, ellipticityScale L * (f (r₀ • x) * ψ x) := by
      apply integral_congr_ae
      exact ae_of_all _ fun x => by
        dsimp only
        rw [heq]
        ring
    _ = ellipticityScale L * ∫ x, f (r₀ • x) * ψ x := integral_const_mul _ _
    _ = _ := by rw [c6_testPairing_dilation f ψ r₀ hr]; ring

open Classical in
/-- The physical field of a reduced pair in the reduced image, with a fixed
value outside it. -/
def c6PhysicalOfReduced {d : ℕ} {L : ℝ} (ω₀ : PhysicalField d L) (ρ : FieldPair d) :
    PhysicalField d L :=
  if h : ρ ∈ physicalReducedRange L then inverseReducePhysical ⟨ρ, h⟩ else ω₀

theorem c6_measurable_physicalOfReduced {d : ℕ} {L : ℝ} (ω₀ : PhysicalField d L) :
    Measurable (c6PhysicalOfReduced ω₀) := by
  classical
  exact Measurable.dite (physicalReduceHomeomorph (d := d) (L := L)).symm.continuous.measurable
    measurable_const (measurableSet_physicalReducedRange L)

theorem c6_physicalOfReduced_reduce {d : ℕ} {L : ℝ} (ω₀ ω : PhysicalField d L) :
    c6PhysicalOfReduced ω₀ (reduce ω.1) = ω := by
  have h : reduce ω.1 ∈ physicalReducedRange L := ⟨ω.1, ω.2, rfl⟩
  rw [c6PhysicalOfReduced, dif_pos h]
  exact inverseReduce_reducePhysical ω

theorem c6_reduce_physicalOfReduced {d : ℕ} {L : ℝ} (ω₀ : PhysicalField d L)
    {ρ : FieldPair d} (h : ρ ∈ physicalReducedRange L) :
    reduce (c6PhysicalOfReduced ω₀ ρ).1 = ρ := by
  rw [c6PhysicalOfReduced, dif_pos h]
  exact congrArg Subtype.val (reducePhysical_inverseReduce ⟨ρ, h⟩)

/-- Reconstruction carries the reduced law to the physical reference law. -/
theorem c6_measurePreserving_physicalOfReduced {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) (ω₀ : PhysicalField d L) :
    MeasurePreserving (c6PhysicalOfReduced ω₀) (reducedEnvironmentLaw Q)
      (physicalReferenceLaw Q) := by
  refine ⟨c6_measurable_physicalOfReduced ω₀, ?_⟩
  rw [← (measurePreserving_physicalReduction Q).map_eq,
    Measure.map_map (c6_measurable_physicalOfReduced ω₀)
      (measurePreserving_physicalReduction Q).measurable]
  conv_rhs => rw [← Measure.map_id (μ := physicalReferenceLaw Q)]
  congr 1
  funext ω
  exact c6_physicalOfReduced_reduce ω₀ ω


/-- The reduced tested trace keeps the inverse source amplitude and the exact
spatial Jacobian. It is defined using spatial integration of the selected row. -/
def c6ReducedSourceTracePairing
    {d : ℕ} {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀) (ω₀ : PhysicalField d L)
    {i : Fin d}
    {φ : Corrector (actualCoefficientLaw Q) (correctorUnitVector i).ofLp}
    (S : FluxCorrector φ) (ψ : Vec d → ℝ) (j : Fin d) (ρ : FieldPair d) : ℝ :=
  (r₀ ^ d / ellipticityScale L) * ∫ x,
    c6SourceRowDivergence S
      (project (r₀ := r₀) Q.ellipticity_parameter (c6PhysicalOfReduced ω₀ ρ)) x j * ψ (r₀ • x)

theorem c6ReducedSourceTracePairing_measurable
    {d : ℕ} {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀) (ω₀ : PhysicalField d L)
    {i : Fin d}
    {φ : Corrector (actualCoefficientLaw Q) (correctorUnitVector i).ofLp}
    (S : FluxCorrector φ) {ψ : Vec d → ℝ} (hψ : Measurable ψ) (j : Fin d) :
    Measurable (c6ReducedSourceTracePairing Q ω₀ S ψ j) := by
  have hp := (measurable_project (r₀ := r₀) Q.ellipticity_parameter).comp
    (c6_measurable_physicalOfReduced ω₀)
  have hm : Measurable (fun p : FieldPair d × Vec d =>
      c6SourceRowDivergence S
        (project (r₀ := r₀) Q.ellipticity_parameter (c6PhysicalOfReduced ω₀ p.1)) p.2 j *
          ψ (r₀ • p.2)) :=
    (((measurable_pi_apply j).comp (c6SourceRowDivergence_measurable S)).comp
      ((hp.comp measurable_fst).prodMk measurable_snd)).mul
        (hψ.comp (measurable_snd.const_smul r₀))
  exact hm.stronglyMeasurable.integral_prod_right'.measurable.const_mul _

/-- The reduced positive-window diagonal sums converge to a measurable tested
trace. Both cutoffs and the source amplitude are transported literally. -/
theorem c6ReducedSourceTracePairing_heat_limit
    {d : ℕ} [Fact (2 ≤ d)] {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) (ω₀ : PhysicalField d L) (i : Fin d)
    {φ : Corrector (actualCoefficientLaw Q) (correctorUnitVector i).ofLp}
    (S : FluxCorrector φ) :
    ∀ᵐ ρ ∂reducedEnvironmentLaw Q, ∀ (ψ : Vec d → ℝ),
      Continuous ψ → HasCompactSupport ψ → ∀ j : Fin d,
      Tendsto (fun mn : ℕ × ℕ => ∫ y,
        (∑ k : Fin d, ∫ t in Icc (r₀ ^ 2 * ((mn.1 + 1 : ℕ) : ℝ)⁻¹)
          (r₀ ^ 2 * ((mn.2 + 1 : ℕ) : ℝ)), akmHeatGradientSpaceIntegral
            (fun z => (canonicalCorrectorFlux Q i (translate z ρ)).ofLp -
              (expectedCorrectorFlux Q i).ofLp) t j k k y) * ψ y)
        atTop (𝓝 (c6ReducedSourceTracePairing Q ω₀ S ψ j ρ)) := by
  have hr : 0 < r₀ := zero_lt_one.trans_le Q.range_parameter
  have hs : ellipticityScale L ≠ 0 := (ellipticityScale_pos Q.ellipticity_parameter).ne'
  have hp : MeasurePreserving (project (r₀ := r₀) Q.ellipticity_parameter)
      (physicalReferenceLaw Q) (actualCoefficientLaw Q) :=
    ⟨measurable_project Q.ellipticity_parameter, rfl⟩
  have hlim := hp.quasiMeasurePreserving.ae (c6SourceRowDivergence_tested_heat_limit S)
  have hphys := (c6_actualSource_diagonalPairing_scaled Q i φ).and hlim
  have hred := (c6_measurePreserving_physicalOfReduced Q ω₀).quasiMeasurePreserving.ae hphys
  filter_upwards [hred, ae_map_reduce_mem_physicalImage Q] with ρ hρ hrange
  rcases hρ with ⟨hscale, htrace⟩
  rw [c6_reduce_physicalOfReduced ω₀ hrange] at hscale
  intro ψ hψ hψc j
  have h := (htrace (fun x => ψ (r₀ • x))
    (hψ.comp (continuous_const_smul r₀)) (hψc.comp_smul hr.ne') j).const_mul
      (r₀ ^ d / ellipticityScale L)
  change Tendsto _ _ (𝓝 (c6ReducedSourceTracePairing Q ω₀ S ψ j ρ)) at h
  apply h.congr'
  exact Eventually.of_forall fun mn => by
    dsimp only
    rw [hscale mn.1 mn.2 j]
    simp only [smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
    field_simp

/- The positive-window identities below adapt the corresponding stationary
heat lemmas without importing their unported v4.35 wrapper modules. -/
namespace C6TraceHeatSupport
variable {d : ℕ}

/-- Each mixed Gaussian Hessian is continuous at positive time. -/
theorem continuous_heatKernel_mixedHessian {d : ℕ} (t : ℝ) (ht : 0 < t)
    (i j : Fin d) :
    Continuous (coordinateDerivative j (coordinateDerivative i
      (euclideanHeatKernel (d := d) t))) := by
  have heq := funext (coordinateDerivative_two_euclideanHeatKernel t ht i j)
  rw [heq]
  exact ((contDiff_euclideanHeatKernel t).continuous).mul
    (((continuous_apply i).mul (continuous_apply j)).div_const _ |>.sub continuous_const)

/-- The two actual Hessian integrands are integrable along almost every
stationary orbit. -/
theorem ae_integrable_heatGradient_mixedHessian {d : ℕ}
    {Q : Measure (FieldPair d)} [IsProbabilityMeasure Q] (hQ : IsStationary Q)
    (F : FieldPair d → Vec d) (hF : Measurable F)
    (t : ℝ) (ht : 0 < t) (j k l : Fin d)
    (hKj : Integrable (coordinateDerivative l (coordinateDerivative j
      (euclideanHeatKernel (d := d) t))) volume)
    (hKk : Integrable (coordinateDerivative l (coordinateDerivative k
      (euclideanHeatKernel (d := d) t))) volume)
    (hFj : Integrable (fun ω => F ω j) Q)
    (hFk : Integrable (fun ω => F ω k) Q) :
    ∀ᵐ ρ ∂Q,
      Integrable (fun y : Vec d => F (translate y ρ) k *
        coordinateDerivative l (coordinateDerivative j
          (euclideanHeatKernel (d := d) t)) (-y)) volume ∧
      Integrable (fun y : Vec d => F (translate y ρ) j *
        coordinateDerivative l (coordinateDerivative k
          (euclideanHeatKernel (d := d) t)) (-y)) volume := by
  have hmj := (continuous_heatKernel_mixedHessian t ht j l).comp continuous_neg
  have hmk := (continuous_heatKernel_mixedHessian t ht k l).comp continuous_neg
  filter_upwards [ae_integrable_kernel_translate hQ hmj.measurable hKj.comp_neg
      ((measurable_pi_apply k).comp hF) hFk,
    ae_integrable_kernel_translate hQ hmk.measurable hKk.comp_neg
      ((measurable_pi_apply j).comp hF) hFj] with ρ hk hj
  exact ⟨by simpa only [Function.comp_apply, mul_comm] using hk,
    by simpa only [Function.comp_apply, mul_comm] using hj⟩

/-- The moment of the literal spatial heat integral is bounded by the
`L¹` masses of its mixed Hessians and the moments of the source coordinates.
No change of heat cutoff or interchange of time integrals is used here. -/
theorem eLpNorm_heatGradientSpaceIntegral_le {d : ℕ}
    {Q : Measure (FieldPair d)} [IsProbabilityMeasure Q] (hQ : IsStationary Q)
    (F : FieldPair d → Vec d) (hF : Measurable F)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ∞)
    (t : ℝ) (ht : 0 < t) (j k l : Fin d)
    (hKj : Integrable (coordinateDerivative l (coordinateDerivative j
      (euclideanHeatKernel (d := d) t))) volume)
    (hKk : Integrable (coordinateDerivative l (coordinateDerivative k
      (euclideanHeatKernel (d := d) t))) volume)
    (hFj : Integrable (fun ω => F ω j) Q)
    (hFk : Integrable (fun ω => F ω k) Q) :
    eLpNorm (fun ρ => akmHeatGradientSpaceIntegral
      (fun y => F (translate y ρ)) t j k l 0) p Q ≤
      ENNReal.ofReal (∫ y, |coordinateDerivative l (coordinateDerivative j
        (euclideanHeatKernel (d := d) t)) y|) * eLpNorm (fun ρ => F ρ k) p Q +
      ENNReal.ofReal (∫ y, |coordinateDerivative l (coordinateDerivative k
        (euclideanHeatKernel (d := d) t)) y|) * eLpNorm (fun ρ => F ρ j) p Q := by
  let Kj : Vec d → ℝ := fun y => coordinateDerivative l (coordinateDerivative j
    (euclideanHeatKernel (d := d) t)) (-y)
  let Kk : Vec d → ℝ := fun y => coordinateDerivative l (coordinateDerivative k
    (euclideanHeatKernel (d := d) t)) (-y)
  have hmj : Measurable Kj :=
    ((continuous_heatKernel_mixedHessian t ht j l).comp continuous_neg).measurable
  have hmk : Measurable Kk :=
    ((continuous_heatKernel_mixedHessian t ht k l).comp continuous_neg).measurable
  have hfjm := (measurable_pi_apply j).comp hF
  have hfkm := (measurable_pi_apply k).comp hF
  have heq : (fun ρ => akmHeatGradientSpaceIntegral
      (fun y => F (translate y ρ)) t j k l 0) =ᵐ[Q]
      (fun ρ => horizontalMollify Kj (fun ω => F ω k) ρ -
        horizontalMollify Kk (fun ω => F ω j) ρ) := by
    filter_upwards [ae_integrable_heatGradient_mixedHessian hQ F hF t ht j k l
      hKj hKk hFj hFk] with ρ hρ
    exact akmHeatGradientSpaceIntegral_eq_horizontalMollify F ρ t ht j k l hρ.1 hρ.2
  rw [eLpNorm_congr_ae heq]
  have hsub := eLpNorm_sub_le (μ := Q) (f := horizontalMollify Kj (fun ω => F ω k))
    (g := horizontalMollify Kk (fun ω => F ω j)) hp
  refine hsub.trans ?_
  have hbj := eLpNorm_horizontalMollify_le hQ hp hpt hmj hKj.comp_neg hfkm
  have hbk := eLpNorm_horizontalMollify_le hQ hp hpt hmk hKk.comp_neg hfjm
  have hIj : (∫ y, |Kj y|) = ∫ y, |coordinateDerivative l (coordinateDerivative j
      (euclideanHeatKernel (d := d) t)) y| :=
    integral_neg_eq_self (fun y : Vec d => |coordinateDerivative l (coordinateDerivative j
      (euclideanHeatKernel (d := d) t)) y|) volume
  have hIk : (∫ y, |Kk y|) = ∫ y, |coordinateDerivative l (coordinateDerivative k
      (euclideanHeatKernel (d := d) t)) y| :=
    integral_neg_eq_self (fun y : Vec d => |coordinateDerivative l (coordinateDerivative k
      (euclideanHeatKernel (d := d) t)) y|) volume
  rw [hIj] at hbj
  rw [hIk] at hbk
  exact add_le_add hbj hbk


/-- Coordinate moment bounds and mixed-Hessian masses give a quantitative
positive-time bound, before any cutoff limit is taken. -/
theorem eLpNorm_heatGradientSpaceIntegral_le_div {d : ℕ}
    {Q : Measure (FieldPair d)} [IsProbabilityMeasure Q] (hQ : IsStationary Q)
    (F : FieldPair d → Vec d) (hF : Measurable F)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ∞)
    (A C : ℝ) (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hFnorm : ∀ i, eLpNorm (fun ρ => F ρ i) p Q ≤ ENNReal.ofReal A)
    (t : ℝ) (ht : 0 < t) (j k l : Fin d)
    (hK : ∀ i, Integrable (coordinateDerivative l (coordinateDerivative i
      (euclideanHeatKernel (d := d) t))) volume ∧
      (∫ y, |coordinateDerivative l (coordinateDerivative i
        (euclideanHeatKernel (d := d) t)) y|) ≤ C / t) :
    eLpNorm (fun ρ => akmHeatGradientSpaceIntegral
      (fun y => F (translate y ρ)) t j k l 0) p Q ≤
      ENNReal.ofReal (2 * C * A / t) := by
  have hi (i : Fin d) : Integrable (fun ρ => F ρ i) Q := by
    have hmem : MemLp (fun ρ => F ρ i) p Q :=
      (hFnorm i).trans_lt ENNReal.ofReal_lt_top
    exact hmem.integrable hp
  apply (eLpNorm_heatGradientSpaceIntegral_le hQ F hF hp hpt t ht j k l
    (hK j).1 (hK k).1 (hi j) (hi k)).trans
  calc
    _ ≤ ENNReal.ofReal (C / t) * ENNReal.ofReal A +
        ENNReal.ofReal (C / t) * ENNReal.ofReal A :=
      add_le_add (mul_le_mul (ENNReal.ofReal_le_ofReal (hK j).2) (hFnorm k)
        zero_le zero_le)
        (mul_le_mul (ENNReal.ofReal_le_ofReal (hK k).2) (hFnorm j)
          zero_le zero_le)
    _ = ENNReal.ofReal (2 * C * A / t) := by
      rw [← ENNReal.ofReal_mul (div_nonneg hC ht.le),
        ← ENNReal.ofReal_add (mul_nonneg (div_nonneg hC ht.le) hA)
          (mul_nonneg (div_nonneg hC ht.le) hA)]
      congr 1
      ring


/-- Square-integrable stationary source coordinates give one finite
`C/t` bound before time and the three derivative indices. -/
theorem exists_stationary_heatGradient_L2_bound_of_unit {d : ℕ}
    {Q : Measure (FieldPair d)} [IsProbabilityMeasure Q] (hQ : IsStationary Q)
    (F : FieldPair d → Vec d) (hF : Measurable F)
    (hF2 : ∀ i, MemLp (fun ω => F ω i) 2 Q)
    (hunit : ∀ i j : Fin d, Integrable (coordinateDerivative j
      (coordinateDerivative i (euclideanHeatKernel (d := d) 1))) volume) :
    ∃ C : ℝ, 0 < C ∧ ∀ (j k l : Fin d) (t : ℝ), 0 < t → eLpNorm
      (fun ω => akmHeatGradientSpaceIntegral (fun y => F (translate y ω)) t j k l 0)
        2 Q ≤ ENNReal.ofReal (C / t) := by
  let A : ℝ := 1 + ∑ i, (eLpNorm (fun ω => F ω i) 2 Q).toReal
  have hA : 0 < A := by
    have : 0 ≤ ∑ i, (eLpNorm (fun ω => F ω i) 2 Q).toReal :=
      Finset.sum_nonneg (fun _ _ => ENNReal.toReal_nonneg)
    dsimp [A]
    linarith
  have hi (i : Fin d) : eLpNorm (fun ω => F ω i) 2 Q ≤ ENNReal.ofReal A := by
    rw [← ENNReal.ofReal_toReal (hF2 i).eLpNorm_ne_top]
    apply ENNReal.ofReal_le_ofReal
    have := Finset.single_le_sum
      (fun j (_ : j ∈ Finset.univ) =>
        ENNReal.toReal_nonneg (a := eLpNorm (fun ω => F ω j) 2 Q))
      (Finset.mem_univ i)
    dsimp [A]
    linarith
  obtain ⟨K, hK, hmass⟩ := heatKernel_mixedHessian_uniform_L1_of_unit hunit
  refine ⟨2 * K * A, by positivity, ?_⟩
  intro j k l t ht
  exact eLpNorm_heatGradientSpaceIntegral_le_div hQ F hF (by norm_num) (by norm_num)
    A K hA.le hK.le hi t ht j k l (fun i => hmass t ht i l)

/-- The Gaussian Hessian premise is discharged by its actual unit-time
integrability, leaving only the stationary source's L² membership. -/
theorem exists_stationary_heatGradient_L2_bound {d : ℕ}
    {Q : Measure (FieldPair d)} [IsProbabilityMeasure Q] (hQ : IsStationary Q)
    (F : FieldPair d → Vec d) (hF : Measurable F)
    (hF2 : ∀ i, MemLp (fun ω => F ω i) 2 Q) :
    ∃ C : ℝ, 0 < C ∧ ∀ (j k l : Fin d) (t : ℝ), 0 < t → eLpNorm
      (fun ω => akmHeatGradientSpaceIntegral (fun y => F (translate y ω)) t j k l 0)
        2 Q ≤ ENNReal.ofReal (C / t) :=
  exists_stationary_heatGradient_L2_bound_of_unit hQ F hF hF2
    integrable_unit_heatKernel_mixedHessian


/-- Translation covariance of a coordinate derivative: differentiating `z ↦ f (z - y)`
in direction `i` is differentiating `f` at `x - y`. -/
theorem coordinateDerivative_comp_sub_apply {d : ℕ} (f : Vec d → ℝ) (i : Fin d) (y x : Vec d) :
    coordinateDerivative i (fun z => f (z - y)) x = coordinateDerivative i f (x - y) := by
  unfold coordinateDerivative
  rw [fderiv_comp_sub]

/-- One integration by parts in a coordinate direction, moving the derivative off `g`
onto a compactly supported `C¹` factor `f`. -/
theorem integral_mul_coordinateDerivative_eq_neg {d : ℕ} {f g : Vec d → ℝ} {i : Fin d}
    (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f) (hg : ContDiff ℝ 1 g) :
    ∫ x, f x * coordinateDerivative i g x = -∫ x, coordinateDerivative i f x * g x := by
  unfold coordinateDerivative
  exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (integrable_mul_of_compact_support (continuous_fderiv_dir hf (unitVector i))
      (hfc.fderiv_apply ℝ (unitVector i)) hg.continuous)
    (integrable_mul_of_compact_support hf.continuous hfc (continuous_fderiv_dir hg (unitVector i)))
    (integrable_mul_of_compact_support hf.continuous hfc hg.continuous)
    (fun x _ => (hf.differentiable one_ne_zero).differentiableAt)
    (fun x _ => (hg.differentiable one_ne_zero).differentiableAt)

/-- `∫ ψ(x) ∂_l∂_jΦ_t(x - y) dx = (Φ_t ⋆ ∂_j∂_lψ)(y)` for smooth compactly supported
`ψ`. Source: AKM (6.7), `paper/main.tex:732-748`. -/
theorem integral_mul_heatHessian_eq_heatKernelConvolution {d : ℕ} {ψ : Vec d → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ) {t : ℝ} (ht : 0 < t)
    (j l : Fin d) (y : Vec d) :
    (∫ x, ψ x * coordinateDerivative l (coordinateDerivative j
      (euclideanHeatKernel (d := d) t)) (x - y)) =
      heatKernelConvolution t (coordinateDerivative j (coordinateDerivative l ψ)) y := by
  have hψ2 : ContDiff ℝ 2 ψ := hψ.of_le (by norm_cast)
  have hψ1 : ContDiff ℝ 1 ψ := hψ2.of_le one_le_two
  -- The translated kernel `φ(z) = Φ_t(z - y)` and its first coordinate derivative.
  have hφ2 : ContDiff ℝ 2 (fun z => euclideanHeatKernel (d := d) t (z - y)) :=
    (contDiff_two_euclideanHeatKernel t).comp (contDiff_id.sub contDiff_const)
  have hφ1 : ContDiff ℝ 1 (fun z => euclideanHeatKernel (d := d) t (z - y)) :=
    hφ2.of_le one_le_two
  have hjφ1 : ContDiff ℝ 1
      (coordinateDerivative j (fun z => euclideanHeatKernel (d := d) t (z - y))) :=
    contDiff_one_fderiv_dir hφ2 (unitVector j)
  have hlψ1 : ContDiff ℝ 1 (coordinateDerivative l ψ) :=
    contDiff_one_fderiv_dir hψ2 (unitVector l)
  have hlψc : HasCompactSupport (coordinateDerivative l ψ) :=
    hψc.fderiv_apply ℝ (unitVector l)
  -- Move the translation through the coordinate derivative.
  have hF : coordinateDerivative j (fun z => euclideanHeatKernel (d := d) t (z - y)) =
      fun z => coordinateDerivative j (euclideanHeatKernel (d := d) t) (z - y) :=
    funext fun z => coordinateDerivative_comp_sub_apply (euclideanHeatKernel (d := d) t) j y z
  have hF2 : ∀ x, coordinateDerivative l
      (coordinateDerivative j (fun z => euclideanHeatKernel (d := d) t (z - y))) x =
      coordinateDerivative l (coordinateDerivative j (euclideanHeatKernel (d := d) t))
        (x - y) := by
    intro x
    rw [hF]
    exact coordinateDerivative_comp_sub_apply (coordinateDerivative j
      (euclideanHeatKernel (d := d) t)) l y x
  -- Two integrations by parts: first in direction `l` against `ψ`, then in `j`.
  have h1 := integral_mul_coordinateDerivative_eq_neg (f := ψ) (i := l) hψ1 hψc hjφ1
  have h2 := integral_mul_coordinateDerivative_eq_neg (f := coordinateDerivative l ψ) (i := j)
    hlψ1 hlψc hφ1
  rw [heatKernelConvolution, if_neg ht.ne']
  have hL : (fun x => ψ x * coordinateDerivative l
      (coordinateDerivative j (euclideanHeatKernel (d := d) t)) (x - y)) =
      fun x => ψ x * coordinateDerivative l
        (coordinateDerivative j (fun z => euclideanHeatKernel (d := d) t (z - y))) x :=
    funext fun x => by rw [hF2 x]
  rw [hL, h1, h2, neg_neg]

/-- The heat-kernel Hessian at time `t`, reflected. -/
def reflectedHeatHessian (t : ℝ) (j l : Fin d) (y : Vec d) : ℝ :=
  coordinateDerivative l (coordinateDerivative j (euclideanHeatKernel (d := d) t)) (-y)

theorem contDiff_coordinateDerivative' {f : Vec d → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (i : Fin d) : ContDiff ℝ (⊤ : ℕ∞) (coordinateDerivative i f) := by
  show ContDiff ℝ (⊤ : ℕ∞) (fun x => fderiv ℝ f x (unitVector i))
  exact ((contDiff_infty_iff_fderiv.mp hf).2).clm_apply contDiff_const

theorem hasCompactSupport_coordinateDerivative' {f : Vec d → ℝ} (hf : HasCompactSupport f)
    (i : Fin d) : HasCompactSupport (coordinateDerivative i f) := by
  change HasCompactSupport (fun x => fderiv ℝ f x (unitVector i))
  exact hf.fderiv_apply ℝ (unitVector i)

theorem continuous_reflectedHeatHessian (t : ℝ) (j l : Fin d) :
    Continuous (reflectedHeatHessian (d := d) t j l) :=
  ((contDiff_coordinateDerivative' (contDiff_coordinateDerivative'
    (contDiff_euclideanHeatKernel t) j) l).continuous).comp continuous_neg

theorem integrable_reflectedHeatHessian {t : ℝ} (ht : 0 < t) (j l : Fin d) :
    Integrable (reflectedHeatHessian (d := d) t j l) volume := by
  obtain ⟨C, -, hC⟩ := heatKernel_mixedHessian_uniform_L1_of_unit
    (integrable_unit_heatKernel_mixedHessian (d := d))
  exact (hC t ht j l).1.comp_neg

/-- Convolution against a kernel respects almost-sure equality of stationary
observables. -/
theorem horizontalMollify_congr_ae {Q : Measure (FieldPair d)} [IsProbabilityMeasure Q]
    (hQ : IsStationary Q) {K : Vec d → ℝ} {f f' : FieldPair d → ℝ} (hf : Measurable f)
    (hf' : Measurable f') (h : f =ᵐ[Q] f') :
    horizontalMollify K f =ᵐ[Q] horizontalMollify K f' := by
  filter_upwards [Entropy.ae_ae_translate_eq hQ hf hf' h] with ρ hρ
  unfold horizontalMollify
  exact integral_congr_ae (hρ.mono fun x hx => by simp only [hx])

/-- Pairing the spatial heat integral at a fixed positive time with a smooth
compactly supported test: both derivatives move onto the test, and the heat
kernel onto the source. -/
theorem ae_horizontalMollify_heatSpaceIntegral_eq (Q : Measure (FieldPair d))
    [IsProbabilityMeasure Q] (hQ : IsStationary Q) {g : FieldPair d → Vec d}
    (hg : Measurable g) (hgi : ∀ k, Integrable (fun ω => g ω k) Q)
    {ψ : Vec d → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ)
    {t : ℝ} (ht : 0 < t) (j k l : Fin d) :
    horizontalMollify ψ
        (fun ω => akmHeatGradientSpaceIntegral (fun y => g (translate y ω)) t j k l 0) =ᵐ[Q]
      fun ρ => horizontalMollify (coordinateDerivative j (coordinateDerivative l ψ))
          (heatSmoothed t (fun ω => g ω k)) ρ -
        horizontalMollify (coordinateDerivative k (coordinateDerivative l ψ))
          (heatSmoothed t (fun ω => g ω j)) ρ := by
  have hgk (i : Fin d) : Measurable (fun ω => g ω i) := (measurable_pi_apply i).comp hg
  have hKm (a b : Fin d) : Measurable (reflectedHeatHessian (d := d) t a b) :=
    (continuous_reflectedHeatHessian t a b).measurable
  have hKi (a b : Fin d) := integrable_reflectedHeatHessian (d := d) ht a b
  have hψm : Measurable ψ := hψ.continuous.measurable
  have hψi : Integrable ψ volume := hψ.continuous.integrable_of_hasCompactSupport hψc
  -- the spatial heat integral as a difference of two convolutions
  have hS : (fun ω => akmHeatGradientSpaceIntegral (fun y => g (translate y ω)) t j k l 0)
      =ᵐ[Q] fun ω => horizontalMollify (reflectedHeatHessian t j l) (fun ω => g ω k) ω -
        horizontalMollify (reflectedHeatHessian t k l) (fun ω => g ω j) ω := by
    filter_upwards [ae_integrable_kernel_translate hQ (hKm j l) (hKi j l) (hgk k) (hgi k),
      ae_integrable_kernel_translate hQ (hKm k l) (hKi k l) (hgk j) (hgi j)] with ω h1 h2
    exact akmHeatGradientSpaceIntegral_eq_horizontalMollify g ω t ht j k l
      (by simpa only [reflectedHeatHessian, mul_comm] using h1)
      (by simpa only [reflectedHeatHessian, mul_comm] using h2)
  have hSm : Measurable
      (fun ω => akmHeatGradientSpaceIntegral (fun y => g (translate y ω)) t j k l 0) :=
    (measurable_actualHeatGradientSpaceIntegral_stationary g hg j k l).comp
      ((measurable_id.prodMk measurable_const).prodMk measurable_const)
  have hconv (a b c : Fin d) :
      MemLp (horizontalMollify (reflectedHeatHessian t a b) (fun ω => g ω c))
        (ENNReal.ofReal 1) Q := by
    have hn : eLpNorm (fun ω => g ω c) (ENNReal.ofReal 1) Q ≤
        ENNReal.ofReal (eLpNorm (fun ω => g ω c) 1 Q).toReal := by
      rw [ENNReal.ofReal_one, ENNReal.ofReal_toReal
        (memLp_one_iff_integrable.mpr (hgi c)).eLpNorm_ne_top]
    exact (horizontalMollify_moment_le Q hQ le_rfl ENNReal.toReal_nonneg (hKm a b) (hKi a b)
      (hgk c) hn).2.1
  have hconvi (a b c : Fin d) :
      Integrable (horizontalMollify (reflectedHeatHessian t a b) (fun ω => g ω c)) Q := by
    simpa only [ENNReal.ofReal_one, memLp_one_iff_integrable] using hconv a b c
  have hconvm (a b c : Fin d) :
      Measurable (horizontalMollify (reflectedHeatHessian t a b) (fun ω => g ω c)) :=
    measurable_horizontalMollify _ (hKm a b) (hgk c)
  -- the composite kernel is the heat smoothing of the second derivatives of the test
  have hker (a b : Fin d) : (fun y => ∫ x, ψ x * reflectedHeatHessian t a b (y - x)) =
      heatKernelConvolution t (coordinateDerivative a (coordinateDerivative b ψ)) := by
    funext y
    rw [← integral_mul_heatHessian_eq_heatKernelConvolution hψ hψc ht a b y]
    simp only [reflectedHeatHessian, neg_sub]
  have hcomp (a b c : Fin d) :
      horizontalMollify ψ (horizontalMollify (reflectedHeatHessian t a b) (fun ω => g ω c))
        =ᵐ[Q] horizontalMollify (coordinateDerivative a (coordinateDerivative b ψ))
          (heatSmoothed t (fun ω => g ω c)) := by
    have hD : ContDiff ℝ (⊤ : ℕ∞) (coordinateDerivative a (coordinateDerivative b ψ)) :=
      contDiff_coordinateDerivative' (contDiff_coordinateDerivative' hψ b) a
    have hDc : HasCompactSupport (coordinateDerivative a (coordinateDerivative b ψ)) :=
      hasCompactSupport_coordinateDerivative' (hasCompactSupport_coordinateDerivative' hψc b) a
    filter_upwards [horizontalMollify_comp_ae Q hQ hψm hψi (hKm a b) (hKi a b) (hgk c) (hgi c),
      horizontalMollify_heatSmoothed_ae Q hQ hD.continuous.measurable
        (hD.continuous.integrable_of_hasCompactSupport hDc) (hgk c) (hgi c) ht.le]
      with ρ h1 h2
    rw [h1, hker, h2]
  filter_upwards [horizontalMollify_congr_ae hQ hSm
      ((hconvm j l k).sub (hconvm k l j)) hS,
    horizontalMollify_sub_ae hQ hψm hψi (hconvm j l k) (hconvi j l k) (hconvm k l j)
      (hconvi k l j), hcomp j l k, hcomp k l j] with ρ h1 h2 h3 h4
  rw [h1]
  simp only [Pi.sub_def]
  rw [h2, h3, h4]

/-- Joint measurability of the spatial heat integral at the origin of the orbit. -/
theorem measurable_heatSpaceIntegral_origin {g : FieldPair d → Vec d} (hg : Measurable g)
    (j k l : Fin d) :
    Measurable (fun p : ℝ × FieldPair d =>
      akmHeatGradientSpaceIntegral (fun y => g (translate y p.2)) p.1 j k l 0) :=
  (measurable_actualHeatGradientSpaceIntegral_stationary g hg j k l).comp
    ((measurable_snd.prodMk measurable_fst).prodMk measurable_const)



/-- The actual heat-gradient integral over an arbitrary finite time window. -/
def heatWindowGradient (g : Vec d → Vec d) (a b : ℝ) (j k l : Fin d) (x : Vec d) : ℝ :=
  ∫ t in Icc a b, akmHeatGradientSpaceIntegral g t j k l x


/-- Pairing a truncation with a test exchanges with the time integral, for almost
every environment. Integrability follows from the stationary `C/t` moment bound. -/
theorem heatWindowGradient_translate (g : FieldPair d → Vec d) (a b : ℝ)
    (j k l : Fin d) (ρ : FieldPair d) (x : Vec d) :
    heatWindowGradient (fun y => g (translate y (translate x ρ))) a b j k l 0 =
      heatWindowGradient (fun y => g (translate y ρ)) a b j k l x := by
  unfold heatWindowGradient
  apply integral_congr_ae
  exact ae_of_all _ fun t => by
    have h := akmHeatGradientSpaceIntegral_translation (fun y => g (translate y ρ))
      x t j k l 0
    simpa only [zero_add, translate_add] using h

theorem ae_integrable_horizontalMollify_window_eq_setIntegral (Q : Measure (FieldPair d))
    [IsProbabilityMeasure Q] (hQ : IsStationary Q) {g : FieldPair d → Vec d}
    (hg : Measurable g) (hg2 : ∀ k, MemLp (fun ω => g ω k) 2 Q)
    {ψ : Vec d → ℝ} (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) (a b : ℝ) (ha : 0 < a)
    (j k l : Fin d) :
    ∀ᵐ ρ ∂Q, Integrable (fun x => ψ x *
        heatWindowGradient (fun y => g (translate y ρ)) a b j k l x) volume ∧
      horizontalMollify ψ
        (fun ω => heatWindowGradient (fun y => g (translate y ω)) a b j k l 0) ρ = ∫ t in Icc a b, horizontalMollify ψ
        (fun ω => akmHeatGradientSpaceIntegral (fun y => g (translate y ω)) t j k l 0) ρ := by
  set ν : Measure ℝ := volume.restrict (Icc a b) with hνdef
  haveI : IsFiniteMeasure ν := isFiniteMeasure_restrict.mpr (by
    simp [Real.volume_Icc])
  set S : ℝ → FieldPair d → ℝ := fun t ω =>
    akmHeatGradientSpaceIntegral (fun y => g (translate y ω)) t j k l 0 with hSdef
  have hSm : Measurable (fun p : ℝ × FieldPair d => S p.1 p.2) :=
    measurable_heatSpaceIntegral_origin hg j k l
  obtain ⟨C, hC, hbound⟩ := exists_stationary_heatGradient_L2_bound hQ g hg hg2
  -- integrable joint integrand on `(space × time) × environment`
  let Φ : (Vec d × ℝ) × FieldPair d → ℝ := fun q => ψ q.1.1 * S q.1.2 (translate q.1.1 q.2)
  have hΦm : Measurable Φ :=
    (hψ.measurable.comp (measurable_fst.comp measurable_fst)).mul
      (hSm.comp ((measurable_snd.comp measurable_fst).prodMk
        (Probability.continuous_translate.measurable.comp
          ((measurable_fst.comp measurable_fst).prodMk measurable_snd))))
  have hS1 (t : ℝ) (ht : 0 < t) : Integrable (S t) Q := by
    have h2 : MemLp (S t) 2 Q :=
      (hbound j k l t ht).trans_lt ENNReal.ofReal_lt_top
    exact h2.integrable one_le_two
  have hS1norm (t : ℝ) (ht : 0 < t) : (∫ ω, ‖S t ω‖ ∂Q) ≤ C / t := by
    have h2 : MemLp (S t) 2 Q :=
      (hbound j k l t ht).trans_lt ENNReal.ofReal_lt_top
    have hle : eLpNorm (S t) 1 Q ≤ eLpNorm (S t) 2 Q :=
      eLpNorm_le_eLpNorm_of_exponent_le one_le_two
    rw [integral_norm_eq_lintegral_enorm h2.aestronglyMeasurable, ← eLpNorm_one_eq_lintegral_enorm h2.aestronglyMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal (div_pos hC ht).le (hle.trans (hbound j k l t ht))
  have hΦi : Integrable Φ (((volume : Measure (Vec d)).prod ν).prod Q) := by
    refine (integrable_prod_iff hΦm.aestronglyMeasurable).2 ⟨?_, ?_⟩
    · have hmem : ∀ᵐ p ∂((volume : Measure (Vec d)).prod ν), p.2 ∈ Icc a b := by
        have := (ae_restrict_mem (μ := (volume : Measure ℝ))
          (measurableSet_Icc : MeasurableSet (Icc a b)))
        exact (Measure.quasiMeasurePreserving_snd (μ := (volume : Measure (Vec d)))
          (ν := ν)).ae this
      filter_upwards [hmem] with p hp
      exact ((measurePreserving_translate Q hQ p.1).integrable_comp_of_integrable
        (hS1 p.2 (ha.trans_le hp.1))).const_mul (ψ p.1)
    · have hψi : Integrable ψ volume := hψ.integrable_of_hasCompactSupport hψc
      have hdom : Integrable (fun p : Vec d × ℝ => |ψ p.1| * (C / a))
          ((volume : Measure (Vec d)).prod ν) :=
        (hψi.abs.mul_const _).comp_fst ν
      refine hdom.mono' (hΦm.norm.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable) ?_
      have hmem : ∀ᵐ p ∂((volume : Measure (Vec d)).prod ν), p.2 ∈ Icc a b :=
        (Measure.quasiMeasurePreserving_snd (μ := (volume : Measure (Vec d))) (ν := ν)).ae
          (ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Icc)
      filter_upwards [hmem] with p hp
      have htpos := ha.trans_le hp.1
      have heq : (∫ ω, ‖Φ (p, ω)‖ ∂Q) = |ψ p.1| * ∫ ω, ‖S p.2 ω‖ ∂Q := by
        simp only [Φ, norm_mul, Real.norm_eq_abs, integral_const_mul]
        congr 1
        exact Probability.integral_translate Q hQ p.1 (fun ω => ‖S p.2 ω‖)
          (hSm.comp (measurable_const.prodMk measurable_id)).norm
      rw [Real.norm_of_nonneg (integral_nonneg fun ω => norm_nonneg _), heq]
      refine mul_le_mul_of_nonneg_left ((hS1norm p.2 htpos).trans ?_) (abs_nonneg _)
      exact div_le_div_of_nonneg_left hC.le ha hp.1
  filter_upwards [hΦi.prod_left_ae] with ρ hρ
  have hρ' : Integrable (Function.uncurry fun (x : Vec d) (t : ℝ) =>
      ψ x * S t (translate x ρ)) ((volume : Measure (Vec d)).prod ν) := hρ
  refine ⟨?_, ?_⟩
  · have hi := hρ'.integral_prod_left
    change Integrable (fun x => ∫ t, ψ x * S t (translate x ρ) ∂ν) volume at hi
    simp_rw [integral_const_mul] at hi
    change Integrable (fun x => ψ x *
      heatWindowGradient (fun y => g (translate y (translate x ρ))) a b j k l 0) volume at hi
    simpa only [heatWindowGradient_translate] using hi
  · change (∫ x, ψ x * ∫ t, S t (translate x ρ) ∂ν) =
      ∫ t, (∫ x, ψ x * S t (translate x ρ)) ∂ν
    simp_rw [← integral_const_mul]
    exact integral_integral_swap hρ'

/-- Spatial testing commutes with a finite positive time window. -/
theorem ae_horizontalMollify_window_eq_setIntegral (Q : Measure (FieldPair d))
    [IsProbabilityMeasure Q] (hQ : IsStationary Q) {g : FieldPair d → Vec d}
    (hg : Measurable g) (hg2 : ∀ k, MemLp (fun ω => g ω k) 2 Q)
    {ψ : Vec d → ℝ} (hψ : Continuous ψ) (hψc : HasCompactSupport ψ)
    (a b : ℝ) (ha : 0 < a) (j k l : Fin d) :
    horizontalMollify ψ
        (fun ω => heatWindowGradient (fun y => g (translate y ω)) a b j k l 0)
      =ᵐ[Q] fun ρ => ∫ t in Icc a b, horizontalMollify ψ
        (fun ω => akmHeatGradientSpaceIntegral (fun y => g (translate y ω)) t j k l 0) ρ :=
  (ae_integrable_horizontalMollify_window_eq_setIntegral Q hQ hg hg2 hψ hψc a b ha j k l).mono
    fun _ h => h.2

/-- AKM (6.7) along the orbit is the time integral of horizontal convolutions of the
heat-smoothed source with second derivatives of the test.
Source: AKM Lemma 6.1, Step 4, `paper/main.tex:732-748`. -/
theorem ae_horizontalMollify_window_eq (Q : Measure (FieldPair d))
    [IsProbabilityMeasure Q] (hQ : IsStationary Q) {g : FieldPair d → Vec d}
    (hg : Measurable g) (hg2 : ∀ k, MemLp (fun ω => g ω k) 2 Q)
    {ψ : Vec d → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ) (a b : ℝ) (ha : 0 < a)
    (j k l : Fin d) :
    horizontalMollify ψ
        (fun ω => heatWindowGradient (fun y => g (translate y ω)) a b j k l 0)
      =ᵐ[Q] fun ρ => ∫ t in Icc a b,
        (horizontalMollify (coordinateDerivative j (coordinateDerivative l ψ))
            (heatSmoothed t (fun ω => g ω k)) ρ -
          horizontalMollify (coordinateDerivative k (coordinateDerivative l ψ))
            (heatSmoothed t (fun ω => g ω j)) ρ) := by
  have hgi (i : Fin d) : Integrable (fun ω => g ω i) Q := (hg2 i).integrable one_le_two
  have hgk (i : Fin d) : Measurable (fun ω => g ω i) := (measurable_pi_apply i).comp hg
  have hSm := measurable_heatSpaceIntegral_origin hg j k l
  have hD (a b : Fin d) : Measurable (coordinateDerivative a (coordinateDerivative b ψ)) :=
    (contDiff_coordinateDerivative' (contDiff_coordinateDerivative' hψ b) a).continuous.measurable
  have hL : Measurable (fun p : ℝ × FieldPair d => horizontalMollify ψ
      (fun ω => akmHeatGradientSpaceIntegral (fun y => g (translate y ω)) p.1 j k l 0) p.2) := by
    have h : Measurable (fun q : (ℝ × FieldPair d) × Vec d => ψ q.2 *
        akmHeatGradientSpaceIntegral (fun y => g (translate y (translate q.2 q.1.2)))
          q.1.1 j k l 0) :=
      (hψ.continuous.measurable.comp measurable_snd).mul (hSm.comp
        ((measurable_fst.comp measurable_fst).prodMk
          (Probability.continuous_translate.measurable.comp
            (measurable_snd.prodMk (measurable_snd.comp measurable_fst)))))
    exact h.stronglyMeasurable.integral_prod_right'.measurable
  have hR : Measurable (fun p : ℝ × FieldPair d =>
      horizontalMollify (coordinateDerivative j (coordinateDerivative l ψ))
          (heatSmoothed p.1 (fun ω => g ω k)) p.2 -
        horizontalMollify (coordinateDerivative k (coordinateDerivative l ψ))
          (heatSmoothed p.1 (fun ω => g ω j)) p.2) :=
    (measurable_horizontalMollify_heatSmoothed_joint (hD j l) (hgk k)).sub
      (measurable_horizontalMollify_heatSmoothed_joint (hD k l) (hgk j))
  have htime : ∀ᵐ t ∂(volume.restrict (Icc a b)), ∀ᵐ ρ ∂Q,
      horizontalMollify ψ
          (fun ω => akmHeatGradientSpaceIntegral (fun y => g (translate y ω)) t j k l 0) ρ =
        (horizontalMollify (coordinateDerivative j (coordinateDerivative l ψ))
            (heatSmoothed t (fun ω => g ω k)) ρ -
          horizontalMollify (coordinateDerivative k (coordinateDerivative l ψ))
            (heatSmoothed t (fun ω => g ω j)) ρ) := by
    refine (ae_restrict_iff' (measurableSet_Icc)).mpr (ae_of_all _ fun t ht => ?_)
    exact ae_horizontalMollify_heatSpaceIntegral_eq Q hQ hg hgi hψ hψc
      (ha.trans_le ht.1) j k l
  have hswap := (Measure.ae_ae_comm (μ := volume.restrict (Icc a b)) (ν := Q)
    (measurableSet_eq_fun hL hR)).mp htime
  filter_upwards [ae_horizontalMollify_window_eq_setIntegral Q hQ hg hg2 hψ.continuous hψc
    a b ha j k l, hswap] with ρ h1 h2
  rw [h1]
  exact integral_congr_ae h2


/-- The heat-transfer identity on a positive window. Source: AKM Lemma 6.1, Step 4. -/
theorem ae_setIntegral_horizontalMollify_laplacian_heatSmoothed {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q] (hQ : IsStationary Q)
    {K : Vec d → ℝ} (hK : ContDiff ℝ 2 K) (hKc : HasCompactSupport K)
    {f : FieldPair d → ℝ} (hf : Measurable f) (hfi : Integrable f Q)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    ∀ᵐ ω ∂Q, IntegrableOn
        (fun t => horizontalMollify (coordLaplacian K) (heatSmoothed t f) ω) (Set.Icc a b) ∧
      (∫ t in Set.Icc a b, horizontalMollify (coordLaplacian K) (heatSmoothed t f) ω) =
        horizontalMollify K (heatSmoothed b f) ω - horizontalMollify K (heatSmoothed a f) ω := by
  have hb : 0 ≤ b := ha.trans hab
  have hL : Measurable (coordLaplacian K) := (continuous_coordLaplacian hK).measurable
  have hLi : Integrable (coordLaplacian K) := integrable_coordLaplacian hK hKc
  filter_upwards [horizontalMollify_heat_transfer Q hQ hK hKc hf hfi ha,
    horizontalMollify_heat_transfer Q hQ hK hKc hf hfi hb,
    ae_intervalIntegrable_horizontalMollify_heatSmoothed Q hQ hL hLi hf hfi hb]
    with ω hTa hTb hint
  have hsub : Set.uIcc 0 a ⊆ Set.uIcc 0 b := by
    rw [Set.uIcc_of_le ha, Set.uIcc_of_le hb]
    exact Set.Icc_subset_Icc le_rfl hab
  have hint0a := hint.mono_set hsub
  have hintab : IntervalIntegrable (fun t => horizontalMollify (coordLaplacian K)
      (heatSmoothed t f) ω) volume a b := by
    refine hint.mono_set ?_
    rw [Set.uIcc_of_le hab, Set.uIcc_of_le hb]
    exact Set.Icc_subset_Icc ha le_rfl
  have hOn : IntegrableOn (fun t => horizontalMollify (coordLaplacian K)
      (heatSmoothed t f) ω) (Set.Icc a b) :=
    (integrableOn_Icc_iff_integrableOn_Ioc (μ := volume)).mpr
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp hintab)
  refine ⟨hOn, ?_⟩
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab,
    ← intervalIntegral.integral_interval_sub_left hint hint0a]
  unfold heatTransferExpression at hTa hTb
  linarith

theorem coordLaplacian_eq_sum (ψ : Vec d → ℝ) :
    coordLaplacian ψ = fun x => ∑ k : Fin d,
      coordinateDerivative k (coordinateDerivative k ψ) x := rfl

/-- Row divergence of the tested truncations along almost every orbit. -/
theorem ae_sum_horizontalMollify_window_diag (Q : Measure (FieldPair d))
    [IsProbabilityMeasure Q] (hQ : IsStationary Q) {g : FieldPair d → Vec d}
    (hg : Measurable g) (hg2 : ∀ k, MemLp (fun ω => g ω k) 2 Q)
    (hdiv : ∀ᵐ ρ ∂Q, HasWeakDivergence Set.univ (fun x => g (translate x ρ)) (fun _ => 0))
    {ψ : Vec d → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ) (a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (j : Fin d) :
    ∀ᵐ ρ ∂Q, (∑ k : Fin d, horizontalMollify ψ (fun ω =>
        heatWindowGradient (fun y => g (translate y ω)) a b j k k 0) ρ) =
      horizontalMollify ψ (heatSmoothed a (fun ω => g ω j)) ρ -
        horizontalMollify ψ (heatSmoothed b (fun ω => g ω j)) ρ := by
  have hb : 0 ≤ b := ha.le.trans hab
  set ν : Measure ℝ := volume.restrict (Icc a b) with hνdef
  have hgi (i : Fin d) : Integrable (fun ω => g ω i) Q := (hg2 i).integrable one_le_two
  have hgk (i : Fin d) : Measurable (fun ω => g ω i) := (measurable_pi_apply i).comp hg
  have hDD (p q : Fin d) :
      ContDiff ℝ (⊤ : ℕ∞) (coordinateDerivative p (coordinateDerivative q ψ)) :=
    contDiff_coordinateDerivative' (contDiff_coordinateDerivative' hψ q) p
  have hDDc (p q : Fin d) : HasCompactSupport (coordinateDerivative p (coordinateDerivative q ψ)) :=
    hasCompactSupport_coordinateDerivative' (hasCompactSupport_coordinateDerivative' hψc q) p
  have hDDm (p q : Fin d) := (hDD p q).continuous.measurable
  have hDDi (p q : Fin d) : Integrable (coordinateDerivative p (coordinateDerivative q ψ)) volume :=
    (hDD p q).continuous.integrable_of_hasCompactSupport (hDDc p q)
  -- time integrability of every term on the window
  have hwin : Icc a b ⊆ Set.Ioc 0 b := fun t ht => ⟨lt_of_lt_of_le ha ht.1, ht.2⟩
  have htimeInt (p q i : Fin d) : ∀ᵐ ρ ∂Q, Integrable (fun t =>
      horizontalMollify (coordinateDerivative p (coordinateDerivative q ψ))
        (heatSmoothed t (fun ω => g ω i)) ρ) ν := by
    filter_upwards [ae_intervalIntegrable_horizontalMollify_heatSmoothed Q hQ (hDDm p q)
      (hDDi p q) (hgk i) (hgi i) hb] with ρ hρ
    exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le hb).mp hρ).mono_set hwin
  -- the divergence term vanishes for almost every time
  have hjoint (p q i : Fin d) : Measurable (fun z : ℝ × FieldPair d =>
      horizontalMollify (coordinateDerivative p (coordinateDerivative q ψ))
        (heatSmoothed z.1 (fun ω => g ω i)) z.2) :=
    measurable_horizontalMollify_heatSmoothed_joint (hDDm p q) (hgk i)
  have hdivTime : ∀ᵐ ρ ∂Q, ∀ᵐ t ∂ν, (∑ k : Fin d,
      horizontalMollify (coordinateDerivative j (coordinateDerivative k ψ))
        (heatSmoothed t (fun ω => g ω k)) ρ) = 0 := by
    have hset : MeasurableSet {z : ℝ × FieldPair d | (∑ k : Fin d,
        horizontalMollify (coordinateDerivative j (coordinateDerivative k ψ))
          (heatSmoothed z.1 (fun ω => g ω k)) z.2) = 0} :=
      measurableSet_eq_fun (Finset.measurable_sum _ fun k _ => hjoint j k k) measurable_const
    refine (Measure.ae_ae_comm (μ := ν) (ν := Q) hset).mp ?_
    refine (ae_restrict_iff' (measurableSet_Icc)).mpr (ae_of_all _ fun t ht => ?_)
    have h := ae_sum_horizontalMollify_heatSmoothed_divergence_eq_zero Q hQ hg hgi hdiv
      (contDiff_coordinateDerivative' hψ j) (hasCompactSupport_coordinateDerivative' hψc j)
      (ha.trans_le ht.1).le
    filter_upwards [h] with ρ hρ
    simpa only [coordinateDerivative_comm hψ j] using hρ
  -- the Laplacian term
  have hlapTime : ∀ᵐ ρ ∂Q, ∀ᵐ t ∂ν, (∑ k : Fin d,
      horizontalMollify (coordinateDerivative k (coordinateDerivative k ψ))
        (heatSmoothed t (fun ω => g ω j)) ρ) =
        horizontalMollify (coordLaplacian ψ) (heatSmoothed t (fun ω => g ω j)) ρ := by
    have hset : MeasurableSet {z : ℝ × FieldPair d | (∑ k : Fin d,
        horizontalMollify (coordinateDerivative k (coordinateDerivative k ψ))
          (heatSmoothed z.1 (fun ω => g ω j)) z.2) =
        horizontalMollify (coordLaplacian ψ) (heatSmoothed z.1 (fun ω => g ω j)) z.2} :=
      measurableSet_eq_fun (Finset.measurable_sum _ fun k _ => hjoint k k j)
        (measurable_horizontalMollify_heatSmoothed_joint
          (continuous_coordLaplacian (hψ.of_le (by norm_cast))).measurable (hgk j))
    refine (Measure.ae_ae_comm (μ := ν) (ν := Q) hset).mp ?_
    refine (ae_restrict_iff' (measurableSet_Icc)).mpr (ae_of_all _ fun t ht => ?_)
    have hHt : Measurable (heatSmoothed t (fun ω => g ω j)) :=
      (measurable_heatSmoothed_joint (hgk j)).comp (measurable_const.prodMk measurable_id)
    have hHti : Integrable (heatSmoothed t (fun ω => g ω j)) Q := by
      have h := eLpNorm_heatSmoothed_le Q hQ le_rfl (hgk j) (ha.trans_le ht.1).le
      rw [ENNReal.ofReal_one] at h
      exact memLp_one_iff_integrable.mp
        (h.trans_lt (memLp_one_iff_integrable.mpr (hgi j)).eLpNorm_lt_top)
    have h := horizontalMollify_sum_kernel_ae hQ Finset.univ (fun k => hDDm k k)
      (fun k => hDDi k k) hHt hHti
    filter_upwards [h] with ρ hρ
    rw [coordLaplacian_eq_sum, hρ]
  filter_upwards [ae_all_iff.mpr fun k => ae_horizontalMollify_window_eq Q hQ hg hg2 hψ hψc
      a b ha j k k, ae_all_iff.mpr fun k => htimeInt j k k, ae_all_iff.mpr fun k => htimeInt k k j,
    hdivTime, hlapTime, ae_setIntegral_horizontalMollify_laplacian_heatSmoothed Q hQ
      (hψ.of_le (by norm_cast)) hψc (hgk j) (hgi j) ha.le hab]
    with ρ hT hA hB hdivρ hlapρ hwinρ
  simp_rw [hT]
  have hsum := integral_finsetSum (μ := ν) Finset.univ fun k _ => (hA k).sub (hB k)
  simp only [Pi.sub_apply] at hsum
  rw [← hsum]
  have hcongr : (fun t => ∑ k : Fin d,
      (horizontalMollify (coordinateDerivative j (coordinateDerivative k ψ))
          (heatSmoothed t (fun ω => g ω k)) ρ -
        horizontalMollify (coordinateDerivative k (coordinateDerivative k ψ))
          (heatSmoothed t (fun ω => g ω j)) ρ)) =ᵐ[ν]
      fun t => -horizontalMollify (coordLaplacian ψ) (heatSmoothed t (fun ω => g ω j)) ρ := by
    filter_upwards [hdivρ, hlapρ] with t h1 h2
    rw [Finset.sum_sub_distrib, h1, h2, zero_sub]
  rw [integral_congr_ae hcongr, integral_neg]
  have hw := hwinρ.2
  change (∫ t in Icc a b, _) = _ at hw
  rw [hw]
  ring



/-- The tested diagonal formula on an arbitrary positive time window. All
integrability needed to move the finite column sum is proved from stationarity. -/
theorem ae_testPairing_window_diag (Q : Measure (FieldPair d))
    [IsProbabilityMeasure Q] (hQ : IsStationary Q) {g : FieldPair d → Vec d}
    (hg : Measurable g) (hg2 : ∀ k, MemLp (fun ω => g ω k) 2 Q)
    (hdiv : ∀ᵐ ρ ∂Q, HasWeakDivergence Set.univ (fun x => g (translate x ρ)) (fun _ => 0))
    {ψ : Vec d → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ)
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (j : Fin d) :
    ∀ᵐ ρ ∂Q, (∫ x, (∑ k : Fin d,
        heatWindowGradient (fun y => g (translate y ρ)) a b j k k x) * ψ x) =
      horizontalMollify ψ (heatSmoothed a (fun ω => g ω j)) ρ -
        horizontalMollify ψ (heatSmoothed b (fun ω => g ω j)) ρ := by
  filter_upwards [ae_sum_horizontalMollify_window_diag Q hQ hg hg2 hdiv hψ hψc a b ha hab j,
    ae_all_iff.mpr fun k => ae_integrable_horizontalMollify_window_eq_setIntegral
      Q hQ hg hg2 hψ.continuous hψc a b ha j k k] with ρ hdiag hi
  rw [← hdiag]
  calc
    _ = ∫ x, ∑ k : Fin d, ψ x *
        heatWindowGradient (fun y => g (translate y ρ)) a b j k k x := by
      apply integral_congr_ae
      exact ae_of_all _ fun x => by dsimp only; rw [mul_comm, Finset.mul_sum]
    _ = _ := by
      rw [integral_finsetSum Finset.univ (fun k _ => (hi k).1)]
      simp only [horizontalMollify, heatWindowGradient_translate]

/-- The integral of a coordinate derivative of a smooth compactly supported function
vanishes. -/
theorem integral_coordinateDerivative_eq_zero {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφc : HasCompactSupport φ) (i : Fin d) : ∫ x, coordinateDerivative i φ x = 0 := by
  have h := integral_mul_coordinateDerivative_eq_neg (f := φ) (g := fun _ => (1 : ℝ)) (i := i)
    (hφ.of_le (by norm_cast)) hφc contDiff_const
  have h0 : coordinateDerivative i (fun _ : Vec d => (1 : ℝ)) = fun _ => 0 := by
    funext x
    simp [coordinateDerivative]
  simp only [h0, mul_zero, integral_zero, mul_one] at h
  linarith

/-- Subtracting a constant vector preserves a weak divergence on all of space. -/
theorem hasWeakDivergence_sub_const {F : Vec d → Vec d} {h : Vec d → ℝ}
    (hF : HasWeakDivergence Set.univ F h) (c : Vec d) :
    HasWeakDivergence Set.univ (fun x => F x - c) h := by
  refine ⟨fun i => (hF.1 i).sub (locallyIntegrableOn_const _), hF.2.1, fun φ hφ => ?_⟩
  have hD (i : Fin d) : ContDiff ℝ (⊤ : ℕ∞) (coordinateDerivative i φ) :=
    contDiff_coordinateDerivative' hφ.1 i
  have hDc (i : Fin d) : HasCompactSupport (coordinateDerivative i φ) :=
    hasCompactSupport_coordinateDerivative' hφ.2.1 i
  have hFi (i : Fin d) : Integrable (fun x => F x i * coordinateDerivative i φ x) volume := by
    simpa only [smul_eq_mul] using (locallyIntegrableOn_univ.mp (hF.1 i))
      |>.integrable_smul_right_of_hasCompactSupport (hD i).continuous (hDc i)
  have hci (i : Fin d) : Integrable (fun x => c i * coordinateDerivative i φ x) volume :=
    ((hD i).continuous.integrable_of_hasCompactSupport (hDc i)).const_mul _
  have h1 := hF.2.2 φ hφ
  simp only [Measure.restrict_univ, dot, gradient] at h1 ⊢
  rw [← h1]
  have hsumF : Integrable (fun x => ∑ i, F x i * coordinateDerivative i φ x) volume :=
    integrable_finsetSum _ fun i _ => hFi i
  have hsumc : Integrable (fun x => ∑ i, c i * coordinateDerivative i φ x) volume :=
    integrable_finsetSum _ fun i _ => hci i
  have hc0 : ∫ x, ∑ i, c i * coordinateDerivative i φ x = 0 := by
    rw [integral_finsetSum _ fun i _ => hci i]
    exact Finset.sum_eq_zero fun i _ => by
      rw [integral_const_mul, integral_coordinateDerivative_eq_zero hφ.1 hφ.2.1 i, mul_zero]
  calc (∫ x, ∑ i, (F x - c) i * coordinateDerivative i φ x)
      = ∫ x, ((∑ i, F x i * coordinateDerivative i φ x) -
          ∑ i, c i * coordinateDerivative i φ x) := by
        refine integral_congr_ae (ae_of_all _ fun x => ?_)
        simp only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
    _ = ∫ x, ∑ i, F x i * coordinateDerivative i φ x := by
        rw [integral_sub hsumF hsumc, hc0, sub_zero]

/-- The centered canonical flux has mean zero in every coordinate. -/
theorem integral_canonicalCenteredFlux_coord {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀)
    (i k : Fin d) :
    ∫ ω, (canonicalCorrectorFlux Q i ω - expectedCorrectorFlux Q i).ofLp k
      ∂reducedEnvironmentLaw Q = 0 := by
  have hint : Integrable (fun ω => canonicalCorrectorFlux Q i ω - expectedCorrectorFlux Q i)
      (reducedEnvironmentLaw Q) :=
    (canonicalCorrectorFlux_integrable Q i).sub (integrable_const _)
  have h0 : ∫ ω, (canonicalCorrectorFlux Q i ω - expectedCorrectorFlux Q i)
      ∂reducedEnvironmentLaw Q = 0 := by
    rw [integral_sub (canonicalCorrectorFlux_integrable Q i) (integrable_const _)]
    simp [expectedCorrectorFlux_eq_integral]
  have h := (EuclideanSpace.proj k : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ).integral_comp_comm hint
  calc (∫ ω, (canonicalCorrectorFlux Q i ω - expectedCorrectorFlux Q i).ofLp k
        ∂reducedEnvironmentLaw Q)
      = ∫ ω, (EuclideanSpace.proj k : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)
          (canonicalCorrectorFlux Q i ω - expectedCorrectorFlux Q i) ∂reducedEnvironmentLaw Q :=
        rfl
    _ = 0 := by rw [h, h0, map_zero]

/-- The variational canonical flux is samplewise divergence free. -/
theorem ae_canonicalCorrectorFlux_hasWeakDivergence [Fact (2 ≤ d)]
    {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀) (i : Fin d) :
    ∀ᵐ ω ∂reducedEnvironmentLaw Q, HasWeakDivergence Set.univ
      (fun x => (canonicalCorrectorFlux Q i (translate x ω)).ofLp) (fun _ => 0) := by
  apply SpatialDivergence.ae_hasWeakDivergence_of_ae_fixedTest
    (reducedEnvironmentLaw Q) (reducedEnvironmentLaw_stationary Q)
    (canonicalCorrectorFlux Q i)
  intro ψ
  exact ae_spatial_divergence_fixedTest (reducedEnvironmentLaw Q)
    (reducedEnvironmentLaw_stationary Q) (canonicalCorrectorFlux Q i)
    (canonicalCorrectorGradient_variational_horizontalH1 Q i)
    ψ ψ.contDiff ψ.hasCompactSupport

/-- The centered canonical flux along almost every orbit is weakly divergence free. -/
theorem ae_canonicalCenteredFlux_hasWeakDivergence [Fact (2 ≤ d)] {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) (i : Fin d) :
    ∀ᵐ ρ ∂reducedEnvironmentLaw Q, HasWeakDivergence Set.univ
      (fun x => (canonicalCorrectorFlux Q i (translate x ρ) - expectedCorrectorFlux Q i).ofLp)
      (fun _ => 0) := by
  filter_upwards [ae_canonicalCorrectorFlux_hasWeakDivergence Q i] with ρ hρ
  simpa only [WithLp.ofLp_sub] using hasWeakDivergence_sub_const hρ (expectedCorrectorFlux Q i).ofLp

theorem canonical_flux_source_measurable_memLp {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) (i : Fin d) :
    Measurable (fun ω => (canonicalCorrectorFlux Q i ω - expectedCorrectorFlux Q i).ofLp) ∧
    ∀ j, MemLp (fun ω => (canonicalCorrectorFlux Q i ω - expectedCorrectorFlux Q i).ofLp j)
      2 (reducedEnvironmentLaw Q) := by
  have hV : Measurable (fun ω => canonicalCorrectorFlux Q i ω - expectedCorrectorFlux Q i) :=
    (Lp.stronglyMeasurable (canonicalCorrectorFlux Q i)).measurable.sub measurable_const
  refine ⟨(PiLp.continuous_ofLp (p := 2) (β := fun _ : Fin d => ℝ)).measurable.comp hV, ?_⟩
  intro j
  have hmem := (Lp.memLp (canonicalCorrectorFlux Q i)).sub
    (memLp_const (expectedCorrectorFlux Q i))
  apply hmem.of_le_mul (c := 1)
  · exact (((PiLp.proj (p := 2) (𝕜 := ℝ) (β := fun _ : Fin d => ℝ) j).continuous).measurable.comp
      hV).aestronglyMeasurable
  · exact ae_of_all _ (fun ω => by
      simpa only [one_mul, Real.norm_eq_abs, Pi.sub_apply] using
        PiLp.norm_apply_le (canonicalCorrectorFlux Q i ω - expectedCorrectorFlux Q i) j)

/-- The canonical centered source satisfies the positive-window diagonal
identity, with no moment hypothesis on the selected trace. -/
theorem ae_canonical_testPairing_window_diag [Fact (2 ≤ d)] {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) (i : Fin d)
    {ψ : Vec d → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ)
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (j : Fin d) :
    ∀ᵐ ρ ∂reducedEnvironmentLaw Q,
      (∫ x, (∑ k : Fin d, heatWindowGradient
        (fun y => (canonicalCorrectorFlux Q i (translate y ρ)).ofLp -
          (expectedCorrectorFlux Q i).ofLp) a b j k k x) * ψ x) =
        horizontalMollify ψ (heatSmoothed a (fun ω =>
          (canonicalCorrectorFlux Q i ω - expectedCorrectorFlux Q i).ofLp j)) ρ -
        horizontalMollify ψ (heatSmoothed b (fun ω =>
          (canonicalCorrectorFlux Q i ω - expectedCorrectorFlux Q i).ofLp j)) ρ := by
  simpa only [WithLp.ofLp_sub] using ae_testPairing_window_diag
    (reducedEnvironmentLaw Q) (reducedEnvironmentLaw_stationary Q)
    (canonical_flux_source_measurable_memLp Q i).1
    (canonical_flux_source_measurable_memLp Q i).2
    (ae_canonicalCenteredFlux_hasWeakDivergence Q i) hψ hψc a b ha hab j

/-- Small-time endpoint: tested heat smoothing converges in `L¹` along any
nonnegative sequence tending to zero. -/
theorem tendsto_eLpNorm_horizontalMollify_heatSmoothed_smallTime_sub {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q] (hQ : IsStationary Q)
    {K : Vec d → ℝ} (hK : ContDiff ℝ 2 K) (hKc : HasCompactSupport K)
    {f : FieldPair d → ℝ} (hf : Measurable f) (hfi : Integrable f Q) :
    ∀ (a : ℕ → ℝ), (∀ m, 0 ≤ a m) → Tendsto a atTop (𝓝 0) →
    Tendsto (fun m : ℕ => eLpNorm (fun ω =>
      horizontalMollify K (heatSmoothed (a m) f) ω -
        horizontalMollify K f ω) 1 Q) atTop (𝓝 0) := by
  intro a ha halim
  have hL : Measurable (coordLaplacian K) := (continuous_coordLaplacian hK).measurable
  have hLi : Integrable (coordLaplacian K) := integrable_coordLaplacian hK hKc
  set M : ℝ := (eLpNorm f 1 Q).toReal with hMdef
  have hM : 0 ≤ M := ENNReal.toReal_nonneg
  have hfn : ∀ t : ℝ, 0 ≤ t → eLpNorm (heatSmoothed t f) (ENNReal.ofReal 1) Q ≤
      ENNReal.ofReal (M * heatAveragingProfile 1 t) := by
    intro t ht
    refine (eLpNorm_heatSmoothed_le Q hQ le_rfl hf ht).trans ?_
    rw [ENNReal.ofReal_one,
      ← ENNReal.ofReal_toReal (memLp_one_iff_integrable.mpr hfi).eLpNorm_ne_top]
    refine ENNReal.ofReal_le_ofReal ?_
    have hp : 1 ≤ heatAveragingProfile 1 t := by
      unfold heatAveragingProfile
      have : 0 ≤ (Real.sqrt (1 + t))⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
      linarith [inv_one (G := ℝ)]
    nlinarith
  have hbound (a : ℝ) (ha : 0 ≤ a) : eLpNorm (fun ω =>
      horizontalMollify K (heatSmoothed a f) ω - horizontalMollify K f ω) 1 Q ≤
      ENNReal.ofReal ((∫ x, |coordLaplacian K x|) * M * (2 * a)) := by
    have hmom := (integral_horizontalMollify_heatSmoothed_moment_le Q hQ le_rfl hM one_pos ha
      hL hLi hf hfn).2.2
    rw [ENNReal.ofReal_one] at hmom
    have heq : (fun ω => horizontalMollify K (heatSmoothed a f) ω - horizontalMollify K f ω)
        =ᵐ[Q] fun ω => ∫ t in (0 : ℝ)..a, horizontalMollify (coordLaplacian K)
          (heatSmoothed t f) ω := by
      filter_upwards [horizontalMollify_heat_transfer Q hQ hK hKc hf hfi ha] with ω hω
      unfold heatTransferExpression at hω
      linarith
    rw [eLpNorm_congr_ae heq]
    refine hmom.trans (ENNReal.ofReal_le_ofReal ?_)
    have hprof : (∫ t in (0 : ℝ)..a, heatAveragingProfile 1 t) ≤ 2 * a := by
      have hle : ∀ t ∈ Set.Icc (0 : ℝ) a, heatAveragingProfile 1 t ≤ 2 := by
        intro t ht
        unfold heatAveragingProfile
        have h1 : (Real.sqrt (1 + t))⁻¹ ≤ 1 := by
          apply inv_le_one_of_one_le₀
          rw [Real.one_le_sqrt]
          linarith [ht.1]
        linarith [inv_one (G := ℝ)]
      calc (∫ t in (0 : ℝ)..a, heatAveragingProfile 1 t) ≤ ∫ t in (0 : ℝ)..a, (2 : ℝ) :=
            intervalIntegral.integral_mono_on ha (intervalIntegrable_heatAveragingProfile 1 ha)
              intervalIntegrable_const hle
        _ = 2 * a := by simp; ring
    have hc : 0 ≤ (∫ x, |coordLaplacian K x|) * M :=
      mul_nonneg (integral_nonneg fun _ => abs_nonneg _) hM
    exact mul_le_mul_of_nonneg_left hprof hc
  have hlim : Tendsto (fun m : ℕ => ENNReal.ofReal ((∫ x, |coordLaplacian K x|) * M *
      (2 * a m))) atTop (𝓝 0) := by
    rw [← ENNReal.ofReal_zero]
    refine ENNReal.tendsto_ofReal ?_
    simpa only [mul_zero] using (halim.const_mul 2).const_mul ((∫ x, |coordLaplacian K x|) * M)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun _ => zero_le) (fun m => hbound _ (ha m))


private theorem euclideanSq_le_two_mul_add (u h : Vec d) :
    euclideanSq u ≤ 2 * euclideanSq (u + h) + 2 * euclideanSq h := by
  unfold euclideanSq dot
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  simp only [Pi.add_apply]
  nlinarith [sq_nonneg (u i + 2 * h i)]

private theorem euclideanSq_le_of_norm_le_one {h : Vec d} (hh : ‖h‖ ≤ 1) :
    euclideanSq h ≤ d := by
  unfold euclideanSq dot
  calc (∑ i, h i * h i) ≤ ∑ _i : Fin d, (1 : ℝ) := by
        refine Finset.sum_le_sum fun i _ => ?_
        have hi := (norm_le_pi_norm h i).trans hh
        rw [Real.norm_eq_abs] at hi
        nlinarith [abs_nonneg (h i), abs_mul_abs_self (h i)]
    _ = d := by simp

/-- A unit-time Gaussian translated by at most one is dominated by a wider Gaussian. -/
private theorem euclideanHeatKernel_one_add_le {u h : Vec d} (hh : ‖h‖ ≤ 1) :
    euclideanHeatKernel 1 (u + h) ≤
      (4 * Real.pi) ^ (-(d : ℝ) / 2) * Real.exp (d / 4) * Real.exp (-(euclideanSq u) / 8) := by
  unfold euclideanHeatKernel
  rw [mul_one, mul_assoc, ← Real.exp_add]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
  have h1 := euclideanSq_le_two_mul_add u h
  have h2 := euclideanSq_le_of_norm_le_one hh
  linarith

private theorem integrable_exp_neg_euclideanSq_div_eight :
    Integrable (fun u : Vec d => Real.exp (-(euclideanSq u) / 8)) volume := by
  have h := (integrable_euclideanHeatKernel (d := d) (by norm_num : (0 : ℝ) < 2)).const_mul
    ((4 * Real.pi * 2) ^ ((d : ℝ) / 2))
  refine h.congr (ae_of_all _ fun u => ?_)
  simp only [euclideanHeatKernel]
  rw [← mul_assoc, ← Real.rpow_add (by positivity)]
  rw [show (d : ℝ) / 2 + -(d : ℝ) / 2 = 0 by ring, Real.rpow_zero, one_mul]
  norm_num

/-- `L¹` continuity of translation for the unit-time heat kernel. -/
theorem tendsto_integral_abs_heatKernel_one_translate_sub :
    Tendsto (fun h : Vec d => ∫ u, |euclideanHeatKernel 1 (u + h) - euclideanHeatKernel 1 u|)
      (𝓝 0) (𝓝 0) := by
  have hc : Continuous (euclideanHeatKernel (d := d) 1) := continuous_euclideanHeatKernel 1
  set K : ℝ := (4 * Real.pi) ^ (-(d : ℝ) / 2) * Real.exp (d / 4) with hKdef
  have hdom := tendsto_integral_filter_of_dominated_convergence
    (μ := (volume : Measure (Vec d))) (l := 𝓝 (0 : Vec d))
    (F := fun h u => |euclideanHeatKernel 1 (u + h) - euclideanHeatKernel 1 u|)
    (f := fun _ => 0)
    (fun u => K * Real.exp (-(euclideanSq u) / 8) + euclideanHeatKernel 1 u)
    (Eventually.of_forall fun h => ((hc.comp (continuous_id.add continuous_const)).sub
      hc).abs.aestronglyMeasurable)
    (by
      filter_upwards [Metric.closedBall_mem_nhds (0 : Vec d) one_pos] with h hh
      refine ae_of_all _ fun u => ?_
      rw [Metric.mem_closedBall, dist_zero_right] at hh
      have h0 := euclideanHeatKernel_nonneg (d := d) zero_le_one (u + h)
      have h1 := euclideanHeatKernel_nonneg (d := d) zero_le_one u
      have h2 := euclideanHeatKernel_one_add_le (u := u) hh
      rw [Real.norm_eq_abs, abs_abs, abs_le]
      constructor <;> linarith)
    ((integrable_exp_neg_euclideanSq_div_eight.const_mul K).add
      (integrable_euclideanHeatKernel zero_lt_one))
    (ae_of_all _ fun u => by
      have ht : Tendsto (fun h : Vec d => euclideanHeatKernel 1 (u + h)) (𝓝 0)
          (𝓝 (euclideanHeatKernel 1 u)) := by
        simpa only [Function.comp_def, Pi.add_apply, id_eq, add_zero] using (hc.tendsto (u + 0)).comp
          ((continuous_const.add continuous_id).tendsto (0 : Vec d))
      have h2 := (ht.sub (tendsto_const_nhds (x := euclideanHeatKernel 1 u))).abs
      simpa using h2)
  simpa using hdom

/-- Parabolic scaling of the translation difference. -/
theorem integral_abs_heatKernel_translate_sub_eq {t : ℝ} (ht : 0 < t) (w : Vec d) :
    (∫ y, |euclideanHeatKernel t (y + w) - euclideanHeatKernel t y|) =
      ∫ u, |euclideanHeatKernel 1 (u + (Real.sqrt t)⁻¹ • w) - euclideanHeatKernel 1 u| := by
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have hchange := Measure.integral_comp_smul (volume : Measure (Vec d))
    (fun y => |euclideanHeatKernel t (y + w) - euclideanHeatKernel t y|) (Real.sqrt t)
  simp only [Module.finrank_fin_fun] at hchange
  have hpt (u : Vec d) : |euclideanHeatKernel t (Real.sqrt t • u + w) -
      euclideanHeatKernel t (Real.sqrt t • u)| =
      (Real.sqrt t ^ d)⁻¹ * |euclideanHeatKernel 1 (u + (Real.sqrt t)⁻¹ • w) -
        euclideanHeatKernel 1 u| := by
    have hw : Real.sqrt t • u + w = Real.sqrt t • (u + (Real.sqrt t)⁻¹ • w) := by
      rw [smul_add, smul_smul, mul_inv_cancel₀ hs.ne', one_smul]
    rw [hw, euclideanHeatKernel_sqrt_smul ht, euclideanHeatKernel_sqrt_smul ht, ← mul_sub,
      abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (Real.sqrt t ^ d)⁻¹)]
  simp_rw [hpt, integral_const_mul] at hchange
  have hne : (Real.sqrt t ^ d)⁻¹ ≠ 0 := by positivity
  rw [abs_of_pos (by positivity : (0 : ℝ) < ((Real.sqrt t) ^ d)⁻¹), smul_eq_mul] at hchange
  exact (mul_left_cancel₀ hne hchange).symm

/-- Large-time translation decay of the Gaussian for arbitrary positive times. -/
theorem tendsto_integral_abs_heatKernel_translate_sub_largeTime
    (b : ℕ → ℝ) (hb : ∀ n, 0 < b n) (hblim : Tendsto b atTop atTop) (w : Vec d) :
    Tendsto (fun n => ∫ y, |euclideanHeatKernel (b n) (y + w) -
      euclideanHeatKernel (b n) y|) atTop (𝓝 0) := by
  simp_rw [integral_abs_heatKernel_translate_sub_eq (hb _)]
  refine tendsto_integral_abs_heatKernel_one_translate_sub.comp ?_
  have hinv := tendsto_inv_atTop_zero.comp hblim
  have hsq : Tendsto (fun n => (Real.sqrt (b n))⁻¹) atTop (𝓝 0) := by
    have h := (Real.continuous_sqrt.tendsto 0).comp hinv
    simpa only [Function.comp_def, Real.sqrt_inv, Real.sqrt_zero] using h
  simpa only [zero_smul] using hsq.smul_const w

/-- Large-time translation decay: translating the kernel changes the tested
heat average by an `L¹`-small amount along any positive sequence tending to infinity. -/
theorem tendsto_eLpNorm_horizontalMollify_heatSmoothed_largeTime_translate_sub {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q] (hQ : IsStationary Q)
    {ψ : Vec d → ℝ} (hψ : Continuous ψ) (hψc : HasCompactSupport ψ)
    {f : FieldPair d → ℝ} (hf : Measurable f) (hfi : Integrable f Q) (z : Vec d)
    (b : ℕ → ℝ) (hbpos : ∀ n, 0 < b n) (hblim : Tendsto b atTop atTop) :
    Tendsto (fun n : ℕ => eLpNorm (fun ω =>
      horizontalMollify (fun x => ψ (x - z)) (heatSmoothed (b n) f) ω -
        horizontalMollify ψ (heatSmoothed (b n) f) ω) 1 Q) atTop (𝓝 0) := by
  have hψi : Integrable ψ volume := hψ.integrable_of_hasCompactSupport hψc
  set A : ℝ := (eLpNorm f 1 Q).toReal with hAdef
  have hA : 0 ≤ A := ENNReal.toReal_nonneg
  have hfA : eLpNorm f (ENNReal.ofReal 1) Q ≤ ENNReal.ofReal A := by
    rw [ENNReal.ofReal_one, hAdef, ENNReal.ofReal_toReal
      (memLp_one_iff_integrable.mpr hfi).eLpNorm_ne_top]
  set D : ℕ → ℝ := fun n => ∫ y, |euclideanHeatKernel (b n) (y + -z) -
    euclideanHeatKernel (b n) y| with hDdef
  have hbound (n : ℕ) : eLpNorm (fun ω =>
      horizontalMollify (fun x => ψ (x - z)) (heatSmoothed (b n) f) ω -
        horizontalMollify ψ (heatSmoothed (b n) f) ω) 1 Q ≤
      ENNReal.ofReal ((∫ x, |ψ x|) * (D n * A)) := by
    set t : ℝ := b n
    have hb : 0 < t := hbpos n
    let k : Vec d → ℝ := fun y => euclideanHeatKernel t (y + -z) - euclideanHeatKernel t y
    have hΦ : Continuous (euclideanHeatKernel (d := d) t) := continuous_euclideanHeatKernel t
    have hkm : Measurable k :=
      ((hΦ.comp (continuous_id.add continuous_const)).sub hΦ).measurable
    have hΦi : Integrable (euclideanHeatKernel (d := d) t) volume :=
      integrable_euclideanHeatKernel hb
    have hΦzi : Integrable (fun y => euclideanHeatKernel (d := d) t (y + -z)) volume :=
      hΦi.comp_add_right (-z)
    have hki : Integrable k volume := hΦzi.sub hΦi
    have hHm : Measurable (heatSmoothed t f) :=
      (measurable_heatSmoothed_joint hf).comp (measurable_const.prodMk measurable_id)
    have hHi : Integrable (heatSmoothed t f) Q := by
      have h1 := eLpNorm_heatSmoothed_le Q hQ le_rfl hf hb.le
      rw [ENNReal.ofReal_one] at h1
      exact memLp_one_iff_integrable.mp
        (h1.trans_lt (memLp_one_iff_integrable.mpr hfi).eLpNorm_lt_top)
    have hHzm : Measurable (fun ρ => heatSmoothed t f (translate z ρ)) :=
      hHm.comp (Probability.measurable_translate z)
    have hHzi : Integrable (fun ρ => heatSmoothed t f (translate z ρ)) Q :=
      (measurePreserving_translate Q hQ z).integrable_comp_of_integrable hHi
    have hkfm : Measurable (horizontalMollify k f) := measurable_horizontalMollify k hkm hf
    -- the translated heat average differs by the convolution with `k`
    have hdiff : (fun ρ => heatSmoothed t f (translate z ρ) - heatSmoothed t f ρ) =ᵐ[Q]
        horizontalMollify k f := by
      have hΦzm : Measurable (fun y => euclideanHeatKernel (d := d) t (y + -z)) :=
        (hΦ.comp (continuous_id.add continuous_const)).measurable
      filter_upwards [ae_integrable_kernel_translate hQ hΦ.measurable hΦi hf hfi,
        ae_integrable_kernel_translate hQ hΦzm hΦzi hf hfi] with ρ h1 h2
      have hshift : heatSmoothed t f (translate z ρ) =
          ∫ y, euclideanHeatKernel t (y + -z) * f (translate y ρ) := by
        simp only [heatSmoothed, if_neg hb.ne', translate_add]
        have h := integral_add_right_eq_self (μ := (volume : Measure (Vec d)))
          (fun y => euclideanHeatKernel t (y + -z) * f (translate y ρ)) z
        simp only [add_neg_cancel_right] at h
        rw [← h]
      rw [hshift]
      simp only [heatSmoothed, if_neg hb.ne', horizontalMollify, k, sub_mul]
      exact (integral_sub h2 h1).symm
    -- bound the tested difference
    have hk1 : eLpNorm (horizontalMollify k f) (ENNReal.ofReal 1) Q ≤
        ENNReal.ofReal ((∫ x, |k x|) * A) :=
      (horizontalMollify_moment_le Q hQ le_rfl hA hkm hki hf hfA).2.2
    have hψk := (horizontalMollify_moment_le Q hQ le_rfl
      (mul_nonneg (integral_nonneg fun _ => abs_nonneg _) hA) hψ.measurable hψi hkfm hk1).2.2
    have heq : (fun ω =>
        horizontalMollify (fun x => ψ (x - z)) (heatSmoothed t f) ω -
          horizontalMollify ψ (heatSmoothed t f) ω) =ᵐ[Q]
        horizontalMollify ψ (horizontalMollify k f) := by
      filter_upwards [horizontalMollify_sub_ae hQ hψ.measurable hψi hHzm hHzi hHm hHi,
        horizontalMollify_congr_ae (K := ψ) hQ (hHzm.sub hHm) hkfm hdiff] with ω h1 h2
      rw [← horizontalMollify_comp_translate, ← h1]
      exact h2
    rw [eLpNorm_congr_ae heq]
    rw [ENNReal.ofReal_one] at hψk
    exact hψk
  have hlim : Tendsto (fun n => ENNReal.ofReal ((∫ x, |ψ x|) * (D n * A))) atTop (𝓝 0) := by
    rw [← ENNReal.ofReal_zero]
    refine ENNReal.tendsto_ofReal ?_
    have h := ((tendsto_integral_abs_heatKernel_translate_sub_largeTime (d := d) b hbpos hblim (-z)).mul_const A).const_mul
      (∫ x, |ψ x|)
    rw [zero_mul, mul_zero] at h
    exact h
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun _ => zero_le) hbound


/-- Variables bounded in `L²` are uniformly integrable in `L¹`. -/
theorem unifIntegrable_one_of_eLpNorm_two_le {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {X : ℕ → Ω → ℝ} {M : ℝ}
    (hX : ∀ n, AEStronglyMeasurable (X n) μ)
    (hbound : ∀ n, eLpNorm (X n) 2 μ ≤ ENNReal.ofReal M) :
    UnifIntegrable X 1 μ := by
  refine unifIntegrable_of le_rfl ENNReal.one_ne_top hX fun ε hε => ?_
  by_cases hεtop : ε = ∞
  · subst ε
    exact ⟨0, fun _ => le_top⟩
  let εR : ℝ := ε.toReal
  have hεR : 0 < εR := ENNReal.toReal_pos hε.ne' hεtop
  set M' : ℝ := max M 0 with hM'
  have hM'0 : 0 ≤ M' := le_max_right _ _
  let C : ℝ≥0 := ⟨M' ^ 2 / εR + 1, by positivity⟩
  have hCpos : (0 : ℝ) < (C : ℝ) := by
    change 0 < M' ^ 2 / εR + 1
    positivity
  have hC0 : (C : ℝ≥0∞) ≠ 0 := by exact_mod_cast (NNReal.coe_pos.mp hCpos).ne'
  refine ⟨C, fun n => ?_⟩
  rw [eLpNorm_one_eq_lintegral_enorm ((hX n).indicator₀
    (nullMeasurableSet_le aemeasurable_const (hX n).nnnorm.aemeasurable))]
  have hpt : ∀ x, ‖{x | C ≤ ‖X n x‖₊}.indicator (X n) x‖ₑ ≤ ‖X n x‖ₑ ^ 2 / C := by
    intro x
    by_cases hx : C ≤ ‖X n x‖₊
    · rw [Set.indicator_of_mem (show x ∈ {x | C ≤ ‖X n x‖₊} from hx),
        ENNReal.le_div_iff_mul_le (Or.inl hC0) (Or.inl ENNReal.coe_ne_top), sq]
      exact mul_le_mul_right (by exact_mod_cast hx) _
    · rw [Set.indicator_of_notMem (show x ∉ {x | C ≤ ‖X n x‖₊} from hx), enorm_zero]
      exact zero_le
  have hMn : eLpNorm (X n) 2 μ ≤ ENNReal.ofReal M' :=
    (hbound n).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  calc (∫⁻ x, ‖{x | C ≤ ‖X n x‖₊}.indicator (X n) x‖ₑ ∂μ)
      ≤ ∫⁻ x, ‖X n x‖ₑ ^ 2 / C ∂μ := lintegral_mono hpt
    _ = (∫⁻ x, ‖X n x‖ₑ ^ 2 ∂μ) / C := by
        simp only [div_eq_mul_inv]
        exact lintegral_mul_const' _ _ (ENNReal.inv_ne_top.mpr hC0)
    _ = eLpNorm (X n) 2 μ ^ 2 / C := by
        have h := eLpNorm_nnreal_pow_eq_lintegral (p := (2 : ℝ≥0))
          (by norm_num) (hX n)
        have hsq : eLpNorm (X n) 2 μ ^ 2 = ∫⁻ x, ‖X n x‖ₑ ^ 2 ∂μ := by
          norm_num only [NNReal.coe_ofNat, ENNReal.coe_ofNat, ENNReal.rpow_ofNat] at h
          exact h
        rw [hsq]
    _ ≤ ENNReal.ofReal M' ^ 2 / C := by gcongr
    _ = ENNReal.ofReal (M' ^ 2 / C) := by
        rw [← ENNReal.ofReal_pow hM'0, ENNReal.ofReal_div_of_pos hCpos, ENNReal.ofReal_coe_nnreal]
    _ ≤ ENNReal.ofReal εR := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [div_le_iff₀ hCpos]
        change M' ^ 2 ≤ εR * (M' ^ 2 / εR + 1)
        rw [mul_add, mul_div_cancel₀ _ hεR.ne', mul_one]
        linarith
    _ = ε := ENNReal.ofReal_toReal hεtop

/-- Almost-sure limits of mean-zero variables bounded in `L²` are integrable with mean
zero. -/
theorem integral_eq_zero_of_tendsto_ae_of_eLpNorm_two_le {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : ℕ → Ω → ℝ} {Y : Ω → ℝ} {M : ℝ}
    (hX : ∀ n, AEStronglyMeasurable (X n) μ)
    (hbound : ∀ n, eLpNorm (X n) 2 μ ≤ ENNReal.ofReal M)
    (hmean : ∀ n, ∫ ω, X n ω ∂μ = 0)
    (hlim : ∀ᵐ ω ∂μ, Tendsto (fun n => X n ω) atTop (𝓝 (Y ω))) :
    Integrable Y μ ∧ ∫ ω, Y ω ∂μ = 0 := by
  have hY : AEStronglyMeasurable Y μ := aestronglyMeasurable_of_tendsto_ae atTop hX hlim
  have hY2 : eLpNorm Y 2 μ ≤ ENNReal.ofReal M :=
    (Lp.eLpNorm_lim_le_liminf_eLpNorm hX Y hY hlim).trans
      (liminf_le_of_frequently_le' (Frequently.of_forall hbound))
  have hYm : MemLp Y 2 μ := hY2.trans_lt ENNReal.ofReal_lt_top
  have hY1 : Integrable Y μ := hYm.integrable one_le_two
  have hXi (n : ℕ) : Integrable (X n) μ :=
    (MemLp.integrable one_le_two ((hbound n).trans_lt ENNReal.ofReal_lt_top))
  have hL1 := tendsto_Lp_finite_of_tendsto_ae le_rfl ENNReal.one_ne_top hX
    (memLp_one_iff_integrable.mpr hY1) (unifIntegrable_one_of_eLpNorm_two_le hX hbound) hlim
  have hint := tendsto_integral_of_L1' Y (Eventually.of_forall hXi) hL1
  simp only [hmean] at hint
  exact ⟨hY1, tendsto_nhds_unique hint tendsto_const_nhds⟩

/-- If `X (m,n) = A m - B n` almost surely, `X` converges almost surely along the
product filter and `A` converges in `L¹`, then `B` converges almost surely along a
subsequence. -/
theorem exists_subseq_ae_tendsto_of_sub {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {X : ℕ × ℕ → Ω → ℝ} {A B : ℕ → Ω → ℝ}
    {Y A' : Ω → ℝ} (_hA : ∀ m, AEStronglyMeasurable (A m) μ)
    (_hA' : AEStronglyMeasurable A' μ)
    (hdec : ∀ m n, ∀ᵐ ω ∂μ, X (m, n) ω = A m ω - B n ω)
    (hX : ∀ᵐ ω ∂μ, Tendsto (fun mn => X mn ω) atTop (𝓝 (Y ω)))
    (hAlim : Tendsto (fun m => eLpNorm (fun ω => A m ω - A' ω) 1 μ) atTop (𝓝 0)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ᵐ ω ∂μ, Tendsto (fun k => B (φ k) ω) atTop (𝓝 (A' ω - Y ω)) := by
  have hmeas : TendstoInMeasure μ A atTop A' :=
    tendstoInMeasure_of_tendsto_eLpNorm one_ne_zero hAlim
  obtain ⟨φ, hφ, hAφ⟩ := hmeas.exists_seq_tendsto_ae
  refine ⟨φ, hφ, ?_⟩
  have hdiag : Tendsto (fun k => (φ k, φ k)) atTop (atTop : Filter (ℕ × ℕ)) := by
    rw [← prod_atTop_atTop_eq]
    exact hφ.tendsto_atTop.prodMk hφ.tendsto_atTop
  filter_upwards [hAφ, hX, ae_all_iff.mpr fun k => hdec (φ k) (φ k)] with ω h1 h2 h3
  have hXk : Tendsto (fun k => X (φ k, φ k) ω) atTop (𝓝 (Y ω)) := h2.comp hdiag
  have heq : (fun k => B (φ k) ω) = fun k => A (φ k) ω - X (φ k, φ k) ω := by
    funext k
    rw [h3 k]
    ring
  rw [heq]
  exact h1.sub hXk

/-- An almost-sure limit along a subsequence agrees with an `L¹` limit. -/
theorem ae_eq_of_subseq_tendsto_ae_of_tendsto_eLpNorm_one {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {B : ℕ → Ω → ℝ} {Y Z : Ω → ℝ}
    (hB : ∀ n, AEStronglyMeasurable (B n) μ) (_hZ : AEStronglyMeasurable Z μ)
    {φ : ℕ → ℕ} (hφ : StrictMono φ)
    (hY : ∀ᵐ ω ∂μ, Tendsto (fun k => B (φ k) ω) atTop (𝓝 (Y ω)))
    (hZlim : Tendsto (fun n => eLpNorm (fun ω => B n ω - Z ω) 1 μ) atTop (𝓝 0)) :
    Y =ᵐ[μ] Z := by
  exact tendstoInMeasure_ae_unique (tendstoInMeasure_of_tendsto_ae (fun k => hB (φ k)) hY)
    (tendstoInMeasure_of_tendsto_eLpNorm one_ne_zero
      (hZlim.comp hφ.tendsto_atTop))


/-- Positive-time heat testing has a uniform square bound and preserves a zero mean. -/
theorem horizontalMollify_heatSmoothed_bound_mean
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q] (hQ : IsStationary Q)
    {ψ : Vec d → ℝ} (hψ : Measurable ψ) (hψi : Integrable ψ volume)
    {f : FieldPair d → ℝ} (hf : Measurable f) (hf2 : MemLp f 2 Q)
    (hf0 : ∫ ω, f ω ∂Q = 0) (t : ℝ) (ht : 0 ≤ t) :
    eLpNorm (horizontalMollify ψ (heatSmoothed t f)) 2 Q ≤
        ENNReal.ofReal ((∫ x, |ψ x|) * (eLpNorm f 2 Q).toReal) ∧
      ∫ ρ, horizontalMollify ψ (heatSmoothed t f) ρ ∂Q = 0 := by
  have hfi : Integrable f Q := hf2.integrable one_le_two
  have hHm : Measurable (heatSmoothed t f) :=
    (measurable_heatSmoothed_joint hf).comp (measurable_const.prodMk measurable_id)
  have h2 := eLpNorm_heatSmoothed_le Q hQ (by norm_num : (1 : ℝ) ≤ 2) hf ht
  have h1 := eLpNorm_heatSmoothed_le Q hQ le_rfl hf ht
  rw [ENNReal.ofReal_one] at h1
  have hHi : Integrable (heatSmoothed t f) Q :=
    memLp_one_iff_integrable.mp
      (h1.trans_lt (memLp_one_iff_integrable.mpr hfi).eLpNorm_lt_top)
  have hfn : eLpNorm (heatSmoothed t f) (ENNReal.ofReal 2) Q ≤
      ENNReal.ofReal (eLpNorm f 2 Q).toReal := by
    rw [ENNReal.ofReal_toReal hf2.eLpNorm_ne_top]
    simpa only [ENNReal.ofReal_ofNat] using h2
  have hm := (horizontalMollify_moment_le Q hQ (by norm_num : (1 : ℝ) ≤ 2)
    ENNReal.toReal_nonneg hψ hψi hHm hfn).2.2
  refine ⟨by simpa only [ENNReal.ofReal_ofNat] using hm, ?_⟩
  rw [integral_horizontalMollify_of_integrable Q hQ hψ hψi hHm hHi,
    integral_heatSmoothed Q hQ hf hfi t ht, hf0, mul_zero]

/-- The literal scaled diagonal windows give a subsequential large-time limit
for the tested source trace defect. No moment bound on the trace is used. -/
theorem exists_subseq_ae_tendsto_canonical_largeTime
    [Fact (2 ≤ d)] {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀)
    (ω₀ : PhysicalField d L) (i : Fin d)
    {φ : Corrector (actualCoefficientLaw Q) (correctorUnitVector i).ofLp}
    (S : FluxCorrector φ) {ψ : Vec d → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ) (j : Fin d) :
    ∃ η : ℕ → ℕ, StrictMono η ∧ ∀ᵐ ρ ∂reducedEnvironmentLaw Q,
      Tendsto (fun k => horizontalMollify ψ
        (heatSmoothed (r₀ ^ 2 * ((η k + 1 : ℕ) : ℝ)) (fun ω =>
          (canonicalCorrectorFlux Q i ω - expectedCorrectorFlux Q i).ofLp j)) ρ)
        atTop (𝓝 (horizontalMollify ψ (fun ω =>
          (canonicalCorrectorFlux Q i ω - expectedCorrectorFlux Q i).ofLp j) ρ -
            c6ReducedSourceTracePairing Q ω₀ S ψ j ρ)) := by
  let f : FieldPair d → ℝ := fun ω =>
    (canonicalCorrectorFlux Q i ω - expectedCorrectorFlux Q i).ofLp j
  have hf : Measurable f := (measurable_pi_apply j).comp
    (canonical_flux_source_measurable_memLp Q i).1
  have hf2 : MemLp f 2 (reducedEnvironmentLaw Q) :=
    (canonical_flux_source_measurable_memLp Q i).2 j
  have hr : 0 < r₀ := zero_lt_one.trans_le Q.range_parameter
  have hr2 : 0 < r₀ ^ 2 := sq_pos_of_pos hr
  have hsmall : Tendsto (fun m : ℕ => r₀ ^ 2 * ((m + 1 : ℕ) : ℝ)⁻¹) atTop (𝓝 0) := by
    have h : Tendsto (fun m : ℕ => ((m + 1 : ℕ) : ℝ)⁻¹) atTop (𝓝 0) := by
      simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using
        tendsto_inv_atTop_zero.comp
          (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
    simpa only [mul_zero] using h.const_mul (r₀ ^ 2)
  apply exists_subseq_ae_tendsto_of_sub (μ := reducedEnvironmentLaw Q)
    (X := fun mn ρ => ∫ x, (∑ k : Fin d, heatWindowGradient
      (fun y => (canonicalCorrectorFlux Q i (translate y ρ)).ofLp -
        (expectedCorrectorFlux Q i).ofLp)
      (r₀ ^ 2 * ((mn.1 + 1 : ℕ) : ℝ)⁻¹) (r₀ ^ 2 * ((mn.2 + 1 : ℕ) : ℝ)) j k k x) * ψ x)
    (A := fun m => horizontalMollify ψ
      (heatSmoothed (r₀ ^ 2 * ((m + 1 : ℕ) : ℝ)⁻¹) f))
    (B := fun n => horizontalMollify ψ (heatSmoothed (r₀ ^ 2 * ((n + 1 : ℕ) : ℝ)) f))
    (Y := c6ReducedSourceTracePairing Q ω₀ S ψ j)
    (A' := horizontalMollify ψ f)
    (fun m => (measurable_horizontalMollify ψ hψ.continuous.measurable
      ((measurable_heatSmoothed_joint hf).comp
        (measurable_const.prodMk measurable_id))).aestronglyMeasurable)
    (measurable_horizontalMollify ψ hψ.continuous.measurable hf).aestronglyMeasurable
  · intro m n
    exact ae_canonical_testPairing_window_diag Q i hψ hψc _ _ (by positivity) (by
      apply mul_le_mul_of_nonneg_left _ hr2.le
      have h1 : ((m + 1 : ℕ) : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by norm_cast; omega)
      exact h1.trans (by norm_cast; omega)) j
  · filter_upwards [c6ReducedSourceTracePairing_heat_limit Q ω₀ i S] with ρ hρ
    exact hρ ψ hψ.continuous hψc j
  · exact tendsto_eLpNorm_horizontalMollify_heatSmoothed_smallTime_sub
      (reducedEnvironmentLaw Q) (reducedEnvironmentLaw_stationary Q)
      (hψ.of_le (by norm_cast)) hψc hf (hf2.integrable one_le_two)
      _ (fun _ => by positivity) hsmall

/-- Translation merging forces any almost-sure subsequential limit to be invariant. -/
theorem ae_invariant_of_subseq_tendsto_of_translate_merging
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q] (hQ : IsStationary Q)
    {B : ℕ → FieldPair d → ℝ} (hB : ∀ n, Measurable (B n))
    {Y : FieldPair d → ℝ} {η : ℕ → ℕ} (hη : StrictMono η)
    (hlim : ∀ᵐ ρ ∂Q, Tendsto (fun k => B (η k) ρ) atTop (𝓝 (Y ρ)))
    (hmerge : ∀ z : Vec d, Tendsto (fun n => eLpNorm
      (fun ρ => B n (translate z ρ) - B n ρ) 1 Q) atTop (𝓝 0)) :
    ∀ z : Vec d, (fun ρ => Y (translate z ρ)) =ᵐ[Q] Y := by
  intro z
  have hlimz := (measurePreserving_translate Q hQ z).quasiMeasurePreserving.ae hlim
  have hdiff : ∀ᵐ ρ ∂Q, Tendsto (fun k =>
      B (η k) (translate z ρ) - B (η k) ρ) atTop (𝓝 (Y (translate z ρ) - Y ρ)) := by
    filter_upwards [hlimz, hlim] with ρ hz hρ using hz.sub hρ
  have heq := ae_eq_of_subseq_tendsto_ae_of_tendsto_eLpNorm_one
    (B := fun n ρ => B n (translate z ρ) - B n ρ) (Z := fun _ => 0)
    (fun n => ((hB n).comp (Probability.measurable_translate z)).sub
      (hB n) |>.aestronglyMeasurable) aestronglyMeasurable_const hη hdiff
    (by simpa only [sub_zero] using hmerge z)
  filter_upwards [heq] with ρ hρ using sub_eq_zero.mp hρ

/-- The literal reduced law inherits the physical translation zero-one law. -/
theorem reducedLaw_zero_one_of_translate_invariant
    {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀) (hd : 2 ≤ d)
    {A : Set (FieldPair d)} (hA : MeasurableSet A)
    (hinv : ∀ z : Vec d, ∀ᵐ ρ ∂reducedEnvironmentLaw Q,
      (translate z ρ ∈ A ↔ ρ ∈ A)) :
    reducedEnvironmentLaw Q A = 0 ∨ reducedEnvironmentLaw Q A = 1 := by
  have hmass : reducedEnvironmentLaw Q A = Q.measure (reduce ⁻¹' A) :=
    Measure.map_apply Probability.measurable_reduce hA
  rw [hmass]
  apply Localization.environmentLaw_translation_ergodic Q hd (reduce ⁻¹' A)
    (Probability.measurable_reduce hA)
  intro z
  have hz := ae_of_ae_map Probability.measurable_reduce.aemeasurable (hinv z)
  filter_upwards [hz] with ω hω
  simpa only [Set.mem_preimage, reduce_translate] using hω

/-- Translation-invariant integrable observables of mean zero vanish under the
actual reduced law. -/
theorem ae_eq_zero_of_translate_invariant_of_integral_eq_zero
    {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀) (hd : 2 ≤ d)
    {H : FieldPair d → ℝ} (hH : Measurable H)
    (hinv : ∀ z : Vec d, (fun ρ => H (translate z ρ)) =ᵐ[reducedEnvironmentLaw Q] H)
    (hmean : ∫ ρ, H ρ ∂reducedEnvironmentLaw Q = 0) :
    H =ᵐ[reducedEnvironmentLaw Q] fun _ => 0 := by
  have h_ae_cond (U : Set ℝ) (hU : MeasurableSet U) :
      (∀ᶠ ρ in ae (reducedEnvironmentLaw Q), H ρ ∈ U) ∨
        (∀ᶠ ρ in ae (reducedEnvironmentLaw Q), H ρ ∉ U) := by
    have hpre : MeasurableSet (H ⁻¹' U) := hH hU
    have h01 := reducedLaw_zero_one_of_translate_invariant Q hd hpre (fun z => by
      filter_upwards [hinv z] with ρ hρ
      change H (translate z ρ) ∈ U ↔ H ρ ∈ U
      rw [hρ])
    rcases h01 with h | h
    · right
      rw [ae_iff]
      simpa only [not_not, Set.preimage] using h
    · left
      rw [ae_iff]
      have htotal := measure_add_measure_compl (μ := reducedEnvironmentLaw Q) hpre
      rw [h, measure_univ] at htotal
      have hz : reducedEnvironmentLaw Q ((H ⁻¹' U)ᶜ) = 0 :=
        (ENNReal.add_right_inj ENNReal.one_ne_top).mp (by simpa only [add_zero] using htotal)
      exact hz
  obtain ⟨c, hc⟩ := Filter.exists_eventuallyEq_const_of_forall_separating
    (l := ae (reducedEnvironmentLaw Q)) MeasurableSet h_ae_cond
  have hc0 : c = 0 := by
    calc c = ∫ _ : FieldPair d, c ∂reducedEnvironmentLaw Q := by simp
      _ = ∫ ρ, H ρ ∂reducedEnvironmentLaw Q := by
        apply integral_congr_ae
        filter_upwards [hc] with ρ hρ using hρ.symm
      _ = 0 := hmean
  simpa only [hc0, Function.const_def] using hc

/-- Every smooth compactly supported test identifies the reduced source trace.
The large-time defect vanishes by translation merging and ergodicity. -/
theorem ae_canonical_tested_source_trace
    [Fact (2 ≤ d)] {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀)
    (ω₀ : PhysicalField d L) (i : Fin d)
    {φ : Corrector (actualCoefficientLaw Q) (correctorUnitVector i).ofLp}
    (S : FluxCorrector φ) {ψ : Vec d → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ) (j : Fin d) :
    c6ReducedSourceTracePairing Q ω₀ S ψ j =ᵐ[reducedEnvironmentLaw Q]
      horizontalMollify ψ (fun ω =>
        (canonicalCorrectorFlux Q i ω - expectedCorrectorFlux Q i).ofLp j) := by
  let f : FieldPair d → ℝ := fun ω =>
    (canonicalCorrectorFlux Q i ω - expectedCorrectorFlux Q i).ofLp j
  let B : ℕ → FieldPair d → ℝ := fun n =>
    horizontalMollify ψ (heatSmoothed (r₀ ^ 2 * ((n + 1 : ℕ) : ℝ)) f)
  let Y : FieldPair d → ℝ := fun ρ =>
    horizontalMollify ψ f ρ - c6ReducedSourceTracePairing Q ω₀ S ψ j ρ
  have hf : Measurable f := (measurable_pi_apply j).comp
    (canonical_flux_source_measurable_memLp Q i).1
  have hf2 := (canonical_flux_source_measurable_memLp Q i).2 j
  have hf0 := integral_canonicalCenteredFlux_coord Q i j
  have hB (n : ℕ) : Measurable (B n) := measurable_horizontalMollify ψ
    hψ.continuous.measurable ((measurable_heatSmoothed_joint hf).comp
      (measurable_const.prodMk measurable_id))
  have hY : Measurable Y := (measurable_horizontalMollify ψ hψ.continuous.measurable hf).sub
    (c6ReducedSourceTracePairing_measurable Q ω₀ S hψ.continuous.measurable j)
  obtain ⟨η, hη, hlim⟩ := exists_subseq_ae_tendsto_canonical_largeTime Q ω₀ i S hψ hψc j
  have hbm (n : ℕ) := horizontalMollify_heatSmoothed_bound_mean
    (reducedEnvironmentLaw Q) (reducedEnvironmentLaw_stationary Q) hψ.continuous.measurable
    (hψ.continuous.integrable_of_hasCompactSupport hψc) hf hf2 hf0
    (r₀ ^ 2 * ((n + 1 : ℕ) : ℝ)) (by positivity)
  have hmean : ∫ ρ, Y ρ ∂reducedEnvironmentLaw Q = 0 :=
    (integral_eq_zero_of_tendsto_ae_of_eLpNorm_two_le
      (fun k => (hB (η k)).aestronglyMeasurable)
      (fun k => (hbm (η k)).1) (fun k => (hbm (η k)).2) hlim).2
  have hinv : ∀ z : Vec d, (fun ρ => Y (translate z ρ)) =ᵐ[reducedEnvironmentLaw Q] Y := by
    apply ae_invariant_of_subseq_tendsto_of_translate_merging
      (reducedEnvironmentLaw Q) (reducedEnvironmentLaw_stationary Q) hB hη hlim
    intro z
    have hr2 : 0 < r₀ ^ 2 := sq_pos_of_pos (zero_lt_one.trans_le Q.range_parameter)
    have hcast : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) atTop atTop := by
      simpa only [Nat.cast_add, Nat.cast_one] using
        (tendsto_natCast_atTop_atTop.atTop_add (tendsto_const_nhds (x := (1 : ℝ))))
    have hbt : Tendsto (fun n : ℕ => r₀ ^ 2 * ((n + 1 : ℕ) : ℝ)) atTop atTop :=
      hcast.const_mul_atTop hr2
    have h := tendsto_eLpNorm_horizontalMollify_heatSmoothed_largeTime_translate_sub
      (reducedEnvironmentLaw Q) (reducedEnvironmentLaw_stationary Q)
      hψ.continuous hψc hf (hf2.integrable one_le_two) z
      (fun n => r₀ ^ 2 * ((n + 1 : ℕ) : ℝ)) (fun n => by positivity) hbt
    convert h using 1
    funext n
    congr 1
    funext ρ
    change horizontalMollify ψ _ (translate z ρ) - _ = _
    rw [← horizontalMollify_comp_translate]
    unfold B horizontalMollify
    simp only [translate_add, add_comm z]
  have hzero := ae_eq_zero_of_translate_invariant_of_integral_eq_zero Q Fact.out hY hinv hmean
  filter_upwards [hzero] with ρ hρ
  exact (sub_eq_zero.mp hρ).symm

/-- Testing separately almost surely against every smooth compactly supported
function identifies two jointly measurable locally integrable fields. A countable
sequence of translated normalized bumps supplies the common spatial event. -/
theorem ae_ae_eq_of_ae_testPairing_eq
    {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω) [SFinite Q]
    {G H : Ω → Vec d → ℝ}
    (hG : Measurable (fun p : Ω × Vec d => G p.1 p.2))
    (hH : Measurable (fun p : Ω × Vec d => H p.1 p.2))
    (hGloc : ∀ᵐ ω ∂Q, LocallyIntegrable (G ω) volume)
    (hHloc : ∀ᵐ ω ∂Q, LocallyIntegrable (H ω) volume)
    (htest : ∀ ψ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      ∀ᵐ ω ∂Q, (∫ x, G ω x * ψ x) = ∫ x, H ω x * ψ x) :
    ∀ᵐ ω ∂Q, G ω =ᵐ[volume] H ω := by
  let K : ℕ → Vec d → ℝ := fun n => (representativeBump d n).normed volume
  have hK (n : ℕ) : Continuous (K n) := (representativeBump d n).continuous_normed
  have hm (F : Ω → Vec d → ℝ)
      (hF : Measurable (fun p : Ω × Vec d => F p.1 p.2)) (n : ℕ) :
      Measurable (fun p : Vec d × Ω => ∫ y, K n (p.1 - y) * F p.2 y) := by
    have hi : Measurable (fun p : (Vec d × Ω) × Vec d =>
        K n (p.1.1 - p.2) * F p.1.2 p.2) :=
      ((hK n).measurable.comp ((measurable_fst.comp measurable_fst).sub measurable_snd)).mul
        (hF.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
    exact hi.stronglyMeasurable.integral_prod_right'.measurable
  have hn (n : ℕ) : ∀ᵐ ω ∂Q, ∀ᵐ z ∂(volume : Measure (Vec d)),
      (∫ y, K n (z - y) * G ω y) = ∫ y, K n (z - y) * H ω y := by
    have hset := measurableSet_eq_fun (hm G hG n) (hm H hH n)
    apply (Measure.ae_ae_comm (μ := (volume : Measure (Vec d))) (ν := Q) hset).mp
    apply ae_of_all
    intro z
    have hψ : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec d => K n (z - y)) :=
      (representativeBump d n).contDiff_normed.comp (contDiff_const.sub contDiff_id)
    have hψc : HasCompactSupport (fun y : Vec d => K n (z - y)) :=
      (representativeBump d n).hasCompactSupport_normed.comp_homeomorph (Homeomorph.subLeft z)
    filter_upwards [htest _ hψ hψc] with ω hω
    simpa only [mul_comm] using hω
  filter_upwards [hGloc, hHloc, ae_all_iff.mpr hn] with ω hGω hHω hω
  filter_upwards [ae_tendsto_originBumpAverage hGω, ae_tendsto_originBumpAverage hHω,
    ae_all_iff.mpr hω] with z hGz hHz hz
  have heq : (fun n => ((representativeBump d n).normed volume ⋆[
      ContinuousLinearMap.lsmul ℝ ℝ, volume] G ω) z) =
      fun n => ((representativeBump d n).normed volume ⋆[
        ContinuousLinearMap.lsmul ℝ ℝ, volume] H ω) z := by
    funext n
    rw [convolution_eq_swap, convolution_eq_swap]
    simpa only [ContinuousLinearMap.lsmul_apply, smul_eq_mul] using hz n
  rw [heq] at hGz
  exact tendsto_nhds_unique hGz hHz

end C6TraceHeatSupport

/-- In original physical coordinates every smooth compact test pairs the source
row trace with the actual centered flux. Both scaling factors cancel exactly. -/
theorem c6_actualSource_trace_testPairing
    {d : ℕ} [Fact (2 ≤ d)] {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀) (i : Fin d)
    (φ : Corrector (actualCoefficientLaw Q) (correctorUnitVector i).ofLp)
    (S : FluxCorrector φ) {ψ : Vec d → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ) (j : Fin d) :
    ∀ᵐ ω ∂physicalReferenceLaw Q,
      (∫ x, c6SourceRowDivergence S (project (r₀ := r₀) Q.ellipticity_parameter ω) x j * ψ x) =
        ∫ x, centeredFlux φ (project (r₀ := r₀) Q.ellipticity_parameter ω) x j * ψ x := by
  letI : IsProbabilityMeasure (physicalReferenceLaw Q) := physicalReferenceLaw_probability Q
  let ω₀ : PhysicalField d L := (nonempty_of_isProbabilityMeasure (physicalReferenceLaw Q)).some
  let f : FieldPair d → ℝ := fun ρ =>
    (canonicalCorrectorFlux Q i ρ - expectedCorrectorFlux Q i).ofLp j
  have hr : 0 < r₀ := zero_lt_one.trans_le Q.range_parameter
  have hs : ellipticityScale L ≠ 0 := (ellipticityScale_pos Q.ellipticity_parameter).ne'
  have hψr : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec d => ψ (r₀⁻¹ • y)) :=
    hψ.comp (contDiff_const_smul r₀⁻¹)
  have hψrc : HasCompactSupport (fun y : Vec d => ψ (r₀⁻¹ • y)) :=
    hψc.comp_smul (inv_ne_zero hr.ne')
  have hred := C6TraceHeatSupport.ae_canonical_tested_source_trace Q ω₀ i S hψr hψrc j
  have hphys := (measurePreserving_physicalReduction Q).quasiMeasurePreserving.ae hred
  filter_upwards [hphys, c6_actualSourceCenteredFlux_canonical Q i φ] with ω hω hflux
  have hscaled : (r₀ ^ d / ellipticityScale L) *
      (∫ x, c6SourceRowDivergence S (project (r₀ := r₀) Q.ellipticity_parameter ω) x j * ψ x) =
      ∫ y, f (translate y (reduce ω.1)) * ψ (r₀⁻¹ • y) := by
    simpa only [c6ReducedSourceTracePairing, c6_physicalOfReduced_reduce,
      horizontalMollify, f, smul_smul, inv_mul_cancel₀ hr.ne', one_smul, mul_comm] using hω
  have hdil := c6_testPairing_dilation (fun y => f (translate y (reduce ω.1))) ψ r₀ hr
  have hsource : (∫ x, centeredFlux φ (project (r₀ := r₀) Q.ellipticity_parameter ω) x j * ψ x) =
      ellipticityScale L * ∫ x, f (translate (r₀ • x) (reduce ω.1)) * ψ x := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [hflux] with x hx
    have hj := congrFun hx j
    change centeredFlux φ (project (r₀ := r₀) Q.ellipticity_parameter ω) x j =
      ellipticityScale L * f (translate (r₀ • x) (reduce ω.1)) at hj
    rw [hj]
    ring
  rw [hsource, hdil]
  rw [← hscaled]
  field_simp

/-- The measurable coefficient reconstruction gives a jointly measurable
representative of the actual centered flux. -/
def c6CenteredFluxRepresentative {d : ℕ} {K : ℝ} {P : Measure (Coefficient d K)}
    {e : Vec d} (φ : Corrector P e) (a : Coefficient d K) (x : Vec d) : Vec d :=
  (coefficientRepresentative a x).mulVec (e + φ.grad a x) - meanFlux φ

theorem c6CenteredFluxRepresentative_measurable {d : ℕ} {K : ℝ}
    {P : Measure (Coefficient d K)} {e : Vec d} (φ : Corrector P e) :
    Measurable (fun p : Coefficient d K × Vec d => c6CenteredFluxRepresentative φ p.1 p.2) := by
  exact ((show Continuous (fun p : Mat d × Vec d => p.1.mulVec p.2) from
    continuous_fst.matrix_mulVec continuous_snd).measurable.comp
      (measurable_coefficientRepresentative.prodMk (measurable_const.add φ.measurable_grad))).sub
        measurable_const

theorem c6CenteredFluxRepresentative_ae_eq {d : ℕ} {K : ℝ}
    {P : Measure (Coefficient d K)} {e : Vec d} (φ : Corrector P e) (a : Coefficient d K) :
    c6CenteredFluxRepresentative φ a =ᵐ[volume] centeredFlux φ a := by
  filter_upwards [coefficientRepresentative_ae_eq a] with x hx
  simp only [c6CenteredFluxRepresentative, centeredFlux, hx]

/-- The source-law test identity uses measurable representatives solely to
transport the almost-everywhere event; the spatial centered flux is unchanged. -/
theorem c6_sourceLaw_trace_testPairing
    {d : ℕ} [Fact (2 ≤ d)] {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀) (i : Fin d)
    (φ : Corrector (actualCoefficientLaw Q) (correctorUnitVector i).ofLp)
    (S : FluxCorrector φ) {ψ : Vec d → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ) (j : Fin d) :
    ∀ᵐ a ∂actualCoefficientLaw Q,
      (∫ x, c6SourceRowDivergence S a x j * ψ x) =
        ∫ x, c6CenteredFluxRepresentative φ a x j * ψ x := by
  have hm (F : Coefficient d (AKMUpperEllipticity L) → Vec d → Vec d)
      (hF : Measurable (fun p : Coefficient d (AKMUpperEllipticity L) × Vec d => F p.1 p.2)) :
      Measurable (fun a => ∫ x, F a x j * ψ x) :=
    ((((measurable_pi_apply j).comp hF).mul
      (hψ.continuous.measurable.comp measurable_snd)).stronglyMeasurable.integral_prod_right').measurable
  have hset := measurableSet_eq_fun (hm _ (c6SourceRowDivergence_measurable S))
    (hm _ (c6CenteredFluxRepresentative_measurable φ))
  apply (ae_map_iff (measurable_project (r₀ := r₀) Q.ellipticity_parameter).aemeasurable hset).mpr
  filter_upwards [c6_actualSource_trace_testPairing Q i φ S hψ hψc j] with ω hω
  refine hω.trans ?_
  apply integral_congr_ae
  filter_upwards [c6CenteredFluxRepresentative_ae_eq φ
    (project (r₀ := r₀) Q.ellipticity_parameter ω)] with x hx
  rw [hx]

/-- The actual heat-selected row trace equals the centered flux of the given
source corrector almost everywhere in both the coefficient and spatial laws.
The smooth-bounds binder is retained from the prescribed contract. -/
@[nolint unusedArguments]
theorem sublinear_source_flux_column_trace
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (hQ : HasSmoothBounds D Q) (i : Fin d)
    (φ : Corrector (actualCoefficientLaw Q) (correctorUnitVector i).ofLp)
    (S : FluxCorrector φ) :
    ∀ᵐ a ∂actualCoefficientLaw Q, ∀ᵐ x ∂(volume : Measure (Vec d)),
      c6SourceRowDivergence S a x = centeredFlux φ a x := by
  letI : Fact (2 ≤ d) := ⟨hd⟩
  letI : IsProbabilityMeasure (actualCoefficientLaw Q) := (lawHypotheses_actualCoefficientLaw Q).1
  have hGloc := c6SourceRowDivergence_divergence_free S
  have hHloc := c6_centeredFlux_divergence_free φ
  have hcoord (j : Fin d) : ∀ᵐ a ∂actualCoefficientLaw Q,
      (fun x => c6SourceRowDivergence S a x j) =ᵐ[volume]
        fun x => c6CenteredFluxRepresentative φ a x j := by
    apply C6TraceHeatSupport.ae_ae_eq_of_ae_testPairing_eq (actualCoefficientLaw Q)
      ((measurable_pi_apply j).comp (c6SourceRowDivergence_measurable S))
      ((measurable_pi_apply j).comp (c6CenteredFluxRepresentative_measurable φ))
    · filter_upwards [hGloc] with a ha
      exact locallyIntegrableOn_univ.mp (ha.1 j)
    · filter_upwards [hHloc] with a ha
      apply (locallyIntegrableOn_univ.mp (ha.1 j)).congr
      filter_upwards [c6CenteredFluxRepresentative_ae_eq φ a] with x hx
      exact (congrFun hx j).symm
    · intro ψ hψ hψc
      exact c6_sourceLaw_trace_testPairing Q i φ S hψ hψc j
  filter_upwards [ae_all_iff.mpr hcoord] with a ha
  filter_upwards [ae_all_iff.mpr ha, c6CenteredFluxRepresentative_ae_eq φ a] with x hx hrep
  exact (funext hx).trans hrep
end EinsteinFull.Blueprint
