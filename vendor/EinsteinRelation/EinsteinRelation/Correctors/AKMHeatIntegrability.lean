import EinsteinRelation.Correctors.AKMFluxIdentification
import EinsteinRelation.Correctors.CanonicalEnergyIntegrability

/-!
# Gaussian integrability after AKM gradient identification

Source: `paper/main.tex:727-729`; AKM (4.4), p. 124. The canonical L²
bound supplies Gaussian integrability of the squared affine gradient.
After a full-space spatial identification, this transfers to the source
corrector and bounds its energy using normalized ellipticity. The
coefficient sigma algebra only needs to observe the measurable gradient;
joint measurability of pointwise coefficient evaluation is not assumed.
-/

open MeasureTheory

noncomputable section

namespace EinsteinRelation.Correctors

open External.AKM Environment.AKMTestIntegralSupport ReductionImageV3

private theorem euclideanSq_ofLp {d : ℕ} (x : EuclideanSpace ℝ (Fin d)) :
    euclideanSq x.ofLp = ‖x‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [euclideanSq, dot, Real.norm_eq_abs, pow_two]

/-- Gaussian-weighted squared affine gradients are samplewise integrable
at every deterministic spatial scale. Only the canonical L² bound is used. -/
theorem ae_integrable_heat_canonical_affineNormSq {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) (i : Fin d) (c : ℝ) :
    ∀ᵐ ω ∂reducedEnvironmentLaw Q, Integrable (fun y : Vec d =>
      heatKernel 0 1 y * euclideanSq (correctorUnitVector i + (canonicalCorrectorGradient Q i :
        Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
          (translate (c • y) ω)).ofLp) volume := by
  let G := (canonicalCorrectorGradient Q i :
    Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
  let F : FieldPair d → ℝ := fun ω => ‖correctorUnitVector i + G ω‖ ^ 2
  have hXm : Measurable (fun ω : FieldPair d => correctorUnitVector i + G ω) :=
    measurable_const.add (Lp.stronglyMeasurable G).measurable
  have hF : Measurable F := hXm.norm.pow_const 2
  have hX : MemLp (fun ω => correctorUnitVector i + G ω) 2 (reducedEnvironmentLaw Q) :=
    (memLp_const (correctorUnitVector i)).add (Lp.memLp G)
  have hFi : Integrable F (reducedEnvironmentLaw Q) :=
    (memLp_two_iff_integrable_sq_norm hX.aestronglyMeasurable).mp hX
  have hw : Measurable (euclideanHeatKernel (d := d) 1) := by
    unfold euclideanHeatKernel euclideanSq dot
    fun_prop
  have hσ : Measurable (fun y : Vec d => c • y) :=
    (continuous_id.const_smul c).measurable
  have h := integrable_weighted_stationary_prod (reducedEnvironmentLaw Q)
    (reducedEnvironmentLaw_stationary Q) volume hF hFi hw
    (Clock.integrable_euclideanHeatKernel (by norm_num : (0 : ℝ) < 1)) hσ
  simpa only [smul_eq_mul, euclideanSq_ofLp, heatKernel, one_pow, sub_zero]
    using h.prod_left_ae

/-- On the AKM carrier, heat-integrability of the squared affine gradient
implies heat-integrability of its energy. Only spatial measurability of
each coefficient is needed. -/
theorem akm_heat_energy_integrable_of_gradient {d : ℕ} {K : ℝ}
    (a : Coefficient d K) (e : Vec d) {g : Vec d → Vec d} (hg : Measurable g)
    (hi : Integrable (fun y => heatKernel 0 1 y * euclideanSq (e + g y)) volume) :
    Integrable (fun y => heatKernel 0 1 y * ((1 / 2 : ℝ) *
      dot (e + g y) ((a y).mulVec (e + g y)))) volume := by
  have ha : AEMeasurable (fun y => a y) volume := by
    change @AEMeasurable (Vec d) (Fin d → Fin d → ℝ)
      (borel (Fin d → Fin d → ℝ)) inferInstance a.field volume
    rw [← @BorelSpace.measurable_eq (Fin d → Fin d → ℝ) _ MeasurableSpace.pi inferInstance]
    exact AEMeasurable.of_eval fun j => AEMeasurable.of_eval fun k =>
      (a.locally_integrable j k).aestronglyMeasurable.aemeasurable
  have hE : Continuous (fun p : Mat d × Vec d =>
      (1 / 2 : ℝ) * dot p.2 (p.1.mulVec p.2)) := by
    unfold dot Matrix.mulVec dotProduct
    fun_prop
  have hw : Measurable (heatKernel (d := d) 0 1) := by
    unfold heatKernel euclideanHeatKernel euclideanSq dot
    fun_prop
  have hv : Measurable (fun y => e + g y) := measurable_const.add hg
  have hM : AEMeasurable (fun y => heatKernel 0 1 y * ((1 / 2 : ℝ) *
      dot (e + g y) ((a y).mulVec (e + g y)))) volume :=
    hw.aemeasurable.mul (hE.measurable.comp_aemeasurable (ha.prodMk hv.aemeasurable))
  refine (hi.const_mul (K / 2)).mono' hM.aestronglyMeasurable (ae_of_all _ fun y => ?_)
  have hsq : 0 ≤ euclideanSq (e + g y) := by
    unfold euclideanSq dot
    exact Finset.sum_nonneg fun j _ => mul_self_nonneg _
  have hq : 0 ≤ dot (e + g y) ((a y).mulVec (e + g y)) :=
    hsq.trans (a.elliptic y (e + g y)).1
  have hw0 : 0 ≤ heatKernel (d := d) 0 1 y := by
    unfold heatKernel euclideanHeatKernel
    positivity
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hw0 (mul_nonneg (by norm_num) hq))]
  nlinarith [mul_le_mul_of_nonneg_left (a.elliptic y (e + g y)).2 hw0]

/-- The source corrector's Gaussian-integrability field is a consequence
of a full-space gradient identification, with no extra external input. -/
theorem akm_heat_integrable_of_global_gradient_identification {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) (i : Fin d)
    (φ : Corrector (actualCoefficientLaw Q) (halfDirection i))
    (hid : ∀ᵐ ω ∂physicalReferenceLaw Q, ∀ᵐ y ∂(volume : Measure (Vec d)),
      (2 : ℝ) • (halfDirection i + φ.grad (project (r₀ := r₀) Q.ellipticity_parameter ω) y) =
        (correctorUnitVector i + (canonicalCorrectorGradient Q i :
          Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
            (translate (r₀ • y) (reduce ω.1))).ofLp) :
    ∀ᵐ a ∂actualCoefficientLaw Q, Integrable (fun y => heatKernel 0 1 y * ((1 / 2 : ℝ) *
      dot (halfDirection i + φ.grad a y) ((a y).mulVec (halfDirection i + φ.grad a y))))
      volume := by
  let f := fun (a : Coefficient d (AKMUpperEllipticity L)) (y : Vec d) =>
    heatKernel 0 1 y * euclideanSq (halfDirection i + φ.grad a y)
  have hm : Measurable (Function.uncurry f) := by
    have hg := φ.measurable_grad
    have hw : Measurable (fun p : Coefficient d (AKMUpperEllipticity L) × Vec d =>
        heatKernel 0 1 p.2) := by
      unfold heatKernel euclideanHeatKernel euclideanSq dot
      fun_prop
    have hs : Continuous (fun v : Vec d => euclideanSq (halfDirection i + v)) := by
      unfold euclideanSq dot
      fun_prop
    exact hw.mul (hs.measurable.comp hg)
  have hset : MeasurableSet {a | Integrable (f a) volume} :=
    measurableSet_integrable hm.stronglyMeasurable
  have hnorm := (measurePreserving_physicalReduction Q).quasiMeasurePreserving.ae
    (ae_integrable_heat_canonical_affineNormSq Q i r₀)
  have hphys : ∀ᵐ ω ∂physicalReferenceLaw Q,
      Integrable (f (project (r₀ := r₀) Q.ellipticity_parameter ω)) volume := by
    filter_upwards [hid, hnorm] with ω hω hn
    apply (hn.const_mul (1 / 4 : ℝ)).congr
    filter_upwards [hω] with y hy
    change (1 / 4 : ℝ) * (heatKernel 0 1 y * euclideanSq _) = _
    rw [← hy, euclideanSq_smul]
    dsimp [f]
    ring
  have hsource : ∀ᵐ a ∂actualCoefficientLaw Q, Integrable (f a) volume :=
    (ae_map_iff (measurable_project Q.ellipticity_parameter).aemeasurable hset).2 hphys
  filter_upwards [hsource] with a ha
  exact akm_heat_energy_integrable_of_gradient a (halfDirection i)
    (φ.measurable_grad.comp (measurable_const.prodMk measurable_id)) ha

end EinsteinRelation.Correctors

