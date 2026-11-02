import EinsteinRelation.Correctors.StationaryWeightedIntegrals
import EinsteinRelation.Clock.HeatCubeMasses

/-!
# Integrability of the canonical affine energy

Source: `paper/main.tex:693-698,727-729`. The canonical gradient and its
flux are L² fields, so their energy pairing is integrable. Stationarity
then gives spatial integrability with every integrable deterministic
weight, including the Gaussian after spatial rescaling. No higher moment
estimate or new external hypothesis is used.
-/

open MeasureTheory

noncomputable section

namespace EinsteinRelation.Correctors

private theorem measurable_affineEnergy {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) (i : Fin d) :
    Measurable (fun ω : FieldPair d => (1 / 2 : ℝ) *
      dot (correctorUnitVector i + (canonicalCorrectorGradient Q i :
        Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q)) ω).ofLp
        ((ω.1 0).mulVec (correctorUnitVector i + (canonicalCorrectorGradient Q i :
          Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q)) ω).ofLp)) := by
  have hG : Measurable (canonicalCorrectorGradient Q i :
      Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q)) :=
    (Lp.stronglyMeasurable _).measurable
  have hX : Measurable (fun ω => correctorUnitVector i + (canonicalCorrectorGradient Q i :
      Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q)) ω) :=
    measurable_const.add hG
  have hX' := (PiLp.continuous_ofLp (p := 2) (β := fun _ : Fin d => ℝ)).measurable.comp hX
  have ha : Measurable (fun ω : FieldPair d => ω.1 (0 : Vec d)) :=
    ((continuous_eval_const (0 : Vec d)).comp continuous_fst).measurable
  unfold dot Matrix.mulVec dotProduct
  fun_prop

/-- The literal coefficient energy of the canonical affine gradient is
integrable under the actual reduced law. -/
theorem integrable_canonical_affineEnergy {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) (i : Fin d) :
    Integrable (fun ω : FieldPair d => (1 / 2 : ℝ) *
      dot (correctorUnitVector i + (canonicalCorrectorGradient Q i :
        Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q)) ω).ofLp
        ((ω.1 0).mulVec (correctorUnitVector i + (canonicalCorrectorGradient Q i :
          Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q)) ω).ofLp))
      (reducedEnvironmentLaw Q) := by
  let G := (canonicalCorrectorGradient Q i :
    Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
  let X := correctorAffineField Q i + G
  have h := (L2.integrable_inner (𝕜 := ℝ) X (reducedOriginCoefficientAction Q X)).const_mul
    (1 / 2 : ℝ)
  apply h.congr
  filter_upwards [reducedOriginCoefficientAction_coeFn Q X,
    Lp.coeFn_add (correctorAffineField Q i) G,
    Lp.coeFn_const 2 (reducedEnvironmentLaw Q) (correctorUnitVector i)]
    with ω hA hsum hc
  have hX : X ω = correctorUnitVector i + G ω := by
    calc X ω = (correctorAffineField Q i) ω + G ω := hsum
      _ = correctorUnitVector i + G ω := by
        change (Lp.const 2 (reducedEnvironmentLaw Q) (correctorUnitVector i)) ω + G ω = _
        rw [hc]
        rfl
  congr 1
  rw [show inner ℝ (X ω) (reducedOriginCoefficientAction Q X ω) =
    dot (X ω).ofLp (reducedOriginCoefficientAction Q X ω).ofLp by
      simp [PiLp.inner_apply, dot, RCLike.inner_apply, mul_comm], hA, hX]

/-- Integrable deterministic weights give samplewise integrable canonical
energy, also when the spatial realization is rescaled. -/
theorem ae_integrable_weighted_canonical_affineEnergy {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) (i : Fin d) {w : Vec d → ℝ}
    (hw : Measurable w) (hwi : Integrable w volume)
    {σ : Vec d → Vec d} (hσ : Measurable σ) :
    ∀ᵐ ω ∂reducedEnvironmentLaw Q, Integrable (fun x : Vec d => w x * ((1 / 2 : ℝ) *
      dot (correctorUnitVector i + (canonicalCorrectorGradient Q i :
        Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q)) (translate (σ x) ω)).ofLp
        ((ω.1 (σ x)).mulVec (correctorUnitVector i + (canonicalCorrectorGradient Q i :
          Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
            (translate (σ x) ω)).ofLp))) volume := by
  have h := integrable_weighted_stationary_prod (reducedEnvironmentLaw Q)
    (reducedEnvironmentLaw_stationary Q) volume (measurable_affineEnergy Q i)
    (integrable_canonical_affineEnergy Q i) hw hwi hσ
  simpa only [smul_eq_mul, translate_matrix, add_zero] using h.prod_left_ae

/-- Gaussian-weighted canonical energy is integrable at every positive
time and every deterministic spatial scale. -/
theorem ae_integrable_heat_canonical_affineEnergy {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) (i : Fin d) {t : ℝ} (ht : 0 < t) (c : ℝ) :
    ∀ᵐ ω ∂reducedEnvironmentLaw Q, Integrable (fun x : Vec d =>
      euclideanHeatKernel t x * ((1 / 2 : ℝ) *
        dot (correctorUnitVector i + (canonicalCorrectorGradient Q i :
          Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q)) (translate (c • x) ω)).ofLp
          ((ω.1 (c • x)).mulVec (correctorUnitVector i + (canonicalCorrectorGradient Q i :
            Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
              (translate (c • x) ω)).ofLp))) volume := by
  have hw : Measurable (euclideanHeatKernel (d := d) t) := by
    unfold euclideanHeatKernel euclideanSq dot
    fun_prop
  exact ae_integrable_weighted_canonical_affineEnergy Q i hw
    (Clock.integrable_euclideanHeatKernel ht) (continuous_const_smul c).measurable

end EinsteinRelation.Correctors

