import EinsteinRelation.Mobility.VelocityRateFromSteps
import EinsteinRelation.Correctors.HeatSmoothingContraction
import EinsteinRelation.Correctors.StationarySpatialRealizationSupport
import EinsteinRelation.Clock.CentredClockField
import EinsteinRelation.Entropy.DivergenceFromFisher
import EinsteinRelation.Correctors.HomogenizedMatrixBounds
import EinsteinRelation.Correctors.StationaryGradientDomainSupport

/-! # The flux decay from the large-time estimate of AKM and the flux moments

Source: `paper/main.tex` 1107-1112 and Armstrong, Kuusi and Mourrat (2019), Theorem 4.1, estimate (4.3),
p. 124. That estimate holds for heat times `t = r² ≥ 1` only: with `Φ_{x,r} = Φ(r², · - x)` it bounds the
heat-kernel average of the centred flux by `O_s(C r^{-d/2})`, hence in every `L^m` by `C_m t^{-d/4}`, which
is at most `C_m (1 + t)^{-1/2}` up to a constant for `t ≥ 1` and `d ≥ 2`. For `0 ≤ t < 1` the bound follows
from the `L^m` moments of the centred flux and the `L^m` contraction of the heat smoothing.
`akmFluxDecay_of_largeTime` combines the two ranges into `AKMFluxDecay`.
-/

open MeasureTheory
open scoped ENNReal

namespace EinsteinRelation

open Correctors

/-- The first coordinate of the centred flux `g_i = a(e_i + ∇φ_i) - ā e_i` on the reduced space
(`paper/main.tex` 699-702), as in `AKMFluxDecay`. -/
noncomputable def centredFluxFirst {d : ℕ} {Λ₀ r₀ : ℝ} (hd : 2 ≤ d) (Q : EnvironmentLaw d Λ₀ r₀)
    (i : Fin d) (ω : FieldPair d) : ℝ :=
  (StationarySpatialRealization.spatialRealization (canonicalCorrectorFlux Q i) ((0 : Vec d), ω)).ofLp (firstIdx hd) -
    (expectedCorrectorFlux Q i).ofLp (firstIdx hd)

/-- Step `AKMFluxDecayLargeTime`, the estimate (4.3) of AKM Theorem 4.1 (p. 124) at heat times
`t ≥ 1`: `‖H_t (g_i)_1‖_{L^m(Q)} ≤ C_m (1 + t)^{-1/2}`, with `C` depending on `d`, `Λ₀`, `r₀`, `m`.

Hypotheses. AKM's standing assumptions (pp. xvii-xviii) are (0.6) `|ξ|² ≤ ξ·a(x)ξ ≤ Λ|ξ|²`,
(0.10) `ℤ^d`-stationarity and (0.11) unit range of dependence, with `d ≥ 2`. The reduced coefficient
law is `ℝ^d`-stationary, has range of dependence `r₀`, and is elliptic with constants in
`[Λ₀⁻¹ e^{-2Λ₀}, Λ₀ e^{2Λ₀}]`. AKM applies after the rescalings `x ↦ x / r₀` and `a ↦ c a`: the
correctors are unchanged, the flux and `ā` scale by `c`, and heat times scale by `r₀²`. The
constant therefore depends only on `d`, `Λ₀`, `r₀` and `m`, as in the quantifier order here.

Objects. AKM's first-order corrector `φ_e` (Sect. 3.4) has a stationary, mean-zero,
square-integrable gradient solving `-∇·a(e + ∇φ_e) = 0`, and `ā e = E[a(e + ∇φ_e)]`. Here the
flux is `canonicalCorrectorFlux Q i` and its mean `expectedCorrectorFlux Q i`, built from
`canonicalCorrectorGradient Q i`. The two agree by the uniqueness of the variational solution in the
potential domain (`existsUnique_canonicalCorrectorGradient_horizontalH1`), applied to `∇φ_{e_i}`
once it is placed in `correctorPotentialDomain`, the `L²` closure of horizontal gradients.

The range `t < 1`, which (4.3) does not cover, is proved from the flux moments in
`akmFluxDecay_of_largeTime`. -/
def AKMFluxDecayLargeTime : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ) (m : ℝ), 2 ≤ m →
    ∃ C : ℝ, ∀ (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (t : ℝ), 1 ≤ t →
      eLpNorm (heatSmoothed t (centredFluxFirst hd Q i)) (ENNReal.ofReal m)
        (Carriers.reducedReferenceLaw Q) ≤ ENNReal.ofReal (C * (Real.sqrt (1 + t))⁻¹)

/-- Step `CentredFluxMoments`: the first coordinate of the centred flux has finite `L^m` moments under
the reduced reference law, bounded uniformly in the environment law and the direction. -/
def CentredFluxMoments : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ) (m : ℝ), 2 ≤ m →
    ∃ C : ℝ, ∀ (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d),
      eLpNorm (centredFluxFirst hd Q i) (ENNReal.ofReal m) (Carriers.reducedReferenceLaw Q) ≤
        ENNReal.ofReal C

theorem measurable_centredFluxFirst {d : ℕ} {Λ₀ r₀ : ℝ} (hd : 2 ≤ d) (Q : EnvironmentLaw d Λ₀ r₀)
    (i : Fin d) : Measurable (centredFluxFirst hd Q i) := by
  have hcoord : Continuous fun x : EuclideanSpace ℝ (Fin d) => x.ofLp (firstIdx hd) :=
    (EuclideanSpace.proj (firstIdx hd)).continuous
  exact (hcoord.measurable.comp ((StationarySpatialRealization.measurable_spatialRealization (canonicalCorrectorFlux Q i)).comp
    (measurable_const.prodMk measurable_id))).sub_const _

/-- **`AKMFluxDecay`** from the large-time estimate of AKM and the flux moments. -/
theorem akmFluxDecay_of_largeTime (hL : AKMFluxDecayLargeTime) (hM : CentredFluxMoments) :
    AKMFluxDecay := by
  intro d hd Λ₀ r₀ m hm
  obtain ⟨C₁, h₁⟩ := hL d hd Λ₀ r₀ m hm
  obtain ⟨C₂, h₂⟩ := hM d hd Λ₀ r₀ m hm
  refine ⟨max C₁ (Real.sqrt 2 * max C₂ 0), fun Q i t ht => ?_⟩
  haveI : IsProbabilityMeasure (Carriers.reducedReferenceLaw Q) :=
    Entropy.reducedReferenceLaw_isProbabilityMeasure Q
  change eLpNorm (heatSmoothed t (centredFluxFirst hd Q i)) (ENNReal.ofReal m)
      (Carriers.reducedReferenceLaw Q) ≤ _
  have hs : 0 ≤ (Real.sqrt (1 + t))⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
  rcases le_or_gt 1 t with h1 | h1
  · refine (h₁ Q i t h1).trans (ENNReal.ofReal_le_ofReal ?_)
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) hs
  · have hcontr := eLpNorm_heatSmoothed_le (Carriers.reducedReferenceLaw Q)
      (Clock.isStationary_reducedReferenceLaw Q) (by linarith : (1 : ℝ) ≤ m)
      (measurable_centredFluxFirst hd Q i) ht
    refine hcontr.trans ((h₂ Q i).trans (ENNReal.ofReal_le_ofReal ?_))
    have hC : C₂ ≤ max C₂ 0 := le_max_left _ _
    have hsqrt : Real.sqrt (1 + t) ≤ Real.sqrt 2 := Real.sqrt_le_sqrt (by linarith)
    have hpos : 0 < Real.sqrt (1 + t) := Real.sqrt_pos.mpr (by linarith)
    have hratio : 1 ≤ Real.sqrt 2 * (Real.sqrt (1 + t))⁻¹ := by
      rw [← div_eq_mul_inv, one_le_div hpos]; exact hsqrt
    calc C₂ ≤ max C₂ 0 := hC
      _ ≤ max C₂ 0 * (Real.sqrt 2 * (Real.sqrt (1 + t))⁻¹) :=
          le_mul_of_one_le_right (le_max_right _ _) hratio
      _ = Real.sqrt 2 * max C₂ 0 * (Real.sqrt (1 + t))⁻¹ := by ring
      _ ≤ max C₁ (Real.sqrt 2 * max C₂ 0) * (Real.sqrt (1 + t))⁻¹ :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) hs

/-! ### The flux moments from the corrector gradient moments -/

/-- The first assertion of Lemma 5.1 (corrector.moments, `paper/main.tex` 704-713) in production
form: the canonical corrector gradient at the origin has `L^m` moments bounded uniformly in the
environment law and the direction. -/
def CorrectorGradientMoments : Prop :=
  ∀ (d : ℕ) (_ : 2 ≤ d) (Λ₀ r₀ : ℝ) (m : ℝ), 2 ≤ m → ∃ C : ℝ,
    ∀ (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d),
      ∫⁻ ω, ENNReal.ofReal
          (euclideanNorm
            ((StationarySpatialRealization.spatialRealization (canonicalCorrectorGradient Q i :
                Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
              ((0 : Vec d), ω)).ofLp) ^ m)
        ∂(reducedEnvironmentLaw Q) ≤ ENNReal.ofReal C

private theorem euclideanNorm_ofLp_eq_norm {d : ℕ} (x : EuclideanSpace ℝ (Fin d)) :
    euclideanNorm x.ofLp = ‖x‖ := by
  rw [EuclideanSpace.norm_eq]
  unfold euclideanNorm euclideanSq dot
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [Real.norm_eq_abs, pow_two]
  exact (abs_mul_abs_self (x.ofLp j)).symm

private theorem abs_coord_le_euclideanNorm {d : ℕ} (v : Vec d) (j : Fin d) :
    |v j| ≤ euclideanNorm v := by
  unfold euclideanNorm euclideanSq dot
  apply Real.abs_le_sqrt
  have h := Finset.single_le_sum (f := fun k => v k * v k)
    (fun k _ => mul_self_nonneg (v k)) (Finset.mem_univ j)
  simpa only [sq] using h

/-- **`CentredFluxMoments`** from the corrector gradient moments: `|(g_i)_1| ≤ K (1 + |∇φ_i|) + S`
with `K = e^{2Λ₀} Λ₀` the reduced ellipticity constant and `S` the bound on the columns of `ā`. -/
theorem centredFluxMoments_of_correctorGradientMoments (h : CorrectorGradientMoments) :
    CentredFluxMoments := by
  intro d hd Λ₀ r₀ m hm
  obtain ⟨C, hC⟩ := h d hd Λ₀ r₀ m hm
  set K : ℝ := Real.exp (2 * Λ₀) * Λ₀ with hKdef
  set S : ℝ := sourceReducedBound Λ₀ with hSdef
  set C' : ℝ := (max C 0) ^ (1 / m) with hC'def
  refine ⟨K * C' + (K + S), fun Q i => ?_⟩
  have hK0 : 0 ≤ K := mul_nonneg (Real.exp_pos _).le (le_trans zero_le_one Q.ellipticity_parameter)
  have hS0 : 0 ≤ S := le_trans zero_le_one (one_le_sourceReducedBound Q.ellipticity_parameter)
  have hC'0 : 0 ≤ C' := Real.rpow_nonneg (le_max_right _ _) _
  have hm0 : 0 < m := by linarith
  rw [Clock.reducedReferenceLaw_eq_reducedEnvironmentLaw]
  set μ := reducedEnvironmentLaw Q with hμ
  haveI : IsProbabilityMeasure μ := by
    rw [hμ, ← Clock.reducedReferenceLaw_eq_reducedEnvironmentLaw]
    exact Entropy.reducedReferenceLaw_isProbabilityMeasure Q
  set G : Lp (EuclideanSpace ℝ (Fin d)) 2 μ :=
    (canonicalCorrectorGradient Q i : Lp (EuclideanSpace ℝ (Fin d)) 2 μ) with hGdef
  -- The homogenized entry is bounded by `S`.
  have hSbound : |(expectedCorrectorFlux Q i).ofLp (firstIdx hd)| ≤ S := by
    have hcol := homogenizedMatrix_euclideanNorm_mulVec_unitVector_le Q i
    have hentry : (homogenizedMatrix Q).mulVec (unitVector i) (firstIdx hd) =
        (expectedCorrectorFlux Q i).ofLp (firstIdx hd) := by
      simp [homogenizedMatrix, unitVector, Matrix.mulVec, dotProduct, Pi.single_apply]
    rw [← hentry]
    exact (abs_coord_le_euclideanNorm _ _).trans hcol
  -- The pointwise bound `|(g_i)_1| ≤ K ‖∇φ_i‖ + (K + S)`.
  have hpt : ∀ᵐ ω ∂μ, ‖centredFluxFirst hd Q i ω‖ ≤ ‖K * ‖G ω‖ + (K + S)‖ := by
    filter_upwards [ae_norm_reducedOriginCoefficientAction_le Q (correctorAffineField Q i + G),
      Lp.coeFn_add (correctorAffineField Q i) G,
      Lp.coeFn_const (p := 2) (μ := μ) (correctorUnitVector i)] with ω h1 h2 h3
    have hflux : StationarySpatialRealization.spatialRealization (canonicalCorrectorFlux Q i)
        ((0 : Vec d), ω) = reducedOriginCoefficientAction Q (correctorAffineField Q i + G) ω := by
      simp only [StationarySpatialRealization.spatialRealization, translate_zero]
      rfl
    have hsum : ‖(correctorAffineField Q i + G) ω‖ ≤ 1 + ‖G ω‖ := by
      rw [h2]
      have haff : (correctorAffineField Q i) ω = correctorUnitVector i := h3
      rw [Pi.add_apply, haff]
      refine (norm_add_le _ _).trans ?_
      gcongr
      simp [correctorUnitVector]
    have hcoord : |(reducedOriginCoefficientAction Q (correctorAffineField Q i + G) ω).ofLp
        (firstIdx hd)| ≤ ‖reducedOriginCoefficientAction Q (correctorAffineField Q i + G) ω‖ := by
      rw [← euclideanNorm_ofLp_eq_norm]
      exact abs_coord_le_euclideanNorm _ _
    have hnonneg : 0 ≤ K * ‖G ω‖ + (K + S) := by positivity
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hnonneg]
    simp only [centredFluxFirst]
    rw [hflux]
    calc |(reducedOriginCoefficientAction Q (correctorAffineField Q i + G) ω).ofLp (firstIdx hd) -
          (expectedCorrectorFlux Q i).ofLp (firstIdx hd)|
        ≤ |(reducedOriginCoefficientAction Q (correctorAffineField Q i + G) ω).ofLp (firstIdx hd)| +
          |(expectedCorrectorFlux Q i).ofLp (firstIdx hd)| := abs_sub _ _
      _ ≤ K * (1 + ‖G ω‖) + S := add_le_add (hcoord.trans (h1.trans
          (mul_le_mul_of_nonneg_left hsum hK0))) hSbound
      _ = K * ‖G ω‖ + (K + S) := by ring
  -- The `L^m` norm of `‖∇φ_i‖`.
  have hp0 : ENNReal.ofReal m ≠ 0 := (ENNReal.ofReal_pos.mpr hm0).ne'
  have hptop : ENNReal.ofReal m ≠ ∞ := ENNReal.ofReal_ne_top
  have hGm : eLpNorm (fun ω => ‖G ω‖) (ENNReal.ofReal m) μ ≤ ENNReal.ofReal C' := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hptop (Lp.aestronglyMeasurable G).norm,
      ENNReal.toReal_ofReal hm0.le]
    have hint : ∫⁻ ω, ‖‖G ω‖‖ₑ ^ m ∂μ ≤ ENNReal.ofReal (max C 0) := by
      refine le_trans (le_of_eq ?_) ((hC Q i).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _)))
      refine lintegral_congr fun ω => ?_
      rw [Real.enorm_of_nonneg (norm_nonneg _), ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hm0.le]
      congr 2
      rw [StationarySpatialRealization.spatialRealization, translate_zero, euclideanNorm_ofLp_eq_norm]
    calc (∫⁻ ω, ‖‖G ω‖‖ₑ ^ m ∂μ) ^ (1 / m) ≤ (ENNReal.ofReal (max C 0)) ^ (1 / m) :=
          ENNReal.rpow_le_rpow hint (by positivity)
      _ = ENNReal.ofReal C' := by
          rw [hC'def, ENNReal.ofReal_rpow_of_nonneg (le_max_right _ _) (by positivity)]
  -- Minkowski.
  have hGmeas : AEStronglyMeasurable (fun ω => K * ‖G ω‖) μ :=
    ((Lp.aestronglyMeasurable G).norm).const_mul K
  calc eLpNorm (centredFluxFirst hd Q i) (ENNReal.ofReal m) μ
      ≤ eLpNorm (fun ω => K * ‖G ω‖ + (K + S)) (ENNReal.ofReal m) μ := eLpNorm_mono_ae (measurable_centredFluxFirst hd Q i).aestronglyMeasurable hpt
    _ ≤ eLpNorm (fun ω => K * ‖G ω‖) (ENNReal.ofReal m) μ +
          eLpNorm (fun _ : FieldPair d => K + S) (ENNReal.ofReal m) μ :=
        eLpNorm_add_le
          (by rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (by linarith))
    _ ≤ ENNReal.ofReal K * ENNReal.ofReal C' + ENNReal.ofReal (K + S) := by
        gcongr
        · have : (fun ω => K * ‖G ω‖) = K • fun ω => ‖G ω‖ := by funext ω; simp [smul_eq_mul]
          rw [this, eLpNorm_const_smul, Real.enorm_of_nonneg hK0]
          gcongr
        · rw [eLpNorm_const _ hp0 (NeZero.ne μ), measure_univ, ENNReal.one_rpow, mul_one,
            Real.enorm_of_nonneg (by positivity)]
    _ = ENNReal.ofReal (K * C' + (K + S)) := by
        rw [← ENNReal.ofReal_mul hK0, ← ENNReal.ofReal_add (by positivity) (by positivity)]

end EinsteinRelation
