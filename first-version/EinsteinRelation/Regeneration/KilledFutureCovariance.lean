import EinsteinRelation.Regeneration.FirstRegenerationEndpointFormula
import EinsteinRelation.Regeneration.CouplingSpatialMaps
import EinsteinRelation.Regeneration.RecenterNoBacktracking
import EinsteinRelation.Regeneration.KilledFutureKernel
import EinsteinRelation.Regeneration.CouplingCovarianceFromV2
import EinsteinRelation.Regeneration.BoundedMeasurableKilledFutureVersion

/-! # Covariance of the killed future expectation

Source `paper/main.tex:383–409`. A covariance identity for the full coupled
law transports the killed future integral. Spatial recentering preserves
the no-backtracking event and the Bernoulli sequence.
-/

open MeasureTheory
open scoped NNReal ENNReal

noncomputable section
attribute [local instance] Classical.propDecidable

namespace EinsteinRelation.Regeneration

/-- The killed future expectation at `(x,ω)` equals the origin expectation in
`T_x ω` whenever the full coupled law has the corresponding covariance. -/
theorem killed_future_integral_eq_of_recenter {d : ℕ} (K : CoupledQuenchedLaws d)
    (x : Vec d) (ω : FieldPair d) (R : ℝ) (i : Fin d)
    (hcov : Measure.map (recenterSample x) (K (x, ω)) = K (0, translate x ω))
    (Φ : FutureState d i R → ℝ) :
    (∫ z, (if NoBacktracking R z.1 i then
      Φ ((recenterSample x z).1, z.2, fun y : FutureHalfSpace d i R =>
        ((translate x (reduce ω)).1 y, (translate x (reduce ω)).2 y)) else 0)
      ∂K (x, ω)) =
    ∫ z, (if NoBacktracking R z.1 i then
      Φ ((recenterSample (0 : Vec d) z).1, z.2, fun y : FutureHalfSpace d i R =>
        ((reduce (translate x ω)).1 y, (reduce (translate x ω)).2 y)) else 0)
      ∂K (0, translate x ω) := by
  rw [← hcov]
  change _ = ∫ z, _ ∂Measure.map (recenterSampleEquiv x) (K (x, ω))
  rw [integral_map_equiv]
  apply integral_congr_ae
  filter_upwards [] with z
  simp only [recenterSampleEquiv_apply, recenterSample_zero, recenterSample_snd,
    noBacktracking_recenterSample_iff, reduce_translate]

/-- The product-a.e. coupled covariance is sufficient for product-a.e. covariance
of every killed future test; no origin conclusion is inferred from spatial a.e. -/
theorem killed_future_integral_ae_eq_of_covariance {d : ℕ} (Q : Measure (FieldPair d))
    (K : CoupledQuenchedLaws d)
    (hcov : ∀ᵐ xω ∂((volume : Measure (Vec d)).prod Q),
      Measure.map (recenterSample xω.1) (K xω) = K (0, translate xω.1 xω.2))
    (R : ℝ) (i : Fin d) (Φ : FutureState d i R → ℝ) :
    (fun p : Vec d × FieldPair d => ∫ z, (if NoBacktracking R z.1 i then
      Φ ((recenterSample p.1 z).1, z.2, fun y : FutureHalfSpace d i R =>
        ((translate p.1 (reduce p.2)).1 y, (translate p.1 (reduce p.2)).2 y)) else 0)
      ∂K p) =ᵐ[((volume : Measure (Vec d)).prod Q)]
    (fun p => ∫ z, (if NoBacktracking R z.1 i then
      Φ ((recenterSample (0 : Vec d) z).1, z.2, fun y : FutureHalfSpace d i R =>
        ((reduce (translate p.1 p.2)).1 y, (reduce (translate p.1 p.2)).2 y)) else 0)
      ∂K (0, translate p.1 p.2)) := by
  filter_upwards [hcov] with p hp
  exact killed_future_integral_eq_of_recenter K p.1 p.2 R i hp Φ

/-- A bounded measurable version of the killed future expectation can be chosen
with the product-a.e. covariance needed in the renewal proof (lines 393–409). -/
theorem exists_covariant_bounded_killed_future_version {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q] (hQ : IsStationary Q)
    (K : CoupledQuenchedLaws d) (hK : HasProbabilityLaws Q K)
    (hcov : ∀ᵐ xω ∂((volume : Measure (Vec d)).prod Q),
      Measure.map (recenterSample xω.1) (K xω) = K (0, translate xω.1 xω.2))
    (R : ℝ) (i : Fin d) (Φ : FutureState d i R → ℝ)
    (hΦ : Measurable Φ) (hb : BoundedRealTest Φ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ B : Vec d × FieldPair d → ℝ, Measurable B ∧
      (∀ p, |B p| ≤ C) ∧
      (∀ᵐ ω ∂Q, B (0, ω) = ∫ z, (if NoBacktracking R z.1 i then
        Φ (z.1, z.2, fun y : FutureHalfSpace d i R =>
          ((reduce ω).1 y, (reduce ω).2 y)) else 0) ∂K (0, ω)) ∧
      B =ᵐ[((volume : Measure (Vec d)).prod Q)] (fun p => ∫ z,
        (if NoBacktracking R z.1 i then
          Φ ((recenterSample p.1 z).1, z.2, fun y : FutureHalfSpace d i R =>
            ((translate p.1 (reduce p.2)).1 y, (translate p.1 (reduce p.2)).2 y))
          else 0) ∂K p) ∧
      B =ᵐ[((volume : Measure (Vec d)).prod Q)]
        (fun p => B (0, translate p.1 p.2)) := by
  obtain ⟨C, hC, B, hBm, hBb, hBo, hBp⟩ :=
    exists_globally_bounded_measurable_killed_future_version Q K hK R i Φ hΦ hb
  have hBo' : ∀ᵐ ω ∂Q, B (0, ω) = ∫ z, (if NoBacktracking R z.1 i then
      Φ (z.1, z.2, fun y : FutureHalfSpace d i R =>
        ((reduce ω).1 y, (reduce ω).2 y)) else 0) ∂K (0, ω) := by
    filter_upwards [hBo] with ω hω
    simpa only [recenterSample_zero, translate_zero] using hω
  refine ⟨C, hC, B, hBm, hBb, hBo', hBp, ?_⟩
  have hBt := Renewal.ae_spatial_translate_of_ae Q hQ hBo'
  filter_upwards [hBp, hBt, hcov] with p hp ht hc
  rw [hp, ht]
  simpa only [recenterSample_zero] using
    killed_future_integral_eq_of_recenter K p.1 p.2 R i hc Φ

/-- The spatial mean of an a.e. covariant measurable version equals its
origin mean, as used in `paper/main.tex:407–408`. -/
theorem integral_future_version_eq_origin_of_ae_covariance {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q] (hQ : IsStationary Q)
    (B : Vec d × FieldPair d → ℝ) (hB : Measurable B)
    (hcov : B =ᵐ[((volume : Measure (Vec d)).prod Q)]
      (fun p => B (0, translate p.1 p.2))) :
    ∀ᵐ x ∂(volume : Measure (Vec d)),
      (∫ ω, B (x, ω) ∂Q) = ∫ ω, B (0, ω) ∂Q := by
  filter_upwards [Measure.ae_ae_of_ae_prod hcov] with x hx
  rw [integral_congr_ae hx]
  exact Probability.integral_translate Q hQ x (fun ω => B (0, ω))
    (hB.comp measurable_prodMk_left)

/-- Recentring the sample and translating the physical environment preserve
the literal killed future test. -/
theorem killedFutureTest_recenter {d : ℕ} (R : ℝ) (i : Fin d)
    (Φ : FutureState d i R → ℝ) (y : Vec d) (ω : FieldPair d) (z : CoupledSample d) :
    killedFutureTest R i Φ ((0, translate y ω), recenterSample y z) =
      killedFutureTest R i Φ ((y, ω), z) := by
  have hrec : spatialFutureRecord R i (0, translate y ω) (recenterSample y z) =
      spatialFutureRecord R i (y, ω) z := by
    apply Prod.ext
    · apply ContinuousMap.ext
      intro t
      simp [spatialFutureRecord, recenterSample]
    · apply Prod.ext
      · rfl
      · funext x
        simp [spatialFutureRecord, reduce_translate]
  simp only [killedFutureTest, noBacktracking_recenterSample_iff, hrec]

/-- A spatial-a.e. covariance identity suffices for the mean identity used
in Step 3. Both a.e. versions of `B` retain their original qualifiers. -/
theorem integral_killed_future_version_eq_origin_of_covariance {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q] (hQ : IsStationary Q)
    (K : CoupledQuenchedLaws d) (R : ℝ) (i : Fin d)
    (Φ : FutureState d i R → ℝ) (hΦ : Measurable Φ)
    (B : Vec d × FieldPair d → ℝ) (hB : Measurable B)
    (hBo : ∀ᵐ ω ∂Q, B (0, ω) = ∫ z, killedFutureTest R i Φ ((0, ω), z) ∂K (0, ω))
    (hBp : ∀ᵐ xω ∂(volume : Measure (Vec d)).prod Q,
      B xω = ∫ z, killedFutureTest R i Φ (xω, z) ∂K xω)
    (hcov : ∀ᵐ xω ∂(volume : Measure (Vec d)).prod Q,
      (K xω).map (recenterSample xω.1) = K (0, translate xω.1 xω.2)) :
    ∀ᵐ y ∂(volume : Measure (Vec d)),
      (∫ ω, B (y, ω) ∂Q) = ∫ ω, B (0, ω) ∂Q := by
  have hp := Measure.ae_ae_of_ae_prod hBp
  have hc := Measure.ae_ae_of_ae_prod hcov
  filter_upwards [hp, hc] with y hyp hyc
  have htranslate : ∀ᵐ ω ∂Q,
      B (0, translate y ω) =
        ∫ z, killedFutureTest R i Φ ((0, translate y ω), z) ∂K (0, translate y ω) := by
    exact ae_of_ae_map (Probability.measurable_translate y).aemeasurable (by
      rw [hQ y]
      exact hBo)
  have heq : (fun ω => B (y, ω)) =ᵐ[Q] (fun ω => B (0, translate y ω)) := by
    filter_upwards [hyp, hyc, htranslate] with ω hω hcω htω
    have hmrec : Measurable (recenterSample y) :=
      (measurable_recenterSample (d := d)).comp (measurable_const.prodMk measurable_id)
    have hmtest : Measurable (fun z => killedFutureTest R i Φ ((0, translate y ω), z)) :=
      (measurable_killedFutureTest R i Φ hΦ).comp (measurable_const.prodMk measurable_id)
    rw [hω, htω, ← hcω, integral_map hmrec.aemeasurable hmtest.aestronglyMeasurable]
    exact integral_congr_ae (Filter.Eventually.of_forall fun z =>
      (killedFutureTest_recenter R i Φ y ω z).symm)
  rw [integral_congr_ae heq]
  exact Probability.integral_translate Q hQ y (fun ω => B (0, ω))
    (hB.comp measurable_prodMk_left)




/-- Apply the V2 covariance theorem to the exact killed-future sufficient
hypothesis of Step 3 (`paper/main.tex:406–408`). -/
theorem integral_killed_future_version_eq_origin_of_isGMPCouplingV2
    (hLoc : External.GMPKernelLocality)
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam l δ : ℝ) (hl0 : 0 < lam) (hl1 : lam ≤ 1) (hl : 0 < l)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : Renewal.IsGMPCouplingV2 hd Q.ellipticity_parameter Q lam l δ hl0.le hl1 P K)
    (Φ : FutureState d (Renewal.forceCoord hd) (l / lam) → ℝ) (hΦ : Measurable Φ)
    (B : Vec d × FieldPair d → ℝ) (hB : Measurable B)
    (hBo : ∀ᵐ ω ∂Q.measure, B (0, ω) = ∫ z,
      killedFutureTest (l / lam) (Renewal.forceCoord hd) Φ ((0, ω), z) ∂K (0, ω))
    (hBp : ∀ᵐ xω ∂(volume : Measure (Vec d)).prod Q.measure,
      B xω = ∫ z, killedFutureTest (l / lam) (Renewal.forceCoord hd) Φ (xω, z) ∂K xω) :
    ∀ᵐ y ∂(volume : Measure (Vec d)),
      (∫ ω, B (y, ω) ∂Q.measure) = ∫ ω, B (0, ω) ∂Q.measure := by
  exact integral_killed_future_version_eq_origin_of_covariance Q.measure Q.stationary K
    (l / lam) (Renewal.forceCoord hd) Φ hΦ B hB hBo hBp
    (Renewal.coupling_covariance_of_isGMPCouplingV2 hLoc hd Q lam l δ hl0 hl1 hl P K hK)

end EinsteinRelation.Regeneration
