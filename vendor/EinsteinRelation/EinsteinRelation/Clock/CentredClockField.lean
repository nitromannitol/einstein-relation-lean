import EinsteinRelation.Carriers.ScalarAveragingTwin
import EinsteinRelation.Correctors.HomogenizedMatrixBounds
import EinsteinRelation.Correctors.StationaryGradientDomainSupport
import EinsteinRelation.Environment.Reduction
import EinsteinRelation.Environment.SourceReducedBoundSupport
import EinsteinRelation.Localization.ReducedJointObservation
import EinsteinRelation.Probability.ReductionLocality
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn

/-! # The centred clock density and its averaging-field basics

The clock density at the origin, `μ = w.2 0`, is centred by its mean under the reduced
reference law. The centred field `f = μ - E μ` depends only on the environment at the origin
(`paper/main.tex:1155-1167`). This file records the properties of `f` used by the scalar
averaging-field estimate: measurability for the σ-algebra of the ball of radius `33 R`, zero
mean, almost-sure boundedness, stationarity and finite range of the reduced law, and the
decay comparison in the heat-smoothing bound.
-/

open MeasureTheory

noncomputable section

namespace EinsteinRelation.Clock

/-- The clock density at the origin, `w ↦ w.2 0`, is continuous on field pairs. -/
theorem continuous_clockAtOrigin {d : ℕ} :
    Continuous (fun w : FieldPair d => w.2 (0 : Vec d)) :=
  (continuous_eval_const (0 : Vec d)).comp continuous_snd

/-- The centred clock density at the origin, `f = μ - E μ`, where `μ = w.2 0` and the mean is
taken under the reduced reference law (`paper/main.tex:1155-1167`). -/
def centredClock {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (w : FieldPair d) : ℝ :=
  w.2 (0 : Vec d) - ∫ w', w'.2 (0 : Vec d) ∂(Carriers.reducedReferenceLaw Q)

/-- The origin lies in the ball `{y | |y - 0| < 33 R}` when `R > 0`. -/
theorem zero_mem_ball_33 {d : ℕ} {R : ℝ} (hR : 0 < R) :
    (0 : Vec d) ∈ {y : Vec d | euclideanNorm (y - (0 : Vec d)) < 33 * R} := by
  have h0 : euclideanNorm ((0 : Vec d) - (0 : Vec d)) = 0 := by
    simp [euclideanNorm, euclideanSq, dot]
  show euclideanNorm ((0 : Vec d) - (0 : Vec d)) < 33 * R
  rw [h0]
  linarith

/-- The clock density at the origin is measurable for `localSigma U` whenever `0 ∈ U`, because
the pair of coefficient and clock values at `0` is one of the generators of `localSigma U`. -/
theorem measurable_clockAtOrigin_localSigma {d : ℕ} {U : Set (Vec d)} (h0 : (0 : Vec d) ∈ U) :
    Measurable[EinsteinRelation.localSigma U] (fun w : FieldPair d => w.2 (0 : Vec d)) := by
  have hpair : Measurable[MeasurableSpace.comap
      (fun w : FieldPair d => (w.1 (0 : Vec d), w.2 (0 : Vec d))) inferInstance]
      (fun w : FieldPair d => (w.1 (0 : Vec d), w.2 (0 : Vec d))) :=
    comap_measurable _
  have hle : MeasurableSpace.comap
      (fun w : FieldPair d => (w.1 (0 : Vec d), w.2 (0 : Vec d))) inferInstance ≤
      EinsteinRelation.localSigma U := by
    unfold EinsteinRelation.localSigma
    exact le_iSup (fun x : U => MeasurableSpace.comap
      (fun w : FieldPair d => (w.1 (x : Vec d), w.2 (x : Vec d))) inferInstance) ⟨0, h0⟩
  exact measurable_snd.comp (hpair.mono hle le_rfl)

/-- The centred clock density is measurable for the σ-algebra of the ball of radius `33 R`
(`paper/main.tex:961`), since its clock term is a generator of that σ-algebra. -/
theorem measurable_centredClock_localSigma {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    {R : ℝ} (hR : 0 < R) :
    Measurable[EinsteinRelation.localSigma {y : Vec d | euclideanNorm (y - (0 : Vec d)) < 33 * R}]
      (centredClock Q) := by
  have h := (measurable_clockAtOrigin_localSigma (zero_mem_ball_33 (d := d) hR)).sub_const
    (∫ w, w.2 (0 : Vec d) ∂(Carriers.reducedReferenceLaw Q))
  exact h

/-- The reduced reference law is a probability measure. -/
theorem isProbabilityMeasure_reducedReferenceLaw {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) : IsProbabilityMeasure (Carriers.reducedReferenceLaw Q) :=
  Correctors.reducedEnvironmentLaw_isProbabilityMeasure Q

/-- The reduced law is the time-changed environment law of `Correctors.reducedEnvironmentLaw`;
the two definitions have the same body. -/
theorem reducedReferenceLaw_eq_reducedEnvironmentLaw {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) :
    Carriers.reducedReferenceLaw Q = Correctors.reducedEnvironmentLaw Q :=
  rfl

/-- The reduced reference law is stationary. -/
theorem isStationary_reducedReferenceLaw {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) :
    EinsteinRelation.IsStationary (Carriers.reducedReferenceLaw Q) :=
  Correctors.reducedEnvironmentLaw_stationary Q

/-- The reduced reference law has joint finite range `r₀`. -/
theorem hasFiniteRange_reducedReferenceLaw {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) :
    EinsteinRelation.HasFiniteRange r₀ (Carriers.reducedReferenceLaw Q) :=
  Localization.finiteRange_map_reduce Q.measure Q.finiteRange

/-- The source constant is positive when the ellipticity parameter is at least one. -/
theorem sourceReducedBound_pos {L : ℝ} (hL : 1 ≤ L) : 0 < sourceReducedBound L := by
  unfold sourceReducedBound
  exact mul_pos (Real.exp_pos _) (by nlinarith [sq_nonneg L])

/-- The reduced clock density at the origin is bounded by the source constant almost surely
under the reduced reference law: the clock density lies in `[Λ⁻¹, Λ]`
(`sourceReducedBound_support`). -/
theorem ae_abs_clockAtOrigin_le {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) :
    ∀ᵐ w ∂(Carriers.reducedReferenceLaw Q), |w.2 (0 : Vec d)| ≤ sourceReducedBound Λ₀ := by
  have hset : MeasurableSet {w : FieldPair d | |w.2 (0 : Vec d)| ≤ sourceReducedBound Λ₀} :=
    (isClosed_le (continuous_clockAtOrigin (d := d)).abs continuous_const).measurableSet
  unfold Carriers.reducedReferenceLaw
  refine (ae_map_iff (Probability.measurable_reduce (d := d)).aemeasurable hset).mpr ?_
  filter_upwards [Q.regular] with ω hω
  have hb := (sourceReducedBound_support Q.ellipticity_parameter hω).2.2.1 (0 : Vec d)
  show |clockDensity ω 0| ≤ sourceReducedBound Λ₀
  rw [abs_of_pos (clockDensity_pos ω 0)]
  exact hb.2

/-- The reduced clock density at the origin is integrable under the reduced reference law. -/
theorem integrable_clockAtOrigin {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) :
    Integrable (fun w : FieldPair d => w.2 (0 : Vec d)) (Carriers.reducedReferenceLaw Q) := by
  haveI := isProbabilityMeasure_reducedReferenceLaw Q
  refine Integrable.of_bound (continuous_clockAtOrigin (d := d)).aestronglyMeasurable
    (sourceReducedBound Λ₀) ?_
  filter_upwards [ae_abs_clockAtOrigin_le Q] with w hw
  simpa [Real.norm_eq_abs] using hw

/-- The centred clock density has mean zero under the reduced reference law. -/
theorem integral_centredClock {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) :
    ∫ w, centredClock Q w ∂(Carriers.reducedReferenceLaw Q) = 0 := by
  haveI := isProbabilityMeasure_reducedReferenceLaw Q
  unfold centredClock
  rw [integral_sub (integrable_clockAtOrigin Q)
      (integrable_const (∫ w, w.2 (0 : Vec d) ∂(Carriers.reducedReferenceLaw Q))),
    integral_const, probReal_univ, one_smul, sub_self]

/-- The centred clock density is almost surely bounded by twice the source constant under the
reduced reference law, since the mean lies in `[Λ⁻¹, Λ]` (`paper/main.tex:1194-1199`). -/
theorem abs_centredClock_le {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) :
    ∀ᵐ w ∂(Carriers.reducedReferenceLaw Q), |centredClock Q w| ≤ 2 * sourceReducedBound Λ₀ := by
  have hmean : (sourceReducedBound Λ₀)⁻¹ ≤
        ∫ w, w.2 (0 : Vec d) ∂(Carriers.reducedReferenceLaw Q) ∧
      ∫ w, w.2 (0 : Vec d) ∂(Carriers.reducedReferenceLaw Q) ≤ sourceReducedBound Λ₀ :=
    reducedClockMean_bounds Q
  have hK : 0 < sourceReducedBound Λ₀ := sourceReducedBound_pos Q.ellipticity_parameter
  have hKinv : 0 < (sourceReducedBound Λ₀)⁻¹ := inv_pos.mpr hK
  obtain ⟨hlo, hhi⟩ := hmean
  filter_upwards [ae_abs_clockAtOrigin_le Q] with w hw
  obtain ⟨hw1, hw2⟩ := abs_le.mp hw
  unfold centredClock
  rw [abs_le]
  constructor <;> linarith

/-- For `t ≥ 0`, the power `(1 + t)^(-1/2)` equals `(√(1 + t))⁻¹`. -/
theorem rpow_neg_half_eq_sqrt_inv {t : ℝ} (ht : 0 ≤ t) :
    (1 + t) ^ (-(1 / 2 : ℝ)) = (Real.sqrt (1 + t))⁻¹ := by
  have h1 : (0 : ℝ) ≤ 1 + t := by linarith
  rw [Real.rpow_neg h1, Real.sqrt_eq_rpow]

/-- A heat-smoothing bound `‖H_t f‖_{L^m} ≤ M m (1 + t)^(-1/2)` on the reduced law gives the
scalar averaging-field estimate of `Carriers.IsScalarAveragingField`. That predicate allows the
larger bound `M m ((√(1 + t))⁻¹ + R⁻¹)`, since `M m R⁻¹ ≥ 0` (`paper/main.tex:961-964`). -/
theorem isScalarAveragingField_of_heat_bound {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (M : ℝ → ℝ) {R : ℝ} (hR : 0 < R) {f : FieldPair d → ℝ}
    (hf : Measurable[EinsteinRelation.localSigma
      {y : Vec d | euclideanNorm (y - (0 : Vec d)) < 33 * R}] f)
    (hM : ∀ m : ℝ, 2 ≤ m → 0 ≤ M m)
    (hheat : ∀ m : ℝ, 2 ≤ m → ∀ t : ℝ, 0 ≤ t →
      eLpNorm (Correctors.heatSmoothed t f) (ENNReal.ofReal m) (Carriers.reducedReferenceLaw Q) ≤
        ENNReal.ofReal (M m * (1 + t) ^ (-(1 / 2 : ℝ)))) :
    Carriers.IsScalarAveragingField Q M R f := by
  unfold Carriers.IsScalarAveragingField
  refine ⟨hf, fun m hm t ht => ?_⟩
  refine (hheat m hm t ht).trans ?_
  apply ENNReal.ofReal_le_ofReal
  rw [rpow_neg_half_eq_sqrt_inv ht]
  have hRinv : 0 ≤ R⁻¹ := inv_nonneg.mpr hR.le
  exact mul_le_mul_of_nonneg_left (by linarith) (hM m hm)

/-- For `d ≥ 2` and `t ≥ 0`, the decay `(1 + t)^(-d/4)` is dominated by `(1 + t)^(-1/2)`. -/
theorem rpow_decay_le {d : ℕ} (hd : 2 ≤ d) {t : ℝ} (ht : 0 ≤ t) :
    (1 + t) ^ (-(d : ℝ) / 4) ≤ (1 + t) ^ (-(1 / 2 : ℝ)) := by
  have hd' : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)

end EinsteinRelation.Clock

end
