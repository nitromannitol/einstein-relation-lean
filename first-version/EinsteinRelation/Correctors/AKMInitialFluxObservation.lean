import EinsteinRelation.Correctors.AKMTestConvolutionBounds
import EinsteinRelation.Correctors.EllipticOperatorBound
import EinsteinRelation.Environment.EuclideanLipschitz
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Topology.Order.LiminfLimsup

/-! # Initial flux observed through local coefficient tests

Source: `paper/main.tex:789–798`. Shrinking smooth coefficient observations
recover a normalized column almost everywhere in space. The recovered field
is jointly measurable, exactly translation covariant and observed in the
unit coefficient ball, including on the raw measurable source carrier.
-/

open MeasureTheory Filter
open scoped Topology Convolution

namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

private noncomputable def initialFluxBump (d n : ℕ) : ContDiffBump (0 : Vec d) where
  rIn := (1 / (2 * ((d : ℝ) + 1)) * (1 / ((n : ℝ) + 1))) / 2
  rOut := 1 / (2 * ((d : ℝ) + 1)) * (1 / ((n : ℝ) + 1))
  rIn_pos := by positivity
  rIn_lt_rOut := by
    have h : 0 < 1 / (2 * ((d : ℝ) + 1)) * (1 / ((n : ℝ) + 1)) := by positivity
    linarith only [h]

private noncomputable def initialFluxTest (d n : ℕ) : SmoothCompactTest d :=
  ⟨(initialFluxBump d n).normed volume, (initialFluxBump d n).contDiff_normed,
    (initialFluxBump d n).hasCompactSupport_normed⟩

private theorem initialFluxBump_tendsto (d : ℕ) :
    Tendsto (fun n => (initialFluxBump d n).rOut) atTop (𝓝 0) := by
  simpa only [initialFluxBump, mul_zero] using
    tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (1 / (2 * ((d : ℝ) + 1)))

private theorem initialFluxTest_local_support (d n : ℕ) (x : Vec d) :
    tsupport (fun y => initialFluxTest d n (x - y)) ⊆
      {y | euclideanNorm (y - x) < 1} := by
  have hclosed : IsClosed {y : Vec d | ‖x - y‖ ≤ (initialFluxBump d n).rOut} :=
    isClosed_le (continuous_const.sub continuous_id).norm continuous_const
  have hsup : tsupport (fun y => initialFluxTest d n (x - y)) ⊆
      {y : Vec d | ‖x - y‖ ≤ (initialFluxBump d n).rOut} := by
    apply closure_minimal _ hclosed
    intro y hy
    have hy' : x - y ∈ Function.support ((initialFluxBump d n).normed volume) := hy
    rw [(initialFluxBump d n).support_normed_eq] at hy'
    have hy'' : ‖x - y‖ < (initialFluxBump d n).rOut := by
      simpa only [Metric.mem_ball, dist_zero_right] using hy'
    exact hy''.le
  intro y hy
  have hr := hsup hy
  have hc : 0 < (d : ℝ) + 1 := by positivity
  have hn : 1 / ((n : ℝ) + 1) ≤ 1 := by
    apply (div_le_one (by positivity)).mpr
    have hnn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hr' : ((d : ℝ) + 1) * (initialFluxBump d n).rOut ≤ 1 / 2 := by
    dsimp only [initialFluxBump]
    calc
      _ ≤ ((d : ℝ) + 1) * (1 / (2 * ((d : ℝ) + 1)) * 1) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hn (by positivity)) hc.le
      _ = 1 / 2 := by field_simp
  calc
    euclideanNorm (y - x) ≤ ((d : ℝ) + 1) * ‖y - x‖ :=
      EinsteinRelation.euclideanNorm_le_dimension_mul_norm _
    _ = ((d : ℝ) + 1) * ‖x - y‖ := by rw [norm_sub_rev y x]
    _ ≤ ((d : ℝ) + 1) * (initialFluxBump d n).rOut :=
      mul_le_mul_of_nonneg_left hr hc.le
    _ ≤ 1 / 2 := hr'
    _ < 1 := by norm_num

/-- A locally observed normalized source column, defined without raw point
observations. Source: `paper/main.tex:789–798`. -/
noncomputable def initialFluxObservation {d : ℕ} {K : ℝ} (i : Fin d)
    (A : Coefficient d K) (x : Vec d) : Vec d := fun j =>
  (((d : ℝ) + 1) * K)⁻¹ *
    liminf (fun n => coefficientTestConvolution (initialFluxTest d n) A x j i) atTop

/-- Source: `paper/main.tex:789–798`. The source initial flux is jointly
measurable for coefficient-test observations and space. -/
theorem measurable_initialFluxObservation {d : ℕ} {K : ℝ} (i : Fin d) :
    Measurable (fun z : Coefficient d K × Vec d => initialFluxObservation i z.1 z.2) := by
  apply measurable_pi_lambda
  intro j
  exact measurable_const.mul (Measurable.liminf
    (fun n => measurable_coefficientTestConvolution (initialFluxTest d n) j i))

/-- Source: `paper/main.tex:789–798`. Each value observes only its unit
coefficient ball. -/
theorem measurable_initialFluxObservation_local {d : ℕ} {K : ℝ}
    (i : Fin d) (x : Vec d) :
    Measurable[Environment.AKMTestIntegralSupport.localSigma {y | euclideanNorm (y - x) < 1}]
      (fun A : Coefficient d K => initialFluxObservation i A x) := by
  letI : MeasurableSpace (Coefficient d K) :=
    Environment.AKMTestIntegralSupport.localSigma {y | euclideanNorm (y - x) < 1}
  apply measurable_pi_lambda
  intro j
  exact measurable_const.mul (Measurable.liminf (fun n =>
    measurable_coefficientTestConvolution_local (initialFluxTest d n) x j i
      (initialFluxTest_local_support d n x)))

/-- Source: `paper/main.tex:789–798`. Covariance is exact on the raw source
carrier, before any law or null-set choice. -/
theorem initialFluxObservation_translate {d : ℕ} {K : ℝ} (i : Fin d)
    (A : Coefficient d K) (y x : Vec d) :
    initialFluxObservation i (translateCoefficient y A) x =
      initialFluxObservation i A (y + x) := by
  ext j
  simp only [initialFluxObservation, coefficientTestConvolution_translate]

/-- Source: `paper/main.tex:789–798`. The observed initial flux agrees
almost everywhere with the actual normalized coefficient column. -/
theorem initialFluxObservation_eq_column_ae {d : ℕ} {K : ℝ} (i : Fin d)
    (A : Coefficient d K) :
    ∀ᵐ x ∂(volume : Measure (Vec d)),
      initialFluxObservation i A x =
        (((d : ℝ) + 1) * K)⁻¹ • (A x).mulVec (unitVector i) := by
  have hconv (j : Fin d) :=
    ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
      (μ := volume) (φ := initialFluxBump d) (initialFluxBump_tendsto d)
      (Filter.Eventually.of_forall fun n => (show
        (initialFluxBump d n).rOut ≤ 2 * (initialFluxBump d n).rIn by
          dsimp only [initialFluxBump]; ring_nf; rfl)) (A.locally_integrable j i)
  filter_upwards [ae_all_iff.mpr hconv] with x hx
  ext j
  have h := (hx j).liminf_eq
  change (((d : ℝ) + 1) * K)⁻¹ * _ = _
  have heq : (fun n => coefficientTestConvolution (initialFluxTest d n) A x j i) =
      (fun n => ((initialFluxBump d n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ,
        volume] (fun y => A y j i)) x) := by
    funext n
    unfold coefficientTestConvolution
    rw [convolution_eq_swap]
    rfl
  rw [heq, h]
  simp [unitVector]

/-- Source: `paper/main.tex:789–798`. For continuous coefficients,
including the actual project coefficients, the locally observed column is
identified at every spatial point. -/
theorem initialFluxObservation_eq_column_of_continuous {d : ℕ} {K : ℝ}
    (i : Fin d) (A : Coefficient d K) (hA : Continuous A) (x : Vec d) :
    initialFluxObservation i A x =
      (((d : ℝ) + 1) * K)⁻¹ • (A x).mulVec (unitVector i) := by
  ext j
  have hcont : Continuous (fun y => A y j i) :=
    (continuous_apply i).comp ((continuous_apply j).comp hA)
  have hconv := ContDiffBump.convolution_tendsto_right_of_continuous
    (μ := volume) (φ := initialFluxBump d) (initialFluxBump_tendsto d) hcont x
  change (((d : ℝ) + 1) * K)⁻¹ * _ = _
  have heq : (fun n => coefficientTestConvolution (initialFluxTest d n) A x j i) =
      (fun n => ((initialFluxBump d n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ,
        volume] (fun y => A y j i)) x) := by
    funext n
    unfold coefficientTestConvolution
    rw [convolution_eq_swap]
    rfl
  rw [heq, hconv.liminf_eq]
  simp [unitVector]

/-- Source: `paper/main.tex:789–798`. The observed source column has
stationarity covariance under every law on the coefficient carrier. -/
theorem initialFluxObservation_stationary {d : ℕ} {K : ℝ}
    (P : Measure (Coefficient d K)) (i : Fin d) :
    IsStationaryField P (initialFluxObservation i) := by
  refine ⟨measurable_initialFluxObservation i, ?_⟩
  intro z
  exact Filter.Eventually.of_forall fun A => Filter.Eventually.of_forall fun x => by
    rw [initialFluxObservation_translate, add_comm x (latticeShift z)]

/-- Source: `paper/main.tex:789–798`. The recovered initial column has
the essential Euclidean bound required by the source semigroup estimate. -/
theorem initialFluxObservation_norm_le_ae {d : ℕ} {K : ℝ} (hK : 0 < K)
    (i : Fin d) (A : Coefficient d K) :
    ∀ᵐ x ∂(volume : Measure (Vec d)), euclideanNorm (initialFluxObservation i A x) ≤ 1 := by
  filter_upwards [initialFluxObservation_eq_column_ae i A] with x hx
  rw [hx, TimeChange.euclideanNorm_smul, abs_of_pos (inv_pos.mpr (by positivity))]
  apply (inv_mul_le_iff₀ (by positivity : 0 < ((d : ℝ) + 1) * K)).mpr
  have hvec := mulVec_euclideanNorm_le_of_quadratic (A x) hK (A.symmetric x)
    (fun ξ => (EinsteinRelation.euclideanSq_nonneg_coords ξ).trans (A.elliptic x ξ).1)
    (fun ξ => (A.elliptic x ξ).2) (unitVector i)
  rw [EinsteinRelation.euclideanNorm_unitVector_eq_one, mul_one] at hvec
  exact hvec.trans (by nlinarith only [Nat.cast_nonneg (α := ℝ) d, hK])

end EinsteinRelation.Correctors
