import EinsteinRelation.Correctors.LocalConditionedAverage
import EinsteinRelation.Correctors.EuclideanLpCoordinates
import EinsteinRelation.TimeChange.EuclideanTransport
import Mathlib.MeasureTheory.SpecificCodomains.Pi

/-! # The scalar local corrector's derivative correction

Source: `paper/main.tex:921–963`. Cancellation is applied separately to the
coordinates of the derivative of the center weight. The resulting field is
the literal integral defining `H_R`, with Euclidean moments and inverse
radius decay. Constructing the source conditional scalar field is separate.
-/

open MeasureTheory
open scoped ENNReal
open EinsteinRelation.Carriers (reducedCoefficientObservationSigma)

namespace EinsteinRelation.Correctors

/-- The actual vector weight-derivative integral has the required inverse
radius rate from the centered scalar conditional tail and shifted mean
estimates. No bound on the common conditional mean is assumed.
Source: `paper/main.tex:942–963`. -/
theorem local_center_conditioned_scalar_derivative_bound {d : ℕ}
    {μ : Measure (FieldPair d)} [IsProbabilityMeasure μ]
    {R : ℝ} (hR : 1 ≤ R)
    (ν : Measure {y : Vec d // euclideanNorm y ≤ R}) [SigmaFinite ν]
    {p A B W : ℝ} (hp : 1 ≤ p) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (w : {y : Vec d // euclideanNorm y ≤ R} → Vec d) (hwm : Measurable w)
    (hwi : ∀ j, Integrable (fun y => w y j) ν)
    (hw : ∀ j, (∫ y, w y j ∂ν) = 0)
    (hwbound : ∀ j, (∫ y, |w y j| ∂ν) ≤ W * R⁻¹)
    (f : FieldPair d → ℝ) (hf : Integrable f μ)
    (g : {y : Vec d // euclideanNorm y ≤ R} → FieldPair d → ℝ)
    (hgi : ∀ y, Integrable (g y) μ)
    (hshift : ∀ y, eLpNorm (g y) (ENNReal.ofReal p) μ ≤ ENNReal.ofReal B)
    (htail : eLpNorm (f - μ[f | reducedCoefficientObservationSigma
      {z : Vec d | euclideanNorm (z - 0) < 8 * R}]) (ENNReal.ofReal p) μ ≤
        ENNReal.ofReal A)
    (u : {y : Vec d // euclideanNorm y ≤ R} × FieldPair d → ℝ)
    (hu : Measurable u)
    (hversion : ∀ y : {y : Vec d // euclideanNorm y ≤ R},
      (fun ω => u (y, ω)) =ᵐ[μ]
        μ[f + g y | reducedCoefficientObservationSigma
          {x : Vec d | euclideanNorm (x - y.1) < 32 * R}]) :
    let H : FieldPair d → Vec d := fun ω => ∫ y, u (y, ω) • w y ∂ν
    (∀ᵐ ω ∂μ, Integrable (fun y => u (y, ω) • w y) ν) ∧
      Measurable H ∧
      MemLp (fun ω => euclideanNorm (H ω)) (ENNReal.ofReal p) μ ∧
      eLpNorm (fun ω => euclideanNorm (H ω)) (ENNReal.ofReal p) μ ≤
        ENNReal.ofReal (((d : ℝ) * (2 * A + B) * W) * R⁻¹) := by
  classical
  let D : FieldPair d → Vec d := fun ω j => ∫ y, w y j * u (y, ω) ∂ν
  have hcoord (j : Fin d) := local_center_conditioned_cancellation_bound hR ν hp hA hB
    (fun y => w y j) ((measurable_pi_apply j).comp hwm) (hwi j) (hw j)
    f hf g hgi hshift htail u hu hversion
  have hsections : ∀ᵐ ω ∂μ, ∀ j : Fin d,
      Integrable (fun y => u (y, ω) * w y j) ν := by
    filter_upwards [ae_all_iff.mpr fun j => (hcoord j).1] with ω hω
    intro j
    simpa only [smul_eq_mul, mul_comm] using hω j
  have hDi : ∀ᵐ ω ∂μ, Integrable (fun y => u (y, ω) • w y) ν := by
    filter_upwards [hsections] with ω hω
    exact integrable_pi_iff.mpr hω
  have hHD : (fun ω => ∫ y, u (y, ω) • w y ∂ν) =ᵐ[μ] D := by
    filter_upwards [hsections] with ω hω
    ext j
    change (∫ y, (fun k => u (y, ω) * w y k) ∂ν) j = D ω j
    rw [eval_integral hω j]
    simp only [D, mul_comm]
  have hDm : Measurable D := by
    apply measurable_pi_lambda
    intro j
    have hm : Measurable (fun z => w z.1 j * u z) :=
      (((measurable_pi_apply j).comp hwm).comp measurable_fst).mul hu
    exact (hm.comp measurable_swap).stronglyMeasurable.integral_prod_right'.measurable
  have hHm : Measurable (fun ω => ∫ y, u (y, ω) • w y ∂ν) := by
    have hm : Measurable (fun z => u z • w z.1) := hu.smul (hwm.comp measurable_fst)
    exact (hm.comp measurable_swap).stronglyMeasurable.integral_prod_right'.measurable
  have hDb : eLpNorm (fun ω => euclideanNorm (D ω)) (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal (((d : ℝ) * (2 * A + B) * W) * R⁻¹) := by
    simp_rw [TimeChange.euclideanNorm_eq_norm_toLp]
    rw [eLpNorm_norm]
    calc
      _ ≤ ∑ j : Fin d, eLpNorm (fun ω => D ω j) (ENNReal.ofReal p) μ :=
        eLpNorm_toLp_le_sum_coordinates (ENNReal.one_le_ofReal.mpr hp) D hDm
      _ ≤ ∑ _j : Fin d, ENNReal.ofReal ((2 * A + B) * (W * R⁻¹)) := by
        apply Finset.sum_le_sum
        intro j _
        exact (hcoord j).2.2.trans
          (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (hwbound j) (by positivity)))
      _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ d)]
        congr 1
        ring
  have hHb : eLpNorm (fun ω => euclideanNorm (∫ y, u (y, ω) • w y ∂ν))
      (ENNReal.ofReal p) μ ≤ ENNReal.ofReal (((d : ℝ) * (2 * A + B) * W) * R⁻¹) := by
    rw [eLpNorm_congr_ae (hHD.mono fun _ hx => congrArg euclideanNorm hx)]
    exact hDb
  refine ⟨hDi, hHm, ⟨?_, hHb.trans_lt ENNReal.ofReal_lt_top⟩, hHb⟩
  have hN : Continuous (fun v : Vec d => euclideanNorm v) := by
    simp_rw [TimeChange.euclideanNorm_eq_norm_toLp]
    exact continuous_norm.comp
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm.continuous
  exact (hN.measurable.comp hHm).aestronglyMeasurable

end EinsteinRelation.Correctors
