import Mathlib
import DeGiorgi.NormalizedRegularity
import DeGiorgi.Localization

/-!
# Two-sided Moser bounds for homogeneous weak solutions

Applies the one-sided Moser `L^p → L^∞` estimate to a homogeneous weak solution `u`
and to `-u`, which is a subsolution because `u` is a supersolution. Both positive
parts `max u 0` and `max (-u) 0` are then controlled by the same `L^p` norm of `u`.
-/

open MeasureTheory Filter
open scoped Topology ENNReal

namespace EinsteinRelation.Correctors

/-- The positive part of a real number is bounded in absolute value by the number. -/
private theorem posPart_abs_le_abs (v : ℝ) : |max v 0| ≤ |v| := by
  rw [abs_of_nonneg (le_max_right v 0)]
  exact max_le (le_abs_self v) (abs_nonneg v)

/-- Monotonicity of `t ↦ t ^ p` applied to the positive part. -/
private theorem posPart_rpow_le_abs_rpow {p : ℝ} (hp : 0 ≤ p) (v : ℝ) :
    |max v 0| ^ p ≤ |v| ^ p :=
  Real.rpow_le_rpow (abs_nonneg _) (posPart_abs_le_abs v) hp

/-- The positive part of `-v` is also controlled by `|v| ^ p`. -/
private theorem negPart_rpow_le_abs_rpow {p : ℝ} (hp : 0 ≤ p) (v : ℝ) :
    |max (-v) 0| ^ p ≤ |v| ^ p := by
  simpa only [abs_neg] using posPart_rpow_le_abs_rpow hp (-v)

/-- Integrability of `|max (v x) 0| ^ p` from integrability of `|v x| ^ p`. -/
private theorem integrableOn_posPart_rpow {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {s : Set α} {v : α → ℝ} {p : ℝ} (hp : 0 ≤ p)
    (hv : AEStronglyMeasurable v (μ.restrict s))
    (hint : IntegrableOn (fun x => |v x| ^ p) s μ) :
    IntegrableOn (fun x => |max (v x) 0| ^ p) s μ := by
  have hmax : Continuous fun t : ℝ => max t 0 := continuous_id.max continuous_const
  have hcont : Continuous fun t : ℝ => |max t 0| ^ p :=
    (continuous_abs.comp hmax).rpow_const fun _ => Or.inr hp
  refine Integrable.mono' hint (hcont.comp_aestronglyMeasurable hv)
    (Filter.Eventually.of_forall fun x => ?_)
  show ‖|max (v x) 0| ^ p‖ ≤ |v x| ^ p
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
  exact posPart_rpow_le_abs_rpow hp (v x)

/-- Combines a pointwise bound `a ≤ K * (Y * I)` with `I ≤ J` and `K, Y ≥ 0`. -/
private theorem posPart_rpow_le_of_integral_bound {K Y I J a : ℝ} (hK : 0 ≤ K) (hY : 0 ≤ Y)
    (hIJ : I ≤ J) (h : a ≤ K * (Y * I)) : a ≤ K * (Y * J) :=
  h.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hIJ hY) hK)

/-- Moser `L^p` bounds on `max u 0` and `max (-u) 0` for a homogeneous weak solution on a
ball of radius `2 R`, read off on the concentric ball of radius `R`. -/
theorem posPart_negPart_rpow_le_of_isHomogeneousWeakSolution {d : ℕ} [NeZero d]
    (hd : 2 ≤ d) {x₀ : EuclideanSpace ℝ (Fin d)} {R : ℝ} (hR : 0 < R)
    (A : DeGiorgi.EllipticCoeff d (Metric.ball x₀ (2 * R)))
    {u : EuclideanSpace ℝ (Fin d) → ℝ} {p : ℝ} (hp : 1 < p)
    (hsol : DeGiorgi.IsHomogeneousWeakSolution A u)
    (hint : IntegrableOn (fun x => |u x| ^ p) (Metric.ball x₀ (2 * R)) volume) :
    ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ R)),
      |max (u x) 0| ^ p ≤
          (DeGiorgi.C_Moser d * DeGiorgi.ellipticityRatio A ^ (DeGiorgi.sobolevDim d / 2) *
            (p / (p - 1)) ^ DeGiorgi.sobolevDim d) *
          (((2 * R) ^ d)⁻¹ * ∫ y in Metric.ball x₀ (2 * R), |u y| ^ p) ∧
      |max (-u x) 0| ^ p ≤
          (DeGiorgi.C_Moser d * DeGiorgi.ellipticityRatio A ^ (DeGiorgi.sobolevDim d / 2) *
            (p / (p - 1)) ^ DeGiorgi.sobolevDim d) *
          (((2 * R) ^ d)⁻¹ * ∫ y in Metric.ball x₀ (2 * R), |u y| ^ p) := by
  have hpos : 0 < 2 * R := by linarith
  have hp0 : 0 ≤ p := by linarith
  have hball : 2 * R / 2 = R := by ring
  have hfin : Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) = d := finrank_euclideanSpace_fin
  have hsubU := DeGiorgi.isHomogeneousWeakSolution_isSubsolution hsol
  have hsubNegU := DeGiorgi.IsSupersolution.neg_ball hpos
    (DeGiorgi.isHomogeneousWeakSolution_isSupersolution hsol)
  have hmeasU : AEStronglyMeasurable u (volume.restrict (Metric.ball x₀ (2 * R))) :=
    (DeGiorgi.isSubsolution_memW1p hsubU).1.aestronglyMeasurable
  have hmeasNeg : AEStronglyMeasurable (fun x => -u x)
      (volume.restrict (Metric.ball x₀ (2 * R))) :=
    hmeasU.neg
  have hintNeg : IntegrableOn (fun x => |-u x| ^ p) (Metric.ball x₀ (2 * R)) volume := by
    simpa only [abs_neg] using hint
  have hposU : IntegrableOn (fun x => |max (u x) 0| ^ p) (Metric.ball x₀ (2 * R)) volume :=
    integrableOn_posPart_rpow hp0 hmeasU hint
  have hposNeg : IntegrableOn (fun x => |max (-u x) 0| ^ p) (Metric.ball x₀ (2 * R)) volume :=
    integrableOn_posPart_rpow hp0 hmeasNeg hintNeg
  have hIJ : (∫ y in Metric.ball x₀ (2 * R), |max (u y) 0| ^ p) ≤
      ∫ y in Metric.ball x₀ (2 * R), |u y| ^ p :=
    setIntegral_mono_on hposU hint measurableSet_ball fun y _ =>
      posPart_rpow_le_abs_rpow hp0 (u y)
  have hIJ' : (∫ y in Metric.ball x₀ (2 * R), |max (-u y) 0| ^ p) ≤
      ∫ y in Metric.ball x₀ (2 * R), |u y| ^ p :=
    setIntegral_mono_on hposNeg hint measurableSet_ball fun y _ =>
      negPart_rpow_le_abs_rpow hp0 (u y)
  have hMoserU := DeGiorgi.linfty_subsolution_Moser_on_ball_of_ellipticCoeff hd hpos A hp hsubU
    hposU
  have hMoserNeg := DeGiorgi.linfty_subsolution_Moser_on_ball_of_ellipticCoeff hd hpos A hp
    hsubNegU hposNeg
  rw [hball, hfin] at hMoserU hMoserNeg
  have hΛ : 0 ≤ DeGiorgi.ellipticityRatio A := by
    show 0 ≤ A.Λ / A.lam
    exact div_nonneg (A.hlam.le.trans A.hΛ) A.hlam.le
  have hC : 0 ≤ DeGiorgi.C_Moser d :=
    le_trans (by norm_num : (0 : ℝ) ≤ 1) (DeGiorgi.one_le_C_Moser (d := d))
  have hK : 0 ≤ DeGiorgi.C_Moser d * DeGiorgi.ellipticityRatio A ^ (DeGiorgi.sobolevDim d / 2) *
      (p / (p - 1)) ^ DeGiorgi.sobolevDim d :=
    mul_nonneg (mul_nonneg hC (Real.rpow_nonneg hΛ _))
      (Real.rpow_nonneg (div_nonneg hp0 (by linarith)) _)
  have hY : 0 ≤ ((2 * R) ^ d)⁻¹ := inv_nonneg.mpr (pow_nonneg hpos.le d)
  filter_upwards [hMoserU, hMoserNeg] with x hx hx'
  exact ⟨posPart_rpow_le_of_integral_bound hK hY hIJ hx,
    posPart_rpow_le_of_integral_bound hK hY hIJ' hx'⟩

end EinsteinRelation.Correctors
