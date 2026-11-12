import EinsteinRelation.Correctors.LocalEuclideanCancellation

/-! # The skew local corrector's derivative correction

Source: `paper/main.tex:921–963`. Columnwise cancellation controls the
literal matrix-vector integral defining `K_R`. The input columns have their
actual local conditional versions; no estimate for `K_R` is assumed.
-/

open MeasureTheory
open scoped ENNReal
open EinsteinRelation.Carriers (reducedCoefficientObservationSigma)

namespace EinsteinRelation.Correctors

/-- Expand the literal matrix-vector correction as the sum of its column
integrals. Source: `paper/main.tex:921–938`. -/
theorem integral_mulVec_eq_sum_columns {X : Type*} [MeasurableSpace X] {d : ℕ}
    (ν : Measure X) (S : X → Mat d) (w : X → Vec d)
    (hi : ∀ k : Fin d, Integrable (fun y => w y k • (fun j => S y j k)) ν) :
    (∫ y, (S y).mulVec (w y) ∂ν) =
      ∑ k : Fin d, ∫ y, w y k • (fun j => S y j k) ∂ν := by
  have heq (y : X) : (S y).mulVec (w y) =
      ∑ k : Fin d, w y k • (fun j => S y j k) := by
    ext j
    simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  simp_rw [heq]
  exact integral_finset_sum _ fun k _ => hi k

/-- The matrix derivative correction has an inverse-radius Euclidean
moment bound by cancellation in every column.
Source: `paper/main.tex:942–963`. -/
theorem local_center_conditioned_skew_derivative_bound {d : ℕ}
    {μ : Measure (FieldPair d)} [IsProbabilityMeasure μ]
    {R : ℝ} (hR : 1 ≤ R)
    (ν : Measure {y : Vec d // euclideanNorm y ≤ R}) [SigmaFinite ν]
    {p A B W : ℝ} (hp : 1 ≤ p) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (w : {y : Vec d // euclideanNorm y ≤ R} → Vec d) (hwm : Measurable w)
    (hwi : ∀ k, Integrable (fun y => w y k) ν)
    (hw : ∀ k, (∫ y, w y k ∂ν) = 0)
    (hwbound : ∀ k, (∫ y, |w y k| ∂ν) ≤ W * R⁻¹)
    (f : Fin d → FieldPair d → Vec d) (hf : ∀ k, Integrable (f k) μ)
    (g : Fin d → {y : Vec d // euclideanNorm y ≤ R} → FieldPair d → Vec d)
    (hgi : ∀ k y, Integrable (g k y) μ)
    (hshift : ∀ k y, eLpNorm (fun ω => euclideanNorm (g k y ω))
      (ENNReal.ofReal p) μ ≤ ENNReal.ofReal B)
    (htail : ∀ k, eLpNorm (fun ω => euclideanNorm
      (f k ω - μ[f k | reducedCoefficientObservationSigma
        {z : Vec d | euclideanNorm (z - 0) < 8 * R}] ω)) (ENNReal.ofReal p) μ ≤
          ENNReal.ofReal A)
    (S : {y : Vec d // euclideanNorm y ≤ R} × FieldPair d → Mat d)
    (hS : Measurable S)
    (hversion : ∀ k (y : {y : Vec d // euclideanNorm y ≤ R}),
      (fun ω j => S (y, ω) j k) =ᵐ[μ]
        μ[f k + g k y | reducedCoefficientObservationSigma
          {x : Vec d | euclideanNorm (x - y.1) < 32 * R}]) :
    let K : FieldPair d → Vec d := fun ω => ∫ y, (S (y, ω)).mulVec (w y) ∂ν
    (∀ᵐ ω ∂μ, Integrable (fun y => (S (y, ω)).mulVec (w y)) ν) ∧
      Measurable K ∧
      MemLp (fun ω => euclideanNorm (K ω)) (ENNReal.ofReal p) μ ∧
      eLpNorm (fun ω => euclideanNorm (K ω)) (ENNReal.ofReal p) μ ≤
        ENNReal.ofReal (((d : ℝ) * (2 * A + B) * W) * R⁻¹) := by
  classical
  let J := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm
  let T : Fin d → FieldPair d → Vec d := fun k ω =>
    ∫ y, w y k • (fun j => S (y, ω) j k) ∂ν
  have hcol (k : Fin d) : Measurable (fun z j => S z j k) :=
    measurable_pi_lambda _ fun j =>
      (continuous_id.matrix_elem j k).measurable.comp hS
  have hcoord (k : Fin d) := local_center_conditioned_euclidean_cancellation_bound hR ν
    hp hA hB (fun y => w y k) ((measurable_pi_apply k).comp hwm) (hwi k) (hw k)
    (f k) (hf k) (g k) (hgi k) (hshift k) (htail k)
    (fun z j => S z j k) (hcol k) (hversion k)
  have hsections := ae_all_iff.mpr fun k => (hcoord k).1
  have hexpand (ω : FieldPair d) (y : {y : Vec d // euclideanNorm y ≤ R}) :
      (S (y, ω)).mulVec (w y) = ∑ k : Fin d, w y k • (fun j => S (y, ω) j k) := by
    ext j
    simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  have hKi : ∀ᵐ ω ∂μ, Integrable (fun y => (S (y, ω)).mulVec (w y)) ν := by
    filter_upwards [hsections] with ω hω
    simpa only [hexpand] using integrable_finset_sum Finset.univ (fun k _ => hω k)
  have hKT : (fun ω => ∫ y, (S (y, ω)).mulVec (w y) ∂ν) =ᵐ[μ]
      (fun ω => ∑ k : Fin d, T k ω) := by
    filter_upwards [hsections] with ω hω
    exact integral_mulVec_eq_sum_columns ν (fun y => S (y, ω)) w hω
  have hTm (k : Fin d) : Measurable (T k) := by
    have hm : Measurable (fun z => w z.1 k • (fun j => S z j k)) :=
      (((measurable_pi_apply k).comp hwm).comp measurable_fst).smul (hcol k)
    exact (hm.comp measurable_swap).stronglyMeasurable.integral_prod_right'.measurable
  have hKm : Measurable (fun ω => ∫ y, (S (y, ω)).mulVec (w y) ∂ν) := by
    have hm : Measurable (fun z => (S z).mulVec (w z.1)) := by
      apply measurable_pi_lambda
      intro j
      change Measurable (fun z => ∑ k : Fin d, S z j k * w z.1 k)
      exact Finset.measurable_fun_sum _ fun k _ =>
        ((continuous_id.matrix_elem j k).measurable.comp hS).mul
          (((measurable_pi_apply k).comp hwm).comp measurable_fst)
    exact (hm.comp measurable_swap).stronglyMeasurable.integral_prod_right'.measurable
  have hKb : eLpNorm (fun ω => euclideanNorm (∫ y, (S (y, ω)).mulVec (w y) ∂ν))
      (ENNReal.ofReal p) μ ≤ ENNReal.ofReal (((d : ℝ) * (2 * A + B) * W) * R⁻¹) := by
    rw [eLpNorm_congr_ae (hKT.mono fun _ hx => congrArg euclideanNorm hx)]
    simp_rw [TimeChange.euclideanNorm_eq_norm_toLp]
    rw [eLpNorm_norm]
    change eLpNorm (fun ω => J (∑ k, T k ω)) (ENNReal.ofReal p) μ ≤ _
    simp_rw [map_sum]
    rw [show (fun ω => ∑ k : Fin d, J (T k ω)) =
      (∑ k : Fin d, fun ω => J (T k ω)) by
        funext ω
        simp only [Finset.sum_apply]]
    calc
      _ ≤ ∑ k : Fin d, eLpNorm (fun ω => J (T k ω)) (ENNReal.ofReal p) μ :=
        eLpNorm_sum_le (fun k _ => (J.continuous.measurable.comp (hTm k)).aestronglyMeasurable)
          (ENNReal.one_le_ofReal.mpr hp)
      _ ≤ ∑ _k : Fin d, ENNReal.ofReal ((2 * A + B) * (W * R⁻¹)) := by
        apply Finset.sum_le_sum
        intro k _
        have hb := (hcoord k).2.2.trans
          (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (hwbound k) (by positivity)))
        simpa only [TimeChange.euclideanNorm_eq_norm_toLp, eLpNorm_norm] using hb
      _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ d)]
        congr 1
        ring
  refine ⟨hKi, hKm, ⟨?_, hKb.trans_lt ENNReal.ofReal_lt_top⟩, hKb⟩
  have hN : Continuous (fun v : Vec d => euclideanNorm v) := by
    simp_rw [TimeChange.euclideanNorm_eq_norm_toLp]
    exact continuous_norm.comp J.continuous
  exact (hN.measurable.comp hKm).aestronglyMeasurable

end EinsteinRelation.Correctors
