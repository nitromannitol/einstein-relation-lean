import EinsteinFull.External.DFGW.MartingaleBlockTail
import EinsteinFull.External.DFGW.BrownianFiniteProjection
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution

/-! # Normalized block values of the increment process

Along the block lengths `(n + 1) / 2 ^ a`, the normalized squares of a projected increment have
means converging to the projected diffusion coefficient and truncated means converging to those
of the centred Gaussian law with that variance. Both follow from the scaled second moments and
the one-time Brownian limits of the increment process.
-/

open MeasureTheory ProbabilityTheory Filter EinsteinRelation
open scoped NNReal ENNReal Topology

namespace EinsteinFull.External.DFGW

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {d : ℕ}

/-- The diffusive scales `(n + 1) ^ (-1 / 2)` tend to zero from above. -/
theorem tendsto_inv_sqrt_succ_nhdsGT :
    Tendsto (fun n : ℕ => (Real.sqrt (n + 1))⁻¹) atTop (𝓝[>] 0) := by
  have h : Tendsto (fun n : ℕ => Real.sqrt ((n : ℝ) + 1)) atTop atTop := by
    have h1 : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
    exact (Real.tendsto_sqrt_atTop).comp h1
  refine tendsto_nhdsWithin_iff.2 ⟨h.inv_tendsto_atTop, ?_⟩
  exact Eventually.of_forall fun n => inv_pos.2 (Real.sqrt_pos.2 (by positivity))

/-- At the scale `(n + 1) ^ (-1 / 2)`, the time `2 ^ (-a)` is the block length. -/
theorem scale_mul_dyadic_eq_blockStep (n a : ℕ) :
    (((Real.sqrt (n + 1))⁻¹)⁻¹ ^ 2).toNNReal * ((2 : ℝ≥0) ^ a)⁻¹ = blockStep n a := by
  apply NNReal.eq
  rw [NNReal.coe_mul, Real.coe_toNNReal _ (sq_nonneg _), inv_inv,
    Real.sq_sqrt (by positivity)]
  simp only [blockStep, NNReal.coe_div, NNReal.coe_inv, NNReal.coe_pow, NNReal.coe_ofNat,
    NNReal.coe_natCast]
  push_cast
  ring

/-- The block length in real numbers. -/
theorem coe_blockStep (n a : ℕ) : ((blockStep n a : ℝ≥0) : ℝ) = ((n : ℝ) + 1) / 2 ^ a := by
  simp only [blockStep, NNReal.coe_div, NNReal.coe_pow, NNReal.coe_ofNat, NNReal.coe_natCast]
  push_cast
  ring

/-- Means of the normalized squared block values converge to the projected diffusion
coefficient. -/
theorem tendsto_integral_dot_blockStep_sq (Y : Ω → Path d) (e : Vec d) {σ2 : ℝ}
    (hsec : ∀ t : ℝ≥0, Tendsto (fun ε : ℝ => ∫ ω, dot e (ε • Y ω ((ε⁻¹ ^ 2).toNNReal * t)) ^ 2 ∂P)
      (𝓝[>] 0) (𝓝 (σ2 * t))) (a : ℕ) :
    Tendsto (fun n : ℕ => ∫ ω, dot e (Y ω (blockStep n a)) ^ 2 / blockStep n a ∂P) atTop
      (𝓝 σ2) := by
  have h := ((hsec ((2 : ℝ≥0) ^ a)⁻¹).comp tendsto_inv_sqrt_succ_nhdsGT).const_mul ((2 : ℝ) ^ a)
  have hlim : (2 : ℝ) ^ a * (σ2 * (((2 : ℝ≥0) ^ a)⁻¹ : ℝ≥0)) = σ2 := by
    push_cast
    field_simp
  rw [hlim] at h
  apply h.congr'
  filter_upwards with n
  simp only [Function.comp_apply, scale_mul_dyadic_eq_blockStep]
  have hdot (v : Vec d) (c : ℝ) : dot e (c • v) = c * dot e v := by
    simp only [dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  simp_rw [hdot]
  rw [← integral_const_mul]
  apply integral_congr_ae
  refine ae_of_all _ fun ω => ?_
  dsimp only
  rw [coe_blockStep, mul_pow, inv_pow, Real.sq_sqrt (by positivity)]
  field_simp

/-- Truncated means of the normalized squared block values converge to those of the centred
Gaussian law with the projected diffusion coefficient as variance. -/
theorem tendsto_integral_min_dot_blockStep_sq [IsProbabilityMeasure P] (Y : Ω → Path d)
    {D : Mat d} {W : Measure (Path d)} (hW : IsBrownianLaw D W)
    (hfdd : ∀ (m : ℕ) (t : Fin m → ℝ≥0),
      letI : IsProbabilityMeasure W := hW.1
      TendstoInDistribution (fun (ε : ℝ) ω j => ε • Y ω ((ε⁻¹ ^ 2).toNNReal * t j))
        (𝓝[>] 0) (fun γ : Path d => fun j => γ (t j)) (fun _ => P) W)
    (e : Vec d) (a : ℕ) (Λ : ℝ) :
    Tendsto (fun n : ℕ => ∫ ω, min (dot e (Y ω (blockStep n a)) ^ 2 / blockStep n a) Λ ∂P)
      atTop (𝓝 (∫ x, min (x ^ 2) Λ ∂(gaussianReal 0 (dot e (D.mulVec e)).toNNReal))) := by
  let : IsProbabilityMeasure W := hW.1
  let δ : ℝ≥0 := ((2 : ℝ≥0) ^ a)⁻¹
  have hδ : (0 : ℝ) < δ := by
    change (0 : ℝ) < ((((2 : ℝ≥0) ^ a)⁻¹ : ℝ≥0) : ℝ)
    push_cast
    positivity
  let t : Fin 1 → ℝ≥0 := fun _ => δ
  have hconv := hfdd 1 t
  have hdot (v : Vec d) (c : ℝ) : dot e (c • v) = c * dot e v := by
    simp only [dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hdotc : Continuous fun v : Vec d => dot e v := by
    unfold dot
    exact continuous_finsetSum _ fun i _ => continuous_const.mul (continuous_apply i)
  let G0 : C(Fin 1 → Vec d, ℝ) :=
    ⟨fun x => min (dot e (x 0) ^ 2 / δ) Λ, by
      exact ((((hdotc.comp (continuous_apply 0)).pow 2).div_const _).min continuous_const)⟩
  have hG0bound (x : Fin 1 → Vec d) : |G0 x| ≤ |Λ| := by
    change |min (dot e (x 0) ^ 2 / δ) Λ| ≤ |Λ|
    have hq : 0 ≤ dot e (x 0) ^ 2 / δ := by positivity
    rcases le_total (dot e (x 0) ^ 2 / δ) Λ with h | h
    · rw [min_eq_left h, abs_of_nonneg hq, abs_of_nonneg (hq.trans h)]
      exact h
    · rw [min_eq_right h]
  let g : BoundedContinuousFunction (Fin 1 → Vec d) ℝ :=
    BoundedContinuousFunction.mkOfBound G0 (2 * |Λ|) (by
      intro x y
      rw [Real.dist_eq]
      calc
        _ ≤ |G0 x| + |G0 y| := abs_sub _ _
        _ ≤ |Λ| + |Λ| := add_le_add (hG0bound x) (hG0bound y)
        _ = 2 * |Λ| := by ring)
  have htest := (tendstoInDistribution_iff_forall_integral_rclike_tendsto ℝ
    hconv.forall_aemeasurable hconv.aemeasurable_limit).1 hconv g
  have hseq := htest.comp tendsto_inv_sqrt_succ_nhdsGT
  -- the limit is the Gaussian truncated mean
  let c : ℝ := (Real.sqrt δ)⁻¹
  have hsqrtδ : 0 < Real.sqrt δ := Real.sqrt_pos.2 hδ
  have hc2 : c ^ 2 * δ = 1 := by
    dsimp only [c]
    rw [inv_pow, Real.sq_sqrt hδ.le]
    field_simp
  have hv : 0 ≤ ∑ j : Fin 1, ∑ l : Fin 1, (min (t j) (t l) : ℝ) *
      dot ((fun _ : Fin 1 => c • e) j) (D.mulVec ((fun _ : Fin 1 => c • e) l)) := by
    simp only [Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton, min_self]
    exact mul_nonneg hδ.le (hW.2.2.1 _)
  have hlaw := isBrownianLaw_map_sum_dot hW 1 t (fun _ => c • e) hv
  have hvar : (∑ j : Fin 1, ∑ l : Fin 1, (min (t j) (t l) : ℝ) *
      dot ((fun _ : Fin 1 => c • e) j) (D.mulVec ((fun _ : Fin 1 => c • e) l))) =
      dot e (D.mulVec e) := by
    simp only [Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton, min_self]
    rw [Matrix.mulVec_smul]
    have h1 : dot (c • e) (c • D.mulVec e) = c ^ 2 * dot e (D.mulVec e) := by
      simp only [dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [h1, ← mul_assoc, mul_comm (δ : ℝ), hc2, one_mul]
  rw [hvar] at hlaw
  have hZ : Measurable fun γ : Path d => ∑ j : Fin 1, dot (c • e) (γ (t j)) := by
      apply Continuous.measurable
      apply continuous_finsetSum
      intro j _
      unfold dot
      exact continuous_finsetSum _ fun i _ =>
        continuous_const.mul ((continuous_apply i).comp (continuous_eval_const _))
  have hlimit : (∫ γ, g (fun j => γ (t j)) ∂W) =
      ∫ x, min (x ^ 2) Λ ∂(gaussianReal 0 (dot e (D.mulVec e)).toNNReal) := by
    rw [← hlaw, integral_map (f := fun x : ℝ => min (x ^ 2) Λ) hZ.aemeasurable
      (by fun_prop : Continuous fun x : ℝ => min (x ^ 2) Λ).aestronglyMeasurable]
    apply integral_congr_ae
    refine ae_of_all _ fun γ => ?_
    change min (dot e (γ δ) ^ 2 / δ) Λ = min ((∑ j : Fin 1, dot (c • e) (γ δ)) ^ 2) Λ
    congr 1
    simp only [Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton]
    have h1 : dot (c • e) (γ δ) = c * dot e (γ δ) := by
      simp only [dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [h1, mul_pow]
    have hc2' : c ^ 2 = (δ : ℝ)⁻¹ := eq_inv_of_mul_eq_one_left hc2
    rw [hc2', div_eq_inv_mul]
  rw [hlimit] at hseq
  apply hseq.congr'
  filter_upwards with n
  simp only [Function.comp_apply]
  apply integral_congr_ae
  refine ae_of_all _ fun ω => ?_
  change min (dot e ((Real.sqrt (n + 1))⁻¹ • Y ω
      ((((Real.sqrt (n + 1))⁻¹)⁻¹ ^ 2).toNNReal * δ)) ^ 2 / δ) Λ = _
  rw [scale_mul_dyadic_eq_blockStep, hdot, mul_pow, inv_pow, Real.sq_sqrt (by positivity),
    coe_blockStep]
  congr 1
  change ((n : ℝ) + 1)⁻¹ * dot e (Y ω (blockStep n a)) ^ 2 /
      ((((2 : ℝ≥0) ^ a)⁻¹ : ℝ≥0) : ℝ) = _
  push_cast
  field_simp

end EinsteinFull.External.DFGW
