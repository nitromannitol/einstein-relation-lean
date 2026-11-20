import EinsteinFull.Homogenization.SourceResponseMeanAbsolute

/-!
# Decay of response fluctuation bounds

The normalized independent-block bound decays geometrically in the difference
between the parent and descendant scales, as in the proof of Proposition 1.7
of Armstrong, Kuusi and Mourrat, *Quantitative Stochastic Homogenization and
Large-Scale Regularity*.
-/

open Filter Topology MeasureTheory
open _root_.Homogenization

namespace EinsteinFull.Homogenization

open EinsteinRelation.Environment.AKMTestIntegralSupport
open EinsteinRelation.External.AKM

/-- A normalized square-root block bound tends to zero as the number of blocks
increases geometrically. -/
theorem tendsto_inv_pow_mul_sqrt_pow_mul_sq {a : ℝ} (ha : 1 < a) (b : ℝ) :
    Tendsto (fun j : ℕ => (a ^ j)⁻¹ * Real.sqrt (a ^ j * b ^ 2)) atTop (𝓝 0) := by
  have ha0 : 0 < a := lt_trans zero_lt_one ha
  have hi0 : 0 ≤ a⁻¹ := inv_nonneg.mpr ha0.le
  have hi1 : a⁻¹ < 1 := (inv_lt_one₀ ha0).2 ha
  have ht : Tendsto (fun j : ℕ => (a⁻¹) ^ j) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hi0 hi1
  have hs := Real.continuous_sqrt.continuousAt.tendsto.comp ht
  have heq : ∀ j : ℕ, (a ^ j)⁻¹ * Real.sqrt (a ^ j * b ^ 2) =
      Real.sqrt ((a⁻¹) ^ j) * |b| := by
    intro j
    have hz : 0 < a ^ j := pow_pos ha0 _
    rw [Real.sqrt_mul hz.le, Real.sqrt_sq_eq_abs, inv_pow, Real.sqrt_inv]
    have hsqrt : Real.sqrt (a ^ j) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hz)
    field_simp
    rw [Real.sq_sqrt hz.le]
  have h := hs.mul_const |b|
  simp only [Real.sqrt_zero, zero_mul] at h
  exact h.congr' (Eventually.of_forall fun j => (heq j).symm)

/-- At fixed descendant scale, the expected positive deviation of the parent
response above the descendant mean tends to zero as the parent scale grows. -/
theorem tendsto_integral_posPart_sourceResponseJ_sub_mean
    {d : ℕ} [NeZero d] {K : ℝ} (hK : 0 ≤ K)
    (P : Measure (Coefficient d K)) [IsProbabilityMeasure P] (hP : AKMFiniteRange P)
    (hstat : ∀ z : LatticeIndex d, Measure.map (translateCoefficient (latticeShift z)) P = P)
    (n k : ℕ) (hk : K ≤ (k : ℝ) + 1) (p q : Vec d) :
    Tendsto (fun j : ℕ => ∫ a, max 0 (Book.Ch02.responseJ
      (Book.Ch02.cubeDomain (originCube d ((n : ℤ) + j)))
      (sourceCoeffOn a (Book.Ch02.cubeDomain (originCube d ((n : ℤ) + j))) k hk) p q -
      ∫ b, Book.Ch02.responseJ (Book.Ch02.cubeDomain (originCube d n))
        (sourceCoeffOn b (Book.Ch02.cubeDomain (originCube d n)) k hk) p q ∂P) ∂P)
      atTop (𝓝 0) := by
  let B := (K / 2) * EinsteinRelation.euclideanSq (-p) + vecNormSq q - vecDot p q
  let C : ℝ := (Fintype.card (Fin d → ZMod 3) : ℝ) *
    EinsteinRelation.Probability.hoeffdingMomentConst 1
  have ha : 1 < (3 : ℝ) ^ d := one_lt_pow₀ (by norm_num) (NeZero.ne d)
  have hC : 0 ≤ C := by
    dsimp only [C]
    have hc : 0 ≤ EinsteinRelation.Probability.hoeffdingMomentConst 1 := by
      unfold EinsteinRelation.Probability.hoeffdingMomentConst
      positivity
    positivity
  have hdec := (tendsto_inv_pow_mul_sqrt_pow_mul_sq ha B).const_mul C
  simp only [mul_zero] at hdec
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hdec
    (fun j => integral_nonneg fun a => le_max_left _ _) ?_
  intro j
  let Q := originCube d ((n : ℤ) + j)
  let f := fun a => Book.Ch02.responseJ (Book.Ch02.cubeDomain Q)
    (sourceCoeffOn a (Book.Ch02.cubeDomain Q) k hk) p q -
    ∫ b, Book.Ch02.responseJ (Book.Ch02.cubeDomain (originCube d n))
      (sourceCoeffOn b (Book.Ch02.cubeDomain (originCube d n)) k hk) p q ∂P
  have hf : Integrable f P := (integrable_sourceResponseJ_cube hK P Q k hk p q).sub
    (integrable_const _)
  have hp : Integrable (fun a => max 0 (f a)) P := by
    simpa only [max_comm] using hf.pos_part
  have hscale : Q.scale = (n : ℤ) + j := rfl
  have hbound := eLpNorm_posPart_sourceResponseJ_sub_mean_le hK P hP hstat
    Q j n hscale k hk p q 1 (by norm_num)
  change eLpNorm (fun a => max 0 (f a)) (ENNReal.ofReal 1) P ≤ _ at hbound
  rw [ENNReal.ofReal_one, eLpNorm_one_eq_lintegral_enorm hp.aestronglyMeasurable,
    ← ofReal_integral_norm_eq_lintegral_enorm hp] at hbound
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound
  have hC' : 0 ≤ EinsteinRelation.Probability.hoeffdingMomentConst 1 := by
    unfold EinsteinRelation.Probability.hoeffdingMomentConst
    positivity
  rw [ENNReal.toReal_ofReal (integral_nonneg fun a => norm_nonneg _),
    ENNReal.toReal_ofReal (by positivity)] at hreal
  have hnorm : ∀ a, ‖max 0 (f a)‖ = max 0 (f a) := by
    intro a
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_left 0 (f a))]
  simp_rw [hnorm] at hreal
  simp only [one_div, inv_one, Real.rpow_one] at hreal
  rw [show (2 : ℝ)⁻¹ = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow] at hreal
  change (∫ a, max 0 (f a) ∂P) ≤ C * ((((3 : ℝ) ^ d) ^ j)⁻¹ *
    Real.sqrt ((((3 : ℝ) ^ d) ^ j) * B ^ 2))
  dsimp only [B, C]
  linarith

end EinsteinFull.Homogenization
