import EinsteinFull.Calculus.C9LocalTimeTransposeEnergy
import EinsteinFull.Calculus.C1LocalTimeGradientMoment

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators
noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation EinsteinFull

/-- Spatial integration of the pointwise temporal energy identity. -/
private theorem transpose_spatial_weighted_energy
    {d : ℕ} {b c : ℝ} (hbc : b ≤ c)
    {W V : Vec d × ℝ → ℂ} {u v : Vec d → ℂ}
    {K : Set (Vec d)} (hK : IsCompact K)
    (hlW : MemLp W 2 ((volume.restrict K).prod (volume.restrict (Icc b c))))
    (hlV : MemLp V 2 ((volume.restrict K).prod (volume.restrict (Icc b c))))
    (hu : MemLp u 2 (volume.restrict K)) (hv : MemLp v 2 (volume.restrict K))
    {φ : Vec d → ℝ} (hφ : Continuous φ)
    {η : ℝ → ℝ} (hη : AbsolutelyContinuousOnInterval η b c)
    (hη' : ContinuousOn (deriv η) (Icc b c))
    (htime : ∀ᵐ x ∂volume.restrict K,
      (∫ s in b..c, η s * (2 * (star (W (x,s)) * V (x,s)).re)) =
        η c * ‖v x‖ ^ 2 - η b * ‖u x‖ ^ 2 -
          ∫ s in b..c, deriv η s * ‖W (x,s)‖ ^ 2) :
    (∫ s in Icc b c, η s * (∫ x in K, φ x ^ 2 *
      (2 * (star (W (x,s)) * V (x,s)).re))) =
        η c * (∫ x in K, φ x ^ 2 * ‖v x‖ ^ 2) -
        η b * (∫ x in K, φ x ^ 2 * ‖u x‖ ^ 2) -
        ∫ s in Icc b c, deriv η s * (∫ x in K, φ x ^ 2 * ‖W (x,s)‖ ^ 2) := by
  let X : Vec d × ℝ → ℂ := W
  let Y : Vec d × ℝ → ℂ := V
  let A : Vec d × ℝ → ℝ := fun p => φ p.1 ^ 2 * η p.2 * (2 * (star (X p) * Y p).re)
  let B : Vec d × ℝ → ℝ := fun p => φ p.1 ^ 2 * deriv η p.2 * ‖X p‖ ^ 2
  have hηc : ContinuousOn η (Icc b c) := by
    simpa only [uIcc_of_le hbc] using hη.continuousOn
  have hweight (ψ : ℝ → ℝ) (hψ : ContinuousOn ψ (Icc b c)) :
      ContinuousOn (fun p : Vec d × ℝ => φ p.1 ^ 2 * ψ p.2) (K ×ˢ Icc b c) :=
    ((hφ.pow 2).comp continuous_fst).continuousOn.mul
      (hψ.comp continuous_snd.continuousOn (fun p hp => hp.2))
  have hprod : Integrable (fun p => star (X p) * Y p)
      ((volume.restrict K).prod (volume.restrict (Icc b c))) :=
    hlW.star.integrable_mul hlV
  have hA : Integrable A ((volume.restrict K).prod (volume.restrict (Icc b c))) :=
    integrable_spacetime_continuousOn_mul hK
      ((Complex.reCLM.integrable_comp hprod).const_mul 2) (hweight η hηc)
  have hB : Integrable B ((volume.restrict K).prod (volume.restrict (Icc b c))) :=
    integrable_spacetime_continuousOn_mul hK
      ((memLp_two_iff_integrable_sq_norm hlW.aestronglyMeasurable).mp hlW)
      (hweight (deriv η) hη')
  have hend (a : Vec d → ℂ) (ha : MemLp a 2 (volume.restrict K)) :
      Integrable (fun x => φ x ^ 2 * ‖a x‖ ^ 2) (volume.restrict K) :=
    IntegrableOn.continuousOn_mul (hφ.pow 2).continuousOn
      ((memLp_two_iff_integrable_sq_norm ha.aestronglyMeasurable).mp ha) hK
  have heq : ∀ᵐ x ∂volume.restrict K,
      (∫ s in Icc b c, A (x, s)) =
        η c * (φ x ^ 2 * ‖v x‖ ^ 2) -
        η b * (φ x ^ 2 * ‖u x‖ ^ 2) - ∫ s in Icc b c, B (x, s) := by
    filter_upwards [htime] with x hx
    have he := hx
    rw [intervalIntegral.integral_of_le hbc, ← integral_Icc_eq_integral_Ioc,
      intervalIntegral.integral_of_le hbc, ← integral_Icc_eq_integral_Ioc] at he
    simp only [A, B, X, Y]
    simp_rw [mul_assoc (φ x ^ 2)]
    rw [integral_const_mul, integral_const_mul, he]
    ring
  calc
    _ = ∫ s in Icc b c, ∫ x in K, A (x, s) := by
      apply integral_congr_ae
      filter_upwards with s
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with x
      dsimp only [A, X, Y]
      ring
    _ = ∫ x in K, ∫ s in Icc b c, A (x, s) := (integral_integral_swap hA).symm
    _ = η c * (∫ x in K, φ x ^ 2 * ‖v x‖ ^ 2) -
        η b * (∫ x in K, φ x ^ 2 * ‖u x‖ ^ 2) -
        ∫ x in K, ∫ s in Icc b c, B (x, s) := by
      have hsplit := integral_sub
        (((hend v hv).const_mul (η c)).sub ((hend u hu).const_mul (η b)))
        hB.integral_prod_left
      have hends := integral_sub ((hend v hv).const_mul (η c))
        ((hend u hu).const_mul (η b))
      simp only [Pi.sub_apply] at hsplit hends
      rw [integral_congr_ae heq, hsplit, hends, integral_const_mul, integral_const_mul]
    _ = _ := by
      rw [integral_integral_swap hB]
      congr 1
      apply integral_congr_ae
      filter_upwards with s
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with x
      dsimp only [B, X]
      ring

private theorem transpose_cutoff_force_error_bound {d : ℕ} {φ : Vec d → ℝ}
    {ζ : ℂ} {B r : ℝ} (_hr : 0 < r)
    (hφ : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1)
    (hD : ∀ j x, |coordinateDerivative j φ x| ≤ B / r) (x : Vec d) :
    ‖ζ‖ ^ 2 * φ x ^ 2 + ∑ j, (coordinateDerivative j φ x) ^ 2 ≤
      ‖ζ‖ ^ 2 + (d : ℝ) * B ^ 2 / r ^ 2 := by
  have hφsq : φ x ^ 2 ≤ 1 := by nlinarith [hφ x]
  have hd j : (coordinateDerivative j φ x) ^ 2 ≤ B ^ 2 / r ^ 2 := by
    have h := mul_self_le_mul_self (abs_nonneg (coordinateDerivative j φ x)) (hD j x)
    simpa only [← sq, sq_abs, div_pow] using h
  have hs : (∑ j, (coordinateDerivative j φ x) ^ 2) ≤ (d : ℝ) * (B ^ 2 / r ^ 2) := by
    simpa using Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hd j)
  simpa only [mul_one, mul_div_assoc] using
    add_le_add (mul_le_mul_of_nonneg_left hφsq (sq_nonneg ‖ζ‖)) hs

private theorem transpose_timeSliceL2_of_cutoff_energy {d : ℕ}
    {b c r B L C : ℝ} (_hbc : b < c) (hr : 0 < r)
    (hL : 0 < L) (hC : 0 ≤ C) {ζ : ℂ} {z : Vec d}
    {W : Vec d × ℝ → ℂ} {D : Fin d → Vec d × ℝ → ℂ} {U : Vec d → ℂ}
    (hW : MemLp W 2 ((volume.restrict {x | euclideanNorm (x - z) ≤ 2 * r}).prod
      (volume.restrict (Icc b c))))
    (hU : MemLp U 2 (volume.restrict {x | euclideanNorm (x - z) ≤ 2 * r}))
    {φ : Vec d → ℝ} (hφ : IsSpatialTest univ φ)
    (hφrange : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1)
    (hone : ∀ x, euclideanNorm (x - z) ≤ r → φ x = 1)
    (hzero : ∀ x, 2 * r ≤ euclideanNorm (x - z) → φ x = 0)
    (hφD : ∀ j x, |coordinateDerivative j φ x| ≤ B / r)
    {η : ℝ → ℝ} (hη : ContinuousOn η (Icc b c))
    (hηd : ContinuousOn (deriv η) (Icc b c))
    (hηrange : ∀ s ∈ Icc b c, 0 ≤ η s ∧ η s ≤ 1 ∧
      0 ≤ deriv η s ∧ deriv η s ≤ 2 / (c - b))
    (henergy : (L⁻¹ / 4) *
        (∫ s in Icc b c, η s * (∫ x, φ x ^ 2 * ∑ j, ‖D j (x, s)‖ ^ 2)) ≤
      -(∫ x, φ x ^ 2 * ‖U x‖ ^ 2) / 2 +
        (∫ s in Icc b c, deriv η s * (∫ x, φ x ^ 2 * ‖W (x, s)‖ ^ 2)) / 2 +
        C * (∫ s in Icc b c, η s *
          (∫ x, (‖ζ‖ ^ 2 * φ x ^ 2 + ∑ j, (coordinateDerivative j φ x) ^ 2) *
            ‖W (x, s)‖ ^ 2))) :
    (∫ x in {x | euclideanNorm (x - z) ≤ r}, ‖U x‖ ^ 2) ≤
      2 * ((c - b)⁻¹ + C * (‖ζ‖ ^ 2 + (d : ℝ) * B ^ 2 / r ^ 2)) *
        (∫ s in Icc b c, ∫ x in {x | euclideanNorm (x - z) ≤ 2 * r},
          ‖W (x, s)‖ ^ 2) := by
  let K := {x : Vec d | euclideanNorm (x - z) ≤ 2 * r}
  have hK : IsCompact K := isCompact_physical_euclidean_closedBall z (2 * r)
  have hz x (hx : x ∉ K) : φ x = 0 := hzero x (not_le.mp hx).le
  have hsupport : tsupport φ ⊆ K := physical_cutoff_tsupport_subset hzero
  have hdz j x (hx : x ∉ K) : coordinateDerivative j φ x = 0 := by
    have hxs : x ∉ tsupport φ := fun hm => hx (hsupport hm)
    simp [coordinateDerivative, fderiv_of_notMem_tsupport ℝ hxs]
  have hiW := (memLp_two_iff_integrable_sq_norm hW.aestronglyMeasurable).mp hW
  have ht := physical_spacetime_weight_integral_le hK hiW
    (fun p => sq_nonneg ‖W p‖) (hφ.1.continuous.pow 2)
    (fun x hx => by simp only [Pi.pow_apply, hz x hx, zero_pow (by decide : 2 ≠ 0)])
    hηd (A := 2 / (c - b)) (by
      intro s hs x hx
      have hsq : φ x ^ 2 ≤ 1 := by nlinarith [hφrange x]
      simpa only [Pi.pow_apply, mul_one] using
        (mul_le_mul_of_nonneg_left hsq (hηrange s hs).2.2.1).trans
          (by simpa only [mul_one] using (hηrange s hs).2.2.2))
  have hd j : Continuous (coordinateDerivative j φ) :=
    ((contDiff_infty_iff_fderiv.mp hφ.1).2.clm_apply contDiff_const).continuous
  have he := physical_spacetime_weight_integral_le hK hiW
    (fun p => sq_nonneg ‖W p‖)
    ((continuous_const.mul (hφ.1.continuous.pow 2)).add
      (continuous_finsetSum _ (fun j _ => (hd j).pow 2)))
    (fun x hx => by simp [hz x hx, hdz, hx]) hη
    (A := ‖ζ‖ ^ 2 + (d : ℝ) * B ^ 2 / r ^ 2) (by
      intro s hs x hx
      have hp : 0 ≤ ‖ζ‖ ^ 2 * φ x ^ 2 + ∑ j, (coordinateDerivative j φ x) ^ 2 :=
        add_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))
          (Finset.sum_nonneg (fun j _ => sq_nonneg _))
      exact (mul_le_mul_of_nonneg_right (hηrange s hs).2.1 hp).trans
        (by simpa only [one_mul] using
          transpose_cutoff_force_error_bound hr hφrange hφD x))
  have hiU := (memLp_two_iff_integrable_sq_norm hU.aestronglyMeasurable).mp hU
  have hiφ : IntegrableOn (fun x => φ x ^ 2 * ‖U x‖ ^ 2) K volume :=
    IntegrableOn.continuousOn_mul (hφ.1.continuous.pow 2).continuousOn hiU hK
  have hinner : (∫ x in {x | euclideanNorm (x - z) ≤ r}, ‖U x‖ ^ 2) ≤
      ∫ x, φ x ^ 2 * ‖U x‖ ^ 2 := by
    have heq : (∫ x in {x | euclideanNorm (x - z) ≤ r}, ‖U x‖ ^ 2) =
        ∫ x in {x | euclideanNorm (x - z) ≤ r}, φ x ^ 2 * ‖U x‖ ^ 2 := by
      apply setIntegral_congr_fun (isCompact_physical_euclidean_closedBall z r).measurableSet
      intro x hx
      change ‖U x‖ ^ 2 = φ x ^ 2 * ‖U x‖ ^ 2
      rw [hone x hx]
      simp
    have hm := setIntegral_mono_set hiφ
      (Eventually.of_forall (fun x => mul_nonneg (sq_nonneg _) (sq_nonneg ‖U x‖)))
      (Eventually.of_forall (fun x (hx : euclideanNorm (x - z) ≤ r) =>
        show x ∈ K from le_trans hx (by linarith)))
    have hzint : (∫ x in K, φ x ^ 2 * ‖U x‖ ^ 2) =
        ∫ x, φ x ^ 2 * ‖U x‖ ^ 2 :=
      setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun x hx => by rw [hz x hx]; simp)
    change (∫ x in {x | euclideanNorm (x - z) ≤ r}, φ x ^ 2 * ‖U x‖ ^ 2) ≤
      (∫ x in K, φ x ^ 2 * ‖U x‖ ^ 2) at hm
    rw [← heq, hzint] at hm
    exact hm
  have hp : 0 ≤ (L⁻¹ / 4) *
      (∫ s in Icc b c, η s * (∫ x, φ x ^ 2 * ∑ j, ‖D j (x, s)‖ ^ 2)) := by
    apply mul_nonneg (by positivity)
    apply setIntegral_nonneg measurableSet_Icc
    intro s hs
    exact mul_nonneg (hηrange s hs).1 (integral_nonneg (fun x =>
      mul_nonneg (sq_nonneg _) (Finset.sum_nonneg (fun j _ => sq_nonneg _))))
  simp only [Pi.add_apply, Pi.mul_apply, Pi.pow_apply] at ht he
  simp only [div_eq_mul_inv] at ht
  have hce := mul_le_mul_of_nonneg_left he hC
  dsimp only [K] at ht hce
  nlinarith only [henergy, hp, ht, hce, hinner]


private theorem transpose_ae_joint_cutoff_energy
    {d : ℕ} [Fact (2 ≤ d)] {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀}
    {i : Fin d} {ζ : ℂ} {b c : ℝ}
    {u v : ℝ → Lp ℂ 2 (reducedLaw Q)}
    (hgen : ∀ s ∈ Icc b c, IsComplexTransposeGeneratorPair Q i ζ (u s) (v s))
    {W V : ℝ × FieldPair d → ℂ}
    (hW : Measurable W) (hV : Measurable V)
    (heW : ∀ s, (fun ω => W (s, ω)) =ᵐ[reducedLaw Q] u s)
    (heV : ∀ s, (fun ω => V (s, ω)) =ᵐ[reducedLaw Q] v s)
    {φ : Vec d → ℝ} (hφ : IsSpatialTest univ φ) :
    let L := Real.exp (2 * Λ₀) * Λ₀
    ∀ᵐ ω ∂reducedLaw Q, ∀ᵐ s ∂volume.restrict (Icc b c),
      0 ≤
        (∫ x, (φ x : ℂ) ^ 2 * star (W (s, translate x ω)) * (-V (s, translate x ω))).re +
        (10 * L ^ 3) *
          (∫ x, (‖ζ‖ ^ 2 * φ x ^ 2 +
            (∑ j, (coordinateDerivative j φ x) ^ 2)) * ‖W (s, translate x ω)‖ ^ 2) := by
  intro L
  let := reducedLaw_probability Q
  have hshift {U : ℝ × FieldPair d → ℂ} (hU : Measurable U) :
      Measurable (fun q : (ℝ × FieldPair d) × Vec d =>
        U (q.1.1, translate q.2 q.1.2)) :=
    hU.comp ((measurable_fst.comp measurable_fst).prodMk
      (Probability.continuous_translate.measurable.comp
        (measurable_snd.prodMk (measurable_snd.comp measurable_fst))))
  have hφm : Measurable (fun q : (ℝ × FieldPair d) × Vec d => φ q.2) :=
    hφ.1.continuous.measurable.comp measurable_snd
  have hder j : Continuous (coordinateDerivative j φ) :=
    ((contDiff_infty_iff_fderiv.mp hφ.1).2.clm_apply contDiff_const).continuous
  let B := (fun p : ℝ × FieldPair d =>
      (∫ x, (φ x : ℂ) ^ 2 * star (W (p.1, translate x p.2)) * (-V (p.1, translate x p.2))).re +
        (10 * L ^ 3) *
          (∫ x, (‖ζ‖ ^ 2 * φ x ^ 2 +
            (∑ j, (coordinateDerivative j φ x) ^ 2)) * ‖W (p.1, translate x p.2)‖ ^ 2))
  have hB : Measurable B := by
    have hmain : Measurable (fun p : ℝ × FieldPair d =>
        ∫ x, (φ x : ℂ) ^ 2 * star (W (p.1, translate x p.2)) * (-V (p.1, translate x p.2))) :=
      (((Complex.continuous_ofReal.measurable.comp hφm).pow_const 2).mul
      ((hshift hW).stronglyMeasurable.star.measurable) |>.mul (hshift hV).neg).stronglyMeasurable.integral_prod_right'.measurable
    have herr : Measurable (fun q : (ℝ × FieldPair d) × Vec d =>
        (‖ζ‖ ^ 2 * φ q.2 ^ 2 + (∑ j, (coordinateDerivative j φ q.2) ^ 2)) *
          ‖W (q.1.1, translate q.2 q.1.2)‖ ^ 2) :=
      ((measurable_const.mul (hφm.pow_const 2)).add
      (Finset.measurable_sum _ fun j _ =>
        (((hder j).measurable.comp measurable_snd).pow_const 2))).mul
          ((hshift hW).norm.pow_const 2)
    exact (Complex.continuous_re.measurable.comp hmain).add
      (measurable_const.mul herr.stronglyMeasurable.integral_prod_right'.measurable)
  change ∀ᵐ ω ∂reducedLaw Q, ∀ᵐ s ∂volume.restrict (Icc b c), 0 ≤ B (s, ω)
  apply (Measure.ae_ae_comm (p := fun s ω => 0 ≤ B (s, ω))
    (measurableSet_le measurable_const hB)).mp
  filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
  have hew := ae_spatial_complex_orbit_congr (reducedLaw Q) (reducedLaw_stationary Q)
    (hW.comp (measurable_const.prodMk measurable_id)) (Lp.stronglyMeasurable (u s)).measurable (heW s)
  have hev := ae_spatial_complex_orbit_congr (reducedLaw Q) (reducedLaw_stationary Q)
    (hV.comp (measurable_const.prodMk measurable_id)) (Lp.stronglyMeasurable (v s)).measurable (heV s)
  obtain ⟨G, hG, _⟩ := hgen s hs
  have hL : 0 < L := mul_pos (Real.exp_pos _)
    (lt_of_lt_of_le zero_lt_one Q.ellipticity_parameter)
  filter_upwards [local_time_transpose_physical_cutoff_energy (hgen s hs) hG, hew, hev]
    with ω henergy hw hv
  have hnonneg : 0 ≤ (L⁻¹ / 4) * (∫ x, φ x ^ 2 * ∑ j, ‖G j (translate x ω)‖ ^ 2) :=
    mul_nonneg (by positivity) (integral_nonneg (fun x =>
      mul_nonneg (sq_nonneg _) (Finset.sum_nonneg (fun j _ => sq_nonneg _))))
  have hmain : (∫ x, (φ x : ℂ) ^ 2 * star (W (s, translate x ω)) * (-V (s, translate x ω))) =
      ∫ x, (φ x : ℂ) ^ 2 * star ((u s) (translate x ω)) * (-(v s) (translate x ω)) := by
    apply integral_congr_ae
    filter_upwards [hw, hv] with x hx hy
    change W (s, translate x ω) = _ at hx
    change V (s, translate x ω) = _ at hy
    rw [hx, hy]
  have herr : (∫ x, (‖ζ‖ ^ 2 * φ x ^ 2 + (∑ j, (coordinateDerivative j φ x) ^ 2)) *
      ‖W (s, translate x ω)‖ ^ 2) =
      ∫ x, (‖ζ‖ ^ 2 * φ x ^ 2 + (∑ j, (coordinateDerivative j φ x) ^ 2)) *
        ‖(u s) (translate x ω)‖ ^ 2 := by
    apply integral_congr_ae
    filter_upwards [hw] with x hx
    change W (s, translate x ω) = _ at hx
    rw [hx]
  change 0 ≤ _ + _ * _
  rw [hmain, herr]
  exact hnonneg.trans (henergy φ hφ)


private theorem transpose_cutoff_energy_time_integral {d : ℕ}
    {Λ₀ : ℝ} {ζ : ℂ} {b c : ℝ}
    {W V : Vec d × ℝ → ℂ}
    {φ : Vec d → ℝ} (hφ : IsSpatialTest univ φ)
    (hW : MemLp W 2 ((volume.restrict (tsupport φ)).prod (volume.restrict (Icc b c))))
    (hV : MemLp V 2 ((volume.restrict (tsupport φ)).prod (volume.restrict (Icc b c))))
    {η : ℝ → ℝ} (hη : ContinuousOn η (Icc b c))
    (hηpos : ∀ s ∈ Icc b c, 0 ≤ η s)
    (hcoer : ∀ᵐ s ∂volume.restrict (Icc b c),
      0 ≤
        (∫ x, (φ x : ℂ) ^ 2 * star (W (x, s)) * (-V (x, s))).re +
          (10 * (Real.exp (2 * Λ₀) * Λ₀) ^ 3) *
            (∫ x, (‖ζ‖ ^ 2 * φ x ^ 2 + (∑ j, (coordinateDerivative j φ x) ^ 2)) *
              ‖W (x, s)‖ ^ 2)) :
    0 ≤
      (∫ s in Icc b c, η s *
        (∫ x, (φ x : ℂ) ^ 2 * star (W (x, s)) * (-V (x, s))).re) +
      (10 * (Real.exp (2 * Λ₀) * Λ₀) ^ 3) *
        (∫ s in Icc b c, η s *
          (∫ x, (‖ζ‖ ^ 2 * φ x ^ 2 + (∑ j, (coordinateDerivative j φ x) ^ 2)) *
            ‖W (x, s)‖ ^ 2)) := by
  have hK := hφ.2.1
  have hz : ∀ x, x ∉ tsupport φ → φ x = 0 := fun x hx => image_eq_zero_of_notMem_tsupport hx
  have hd j : Continuous (coordinateDerivative j φ) :=
    ((contDiff_infty_iff_fderiv.mp hφ.1).2.clm_apply contDiff_const).continuous
  have hdz j x (hx : x ∉ tsupport φ) : coordinateDerivative j φ x = 0 := by
    simp [coordinateDerivative, fderiv_of_notMem_tsupport ℝ hx]
  have herr := integrable_time_integral_compact_spatial_weight hK
    (ψ := fun x => ‖ζ‖ ^ 2 * φ x ^ 2 + ∑ j, (coordinateDerivative j φ x) ^ 2)
    ((memLp_two_iff_integrable_sq_norm hW.aestronglyMeasurable).mp hW)
    ((continuous_const.mul (hφ.1.continuous.pow 2)).add
      (continuous_finsetSum _ (fun j _ => (hd j).pow 2)))
    (fun x hx => by simp [hz x hx, hdz, hx])
  have hm := integrable_time_integral_compact_spatial_weight hK
    (hW.star.integrable_mul hV.neg)
    ((Complex.continuous_ofReal.comp hφ.1.continuous).pow 2)
    (fun x hx => by simp [Function.comp_def, hz x hx])
  have hmain : Integrable (fun s => η s *
      (∫ x, (φ x : ℂ) ^ 2 * star (W (x, s)) * (-V (x, s))).re)
      (volume.restrict (Icc b c)) := by
    simp_rw [mul_assoc] at ⊢
    exact IntegrableOn.continuousOn_mul hη (Complex.reCLM.integrable_comp hm) isCompact_Icc
  have he := IntegrableOn.continuousOn_mul hη herr isCompact_Icc
  have hi := integral_mono_ae (integrable_zero _ _ _ : Integrable (fun _ : ℝ => (0 : ℝ)) (volume.restrict (Icc b c)))
    (hmain.add (he.const_mul
      (10 * (Real.exp (2 * Λ₀) * Λ₀) ^ 3)))
    (by
      filter_upwards [hcoer, ae_restrict_mem measurableSet_Icc] with s hs hsm
      simp only [Pi.add_apply, Pi.zero_apply]
      nlinarith only [mul_le_mul_of_nonneg_left hs (hηpos s hsm)])
  simp only [Pi.add_apply, Pi.zero_apply] at hi
  simpa only [integral_zero, integral_add hmain (he.const_mul _), integral_const_mul] using hi


/-- Terminal-ball trace of the actual transpose semigroup, with a cutoff
constant chosen before the environment law and force. -/
theorem local_time_transpose_ae_terminal_ball_L2
    (d : ℕ) [Fact (2 ≤ d)] :
    ∃ B : ℝ, 0 < B ∧
    ∀ (Λ₀ r₀ : ℝ) (Q : EnvironmentLaw d Λ₀ r₀)
      (i : Fin d) (ζ : ℂ)
      (P T : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)),
      IsComplexEnvironmentSemigroup Q i ζ P →
      IsComplexTransposeSemigroup Q P T →
    ∀ (f g : Lp ℂ 2 (reducedLaw Q)),
      IsComplexTransposeGeneratorPair Q i ζ f g →
    ∃ W : ℝ × FieldPair d → ℂ,
      Measurable W ∧
      (∀ s, (fun ω => W (s, ω)) =ᵐ[reducedLaw Q] T s.toNNReal f) ∧
      ∀ b c : ℝ, 0 ≤ b → b < c →
        ∀ (z : Vec d) (r : ℝ), 0 < r →
          ∀ᵐ ω ∂reducedLaw Q,
            (∫ x in {x | euclideanNorm (x - z) ≤ r},
              ‖(T c.toNNReal f) (translate x ω)‖ ^ 2) ≤
            2 * ((c - b)⁻¹ +
              10 * (Real.exp (2 * Λ₀) * Λ₀) ^ 3 *
                (‖ζ‖ ^ 2 + (d : ℝ) * B ^ 2 / r ^ 2)) *
              (∫ s in Icc b c, ∫ x in {x | euclideanNorm (x - z) ≤ 2 * r},
                ‖W (s, translate x ω)‖ ^ 2) := by
  obtain ⟨B, hB, hcutoff⟩ := exists_physical_euclidean_cutoff d
  refine ⟨B, hB, ?_⟩
  intro Λ₀ r₀ Q i ζ P T hP hT f g hfg
  let := reducedLaw_probability Q
  let L := Real.exp (2 * Λ₀) * Λ₀
  have hL : 0 < L := mul_pos (Real.exp_pos _)
    (lt_of_lt_of_le zero_lt_one Q.ellipticity_parameter)
  have hC : 0 ≤ 10 * L ^ 3 := by positivity
  obtain ⟨W, V, hW, hV, heW, heV, htime⟩ :=
    local_time_transpose_ae_physical_weighted_energy hP hT hfg
  refine ⟨W, hW, heW, ?_⟩
  have hw : Continuous (fun s : ℝ => T s.toNNReal f) :=
    (hT.continuous_apply hP f).comp continuous_real_toNNReal
  have hv : Continuous (fun s : ℝ => T s.toNNReal g) :=
    (hT.continuous_apply hP g).comp continuous_real_toNNReal
  intro b c hb hbc z r hr
  obtain ⟨φ, hφ, hφrange, hone, hzero, hφD⟩ := hcutoff z r hr
  obtain ⟨η, hη, hηd, hηb, hηc, hηbounds⟩ := exists_physical_temporal_cutoff hbc
  have hηcont : ContinuousOn η (Icc b c) := by
    simpa only [uIcc_of_le hbc.le] using hη.continuousOn
  have hηrange s (hs : s ∈ Icc b c) : 0 ≤ η s ∧ η s ≤ 1 ∧
      0 ≤ deriv η s ∧ deriv η s ≤ 2 / (c - b) :=
    ⟨(hηbounds s hs).1, (hηbounds s hs).2.1,
      (hηbounds s hs).2.2.1, (hηbounds s hs).2.2.2.1⟩
  have hwI : IntegrableOn (fun s => ‖T s.toNNReal f‖ ^ 2) (Icc b c) volume :=
    (hw.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc
  have hvI : IntegrableOn (fun s => ‖T s.toNNReal g‖ ^ 2) (Icc b c) volume :=
    (hv.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc
  have hlocalW := ae_locally_memLp_joint_spatial_translate
    (reducedLaw Q) (reducedLaw_stationary Q) hW
    (integrable_sq_joint_l2_representative hwI hW heW)
  have hlocalV := ae_locally_memLp_joint_spatial_translate
    (reducedLaw Q) (reducedLaw_stationary Q) hV
    (integrable_sq_joint_l2_representative hvI hV heV)
  have hcoer := transpose_ae_joint_cutoff_energy (b := b) (c := c)
    (fun s _ => hT.map_generator hP hfg s.toNNReal) hW hV heW heV hφ
  filter_upwards [htime b c hb hbc.le, hlocalW, hlocalV, hcoer,
    ae_complex_orbit_memLp_on_all_compacts (reducedLaw Q) (reducedLaw_stationary Q)
      (T b.toNNReal f),
    ae_complex_orbit_memLp_on_all_compacts (reducedLaw Q) (reducedLaw_stationary Q)
      (T c.toNNReal f)] with ω ht hlW hlV hc hUb hUc
  have hineq := transpose_cutoff_energy_time_integral hφ
    (hlW _ hφ.2.1) (hlV _ hφ.2.1) hηcont
    (fun s hs => (hηbounds s hs).1) hc
  have hp := (hlW (tsupport φ) hφ.2.1).star.integrable_mul
    (hlV (tsupport φ) hφ.2.1)
  have hpφ : Integrable (fun p : Vec d × ℝ =>
      (φ p.1 : ℂ) ^ 2 * star (W (p.2, translate p.1 ω)) * V (p.2, translate p.1 ω))
      ((volume.restrict (tsupport φ)).prod (volume.restrict (Icc b c))) := by
    have hi : Integrable (fun p : Vec d × ℝ =>
        (φ p.1 : ℂ) ^ 2 * (star (W (p.2, translate p.1 ω)) * V (p.2, translate p.1 ω)))
        ((volume.restrict (tsupport φ)).prod (volume.restrict (Icc b c))) := by
      rw [Measure.prod_restrict] at hp ⊢
      exact IntegrableOn.continuousOn_mul
        (((Complex.continuous_ofReal.comp hφ.1.continuous).pow 2).comp
          continuous_fst).continuousOn hp (hφ.2.1.prod isCompact_Icc)
    simpa only [mul_assoc] using hi
  have hpair : (∫ s in Icc b c, η s *
      (∫ x, (φ x : ℂ) ^ 2 * star (W (s, translate x ω)) *
        (-V (s, translate x ω))).re) =
      -(∫ s in Icc b c, η s * (∫ x, φ x ^ 2 *
        (2 * (star (W (s, translate x ω)) * V (s, translate x ω)).re))) / 2 := by
    calc
      _ = ∫ s in Icc b c, -(η s * (∫ x, φ x ^ 2 *
          (2 * (star (W (s, translate x ω)) * V (s, translate x ω)).re))) / 2 := by
        apply integral_congr_ae
        filter_upwards [hpφ.prod_left_ae] with s hs
        rw [physical_cutoff_generator_pairing_eq hs]
        ring
      _ = _ := by rw [integral_div, integral_neg]
  have hres (F : Vec d → ℝ) :
      (∫ x in tsupport φ, φ x ^ 2 * F x) = ∫ x, φ x ^ 2 * F x :=
    setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun x hx => by simp [image_eq_zero_of_notMem_tsupport hx])
  have htemporal := transpose_spatial_weighted_energy hbc.le hφ.2.1
    (hlW _ hφ.2.1) (hlV _ hφ.2.1) (hUb _ hφ.2.1) (hUc _ hφ.2.1)
    hφ.1.continuous hη hηd (by
      filter_upwards [ht (tsupport φ) hφ.2.1] with x hx
      exact hx η hη)
  simp_rw [hres] at htemporal
  rw [hpair, htemporal, hηb, hηc, zero_mul, one_mul, sub_zero] at hineq
  have hK := isCompact_physical_euclidean_closedBall z (2 * r)
  apply transpose_timeSliceL2_of_cutoff_energy
    (D := fun _ _ => 0) hbc hr hL hC
    (hlW _ hK) (hUc _ hK) hφ hφrange hone hzero hφD hηcont hηd hηrange
  simp only [norm_zero, zero_pow (by decide : 2 ≠ 0), Finset.sum_const_zero,
    mul_zero, integral_zero]
  linarith only [hineq]

end EinsteinFull.Blueprint
