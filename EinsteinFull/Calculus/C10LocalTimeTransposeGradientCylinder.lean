import EinsteinFull.Calculus.C1LocalTimeGradientMoment
import EinsteinFull.Calculus.C9LocalTimeTransposeEnergy
import EinsteinFull.Calculus.C9LocalTimeTransposeTrace
import EinsteinFull.Work.W2.TransposeResolventGradientContinuitySupport

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators
noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation EinsteinFull

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

private theorem exists_transpose_third_temporal_cutoff {b c : ℝ} (hbc : b < c) :
    ∃ η : ℝ → ℝ, AbsolutelyContinuousOnInterval η b c ∧
      ContinuousOn (deriv η) (Icc b c) ∧ η b = 0 ∧ η c = 1 ∧
      ∀ s ∈ Icc b c, 0 ≤ η s ∧ η s ≤ 1 ∧
        0 ≤ deriv η s ∧ deriv η s ≤ 2 / (c - b) ∧
        ((2 * b + c) / 3 ≤ s → 1 / 9 ≤ η s) := by
  let η : ℝ → ℝ := fun s => ((s - b) / (c - b)) ^ 2
  have hΔ : 0 < c - b := sub_pos.mpr hbc
  have hs : ContDiff ℝ 1 η := by dsimp [η]; fun_prop
  have hd s : deriv η s = 2 * ((s - b) / (c - b)) / (c - b) := by
    have h := (((hasDerivAt_id s).sub_const b).div_const (c - b)).pow 2
    simp only [Nat.reduceSub, pow_one, Nat.cast_ofNat, id_eq] at h
    change HasDerivAt η (2 * ((s - b) / (c - b)) * (1 / (c - b))) s at h
    rw [h.deriv]
    ring
  refine ⟨η, hs.contDiffOn.absolutelyContinuousOnInterval, ?_, ?_, ?_, ?_⟩
  · have he : deriv η = fun s => 2 * ((s - b) / (c - b)) / (c - b) := funext hd
    rw [he]
    fun_prop
  · simp [η]
  · simp [η, hΔ.ne']
  · intro s hs
    have hq : 0 ≤ (s - b) / (c - b) ∧ (s - b) / (c - b) ≤ 1 := by
      constructor
      · exact div_nonneg (sub_nonneg.mpr hs.1) hΔ.le
      · apply (div_le_one hΔ).mpr
        linarith [hs.2]
    refine ⟨sq_nonneg _, ?_, ?_, ?_, ?_⟩
    · dsimp [η]
      nlinarith
    · rw [hd]
      exact div_nonneg (mul_nonneg (by norm_num) hq.1) hΔ.le
    · rw [hd]
      exact div_le_div_of_nonneg_right (by linarith [hq.2]) hΔ.le
    · intro hm
      have hhalf : (1 / 3 : ℝ) ≤ (s - b) / (c - b) := by
        apply (le_div_iff₀ hΔ).mpr
        linarith
      dsimp [η]
      nlinarith [sq_nonneg ((s - b) / (c - b) - 1 / 3)]

private theorem transpose_inner_cylinder_integral_le {d : ℕ} {K S : Set (Vec d)}
    (hK : IsCompact K) (hS : MeasurableSet S) (hSK : S ⊆ K)
    {b c : ℝ} (hbc : b ≤ c) {F : Vec d × ℝ → ℝ}
    (hF : Integrable F ((volume.restrict K).prod (volume.restrict (Icc b c))))
    (hFpos : ∀ p, 0 ≤ F p) {φ : Vec d → ℝ} (hφ : Continuous φ)
    (hzero : ∀ x, x ∉ K → φ x = 0) (hone : ∀ x ∈ S, φ x = 1)
    {η : ℝ → ℝ} (hη : ContinuousOn η (Icc b c))
    (hηpos : ∀ s ∈ Icc b c, 0 ≤ η s)
    (hηlower : ∀ s ∈ Icc ((2 * b + c) / 3) c, 1 / 9 ≤ η s) :
    (∫ s in Icc ((2 * b + c) / 3) c, ∫ x in S, F (x, s)) ≤
      9 * (∫ s in Icc b c, η s * (∫ x, φ x ^ 2 * F (x, s))) := by
  have hJI : Icc ((2 * b + c) / 3) c ⊆ Icc b c := by
    intro s hs
    exact ⟨by linarith [hs.1], hs.2⟩
  have hw := IntegrableOn.continuousOn_mul hη
    (integrable_time_integral_compact_spatial_weight hK hF (hφ.pow 2)
      (fun x hx => by simp only [Pi.pow_apply, hzero x hx, zero_pow (by decide : 2 ≠ 0)])) isCompact_Icc
  have hinner := hF.mono_measure
    (Measure.prod_mono (Measure.restrict_mono hSK le_rfl) le_rfl)
  have hiJ := hinner.integral_prod_right.mono_measure (Measure.restrict_mono hJI le_rfl)
  have hwJ := Integrable.mono_measure hw (Measure.restrict_mono hJI le_rfl)
  have hcmp : (∫ s in Icc ((2 * b + c) / 3) c, ∫ x in S, F (x, s)) ≤
      9 * (∫ s in Icc ((2 * b + c) / 3) c, η s * (∫ x, φ x ^ 2 * F (x, s))) := by
    have hm := integral_mono_ae hiJ (hwJ.const_mul 9) (by
      filter_upwards [ae_restrict_of_ae_restrict_of_subset hJI hF.prod_left_ae,
        ae_restrict_mem measurableSet_Icc] with s hs hsm
      have hi : IntegrableOn (fun x => φ x ^ 2 * F (x, s)) K volume :=
        IntegrableOn.continuousOn_mul (hφ.pow 2).continuousOn hs hK
      have he : (∫ x in S, F (x, s)) = ∫ x in S, φ x ^ 2 * F (x, s) := by
        apply setIntegral_congr_fun hS
        intro x hx
        change F (x, s) = φ x ^ 2 * F (x, s)
        rw [hone x hx]
        simp
      have hsp := setIntegral_mono_set hi
        (Eventually.of_forall (fun x => mul_nonneg (sq_nonneg _) (hFpos (x, s))))
        (Eventually.of_forall (fun x hx => hSK hx))
      have hz : (∫ x in K, φ x ^ 2 * F (x, s)) = ∫ x, φ x ^ 2 * F (x, s) :=
        setIntegral_eq_integral_of_forall_compl_eq_zero
          (fun x hx => by rw [hzero x hx]; simp)
      rw [← he, hz] at hsp
      have hp : 0 ≤ ∫ x, φ x ^ 2 * F (x, s) :=
        integral_nonneg (fun x => mul_nonneg (sq_nonneg _) (hFpos (x, s)))
      simp only [Pi.pow_apply]
      nlinarith [mul_le_mul_of_nonneg_right (hηlower s hsm) hp])
    simpa only [Pi.pow_apply, integral_const_mul] using hm
  apply hcmp.trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply setIntegral_mono_set hw _ (Eventually.of_forall (fun s hs => hJI hs))
  filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
  exact mul_nonneg (hηpos s hs)
    (integral_nonneg (fun x => mul_nonneg (sq_nonneg _) (hFpos (x, s))))

private theorem transpose_ae_joint_cutoff_energy
    {d : ℕ} [Fact (2 ≤ d)] {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀}
    {i : Fin d} {ζ : ℂ} {b c : ℝ}
    {u v : ℝ → Lp ℂ 2 (reducedLaw Q)}
    (hgen : ∀ s ∈ Icc b c, IsComplexTransposeGeneratorPair Q i ζ (u s) (v s))
    {W V : ℝ × FieldPair d → ℂ}
    (hW : Measurable W) (hV : Measurable V)
    (heW : ∀ s, (fun ω => W (s, ω)) =ᵐ[reducedLaw Q] u s)
    (heV : ∀ s, (fun ω => V (s, ω)) =ᵐ[reducedLaw Q] v s)
    {G : ℝ → Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hG : ∀ s, HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) (u s) (G s))
    {D : Fin d → ℝ × FieldPair d → ℂ}
    (hD : ∀ j, Measurable (D j))
    (heD : ∀ j s, (fun ω => D j (s, ω)) =ᵐ[reducedLaw Q] G s j)
    {φ : Vec d → ℝ} (hφ : IsSpatialTest univ φ) :
    let L := Real.exp (2 * Λ₀) * Λ₀
    ∀ᵐ ω ∂reducedLaw Q, ∀ᵐ s ∂volume.restrict (Icc b c),
      (L⁻¹ / 4) * (∫ x, φ x ^ 2 * ∑ j, ‖D j (s, translate x ω)‖ ^ 2) ≤
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
  let A := fun p : ℝ × FieldPair d =>
    (L⁻¹ / 4) * (∫ x, φ x ^ 2 * ∑ j, ‖D j (p.1, translate x p.2)‖ ^ 2)
  have hA : Measurable A :=
    measurable_const.mul ((hφm.pow_const 2).mul
      (Finset.measurable_sum _ fun j _ => (hshift (hD j)).norm.pow_const 2)).stronglyMeasurable.integral_prod_right'.measurable
  change ∀ᵐ ω ∂reducedLaw Q, ∀ᵐ s ∂volume.restrict (Icc b c), A (s, ω) ≤ B (s, ω)
  apply (Measure.ae_ae_comm (p := fun s ω => A (s, ω) ≤ B (s, ω))
    (measurableSet_le hA hB)).mp
  filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
  have hew := ae_spatial_complex_orbit_congr (reducedLaw Q) (reducedLaw_stationary Q)
    (hW.comp (measurable_const.prodMk measurable_id)) (Lp.stronglyMeasurable (u s)).measurable (heW s)
  have hev := ae_spatial_complex_orbit_congr (reducedLaw Q) (reducedLaw_stationary Q)
    (hV.comp (measurable_const.prodMk measurable_id)) (Lp.stronglyMeasurable (v s)).measurable (heV s)
  have hed (j : Fin d) := ae_spatial_complex_orbit_congr (reducedLaw Q) (reducedLaw_stationary Q)
    ((hD j).comp (measurable_const.prodMk measurable_id))
    (Lp.stronglyMeasurable (G s j)).measurable (heD j s)
  filter_upwards [local_time_transpose_physical_cutoff_energy (hgen s hs) (hG s), hew, hev,
    ae_all_iff.mpr hed] with ω henergy hw hv hd
  have hgrad : (∫ x, φ x ^ 2 * ∑ j, ‖D j (s, translate x ω)‖ ^ 2) =
      ∫ x, φ x ^ 2 * ∑ j, ‖G s j (translate x ω)‖ ^ 2 := by
    apply integral_congr_ae
    filter_upwards [ae_all_iff.mpr hd] with x hx
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    have hj : D j (s, translate x ω) = G s j (translate x ω) := hx j
    rw [hj]
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
  change (L⁻¹ / 4) * _ ≤ _ + _ * _
  rw [hgrad, hmain, herr]
  exact henergy φ hφ



private theorem transpose_cutoff_energy_time_integral {d : ℕ}
    {Λ₀ : ℝ} {ζ : ℂ} {b c : ℝ}
    {W V : Vec d × ℝ → ℂ}
    {φ : Vec d → ℝ} (hφ : IsSpatialTest univ φ)
    (hW : MemLp W 2 ((volume.restrict (tsupport φ)).prod (volume.restrict (Icc b c))))
    (hV : MemLp V 2 ((volume.restrict (tsupport φ)).prod (volume.restrict (Icc b c))))
    {D : Fin d → Vec d × ℝ → ℂ}
    (hD : ∀ j, MemLp (D j) 2 ((volume.restrict (tsupport φ)).prod (volume.restrict (Icc b c))))
    {η : ℝ → ℝ} (hη : ContinuousOn η (Icc b c))
    (hηpos : ∀ s ∈ Icc b c, 0 ≤ η s)
    (hcoer : ∀ᵐ s ∂volume.restrict (Icc b c),
      ((Real.exp (2 * Λ₀) * Λ₀)⁻¹ / 4) *
        (∫ x, φ x ^ 2 * ∑ j, ‖D j (x, s)‖ ^ 2) ≤
        (∫ x, (φ x : ℂ) ^ 2 * star (W (x, s)) * (-V (x, s))).re +
          (10 * (Real.exp (2 * Λ₀) * Λ₀) ^ 3) *
            (∫ x, (‖ζ‖ ^ 2 * φ x ^ 2 + (∑ j, (coordinateDerivative j φ x) ^ 2)) *
              ‖W (x, s)‖ ^ 2)) :
    ((Real.exp (2 * Λ₀) * Λ₀)⁻¹ / 4) *
      (∫ s in Icc b c, η s * (∫ x, φ x ^ 2 * ∑ j, ‖D j (x, s)‖ ^ 2)) ≤
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
  have hg := integrable_time_integral_compact_spatial_weight hK
    (integrable_finsetSum Finset.univ fun j _ =>
      (memLp_two_iff_integrable_sq_norm (hD j).aestronglyMeasurable).mp (hD j))
    (hφ.1.continuous.pow 2) (fun x hx => by simp [hz x hx])
  have hgi := IntegrableOn.continuousOn_mul hη hg isCompact_Icc
  have hi := integral_mono_ae (hgi.const_mul ((Real.exp (2 * Λ₀) * Λ₀)⁻¹ / 4))
    (hmain.add (he.const_mul (10 * (Real.exp (2 * Λ₀) * Λ₀) ^ 3))) (by
      filter_upwards [hcoer, ae_restrict_mem measurableSet_Icc] with s hs hsm
      simp only [Pi.add_apply, Pi.pow_apply]
      nlinarith only [mul_le_mul_of_nonneg_left hs (hηpos s hsm)])
  simp only [Pi.add_apply, Pi.pow_apply] at hi
  simpa only [integral_add hmain (he.const_mul _), integral_const_mul] using hi


private theorem transpose_orbit_boundary_energy
    {d : ℕ} [Fact (2 ≤ d)] {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀}
    {i : Fin d} {ζ : ℂ}
    {P T : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (hT : IsComplexTransposeSemigroup Q P T)
    {f g : Lp ℂ 2 (reducedLaw Q)}
    (hfg : IsComplexTransposeGeneratorPair Q i ζ f g) :
    ∃ G : ℝ≥0 → Fin d → Lp ℂ 2 (reducedLaw Q),
    ∃ W : ℝ × FieldPair d → ℂ, ∃ D : Fin d → ℝ × FieldPair d → ℂ,
      Measurable W ∧ (∀ j, Measurable (D j)) ∧
      (∀ s, (fun ω => W (s, ω)) =ᵐ[reducedLaw Q] T s.toNNReal f) ∧
      (∀ s, HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) (T s f) (G s)) ∧
      (∀ j s, (fun ω => D j (s, ω)) =ᵐ[reducedLaw Q] G s.toNNReal j) ∧
      (∀ j, Continuous (fun s : ℝ => G s.toNNReal j)) ∧
      ∀ b c : ℝ, 0 ≤ b → b < c →
      ∀ φ : Vec d → ℝ, IsSpatialTest univ φ →
      ∀ η : ℝ → ℝ, AbsolutelyContinuousOnInterval η b c →
        ContinuousOn (deriv η) (Icc b c) →
        (∀ s ∈ Icc b c, 0 ≤ η s) → η b = 0 → η c = 1 →
        ∀ᵐ ω ∂reducedLaw Q,
          ((Real.exp (2 * Λ₀) * Λ₀)⁻¹ / 4) *
            (∫ s in Icc b c, η s * (∫ x, φ x ^ 2 * ∑ j, ‖D j (s, translate x ω)‖ ^ 2)) ≤
          -(∫ x, φ x ^ 2 * ‖(T c.toNNReal f) (translate x ω)‖ ^ 2) / 2 +
            (∫ s in Icc b c, deriv η s * (∫ x, φ x ^ 2 * ‖W (s, translate x ω)‖ ^ 2)) / 2 +
            (10 * (Real.exp (2 * Λ₀) * Λ₀) ^ 3) *
              (∫ s in Icc b c, η s * (∫ x,
                (‖ζ‖ ^ 2 * φ x ^ 2 + ∑ j, (coordinateDerivative j φ x) ^ 2) *
                  ‖W (s, translate x ω)‖ ^ 2)) := by
  let := reducedLaw_probability Q
  obtain ⟨G, hG, _⟩ := hT.existsUnique_continuous_gradient_orbit hP hfg
  have hGc (j : Fin d) : Continuous (fun s : ℝ => G s.toNNReal j) :=
    (PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q)) j).continuous.comp
      (hG.2.comp continuous_real_toNNReal)
  choose D hD heD using fun j =>
    EinsteinFull.StronglyMeasurable.exists_joint_l2_representative (hGc j).stronglyMeasurable
  obtain ⟨W, V, hW, hV, heW, heV, htime⟩ :=
    local_time_transpose_ae_physical_weighted_energy hP hT hfg
  refine ⟨fun s j => G s j, W, D, hW, hD, heW, hG.1, heD, hGc, ?_⟩
  have hw : Continuous (fun s : ℝ => T s.toNNReal f) :=
    (hT.continuous_apply hP f).comp continuous_real_toNNReal
  have hv : Continuous (fun s : ℝ => T s.toNNReal g) :=
    (hT.continuous_apply hP g).comp continuous_real_toNNReal
  intro b c hb hbc φ hφ η hη hηd hηpos hηb hηc
  have hηcont : ContinuousOn η (Icc b c) := by
    simpa only [uIcc_of_le hbc.le] using hη.continuousOn
  have hlocalD (j : Fin d) := ae_locally_memLp_joint_spatial_translate
    (reducedLaw Q) (reducedLaw_stationary Q) (hD j)
    (integrable_sq_joint_l2_representative
      (show IntegrableOn (fun s : ℝ => ‖G s.toNNReal j‖ ^ 2) (Icc b c) volume from
        ((hGc j).norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc)
      (hD j) (heD j))
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
    (fun s _ => hT.map_generator hP hfg s.toNNReal) hW hV heW heV (fun s => hG.1 s.toNNReal) hD heD hφ
  filter_upwards [htime b c hb hbc.le, hlocalW, hlocalV, hcoer,
    ae_complex_orbit_memLp_on_all_compacts (reducedLaw Q) (reducedLaw_stationary Q)
      (T b.toNNReal f),
    ae_complex_orbit_memLp_on_all_compacts (reducedLaw Q) (reducedLaw_stationary Q)
      (T c.toNNReal f), ae_all_iff.mpr hlocalD] with ω ht hlW hlV hc hUb hUc hlD
  have hineq := transpose_cutoff_energy_time_integral hφ
    (hlW _ hφ.2.1) (hlV _ hφ.2.1) (fun j => hlD j _ hφ.2.1) hηcont hηpos hc
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
  linarith only [hineq]


private theorem transpose_cylinder_of_cutoff_energy {d : ℕ}
    {b c r B L C : ℝ} (hbc : b < c) (hr : 0 < r)
    (hL : 0 < L) (hC : 0 ≤ C) {ζ : ℂ} {z : Vec d}
    {W : Vec d × ℝ → ℂ} {D : Fin d → Vec d × ℝ → ℂ} {U : Vec d → ℂ}
    (hW : MemLp W 2 ((volume.restrict {x | euclideanNorm (x - z) ≤ 2 * r}).prod
      (volume.restrict (Icc b c))))
    (hD : ∀ j, MemLp (D j) 2
      ((volume.restrict {x | euclideanNorm (x - z) ≤ 2 * r}).prod
        (volume.restrict (Icc b c))))
    {φ : Vec d → ℝ} (hφ : IsSpatialTest univ φ)
    (hφrange : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1)
    (hone : ∀ x, euclideanNorm (x - z) ≤ r → φ x = 1)
    (hzero : ∀ x, 2 * r ≤ euclideanNorm (x - z) → φ x = 0)
    (hφD : ∀ j x, |coordinateDerivative j φ x| ≤ B / r)
    {η : ℝ → ℝ} (hη : ContinuousOn η (Icc b c))
    (hηd : ContinuousOn (deriv η) (Icc b c))
    (hηrange : ∀ s ∈ Icc b c, 0 ≤ η s ∧ η s ≤ 1 ∧
      0 ≤ deriv η s ∧ deriv η s ≤ 2 / (c - b))
    (hηlower : ∀ s ∈ Icc ((2 * b + c) / 3) c, 1 / 9 ≤ η s)
    (henergy : (L⁻¹ / 4) *
        (∫ s in Icc b c, η s * (∫ x, φ x ^ 2 * ∑ j, ‖D j (x, s)‖ ^ 2)) ≤
      -(∫ x, φ x ^ 2 * ‖U x‖ ^ 2) / 2 +
        (∫ s in Icc b c, deriv η s * (∫ x, φ x ^ 2 * ‖W (x, s)‖ ^ 2)) / 2 +
        C * (∫ s in Icc b c, η s *
          (∫ x, (‖ζ‖ ^ 2 * φ x ^ 2 + ∑ j, (coordinateDerivative j φ x) ^ 2) *
            ‖W (x, s)‖ ^ 2))) :
    (∫ s in Icc ((2 * b + c) / 3) c, ∫ x in {x | euclideanNorm (x - z) ≤ r},
      ∑ j, ‖D j (x, s)‖ ^ 2) ≤
      36 * L * ((c - b)⁻¹ + C * (‖ζ‖ ^ 2 + (d : ℝ) * B ^ 2 / r ^ 2)) *
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
  have hiD := integrable_finsetSum Finset.univ (fun j _ =>
    (memLp_two_iff_integrable_sq_norm (hD j).aestronglyMeasurable).mp (hD j))
  have hinner := transpose_inner_cylinder_integral_le hK
    (isCompact_physical_euclidean_closedBall z r).measurableSet
    (fun x hx => by
      change euclideanNorm (x - z) ≤ r at hx
      change euclideanNorm (x - z) ≤ 2 * r
      linarith)
    hbc.le hiD (fun p => Finset.sum_nonneg (fun j _ => sq_nonneg ‖D j p‖))
    hφ.1.continuous hz (fun x hx => hone x hx) hη
    (fun s hs => (hηrange s hs).1) hηlower
  have hp : 0 ≤ ∫ x, φ x ^ 2 * ‖U x‖ ^ 2 :=
    integral_nonneg (fun x => mul_nonneg (sq_nonneg _) (sq_nonneg _))
  have hupper : (L⁻¹ / 4) *
      (∫ s in Icc b c, η s * (∫ x, φ x ^ 2 * ∑ j, ‖D j (x, s)‖ ^ 2)) ≤
      ((c - b)⁻¹ + C * (‖ζ‖ ^ 2 + (d : ℝ) * B ^ 2 / r ^ 2)) *
        (∫ s in Icc b c, ∫ x in K, ‖W (x, s)‖ ^ 2) := by
    simp only [Pi.add_apply, Pi.mul_apply, Pi.pow_apply] at ht he
    simp only [div_eq_mul_inv] at ht
    have hce := mul_le_mul_of_nonneg_left he hC
    nlinarith only [henergy, hp, ht, hce]
  have hm := mul_le_mul_of_nonneg_left hupper (show 0 ≤ 4 * L by positivity)
  have hinv : (4 * L) * (L⁻¹ / 4) = 1 := by field_simp [hL.ne']
  rw [← mul_assoc, hinv, one_mul] at hm
  calc
    _ ≤ 9 * (∫ s in Icc b c, η s * (∫ x, φ x ^ 2 * ∑ j, ‖D j (x, s)‖ ^ 2)) := hinner
    _ ≤ 9 * ((4 * L) * (((c - b)⁻¹ + C * (‖ζ‖ ^ 2 + (d : ℝ) * B ^ 2 / r ^ 2)) *
        (∫ s in Icc b c, ∫ x in K, ‖W (x, s)‖ ^ 2))) :=
      mul_le_mul_of_nonneg_left hm (by norm_num)
    _ = _ := by dsimp only [K]; ring


/-- Euclidean cylinder dissipation for the actual transpose orbit. -/
theorem local_time_transpose_gradient_cylinder
    (d : ℕ) [Fact (2 ≤ d)] (Λ₀ : ℝ) (hΛ : 1 ≤ Λ₀) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (r₀ : ℝ) (Q : EnvironmentLaw d Λ₀ r₀)
      (i : Fin d) (ζ : ℂ)
      (P T : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)),
      IsComplexEnvironmentSemigroup Q i ζ P →
      IsComplexTransposeSemigroup Q P T →
    ∀ (f g : Lp ℂ 2 (reducedLaw Q)),
      IsComplexTransposeGeneratorPair Q i ζ f g →
    ∃ G : ℝ≥0 → Fin d → Lp ℂ 2 (reducedLaw Q),
    ∃ U : ℝ × FieldPair d → ℂ,
    ∃ DU : Fin d → ℝ × FieldPair d → ℂ,
      Measurable U ∧ (∀ j, Measurable (DU j)) ∧
      (∀ s, (fun ω => U (s, ω)) =ᵐ[reducedLaw Q] T s.toNNReal f) ∧
      (∀ s : ℝ≥0,
        HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
          (T s f) (G s)) ∧
      (∀ (s : ℝ) (j : Fin d),
        (fun ω => DU j (s, ω)) =ᵐ[reducedLaw Q] G s.toNNReal j) ∧
      ∀ (t : ℝ) (ht : 0 < t) (ρ : ℝ) (hρ : Real.sqrt t ≤ ρ) (z : Vec d),
        ∀ᵐ ω ∂reducedLaw Q,
          (∫ s in Icc (t / 2) t,
            ∫ x in {x | euclideanNorm (x - z) ≤ ρ},
              ∑ j : Fin d, ‖DU j (s, translate x ω)‖ ^ 2) ≤
          C * (1 + ‖ζ‖ * Real.sqrt t) ^ 2 / t *
            (∫ s in Icc (t / 4) t,
              ∫ x in {x | euclideanNorm (x - z) ≤ 2 * ρ},
                ‖U (s, translate x ω)‖ ^ 2) := by
  obtain ⟨B, hB, hcutoff⟩ := exists_physical_euclidean_cutoff d
  let L := Real.exp (2 * Λ₀) * Λ₀
  have hL : 0 < L := mul_pos (Real.exp_pos _) (lt_of_lt_of_le zero_lt_one hΛ)
  let A := 10 * L ^ 3
  have hA : 0 ≤ A := by positivity
  let C := 36 * L * (2 + A * (1 + (d : ℝ) * B ^ 2))
  have hC : 0 < C := by dsimp only [C, A]; positivity
  refine ⟨C, hC, ?_⟩
  intro r₀ Q i ζ P T hP hT f g hfg
  let := reducedLaw_probability Q
  obtain ⟨G, W, D, hW, hD, heW, hG, heD, hGc, henergy⟩ :=
    transpose_orbit_boundary_energy hP hT hfg
  refine ⟨G, W, D, hW, hD, heW, hG, (fun s j => heD j s), ?_⟩
  intro t ht r hr z
  have hbc : t / 4 < t := by linarith
  have hrpos : 0 < r := (Real.sqrt_pos.mpr ht).trans_le hr
  obtain ⟨φ, hφ, hφrange, hone, hzero, hφD⟩ := hcutoff z r hrpos
  obtain ⟨η, hη, hηd, hηb, hηc, hηbounds⟩ := exists_transpose_third_temporal_cutoff hbc
  have hηcont : ContinuousOn η (Icc (t / 4) t) := by
    simpa only [uIcc_of_le hbc.le] using hη.continuousOn
  have hηrange s (hs : s ∈ Icc (t / 4) t) : 0 ≤ η s ∧ η s ≤ 1 ∧
      0 ≤ deriv η s ∧ deriv η s ≤ 2 / (t - t / 4) :=
    ⟨(hηbounds s hs).1, (hηbounds s hs).2.1,
      (hηbounds s hs).2.2.1, (hηbounds s hs).2.2.2.1⟩
  have hηlower s (hs : s ∈ Icc ((2 * (t / 4) + t) / 3) t) : 1 / 9 ≤ η s :=
    (hηbounds s ⟨by linarith [hs.1], hs.2⟩).2.2.2.2 hs.1
  have hw : Continuous (fun s : ℝ => T s.toNNReal f) :=
    (hT.continuous_apply hP f).comp continuous_real_toNNReal
  have hlocalW := ae_locally_memLp_joint_spatial_translate
    (reducedLaw Q) (reducedLaw_stationary Q) hW
    (integrable_sq_joint_l2_representative
      (show IntegrableOn (fun s : ℝ => ‖T s.toNNReal f‖ ^ 2) (Icc (t / 4) t) volume from
        (hw.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc) hW heW)
  have hlocalD (j : Fin d) := ae_locally_memLp_joint_spatial_translate
    (reducedLaw Q) (reducedLaw_stationary Q) (hD j)
    (integrable_sq_joint_l2_representative
      (show IntegrableOn (fun s : ℝ => ‖G s.toNNReal j‖ ^ 2) (Icc (t / 4) t) volume from
        ((hGc j).norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc) (hD j) (heD j))
  filter_upwards [henergy (t / 4) t (by positivity) hbc φ hφ η hη hηd
    (fun s hs => (hηbounds s hs).1) hηb hηc, hlocalW, ae_all_iff.mpr hlocalD]
    with ω he hlW hlD
  have hK := isCompact_physical_euclidean_closedBall z (2 * r)
  have hcyl := transpose_cylinder_of_cutoff_energy hbc hrpos hL hA
    (hlW _ hK) (fun j => hlD j _ hK) hφ hφrange hone hzero hφD hηcont hηd
    hηrange hηlower he
  rw [show (2 * (t / 4) + t) / 3 = t / 2 by ring] at hcyl
  apply hcyl.trans
  apply mul_le_mul_of_nonneg_right _ (setIntegral_nonneg measurableSet_Icc
    (fun s _ => integral_nonneg (fun x => sq_nonneg _)))
  let k := 1 + ‖ζ‖ * Real.sqrt t
  have hk : 1 ≤ k := le_add_of_nonneg_right (mul_nonneg (norm_nonneg ζ) (Real.sqrt_nonneg _))
  have hk0 : 0 ≤ k := zero_le_one.trans hk
  have hroot := Real.sq_sqrt ht.le
  have hr2 : t ≤ r ^ 2 := by nlinarith [Real.sqrt_nonneg t]
  have htime : (t - t / 4)⁻¹ ≤ 2 / t := by
    apply (inv_le_iff_one_le_mul₀ (by linarith : 0 < t - t / 4)).mpr
    field_simp
    linarith
  have hrinv : 1 / r ^ 2 ≤ 1 / t := one_div_le_one_div_of_le ht hr2
  have hone : 1 / t ≤ k ^ 2 / t := div_le_div_of_nonneg_right (by nlinarith) ht.le
  have hforce : ‖ζ‖ ^ 2 ≤ k ^ 2 / t := by
    apply (le_div_iff₀ ht).mpr
    dsimp only [k]
    nlinarith [norm_nonneg ζ, Real.sqrt_nonneg t]
  have hspatial : (d : ℝ) * B ^ 2 / r ^ 2 ≤ (d : ℝ) * B ^ 2 * (k ^ 2 / t) := by
    calc
      _ = ((d : ℝ) * B ^ 2) * (1 / r ^ 2) := by ring
      _ ≤ ((d : ℝ) * B ^ 2) * (k ^ 2 / t) :=
        mul_le_mul_of_nonneg_left (hrinv.trans hone) (by positivity)
  have hsum : (t - t / 4)⁻¹ + A * (‖ζ‖ ^ 2 + (d : ℝ) * B ^ 2 / r ^ 2) ≤
      (2 + A * (1 + (d : ℝ) * B ^ 2)) * (k ^ 2 / t) := by
    have ha := mul_le_mul_of_nonneg_left (add_le_add hforce hspatial) hA
    have ht' : (t - t / 4)⁻¹ ≤ 2 * (k ^ 2 / t) := htime.trans (by
      simpa only [div_eq_mul_inv, one_mul] using
        mul_le_mul_of_nonneg_left hone (by norm_num : (0 : ℝ) ≤ 2))
    calc
      _ ≤ 2 * (k ^ 2 / t) + A * (k ^ 2 / t + (d : ℝ) * B ^ 2 * (k ^ 2 / t)) :=
        add_le_add ht' ha
      _ = _ := by ring
  calc
    _ ≤ (36 * L) * ((2 + A * (1 + (d : ℝ) * B ^ 2)) * (k ^ 2 / t)) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by dsimp only [C, k]; ring

end EinsteinFull.Blueprint

#print axioms EinsteinFull.Blueprint.local_time_transpose_gradient_cylinder

#lint

-- Audit private and generated declarations as well as the exported theorem.
run_cmd do
  let env ← Lean.getEnv
  let mut checked : Nat := 0
  for (name, _) in env.constants.toList do
    unless env.isImportedConst name do
      let axioms ← Lean.collectAxioms name
      for ax in axioms do
        unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
          Lean.logError m!"Unexpected axiom {ax} in {name}"
      checked := checked + 1
  Lean.logInfo m!"Owned/generated transitive axiom audit: {checked} declarations checked"
