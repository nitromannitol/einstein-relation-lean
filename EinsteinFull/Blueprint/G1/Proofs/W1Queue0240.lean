import EinsteinFull.Blueprint.G1.node_p_u3A_tail_u23_small_u2D_endpoints
import EinsteinFull.Blueprint.Roots.node_p_u3A_scalar
import EinsteinFull.Calculus.ComplexSemigroupCenteringSupport
import EinsteinFull.Work.W2.MassiveCorrectorGradientSupport

/-! Force-time endpoint smallness and the exact bilinear correlation splitting. -/

open MeasureTheory
open scoped NNReal ENNReal BigOperators

noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation

private theorem drift_mean_zero {d : ℕ} {D : StructuralData d}
    {Q : EnvironmentLaw d D.ellipticity D.dependenceRange} {hQ : HasSmoothBounds D Q}
    {β : Fin d → Lp ℂ 2 (reducedLaw Q)} (hβ : IsReducedDriftObservation Q hQ β)
    (i : Fin d) : (∫ ω, β i ω ∂reducedLaw Q) = 0 := by
  letI := reducedLaw_probability Q
  have hh := hβ.integral_mul i (Lp.const 2 (reducedLaw Q) 1) (fun _ => 0)
    (hasComplexHorizontalGradient_const _ (reducedLaw_stationary Q) 1)
  have hl : (∫ ω, β i ω * Lp.const 2 (reducedLaw Q) 1 ω ∂reducedLaw Q) =
      ∫ ω, β i ω ∂reducedLaw Q := by
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_const 2 (reducedLaw Q) (1 : ℂ)] with ω hω
    simp only [hω, Function.const_apply, mul_one]
  have hr : (∫ ω, ∑ k, (ω.1 0 k i : ℂ) *
      (0 : Lp ℂ 2 (reducedLaw Q)) ω ∂reducedLaw Q) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [Lp.coeFn_zero ℂ 2 (reducedLaw Q)] with ω hω
    simp only [hω, Pi.zero_apply, mul_zero, Finset.sum_const_zero]
  simpa only [hl, hr, mul_zero] using! hh

private theorem clock_centered {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (ζ : ℂ)
    (P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (μ : Lp ℂ 2 (reducedLaw Q)) (T : ℝ≥0) :
    clockEndpoint Q ζ P μ T = centeredComplexLp Q (P T (ζ • μ)) := by
  letI := reducedLaw_probability Q
  apply Lp.ext
  filter_upwards [Lp.coeFn_smul ζ (centeredComplexLp Q (P T μ)),
    coeFn_centeredComplexLp Q (P T μ),
    coeFn_centeredComplexLp Q (P T (ζ • μ)),
    Lp.coeFn_smul ζ (P T μ)] with ω h1 h2 h3 h4
  have hi : (∫ ω, P T (ζ • μ) ω ∂reducedLaw Q) =
      ζ * ∫ ω, P T μ ω ∂reducedLaw Q := by
    rw [map_smul, integral_congr_ae (Lp.coeFn_smul ζ (P T μ))]
    exact integral_smul ζ _
  change (ζ • centeredComplexLp Q (P T μ)) ω = _
  rw [h1, Pi.smul_apply, h2, h3, hi, map_smul, h4, Pi.smul_apply]
  change ζ * (_ - _) = ζ * _ - ζ * _
  ring

private theorem split_pairing {d : ℕ} {Λ r : ℝ}
    {Q : EnvironmentLaw d Λ r} {i : Fin d} {ζ : ℂ}
    {P R : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (hR : IsComplexTransposeSemigroup Q P R)
    (b f : Lp ℂ 2 (reducedLaw Q)) (hb : (∫ ω, b ω ∂reducedLaw Q) = 0)
    (T t : ℝ≥0) (ht : 2 * T ≤ t) :
    (∫ ω, b ω * P t f ω ∂reducedLaw Q) =
      ∫ ω, R T b ω * P (t - 2 * T) (centeredComplexLp Q (P T f)) ω
        ∂reducedLaw Q := by
  letI := reducedLaw_probability Q
  let m := ∫ ω, P T f ω ∂reducedLaw Q
  have hTt : T ≤ t := (le_add_of_nonneg_right T.property).trans (by simpa only [two_mul] using! ht)
  have hTT : T ≤ t - T := (le_tsub_iff_right hTt).mpr (by simpa only [two_mul] using! ht)
  have he : P (t - 2 * T) (centeredComplexLp Q (P T f)) =
      P (t - T) f - Lp.const 2 (reducedLaw Q) m := by
    unfold centeredComplexLp
    rw [map_sub, hP.map_const]
    have ht' : t - 2 * T + T = t - T := by
      rw [two_mul, ← tsub_tsub, tsub_add_cancel_of_le hTT]
    rw [← ContinuousLinearMap.comp_apply, ← hP.2.1, ht']
  rw [he]
  have hmean := hR.integral_eq hP T b
  rw [hb] at hmean
  calc
    _ = ∫ ω, P (t - T) f ω * R T b ω ∂reducedLaw Q := by
      rw [← hR T (P (t - T) f) b]
      have htt : T + (t - T) = t := add_tsub_cancel_of_le hTt
      rw [← ContinuousLinearMap.comp_apply, ← hP.2.1, htt]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun ω => mul_comm _ _
    _ = ∫ ω, R T b ω * (P (t - T) f ω - m) ∂reducedLaw Q := by
      rw [show (fun ω => R T b ω * (P (t - T) f ω - m)) =
        (fun ω => R T b ω * P (t - T) f ω - R T b ω * m) by
          funext ω; ring]
      rw [integral_sub (integrable_complexLp_mul Q _ _)
        ((integrable_complexLp Q _).mul_const m), integral_mul_const, hmean,
        zero_mul, sub_zero]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun ω => mul_comm _ _
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_sub (P (t - T) f) (Lp.const 2 (reducedLaw Q) m),
        Lp.coeFn_const 2 (reducedLaw Q) m] with ω hs hc
      simp only [hs, Pi.sub_apply, hc, Function.const_apply]

/-- The scalar estimate at the literal inverse-square force time supplies both
small centered endpoints; the semigroup and its bilinear transpose split the
actual correlation after two such time intervals. -/
theorem node_p_u3A_tail_u23_small_u2D_endpoints_of_deps
    (hscalar : node_p_u3A_scalarStmt) : node_p_u3A_tail_u23_small_u2D_endpointsStmt := by
  intro d hd D p hp
  obtain ⟨a₀, η₀, _, _, _, hs⟩ := hscalar d hd D
  obtain ⟨C, Dp, t₀, Cder, hC, _, _, _, hs⟩ := hs p hp
  refine ⟨C, hC, ?_⟩
  intro Q hQ β a μ hβ ha hμ lam hlam hsmall P Pdag hP hPdag
  letI := reducedLaw_probability Q
  let s := |lam|
  have hspos : 0 < s := hlam
  have hsle : s ≤ 1 := hsmall.trans (Real.exp_le_one_iff.mpr (by norm_num))
  let T : ℝ≥0 := ((s ^ 2)⁻¹).toNNReal
  have hT : (T : ℝ) = (s ^ 2)⁻¹ := Real.coe_toNNReal _ (by positivity)
  have hTone : 1 ≤ (T : ℝ) := by
    rw [hT]
    exact (one_le_inv₀ (by positivity)).mpr (by nlinarith)
  have hsqrt : Real.sqrt (T : ℝ) = s⁻¹ := by
    rw [hT, Real.sqrt_inv, Real.sqrt_sq hspos.le]
  have hforce : ‖(lam : ℂ)‖ * Real.sqrt (T : ℝ) ≤ 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, hsqrt]
    change s * s⁻¹ ≤ 2
    rw [mul_inv_cancel₀ hspos.ne']
    norm_num
  obtain ⟨hmem, hbound⟩ := (hs Q hQ β a μ hβ ha hμ (lam : ℂ) P Pdag hP hPdag).1
    T hTone hforce
  have hpower : (T : ℝ) ^ (-(1 / 2 + (d : ℝ) / 4)) =
      s ^ (1 + (d : ℝ) / 2) := by
    rw [hT, ← Real.rpow_neg_eq_inv_rpow, ← Real.rpow_natCast_mul hspos.le]
    congr 1
    ring
  rw [hpower] at hbound
  have hFmem := hmem _ (by
    exact Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_singleton _)))
  have hFmean : (∫ ω, transposeEndpoint Q ⟨0, by omega⟩ Pdag β T ω ∂reducedLaw Q) = 0 :=
    (hPdag.integral_eq hP T _).trans (drift_mean_zero hβ _)
  dsimp only
  intro j velocity
  have hGmem := hmem (if velocity then
      velocityEndpoint Q ⟨0, by omega⟩ j (lam : ℂ) P β a T else
      clockEndpoint Q (lam : ℂ) P μ T) (by
    cases velocity
    · exact Set.mem_union_right _ (Set.mem_singleton _)
    · exact Set.mem_union_left _ (Set.mem_union_right _ ⟨j, rfl⟩))
  refine ⟨hFmem, hGmem, hFmean, ?_, ?_, ?_⟩
  · cases velocity
    · rw [clock_centered]
      exact integral_centeredComplexLp Q _
    · exact integral_centeredComplexLp Q _
  · have hsum : (eLpNorm (velocityEndpoint Q ⟨0, by omega⟩ j (lam : ℂ) P β a T)
        (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤
        ∑ k : Fin d, (eLpNorm (velocityEndpoint Q ⟨0, by omega⟩ k (lam : ℂ) P β a T)
          (ENNReal.ofReal p) (reducedLaw Q)).toReal :=
      Finset.single_le_sum (f := fun k : Fin d =>
        (eLpNorm (velocityEndpoint Q ⟨0, by omega⟩ k (lam : ℂ) P β a T)
          (ENNReal.ofReal p) (reducedLaw Q)).toReal)
        (fun _ _ => ENNReal.toReal_nonneg) (Finset.mem_univ j)
    have hsumpos : 0 ≤ ∑ k : Fin d,
        (eLpNorm (velocityEndpoint Q ⟨0, by omega⟩ k (lam : ℂ) P β a T)
          (ENNReal.ofReal p) (reducedLaw Q)).toReal :=
      Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg
    have hcpos := ENNReal.toReal_nonneg (a := eLpNorm
      (clockEndpoint Q (lam : ℂ) P μ T) (ENNReal.ofReal p) (reducedLaw Q))
    cases velocity
    · change (eLpNorm (transposeEndpoint Q ⟨0, by omega⟩ Pdag β T)
        (ENNReal.ofReal p) (reducedLaw Q)).toReal +
        (eLpNorm (clockEndpoint Q (lam : ℂ) P μ T)
          (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤ C * s ^ (1 + (d : ℝ) / 2)
      linarith only [hbound, hsumpos]
    · change (eLpNorm (transposeEndpoint Q ⟨0, by omega⟩ Pdag β T)
        (ENNReal.ofReal p) (reducedLaw Q)).toReal +
        (eLpNorm (velocityEndpoint Q ⟨0, by omega⟩ j (lam : ℂ) P β a T)
          (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤ C * s ^ (1 + (d : ℝ) / 2)
      linarith only [hbound, hsum, hcpos]
  · intro t ht
    have ht' : 2 * T ≤ t := by exact_mod_cast ht
    cases velocity
    · simpa only [clockCorrelation, transposeEndpoint, clock_centered] using!
        split_pairing hP hPdag (β ⟨0, by omega⟩) ((lam : ℂ) • μ)
          (drift_mean_zero hβ _) T t ht'
    · exact split_pairing hP hPdag (β ⟨0, by omega⟩)
        (β j + (lam : ℂ) • a ⟨0, by omega⟩ j) (drift_mean_zero hβ _) T t ht'

end EinsteinFull.Blueprint
