import EinsteinFull.Blueprint.G1.Proofs.SbxS4KmPathIdentification
import EinsteinFull.Frozen.SmoothEnvironment
import EinsteinFull.Blueprint.G1.node_rt_u3A_remainder_u2D_moment

open MeasureTheory
open scoped NNReal ENNReal Topology
noncomputable section
namespace EinsteinFull.Blueprint.SbxAKMGrowthFromRemainderR09
open EinsteinRelation

theorem a_uniform_complex_path_product_growth_of_remainder
    (hrem : EinsteinFull.Blueprint.node_rt_u3A_remainder_u2D_momentStmt) :
    ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ) (hΛ : 1 ≤ Λ₀) (hr : 1 ≤ r₀),
    ∃ l₀ p C : ℝ, 0 < l₀ ∧ r₀ < 2 * l₀ ∧ 2 ≤ p ∧ 0 < C ∧
    ∀ (β : ℕ → ℝ) (hβ : ∀ k, 1 ≤ k → 0 < β k),
    let D : StructuralData d := ⟨Λ₀, r₀, β, hΛ, hr, hβ⟩
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange), HasSmoothBounds D Q →
    ∀ (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
      (l δ : ℝ), l₀ ≤ l → 0 < δ → δ < 1 →
    ∀ (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
      (_hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K)
      (_hD : Regeneration.annealedCoupledLaw Q.measure K
        (regenerationNoReturn hd (l / lam)) ≠ 0)
      (F G : FieldPair d → ℂ),
    Measurable F → Measurable G →
    MemLp F (ENNReal.ofReal p) (reducedLaw Q) →
    MemLp G (ENNReal.ofReal p) (reducedLaw Q) → ∀ t : ℝ≥0,
    Integrable (fun w => F (reduce w.1) * G (sbxS4CoupledEndpoint t w))
      (Regeneration.annealedCoupledLaw Q.measure K) ∧
    (∫ w, F (reduce w.1) * G (sbxS4CoupledEndpoint t w)
      ∂Regeneration.annealedCoupledLaw Q.measure K) =
      (∫ ω, F (reduce ω) *
        (∫ γ : Path d, G (translate (γ t) (reduce ω)) ∂P (0, ω)) ∂Q.measure) ∧
    (∫ w, ‖F (reduce w.1) * G (sbxS4CoupledEndpoint t w)‖
      ∂Regeneration.annealedCoupledLaw Q.measure K) ≤
      C * Real.exp (C * lam ^ 2 * (t : ℝ)) *
        (eLpNorm F (ENNReal.ofReal p) (reducedLaw Q)).toReal *
        (eLpNorm G (ENNReal.ofReal p) (reducedLaw Q)).toReal := by
  intro d hd Λ₀ r₀ hΛ hr
  obtain ⟨l₀, p, c, C, hl₀, hsep, hp, hc, hC, hrest⟩ :=
    hrem d hd Λ₀ r₀ 1 1 zero_lt_one zero_lt_one
  refine ⟨l₀, p, C, hl₀, hsep, hp, hC, ?_⟩
  intro β hβ
  dsimp only
  intro Q hQ lam h₀ h₁ l δ hl hδ₀ hδ₁ P K hK hD F G hF hG hFp hGp t
  have := Regeneration.annealedCoupledLaw_isProbabilityMeasure Q.measure K hK.1
  have hwhole : Regeneration.annealedCoupledLaw Q.measure K Set.univ ≤
      ENNReal.ofReal (1 * Real.exp (1 * (lam ^ 2 * (t : ℝ)) -
        1 * lam ^ 2 * (t : ℝ))) := by
    simp only [one_mul, sub_self, Real.exp_zero, ENNReal.ofReal_one, measure_univ, le_rfl]
  obtain ⟨hprod, hbound⟩ := hrest Q lam h₀ h₁ l δ hl hδ₀ hδ₁ P K hK hD
    (fun ω => ‖F ω‖) (fun ω => ‖G ω‖) hF.norm hG.norm hFp.norm hGp.norm
    (lam ^ 2 * (t : ℝ)) t Set.univ (by positivity) MeasurableSet.univ hwhole
    (Regeneration.annealedCoupledLaw Q.measure K) (Set.mem_insert _ _)
  have hnorm : Integrable (fun w => ‖F (reduce w.1) * G (sbxS4CoupledEndpoint t w)‖)
      (Regeneration.annealedCoupledLaw Q.measure K) := by
    simpa only [IntegrableOn, Measure.restrict_univ, norm_mul, sbxS4CoupledEndpoint] using hprod
  have hcomplex := (integrable_norm_iff
    (((hF.comp (Probability.measurable_reduce.comp measurable_fst)).mul
      (hG.comp (sbxS4_measurable_coupledEndpoint t))).aestronglyMeasurable)).mp hnorm
  refine ⟨hcomplex, sbxS4_coupled_product_integral_eq_supplied hd Q lam l δ h₀.le h₁
    P K hK t hG hcomplex, ?_⟩
  have hb : |∫ w, ‖F (reduce w.1) * G (sbxS4CoupledEndpoint t w)‖
      ∂Regeneration.annealedCoupledLaw Q.measure K| ≤
      C * Real.exp (C * lam ^ 2 * (t : ℝ) - c * lam ^ 2 * (t : ℝ)) *
        (eLpNorm F (ENNReal.ofReal p) (reducedLaw Q)).toReal *
        (eLpNorm G (ENNReal.ofReal p) (reducedLaw Q)).toReal := by
    simpa only [Measure.restrict_univ, norm_mul, sbxS4CoupledEndpoint,
      eLpNorm_norm F hFp.aestronglyMeasurable, eLpNorm_norm G hGp.aestronglyMeasurable,
      mul_assoc] using hbound
  refine (le_abs_self _).trans (hb.trans ?_)
  apply mul_le_mul_of_nonneg_right _ ENNReal.toReal_nonneg
  apply mul_le_mul_of_nonneg_right _ ENNReal.toReal_nonneg
  apply mul_le_mul_of_nonneg_left _ hC.le
  exact Real.exp_le_exp.mpr (sub_le_self _ (by positivity))


theorem a_uniform_coupled_endpoint_memLp_two_of_remainder
    (hrem : EinsteinFull.Blueprint.node_rt_u3A_remainder_u2D_momentStmt) :
    ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ) (hΛ : 1 ≤ Λ₀) (hr : 1 ≤ r₀),
    ∃ l₀ p C : ℝ, 0 < l₀ ∧ r₀ < 2 * l₀ ∧ 2 ≤ p ∧ 0 < C ∧
    ∀ (β : ℕ → ℝ) (hβ : ∀ k, 1 ≤ k → 0 < β k),
    let D : StructuralData d := ⟨Λ₀, r₀, β, hΛ, hr, hβ⟩
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange), HasSmoothBounds D Q →
    ∀ (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
      (l δ : ℝ), l₀ ≤ l → 0 < δ → δ < 1 →
    ∀ (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
      (_hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K)
      (_hD : Regeneration.annealedCoupledLaw Q.measure K
        (regenerationNoReturn hd (l / lam)) ≠ 0)
      (F : FieldPair d → ℂ),
    Measurable F → MemLp F (2 * ENNReal.ofReal p) (reducedLaw Q) → ∀ t : ℝ≥0,
    MemLp (fun w => F (sbxS4CoupledEndpoint t w)) 2
      (Regeneration.annealedCoupledLaw Q.measure K) ∧
    (∀ᵐ ω ∂Q.measure,
      MemLp (fun γ : Path d => F (translate (γ t) (reduce ω))) 2 (P (0, ω))) ∧
    (∫ w, ‖F (sbxS4CoupledEndpoint t w)‖ ^ 2
      ∂Regeneration.annealedCoupledLaw Q.measure K) ≤
      C * Real.exp (C * lam ^ 2 * (t : ℝ)) *
        (eLpNorm F (2 * ENNReal.ofReal p) (reducedLaw Q)).toReal ^ 2 := by
  intro d hd Λ₀ r₀ hΛ hr
  obtain ⟨l₀, p, C, hl₀, hsep, hp, hC, hgrowth⟩ :=
    a_uniform_complex_path_product_growth_of_remainder hrem d hd Λ₀ r₀ hΛ hr
  refine ⟨l₀, p, C, hl₀, hsep, hp, hC, ?_⟩
  intro β hβ
  dsimp only
  intro Q hQ lam h₀ h₁ l δ hl hδ₀ hδ₁ P K hK hD F hF hFp t
  have := reducedLaw_probability Q
  have hp0 : 0 < p := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) hp
  have hsquare : MemLp (fun ω => ‖F ω‖ ^ 2) (ENNReal.ofReal p) (reducedLaw Q) := by
    convert hFp.norm_rpow_div (2 : ℝ≥0∞) using 1
    · ext ω
      simp only [ENNReal.toReal_ofNat, Real.rpow_two]
    · rw [div_eq_mul_inv, mul_comm (2 : ℝ≥0∞), mul_assoc,
        ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, mul_one]
  have hcast : AEStronglyMeasurable
      (fun ω => ((‖F ω‖ ^ 2 : ℝ) : ℂ)) (reducedLaw Q) :=
    Complex.continuous_ofReal.comp_aestronglyMeasurable hsquare.aestronglyMeasurable
  have hcastnorm : ∀ᵐ ω ∂reducedLaw Q, ‖((‖F ω‖ ^ 2 : ℝ) : ℂ)‖ = ‖‖F ω‖ ^ 2‖ :=
    Filter.Eventually.of_forall fun ω => Complex.norm_real _
  have hcastLp : MemLp (fun ω => ((‖F ω‖ ^ 2 : ℝ) : ℂ))
      (ENNReal.ofReal p) (reducedLaw Q) :=
    (memLp_congr_norm hcast hsquare.aestronglyMeasurable hcastnorm).mpr hsquare
  have hnorm : eLpNorm (fun ω => ((‖F ω‖ ^ 2 : ℝ) : ℂ))
      (ENNReal.ofReal p) (reducedLaw Q) =
      eLpNorm F (2 * ENNReal.ofReal p) (reducedLaw Q) ^ 2 := by
    rw [eLpNorm_congr_norm_ae hcast hsquare.aestronglyMeasurable hcastnorm]
    simpa only [Real.rpow_two, ENNReal.ofReal_ofNat, ENNReal.rpow_two,
      mul_comm] using (eLpNorm_norm_rpow F hFp.aestronglyMeasurable (by norm_num : (0 : ℝ) < 2)
        (p := ENNReal.ofReal p))
  obtain ⟨hprod, _hpair, hb⟩ := hgrowth β hβ Q hQ lam h₀ h₁ l δ hl hδ₀ hδ₁ P K hK hD
    (fun _ => 1) (fun ω => ((‖F ω‖ ^ 2 : ℝ) : ℂ)) measurable_const
    (Complex.continuous_ofReal.measurable.comp (hF.norm.pow_const 2))
    (memLp_const 1) hcastLp t
  have hsquareEnd : Integrable (fun w => ‖F (sbxS4CoupledEndpoint t w)‖ ^ 2)
      (Regeneration.annealedCoupledLaw Q.measure K) := by
    simpa only [one_mul, Complex.norm_real, Real.norm_eq_abs, abs_sq] using hprod.norm
  have hFend := (memLp_two_iff_integrable_sq_norm
    (hF.comp (sbxS4_measurable_coupledEndpoint t)).aestronglyMeasurable).mpr hsquareEnd
  refine ⟨hFend, sbxS4_supplied_endpoint_memLp_two_of_coupled hd Q lam l δ h₀.le h₁
    P K hK t hF hFend, ?_⟩
  have hone : eLpNorm (fun _ : FieldPair d => (1 : ℂ)) (ENNReal.ofReal p)
      (reducedLaw Q) = 1 := by
    rw [eLpNorm_const _ (ENNReal.ofReal_pos.mpr hp0).ne' (NeZero.ne _), measure_univ,
      ENNReal.one_rpow, mul_one]
    norm_num
  simpa only [one_mul, Complex.norm_real, Real.norm_eq_abs, abs_sq, hone,
    ENNReal.toReal_one, mul_one, hnorm, ENNReal.toReal_pow] using hb





end EinsteinFull.Blueprint.SbxAKMGrowthFromRemainderR09
