import EinsteinFull.Blueprint.G1.Proofs.SbxS2KmDecomp
import EinsteinFull.Frozen.SmoothEnvironment
import EinsteinFull.Blueprint.G1.node_rt_u3A_remainder_u2D_moment

open MeasureTheory
open scoped NNReal ENNReal Topology
noncomputable section
namespace EinsteinFull.Blueprint.SbxAKMMomentFromRemainderR09
open EinsteinRelation

theorem a_uniform_covariance_power_moment_of_remainder
    (hrem : node_rt_u3A_remainder_u2D_momentStmt) :
    ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ) (hΛ : 1 ≤ Λ₀) (hr : 1 ≤ r₀),
    ∃ l₀ p C : ℝ, 0 < l₀ ∧ r₀ < 2 * l₀ ∧ 2 ≤ p ∧ 0 < C ∧
    ∀ (r : ℝ), 0 < r →
    ∀ (β : ℕ → ℝ) (hβ : ∀ k, 1 ≤ k → 0 < β k),
    let SD : StructuralData d := ⟨Λ₀, r₀, β, hΛ, hr, hβ⟩
    ∀ (Q : EnvironmentLaw d SD.ellipticity SD.dependenceRange), HasSmoothBounds SD Q →
    ∀ (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
      (l δ : ℝ), l₀ ≤ l → 0 < δ → δ < 1 →
    ∀ (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
      (hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K)
      (hD : Regeneration.annealedCoupledLaw Q.measure K
        (regenerationNoReturn hd (l / lam)) ≠ 0),
    ∀ F G : FieldPair d → ℝ, Measurable F → Measurable G →
      MemLp F (ENNReal.ofReal (p * r)) (reducedLaw Q) →
      MemLp G (ENNReal.ofReal (p * r)) (reducedLaw Q) → ∀ t : ℝ≥0,
    ∀ μ ∈ ({Regeneration.annealedCoupledLaw Q.measure K,
      regenerationConditionedLaw hd Q lam l K hK.1 hD} :
        Set (Measure (FieldPair d × Regeneration.CoupledSample d))),
      Integrable (fun ωz => ‖F (reduce ωz.1) *
        G (translate (ωz.2.1 t) (reduce ωz.1))‖ ^ r) μ ∧
      (∫ ωz, ‖F (reduce ωz.1) *
        G (translate (ωz.2.1 t) (reduce ωz.1))‖ ^ r ∂μ) ≤
        C * Real.exp (C * lam ^ 2 * (t : ℝ)) *
          (eLpNorm F (ENNReal.ofReal (p * r)) (reducedLaw Q)).toReal ^ r *
          (eLpNorm G (ENNReal.ofReal (p * r)) (reducedLaw Q)).toReal ^ r := by
  intro d hd Λ₀ r₀ hΛ hr
  obtain ⟨l₀, p, c, C, hl₀, hsep, hp, hc, hC, hrem'⟩ :=
    hrem d hd Λ₀ r₀ 1 1 zero_lt_one zero_lt_one
  refine ⟨l₀, p, C, hl₀, hsep, hp, hC, ?_⟩
  intro r hr β hβ
  dsimp only
  intro Q hQ lam h₀ h₁ l δ hl hδ₀ hδ₁ P K hK hD F G hF hG hFp hGp t μ hμ
  have hp₀ : 0 ≤ p := le_trans (by norm_num) hp
  have hpow (f : FieldPair d → ℝ)
      (hfp : MemLp f (ENNReal.ofReal (p * r)) (reducedLaw Q)) :
      MemLp (fun ω => ‖f ω‖ ^ r) (ENNReal.ofReal p) (reducedLaw Q) := by
    rw [memLp_iff, eLpNorm_norm_rpow f hfp.aestronglyMeasurable hr,
      ← ENNReal.ofReal_mul hp₀]
    exact ENNReal.rpow_lt_top_of_nonneg hr.le hfp.eLpNorm_ne_top
  have hnorm (f : FieldPair d → ℝ)
      (hfp : MemLp f (ENNReal.ofReal (p * r)) (reducedLaw Q)) :
      (eLpNorm (fun ω => ‖f ω‖ ^ r) (ENNReal.ofReal p) (reducedLaw Q)).toReal =
        (eLpNorm f (ENNReal.ofReal (p * r)) (reducedLaw Q)).toReal ^ r := by
    rw [eLpNorm_norm_rpow f hfp.aestronglyMeasurable hr,
      ← ENNReal.ofReal_mul hp₀, ENNReal.toReal_rpow]
  let : IsProbabilityMeasure (Regeneration.annealedCoupledLaw Q.measure K) :=
    Regeneration.annealedCoupledLaw_isProbabilityMeasure Q.measure K hK.1
  have hprob : Regeneration.annealedCoupledLaw Q.measure K Set.univ ≤
      ENNReal.ofReal (1 * Real.exp (1 * (lam ^ 2 * (t : ℝ)) -
        1 * lam ^ 2 * (t : ℝ))) := by simp
  have hmain := hrem' Q lam h₀ h₁ l δ hl hδ₀ hδ₁ P K hK hD
    (fun ω => ‖F ω‖ ^ r) (fun ω => ‖G ω‖ ^ r)
    (hF.norm.pow_const r) (hG.norm.pow_const r) (hpow F hFp) (hpow G hGp)
    (lam ^ 2 * (t : ℝ)) t Set.univ (by positivity) MeasurableSet.univ hprob μ hμ
  simp only [integrableOn_univ, Measure.restrict_univ, hnorm F hFp,
    hnorm G hGp] at hmain
  have hident : (fun ωz : FieldPair d × Regeneration.CoupledSample d =>
      ‖F (reduce ωz.1) * G (translate (ωz.2.1 t) (reduce ωz.1))‖ ^ r) =
      (fun ωz => ‖F (reduce ωz.1)‖ ^ r *
        ‖G (translate (ωz.2.1 t) (reduce ωz.1))‖ ^ r) := by
    funext ωz
    rw [norm_mul, Real.mul_rpow (norm_nonneg _) (norm_nonneg _)]
  rw [hident]
  refine ⟨hmain.1, ?_⟩
  have hnonneg : 0 ≤ ∫ ωz, ‖F (reduce ωz.1)‖ ^ r *
      ‖G (translate (ωz.2.1 t) (reduce ωz.1))‖ ^ r ∂μ :=
    integral_nonneg fun _ => by positivity
  rw [abs_of_nonneg hnonneg] at hmain
  apply hmain.2.trans
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hC.le
  have htime : 0 ≤ lam ^ 2 * (t : ℝ) := by positivity
  nlinarith only [mul_nonneg hc.le htime]



theorem a_uniform_remainder_variable_rate_of_remainder
    (hrem : node_rt_u3A_remainder_u2D_momentStmt) :
    ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ) (hΛ : 1 ≤ Λ₀) (hr : 1 ≤ r₀),
    ∃ l₀ : ℝ, 0 < l₀ ∧ r₀ < 2 * l₀ ∧
    ∀ a : ℝ, 0 < a → ∃ p c C : ℝ, 2 ≤ p ∧ 0 < c ∧ 0 < C ∧
    ∀ (β : ℕ → ℝ) (hβ : ∀ k, 1 ≤ k → 0 < β k),
    let SD : StructuralData d := ⟨Λ₀, r₀, β, hΛ, hr, hβ⟩
    ∀ (Q : EnvironmentLaw d SD.ellipticity SD.dependenceRange), HasSmoothBounds SD Q →
    ∀ (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
      (l δ : ℝ), l₀ ≤ l → 0 < δ → δ < 1 →
    ∀ (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
      (_hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K)
      (_hD : Regeneration.annealedCoupledLaw Q.measure K
        (regenerationNoReturn hd (l / lam)) ≠ 0),
    ∀ F G : FieldPair d → ℝ, Measurable F → Measurable G →
      MemLp F (ENNReal.ofReal p) (reducedLaw Q) →
      MemLp G (ENNReal.ofReal p) (reducedLaw Q) →
    ∀ (J : ℝ) (t : ℝ≥0) (E : Set (FieldPair d × Regeneration.CoupledSample d)),
      0 ≤ J → Regeneration.annealedCoupledLaw Q.measure K E ≤
        ENNReal.ofReal (Real.exp (J - a * lam ^ 2 * (t : ℝ))) →
      IntegrableOn (fun ωz => F (reduce ωz.1) *
        G (translate (ωz.2.1 t) (reduce ωz.1))) E
        (Regeneration.annealedCoupledLaw Q.measure K) ∧
      |∫ ωz in E, F (reduce ωz.1) *
        G (translate (ωz.2.1 t) (reduce ωz.1))
          ∂Regeneration.annealedCoupledLaw Q.measure K| ≤
        C * Real.exp (C * J - c * lam ^ 2 * (t : ℝ)) *
          (eLpNorm F (ENNReal.ofReal p) (reducedLaw Q)).toReal *
          (eLpNorm G (ENNReal.ofReal p) (reducedLaw Q)).toReal := by
  intro d hd Λ₀ r₀ hΛ hr
  obtain ⟨l₀, p₀, D, hl₀, hsep, hp₀, hDpos, hmoment⟩ :=
    a_uniform_covariance_power_moment_of_remainder hrem d hd Λ₀ r₀ hΛ hr
  refine ⟨l₀, hl₀, hsep, ?_⟩
  intro a ha
  obtain ⟨r, c, C, hr, hc, hC, hscalar⟩ :=
    sbxS2_power_interpolation_constants D a hDpos ha
  have hr₁ : 1 < r := lt_of_lt_of_le (by norm_num) hr
  have hr₀ : 0 < r := lt_trans zero_lt_one hr₁
  have hp₀pos : 0 ≤ p₀ := le_trans (by norm_num) hp₀
  refine ⟨p₀ * r, c, C, ?_, hc, hC, ?_⟩
  · exact hp₀.trans (le_mul_of_one_le_right hp₀pos hr₁.le)
  intro β hβ
  dsimp only
  intro Q hQ lam h₀ h₁ l δ hl hδ₀ hδ₁ P K hK hD F G hF hG hFp hGp J t E hJ hprob
  let μ := Regeneration.annealedCoupledLaw Q.measure K
  let f := fun ωz : FieldPair d × Regeneration.CoupledSample d =>
    F (reduce ωz.1) * G (translate (ωz.2.1 t) (reduce ωz.1))
  have hfm : Measurable f :=
    ((hF.comp Probability.measurable_reduce).comp measurable_fst).mul
      (hG.comp (Probability.continuous_translate.measurable.comp
        (((continuous_eval_const t).measurable.comp measurable_snd.fst).prodMk
          (Probability.measurable_reduce.comp measurable_fst))))
  have hpower := hmoment r hr₀ β hβ Q hQ lam h₀ h₁ l δ hl hδ₀ hδ₁ P K hK hD
    F G hF hG hFp hGp t μ (Set.mem_insert _ _)
  let : IsProbabilityMeasure μ :=
    Regeneration.annealedCoupledLaw_isProbabilityMeasure Q.measure K hK.1
  have hfr : MemLp f (ENNReal.ofReal r) μ := by
    apply (integrable_norm_rpow_iff hfm.aestronglyMeasurable (by positivity)
      ENNReal.ofReal_ne_top).mp
    simpa only [ENNReal.toReal_ofReal hr₀.le] using hpower.1
  refine ⟨(MemLp.integrable (q := ENNReal.ofReal r) ?_ hfr).integrableOn, ?_⟩
  · simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hr₁.le
  have hb := sbxS2_setIntegral_abs_le_moment μ f hfm.aestronglyMeasurable E r
    (D * Real.exp (D * lam ^ 2 * (t : ℝ)) *
      (eLpNorm F (ENNReal.ofReal (p₀ * r)) (reducedLaw Q)).toReal ^ r *
      (eLpNorm G (ENNReal.ofReal (p₀ * r)) (reducedLaw Q)).toReal ^ r)
    (Real.exp (J - a * lam ^ 2 * (t : ℝ))) hr₁ hpower.1 hpower.2
    (Real.exp_pos _).le hprob
  apply hb.trans
  simpa only [mul_assoc] using hscalar J (lam ^ 2 * (t : ℝ))
    (eLpNorm F (ENNReal.ofReal (p₀ * r)) (reducedLaw Q)).toReal
    (eLpNorm G (ENNReal.ofReal (p₀ * r)) (reducedLaw Q)).toReal
    hJ (by positivity) ENNReal.toReal_nonneg ENNReal.toReal_nonneg

end EinsteinFull.Blueprint.SbxAKMMomentFromRemainderR09
