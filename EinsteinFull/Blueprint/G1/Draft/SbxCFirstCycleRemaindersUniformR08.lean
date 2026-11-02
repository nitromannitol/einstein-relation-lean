import EinsteinFull.Blueprint.G1.Draft.SbxS6LocalMixingSmoothR01
import EinsteinFull.Blueprint.Roots.Draft.SbxCRenewalUniformR06

/-! Conditional uniform first-cycle remainder bounds, not reviewed or adopted. -/
open MeasureTheory
open scoped NNReal ENNReal Topology
namespace EinsteinFull.Blueprint.SbxCFirstCycleRemaindersUniformR08
open EinsteinRelation EinsteinFull.Blueprint SbxS6Section3R01

theorem covariance_power_moment_all_laws
    (hrem : node_rt_u3A_remainder_u2D_momentStmt) :
    ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ),
    ∃ l₀ p C : ℝ, 0 < l₀ ∧ r₀ < 2 * l₀ ∧ 2 ≤ p ∧ 0 < C ∧
    ∀ (r : ℝ), 0 < r →
    ∀ (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
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
  intro d hd Λ₀ r₀
  obtain ⟨l₀, p, c, C, hl₀, hsep, hp, hc, hC, hrem'⟩ :=
    hrem d hd Λ₀ r₀ 1 1 (by norm_num) (by norm_num)
  refine ⟨l₀, p, C, hl₀, hsep, hp, hC, ?_⟩
  intro r hr Q lam h₀ h₁ l δ hl hδ₀ hδ₁ P K hK hD F G hF hG hFp hGp t μ hμ
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

theorem remainder_variable_rate_all_laws
    (hrem : node_rt_u3A_remainder_u2D_momentStmt) :
    ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ),
    ∃ l₀ : ℝ, 0 < l₀ ∧ r₀ < 2 * l₀ ∧
    ∀ a : ℝ, 0 < a → ∃ p c C : ℝ, 2 ≤ p ∧ 0 < c ∧ 0 < C ∧
    ∀ (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
      (l δ : ℝ), l₀ ≤ l → 0 < δ → δ < 1 →
    ∀ (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
      (hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K)
      (hD : Regeneration.annealedCoupledLaw Q.measure K
        (regenerationNoReturn hd (l / lam)) ≠ 0),
    ∀ F G : FieldPair d → ℝ, Measurable F → Measurable G →
      MemLp F (ENNReal.ofReal p) (reducedLaw Q) →
      MemLp G (ENNReal.ofReal p) (reducedLaw Q) →
    ∀ (J : ℝ) (t : ℝ≥0) (E : Set (FieldPair d × Regeneration.CoupledSample d)),
    0 ≤ J → ∀ μ ∈ ({Regeneration.annealedCoupledLaw Q.measure K,
      regenerationConditionedLaw hd Q lam l K hK.1 hD} :
        Set (Measure (FieldPair d × Regeneration.CoupledSample d))),
    μ E ≤ ENNReal.ofReal (Real.exp (J - a * (lam ^ 2 * (t : ℝ)))) →
    IntegrableOn (fun ωz => F (reduce ωz.1) *
      G (translate (ωz.2.1 t) (reduce ωz.1))) E μ ∧
    |∫ ωz in E, F (reduce ωz.1) * G (translate (ωz.2.1 t) (reduce ωz.1)) ∂μ| ≤
      C * Real.exp (C * J - c * (lam ^ 2 * (t : ℝ))) *
        (eLpNorm F (ENNReal.ofReal p) (reducedLaw Q)).toReal *
        (eLpNorm G (ENNReal.ofReal p) (reducedLaw Q)).toReal := by
  intro d hd Λ₀ r₀
  obtain ⟨l₀, p₀, D, hl₀, hsep, hp₀, hDpos, hmoment⟩ :=
    covariance_power_moment_all_laws hrem d hd Λ₀ r₀
  refine ⟨l₀, hl₀, hsep, ?_⟩
  intro a ha
  obtain ⟨r, c, C, hr, hc, hC, hscalar⟩ :=
    sbxS2_power_interpolation_constants D a hDpos ha
  have hr₁ : 1 < r := lt_of_lt_of_le (by norm_num) hr
  have hr₀ : 0 < r := lt_trans zero_lt_one hr₁
  refine ⟨p₀ * r, c, C,
    hp₀.trans (le_mul_of_one_le_right (by linarith only [hp₀]) hr₁.le), hc, hC, ?_⟩
  intro Q lam h₀ h₁ l δ hl hδ₀ hδ₁ P K hK hD F G hF hG hFp hGp J t E hJ μ hμ hprob
  let f := fun ωz : FieldPair d × Regeneration.CoupledSample d =>
    F (reduce ωz.1) * G (translate (ωz.2.1 t) (reduce ωz.1))
  have ht : Measurable (fun ωz : FieldPair d × Regeneration.CoupledSample d =>
      ωz.2.1 t) := (continuous_eval_const t).measurable.comp measurable_snd.fst
  have hred : Measurable (fun ωz : FieldPair d × Regeneration.CoupledSample d =>
      reduce ωz.1) := Probability.measurable_reduce.comp measurable_fst
  have hfm : Measurable f := (hF.comp hred).mul
    (hG.comp (Probability.continuous_translate.measurable.comp (ht.prodMk hred)))
  have hpower := hmoment r hr₀ Q lam h₀ h₁ l δ hl hδ₀ hδ₁ P K hK hD
    F G hF hG hFp hGp t μ hμ
  have hμprob : IsProbabilityMeasure μ := by
    rcases hμ with rfl | hμ
    · exact Regeneration.annealedCoupledLaw_isProbabilityMeasure Q.measure K hK.1
    · rw [Set.mem_singleton_iff] at hμ
      rw [hμ]
      exact regenerationConditionedLaw_probability hd Q lam l K hK.1 hD
  let := hμprob
  have hfr : MemLp f (ENNReal.ofReal r) μ := by
    apply (integrable_norm_rpow_iff hfm.aestronglyMeasurable
      (ENNReal.ofReal_ne_zero_iff.mpr hr₀) ENNReal.ofReal_ne_top).mp
    simpa only [ENNReal.toReal_ofReal hr₀.le] using hpower.1
  have hri : (1 : ℝ≥0∞) ≤ ENNReal.ofReal r := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hr₁.le
  refine ⟨(hfr.integrable hri).integrableOn, ?_⟩
  have hb := sbxS2_setIntegral_abs_le_moment μ f hfm.aestronglyMeasurable E r
    (D * Real.exp (D * (lam ^ 2 * (t : ℝ))) *
      (eLpNorm F (ENNReal.ofReal (p₀ * r)) (reducedLaw Q)).toReal ^ r *
      (eLpNorm G (ENNReal.ofReal (p₀ * r)) (reducedLaw Q)).toReal ^ r)
    (Real.exp (J - a * (lam ^ 2 * (t : ℝ)))) hr₁ hpower.1
    (by simpa only [mul_assoc] using hpower.2) (Real.exp_pos _).le hprob
  exact hb.trans (hscalar J (lam ^ 2 * (t : ℝ)) _ _ hJ
    (by positivity) ENNReal.toReal_nonneg ENNReal.toReal_nonneg)


def firstCycleRemaindersUniformStmt : Prop :=
    ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ) (hΛ : 1 ≤ Λ₀) (hr : 1 ≤ r₀),
    ∃ l₀ : ℝ, 0 < l₀ ∧ r₀ < 2 * l₀ ∧
    ∀ l : ℝ, l₀ ≤ l → ∀ δ : ℝ, 0 < δ → δ < 1 →
    ∃ p c C : ℝ, 2 ≤ p ∧ 0 < c ∧ 0 < C ∧
    ∀ (β : ℕ → ℝ) (hβ : ∀ k, 1 ≤ k → 0 < β k),
    let SD : StructuralData d := ⟨Λ₀, r₀, β, hΛ, hr, hβ⟩
    ∀ (Q : EnvironmentLaw d SD.ellipticity SD.dependenceRange) (_hQ : HasSmoothBounds SD Q) (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
      (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
      (hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K)
      (hD : Regeneration.annealedCoupledLaw Q.measure K
        (regenerationNoReturn hd (l / lam)) ≠ 0),
    ∀ F G : FieldPair d → ℝ, Measurable F → Measurable G →
      MemLp F (ENNReal.ofReal p) (reducedLaw Q) →
      MemLp G (ENNReal.ofReal p) (reducedLaw Q) →
    ∀ t : ℝ≥0, ∀ μ ∈ ({Regeneration.annealedCoupledLaw Q.measure K,
      regenerationConditionedLaw hd Q lam l K hK.1 hD} :
        Set (Measure (FieldPair d × Regeneration.CoupledSample d))),
    IntegrableOn (fun ωz => F (reduce ωz.1) *
      G (translate (ωz.2.1 t) (reduce ωz.1)))
      {ωz | (t : ℝ≥0∞) < regenerationTime hd lam l 1 ωz.2} μ ∧
    |∫ ωz in {ωz | (t : ℝ≥0∞) < regenerationTime hd lam l 1 ωz.2},
      F (reduce ωz.1) * G (translate (ωz.2.1 t) (reduce ωz.1)) ∂μ| ≤
      C * Real.exp (-c * lam ^ 2 * (t : ℝ)) *
        (eLpNorm F (ENNReal.ofReal p) (reducedLaw Q)).toReal *
        (eLpNorm G (ENNReal.ofReal p) (reducedLaw Q)).toReal

theorem firstCycleRemaindersUniform_of_deps
    (hren : SbxCRenewalUniformR06.renewalUniformStmt)
    (hrem : node_rt_u3A_remainder_u2D_momentStmt) :
    firstCycleRemaindersUniformStmt := by
  intro d hd Λ₀ r₀ hΛ hr
  obtain ⟨lR, hlR, hsepR, hren'⟩ := hren d hd Λ₀ r₀ hΛ hr
  obtain ⟨lV, _hlV, _hsepV, hvar⟩ :=
    remainder_variable_rate_all_laws hrem d hd Λ₀ r₀
  refine ⟨max lR lV, hlR.trans_le (le_max_left _ _),
    hsepR.trans_le (by linarith only [le_max_left lR lV]), ?_⟩
  intro l hl δ hδ₀ hδ₁
  obtain ⟨c₁, C₁, a, M, _hc₁, _hC₁, ha, _hM, hdata⟩ :=
    hren' l ((le_max_left _ _).trans hl) δ hδ₀ hδ₁
  obtain ⟨p, c, C, hp, hc, hC, hvar'⟩ := hvar a ha
  let B := max 1 (max M (C₁ * M))
  have hB1 : 1 ≤ B := le_max_left _ _
  have hB : 0 < B := zero_lt_one.trans_le hB1
  let D := C * Real.exp (C * Real.log B)
  have hD : 0 < D := mul_pos hC (Real.exp_pos _)
  refine ⟨p, c, D, hp, hc, hD, ?_⟩
  intro β hβ SD Q hQ lam h₀ h₁ P K hK hDnonzero F G hF hG hFp hGp t μ hμ
  have hmom : (∫⁻ ωz, if regenerationTime hd lam l 1 ωz.2 = ⊤ then ⊤ else
      ENNReal.ofReal (Real.exp (a * lam ^ 2 *
        (regenerationTime hd lam l 1 ωz.2).toReal)) ∂μ) ≤ ENNReal.ofReal B := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hμ
    rcases hμ with rfl | rfl
    · exact ((hdata β hβ Q hQ lam h₀ h₁ P K hK hDnonzero).2.2 1).trans
        (ENNReal.ofReal_le_ofReal (by
          simpa only [pow_one] using
            (le_max_right M (C₁ * M)).trans (le_max_right 1 (max M (C₁ * M)))))
    · exact ((hdata β hβ Q hQ lam h₀ h₁ P K hK hDnonzero).2.1 1).trans
        (ENNReal.ofReal_le_ofReal (by
          simpa only [pow_one] using
            (le_max_left M (C₁ * M)).trans (le_max_right 1 (max M (C₁ * M)))))
  have hTm : Measurable (fun ωz : FieldPair d × Regeneration.CoupledSample d =>
      regenerationTime hd lam l 1 ωz.2) :=
    (Regeneration.measurable_regenerationTime (Regeneration.Renewal.regenDelta lam) lam
      (l / lam) (Regeneration.Renewal.forceCoord hd) 1).comp measurable_snd
  have htail := exponential_time_tail μ _ hTm (a * lam ^ 2) B (by positivity) t hmom
  have hprob : μ {ωz | (t : ℝ≥0∞) < regenerationTime hd lam l 1 ωz.2} ≤
      ENNReal.ofReal (Real.exp (Real.log B - a * (lam ^ 2 * (t : ℝ)))) := by
    apply htail.trans
    apply ENNReal.ofReal_le_ofReal
    rw [sub_eq_add_neg, Real.exp_add, Real.exp_log hB]
    have he : -(a * lam ^ 2) * (t : ℝ) = -(a * (lam ^ 2 * (t : ℝ))) := by ring
    simpa only [he] using (le_refl (B * Real.exp (-(a * (lam ^ 2 * (t : ℝ))))))
  have hout := hvar' Q lam h₀ h₁ l δ ((le_max_right _ _).trans hl) hδ₀ hδ₁
    P K hK hDnonzero F G hF hG hFp hGp (Real.log B) t _
      (Real.log_nonneg hB1) μ hμ hprob
  refine ⟨hout.1, ?_⟩
  have he : C * Real.exp (C * Real.log B - c * (lam ^ 2 * (t : ℝ))) =
      D * Real.exp (-c * lam ^ 2 * (t : ℝ)) := by
    dsimp only [D]
    rw [sub_eq_add_neg, Real.exp_add]
    have he : -(c * (lam ^ 2 * (t : ℝ))) = -c * lam ^ 2 * (t : ℝ) := by ring
    rw [he]
    ring
  simpa only [he] using hout.2

end EinsteinFull.Blueprint.SbxCFirstCycleRemaindersUniformR08
