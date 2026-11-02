import EinsteinFull.Blueprint.G1.Proofs.SbxS9PhaseError
import EinsteinFull.Blueprint.Roots.Draft.SbxCRenewalUniformR06

/-! Conditional uniform-witness phase cycle estimates, draft only. -/
open MeasureTheory
open scoped NNReal ENNReal Topology
namespace EinsteinFull.Blueprint.SbxCConditionedCycleUniformR07
open EinsteinRelation EinsteinFull.Blueprint

def remainderUniformStmt : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ) (hΛ : 1 ≤ Λ₀) (hr : 1 ≤ r₀) (B b : ℝ), 0 < B → 0 < b →
    ∃ l₀ p c C : ℝ, 0 < l₀ ∧ r₀ < 2 * l₀ ∧ 2 ≤ p ∧ 0 < c ∧ 0 < C ∧
    ∀ (β : ℕ → ℝ) (hβ : ∀ k, 1 ≤ k → 0 < β k),
    let D : StructuralData d := ⟨Λ₀, r₀, β, hΛ, hr, hβ⟩
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange), HasSmoothBounds D Q →
    ∀ (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
      (l δ : ℝ), l₀ ≤ l → 0 < δ → δ < 1 →
    ∀ (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
      (hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K)
      (hD : Regeneration.annealedCoupledLaw Q.measure K
        (regenerationNoReturn hd (l / lam)) ≠ 0),
    ∀ F G : FieldPair d → ℝ,
    Measurable F → Measurable G →
    MemLp F (ENNReal.ofReal p) (reducedLaw Q) →
    MemLp G (ENNReal.ofReal p) (reducedLaw Q) →
    ∀ (J : ℝ) (t : ℝ≥0) (A : Set (FieldPair d × Regeneration.CoupledSample d)),
    0 ≤ J → MeasurableSet A →
    Regeneration.annealedCoupledLaw Q.measure K A ≤
      ENNReal.ofReal (B * Real.exp (B * J - b * lam ^ 2 * (t : ℝ))) →
    ∀ μ ∈ ({Regeneration.annealedCoupledLaw Q.measure K,
      regenerationConditionedLaw hd Q lam l K hK.1 hD} :
        Set (Measure (FieldPair d × Regeneration.CoupledSample d))),
      IntegrableOn (fun ωz => F (reduce ωz.1) *
        G (translate (ωz.2.1 t) (reduce ωz.1))) A μ ∧
      |∫ ωz in A, F (reduce ωz.1) * G (translate (ωz.2.1 t) (reduce ωz.1)) ∂μ| ≤
        C * Real.exp (C * J - c * lam ^ 2 * (t : ℝ)) *
          (eLpNorm F (ENNReal.ofReal p) (reducedLaw Q)).toReal *
          (eLpNorm G (ENNReal.ofReal p) (reducedLaw Q)).toReal

theorem uniform_covariance_power_moment
    (hrem : remainderUniformStmt) :
    ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ) (hΛ : 1 ≤ Λ₀) (hr : 1 ≤ r₀),
    ∃ l₀ p C : ℝ, 0 < l₀ ∧ r₀ < 2 * l₀ ∧ 2 ≤ p ∧ 0 < C ∧
    ∀ (r : ℝ), 0 < r →
    ∀ (β : ℕ → ℝ) (hβ : ∀ k, 1 ≤ k → 0 < β k),
    let D : StructuralData d := ⟨Λ₀, r₀, β, hΛ, hr, hβ⟩
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (_hQ : HasSmoothBounds D Q) (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
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
    hrem d hd Λ₀ r₀ hΛ hr 1 1 (by norm_num) (by norm_num)
  refine ⟨l₀, p, C, hl₀, hsep, hp, hC, ?_⟩
  intro r hr β hβ D Q hQ lam h₀ h₁ l δ hl hδ₀ hδ₁ P K hK hD F G hF hG hFp hGp t μ hμ
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
  have hmain := hrem' β hβ Q hQ lam h₀ h₁ l δ hl hδ₀ hδ₁ P K hK hD
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

theorem uniform_conditioned_variable_rate
    (hrem : remainderUniformStmt) :
    ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ) (hΛ : 1 ≤ Λ₀) (hr : 1 ≤ r₀),
    ∃ l₀ : ℝ, 0 < l₀ ∧ r₀ < 2 * l₀ ∧
    ∀ a : ℝ, 0 < a → ∃ p c C : ℝ, 2 ≤ p ∧ 0 < c ∧ 0 < C ∧
    ∀ (β : ℕ → ℝ) (hβ : ∀ k, 1 ≤ k → 0 < β k),
    let D : StructuralData d := ⟨Λ₀, r₀, β, hΛ, hr, hβ⟩
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (_hQ : HasSmoothBounds D Q) (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
      (l δ : ℝ), l₀ ≤ l → 0 < δ → δ < 1 →
    ∀ (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
      (hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K)
      (hD : Regeneration.annealedCoupledLaw Q.measure K
        (regenerationNoReturn hd (l / lam)) ≠ 0),
    ∀ F G : FieldPair d → ℝ, Measurable F → Measurable G →
      MemLp F (ENNReal.ofReal p) (reducedLaw Q) →
      MemLp G (ENNReal.ofReal p) (reducedLaw Q) →
    ∀ (J : ℝ) (t : ℝ≥0) (E : Set (FieldPair d × Regeneration.CoupledSample d)),
      0 ≤ J → regenerationConditionedLaw hd Q lam l K hK.1 hD E ≤
        ENNReal.ofReal (Real.exp (J - a * lam ^ 2 * (t : ℝ))) →
      IntegrableOn (fun ωz => F (reduce ωz.1) *
        G (translate (ωz.2.1 t) (reduce ωz.1))) E
        (regenerationConditionedLaw hd Q lam l K hK.1 hD) ∧
      |∫ ωz in E, F (reduce ωz.1) *
        G (translate (ωz.2.1 t) (reduce ωz.1))
          ∂regenerationConditionedLaw hd Q lam l K hK.1 hD| ≤
        C * Real.exp (C * J - c * lam ^ 2 * (t : ℝ)) *
          (eLpNorm F (ENNReal.ofReal p) (reducedLaw Q)).toReal *
          (eLpNorm G (ENNReal.ofReal p) (reducedLaw Q)).toReal := by
  intro d hd Λ₀ r₀ hΛ hr
  obtain ⟨l₀, p₀, D, hl₀, hsep, hp₀, hDpos, hmoment⟩ :=
    uniform_covariance_power_moment hrem d hd Λ₀ r₀ hΛ hr
  refine ⟨l₀, hl₀, hsep, ?_⟩
  intro a ha
  obtain ⟨r, c, C, hr, hc, hC, hscalar⟩ :=
    sbxS2_power_interpolation_constants D a hDpos ha
  have hr₁ : 1 < r := lt_of_lt_of_le (by norm_num) hr
  have hr₀ : 0 < r := lt_trans zero_lt_one hr₁
  have hp₀pos : 0 ≤ p₀ := le_trans (by norm_num) hp₀
  refine ⟨p₀ * r, c, C, ?_, hc, hC, ?_⟩
  · exact hp₀.trans (le_mul_of_one_le_right hp₀pos hr₁.le)
  intro β hβ SD Q hQ lam h₀ h₁ l δ hl hδ₀ hδ₁ P K hK hD F G hF hG hFp hGp J t E hJ hprob
  let μ := regenerationConditionedLaw hd Q lam l K hK.1 hD
  let f := fun ωz : FieldPair d × Regeneration.CoupledSample d =>
    F (reduce ωz.1) * G (translate (ωz.2.1 t) (reduce ωz.1))
  have hfm : Measurable f :=
    ((hF.comp Probability.measurable_reduce).comp measurable_fst).mul
      (hG.comp (Probability.continuous_translate.measurable.comp
        (((continuous_eval_const t).measurable.comp measurable_snd.fst).prodMk
          (Probability.measurable_reduce.comp measurable_fst))))
  have hpower := hmoment r hr₀ β hβ Q hQ lam h₀ h₁ l δ hl hδ₀ hδ₁ P K hK hD
    F G hF hG hFp hGp t μ (by simp only [μ, Set.mem_insert_iff, Set.mem_singleton_iff, or_true])
  let : IsProbabilityMeasure μ :=
    regenerationConditionedLaw_probability hd Q lam l K hK.1 hD
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

theorem uniform_renewal_cycle_tails (hren : SbxCRenewalUniformR06.renewalUniformStmt) :
    ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ) (hΛ : 1 ≤ Λ₀) (hr : 1 ≤ r₀),
    ∃ l₀ : ℝ, 0 < l₀ ∧ r₀ < 2 * l₀ ∧
    ∀ l : ℝ, l₀ ≤ l → ∀ δ : ℝ, 0 < δ → δ < 1 →
    ∃ a C : ℝ, 0 < a ∧ 0 < C ∧
    ∀ (β : ℕ → ℝ) (hβ : ∀ k, 1 ≤ k → 0 < β k),
    let D : StructuralData d := ⟨Λ₀, r₀, β, hΛ, hr, hβ⟩
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (_hQ : HasSmoothBounds D Q) (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
      (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
      (hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K)
      (hD : Regeneration.annealedCoupledLaw Q.measure K
        (regenerationNoReturn hd (l / lam)) ≠ 0),
    ∀ (m : ℕ) (t : ℝ≥0),
      regenerationConditionedLaw hd Q lam l K hK.1 hD
        {ωz | regenerationTime hd lam l m ωz.2 ≤ (t : ℝ≥0∞) ∧
          (t : ℝ≥0∞) < regenerationTime hd lam l (m + 1) ωz.2} ≤
        ENNReal.ofReal (C * Real.exp (C * m - a * lam ^ 2 * (t : ℝ))) := by
  intro d hd Λ₀ r₀ hΛ hr
  obtain ⟨l₀, hl₀, hsep, hren'⟩ := hren d hd Λ₀ r₀ hΛ hr
  refine ⟨l₀, hl₀, hsep, ?_⟩
  intro l hl δ hδ₀ hδ₁
  obtain ⟨_, _, a, M, _, _, ha, hM, hmoment⟩ := hren' l hl δ hδ₀ hδ₁
  obtain ⟨C, hC, hcycle⟩ := geometric_cycle_bound M 1 hM
  refine ⟨a, C, ha, hC, ?_⟩
  intro β hβ D Q hQ lam h₀ h₁ P K hK hD m t
  have htail := regeneration_cycle_tail_of_moment d hd lam l a (M ^ (m + 1)) ha.le m
    (regenerationConditionedLaw hd Q lam l K hK.1 hD)
    ((hmoment β hβ Q hQ lam h₀ h₁ P K hK hD).2.1 (m + 1)) t
  apply htail.trans
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ (C * Real.exp (C * m)) * Real.exp (-a * lam ^ 2 * (t : ℝ)) :=
      mul_le_mul_of_nonneg_right (by simpa only [one_mul] using hcycle m)
        (Real.exp_pos _).le
    _ = _ := by simp only [sub_eq_add_neg, Real.exp_add, neg_mul, mul_assoc]

theorem uniform_conditioned_cycle_remainder
    (hren : SbxCRenewalUniformR06.renewalUniformStmt)
    (hrem : remainderUniformStmt) :
    ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ) (hΛ : 1 ≤ Λ₀) (hr : 1 ≤ r₀),
    ∃ l₀ : ℝ, 0 < l₀ ∧ r₀ < 2 * l₀ ∧
    ∀ l : ℝ, l₀ ≤ l → ∀ δ : ℝ, 0 < δ → δ < 1 →
    ∃ p c C : ℝ, 2 ≤ p ∧ 0 < c ∧ 0 < C ∧
    ∀ (β : ℕ → ℝ) (hβ : ∀ k, 1 ≤ k → 0 < β k),
    let D : StructuralData d := ⟨Λ₀, r₀, β, hΛ, hr, hβ⟩
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (_hQ : HasSmoothBounds D Q) (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
      (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
      (hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K)
      (hD : Regeneration.annealedCoupledLaw Q.measure K
        (regenerationNoReturn hd (l / lam)) ≠ 0),
    ∀ (m : ℕ) (G : FieldPair d → ℝ), Measurable G →
      MemLp G (ENNReal.ofReal p) (reducedLaw Q) → ∀ t : ℝ≥0,
      |∫ ωz in {ωz | regenerationTime hd lam l m ωz.2 ≤ (t : ℝ≥0∞) ∧
        (t : ℝ≥0∞) < regenerationTime hd lam l (m + 1) ωz.2},
        G (translate (ωz.2.1 t) (reduce ωz.1))
          ∂regenerationConditionedLaw hd Q lam l K hK.1 hD| ≤
        C * Real.exp (C * m - c * lam ^ 2 * (t : ℝ)) *
          (eLpNorm G (ENNReal.ofReal p) (reducedLaw Q)).toReal := by
  intro d hd Λ₀ r₀ hΛ hr
  obtain ⟨L₀, hL₀, hsep₀, hevent⟩ :=
    uniform_conditioned_variable_rate hrem d hd Λ₀ r₀ hΛ hr
  obtain ⟨L₁, _hL₁, _hsep₁, htail⟩ := uniform_renewal_cycle_tails hren d hd Λ₀ r₀ hΛ hr
  refine ⟨max L₀ L₁, hL₀.trans_le (le_max_left _ _),
    hsep₀.trans_le (by linarith only [le_max_left L₀ L₁]), ?_⟩
  intro l hl δ hδ₀ hδ₁
  have hl₀ : L₀ ≤ l := (le_max_left _ _).trans hl
  have hl₁ : L₁ ≤ l := (le_max_right _ _).trans hl
  obtain ⟨a, B, ha, hB, htail'⟩ := htail l hl₁ δ hδ₀ hδ₁
  obtain ⟨p, c, C₀, hp, hc, hC₀, hevent'⟩ := hevent a ha
  obtain ⟨C, hC, hcycle⟩ := geometric_cycle_bound (Real.exp (C₀ * B)) C₀
    (Real.exp_pos _)
  refine ⟨p, c, C, hp, hc, hC, ?_⟩
  intro β hβ D Q hQ lam h₀ h₁ P K hK hD m G hG hLp t
  let : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  let J := B * ((m : ℝ) + 1)
  have hJ : 0 ≤ J := mul_nonneg hB.le (by positivity)
  have hprob : regenerationConditionedLaw hd Q lam l K hK.1 hD
      {ωz | regenerationTime hd lam l m ωz.2 ≤ (t : ℝ≥0∞) ∧
        (t : ℝ≥0∞) < regenerationTime hd lam l (m + 1) ωz.2} ≤
      ENNReal.ofReal (Real.exp (J - a * lam ^ 2 * (t : ℝ))) := by
    apply (htail' β hβ Q hQ lam h₀ h₁ P K hK hD m t).trans
    apply ENNReal.ofReal_le_ofReal
    calc
      B * Real.exp (B * m - a * lam ^ 2 * (t : ℝ)) ≤
          Real.exp B * Real.exp (B * m - a * lam ^ 2 * (t : ℝ)) :=
        mul_le_mul_of_nonneg_right
          ((show B ≤ B + 1 by linarith).trans (Real.add_one_le_exp B))
          (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; dsimp only [J]; ring
  have hone : eLpNorm (fun _ : FieldPair d => (1 : ℝ))
      (ENNReal.ofReal p) (reducedLaw Q) = 1 := by
    rw [eLpNorm_const' 1 (ne_of_gt (ENNReal.ofReal_pos.mpr (by linarith)))
      ENNReal.ofReal_ne_top]
    simp
  have hout := hevent' β hβ Q hQ lam h₀ h₁ l δ hl₀ hδ₀ hδ₁ P K hK hD
    (fun _ => 1) G measurable_const hG (memLp_const 1) hLp J t _ hJ hprob
  have hbound : |∫ ωz in {ωz | regenerationTime hd lam l m ωz.2 ≤ (t : ℝ≥0∞) ∧
      (t : ℝ≥0∞) < regenerationTime hd lam l (m + 1) ωz.2},
      G (translate (ωz.2.1 t) (reduce ωz.1))
        ∂regenerationConditionedLaw hd Q lam l K hK.1 hD| ≤
      C₀ * Real.exp (C₀ * J - c * lam ^ 2 * (t : ℝ)) *
        (eLpNorm G (ENNReal.ofReal p) (reducedLaw Q)).toReal := by
    simpa only [one_mul, hone, ENNReal.toReal_one, mul_one] using hout.2
  have hpref : C₀ * Real.exp (C₀ * J) ≤ C * Real.exp (C * m) := by
    calc
      _ = C₀ * (Real.exp (C₀ * B)) ^ (m + 1) := by
        rw [← Real.exp_nat_mul]
        congr 1
        congr 1
        dsimp only [J]
        push_cast
        ring
      _ ≤ _ := hcycle m
  apply hbound.trans
  calc
    _ = (C₀ * Real.exp (C₀ * J)) * Real.exp (-c * lam ^ 2 * (t : ℝ)) *
        (eLpNorm G (ENNReal.ofReal p) (reducedLaw Q)).toReal := by
      simp only [sub_eq_add_neg, Real.exp_add, neg_mul, mul_assoc]
    _ ≤ (C * Real.exp (C * m)) * Real.exp (-c * lam ^ 2 * (t : ℝ)) *
        (eLpNorm G (ENNReal.ofReal p) (reducedLaw Q)).toReal :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hpref (Real.exp_pos _).le) ENNReal.toReal_nonneg
    _ = _ := by simp only [sub_eq_add_neg, Real.exp_add, neg_mul, mul_assoc]

end EinsteinFull.Blueprint.SbxCConditionedCycleUniformR07
