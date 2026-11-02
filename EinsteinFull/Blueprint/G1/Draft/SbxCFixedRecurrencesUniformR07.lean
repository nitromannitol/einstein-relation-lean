import EinsteinFull.Blueprint.G1.Draft.SbxCFixedRadiusRecurrencesR02

/-! Conditional uniform smooth-law fixed-radius recurrences; unreviewed draft. -/
open MeasureTheory
open scoped NNReal ENNReal Topology
namespace EinsteinFull.Blueprint.SbxCFixedRecurrencesUniformR07
open EinsteinRelation EinsteinFull.Blueprint SbxS6Section3R01
open SbxCFixedRadiusRecurrencesR02

def remainderUniformSmoothStmt : Prop :=
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

theorem uniform_covariance_integrable
    (hrem : remainderUniformSmoothStmt) :
    ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ) (hΛ : 1 ≤ Λ₀) (hr : 1 ≤ r₀),
    ∃ l₀ p : ℝ, 0 < l₀ ∧ r₀ < 2 * l₀ ∧ 2 ≤ p ∧
    ∀ (β : ℕ → ℝ) (hβ : ∀ k, 1 ≤ k → 0 < β k),
    let SD : StructuralData d := ⟨Λ₀, r₀, β, hΛ, hr, hβ⟩
    ∀ (Q : EnvironmentLaw d SD.ellipticity SD.dependenceRange) (_hQ : HasSmoothBounds SD Q) (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
      (l δ : ℝ), l₀ ≤ l → 0 < δ → δ < 1 →
    ∀ (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
      (hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K)
      (hD : Regeneration.annealedCoupledLaw Q.measure K
        (regenerationNoReturn hd (l / lam)) ≠ 0),
    ∀ F G : FieldPair d → ℝ, Measurable F → Measurable G →
      MemLp F (ENNReal.ofReal p) (reducedLaw Q) →
      MemLp G (ENNReal.ofReal p) (reducedLaw Q) → ∀ t : ℝ≥0,
    ∀ μ ∈ ({Regeneration.annealedCoupledLaw Q.measure K,
      regenerationConditionedLaw hd Q lam l K hK.1 hD} :
        Set (Measure (FieldPair d × Regeneration.CoupledSample d))),
      Integrable (fun ωz => F (reduce ωz.1) *
        G (translate (ωz.2.1 t) (reduce ωz.1))) μ := by
  intro d hd Λ₀ r₀ hΛ hr
  obtain ⟨l₀, p, c, C, hl₀, hsep, hp, _hc, _hC, hrem'⟩ :=
    hrem d hd Λ₀ r₀ hΛ hr 1 1 (by norm_num) (by norm_num)
  refine ⟨l₀, p, hl₀, hsep, hp, ?_⟩
  intro β hβ
  dsimp only
  intro Q hQ lam h₀ h₁ l δ hl hδ₀ hδ₁ P K hK hD F G hF hG hFp hGp t μ hμ
  let : IsProbabilityMeasure (Regeneration.annealedCoupledLaw Q.measure K) :=
    Regeneration.annealedCoupledLaw_isProbabilityMeasure Q.measure K hK.1
  have hprob : Regeneration.annealedCoupledLaw Q.measure K Set.univ ≤
      ENNReal.ofReal (1 * Real.exp (1 * (lam ^ 2 * (t : ℝ)) -
        1 * lam ^ 2 * (t : ℝ))) := by simp
  have hint := (hrem' β hβ Q hQ lam h₀ h₁ l δ hl hδ₀ hδ₁ P K hK hD
    F G hF hG hFp hGp (lam ^ 2 * (t : ℝ)) t Set.univ
    (mul_nonneg (sq_nonneg lam) t.coe_nonneg) MeasurableSet.univ hprob μ hμ).1
  simpa only [integrableOn_univ] using hint

def fixedRecurrencesSmoothStmt : Prop :=
    ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ) (hΛ : 1 ≤ Λ₀) (hr : 1 ≤ r₀),
    ∃ l₀ p : ℝ, 0 < l₀ ∧ r₀ < 2 * l₀ ∧ 2 ≤ p ∧
    ∀ (l δ : ℝ), l₀ ≤ l → 0 < δ → δ < 1 →
    ∀ (β : ℕ → ℝ) (hβ : ∀ k, 1 ≤ k → 0 < β k),
    let SD : StructuralData d := ⟨Λ₀, r₀, β, hΛ, hr, hβ⟩
    ∀ (Q : EnvironmentLaw d SD.ellipticity SD.dependenceRange) (_hQ : HasSmoothBounds SD Q) (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
      (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
      (hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K)
      (hD : Regeneration.annealedCoupledLaw Q.measure K
        (regenerationNoReturn hd (l / lam)) ≠ 0),
    ∀ F G : FieldPair d → ℝ,
      Measurable[localSigma {x : Vec d | euclideanNorm x < l / lam}] F →
      Measurable[localSigma {x : Vec d | euclideanNorm x < l / lam}] G →
      MemLp F (ENNReal.ofReal p) (reducedLaw Q) →
      MemLp G (ENNReal.ofReal p) (reducedLaw Q) →
    let μ := Regeneration.annealedCoupledLaw Q.measure K
    let ν := regenerationConditionedLaw hd Q lam l K hK.1 hD
    let Δ := Regeneration.Renewal.regenDelta lam
    let h := fun t : ℝ≥0 => ∫ q, G (translate (q.2.1 t) (reduce q.1)) ∂ν
    let r := fun t : ℝ≥0 => ∫ q in {q | (t : ℝ≥0∞) < regenerationTime hd lam l 1 q.2},
      G (translate (q.2.1 t) (reduce q.1)) ∂ν
    let hF := fun t : ℝ≥0 => ∫ q, F (reduce q.1) *
      G (translate (q.2.1 t) (reduce q.1)) ∂μ
    let rF := fun t : ℝ≥0 => ∫ q in {q | (t : ℝ≥0∞) < regenerationTime hd lam l 1 q.2},
      F (reduce q.1) * G (translate (q.2.1 t) (reduce q.1)) ∂μ
    let q := fun n : ℕ => ∫ q in {q | regenerationTime hd lam l 1 q.2 =
      (((n : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞)}, F (reduce q.1) ∂μ
    ∀ s : ℝ≥0, s < Δ → ∀ k : ℕ,
      h (s + k * Δ) = r (s + k * Δ) +
        ∑ n ∈ Finset.range (k + 1), regenerationLatticeMass hd Q lam l K hK.1 hD n *
          h (s + (k - n : ℕ) * Δ) ∧
      hF (s + k * Δ) = rF (s + k * Δ) +
        ∑ n ∈ Finset.range (k + 1), q n * h (s + (k - n : ℕ) * Δ)

/-- Both first-cycle recurrences from smooth factorization and the uniform remainder estimate. -/
theorem fixed_recurrences_of_smooth_deps
    (hfact : SbxCFactorizationR01.environmentalFactorizationSmoothStmt)
    (hrem : remainderUniformSmoothStmt) : fixedRecurrencesSmoothStmt := by
  intro d hd Λ₀ r₀ hΛ hr
  obtain ⟨l₀, p, hl₀, hsep, hp, hInt⟩ :=
    uniform_covariance_integrable hrem d hd Λ₀ r₀ hΛ hr
  refine ⟨l₀, p, hl₀, hsep, hp, ?_⟩
  intro l δ hl hδ₀ hδ₁ β hβ
  let SD : StructuralData d := ⟨Λ₀, r₀, β, hΛ, hr, hβ⟩
  change ∀ (Q : EnvironmentLaw d SD.ellipticity SD.dependenceRange), _
  intro Q hQ lam h₀ h₁ P K hK hD F G hF hG hFp hGp
  dsimp only
  intro s hs k
  let μ := Regeneration.annealedCoupledLaw Q.measure K
  let ν := regenerationConditionedLaw hd Q lam l K hK.1 hD
  let := reducedLaw_probability Q
  let : IsProbabilityMeasure ν := regenerationConditionedLaw_probability hd Q lam l K hK.1 hD
  have hFg : Measurable F := hF.mono (Probability.localSigma_le_borel _) le_rfl
  have hGg : Measurable G := hG.mono (Probability.localSigma_le_borel _) le_rfl
  have hFi : Integrable F (reducedLaw Q) := hFp.integrable (by
    rw [← ENNReal.ofReal_one, ENNReal.ofReal_le_ofReal_iff (by positivity)]
    linarith)
  have hFr := (sbxS2_reducedFst_measurePreserving Q K hK.1).integrable_comp_of_integrable hFi
  have hiFG (v : ℝ≥0) := hInt β hβ Q hQ lam h₀ h₁ l δ hl hδ₀ hδ₁ P K hK hD F G
    hFg hGg hFp hGp v μ (by simp [μ])
  have hiG (v : ℝ≥0) : Integrable
      (fun q : FieldPair d × Regeneration.CoupledSample d =>
        G (translate (q.2.1 v) (reduce q.1))) ν := by
    simpa only [one_mul] using hInt β hβ Q hQ lam h₀ h₁ l δ hl hδ₀ hδ₁ P K hK hD
      (fun _ => 1) G measurable_const hGg (memLp_const 1) hGp v ν (by simp [ν])
  have hlpos := hl₀.trans_le hl
  have hsepl : SD.dependenceRange < 2 * l := hsep.trans_le (by linarith)
  constructor
  · have hh := first_cycle_recurrence_of_integrable hfact hd SD Q hQ lam h₀ h₁ l δ
      hlpos hsepl hδ₀ hδ₁ P K hK hD (fun _ => 1) G measurable_const hG ν
      (by simp [ν]) (integrable_const 1) (by simpa only [one_mul] using hiG) hiG s hs k
    have hmass (n : ℕ) :
        (∫ q in {q : FieldPair d × Regeneration.CoupledSample d |
          regenerationTime hd lam l 1 q.2 =
            (((n : ℝ≥0) * Regeneration.Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)},
          (1 : ℝ) ∂ν) = regenerationLatticeMass hd Q lam l K hK.1 hD n := by
      rw [setIntegral_const, smul_eq_mul, mul_one]
      rfl
    simpa only [one_mul, hmass] using hh
  · exact first_cycle_recurrence_of_integrable hfact hd SD Q hQ lam h₀ h₁ l δ
      hlpos hsepl hδ₀ hδ₁ P K hK hD F G hF hG μ (by simp [μ]) hFr hiFG hiG s hs k

end EinsteinFull.Blueprint.SbxCFixedRecurrencesUniformR07
