import EinsteinFull.Blueprint.G1.Draft.SbxCMRenewalUniformR06

/-! Conditional uniform smooth-law recurrence; draft, not reviewed or adopted. -/
open MeasureTheory
open scoped NNReal ENNReal Topology
namespace EinsteinFull.Blueprint.SbxCPhaseRecurrenceUniformR07
open EinsteinRelation EinsteinFull.Blueprint SbxS6Section3R01

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

/-- The original all-law remainder estimate implies this smooth uniform instance. -/
theorem remainderUniformSmooth_of_all_laws
    (h : node_rt_u3A_remainder_u2D_momentStmt) : remainderUniformSmoothStmt := by
  intro d hd Λ₀ r₀ hΛ hr B b hB hb
  obtain ⟨l₀, p, c, C, hl₀, hsep, hp, hc, hC, h⟩ :=
    h d hd Λ₀ r₀ B b hB hb
  exact ⟨l₀, p, c, C, hl₀, hsep, hp, hc, hC, fun _ _ Q _ => h Q⟩

/-- A uniform m-renewal hypothesis specializes to the fixed-structure version. -/
theorem mRenewal_of_uniform (h : SbxCMRenewalUniformR06.phaseMRenewalSmoothStmt) :
    SbxCPhaseSmoothR01.phaseMRenewalSmoothStmt := by
  intro d hd D l δ hl hsep hδ₀ hδ₁
  obtain ⟨C, hC, h⟩ := h d hd D.ellipticity D.dependenceRange
    D.one_le_ellipticity D.one_le_dependenceRange l δ hl hsep hδ₀ hδ₁
  exact ⟨C, hC, h D.derivativeBound D.derivativeBound_pos⟩

theorem uniform_translated_integrable
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
    ∀ G : FieldPair d → ℝ, Measurable G →
      MemLp G (ENNReal.ofReal p) (reducedLaw Q) → ∀ t : ℝ≥0,
    ∀ μ ∈ ({Regeneration.annealedCoupledLaw Q.measure K,
      regenerationConditionedLaw hd Q lam l K hK.1 hD} :
        Set (Measure (FieldPair d × Regeneration.CoupledSample d))),
      Integrable (fun ωz => G (translate (ωz.2.1 t) (reduce ωz.1))) μ := by
  intro d hd Λ₀ r₀ hΛ hr
  obtain ⟨l₀, p, c, C, hl₀, hsep, hp, _hc, _hC, hrem'⟩ :=
    hrem d hd Λ₀ r₀ hΛ hr 1 1 (by norm_num) (by norm_num)
  refine ⟨l₀, p, hl₀, hsep, hp, ?_⟩
  intro β hβ
  dsimp only
  intro Q hQ lam h₀ h₁ l δ hl hδ₀ hδ₁ P K hK hD G hG hLp t μ hμ
  let : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  let : IsProbabilityMeasure (Regeneration.annealedCoupledLaw Q.measure K) :=
    Regeneration.annealedCoupledLaw_isProbabilityMeasure Q.measure K hK.1
  have hprob : Regeneration.annealedCoupledLaw Q.measure K Set.univ ≤
      ENNReal.ofReal (1 * Real.exp (1 * (lam ^ 2 * (t : ℝ)) -
        1 * lam ^ 2 * (t : ℝ))) := by simp
  have hint := (hrem' β hβ Q hQ lam h₀ h₁ l δ hl hδ₀ hδ₁ P K hK hD
    (fun _ => 1) G measurable_const hG (memLp_const 1) hLp
    (lam ^ 2 * (t : ℝ)) t Set.univ (mul_nonneg (sq_nonneg lam) t.coe_nonneg)
    MeasurableSet.univ hprob μ hμ).1
  simpa only [one_mul, integrableOn_univ] using hint

theorem phase_m_renewal_eq_memLp
    (hmren : SbxCMRenewalUniformR06.phaseMRenewalSmoothStmt)
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
        (regenerationNoReturn hd (l / lam)) ≠ 0)
      (A : ℝ) (m : ℕ), 1 ≤ m →
      10 * (m : ℝ) * l - l - A ≥ -2 * l →
    ∀ G : FieldPair d → ℝ,
      Measurable[localSigma {x : Vec d | euclideanNorm x < A / lam}] G →
      MemLp G (ENNReal.ofReal p) (reducedLaw Q) →
    let ν := regenerationConditionedLaw hd Q lam l K hK.1 hD
    let Δ := Regeneration.Renewal.regenDelta lam
    let pn := regenerationLatticeMass hd Q lam l K hK.1 hD
    let h := fun t : ℝ≥0 => ∫ ωz in
      {ωz | regenerationTime hd lam l m ωz.2 ≤ (t : ℝ≥0∞)},
      G (translate (ωz.2.1 t) (reduce ωz.1)) ∂ν
    let r := fun t : ℝ≥0 => ∫ ωz in
      {ωz | regenerationTime hd lam l m ωz.2 ≤ (t : ℝ≥0∞) ∧
        (t : ℝ≥0∞) < regenerationTime hd lam l (m + 1) ωz.2},
      G (translate (ωz.2.1 t) (reduce ωz.1)) ∂ν
    ∀ t : ℝ≥0, h t = r t +
      ∑ n ∈ Finset.range (⌊(t : ℝ) / (Δ : ℝ)⌋₊ + 1), pn n * h (t - n * Δ) := by
  intro d hd Λ₀ r₀ hΛ hr
  obtain ⟨l₀, p, hl₀, hsep, hp, hInt⟩ :=
    uniform_translated_integrable hrem d hd Λ₀ r₀ hΛ hr
  refine ⟨l₀, p, hl₀, hsep, hp, ?_⟩
  intro β hβ
  let SD : StructuralData d := ⟨Λ₀, r₀, β, hΛ, hr, hβ⟩
  change ∀ (Q : EnvironmentLaw d SD.ellipticity SD.dependenceRange), _
  intro Q hQ lam h₀ h₁ l δ hl hδ₀ hδ₁ P K hK hD A m hm hs G hG hLp
  let ν := regenerationConditionedLaw hd Q lam l K hK.1 hD
  let Δ := Regeneration.Renewal.regenDelta lam
  let pn := regenerationLatticeMass hd Q lam l K hK.1 hD
  let H := fun (F : FieldPair d → ℝ) (t : ℝ≥0) => ∫ ωz in
    {ωz | regenerationTime hd lam l m ωz.2 ≤ (t : ℝ≥0∞)},
    F (translate (ωz.2.1 t) (reduce ωz.1)) ∂ν
  let R := fun (F : FieldPair d → ℝ) (t : ℝ≥0) => ∫ ωz in
    {ωz | regenerationTime hd lam l m ωz.2 ≤ (t : ℝ≥0∞) ∧
      (t : ℝ≥0∞) < regenerationTime hd lam l (m + 1) ωz.2},
    F (translate (ωz.2.1 t) (reduce ωz.1)) ∂ν
  let Gk := fun (n : ℕ) (ω : FieldPair d) => max (-(n : ℝ)) (min (n : ℝ) (G ω))
  have hGk (n : ℕ) :
      Measurable[localSigma {x : Vec d | euclideanNorm x < A / lam}] (Gk n) :=
    measurable_const.max (measurable_const.min hG)
  have hb (n : ℕ) : Regeneration.BoundedRealTest (Gk n) := by
    refine ⟨(n : ℝ), fun ω => abs_le.mpr ⟨le_max_left _ _, ?_⟩⟩
    exact max_le
      ((neg_nonpos.mpr (Nat.cast_nonneg n)).trans (Nat.cast_nonneg n)) (min_le_left _ _)
  have hi (t : ℝ≥0) :
      Integrable (fun ωz => G (translate (ωz.2.1 t) (reduce ωz.1))) ν :=
    hInt β hβ Q hQ lam h₀ h₁ l δ hl hδ₀ hδ₁ P K hK hD G
      (hG.mono (Probability.localSigma_le_borel _) le_rfl) hLp t ν (by simp [ν])
  have hH (t : ℝ≥0) : Filter.Tendsto (fun n => H (Gk n) t)
      Filter.atTop (𝓝 (H G t)) :=
    tendsto_setIntegral_clamp ν _ (hi t) _
  have hR (t : ℝ≥0) : Filter.Tendsto (fun n => R (Gk n) t)
      Filter.atTop (𝓝 (R G t)) :=
    tendsto_setIntegral_clamp ν _ (hi t) _
  change ∀ t, H G t = R G t +
    ∑ n ∈ Finset.range (⌊(t : ℝ) / (Δ : ℝ)⌋₊ + 1), pn n * H G (t - n * Δ)
  intro t
  have heq (n : ℕ) : H (Gk n) t = R (Gk n) t +
      ∑ k ∈ Finset.range (⌊(t : ℝ) / (Δ : ℝ)⌋₊ + 1),
        pn k * H (Gk n) (t - k * Δ) :=
    SbxCPhaseSmoothR01.smooth_m_renewal_eq_of_support (mRenewal_of_uniform hmren) d hd SD l δ (hl₀.trans_le hl)
      (hsep.trans_le (by linarith)) hδ₀ hδ₁ Q hQ lam h₀ h₁ P K hK hD A m hm hs
      (Gk n) (hGk n) (hb n) t
  have hsum : Filter.Tendsto
      (fun n : ℕ => ∑ k ∈ Finset.range (⌊(t : ℝ) / (Δ : ℝ)⌋₊ + 1),
        pn k * H (Gk n) (t - k * Δ)) Filter.atTop
      (𝓝 (∑ k ∈ Finset.range (⌊(t : ℝ) / (Δ : ℝ)⌋₊ + 1),
        pn k * H G (t - k * Δ))) :=
    tendsto_finsetSum (Finset.range (⌊(t : ℝ) / (Δ : ℝ)⌋₊ + 1))
      (fun k _ => tendsto_const_nhds.mul (hH (t - k * Δ)))
  exact tendsto_nhds_unique (hH t) (((hR t).add hsum).congr'
    (Filter.Eventually.of_forall (fun n => (heq n).symm)))

end EinsteinFull.Blueprint.SbxCPhaseRecurrenceUniformR07
