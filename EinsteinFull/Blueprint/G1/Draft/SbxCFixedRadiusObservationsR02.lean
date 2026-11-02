import EinsteinFull.Blueprint.G1.Draft.SbxS6LocalMixingSmoothR01
import EinsteinFull.Blueprint.G1.Draft.SbxCKMCenteredSlicesSmoothR01
import EinsteinFull.Blueprint.Roots.Draft.SbxCRenewalRootR01

/-! Conditional fixed-radius observation producer for smooth laws. -/
open MeasureTheory
open scoped NNReal ENNReal Topology
namespace EinsteinFull.Blueprint.SbxS6Section3R01
open EinsteinRelation EinsteinFull.Blueprint

/-- Literal smooth first-cycle recurrence output, still a producer obligation. -/
def fixedRecurrencesSmoothStmt : Prop :=
    ∀ (d : ℕ) (hd : 2 ≤ d) (SD : StructuralData d),
    ∃ l₀ p : ℝ, 0 < l₀ ∧ SD.dependenceRange < 2 * l₀ ∧ 2 ≤ p ∧
    ∀ (l δ : ℝ), l₀ ≤ l → 0 < δ → δ < 1 →
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

private theorem local_many_cycle_of_renewal (hren : SbxCRenewalR01.renewalSmoothStmt) :
    SbxCKMCenteredSlicesSmoothR01.centeredManyCycleSmoothStmt := by
  intro d hd SD
  obtain ⟨l₀, hl₀, hsep, hren'⟩ := hren d hd SD
  refine ⟨l₀, hl₀, hsep, ?_⟩
  intro l hl δ hδ₀ hδ₁
  obtain ⟨c, C, a, M, _hc, hC, ha, hM, hdata⟩ := hren' l hl δ hδ₀ hδ₁
  refine ⟨a, M, C, ha, hM, hC, ?_⟩
  intro Q hQ lam h₀ h₁ P K hK hD
  exact (hdata Q hQ lam h₀ h₁ P K hK hD).2

theorem local_scalar_of_renewal (hren : SbxCRenewalR01.renewalSmoothStmt) :
    ∀ (d : ℕ) (hd : 2 ≤ d) (SD : StructuralData d),
    ∃ l₀ : ℝ, 0 < l₀ ∧ SD.dependenceRange < 2 * l₀ ∧
    ∀ l : ℝ, l₀ ≤ l → ∀ δ : ℝ, 0 < δ → δ < 1 →
    ∀ b : ℝ, 0 < b →
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    ∀ (Q : EnvironmentLaw d SD.ellipticity SD.dependenceRange) (_hQ : HasSmoothBounds SD Q) (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
      (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
      (hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K)
      (hD : Regeneration.annealedCoupledLaw Q.measure K
        (regenerationNoReturn hd (l / lam)) ≠ 0),
    let Δ := Regeneration.Renewal.regenDelta lam
    let pn := regenerationLatticeMass hd Q lam l K hK.1 hD
    let mean := ∑' n : ℕ, (n : ℝ) * pn n
    ∀ (s : ℝ≥0), s < Δ → ∀ (h r hF rF : ℕ → ℝ) (q : ℕ → ℝ)
      (R Rf Bq : ℝ), 0 ≤ R → 0 ≤ Rf → 0 ≤ Bq →
    (∀ j, h j = r j + ∑ n ∈ Finset.range (j + 1), pn n * h (j - n)) →
    (∀ j, hF j = rF j + ∑ n ∈ Finset.range (j + 1), q n * h (j - n)) →
    (∀ j, |r j| ≤ R * Real.exp (-b * j)) →
    (∀ j, |rF j| ≤ Rf * Real.exp (-b * j)) →
    (∀ n, |q n| ≤ Bq * Real.exp (-b * n)) →
    Summable q → (∑' n, q n) = 0 →
    let H := mean⁻¹ * ∑' j : ℕ, r j
    Summable r ∧ |H| ≤ C * R ∧ ∀ j : ℕ,
      |h j - H| ≤ C * R * Real.exp (-c * j) ∧
      hF j = rF j +
        (∑ n ∈ Finset.range (j + 1), q n * (h (j - n) - H)) -
        H * ∑' n : ℕ, q (j + 1 + n) ∧
      |hF j| ≤ C * (Rf + Bq * R) * Real.exp (-c * j) := by
  intro d hd SD
  obtain ⟨l₀, hl₀, hsep, hren'⟩ := hren d hd SD
  refine ⟨l₀, hl₀, hsep, ?_⟩
  intro l hl δ hδ₀ hδ₁ b hb
  obtain ⟨c₁, C₁, a, M, hc₁, hC₁, _, _, hdata⟩ := hren' l hl δ hδ₀ hδ₁
  obtain ⟨c, C, hc, hC, hscalar⟩ :=
    sbxS4_fixedRadius_scalar_uniform C₁ c₁ b hC₁ hc₁ hb
  refine ⟨c, C, hc, hC, ?_⟩
  intro Q hQ lam h₀ h₁ P K hK hD
  let pn := regenerationLatticeMass hd Q lam l K hK.1 hD
  have hp : pn 0 = 0 :=
    regenerationLatticeMass_zero hd Q lam l h₀ (hl₀.trans_le hl) K hK.1 hD
  have hmean : (∑' n : ℕ, pn n * (n : ℝ)) = ∑' n : ℕ, (n : ℝ) * pn n :=
    tsum_congr (fun n => mul_comm _ _)
  have hU : ∀ n : ℕ, |(∑' j : ℕ, latticeConvolutionPower pn j n) -
      (∑' n : ℕ, (n : ℝ) * pn n)⁻¹| ≤ C₁ * Real.exp (-c₁ * n) := by
    have h := (hdata Q hQ lam h₀ h₁ P K hK hD).1
    change ∀ n : ℕ, |(∑' j : ℕ, latticeConvolutionPower pn j n) -
      (∑' n : ℕ, pn n * (n : ℝ))⁻¹| ≤ C₁ * Real.exp (-c₁ * n) at h
    rwa [hmean] at h
  dsimp only
  intro s _hs
  exact hscalar pn _ hp hU

theorem local_centered_slices_of_renewal (hren : SbxCRenewalR01.renewalSmoothStmt) :
    ∀ (d : ℕ) (hd : 2 ≤ d) (SD : StructuralData d),
    ∃ l₀ : ℝ, 0 < l₀ ∧ SD.dependenceRange < 2 * l₀ ∧
    ∀ l : ℝ, l₀ ≤ l → ∀ δ : ℝ, 0 < δ → δ < 1 →
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    ∀ (Q : EnvironmentLaw d SD.ellipticity SD.dependenceRange) (_hQ : HasSmoothBounds SD Q) (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
      (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
      (_hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K)
      (_hD : Regeneration.annealedCoupledLaw Q.measure K
        (regenerationNoReturn hd (l / lam)) ≠ 0)
      (p : ℝ), 2 ≤ p → ∀ F : FieldPair d → ℝ,
    Measurable F → MemLp F (ENNReal.ofReal p) (reducedLaw Q) →
    (∫ ω, F ω ∂reducedLaw Q) = 0 →
    let q := fun n : ℕ => ∫ ωz in {ωz | regenerationTime hd lam l 1 ωz.2 =
      (((n : ℝ≥0) * Regeneration.Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)},
      F (reduce ωz.1) ∂Regeneration.annealedCoupledLaw Q.measure K
    Summable q ∧ (∑' n, q n) = 0 ∧
      ∀ n : ℕ, |q n| ≤ C * Real.exp (-c * n) *
        (eLpNorm F 2 (reducedLaw Q)).toReal := by
  intro d hd SD
  have hmany := local_many_cycle_of_renewal hren
  obtain ⟨lS, hlS, hsepS, hsum⟩ :=
    SbxCKMCenteredSlicesSmoothR01.smooth_centered_slices_of_manyCycleMoment hmany d hd SD
  obtain ⟨lD, hlD, _hsepD, hdec⟩ :=
    SbxCKMCenteredSlicesSmoothR01.smooth_slice_decay_of_manyCycleMoment hmany d hd SD
  refine ⟨max lS lD, hlS.trans_le (le_max_left _ _),
    hsepS.trans_le (by linarith only [le_max_left lS lD]), ?_⟩
  intro l hl δ hδ₀ hδ₁
  obtain ⟨a, A, ha, _hA, hdec'⟩ :=
    hdec l ((le_max_right _ _).trans hl) δ hδ₀ hδ₁
  refine ⟨a / 2, Real.exp (A / 2), half_pos ha, Real.exp_pos _, ?_⟩
  intro Q hQ lam h₀ h₁ P K hK hD p hp F hF hFp hzero
  obtain ⟨hqs, hq0⟩ := hsum l ((le_max_left _ _).trans hl) δ hδ₀ hδ₁
    Q hQ lam h₀ h₁ P K hK hD p ((by norm_num : (1 : ℝ) ≤ 2).trans hp)
      F hF hFp hzero 1
  refine ⟨hqs, hq0, ?_⟩
  intro n
  let := reducedLaw_probability Q
  have hp2 : (2 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    simpa only [ENNReal.ofReal_ofNat] using ENNReal.ofReal_le_ofReal hp
  have hFn : MemLp F (ENNReal.ofReal 2) (reducedLaw Q) := by
    simpa only [ENNReal.ofReal_ofNat] using hFp.mono_exponent hp2
  have hbound := hdec' Q hQ lam h₀ h₁ P K hK hD 2 le_rfl F hF hFn 1 le_rfl n
  have hexp : Real.exp ((A * (1 : ℕ) - a * n) / 2) =
      Real.exp (A / 2) * Real.exp (-(a / 2) * n) := by
    rw [← Real.exp_add]
    congr 1
    push_cast
    ring
  simpa only [ENNReal.ofReal_ofNat, hexp] using hbound

theorem local_first_cycle_remainders
    (hren : SbxCRenewalR01.renewalSmoothStmt) (hrem : node_rt_u3A_remainder_u2D_momentStmtV3) :
    ∀ (d : ℕ) (hd : 2 ≤ d) (SD : StructuralData d),
    ∃ l₀ : ℝ, 0 < l₀ ∧ SD.dependenceRange < 2 * l₀ ∧
    ∀ l : ℝ, l₀ ≤ l → ∀ δ : ℝ, 0 < δ → δ < 1 →
    ∃ p c C : ℝ, 2 ≤ p ∧ 0 < c ∧ 0 < C ∧
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
        (eLpNorm G (ENNReal.ofReal p) (reducedLaw Q)).toReal := by
  intro d hd SD
  obtain ⟨lR, hlR, hsepR, hren'⟩ := hren d hd SD
  obtain ⟨lV, _hlV, _hsepV, hvar⟩ :=
    smooth_remainder_variable_rate_both hrem d hd SD
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
  intro Q hQ lam h₀ h₁ P K hK hDnonzero F G hF hG hFp hGp t μ hμ
  have hmom : (∫⁻ ωz, if regenerationTime hd lam l 1 ωz.2 = ⊤ then ⊤ else
      ENNReal.ofReal (Real.exp (a * lam ^ 2 *
        (regenerationTime hd lam l 1 ωz.2).toReal)) ∂μ) ≤ ENNReal.ofReal B := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hμ
    rcases hμ with rfl | rfl
    · exact ((hdata Q hQ lam h₀ h₁ P K hK hDnonzero).2.2 1).trans
        (ENNReal.ofReal_le_ofReal (by
          simpa only [pow_one] using
            (le_max_right M (C₁ * M)).trans (le_max_right 1 (max M (C₁ * M)))))
    · exact ((hdata Q hQ lam h₀ h₁ P K hK hDnonzero).2.1 1).trans
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
  have hout := hvar' Q hQ lam h₀ h₁ l δ ((le_max_right _ _).trans hl) hδ₀ hδ₁
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

theorem fixed_observations_of_smooth_inputs
    (hren : SbxCRenewalR01.renewalSmoothStmt)
    (hrem : node_rt_u3A_remainder_u2D_momentStmtV3)
    (hrec : fixedRecurrencesSmoothStmt) :
    ∀ (d : ℕ) (hd : 2 ≤ d) (SD : StructuralData d),
    ∃ l₀ : ℝ, 0 < l₀ ∧ SD.dependenceRange < 2 * l₀ ∧
    ∀ l : ℝ, l₀ ≤ l → ∀ δ : ℝ, 0 < δ → δ < 1 →
    ∃ p c C : ℝ, 2 ≤ p ∧ 0 < c ∧ 0 < C ∧
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
    (∫ ω, F ω ∂reducedLaw Q) = 0 →
    let μ := Regeneration.annealedCoupledLaw Q.measure K
    let ν := regenerationConditionedLaw hd Q lam l K hK.1 hD
    let Δ := Regeneration.Renewal.regenDelta lam
    let pn := regenerationLatticeMass hd Q lam l K hK.1 hD
    let m := ∑' n : ℕ, (n : ℝ) * pn n
    let h := fun t : ℝ≥0 => ∫ ωz, G (translate (ωz.2.1 t) (reduce ωz.1)) ∂ν
    let r := fun t : ℝ≥0 => ∫ ωz in {ωz | (t : ℝ≥0∞) <
      regenerationTime hd lam l 1 ωz.2}, G (translate (ωz.2.1 t) (reduce ωz.1)) ∂ν
    let hF := fun t : ℝ≥0 => ∫ ωz, F (reduce ωz.1) *
      G (translate (ωz.2.1 t) (reduce ωz.1)) ∂μ
    let rF := fun t : ℝ≥0 => ∫ ωz in {ωz | (t : ℝ≥0∞) <
      regenerationTime hd lam l 1 ωz.2}, F (reduce ωz.1) *
        G (translate (ωz.2.1 t) (reduce ωz.1)) ∂μ
    let q := fun n : ℕ => ∫ ωz in {ωz | regenerationTime hd lam l 1 ωz.2 =
      (((n : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞)}, F (reduce ωz.1) ∂μ
    let Nf := (eLpNorm F (ENNReal.ofReal p) (reducedLaw Q)).toReal
    let Ng := (eLpNorm G (ENNReal.ofReal p) (reducedLaw Q)).toReal
    let H := fun s : ℝ≥0 => m⁻¹ * ∑' j : ℕ, r (s + j * Δ)
    Summable q ∧ (∑' n, q n) = 0 ∧
    (∀ n : ℕ, |q n| ≤ C * Real.exp (-c * n) *
      (eLpNorm F 2 (reducedLaw Q)).toReal) ∧
    (∀ t : ℝ≥0, |r t| ≤ C * Real.exp (-c * lam ^ 2 * (t : ℝ)) * Ng ∧
      |rF t| ≤ C * Real.exp (-c * lam ^ 2 * (t : ℝ)) * Nf * Ng) ∧
    ∀ s : ℝ≥0, s < Δ →
      Summable (fun j : ℕ => r (s + j * Δ)) ∧ |H s| ≤ C * Ng ∧
      ∀ k : ℕ,
        h (s + k * Δ) = r (s + k * Δ) +
          ∑ n ∈ Finset.range (k + 1), pn n * h (s + (k - n) * Δ) ∧
        hF (s + k * Δ) = rF (s + k * Δ) +
          ∑ n ∈ Finset.range (k + 1), q n * h (s + (k - n) * Δ) ∧
        |h (s + k * Δ) - H s| ≤ C * Real.exp (-c * k) * Ng ∧
        hF (s + k * Δ) = rF (s + k * Δ) +
          (∑ n ∈ Finset.range (k + 1), q n * (h (s + (k - n) * Δ) - H s)) -
          H s * ∑' n : ℕ, q (k + 1 + n) ∧
        |hF (s + k * Δ)| ≤ C * Real.exp (-c * k) * Nf * Ng := by
  intro d hd SD
  obtain ⟨lS, hlS, hsepS, hscalar⟩ := local_scalar_of_renewal hren d hd SD
  obtain ⟨lQ, _hlQ, _hsepQ, hslices⟩ :=
    local_centered_slices_of_renewal hren d hd SD
  obtain ⟨lR, _hlR, _hsepR, hremainder⟩ :=
    local_first_cycle_remainders hren hrem d hd SD
  obtain ⟨lI, pI, _hlI, _hsepI, hpI, hrecurrence⟩ :=
    hrec d hd SD
  have hleS : lS ≤ max (max lS lQ) (max lR lI) :=
    (le_max_left _ _).trans (le_max_left _ _)
  refine ⟨max (max lS lQ) (max lR lI), hlS.trans_le hleS,
    hsepS.trans_le (by linarith only [hleS]), ?_⟩
  intro l hl δ hδ₀ hδ₁
  have hls : lS ≤ l := (le_max_left _ _).trans ((le_max_left _ _).trans hl)
  have hlq : lQ ≤ l := (le_max_right _ _).trans ((le_max_left _ _).trans hl)
  have hlr : lR ≤ l := (le_max_left _ _).trans ((le_max_right _ _).trans hl)
  have hli : lI ≤ l := (le_max_right _ _).trans ((le_max_right _ _).trans hl)
  obtain ⟨cQ, CQ, hcQ, hCQ, hqdata⟩ := hslices l hlq δ hδ₀ hδ₁
  obtain ⟨pR, cR, CR, hpR, hcR, hCR, hrdata⟩ := hremainder l hlr δ hδ₀ hδ₁
  let p := max pR pI
  let b := min cQ cR
  have hb : 0 < b := lt_min hcQ hcR
  obtain ⟨cA, CA, hcA, hCA, hscalar'⟩ := hscalar l hls δ hδ₀ hδ₁ b hb
  let c := min cQ (min cR cA)
  let C := 1 + CQ + CR + CA * CR + CA * (CR + CQ * CR)
  have hC : 0 < C := by dsimp only [C]; positivity
  have hprod : 0 < CA * CR := mul_pos hCA hCR
  have hall : 0 < CA * (CR + CQ * CR) := by positivity
  have hCq : CQ ≤ C := by dsimp only [C]; linarith only [hCR, hprod, hall]
  have hCr : CR ≤ C := by dsimp only [C]; linarith only [hCQ, hprod, hall]
  have hCa : CA * CR ≤ C := by dsimp only [C]; linarith only [hCQ, hCR, hall]
  have hCf : CA * (CR + CQ * CR) ≤ C := by dsimp only [C]; linarith only [hCQ, hCR, hprod]
  have hcq : c ≤ cQ := min_le_left _ _
  have hcr : c ≤ cR := (min_le_right _ _).trans (min_le_left _ _)
  have hca : c ≤ cA := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨p, c, C, hpR.trans (le_max_left _ _), lt_min hcQ (lt_min hcR hcA), hC, ?_⟩
  intro Q hQ lam h₀ h₁ P K hK hD F G hF hG hFp hGp hzero
  let := reducedLaw_probability Q
  let μ := Regeneration.annealedCoupledLaw Q.measure K
  let ν := regenerationConditionedLaw hd Q lam l K hK.1 hD
  let Δ := Regeneration.Renewal.regenDelta lam
  let pn := regenerationLatticeMass hd Q lam l K hK.1 hD
  let m := ∑' n : ℕ, (n : ℝ) * pn n
  let h := fun t : ℝ≥0 => ∫ ωz, G (translate (ωz.2.1 t) (reduce ωz.1)) ∂ν
  let r := fun t : ℝ≥0 => ∫ ωz in {ωz | (t : ℝ≥0∞) <
    regenerationTime hd lam l 1 ωz.2}, G (translate (ωz.2.1 t) (reduce ωz.1)) ∂ν
  let hF' := fun t : ℝ≥0 => ∫ ωz, F (reduce ωz.1) *
    G (translate (ωz.2.1 t) (reduce ωz.1)) ∂μ
  let rF := fun t : ℝ≥0 => ∫ ωz in {ωz | (t : ℝ≥0∞) <
    regenerationTime hd lam l 1 ωz.2}, F (reduce ωz.1) *
      G (translate (ωz.2.1 t) (reduce ωz.1)) ∂μ
  let q := fun n : ℕ => ∫ ωz in {ωz | regenerationTime hd lam l 1 ωz.2 =
    (((n : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞)}, F (reduce ωz.1) ∂μ
  let Nf := (eLpNorm F (ENNReal.ofReal p) (reducedLaw Q)).toReal
  let Ng := (eLpNorm G (ENNReal.ofReal p) (reducedLaw Q)).toReal
  let H := fun s : ℝ≥0 => m⁻¹ * ∑' j : ℕ, r (s + j * Δ)
  change Summable q ∧ (∑' n, q n) = 0 ∧
    (∀ n : ℕ, |q n| ≤ C * Real.exp (-c * n) *
      (eLpNorm F 2 (reducedLaw Q)).toReal) ∧
    (∀ t : ℝ≥0, |r t| ≤ C * Real.exp (-c * lam ^ 2 * (t : ℝ)) * Ng ∧
      |rF t| ≤ C * Real.exp (-c * lam ^ 2 * (t : ℝ)) * Nf * Ng) ∧
    ∀ s : ℝ≥0, s < Δ → Summable (fun j : ℕ => r (s + j * Δ)) ∧
      |H s| ≤ C * Ng ∧ ∀ k : ℕ,
      h (s + k * Δ) = r (s + k * Δ) +
        ∑ n ∈ Finset.range (k + 1), pn n * h (s + (k - n) * Δ) ∧
      hF' (s + k * Δ) = rF (s + k * Δ) +
        ∑ n ∈ Finset.range (k + 1), q n * h (s + (k - n) * Δ) ∧
      |h (s + k * Δ) - H s| ≤ C * Real.exp (-c * k) * Ng ∧
      hF' (s + k * Δ) = rF (s + k * Δ) +
        (∑ n ∈ Finset.range (k + 1), q n * (h (s + (k - n) * Δ) - H s)) -
        H s * ∑' n : ℕ, q (k + 1 + n) ∧
      |hF' (s + k * Δ)| ≤ C * Real.exp (-c * k) * Nf * Ng
  have hFg := hF.mono (Probability.localSigma_le_borel _) le_rfl
  have hGg := hG.mono (Probability.localSigma_le_borel _) le_rfl
  have hpR' : ENNReal.ofReal pR ≤ ENNReal.ofReal p :=
    ENNReal.ofReal_le_ofReal (le_max_left _ _)
  have hpI' : ENNReal.ofReal pI ≤ ENNReal.ofReal p :=
    ENNReal.ofReal_le_ofReal (le_max_right _ _)
  have hnfR : (eLpNorm F (ENNReal.ofReal pR) (reducedLaw Q)).toReal ≤ Nf :=
    ENNReal.toReal_mono hFp.eLpNorm_ne_top (eLpNorm_le_eLpNorm_of_exponent_le hpR')
  have hngR : (eLpNorm G (ENNReal.ofReal pR) (reducedLaw Q)).toReal ≤ Ng :=
    ENNReal.toReal_mono hGp.eLpNorm_ne_top (eLpNorm_le_eLpNorm_of_exponent_le hpR')
  have hnf2 : (eLpNorm F 2 (reducedLaw Q)).toReal ≤ Nf :=
    ENNReal.toReal_mono hFp.eLpNorm_ne_top (eLpNorm_le_eLpNorm_of_exponent_le (by
      simpa only [ENNReal.ofReal_ofNat] using
        ENNReal.ofReal_le_ofReal (hpR.trans (le_max_left pR pI))))
  have hNf : 0 ≤ Nf := ENNReal.toReal_nonneg
  have hNg : 0 ≤ Ng := ENNReal.toReal_nonneg
  have hone : eLpNorm (fun _ : FieldPair d => (1 : ℝ))
      (ENNReal.ofReal pR) (reducedLaw Q) = 1 := by
    rw [eLpNorm_const' 1 (ne_of_gt (ENNReal.ofReal_pos.mpr (by linarith)))
      ENNReal.ofReal_ne_top]
    simp
  have hr (t : ℝ≥0) : |r t| ≤ CR * Real.exp (-cR * lam ^ 2 * (t : ℝ)) * Ng := by
    have hbnd := (hrdata Q hQ lam h₀ h₁ P K hK hD (fun _ => 1) G measurable_const hGg
      (memLp_const 1) (hGp.mono_exponent hpR') t ν (by simp [ν])).2
    simp only [one_mul, hone, ENNReal.toReal_one, mul_one] at hbnd
    exact hbnd.trans (mul_le_mul_of_nonneg_left hngR (by positivity))
  have hrF (t : ℝ≥0) : |rF t| ≤ CR * Real.exp (-cR * lam ^ 2 * (t : ℝ)) * Nf * Ng := by
    have hbnd := (hrdata Q hQ lam h₀ h₁ P K hK hD F G hFg hGg
      (hFp.mono_exponent hpR') (hGp.mono_exponent hpR') t μ (by simp [μ])).2
    apply hbnd.trans
    apply mul_le_mul _ hngR ENNReal.toReal_nonneg (by positivity)
    exact mul_le_mul_of_nonneg_left hnfR (by positivity)
  obtain ⟨hqs, hqzero, hqdec⟩ := hqdata Q hQ lam h₀ h₁ P K hK hD p
    (hpR.trans (le_max_left _ _)) F hFg hFp hzero
  have hrec := hrecurrence l δ hli hδ₀ hδ₁ Q hQ lam h₀ h₁ P K hK hD F G hF hG
    (hFp.mono_exponent hpI') (hGp.mono_exponent hpI')
  have hΔ : lam ^ 2 * (Δ : ℝ) = 1 := by
    dsimp only [Δ, Regeneration.Renewal.regenDelta]
    rw [Real.coe_toNNReal _ (inv_nonneg.mpr (sq_nonneg lam))]
    exact mul_inv_cancel₀ (pow_ne_zero 2 h₀.ne')
  have hsub (j n : ℕ) : ((j - n : ℕ) : ℝ≥0) = (j : ℝ≥0) - (n : ℝ≥0) := by
    rcases le_total n j with hnj | hjn
    · apply NNReal.coe_injective
      rw [NNReal.coe_sub (Nat.cast_le.mpr hnj)]
      simpa only [NNReal.coe_natCast] using (Nat.cast_sub hnj : ((j - n : ℕ) : ℝ) = j - n)
    · rw [Nat.sub_eq_zero_of_le hjn, Nat.cast_zero,
        tsub_eq_zero_of_le (Nat.cast_le.mpr hjn)]
  refine ⟨hqs, hqzero, ?_, ?_, ?_⟩
  · intro n
    exact (hqdec n).trans (sbxS4_decay_mono CQ C cQ c n _ hCQ.le hCq hcq
      (Nat.cast_nonneg n) ENNReal.toReal_nonneg)
  · intro t
    constructor
    · apply (hr t).trans
      simpa only [mul_assoc] using sbxS4_decay_mono CR C cR c (lam ^ 2 * (t : ℝ)) Ng
        hCR.le hCr hcr (by positivity) hNg
    · apply (hrF t).trans
      simpa only [mul_assoc] using sbxS4_decay_mono CR C cR c (lam ^ 2 * (t : ℝ))
        (Nf * Ng) hCR.le hCr hcr (by positivity) (mul_nonneg hNf hNg)
  · intro s hs
    have hrphase (j : ℕ) : |r (s + j * Δ)| ≤ (CR * Ng) * Real.exp (-b * j) := by
      have hbnd := phase_remainder_bound r CR cR lam Ng 0 hCR.le hcR.le hNg Δ hΔ
        (by simpa only [Nat.cast_zero, mul_zero, zero_sub, neg_mul] using hr) s j
      simp only [Nat.cast_zero, mul_zero, zero_sub] at hbnd
      apply hbnd.trans
      have hh := sbxS4_decay_mono CR CR cR b j Ng hCR.le le_rfl (min_le_right _ _)
        (Nat.cast_nonneg j) hNg
      simpa only [neg_mul, mul_neg, mul_comm, mul_left_comm, mul_assoc] using hh
    have hrFphase (j : ℕ) :
        |rF (s + j * Δ)| ≤ (CR * Nf * Ng) * Real.exp (-b * j) := by
      have hbnd := phase_remainder_bound rF CR cR lam (Nf * Ng) 0 hCR.le hcR.le
        (mul_nonneg hNf hNg) Δ hΔ
        (by simpa only [Nat.cast_zero, mul_zero, zero_sub, neg_mul, mul_assoc] using hrF) s j
      simp only [Nat.cast_zero, mul_zero, zero_sub] at hbnd
      apply hbnd.trans
      have hh := sbxS4_decay_mono CR CR cR b j (Nf * Ng) hCR.le le_rfl
        (min_le_right _ _) (Nat.cast_nonneg j) (mul_nonneg hNf hNg)
      simpa only [neg_mul, mul_neg, mul_comm, mul_left_comm, mul_assoc] using hh
    have hqphase (n : ℕ) : |q n| ≤ (CQ * Nf) * Real.exp (-b * n) := by
      apply (hqdec n).trans
      have hh := sbxS4_decay_mono CQ CQ cQ b n
        (eLpNorm F 2 (reducedLaw Q)).toReal hCQ.le le_rfl (min_le_left _ _)
        (Nat.cast_nonneg n) ENNReal.toReal_nonneg
      apply hh.trans
      have hn := mul_le_mul_of_nonneg_left hnf2
        (mul_nonneg hCQ.le (Real.exp_pos (-b * n)).le)
      simpa only [neg_mul, mul_neg, mul_comm, mul_left_comm, mul_assoc] using hn
    obtain ⟨hrs, hH, hbounds⟩ := hscalar' Q hQ lam h₀ h₁ P K hK hD s hs
      (fun j => h (s + j * Δ)) (fun j => r (s + j * Δ))
      (fun j => hF' (s + j * Δ)) (fun j => rF (s + j * Δ)) q
      (CR * Ng) (CR * Nf * Ng) (CQ * Nf) (by positivity) (by positivity) (by positivity)
      (by intro j; simpa only [hsub] using (hrec s hs j).1)
      (by intro j; simpa only [hsub] using (hrec s hs j).2)
      hrphase hrFphase hqphase hqs hqzero
    refine ⟨hrs, ?_, ?_⟩
    · exact hH.trans (by simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_right hCa hNg)
    · intro k
      obtain ⟨hdec, hidentity, hcov⟩ := hbounds k
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · simpa only [hsub] using (hrec s hs k).1
      · simpa only [hsub] using (hrec s hs k).2
      · apply hdec.trans
        have hh := sbxS4_decay_mono (CA * CR) C cA c k Ng (by positivity)
          hCa hca (Nat.cast_nonneg k) hNg
        simpa only [neg_mul, mul_neg, mul_comm, mul_left_comm, mul_assoc] using hh
      · simpa only [hsub] using hidentity
      · apply hcov.trans
        have he : CA * (CR * Nf * Ng + CQ * Nf * (CR * Ng)) =
            (CA * (CR + CQ * CR)) * (Nf * Ng) := by ring
        rw [he]
        have hh := sbxS4_decay_mono (CA * (CR + CQ * CR)) C cA c k
          (Nf * Ng) (by positivity) hCf hca (Nat.cast_nonneg k) (mul_nonneg hNf hNg)
        simpa only [neg_mul, mul_neg, mul_comm, mul_left_comm, mul_assoc] using hh


end EinsteinFull.Blueprint.SbxS6Section3R01
