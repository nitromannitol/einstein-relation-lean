import EinsteinFull.Blueprint.G1.Proofs.SbxS9PhaseError
import EinsteinFull.Blueprint.Roots.Draft.SbxCRenewalUniformR06

/-! Conditional uniform phase assembly, draft only. -/
open MeasureTheory
open scoped NNReal ENNReal Topology
namespace EinsteinFull.Blueprint.SbxCPhaseUniformR07
open EinsteinRelation EinsteinFull.Blueprint

def recurrenceUniformStmt : Prop :=
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
      ∑ n ∈ Finset.range (⌊(t : ℝ) / (Δ : ℝ)⌋₊ + 1), pn n * h (t - n * Δ)

def cycleUniformStmt : Prop :=
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
          (eLpNorm G (ENNReal.ofReal p) (reducedLaw Q)).toReal

def phaseUniformStmt : Prop :=
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
    ∀ (A : ℝ) (m : ℕ), l ≤ A → 1 ≤ m → 10 * (m : ℝ) * l - l - A ≥ -2 * l →
    ∀ G : FieldPair d → ℝ,
    Measurable[localSigma {x : Vec d | euclideanNorm x < A / lam}] G →
    MemLp G (ENNReal.ofReal p) (reducedLaw Q) →
    let ν := regenerationConditionedLaw hd Q lam l K hK.1 hD
    let Δ := Regeneration.Renewal.regenDelta lam
    let pn := regenerationLatticeMass hd Q lam l K hK.1 hD
    let mean := ∑' n : ℕ, (n : ℝ) * pn n
    let hm := fun t : ℝ≥0 => ∫ ωz in {ωz |
      regenerationTime hd lam l m ωz.2 ≤ (t : ℝ≥0∞)},
      G (translate (ωz.2.1 t) (reduce ωz.1)) ∂ν
    let rm := fun t : ℝ≥0 => ∫ ωz in {ωz |
      regenerationTime hd lam l m ωz.2 ≤ (t : ℝ≥0∞) ∧
      (t : ℝ≥0∞) < regenerationTime hd lam l (m + 1) ωz.2},
      G (translate (ωz.2.1 t) (reduce ωz.1)) ∂ν
    let Ng := (eLpNorm G (ENNReal.ofReal p) (reducedLaw Q)).toReal
    let Hm := fun s : ℝ≥0 => mean⁻¹ * ∑' j : ℕ, rm (s + j * Δ)
    (∀ t : ℝ≥0, |rm t| ≤ C * Real.exp (C * m - c * lam ^ 2 * (t : ℝ)) * Ng) ∧
    ∀ s : ℝ≥0, s < Δ →
      Summable (fun j : ℕ => rm (s + j * Δ)) ∧
      |Hm s| ≤ C * Real.exp (C * m) * Ng ∧
      ∀ j : ℕ,
        hm (s + j * Δ) = rm (s + j * Δ) +
          ∑ n ∈ Finset.range (j + 1), pn n * hm (s + (j - n) * Δ) ∧
        hm (s + j * Δ) - Hm s =
          (∑ n ∈ Finset.range (j + 1),
            ((∑' a : ℕ, EinsteinFull.latticeConvolutionPower pn a (j - n)) - mean⁻¹) *
              rm (s + n * Δ)) - mean⁻¹ * ∑' n : ℕ, rm (s + (j + 1 + n) * Δ) ∧
        |hm (s + j * Δ) - Hm s| ≤ C * Real.exp (C * m - c * j) * Ng


theorem phase_of_uniform_deps
    (hmren : recurrenceUniformStmt) (hcycleInput : cycleUniformStmt)
    (hren : SbxCRenewalUniformR06.renewalUniformStmt) : phaseUniformStmt := by
  intro d hd Λ₀ r₀ hΛ hr
  obtain ⟨L₀, p₀, hL₀, hsep₀, hp₀, hrenew⟩ :=
    hmren d hd Λ₀ r₀ hΛ hr
  obtain ⟨L₁, _hL₁, _hsep₁, hcycle⟩ :=
    hcycleInput d hd Λ₀ r₀ hΛ hr
  obtain ⟨L₂, _hL₂, _hsep₂, hren'⟩ := hren d hd Λ₀ r₀ hΛ hr
  refine ⟨max L₀ (max L₁ L₂),
    hL₀.trans_le (le_max_left _ _),
    hsep₀.trans_le (by linarith only [le_max_left L₀ (max L₁ L₂)]),
    ?_⟩
  intro l hl δ hδ₀ hδ₁
  have hl₀ : L₀ ≤ l := (le_max_left _ _).trans hl
  have hl₁ : L₁ ≤ l := (le_max_left _ _).trans ((le_max_right _ _).trans hl)
  have hl₂ : L₂ ≤ l := (le_max_right _ _).trans ((le_max_right _ _).trans hl)
  obtain ⟨c₁, C₁, _a, _M, hc₁, hC₁, _ha, _hM, hren''⟩ :=
    hren' l hl₂ δ hδ₀ hδ₁
  obtain ⟨p₁, c₀, C₀, _hp₁, hc₀, hC₀, hcycle'⟩ :=
    hcycle l hl₁ δ hδ₀ hδ₁
  obtain ⟨c, D, hc, hDpos, hest⟩ :=
    renewal_phase_error_on_lattice_uniform C₁ c₁ c₀ C₀ hC₁ hc₁ hc₀ hC₀
  let C := max C₀ D
  have hC₀C : C₀ ≤ C := le_max_left _ _
  have hDC : D ≤ C := le_max_right _ _
  have hC : 0 < C := hC₀.trans_le hC₀C
  refine ⟨max p₀ p₁, min c c₀, C, hp₀.trans (le_max_left _ _),
    lt_min hc hc₀, hC, ?_⟩
  intro β hβ SD Q hQ lam h₀ h₁ P K hK hD A m _hA hmpos hsupp G hG hLp
  let : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  have hLp₀ : MemLp G (ENNReal.ofReal p₀) (reducedLaw Q) :=
    hLp.mono_exponent (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  have hLp₁ : MemLp G (ENNReal.ofReal p₁) (reducedLaw Q) :=
    hLp.mono_exponent (ENNReal.ofReal_le_ofReal (le_max_right _ _))
  let Ng := (eLpNorm G (ENNReal.ofReal (max p₀ p₁)) (reducedLaw Q)).toReal
  have hNg : (eLpNorm G (ENNReal.ofReal p₁) (reducedLaw Q)).toReal ≤ Ng :=
    ENNReal.toReal_mono hLp.eLpNorm_ne_top
      (eLpNorm_le_eLpNorm_of_exponent_le
        (ENNReal.ofReal_le_ofReal (le_max_right _ _)))
  let ν := regenerationConditionedLaw hd Q lam l K hK.1 hD
  let Δ := Regeneration.Renewal.regenDelta lam
  let pn := regenerationLatticeMass hd Q lam l K hK.1 hD
  let mean := ∑' n : ℕ, (n : ℝ) * pn n
  let hm := fun t : ℝ≥0 => ∫ ωz in {ωz |
    regenerationTime hd lam l m ωz.2 ≤ (t : ℝ≥0∞)},
    G (translate (ωz.2.1 t) (reduce ωz.1)) ∂ν
  let rm := fun t : ℝ≥0 => ∫ ωz in {ωz |
    regenerationTime hd lam l m ωz.2 ≤ (t : ℝ≥0∞) ∧
    (t : ℝ≥0∞) < regenerationTime hd lam l (m + 1) ωz.2},
    G (translate (ωz.2.1 t) (reduce ωz.1)) ∂ν
  have hactual := hren'' β hβ Q hQ lam h₀ h₁ P K hK hD
  have hU : ∀ n : ℕ, |(∑' a : ℕ, latticeConvolutionPower pn a n) - mean⁻¹| ≤
      C₁ * Real.exp (-c₁ * n) := by
    simpa only [pn, mean, mul_comm] using hactual.1
  have hp : pn 0 = 0 :=
    regenerationLatticeMass_zero hd Q lam l h₀ (hL₀.trans_le hl₀) K hK.1 hD
  have hΔ : lam ^ 2 * (Δ : ℝ) = 1 := by
    dsimp only [Δ, Regeneration.Renewal.regenDelta]
    rw [Real.coe_toNNReal _ (inv_nonneg.mpr (sq_nonneg lam))]
    exact mul_inv_cancel₀ (pow_ne_zero 2 h₀.ne')
  have hr : ∀ t : ℝ≥0, |rm t| ≤
      C₀ * Real.exp (C₀ * m - c₀ * lam ^ 2 * (t : ℝ)) * Ng := by
    intro t
    have hbnd := hcycle' β hβ Q hQ lam h₀ h₁ P K hK hD
      m G (hG.mono (Probability.localSigma_le_borel _) le_rfl) hLp₁ t
    exact hbnd.trans (mul_le_mul_of_nonneg_left hNg
      (mul_nonneg hC₀.le (Real.exp_pos _).le))
  have hh : ∀ t : ℝ≥0, hm t = rm t +
      ∑ n ∈ Finset.range (⌊(t : ℝ) / (Δ : ℝ)⌋₊ + 1), pn n * hm (t - n * Δ) :=
    hrenew β hβ Q hQ lam h₀ h₁ l δ hl₀ hδ₀ hδ₁ P K hK hD A m hmpos hsupp G hG hLp₀
  dsimp only
  refine ⟨?_, ?_⟩
  · intro t
    apply (hr t).trans
    apply mul_le_mul_of_nonneg_right _ ENNReal.toReal_nonneg
    apply mul_le_mul hC₀C _ (Real.exp_pos _).le hC.le
    apply Real.exp_le_exp.mpr
    have hcm := mul_le_mul_of_nonneg_right hC₀C (Nat.cast_nonneg m)
    have hrate := mul_le_mul_of_nonneg_right (min_le_right c c₀)
      (mul_nonneg (sq_nonneg lam) t.coe_nonneg)
    nlinarith only [hcm, hrate]
  · intro s hs
    obtain ⟨hrs, hlim, herr⟩ := hest pn mean hp hU lam Δ hΔ m Ng
      ENNReal.toReal_nonneg hm rm hr hh s hs
    refine ⟨hrs, ?_, ?_⟩
    · apply hlim.trans
      apply mul_le_mul_of_nonneg_right _ ENNReal.toReal_nonneg
      exact mul_le_mul hDC (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_right hDC (Nat.cast_nonneg m))) (Real.exp_pos _).le hC.le
    · intro j
      obtain ⟨hrec, hid, herror⟩ := herr j
      refine ⟨?_, ?_, herror.trans ?_⟩
      · change hm (s + j * Δ) = rm (s + j * Δ) +
          ∑ n ∈ Finset.range (j + 1), pn n * hm (s + ((j : ℝ≥0) - n) * Δ)
        rw [hrec]
        congr 1
        apply Finset.sum_congr rfl
        intro n _hn
        rw [Nat.cast_tsub]
      · simpa only [Nat.cast_add, Nat.cast_one] using hid
      · apply mul_le_mul_of_nonneg_right _ ENNReal.toReal_nonneg
        apply mul_le_mul hDC _ (Real.exp_pos _).le hC.le
        apply Real.exp_le_exp.mpr
        have hcm := mul_le_mul_of_nonneg_right hDC (Nat.cast_nonneg m)
        have hrate := mul_le_mul_of_nonneg_right (min_le_left c c₀) (Nat.cast_nonneg j)
        linarith only [hcm, hrate]


end EinsteinFull.Blueprint.SbxCPhaseUniformR07
