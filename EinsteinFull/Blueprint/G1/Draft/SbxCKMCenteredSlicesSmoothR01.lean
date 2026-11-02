import EinsteinFull.Blueprint.G1.Draft.S3SmoothScope
import EinsteinFull.Blueprint.G1.Proofs.SbxS2KmDecomp

/-! Conditional smooth-law centered regeneration slice estimates. -/
open MeasureTheory
open scoped NNReal ENNReal Topology
noncomputable section
namespace EinsteinFull.Blueprint.SbxCKMCenteredSlicesSmoothR01
open EinsteinRelation
open EinsteinFull.Work.W5

/-- The literal many-cycle moment statement restricted to smooth laws. -/
def centeredManyCycleSmoothStmt : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d),
    ∃ l₀ : ℝ, 0 < l₀ ∧ D.dependenceRange < 2 * l₀ ∧
    ∀ l : ℝ, l₀ ≤ l → ∀ δ : ℝ, 0 < δ → δ < 1 →
    ∃ a M C : ℝ, 0 < a ∧ 0 < M ∧ 0 < C ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (_hQ : HasSmoothBounds D Q) (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
      (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
      (hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K)
      (hD : Regeneration.annealedCoupledLaw Q.measure K
        (regenerationNoReturn hd (l / lam)) ≠ 0),
    (∀ j : ℕ,
      (∫⁻ ωz, regenerationExponentialWeight hd lam l a j ωz.2
        ∂regenerationConditionedLaw hd Q lam l K hK.1 hD) ≤ ENNReal.ofReal (M ^ j)) ∧
    (∀ j : ℕ,
      (∫⁻ ωz, regenerationExponentialWeight hd lam l a j ωz.2
        ∂Regeneration.annealedCoupledLaw Q.measure K) ≤ ENNReal.ofReal (C * M ^ j))


theorem smooth_centered_slices_of_manyCycleMoment
    (hmany : centeredManyCycleSmoothStmt)
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) :
    ∃ l₀ : ℝ, 0 < l₀ ∧ D.dependenceRange < 2 * l₀ ∧
    ∀ l : ℝ, l₀ ≤ l → ∀ δ : ℝ, 0 < δ → δ < 1 →
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (_hQ : HasSmoothBounds D Q) (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
      (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
      (_hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K)
      (_hD : Regeneration.annealedCoupledLaw Q.measure K
        (regenerationNoReturn hd (l / lam)) ≠ 0)
      (p : ℝ), 1 ≤ p → ∀ F : FieldPair d → ℝ,
    Measurable F → MemLp F (ENNReal.ofReal p) (reducedLaw Q) →
    (∫ ω, F ω ∂reducedLaw Q) = 0 → ∀ k : ℕ,
    let q := fun n : ℕ => ∫ ωz in {ωz | regenerationTime hd lam l k ωz.2 =
      (((n : ℝ≥0) * Regeneration.Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)},
      F (reduce ωz.1) ∂Regeneration.annealedCoupledLaw Q.measure K
    Summable q ∧ (∑' n, q n) = 0 := by
  obtain ⟨l₀, hl₀, hsep, hmom⟩ := hmany d hd D
  refine ⟨l₀, hl₀, hsep, ?_⟩
  intro l hl δ hδ₀ hδ₁
  obtain ⟨a, M, C, _ha, _hM, _hC, hm⟩ := hmom l hl δ hδ₀ hδ₁
  intro Q hQ lam h₀ h₁ P K hK hD p hp F hF hFp hzero k
  let := reducedLaw_probability Q
  have hmfin : (∫⁻ ωz, regenerationExponentialWeight hd lam l a k ωz.2
      ∂Regeneration.annealedCoupledLaw Q.measure K) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top ((hm Q hQ lam h₀ h₁ P K hK hD).2 k)
  have hq := sbxS2_centered_regenerationSlice_hasSum hd Q lam l a h₀.ne' K hK.1 k
    hmfin F hF (hFp.integrable (by simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp)) hzero
  exact ⟨hq.summable, hq.tsum_eq⟩

/-- The supplied many-cycle moment yields uniform decay of every nonzero-cycle
coefficient in any finite Lᵖ norm with `2 ≤ p`. -/
theorem smooth_slice_decay_of_manyCycleMoment
    (hmany : centeredManyCycleSmoothStmt)
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) :
    ∃ l₀ : ℝ, 0 < l₀ ∧ D.dependenceRange < 2 * l₀ ∧
    ∀ l : ℝ, l₀ ≤ l → ∀ δ : ℝ, 0 < δ → δ < 1 →
    ∃ a C : ℝ, 0 < a ∧ 0 < C ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (_hQ : HasSmoothBounds D Q) (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
      (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
      (_hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K)
      (_hD : Regeneration.annealedCoupledLaw Q.measure K
        (regenerationNoReturn hd (l / lam)) ≠ 0)
      (p : ℝ), 2 ≤ p → ∀ F : FieldPair d → ℝ,
    Measurable F → MemLp F (ENNReal.ofReal p) (reducedLaw Q) →
    ∀ k : ℕ, 1 ≤ k → ∀ n : ℕ,
    |∫ ωz in {ωz | regenerationTime hd lam l k ωz.2 =
      (((n : ℝ≥0) * Regeneration.Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)},
      F (reduce ωz.1) ∂Regeneration.annealedCoupledLaw Q.measure K| ≤
      Real.exp ((C * k - a * n) / 2) *
        (eLpNorm F (ENNReal.ofReal p) (reducedLaw Q)).toReal := by
  obtain ⟨l₀, hl₀, hsep, hmom⟩ := hmany d hd D
  refine ⟨l₀, hl₀, hsep, ?_⟩
  intro l hl δ hδ₀ hδ₁
  obtain ⟨a, M, C, ha, hM, hC, hm⟩ := hmom l hl δ hδ₀ hδ₁
  refine ⟨a, C + M, ha, add_pos hC hM, ?_⟩
  intro Q hQ lam h₀ h₁ P K hK hD p hp F hF hFp k hk n
  let := reducedLaw_probability Q
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hCexp : C ≤ Real.exp (C * k) := by
    have hself : C ≤ Real.exp C := by linarith only [Real.add_one_le_exp C]
    apply hself.trans
    apply Real.exp_le_exp.mpr
    nlinarith only [hC.le, hk']
  have hMexp : M ≤ Real.exp M := by linarith only [Real.add_one_le_exp M]
  have hgeom : C * M ^ k ≤ Real.exp ((C + M) * k) := by
    calc
      _ ≤ Real.exp (C * k) * Real.exp M ^ k :=
        mul_le_mul hCexp (pow_le_pow_left₀ hM.le hMexp k)
          (pow_nonneg hM.le k) (Real.exp_pos _).le
      _ = _ := by
        rw [← Real.exp_nat_mul, ← Real.exp_add]
        congr 1
        ring
  have hp' : (2 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    simpa using ENNReal.ofReal_le_ofReal hp
  have hq := sbxS2_regenerationSlice_abs_le hd Q lam l a (C + M) h₀.ne' K hK.1
    k n F hF (hFp.mono_exponent hp')
      (((hm Q hQ lam h₀ h₁ P K hK hD).2 k).trans (ENNReal.ofReal_le_ofReal hgeom))
  exact hq.trans (mul_le_mul_of_nonneg_left
    (ENNReal.toReal_mono hFp.eLpNorm_ne_top (eLpNorm_le_eLpNorm_of_exponent_le hp'))
      (Real.exp_pos _).le)


end EinsteinFull.Blueprint.SbxCKMCenteredSlicesSmoothR01
