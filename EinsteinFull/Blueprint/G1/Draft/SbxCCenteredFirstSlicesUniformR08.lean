import EinsteinFull.Blueprint.G1.Draft.SbxCKMCenteredSlicesSmoothR01
import EinsteinFull.Blueprint.Roots.Draft.SbxCRenewalUniformR06

/-! Conditional uniform centered first-cycle slices; not reviewed or adopted. -/
open MeasureTheory
open scoped NNReal ENNReal Topology
namespace EinsteinFull.Blueprint.SbxCCenteredFirstSlicesUniformR08
open EinsteinRelation EinsteinFull.Blueprint EinsteinFull.Work.W5

def centeredFirstSlicesUniformStmt : Prop :=
    ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ) (hΛ : 1 ≤ Λ₀) (hr : 1 ≤ r₀),
    ∃ l₀ : ℝ, 0 < l₀ ∧ r₀ < 2 * l₀ ∧
    ∀ l : ℝ, l₀ ≤ l → ∀ δ : ℝ, 0 < δ → δ < 1 →
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    ∀ (β : ℕ → ℝ) (hβ : ∀ k, 1 ≤ k → 0 < β k),
    let SD : StructuralData d := ⟨Λ₀, r₀, β, hΛ, hr, hβ⟩
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
        (eLpNorm F 2 (reducedLaw Q)).toReal

theorem centeredFirstSlicesUniform_of_renewal
    (hren : SbxCRenewalUniformR06.renewalUniformStmt) :
    centeredFirstSlicesUniformStmt := by
  intro d hd Λ₀ r₀ hΛ hr
  obtain ⟨l₀, hl₀, hsep, hren⟩ := hren d hd Λ₀ r₀ hΛ hr
  refine ⟨l₀, hl₀, hsep, ?_⟩
  intro l hl δ hδ₀ hδ₁
  obtain ⟨c, C, a, M, hc, hC, ha, hM, hdata⟩ := hren l hl δ hδ₀ hδ₁
  refine ⟨a / 2, Real.exp (C * M / 2), half_pos ha, Real.exp_pos _, ?_⟩
  intro β hβ SD Q hQ lam h₀ h₁ P K hK hD p hp F hF hFp hzero
  let := reducedLaw_probability Q
  have hp2 : (2 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    simpa only [ENNReal.ofReal_ofNat] using ENNReal.ofReal_le_ofReal hp
  have hFn : MemLp F 2 (reducedLaw Q) := by
    simpa only [ENNReal.ofReal_ofNat] using hFp.mono_exponent hp2
  have hm : (∫⁻ ωz, regenerationExponentialWeight hd lam l a 1 ωz.2
      ∂Regeneration.annealedCoupledLaw Q.measure K) ≤ ENNReal.ofReal (C * M) := by
    simpa only [regenerationExponentialWeight, pow_one] using
      (hdata β hβ Q hQ lam h₀ h₁ P K hK hD).2.2 1
  have hmfin : (∫⁻ ωz, regenerationExponentialWeight hd lam l a 1 ωz.2
      ∂Regeneration.annealedCoupledLaw Q.measure K) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hm
  have hq := sbxS2_centered_regenerationSlice_hasSum hd Q lam l a h₀.ne' K hK.1 1
    hmfin F hF (hFp.integrable (by
      simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal
        ((by norm_num : (1 : ℝ) ≤ 2).trans hp))) hzero
  refine ⟨hq.summable, hq.tsum_eq, ?_⟩
  intro n
  have hCexp : C * M ≤ Real.exp (C * M) := by
    linarith only [Real.add_one_le_exp (C * M)]
  have hmexp := hm.trans (ENNReal.ofReal_le_ofReal hCexp)
  have hbound := sbxS2_regenerationSlice_abs_le hd Q lam l a (C * M) h₀.ne' K hK.1
    1 n F hF hFn (by simpa only [Nat.cast_one, mul_one] using hmexp)
  have hexp : Real.exp ((C * M * (1 : ℕ) - a * n) / 2) =
      Real.exp (C * M / 2) * Real.exp (-(a / 2) * n) := by
    rw [← Real.exp_add]
    congr 1
    push_cast
    ring
  simpa only [ENNReal.ofReal_ofNat, hexp] using hbound

end EinsteinFull.Blueprint.SbxCCenteredFirstSlicesUniformR08
