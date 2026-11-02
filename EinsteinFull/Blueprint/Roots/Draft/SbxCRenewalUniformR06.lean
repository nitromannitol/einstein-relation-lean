import EinsteinFull.Blueprint.G1.Draft.SbxCRenewalSmoothR01

/-! Draft uniform-witness renewal contracts and conditional assembly. -/
open MeasureTheory
open scoped NNReal ENNReal

namespace EinsteinFull.Blueprint.SbxCRenewalUniformR06
open EinsteinRelation EinsteinFull.Work.W5

def cauchyUniformStmt : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ) (hΛ : 1 ≤ Λ₀) (hr : 1 ≤ r₀),
    ∃ l₀ : ℝ, 0 < l₀ ∧ r₀ < 2 * l₀ ∧
    ∀ l : ℝ, l₀ ≤ l → ∀ δ : ℝ, 0 < δ → δ < 1 →
    ∃ ρ B c C : ℝ, 0 < ρ ∧ 0 < B ∧ 0 < c ∧ 0 < C ∧
    ∀ (β : ℕ → ℝ) (hβ : ∀ k, 1 ≤ k → 0 < β k),
    let D : StructuralData d := ⟨Λ₀, r₀, β, hΛ, hr, hβ⟩
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (_hQ : HasSmoothBounds D Q) (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
      (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
      (hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K)
      (hD : Regeneration.annealedCoupledLaw Q.measure K
        (regenerationNoReturn hd (l / lam)) ≠ 0),
    let p := regenerationLatticeMass hd Q lam l K hK.1 hD
    let V := renewalRemovableDifference p
    AnalyticOnNhd ℂ V (Metric.closedBall 0 (1 + ρ)) ∧
    (∀ z : ℂ, ‖z‖ ≤ 1 + ρ → ‖V z‖ ≤ B) ∧
    (∀ z : ℂ, ‖z‖ ≤ 1 + ρ → z ≠ 1 →
      V z = (1 - renewalGenerating p z)⁻¹ -
        ((renewalMean p : ℂ) * (1 - z))⁻¹) ∧
    (∀ n : ℕ, |(∑' j : ℕ, latticeConvolutionPower p j n) -
      (renewalMean p)⁻¹| ≤ C * Real.exp (-c * n))


def manyCycleUniformStmt : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ) (hΛ : 1 ≤ Λ₀) (hr : 1 ≤ r₀),
    ∃ l₀ : ℝ, 0 < l₀ ∧ r₀ < 2 * l₀ ∧
    ∀ l : ℝ, l₀ ≤ l → ∀ δ : ℝ, 0 < δ → δ < 1 →
    ∃ a M C : ℝ, 0 < a ∧ 0 < M ∧ 0 < C ∧
    ∀ (β : ℕ → ℝ) (hβ : ∀ k, 1 ≤ k → 0 < β k),
    let D : StructuralData d := ⟨Λ₀, r₀, β, hΛ, hr, hβ⟩
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (_hQ : HasSmoothBounds D Q) (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
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


def renewalUniformStmt : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ) (hΛ : 1 ≤ Λ₀) (hr : 1 ≤ r₀),
    ∃ l₀ : ℝ, 0 < l₀ ∧ r₀ < 2 * l₀ ∧
    ∀ l : ℝ, l₀ ≤ l → ∀ δ : ℝ, 0 < δ → δ < 1 →
    ∃ c C a M : ℝ, 0 < c ∧ 0 < C ∧ 0 < a ∧ 0 < M ∧
    ∀ (β : ℕ → ℝ) (hβ : ∀ k, 1 ≤ k → 0 < β k),
    let D : StructuralData d := ⟨Λ₀, r₀, β, hΛ, hr, hβ⟩
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (_hQ : HasSmoothBounds D Q) (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
      (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d),
    ∀ hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K,
    ∀ hD : Regeneration.annealedCoupledLaw Q.measure K
      (regenerationNoReturn hd (l / lam)) ≠ 0,
      let p := regenerationLatticeMass hd Q lam l K hK.1 hD
      let m := ∑' n : ℕ, p n * (n : ℝ)
      (∀ n : ℕ, |(∑' j : ℕ, latticeConvolutionPower p j n) - m⁻¹| ≤
        C * Real.exp (-c * n)) ∧
      (∀ j : ℕ,
        (∫⁻ ωz, if regenerationTime hd lam l j ωz.2 = ⊤ then ⊤ else
          ENNReal.ofReal (Real.exp (a * lam ^ 2 *
            (regenerationTime hd lam l j ωz.2).toReal))
          ∂regenerationConditionedLaw hd Q lam l K hK.1 hD) ≤ ENNReal.ofReal (M ^ j)) ∧
      (∀ j : ℕ,
        (∫⁻ ωz, if regenerationTime hd lam l j ωz.2 = ⊤ then ⊤ else
          ENNReal.ofReal (Real.exp (a * lam ^ 2 *
            (regenerationTime hd lam l j ωz.2).toReal))
          ∂Regeneration.annealedCoupledLaw Q.measure K) ≤
            ENNReal.ofReal (C * M ^ j))


/-- Conditional assembly from the two uniform predecessors and the original
all-law coupling-parameter transfer proposition, in graph order. -/
theorem renewalUniform_of_deps
    (hcauchy : cauchyUniformStmt)
    (hmoments : manyCycleUniformStmt)
    (htransfer : node_rt_u3A_renewal_u23_coupling_u2D_parameter_u2D_transferStmt) :
    renewalUniformStmt := by
  intro d hd Λ₀ r₀ hΛ hr
  obtain ⟨lc, hlc, hrc, hc⟩ := hcauchy d hd Λ₀ r₀ hΛ hr
  obtain ⟨lm, _, _, hm⟩ := hmoments d hd Λ₀ r₀ hΛ hr
  obtain ⟨lt, _, _, _⟩ := htransfer d hd Λ₀ r₀
  refine ⟨max lc (max lm lt), hlc.trans_le (le_max_left _ _),
    hrc.trans_le (mul_le_mul_of_nonneg_left (le_max_left _ _) (by norm_num)), ?_⟩
  intro l hl δ hδ₀ hδ₁
  have hcl : lc ≤ l := (le_max_left _ _).trans hl
  have hml : lm ≤ l := ((le_max_left lm lt).trans (le_max_right lc _)).trans hl
  obtain ⟨ρ, B, c, Cc, _, _, hcpos, hCc, hcest⟩ := hc l hcl δ hδ₀ hδ₁
  obtain ⟨a, M, Cm, hapos, hM, hCm, hmest⟩ := hm l hml δ hδ₀ hδ₁
  refine ⟨c, max Cc Cm, a, M, hcpos, hCc.trans_le (le_max_left _ _),
    hapos, hM, ?_⟩
  intro β hβ D Q hQ lam h₀ h₁ P K hK hD
  obtain ⟨_, _, _, hdecay⟩ := hcest β hβ Q hQ lam h₀ h₁ P K hK hD
  obtain ⟨hconditioned, hannealed⟩ := hmest β hβ Q hQ lam h₀ h₁ P K hK hD
  refine ⟨?_, hconditioned, ?_⟩
  · intro n
    exact (hdecay n).trans
      (mul_le_mul_of_nonneg_right (le_max_left Cc Cm) (Real.exp_pos _).le)
  · intro j
    exact (hannealed j).trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (le_max_right Cc Cm) (pow_nonneg hM.le j)))

end EinsteinFull.Blueprint.SbxCRenewalUniformR06
