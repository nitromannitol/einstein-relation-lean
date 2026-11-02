import EinsteinFull.Blueprint.G1.Draft.SbxCRenewalSmoothR01
import EinsteinFull.Blueprint.Roots.node_rt_u3A_renewal

/-! Draft smooth renewal statement and its conditional reduction. -/
open MeasureTheory
open scoped NNReal ENNReal

namespace EinsteinFull.Blueprint.SbxCRenewalR01
open EinsteinRelation EinsteinFull.Work.W5

def renewalSmoothStmt : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d),
    ∃ l₀ : ℝ, 0 < l₀ ∧ D.dependenceRange < 2 * l₀ ∧
    ∀ l : ℝ, l₀ ≤ l → ∀ δ : ℝ, 0 < δ → δ < 1 →
    ∃ c C a M : ℝ, 0 < c ∧ 0 < C ∧ 0 < a ∧ 0 < M ∧
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


/-- Assemble the smooth renewal estimate from its three ordered predecessors. -/
theorem renewalSmooth_of_deps
    (hcauchy : cauchySmoothStmt)
    (hmoments : manyCycleSmoothStmt)
    (htransfer : couplingParameterTransferSmoothStmt) :
    renewalSmoothStmt := by
  intro d hd D
  obtain ⟨lc, hlc, hrc, hc⟩ := hcauchy d hd D
  obtain ⟨lm, _, _, hm⟩ := hmoments d hd D
  obtain ⟨lt, _, _, _⟩ := htransfer d hd D
  refine ⟨max lc (max lm lt), hlc.trans_le (le_max_left _ _),
    hrc.trans_le (mul_le_mul_of_nonneg_left (le_max_left _ _) (by norm_num)), ?_⟩
  intro l hl δ hδ₀ hδ₁
  have hcl : lc ≤ l := (le_max_left _ _).trans hl
  have hml : lm ≤ l := ((le_max_left lm lt).trans (le_max_right lc _)).trans hl
  obtain ⟨ρ, B, c, Cc, _, _, hcpos, hCc, hcest⟩ := hc l hcl δ hδ₀ hδ₁
  obtain ⟨a, M, Cm, hapos, hM, hCm, hmest⟩ := hm l hml δ hδ₀ hδ₁
  refine ⟨c, max Cc Cm, a, M, hcpos, hCc.trans_le (le_max_left _ _),
    hapos, hM, ?_⟩
  intro Q hQ lam h₀ h₁ P K hK hD
  obtain ⟨_, _, _, hdecay⟩ := hcest Q hQ lam h₀ h₁ P K hK hD
  obtain ⟨hconditioned, hannealed⟩ := hmest Q hQ lam h₀ h₁ P K hK hD
  refine ⟨?_, hconditioned, ?_⟩
  · intro n
    exact (hdecay n).trans
      (mul_le_mul_of_nonneg_right (le_max_left Cc Cm) (Real.exp_pos _).le)
  · intro j
    exact (hannealed j).trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (le_max_right Cc Cm) (pow_nonneg hM.le j)))


end EinsteinFull.Blueprint.SbxCRenewalR01
