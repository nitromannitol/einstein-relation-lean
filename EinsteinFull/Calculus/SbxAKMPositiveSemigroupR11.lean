import EinsteinFull.Calculus.SbxAKMPositiveFromPredecessorsR10
import EinsteinFull.Calculus.SbxAKMSemigroupAssociationR10

/-! Uniform supplied-coupling covariance estimates from the four predecessors. -/
open MeasureTheory
open scoped NNReal ENNReal Topology
noncomputable section
namespace EinsteinFull.Blueprint.SbxAKMPositiveSemigroupR11
open EinsteinRelation EinsteinFull.Work.W5
open EinsteinFull.Blueprint.SbxCKMCovarianceSmoothR01
open EinsteinFull.Blueprint.SbxS5Section3R01
open EinsteinFull.Blueprint.SbxCKMCovarianceDecaySmoothR02
open EinsteinFull.Blueprint.SbxAUniformKMAssemblerR07
open EinsteinFull.Blueprint.SbxAKMPositiveFromPredecessorsR10
open EinsteinFull.Blueprint.SbxAKMSemigroupAssociationR10

theorem a_uniform_covariance_radius_decay_of_exact_predecessors
    (hfactor : node_rt_u3A_k_u2D_factorStmt)
    (hphase : SbxCPhaseUniformR07.phaseUniformStmt)
    (hmany : SbxCManyCycleUniformR06.manyCycleSmoothStmt)
    (hrem : node_rt_u3A_remainder_u2D_momentStmt) :
    ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ) (hΛ : 1 ≤ Λ₀) (hr : 1 ≤ r₀),
    ∃ l₀ : ℝ, 0 < l₀ ∧ r₀ < 2 * l₀ ∧
    ∀ l : ℝ, l₀ ≤ l → ∀ δ : ℝ, 0 < δ → δ < 1 →
    ∃ p c C : ℝ, 2 ≤ p ∧ 0 < c ∧ 0 < C ∧
    ∀ (β : ℕ → ℝ) (hβ : ∀ k, 1 ≤ k → 0 < β k),
    let SD : StructuralData d := ⟨Λ₀, r₀, β, hΛ, hr, hβ⟩
    ∀ (Q : EnvironmentLaw d SD.ellipticity SD.dependenceRange), HasSmoothBounds SD Q →
    ∀ (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
      (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
      (_hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K)
      (_hD : Regeneration.annealedCoupledLaw Q.measure K
        (regenerationNoReturn hd (l / lam)) ≠ 0)
      (A : ℝ), l ≤ A → ∀ F G : FieldPair d → ℝ,
    Measurable[localSigma {x : Vec d | euclideanNorm x < A / lam}] F →
    Measurable[localSigma {x : Vec d | euclideanNorm x < A / lam}] G →
    MemLp F (ENNReal.ofReal p) (reducedLaw Q) →
    MemLp G (ENNReal.ofReal p) (reducedLaw Q) →
    (∫ ω, F ω ∂reducedLaw Q) = 0 →
    let μ := Regeneration.annealedCoupledLaw Q.measure K
    let cov := fun t : ℝ≥0 => ∫ ωz, F (reduce ωz.1) *
      G (translate (ωz.2.1 t) (reduce ωz.1)) ∂μ
    ∀ t : ℝ≥0, |cov t| ≤
      C * Real.exp (C * A - c * lam ^ 2 * (t : ℝ)) *
        (eLpNorm F (ENNReal.ofReal p) (reducedLaw Q)).toReal *
        (eLpNorm G (ENNReal.ofReal p) (reducedLaw Q)).toReal := by
  intro d hd Λ₀ r₀ hΛ hr
  obtain ⟨l₀, hl₀, hsep, hdecay⟩ :=
    a_uniform_covariance_and_remainder_decay_of_predecessors hfactor hrem hmany hphase d hd Λ₀ r₀ hΛ hr
  refine ⟨l₀, hl₀, hsep, ?_⟩
  intro l hl δ hδ₀ hδ₁
  have hlpos : 0 < l := hl₀.trans_le hl
  obtain ⟨p, c, C, hp, hc, hC, hb⟩ := hdecay l hl δ hδ₀ hδ₁
  let D := 1 + C + C * (4 + 1 / l) * (1 + 1 / l)
  have hD : 0 < D := by dsimp only [D]; positivity
  have hCD : C ≤ D := by
    dsimp only [D]
    have : 0 < C * (4 + 1 / l) * (1 + 1 / l) := by positivity
    linarith only [this]
  have hDC : C * (4 + 1 / l) * (1 + 1 / l) ≤ D := by
    dsimp only [D]
    linarith only [hC]
  refine ⟨p, c, D, hp, hc, hD, ?_⟩
  intro β hβ
  dsimp only
  intro Q hQ lam h₀ h₁ P K hK hD' A hA F G hF hG hFp hGp hzero t
  apply ((hb β hβ Q hQ lam h₀ h₁ P K hK hD' A hA F G hF hG hFp hGp hzero t).2).trans
  apply mul_le_mul_of_nonneg_right _ ENNReal.toReal_nonneg
  apply mul_le_mul_of_nonneg_right _ ENNReal.toReal_nonneg
  apply mul_le_mul hCD (Real.exp_le_exp.mpr ?_) (Real.exp_pos _).le hD.le
  apply sub_le_sub_right
  have hcycle := sbxS2_prescribed_cycles_le l A hlpos hA
  have hApos : 0 < A := hlpos.trans_le hA
  have hAl : 1 ≤ A / l := (le_div_iff₀ hlpos).mpr (by simpa only [one_mul] using hA)
  calc
    _ ≤ C * ((4 + 1 / l) * (1 + A)) := mul_le_mul_of_nonneg_left hcycle hC.le
    _ ≤ C * ((4 + 1 / l) * ((1 + 1 / l) * A)) := by
      apply mul_le_mul_of_nonneg_left _ hC.le
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have hAlmul : 1 ≤ (1 / l) * A := by
        simpa only [div_eq_mul_inv, one_mul, mul_one, mul_comm] using hAl
      nlinarith only [hAlmul]
    _ = (C * (4 + 1 / l) * (1 + 1 / l)) * A := by ring
    _ ≤ D * A := mul_le_mul_of_nonneg_right hDC hApos.le



theorem a_uniform_positive_complex_path_covariance_of_exact_predecessors
    (hfactor : node_rt_u3A_k_u2D_factorStmt)
    (hphase : SbxCPhaseUniformR07.phaseUniformStmt)
    (hmany : SbxCManyCycleUniformR06.manyCycleSmoothStmt)
    (hrem : node_rt_u3A_remainder_u2D_momentStmt) :
    ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ) (hΛ : 1 ≤ Λ₀) (hr : 1 ≤ r₀),
    ∃ l₀ : ℝ, 0 < l₀ ∧ r₀ < 2 * l₀ ∧
    ∀ l : ℝ, l₀ ≤ l → ∀ δ : ℝ, 0 < δ → δ < 1 →
    ∃ p c C : ℝ, 2 ≤ p ∧ 0 < c ∧ 0 < C ∧
    ∀ (β : ℕ → ℝ) (hβ : ∀ k, 1 ≤ k → 0 < β k),
    let SD : StructuralData d := ⟨Λ₀, r₀, β, hΛ, hr, hβ⟩
    ∀ (Q : EnvironmentLaw d SD.ellipticity SD.dependenceRange), HasSmoothBounds SD Q →
    ∀ (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
      (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
      (_hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K)
      (_hD : Regeneration.annealedCoupledLaw Q.measure K
        (regenerationNoReturn hd (l / lam)) ≠ 0)
      (A : ℝ), l ≤ A → ∀ F G : Lp ℂ 2 (reducedLaw Q),
    IsRealLocalObservation Q (A / lam) F →
    IsRealLocalObservation Q (A / lam) G →
    MemLp (F : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q) →
    MemLp (G : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q) →
    (∫ ω, F ω ∂reducedLaw Q) = 0 → ∀ t : ℝ≥0,
    ‖∫ w, F (reduce w.1) * G (sbxS4CoupledEndpoint t w)
      ∂Regeneration.annealedCoupledLaw Q.measure K‖ ≤
      C * Real.exp (C * A - c * lam ^ 2 * (t : ℝ)) *
        (eLpNorm (F : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q)).toReal *
        (eLpNorm (G : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q)).toReal := by
  intro d hd Λ₀ r₀ hΛ hr
  obtain ⟨l₀, hl₀, hsep, hdecay⟩ :=
    a_uniform_covariance_radius_decay_of_exact_predecessors hfactor hphase hmany hrem d hd Λ₀ r₀ hΛ hr
  refine ⟨l₀, hl₀, hsep, ?_⟩
  intro l hl δ hδ₀ hδ₁
  obtain ⟨p, c, C, hp, hc, hC, hb⟩ := hdecay l hl δ hδ₀ hδ₁
  refine ⟨p, c, C, hp, hc, hC, ?_⟩
  intro β hβ
  dsimp only
  intro Q hQ lam h₀ h₁ P K hK hD A hA F G hFl hGl hFp hGp hzero t
  obtain ⟨f, hf, hfF, hfp, hfnorm⟩ :=
    sbxS4_realLocal_representative Q (A / lam) F hFl (ENNReal.ofReal p) hFp
  obtain ⟨g, hg, hgG, hgp, hgnorm⟩ :=
    sbxS4_realLocal_representative Q (A / lam) G hGl (ENNReal.ofReal p) hGp
  have hfzero := sbxS4_real_representative_centered Q F hfF hzero
  have hcov := sbxS4_coupled_covariance_congr hd Q lam l δ h₀.le h₁ P K hK t
    hfF.symm hgG.symm
  rw [hcov]
  simp_rw [← Complex.ofReal_mul]
  rw [integral_complex_ofReal, Complex.norm_real, Real.norm_eq_abs]
  have hbound := hb β hβ Q hQ lam h₀ h₁ P K hK hD A hA f g hf hg hfp hgp hfzero t
  rw [hfnorm, hgnorm] at hbound
  exact hbound



theorem a_uniform_positive_semigroup_covariance_of_exact_predecessors
    (hfactor : node_rt_u3A_k_u2D_factorStmt)
    (hphase : SbxCPhaseUniformR07.phaseUniformStmt)
    (hmany : SbxCManyCycleUniformR06.manyCycleSmoothStmt)
    (hrem : node_rt_u3A_remainder_u2D_momentStmt) :
    ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ) (hΛ : 1 ≤ Λ₀) (hr : 1 ≤ r₀),
    ∃ l₀ : ℝ, 0 < l₀ ∧ r₀ < 2 * l₀ ∧
    ∀ l : ℝ, l₀ ≤ l → ∀ δ : ℝ, 0 < δ → δ < 1 →
    ∃ p c C : ℝ, 2 ≤ p ∧ 0 < c ∧ 0 < C ∧
    ∀ (β : ℕ → ℝ) (hβ : ∀ k, 1 ≤ k → 0 < β k),
    let SD : StructuralData d := ⟨Λ₀, r₀, β, hΛ, hr, hβ⟩
    ∀ (Q : EnvironmentLaw d SD.ellipticity SD.dependenceRange), HasSmoothBounds SD Q →
    ∀ (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
      (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
      (_hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K)
      (_hD : Regeneration.annealedCoupledLaw Q.measure K
        (regenerationNoReturn hd (l / lam)) ≠ 0)
      (S : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)),
    IsComplexEnvironmentSemigroup Q (Regeneration.Renewal.forceCoord hd) (lam : ℂ) S →
    ∀ A : ℝ, l ≤ A → ∀ F G : Lp ℂ 2 (reducedLaw Q),
    IsRealLocalObservation Q (A / lam) F → IsRealLocalObservation Q (A / lam) G →
    MemLp (F : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q) →
    MemLp (G : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q) →
    (∫ ω, F ω ∂reducedLaw Q) = 0 → ∀ t : ℝ≥0,
    ‖∫ ω, F ω * S t G ω ∂reducedLaw Q‖ ≤
      C * Real.exp (C * A - c * lam ^ 2 * (t : ℝ)) *
        (eLpNorm (F : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q)).toReal *
        (eLpNorm (G : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q)).toReal := by
  intro d hd Λ₀ r₀ hΛ hr
  obtain ⟨lD, hlD, hsD, hdecay⟩ :=
    a_uniform_positive_complex_path_covariance_of_exact_predecessors hfactor hphase hmany hrem d hd Λ₀ r₀ hΛ hr
  obtain ⟨lR, pR, hlR, hsR, hpR, hassoc⟩ :=
    a_uniform_supplied_covariance_eq_semigroup_of_remainder hrem d hd Λ₀ r₀ hΛ hr
  refine ⟨max lD lR, hlD.trans_le (le_max_left _ _),
    hsD.trans_le (by linarith only [le_max_left lD lR]), ?_⟩
  intro l hl δ hδ0 hδ1
  have hlD' := (le_max_left lD lR).trans hl
  have hlR' := (le_max_right lD lR).trans hl
  obtain ⟨pD, c, C, hpD, hc, hC, hbound⟩ := hdecay l hlD' δ hδ0 hδ1
  refine ⟨max pD (2 * pR), c, C, hpD.trans (le_max_left _ _), hc, hC, ?_⟩
  intro β hβ
  dsimp only
  intro Q hQ lam h0 h1 P K hK hD S hS A hA F G hFl hGl hFp hGp hmean t
  let := reducedLaw_probability Q
  have hpD' : ENNReal.ofReal pD ≤ ENNReal.ofReal (max pD (2 * pR)) :=
    ENNReal.ofReal_le_ofReal (le_max_left _ _)
  have hpR' : ENNReal.ofReal (2 * pR) ≤ ENNReal.ofReal (max pD (2 * pR)) :=
    ENNReal.ofReal_le_ofReal (le_max_right _ _)
  have heq := (hassoc β hβ Q hQ lam h0 h1 l δ hlR' hδ0 hδ1 P K hK hD S hS F G
    (hGp.mono_exponent hpR') t).2
  have hb := hbound β hβ Q hQ lam h0 h1 P K hK hD A hA F G hFl hGl
    (hFp.mono_exponent hpD') (hGp.mono_exponent hpD') hmean t
  have hFnorm := ENNReal.toReal_mono hFp.eLpNorm_ne_top
    (eLpNorm_le_eLpNorm_of_exponent_le (f := (F : FieldPair d → ℂ)) hpD')
  have hGnorm := ENNReal.toReal_mono hGp.eLpNorm_ne_top
    (eLpNorm_le_eLpNorm_of_exponent_le (f := (G : FieldPair d → ℂ)) hpD')
  rw [heq]
  exact hb.trans (mul_le_mul
    (mul_le_mul_of_nonneg_left hFnorm (mul_nonneg hC.le (Real.exp_pos _).le))
    hGnorm ENNReal.toReal_nonneg (by positivity))


#print axioms a_uniform_positive_semigroup_covariance_of_exact_predecessors

end EinsteinFull.Blueprint.SbxAKMPositiveSemigroupR11
