import EinsteinFull.Calculus.SbxAKMPositiveSemigroupR11

/-! Signed k/m assembly conditional on actual coupling existence. -/
open MeasureTheory ProbabilityTheory EinsteinRelation
open EinsteinRelation.Regeneration
open EinsteinRelation.External.GantertSection7Support
open EinsteinFull.External.Source.GMP
open scoped NNReal ENNReal Topology
noncomputable section
namespace EinsteinFull.Blueprint.SbxAKMSignedAssemblyR11
open EinsteinFull.Work.W5
open EinsteinFull.Blueprint.SbxS5Section3R01
open EinsteinFull.Blueprint.SbxAKMPositiveFromPredecessorsR10
open EinsteinFull.Blueprint.SbxAKMPositiveSemigroupR11

/-- Uniform signed covariance and k/m estimates, conditional on actual coupling existence. -/
theorem a_uniform_km_of_exact_predecessors_and_actual_couplings
    (hfactor : node_rt_u3A_k_u2D_factorStmt)
    (hphase : SbxCPhaseUniformR07.phaseUniformStmt)
    (hmany : SbxCManyCycleUniformR06.manyCycleSmoothStmt)
    (hrem : node_rt_u3A_remainder_u2D_momentStmt)
    (hcoup : ∀ (d : ℕ) (hd : 2 ≤ d) (Λ r : ℝ),
      ∃ L : ℝ, 0 < L ∧ r < 2 * L ∧
      ∀ l : ℝ, L ≤ l → ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧
      ∀ (D : StructuralData d), D.ellipticity = Λ → D.dependenceRange = r →
      ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange), HasSmoothBounds D Q →
      ∀ (μ : ℝ) (h0 : 0 < μ) (h1 : μ ≤ 1),
        ∃ (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d),
          IsRegenerationCoupling hd Q μ l δ h0.le h1 P K ∧
          ENNReal.ofReal (1 / 2 : ℝ) ≤ annealedCoupledLaw Q.measure K
            (regenerationNoReturn hd (l / μ))) :
    SbxCLocalMixingUniformR06.kmDecompUniformFullRangeSmoothStmt := by
  intro d hd Λ₀ r₀ hΛ hr
  obtain ⟨L, hL, hsepL, hcoupling⟩ :=
    hcoup d hd Λ₀ r₀
  obtain ⟨lD, hlD, hsepD, hdecay⟩ :=
    a_uniform_positive_semigroup_covariance_of_exact_predecessors hfactor hphase hmany hrem d hd Λ₀ r₀ hΛ hr
  obtain ⟨lK, hlK, hsepK, hkm⟩ :=
    a_uniform_positiveKmFullRange_of_predecessors hfactor hrem hmany hphase d hd Λ₀ r₀ hΛ hr
  refine ⟨max lK (max L lD), hlK.trans_le (le_max_left _ _),
    hsepK.trans_le (by linarith only [le_max_left lK (max L lD)]), ?_⟩
  intro l hl δ hδ0 hδ1
  have hlK' : lK ≤ l := (le_max_left _ _).trans hl
  have hlL : L ≤ l := (le_max_left _ _).trans ((le_max_right _ _).trans hl)
  have hlD' : lD ≤ l := (le_max_right _ _).trans ((le_max_right _ _).trans hl)
  obtain ⟨δa, hδa0, hδa1, hexists⟩ := hcoupling l hlL
  obtain ⟨pD, cD, CD, hpD, hcD, hCD, hcov⟩ := hdecay l hlD' δa hδa0 hδa1
  obtain ⟨pK, cK, CK, hpK, hcK, hCK, hk⟩ := hkm l hlK' δ hδ0 hδ1
  let p := max pK pD
  let c := min cK cD
  let C := max CK CD
  refine ⟨p, c, C, hpK.trans (le_max_left _ _), lt_min hcK hcD,
    hCK.trans_le (le_max_left _ _), ?_⟩
  intro β hβ
  dsimp only
  let D : StructuralData d := ⟨Λ₀, r₀, β, hΛ, hr, hβ⟩
  have hpositive : ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange),
      HasSmoothBounds D Q → ∀ (lam : ℝ), 0 < lam → lam ≤ 1 →
      ∀ S : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      IsComplexEnvironmentSemigroup Q (Renewal.forceCoord hd) (lam : ℂ) S →
      ∀ A : ℝ, l ≤ A → ∀ F G : Lp ℂ 2 (reducedLaw Q),
      IsRealLocalObservation Q (A / lam) F → IsRealLocalObservation Q (A / lam) G →
      MemLp (F : FieldPair d → ℂ) (ENNReal.ofReal pD) (reducedLaw Q) →
      MemLp (G : FieldPair d → ℂ) (ENNReal.ofReal pD) (reducedLaw Q) →
      (∫ ω, F ω ∂reducedLaw Q) = 0 → ∀ t : ℝ≥0,
      ‖∫ ω, F ω * S t G ω ∂reducedLaw Q‖ ≤
        CD * Real.exp (CD * A - cD * lam ^ 2 * (t : ℝ)) *
          (eLpNorm (F : FieldPair d → ℂ) (ENNReal.ofReal pD) (reducedLaw Q)).toReal *
          (eLpNorm (G : FieldPair d → ℂ) (ENNReal.ofReal pD) (reducedLaw Q)).toReal := by
    intro Q hQ lam h0 h1 S hS A hA F G hF hG hFp hGp hzero t
    obtain ⟨P, K, hK, hmass⟩ := hexists D rfl rfl Q hQ lam h0 h1
    have hD : annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam)) ≠ 0 := by
      intro hz
      rw [hz] at hmass
      exact (not_le_of_gt (ENNReal.ofReal_pos.mpr (by norm_num : (0 : ℝ) < 1 / 2))) hmass
    exact hcov β hβ Q hQ lam h0 h1 P K hK hD S hS A hA F G hF hG hFp hGp hzero t
  have hsigned := smooth_positive_covariance_bound_mono_signed D
    (Renewal.forceCoord hd)
    (l := l) (p := pD) (c := cD) (C := CD) (lam₀ := 1)
    (p' := p) (c' := c) (C' := C) (lam₀' := 1)
    (hlK.trans_le hlK') hCD.le (le_max_right _ _) (min_le_right _ _)
    (le_max_right _ _) le_rfl hpositive
  have hkm' := smooth_positive_km_bound_mono hd D (p' := p) (c' := c) (C' := C)
    (lam₀' := 1) (hlK.trans_le hlK') hCK.le
    (le_max_left _ _) (min_le_left _ _) (le_max_left _ _) le_rfl (hk β hβ)
  intro Q hQ
  refine ⟨?_, hsigned Q hQ⟩
  intro lam h0 h1
  exact hkm' Q hQ lam h0 h1 h1


end EinsteinFull.Blueprint.SbxAKMSignedAssemblyR11
