import EinsteinFull.Blueprint.G1.Draft.SbxCManyCycleSmoothR03

/-! Uniform many-cycle moments, conditional on the three source predecessors.
This draft is not a frozen or adopted graph reduction. -/

open MeasureTheory
open scoped NNReal ENNReal

namespace EinsteinFull.Blueprint.SbxCManyCycleUniformR06
open EinsteinRelation Regeneration EinsteinFull.Work.W5

/-- All moment constants are fixed before the smoothness derivative bounds. -/
def manyCycleSmoothStmt : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ) (hΛ : 1 ≤ Λ₀) (hr : 1 ≤ r₀),
    ∃ l₀ : ℝ, 0 < l₀ ∧ r₀ < 2 * l₀ ∧
    ∀ l : ℝ, l₀ ≤ l → ∀ δ : ℝ, 0 < δ → δ < 1 →
    ∃ a M C : ℝ, 0 < a ∧ 0 < M ∧ 0 < C ∧
    ∀ (β : ℕ → ℝ) (hβ : ∀ k, 1 ≤ k → 0 < β k),
    let D : StructuralData d := ⟨Λ₀, r₀, β, hΛ, hr, hβ⟩
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (_hQ : HasSmoothBounds D Q) (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
      (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
      (hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K)
      (hD : annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam)) ≠ 0),
    (∀ j : ℕ,
      (∫⁻ ωz, regenerationExponentialWeight hd lam l a j ωz.2
        ∂regenerationConditionedLaw hd Q lam l K hK.1 hD) ≤ ENNReal.ofReal (M ^ j)) ∧
    (∀ j : ℕ,
      (∫⁻ ωz, regenerationExponentialWeight hd lam l a j ωz.2
        ∂annealedCoupledLaw Q.measure K) ≤ ENNReal.ofReal (C * M ^ j))

/-- Uniform moments from factorization, all-law first-cycle tails and transfer. -/
theorem manyCycleSmooth_of_deps
    (hfac : SbxCFactorizationR01.environmentalFactorizationSmoothStmt)
    (htails : node_app_u3A_regen_u2D_tailsStmt)
    (htransfer : node_rt_u3A_renewal_u23_coupling_u2D_parameter_u2D_transferStmt) :
    manyCycleSmoothStmt := by
  intro d hd Λ₀ r₀ hΛ hr₀
  obtain ⟨lt, hlt, hrt, ht⟩ := htails d hd Λ₀ r₀
  obtain ⟨lp, _hlp, _hrp, _hp⟩ := htransfer d hd Λ₀ r₀
  refine ⟨max lt lp, hlt.trans_le (le_max_left _ _),
    hrt.trans_le (mul_le_mul_of_nonneg_left (le_max_left _ _) (by norm_num)), ?_⟩
  intro l hl δ hδ hδ₁
  obtain ⟨c, C, a, M, _hc, _hC, ha, _hac, hM, ht⟩ :=
    ht l ((le_max_left _ _).trans hl) δ hδ hδ₁
  refine ⟨a, max M 1, 1, ha, hM.trans_le (le_max_left _ _), zero_lt_one, ?_⟩
  intro β hβ
  dsimp only
  let D : StructuralData d := ⟨Λ₀, r₀, β, hΛ, hr₀, hβ⟩
  intro Q hQ lam h₀ h₁ P K hK hD
  obtain ⟨hD', _hhalf, _htail, hfirst, hcond⟩ := ht Q lam h₀ h₁ P K hK
  let μ := annealedCoupledLaw Q.measure K
  let ν := regenerationConditionedLaw hd Q lam l K hK.1 hD
  let : IsProbabilityMeasure μ := annealedCoupledLaw_isProbabilityMeasure Q.measure K hK.1
  let : IsProbabilityMeasure ν := regenerationConditionedLaw_probability hd Q lam l K hK.1 hD
  have hν : (∫⁻ q, regenerationExponentialWeight hd lam l a 1 q.2 ∂ν) ≤
      ENNReal.ofReal (max M 1) := hcond.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  have hμ : (∫⁻ q, regenerationExponentialWeight hd lam l a 1 q.2 ∂μ) ≤
      ENNReal.ofReal (max M 1) := hfirst.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  have hfν := regenerationTime_ne_top_ae_of_exponentialMoment hd lam l a 1 ν
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hν)
  have hfμ := regenerationTime_ne_top_ae_of_exponentialMoment hd lam l a 1 μ
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hμ)
  have hlpos : 0 < l := hlt.trans_le ((le_max_left _ _).trans hl)
  have hr : D.dependenceRange < 2 * l := hrt.trans_le
    (mul_le_mul_of_nonneg_left ((le_max_left _ _).trans hl) (by norm_num))
  have hpow (j : ℕ) : (∫⁻ q, regenerationExponentialWeight hd lam l a j q.2 ∂ν) ≤
      ENNReal.ofReal ((max M 1) ^ j) := by
    induction j with
    | zero => simp only [many_cycle_weight_zero, lintegral_one, measure_univ,
        pow_zero, ENNReal.ofReal_one, le_refl]
    | succ j ih =>
      rw [SbxCManyCycleSmoothR03.many_cycle_moment_succ_smooth hfac hd D Q hQ lam h₀ h₁ l δ hlpos hr hδ hδ₁ P K hK hD ν
        (by simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; exact Or.inr rfl) hfν a j]
      exact (mul_le_mul' hν ih).trans_eq (by
        rw [← ENNReal.ofReal_mul (le_max_of_le_right zero_le_one), pow_succ, mul_comm])
  refine ⟨hpow, ?_⟩
  intro j
  cases j with
  | zero => simp only [many_cycle_weight_zero, lintegral_one, measure_univ,
      pow_zero, mul_one, ENNReal.ofReal_one, le_refl]
  | succ j =>
    rw [SbxCManyCycleSmoothR03.many_cycle_moment_succ_smooth hfac hd D Q hQ lam h₀ h₁ l δ hlpos hr hδ hδ₁ P K hK hD μ
      (by simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; exact Or.inl rfl) hfμ a j]
    exact (mul_le_mul' hμ (hpow j)).trans_eq (by
      rw [one_mul, ← ENNReal.ofReal_mul (le_max_of_le_right zero_le_one), pow_succ, mul_comm])


end EinsteinFull.Blueprint.SbxCManyCycleUniformR06
