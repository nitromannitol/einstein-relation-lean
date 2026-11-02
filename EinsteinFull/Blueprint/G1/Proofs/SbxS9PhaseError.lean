import EinsteinFull.Blueprint.G1.Proofs.SbxS2KmDecomp
import EinsteinFull.Blueprint.G1.Proofs.SbxS5PhaseError
import EinsteinFull.Blueprint.G1.node_rt_u3A_local_u2D_mixing_u23_phase_u2D_error
import EinsteinFull.Blueprint.G1.node_rt_u3A_local_u2D_mixing_u23_fixed_u2D_radius

open MeasureTheory
open scoped NNReal ENNReal Topology

namespace EinsteinFull.Blueprint
open EinsteinRelation

/-- Conditioned event decay with a structural threshold preceding the tail rate.
The higher moment uses the actual conditioned law and terminal observable. -/
theorem sbxS9_conditioned_remainder_moment_variable_rate
    (hrem : node_rt_u3A_remainder_u2D_momentStmt) :
    ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ),
    ∃ l₀ : ℝ, 0 < l₀ ∧ r₀ < 2 * l₀ ∧
    ∀ a : ℝ, 0 < a → ∃ p c C : ℝ, 2 ≤ p ∧ 0 < c ∧ 0 < C ∧
    ∀ (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
      (l δ : ℝ), l₀ ≤ l → 0 < δ → δ < 1 →
    ∀ (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
      (hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K)
      (hD : Regeneration.annealedCoupledLaw Q.measure K
        (regenerationNoReturn hd (l / lam)) ≠ 0),
    ∀ F G : FieldPair d → ℝ, Measurable F → Measurable G →
      MemLp F (ENNReal.ofReal p) (reducedLaw Q) →
      MemLp G (ENNReal.ofReal p) (reducedLaw Q) →
    ∀ (J : ℝ) (t : ℝ≥0) (E : Set (FieldPair d × Regeneration.CoupledSample d)),
      0 ≤ J → regenerationConditionedLaw hd Q lam l K hK.1 hD E ≤
        ENNReal.ofReal (Real.exp (J - a * lam ^ 2 * (t : ℝ))) →
      IntegrableOn (fun ωz => F (reduce ωz.1) *
        G (translate (ωz.2.1 t) (reduce ωz.1))) E
        (regenerationConditionedLaw hd Q lam l K hK.1 hD) ∧
      |∫ ωz in E, F (reduce ωz.1) *
        G (translate (ωz.2.1 t) (reduce ωz.1))
          ∂regenerationConditionedLaw hd Q lam l K hK.1 hD| ≤
        C * Real.exp (C * J - c * lam ^ 2 * (t : ℝ)) *
          (eLpNorm F (ENNReal.ofReal p) (reducedLaw Q)).toReal *
          (eLpNorm G (ENNReal.ofReal p) (reducedLaw Q)).toReal := by
  intro d hd Λ₀ r₀
  obtain ⟨l₀, p₀, D, hl₀, hsep, hp₀, hDpos, hmoment⟩ :=
    sbxS2_covariance_power_moment_of_remainder hrem d hd Λ₀ r₀
  refine ⟨l₀, hl₀, hsep, ?_⟩
  intro a ha
  obtain ⟨r, c, C, hr, hc, hC, hscalar⟩ :=
    sbxS2_power_interpolation_constants D a hDpos ha
  have hr₁ : 1 < r := lt_of_lt_of_le (by norm_num) hr
  have hr₀ : 0 < r := lt_trans zero_lt_one hr₁
  have hp₀pos : 0 ≤ p₀ := le_trans (by norm_num) hp₀
  refine ⟨p₀ * r, c, C, ?_, hc, hC, ?_⟩
  · exact hp₀.trans (le_mul_of_one_le_right hp₀pos hr₁.le)
  intro Q lam h₀ h₁ l δ hl hδ₀ hδ₁ P K hK hD F G hF hG hFp hGp J t E hJ hprob
  let μ := regenerationConditionedLaw hd Q lam l K hK.1 hD
  let f := fun ωz : FieldPair d × Regeneration.CoupledSample d =>
    F (reduce ωz.1) * G (translate (ωz.2.1 t) (reduce ωz.1))
  have hfm : Measurable f :=
    ((hF.comp Probability.measurable_reduce).comp measurable_fst).mul
      (hG.comp (Probability.continuous_translate.measurable.comp
        (((continuous_eval_const t).measurable.comp measurable_snd.fst).prodMk
          (Probability.measurable_reduce.comp measurable_fst))))
  have hpower := hmoment r hr₀ Q lam h₀ h₁ l δ hl hδ₀ hδ₁ P K hK hD
    F G hF hG hFp hGp t μ (by simp only [μ, Set.mem_insert_iff, Set.mem_singleton_iff, or_true])
  let : IsProbabilityMeasure μ :=
    regenerationConditionedLaw_probability hd Q lam l K hK.1 hD
  have hfr : MemLp f (ENNReal.ofReal r) μ := by
    apply (integrable_norm_rpow_iff hfm.aestronglyMeasurable (by positivity)
      ENNReal.ofReal_ne_top).mp
    simpa only [ENNReal.toReal_ofReal hr₀.le] using hpower.1
  refine ⟨(MemLp.integrable (q := ENNReal.ofReal r) ?_ hfr).integrableOn, ?_⟩
  · simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hr₁.le
  have hb := sbxS2_setIntegral_abs_le_moment μ f hfm.aestronglyMeasurable E r
    (D * Real.exp (D * lam ^ 2 * (t : ℝ)) *
      (eLpNorm F (ENNReal.ofReal (p₀ * r)) (reducedLaw Q)).toReal ^ r *
      (eLpNorm G (ENNReal.ofReal (p₀ * r)) (reducedLaw Q)).toReal ^ r)
    (Real.exp (J - a * lam ^ 2 * (t : ℝ))) hr₁ hpower.1 hpower.2
    (Real.exp_pos _).le hprob
  apply hb.trans
  simpa only [mul_assoc] using hscalar J (lam ^ 2 * (t : ℝ))
    (eLpNorm F (ENNReal.ofReal (p₀ * r)) (reducedLaw Q)).toReal
    (eLpNorm G (ENNReal.ofReal (p₀ * r)) (reducedLaw Q)).toReal
    hJ (by positivity) ENNReal.toReal_nonneg ENNReal.toReal_nonneg

/-- The literal terminal-cycle integral under the conditioned law has a decay
rate chosen after the structural threshold, uniformly over all cycle indices. -/
theorem sbxS9_conditioned_cycle_remainder
    (hren : node_rt_u3A_renewalStmt)
    (hrem : node_rt_u3A_remainder_u2D_momentStmt) :
    ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ),
    ∃ l₀ : ℝ, 0 < l₀ ∧ r₀ < 2 * l₀ ∧
    ∀ l : ℝ, l₀ ≤ l → ∀ δ : ℝ, 0 < δ → δ < 1 →
    ∃ p c C : ℝ, 2 ≤ p ∧ 0 < c ∧ 0 < C ∧
    ∀ (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
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
          (eLpNorm G (ENNReal.ofReal p) (reducedLaw Q)).toReal := by
  intro d hd Λ₀ r₀
  obtain ⟨L₀, hL₀, hsep₀, hevent⟩ :=
    sbxS9_conditioned_remainder_moment_variable_rate hrem d hd Λ₀ r₀
  obtain ⟨L₁, _hL₁, _hsep₁, htail⟩ := renewal_cycle_tails hren d hd Λ₀ r₀
  refine ⟨max L₀ L₁, hL₀.trans_le (le_max_left _ _),
    hsep₀.trans_le (by linarith only [le_max_left L₀ L₁]), ?_⟩
  intro l hl δ hδ₀ hδ₁
  have hl₀ : L₀ ≤ l := (le_max_left _ _).trans hl
  have hl₁ : L₁ ≤ l := (le_max_right _ _).trans hl
  obtain ⟨a, B, ha, hB, htail'⟩ := htail l hl₁ δ hδ₀ hδ₁
  obtain ⟨p, c, C₀, hp, hc, hC₀, hevent'⟩ := hevent a ha
  obtain ⟨C, hC, hcycle⟩ := geometric_cycle_bound (Real.exp (C₀ * B)) C₀
    (Real.exp_pos _)
  refine ⟨p, c, C, hp, hc, hC, ?_⟩
  intro Q lam h₀ h₁ P K hK hD m G hG hLp t
  let : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  let J := B * ((m : ℝ) + 1)
  have hJ : 0 ≤ J := mul_nonneg hB.le (by positivity)
  have hprob : regenerationConditionedLaw hd Q lam l K hK.1 hD
      {ωz | regenerationTime hd lam l m ωz.2 ≤ (t : ℝ≥0∞) ∧
        (t : ℝ≥0∞) < regenerationTime hd lam l (m + 1) ωz.2} ≤
      ENNReal.ofReal (Real.exp (J - a * lam ^ 2 * (t : ℝ))) := by
    apply (htail' Q lam h₀ h₁ P K hK hD m t).trans
    apply ENNReal.ofReal_le_ofReal
    calc
      B * Real.exp (B * m - a * lam ^ 2 * (t : ℝ)) ≤
          Real.exp B * Real.exp (B * m - a * lam ^ 2 * (t : ℝ)) :=
        mul_le_mul_of_nonneg_right
          ((show B ≤ B + 1 by linarith).trans (Real.add_one_le_exp B))
          (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; dsimp only [J]; ring
  have hone : eLpNorm (fun _ : FieldPair d => (1 : ℝ))
      (ENNReal.ofReal p) (reducedLaw Q) = 1 := by
    rw [eLpNorm_const' 1 (ne_of_gt (ENNReal.ofReal_pos.mpr (by linarith)))
      ENNReal.ofReal_ne_top]
    simp
  have hout := hevent' Q lam h₀ h₁ l δ hl₀ hδ₀ hδ₁ P K hK hD
    (fun _ => 1) G measurable_const hG (memLp_const 1) hLp J t _ hJ hprob
  have hbound : |∫ ωz in {ωz | regenerationTime hd lam l m ωz.2 ≤ (t : ℝ≥0∞) ∧
      (t : ℝ≥0∞) < regenerationTime hd lam l (m + 1) ωz.2},
      G (translate (ωz.2.1 t) (reduce ωz.1))
        ∂regenerationConditionedLaw hd Q lam l K hK.1 hD| ≤
      C₀ * Real.exp (C₀ * J - c * lam ^ 2 * (t : ℝ)) *
        (eLpNorm G (ENNReal.ofReal p) (reducedLaw Q)).toReal := by
    simpa only [one_mul, hone, ENNReal.toReal_one, mul_one] using hout.2
  have hpref : C₀ * Real.exp (C₀ * J) ≤ C * Real.exp (C * m) := by
    calc
      _ = C₀ * (Real.exp (C₀ * B)) ^ (m + 1) := by
        rw [← Real.exp_nat_mul]
        congr 1
        congr 1
        dsimp only [J]
        push_cast
        ring
      _ ≤ _ := hcycle m
  apply hbound.trans
  calc
    _ = (C₀ * Real.exp (C₀ * J)) * Real.exp (-c * lam ^ 2 * (t : ℝ)) *
        (eLpNorm G (ENNReal.ofReal p) (reducedLaw Q)).toReal := by
      simp only [sub_eq_add_neg, Real.exp_add, neg_mul, mul_assoc]
    _ ≤ (C * Real.exp (C * m)) * Real.exp (-c * lam ^ 2 * (t : ℝ)) *
        (eLpNorm G (ENNReal.ofReal p) (reducedLaw Q)).toReal :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hpref (Real.exp_pos _).le) ENNReal.toReal_nonneg
    _ = _ := by simp only [sub_eq_add_neg, Real.exp_add, neg_mul, mul_assoc]

/-- Exact phase-error reduction with the four ordered source dependencies.
All constants are chosen before the law, force, support radius, and cycle count. -/
theorem node_rt_u3A_local_u2D_mixing_u23_phase_u2D_error_of_deps
    (hmren : node_rt_u3A_m_u2D_renewalStmt)
    (hren : node_rt_u3A_renewalStmt)
    (hrem : node_rt_u3A_remainder_u2D_momentStmt)
    (_hfixed : node_rt_u3A_local_u2D_mixing_u23_fixed_u2D_radiusStmt) :
    node_rt_u3A_local_u2D_mixing_u23_phase_u2D_errorStmt := by
  intro d hd Λ₀ r₀
  obtain ⟨L₀, p₀, hL₀, hsep₀, hp₀, hrenew⟩ :=
    m_renewal_eq_memLp hmren hrem d hd Λ₀ r₀
  obtain ⟨L₁, _hL₁, _hsep₁, hcycle⟩ :=
    sbxS9_conditioned_cycle_remainder hren hrem d hd Λ₀ r₀
  obtain ⟨L₂, _hL₂, _hsep₂, hren'⟩ := hren d hd Λ₀ r₀
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
  intro Q lam h₀ h₁ P K hK hD A m _hA hmpos hsupp G hG hLp
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
  have hactual := hren'' Q lam h₀ h₁ P K hK hD
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
    have hbnd := hcycle' Q lam h₀ h₁ P K hK hD
      m G (hG.mono (Probability.localSigma_le_borel _) le_rfl) hLp₁ t
    exact hbnd.trans (mul_le_mul_of_nonneg_left hNg
      (mul_nonneg hC₀.le (Real.exp_pos _).le))
  have hh : ∀ t : ℝ≥0, hm t = rm t +
      ∑ n ∈ Finset.range (⌊(t : ℝ) / (Δ : ℝ)⌋₊ + 1), pn n * hm (t - n * Δ) :=
    hrenew Q lam h₀ h₁ l δ hl₀ hδ₀ hδ₁ P K hK hD A m hmpos hsupp G hG hLp₀
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

#print axioms sbxS9_conditioned_remainder_moment_variable_rate
#print axioms sbxS9_conditioned_cycle_remainder
#print axioms node_rt_u3A_local_u2D_mixing_u23_phase_u2D_error_of_deps

example (h₁ : node_rt_u3A_m_u2D_renewalStmt) (h₂ : node_rt_u3A_renewalStmt)
    (h₃ : node_rt_u3A_remainder_u2D_momentStmt)
    (h₄ : node_rt_u3A_local_u2D_mixing_u23_fixed_u2D_radiusStmt) :
    node_rt_u3A_local_u2D_mixing_u23_phase_u2D_errorStmt :=
  node_rt_u3A_local_u2D_mixing_u23_phase_u2D_error_of_deps h₁ h₂ h₃ h₄

end EinsteinFull.Blueprint

#lint
