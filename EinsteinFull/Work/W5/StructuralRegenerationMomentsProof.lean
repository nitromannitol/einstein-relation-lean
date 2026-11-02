import EinsteinFull.Work.W5.UniformLatticeRenewalProof
import EinsteinFull.Frozen.GantertRegenerationTail
import EinsteinRelation.Regeneration.FirstRegenerationFiniteness
import EinsteinRelation.Regeneration.RenewalRecordIteration
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# First-cycle moments for the fixed GMP construction

The only nonstandard input used here is the root-approved named GMP tail and
no-return input. The construction scale and split probability are fixed before
the moment constants and the environment law. No change of coupling or scale,
two-positive-mass claim, or many-cycle independence is implicit in these results.
-/

open MeasureTheory
open scoped NNReal ENNReal

noncomputable section

namespace EinsteinFull.Work.W5

open EinsteinRelation

/-- An actual first-cycle exponential tail forces finiteness, including the
infinite branch of the literal trial construction. -/
theorem regenerationTime_one_ne_top_ae_of_tail {d : ℕ} (hd : 2 ≤ d)
    {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (lam l c C : ℝ)
    (hlam : 0 < lam) (hc : 0 < c) (K : Regeneration.CoupledQuenchedLaws d)
    (htail : ∀ t : ℝ, 0 ≤ t →
      Regeneration.annealedCoupledLaw Q.measure K
        {ωz | ENNReal.ofReal t < regenerationTime hd lam l 1 ωz.2} ≤
          ENNReal.ofReal (C * Real.exp (-c * lam ^ 2 * t))) :
    ∀ᵐ ωz ∂Regeneration.annealedCoupledLaw Q.measure K,
      regenerationTime hd lam l 1 ωz.2 ≠ ⊤ := by
  have he (z : Regeneration.CoupledSample d) :
      regenerationTime hd lam l 1 z = Regeneration.firstRegenerationTime
        (Regeneration.Renewal.regenDelta lam) lam (l / lam) z
        (Regeneration.Renewal.forceCoord hd) := Regeneration.regenerationTime_one _ _ _ _ _
  simp_rw [he] at htail ⊢
  exact Regeneration.firstRegenerationTime_ne_top_ae_of_tail Q.measure K
    (Regeneration.Renewal.regenDelta lam) lam (l / lam) c C hc hlam
    (Regeneration.Renewal.forceCoord hd) htail

private theorem regeneration_first_slice_le_of_tail {d : ℕ} (hd : 2 ≤ d)
    {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (lam l c C : ℝ)
    (hlam : 0 < lam) (hc : 0 < c) (hC : 0 < C)
    (K : Regeneration.CoupledQuenchedLaws d)
    (hK : Regeneration.HasProbabilityLaws Q.measure K)
    (htail : ∀ t : ℝ, 0 ≤ t →
      Regeneration.annealedCoupledLaw Q.measure K
        {ωz | ENNReal.ofReal t < regenerationTime hd lam l 1 ωz.2} ≤
          ENNReal.ofReal (C * Real.exp (-c * lam ^ 2 * t))) (n : ℕ) :
    Regeneration.annealedCoupledLaw Q.measure K {ωz |
      regenerationTime hd lam l 1 ωz.2 =
        (((n : ℝ≥0) * Regeneration.Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)} ≤
      ENNReal.ofReal ((1 + C) * Real.exp (-(c / 2) * n)) := by
  letI := Regeneration.annealedCoupledLaw_isProbabilityMeasure Q.measure K hK
  by_cases hn : n = 0
  · subst n
    simp only [Nat.cast_zero, mul_zero, Real.exp_zero, mul_one]
    exact (prob_le_one).trans (by
      simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal (show 1 ≤ 1 + C by linarith))
  · have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    let t : ℝ := ((n : ℝ) / 2) / lam ^ 2
    have ht : 0 ≤ t := div_nonneg (by positivity) (sq_nonneg lam)
    have hsub : {ωz : FieldPair d × Regeneration.CoupledSample d |
        regenerationTime hd lam l 1 ωz.2 =
          (((n : ℝ≥0) * Regeneration.Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)} ⊆
        {ωz | ENNReal.ofReal t < regenerationTime hd lam l 1 ωz.2} := by
      intro ωz hωz
      change ENNReal.ofReal t < _
      rw [hωz, ENNReal.ofReal_lt_iff_lt_toReal ht ENNReal.coe_ne_top]
      have hgrid := regeneration_scaled_grid_time lam hlam.ne' n
      exact (div_lt_iff₀ (sq_pos_of_pos hlam)).mpr (by nlinarith only [hgrid, hnpos])
    have he : -c * lam ^ 2 * t = -(c / 2) * n := by dsimp [t]; field_simp
    calc
      _ ≤ ENNReal.ofReal (C * Real.exp (-c * lam ^ 2 * t)) :=
        (measure_mono hsub).trans (htail t ht)
      _ ≤ _ := by
        rw [he]
        apply ENNReal.ofReal_le_ofReal
        exact mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le

/-- At a fixed construction and with the actual tail constants, the first
cycle has a finite exponential moment uniformly in the environment and force.
This estimate uses no independence and retains the infinite-time branch. -/
theorem regeneration_first_exponentialMoment_le_of_tail {d : ℕ} (hd : 2 ≤ d)
    {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (lam l c C : ℝ)
    (hlam : 0 < lam) (hc : 0 < c) (hC : 0 < C)
    (K : Regeneration.CoupledQuenchedLaws d)
    (hK : Regeneration.HasProbabilityLaws Q.measure K)
    (htail : ∀ t : ℝ, 0 ≤ t →
      Regeneration.annealedCoupledLaw Q.measure K
        {ωz | ENNReal.ofReal t < regenerationTime hd lam l 1 ωz.2} ≤
          ENNReal.ofReal (C * Real.exp (-c * lam ^ 2 * t))) :
    (∫⁻ ωz, regenerationExponentialWeight hd lam l (c / 4) 1 ωz.2
      ∂Regeneration.annealedCoupledLaw Q.measure K) ≤
        ENNReal.ofReal ((1 + C) / (1 - Real.exp (-(c / 4)))) := by
  have hf := regenerationTime_one_ne_top_ae_of_tail hd Q lam l c C hlam hc K htail
  rw [regeneration_exponentialMoment_eq_tsum hd lam l (c / 4) hlam.ne' 1 _ hf]
  have hr : Real.exp (-(c / 4)) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hs := (hasSum_geometric_of_lt_one (Real.exp_pos (-(c / 4))).le hr).mul_left (1 + C)
  calc
    _ ≤ ∑' n : ℕ, ENNReal.ofReal ((1 + C) * Real.exp (-(c / 4)) ^ n) := by
      apply ENNReal.tsum_le_tsum
      intro n
      calc
        _ ≤ ENNReal.ofReal (Real.exp (c / 4 * n)) *
            ENNReal.ofReal ((1 + C) * Real.exp (-(c / 2) * n)) :=
          mul_le_mul_right (regeneration_first_slice_le_of_tail hd Q lam l c C hlam hc hC
            K hK htail n) _
        _ = _ := by
          rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_nat_mul]
          congr 1
          rw [mul_left_comm, ← Real.exp_add]
          congr 2
          ring
    _ = ENNReal.ofReal ((1 + C) / (1 - Real.exp (-(c / 4)))) := by
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hs.summable, hs.tsum_eq]
      rfl

/-- Structural first-cycle witnesses from precisely the approved fixed-scale
GMP input. The scale threshold precedes the scale, which precedes the split
probability, which precedes all moment constants and actual laws/couplings.
No existence or change of the split coupling is asserted. -/
theorem exists_structural_first_cycle_moments (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ) :
    ∃ l₀ : ℝ, 0 < l₀ ∧ r₀ < 2 * l₀ ∧
    ∀ l : ℝ, l₀ ≤ l → ∀ δ : ℝ, 0 < δ → δ < 1 →
    ∃ a M : ℝ, 0 < a ∧ 0 < M ∧
    ∀ (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
      (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
      (hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K),
    ∃ hD : Regeneration.annealedCoupledLaw Q.measure K
        (regenerationNoReturn hd (l / lam)) ≠ 0,
      ENNReal.ofReal (1 / 2 : ℝ) ≤ Regeneration.annealedCoupledLaw Q.measure K
        (regenerationNoReturn hd (l / lam)) ∧
      (∫⁻ ωz, regenerationExponentialWeight hd lam l a 1 ωz.2
        ∂Regeneration.annealedCoupledLaw Q.measure K) ≤ ENNReal.ofReal M ∧
      (∫⁻ ωz, regenerationExponentialWeight hd lam l a 1 ωz.2
        ∂regenerationConditionedLaw hd Q lam l K hK.1 hD) ≤ ENNReal.ofReal M ∧
      (∫⁻ ωz, regenerationExponentialWeight hd lam l a 1 ωz.2
        ∂Regeneration.annealedCoupledLaw Q.measure K) +
      (∫⁻ ωz, regenerationExponentialWeight hd lam l a 1 ωz.2
        ∂regenerationConditionedLaw hd Q lam l K hK.1 hD) ≤ ENNReal.ofReal M ∧
      HasSum (regenerationLatticeMass hd Q lam l K hK.1 hD) 1 ∧
      Summable (fun n : ℕ =>
        regenerationLatticeMass hd Q lam l K hK.1 hD n * Real.exp (a * n)) ∧
      (∑' n : ℕ, regenerationLatticeMass hd Q lam l K hK.1 hD n * Real.exp (a * n)) ≤ M := by
  obtain ⟨l₀, hl₀, hsep, htail⟩ := External.gantert_regeneration_tail d hd Λ₀ r₀
  refine ⟨l₀, hl₀, hsep, ?_⟩
  intro l hl δ hδ₀ hδ₁
  obtain ⟨c, C, hc, hC, ht⟩ := htail l hl δ hδ₀ hδ₁
  let B : ℝ := (1 + C) / (1 - Real.exp (-(c / 4)))
  have hB : 0 < B := div_pos (by linarith)
    (sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith)))
  refine ⟨c / 4, 3 * B, by positivity, by positivity, ?_⟩
  intro Q lam h₀ h₁ P K hK
  obtain ⟨hno, htau⟩ := ht Q lam h₀ h₁ P K hK
  have hD : Regeneration.annealedCoupledLaw Q.measure K
      (regenerationNoReturn hd (l / lam)) ≠ 0 :=
    ne_of_gt ((ENNReal.ofReal_pos.mpr (by norm_num : (0 : ℝ) < 1 / 2)).trans_le hno)
  have hm := regeneration_first_exponentialMoment_le_of_tail hd Q lam l c C h₀ hc hC K hK.1 htau
  have hmD := regenerationConditioned_exponentialMoment_le_of_annealed hd Q lam l (c / 4)
    (1 / 2) B (by norm_num) K hK.1 hD hno 1 hm
  have he : B / (1 / 2) = 2 * B := by ring
  rw [he] at hmD
  have hm' : (∫⁻ ωz, regenerationExponentialWeight hd lam l (c / 4) 1 ωz.2
      ∂Regeneration.annealedCoupledLaw Q.measure K) ≤ ENNReal.ofReal (3 * B) :=
    hm.trans (ENNReal.ofReal_le_ofReal (by linarith))
  have hmD' : (∫⁻ ωz, regenerationExponentialWeight hd lam l (c / 4) 1 ωz.2
      ∂regenerationConditionedLaw hd Q lam l K hK.1 hD) ≤ ENNReal.ofReal (3 * B) :=
    hmD.trans (ENNReal.ofReal_le_ofReal (by linarith))
  have hfin := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hmD'
  refine ⟨hD, hno, hm', hmD', ?_,
    regenerationLatticeMass_hasSum_of_exponentialMoment hd Q lam l (c / 4) h₀.ne'
      K hK.1 hD hfin,
    (regenerationLatticeMass_exponential_hasSum hd Q lam l (c / 4) h₀.ne'
      K hK.1 hD hfin).summable,
    regenerationLatticeMass_exponential_tsum_le hd Q lam l (c / 4) (3 * B) h₀.ne'
      (by positivity) K hK.1 hD hmD'⟩
  calc
    _ ≤ ENNReal.ofReal B + ENNReal.ofReal (2 * B) := add_le_add hm hmD
    _ = ENNReal.ofReal (3 * B) := by
      rw [← ENNReal.ofReal_add hB.le (by positivity)]
      congr 1
      ring

/-- Shrinking an actual regeneration exponent gives a moment close to one.
The original finite moment also supplies a.e. finiteness, so infinity is never
silently mapped to zero by `toReal`. -/
theorem regeneration_exponentialMoment_mul_le {d : ℕ} (hd : 2 ≤ d)
    (lam l b θ M : ℝ) (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1) (hM : 0 ≤ M)
    (j : ℕ) (μ : Measure (FieldPair d × Regeneration.CoupledSample d))
    [IsProbabilityMeasure μ]
    (hm : (∫⁻ ωz, regenerationExponentialWeight hd lam l b j ωz.2 ∂μ) ≤
      ENNReal.ofReal M) :
    (∫⁻ ωz, regenerationExponentialWeight hd lam l (b * θ) j ωz.2 ∂μ) ≤
      ENNReal.ofReal (1 + θ * M) := by
  have hf := regenerationTime_ne_top_ae_of_exponentialMoment hd lam l b j μ
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hm)
  have hp : ∀ᵐ ωz ∂μ, regenerationExponentialWeight hd lam l (b * θ) j ωz.2 ≤
      1 + ENNReal.ofReal θ * regenerationExponentialWeight hd lam l b j ωz.2 := by
    filter_upwards [hf] with ωz hωz
    have hc := convexOn_exp.2 (Set.mem_univ (0 : ℝ))
      (Set.mem_univ (b * lam ^ 2 * (regenerationTime hd lam l j ωz.2).toReal))
      (show 0 ≤ 1 - θ by linarith) hθ₀ (show 1 - θ + θ = 1 by ring)
    simp only [smul_eq_mul, mul_zero, zero_add, Real.exp_zero, mul_one] at hc
    have he : (b * θ) * lam ^ 2 * (regenerationTime hd lam l j ωz.2).toReal =
        θ * (b * lam ^ 2 * (regenerationTime hd lam l j ωz.2).toReal) := by ring
    simp only [regenerationExponentialWeight, if_neg hωz, he]
    calc
      _ ≤ ENNReal.ofReal (1 + θ *
          Real.exp (b * lam ^ 2 * (regenerationTime hd lam l j ωz.2).toReal)) :=
        ENNReal.ofReal_le_ofReal (by linarith only [hc, hθ₀])
      _ = _ := by
        rw [ENNReal.ofReal_add zero_le_one (mul_nonneg hθ₀ (Real.exp_pos _).le), ENNReal.ofReal_one,
          ENNReal.ofReal_mul hθ₀]
  calc
    _ ≤ ∫⁻ ωz, (1 + ENNReal.ofReal θ *
        regenerationExponentialWeight hd lam l b j ωz.2) ∂μ := lintegral_mono_ae hp
    _ = 1 + ENNReal.ofReal θ *
        (∫⁻ ωz, regenerationExponentialWeight hd lam l b j ωz.2 ∂μ) := by
      rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ 1 + ENNReal.ofReal θ * ENNReal.ofReal M :=
      add_le_add_right (mul_le_mul_right hm _) _
    _ = ENNReal.ofReal (1 + θ * M) := by
      rw [← ENNReal.ofReal_mul hθ₀, ENNReal.ofReal_add zero_le_one (mul_nonneg hθ₀ hM), ENNReal.ofReal_one]

/-- For every prescribed positive tolerance, the exponent is chosen before the
law and force so that BOTH actual first-cycle moments are at most `1 + η`.
The same fixed construction is retained throughout. -/
theorem exists_structural_small_first_cycle_moments (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ) :
    ∃ l₀ : ℝ, 0 < l₀ ∧ r₀ < 2 * l₀ ∧
    ∀ l : ℝ, l₀ ≤ l → ∀ δ : ℝ, 0 < δ → δ < 1 →
    ∀ η : ℝ, 0 < η → ∃ a : ℝ, 0 < a ∧
    ∀ (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
      (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
      (hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K),
    ∃ hD : Regeneration.annealedCoupledLaw Q.measure K
        (regenerationNoReturn hd (l / lam)) ≠ 0,
      (∫⁻ ωz, regenerationExponentialWeight hd lam l a 1 ωz.2
        ∂Regeneration.annealedCoupledLaw Q.measure K) ≤ ENNReal.ofReal (1 + η) ∧
      (∫⁻ ωz, regenerationExponentialWeight hd lam l a 1 ωz.2
        ∂regenerationConditionedLaw hd Q lam l K hK.1 hD) ≤ ENNReal.ofReal (1 + η) := by
  obtain ⟨l₀, hl₀, hsep, hmom⟩ := exists_structural_first_cycle_moments d hd Λ₀ r₀
  refine ⟨l₀, hl₀, hsep, ?_⟩
  intro l hl δ hδ₀ hδ₁ η hη
  obtain ⟨b, M, hb, hM, hm⟩ := hmom l hl δ hδ₀ hδ₁
  let θ : ℝ := η / (M + η)
  have hden : 0 < M + η := add_pos hM hη
  have hθ : 0 < θ := div_pos hη hden
  have hθ₁ : θ ≤ 1 := (div_le_one hden).mpr (by linarith)
  have hθη : θ * M ≤ η := by
    dsimp [θ]
    rw [div_mul_eq_mul_div, div_le_iff₀ hden]
    nlinarith only [sq_nonneg η]
  refine ⟨b * θ, mul_pos hb hθ, ?_⟩
  intro Q lam h₀ h₁ P K hK
  obtain ⟨hD, _, hma, hmc, _⟩ := hm Q lam h₀ h₁ P K hK
  letI := Regeneration.annealedCoupledLaw_isProbabilityMeasure Q.measure K hK.1
  letI := regenerationConditionedLaw_probability hd Q lam l K hK.1 hD
  refine ⟨hD, ?_, ?_⟩
  · exact (regeneration_exponentialMoment_mul_le hd lam l b θ M hθ.le hθ₁ hM.le 1 _ hma).trans
      (ENNReal.ofReal_le_ofReal (by linarith only [hθη]))
  · exact (regeneration_exponentialMoment_mul_le hd lam l b θ M hθ.le hθ₁ hM.le 1 _ hmc).trans
      (ENNReal.ofReal_le_ofReal (by linarith only [hθη]))

end EinsteinFull.Work.W5
