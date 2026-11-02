import EinsteinFull.Blueprint.G1.node_rt_u3A_local_u2D_mixing_u23_fixed_u2D_radius
import EinsteinFull.Blueprint.G1.Proofs.SbxS5PhaseError
import EinsteinFull.Blueprint.G1.Proofs.SbxS2KmDecomp
import EinsteinFull.Blueprint.G1.Proofs.S3MRenewalObs
import EinsteinFull.Blueprint.Foundation.node_app_u3A_regen_u2D_tails

open MeasureTheory
open scoped NNReal ENNReal Topology

namespace EinsteinFull.Blueprint

open EinsteinRelation

/-- Uniform scalar fixed-radius estimates, retaining arbitrary remainder
prefactors and the entire infinite centered tail. -/
theorem sbxS4_fixedRadius_scalar_uniform (C₁ c₁ b : ℝ)
    (hC₁ : 0 < C₁) (hc₁ : 0 < c₁) (hb : 0 < b) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    ∀ (pn : ℕ → ℝ) (mean : ℝ), pn 0 = 0 →
    (∀ n : ℕ, |(∑' a, latticeConvolutionPower pn a n) - mean⁻¹| ≤
      C₁ * Real.exp (-c₁ * n)) →
    ∀ (h r hF rF : ℕ → ℝ) (q : ℕ → ℝ) (R Rf Bq : ℝ),
    0 ≤ R → 0 ≤ Rf → 0 ≤ Bq →
    (∀ j, h j = r j + ∑ n ∈ Finset.range (j + 1), pn n * h (j - n)) →
    (∀ j, hF j = rF j + ∑ n ∈ Finset.range (j + 1), q n * h (j - n)) →
    (∀ j, |r j| ≤ R * Real.exp (-b * j)) →
    (∀ j, |rF j| ≤ Rf * Real.exp (-b * j)) →
    (∀ n, |q n| ≤ Bq * Real.exp (-b * n)) →
    Summable q → (∑' n, q n) = 0 →
    let H := mean⁻¹ * ∑' j : ℕ, r j
    Summable r ∧ |H| ≤ C * R ∧ ∀ j : ℕ,
      |h j - H| ≤ C * R * Real.exp (-c * j) ∧
      hF j = rF j +
        (∑ n ∈ Finset.range (j + 1), q n * (h (j - n) - H)) -
        H * ∑' n : ℕ, q (j + 1 + n) ∧
      |hF j| ≤ C * (Rf + Bq * R) * Real.exp (-c * j) := by
  obtain ⟨a, A, ha, hA, hest⟩ := renewal_estimates_uniform C₁ c₁ b hC₁ hc₁ hb
  let D := (1 + 2 / min b a) + (1 - Real.exp (-b))⁻¹
  have hden : 0 < 1 - Real.exp (-b) :=
    sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_neg_of_pos hb))
  have hD : 0 < D := by dsimp only [D]; positivity
  let c := min b a / 2
  let C := 1 + A + A * D
  have hc : 0 < c := half_pos (lt_min hb ha)
  have hC : 0 < C := by dsimp only [C]; positivity
  have hAC : A ≤ C := by dsimp only [C]; linarith only [mul_pos hA hD]
  have h1C : 1 ≤ C := by dsimp only [C]; linarith only [hA, mul_pos hA hD]
  have hADC : A * D ≤ C := by dsimp only [C]; linarith only [hA]
  have hca : c ≤ a := by dsimp only [c]; linarith only [min_le_right b a, ha]
  have hcb : c ≤ b := by dsimp only [c]; linarith only [min_le_left b a, hb]
  refine ⟨c, C, hc, hC, ?_⟩
  intro pn mean hp hU h r hF rF q R Rf Bq hR hRf hBq hh hhF hr hrF hq hqs hq0
  have hU0 : (∑' a, latticeConvolutionPower pn a 0) = 1 := by
    rw [tsum_lcp_eq_sum pn hp 0 1 (by omega)]
    simp only [Finset.sum_range_one, latticeConvolutionPower, ite_true]
  obtain ⟨hrs, hH, herr⟩ := hest _ mean hU0 hU h r R hR hr
    (renewal_conv pn h r _ (U_recursion pn hp) hh)
  dsimp only
  refine ⟨hrs, hH.trans (mul_le_mul_of_nonneg_right hAC hR), ?_⟩
  intro j
  have hexa : Real.exp (-a * j) ≤ Real.exp (-c * j) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (neg_le_neg hca) (Nat.cast_nonneg j))
  have hexb : Real.exp (-b * j) ≤ Real.exp (-c * j) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (neg_le_neg hcb) (Nat.cast_nonneg j))
  have hid : hF j = rF j +
      (∑ n ∈ Finset.range (j + 1), q n * (h (j - n) - mean⁻¹ * ∑' i, r i)) -
        (mean⁻¹ * ∑' i, r i) * ∑' n, q (j + 1 + n) := by
    rw [hhF j, sbxS2_centered_convolution q (fun n => h (j - n)) _ j hqs hq0,
      add_sub_assoc]
  refine ⟨(herr j).trans (mul_le_mul
    (mul_le_mul_of_nonneg_right hAC hR) hexa (Real.exp_pos _).le
      (mul_nonneg hC.le hR)), hid, ?_⟩
  have hdec := sbxS2_centered_convolution_decay q h (mean⁻¹ * ∑' i, r i)
    Bq (A * R) b a hBq (mul_nonneg hA.le hR) hb ha hq herr hH j
  calc |hF j| ≤ |rF j| +
      |(∑ n ∈ Finset.range (j + 1), q n * (h (j - n) - mean⁻¹ * ∑' i, r i)) -
        (mean⁻¹ * ∑' i, r i) * ∑' n, q (j + 1 + n)| := by
          rw [hid, add_sub_assoc]; exact abs_add_le _ _
    _ ≤ Rf * Real.exp (-b * j) + Bq * (A * R) * D * Real.exp (-c * j) :=
      add_le_add (hrF j) hdec
    _ ≤ Rf * Real.exp (-c * j) + Bq * (A * R) * D * Real.exp (-c * j) :=
      add_le_add (mul_le_mul_of_nonneg_left hexb hRf) le_rfl
    _ = (Rf + A * D * (Bq * R)) * Real.exp (-c * j) := by ring
    _ ≤ (C * Rf + C * (Bq * R)) * Real.exp (-c * j) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      exact add_le_add (by nlinarith only [h1C, hRf])
        (mul_le_mul_of_nonneg_right hADC (mul_nonneg hBq hR))
    _ = C * (Rf + Bq * R) * Real.exp (-c * j) := by ring

/-- The entire universal scalar clause of the fixed-radius statement follows
from the supplied renewal statement, with its structural threshold unchanged.
This theorem does not assert the full-Lp observation clause. -/
theorem sbxS4_fixedRadius_scalar_of_renewal (hren : node_rt_u3A_renewalStmt) :
    ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ),
    ∃ l₀ : ℝ, 0 < l₀ ∧ r₀ < 2 * l₀ ∧
    ∀ l : ℝ, l₀ ≤ l → ∀ δ : ℝ, 0 < δ → δ < 1 →
    ∀ b : ℝ, 0 < b →
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    ∀ (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
      (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
      (hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K)
      (hD : Regeneration.annealedCoupledLaw Q.measure K
        (regenerationNoReturn hd (l / lam)) ≠ 0),
    let Δ := Regeneration.Renewal.regenDelta lam
    let pn := regenerationLatticeMass hd Q lam l K hK.1 hD
    let mean := ∑' n : ℕ, (n : ℝ) * pn n
    ∀ (s : ℝ≥0), s < Δ → ∀ (h r hF rF : ℕ → ℝ) (q : ℕ → ℝ)
      (R Rf Bq : ℝ), 0 ≤ R → 0 ≤ Rf → 0 ≤ Bq →
    (∀ j, h j = r j + ∑ n ∈ Finset.range (j + 1), pn n * h (j - n)) →
    (∀ j, hF j = rF j + ∑ n ∈ Finset.range (j + 1), q n * h (j - n)) →
    (∀ j, |r j| ≤ R * Real.exp (-b * j)) →
    (∀ j, |rF j| ≤ Rf * Real.exp (-b * j)) →
    (∀ n, |q n| ≤ Bq * Real.exp (-b * n)) →
    Summable q → (∑' n, q n) = 0 →
    let H := mean⁻¹ * ∑' j : ℕ, r j
    Summable r ∧ |H| ≤ C * R ∧ ∀ j : ℕ,
      |h j - H| ≤ C * R * Real.exp (-c * j) ∧
      hF j = rF j +
        (∑ n ∈ Finset.range (j + 1), q n * (h (j - n) - H)) -
        H * ∑' n : ℕ, q (j + 1 + n) ∧
      |hF j| ≤ C * (Rf + Bq * R) * Real.exp (-c * j) := by
  intro d hd Λ₀ r₀
  obtain ⟨l₀, hl₀, hsep, hren'⟩ := hren d hd Λ₀ r₀
  refine ⟨l₀, hl₀, hsep, ?_⟩
  intro l hl δ hδ₀ hδ₁ b hb
  obtain ⟨c₁, C₁, a, M, hc₁, hC₁, _, _, hdata⟩ := hren' l hl δ hδ₀ hδ₁
  obtain ⟨c, C, hc, hC, hscalar⟩ :=
    sbxS4_fixedRadius_scalar_uniform C₁ c₁ b hC₁ hc₁ hb
  refine ⟨c, C, hc, hC, ?_⟩
  intro Q lam h₀ h₁ P K hK hD
  let pn := regenerationLatticeMass hd Q lam l K hK.1 hD
  have hp : pn 0 = 0 :=
    regenerationLatticeMass_zero hd Q lam l h₀ (hl₀.trans_le hl) K hK.1 hD
  have hmean : (∑' n : ℕ, pn n * (n : ℝ)) = ∑' n : ℕ, (n : ℝ) * pn n :=
    tsum_congr (fun n => mul_comm _ _)
  have hU : ∀ n : ℕ, |(∑' j : ℕ, latticeConvolutionPower pn j n) -
      (∑' n : ℕ, (n : ℝ) * pn n)⁻¹| ≤ C₁ * Real.exp (-c₁ * n) := by
    have h := (hdata Q lam h₀ h₁ P K hK hD).1
    change ∀ n : ℕ, |(∑' j : ℕ, latticeConvolutionPower pn j n) -
      (∑' n : ℕ, pn n * (n : ℝ))⁻¹| ≤ C₁ * Real.exp (-c₁ * n) at h
    rwa [hmean] at h
  dsimp only
  intro s _hs
  exact hscalar pn _ hp hU

/-- The moment clauses already contained in the supplied renewal statement
give the literal many-cycle moment statement, with no additional input. -/
theorem sbxS4_manyCycleMoment_of_renewal (hren : node_rt_u3A_renewalStmt) :
    node_rt_u3A_many_u2D_cycle_u2D_momentStmt := by
  intro d hd Λ₀ r₀
  obtain ⟨l₀, hl₀, hsep, hren'⟩ := hren d hd Λ₀ r₀
  refine ⟨l₀, hl₀, hsep, ?_⟩
  intro l hl δ hδ₀ hδ₁
  obtain ⟨c, C, a, M, _hc, hC, ha, hM, hdata⟩ := hren' l hl δ hδ₀ hδ₁
  refine ⟨a, M, C, ha, hM, hC, ?_⟩
  intro Q lam h₀ h₁ P K hK hD
  exact (hdata Q lam h₀ h₁ P K hK hD).2

/-- The actual first-cycle coefficients are centered and decay in the exact
L² norm used by the fixed-radius statement. Only the renewal input is needed;
the threshold precedes the scale and the moment rate. -/
theorem sbxS4_fixedRadius_centered_slices_of_renewal (hren : node_rt_u3A_renewalStmt) :
    ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ),
    ∃ l₀ : ℝ, 0 < l₀ ∧ r₀ < 2 * l₀ ∧
    ∀ l : ℝ, l₀ ≤ l → ∀ δ : ℝ, 0 < δ → δ < 1 →
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    ∀ (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
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
        (eLpNorm F 2 (reducedLaw Q)).toReal := by
  intro d hd Λ₀ r₀
  have hmany := sbxS4_manyCycleMoment_of_renewal hren
  obtain ⟨lS, hlS, hsepS, hsum⟩ :=
    sbxS2_centered_slices_of_manyCycleMoment hmany d hd Λ₀ r₀
  obtain ⟨lD, hlD, _hsepD, hdec⟩ :=
    sbxS2_slice_decay_of_manyCycleMoment hmany d hd Λ₀ r₀
  refine ⟨max lS lD, hlS.trans_le (le_max_left _ _),
    hsepS.trans_le (by linarith only [le_max_left lS lD]), ?_⟩
  intro l hl δ hδ₀ hδ₁
  obtain ⟨a, A, ha, _hA, hdec'⟩ :=
    hdec l ((le_max_right _ _).trans hl) δ hδ₀ hδ₁
  refine ⟨a / 2, Real.exp (A / 2), half_pos ha, Real.exp_pos _, ?_⟩
  intro Q lam h₀ h₁ P K hK hD p hp F hF hFp hzero
  obtain ⟨hqs, hq0⟩ := hsum l ((le_max_left _ _).trans hl) δ hδ₀ hδ₁
    Q lam h₀ h₁ P K hK hD p ((by norm_num : (1 : ℝ) ≤ 2).trans hp)
      F hF hFp hzero 1
  refine ⟨hqs, hq0, ?_⟩
  intro n
  let := reducedLaw_probability Q
  have hp2 : (2 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    simpa only [ENNReal.ofReal_ofNat] using ENNReal.ofReal_le_ofReal hp
  have hFn : MemLp F (ENNReal.ofReal 2) (reducedLaw Q) := by
    simpa only [ENNReal.ofReal_ofNat] using hFp.mono_exponent hp2
  have hbound := hdec' Q lam h₀ h₁ P K hK hD 2 le_rfl F hF hFn 1 le_rfl n
  have hexp : Real.exp ((A * (1 : ℕ) - a * n) / 2) =
      Real.exp (A / 2) * Real.exp (-(a / 2) * n) := by
    rw [← Real.exp_add]
    congr 1
    push_cast
    ring
  simpa only [ENNReal.ofReal_ofNat, hexp] using hbound

/-- Raising the observables to higher powers allows the decay rate to be
chosen after a single structural threshold. This uses the literal remainder
dependency for both actual path laws and introduces no semigroup premise. -/
theorem sbxS4_remainder_moment_variable_rate_both
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
    0 ≤ J → ∀ μ ∈ ({Regeneration.annealedCoupledLaw Q.measure K,
      regenerationConditionedLaw hd Q lam l K hK.1 hD} :
        Set (Measure (FieldPair d × Regeneration.CoupledSample d))),
    μ E ≤ ENNReal.ofReal (Real.exp (J - a * (lam ^ 2 * (t : ℝ)))) →
    IntegrableOn (fun ωz => F (reduce ωz.1) *
      G (translate (ωz.2.1 t) (reduce ωz.1))) E μ ∧
    |∫ ωz in E, F (reduce ωz.1) * G (translate (ωz.2.1 t) (reduce ωz.1)) ∂μ| ≤
      C * Real.exp (C * J - c * (lam ^ 2 * (t : ℝ))) *
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
  refine ⟨p₀ * r, c, C,
    hp₀.trans (le_mul_of_one_le_right (by linarith only [hp₀]) hr₁.le), hc, hC, ?_⟩
  intro Q lam h₀ h₁ l δ hl hδ₀ hδ₁ P K hK hD F G hF hG hFp hGp J t E hJ μ hμ hprob
  let f := fun ωz : FieldPair d × Regeneration.CoupledSample d =>
    F (reduce ωz.1) * G (translate (ωz.2.1 t) (reduce ωz.1))
  have ht : Measurable (fun ωz : FieldPair d × Regeneration.CoupledSample d =>
      ωz.2.1 t) := (continuous_eval_const t).measurable.comp measurable_snd.fst
  have hred : Measurable (fun ωz : FieldPair d × Regeneration.CoupledSample d =>
      reduce ωz.1) := Probability.measurable_reduce.comp measurable_fst
  have hfm : Measurable f := (hF.comp hred).mul
    (hG.comp (Probability.continuous_translate.measurable.comp (ht.prodMk hred)))
  have hpower := hmoment r hr₀ Q lam h₀ h₁ l δ hl hδ₀ hδ₁ P K hK hD
    F G hF hG hFp hGp t μ hμ
  have hμprob : IsProbabilityMeasure μ := by
    rcases hμ with rfl | hμ
    · exact Regeneration.annealedCoupledLaw_isProbabilityMeasure Q.measure K hK.1
    · rw [Set.mem_singleton_iff] at hμ
      rw [hμ]
      exact regenerationConditionedLaw_probability hd Q lam l K hK.1 hD
  let := hμprob
  have hfr : MemLp f (ENNReal.ofReal r) μ := by
    apply (integrable_norm_rpow_iff hfm.aestronglyMeasurable
      (ENNReal.ofReal_ne_zero_iff.mpr hr₀) ENNReal.ofReal_ne_top).mp
    simpa only [ENNReal.toReal_ofReal hr₀.le] using hpower.1
  have hri : (1 : ℝ≥0∞) ≤ ENNReal.ofReal r := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hr₁.le
  refine ⟨(hfr.integrable hri).integrableOn, ?_⟩
  have hb := sbxS2_setIntegral_abs_le_moment μ f hfm.aestronglyMeasurable E r
    (D * Real.exp (D * (lam ^ 2 * (t : ℝ))) *
      (eLpNorm F (ENNReal.ofReal (p₀ * r)) (reducedLaw Q)).toReal ^ r *
      (eLpNorm G (ENNReal.ofReal (p₀ * r)) (reducedLaw Q)).toReal ^ r)
    (Real.exp (J - a * (lam ^ 2 * (t : ℝ)))) hr₁ hpower.1
    (by simpa only [mul_assoc] using hpower.2) (Real.exp_pos _).le hprob
  exact hb.trans (hscalar J (lam ^ 2 * (t : ℝ)) _ _ hJ
    (by positivity) ENNReal.toReal_nonneg ENNReal.toReal_nonneg)

/-- Actual first-cycle remainder decay on both path laws. The structural
threshold is fixed before the scale and coin probability; the observable
exponent is chosen afterwards, using the renewal rate available at that scale. -/
theorem sbxS4_first_cycle_remainders_of_renewal
    (hren : node_rt_u3A_renewalStmt) (hrem : node_rt_u3A_remainder_u2D_momentStmt) :
    ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ),
    ∃ l₀ : ℝ, 0 < l₀ ∧ r₀ < 2 * l₀ ∧
    ∀ l : ℝ, l₀ ≤ l → ∀ δ : ℝ, 0 < δ → δ < 1 →
    ∃ p c C : ℝ, 2 ≤ p ∧ 0 < c ∧ 0 < C ∧
    ∀ (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
      (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
      (hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K)
      (hD : Regeneration.annealedCoupledLaw Q.measure K
        (regenerationNoReturn hd (l / lam)) ≠ 0),
    ∀ F G : FieldPair d → ℝ, Measurable F → Measurable G →
      MemLp F (ENNReal.ofReal p) (reducedLaw Q) →
      MemLp G (ENNReal.ofReal p) (reducedLaw Q) →
    ∀ t : ℝ≥0, ∀ μ ∈ ({Regeneration.annealedCoupledLaw Q.measure K,
      regenerationConditionedLaw hd Q lam l K hK.1 hD} :
        Set (Measure (FieldPair d × Regeneration.CoupledSample d))),
    IntegrableOn (fun ωz => F (reduce ωz.1) *
      G (translate (ωz.2.1 t) (reduce ωz.1)))
      {ωz | (t : ℝ≥0∞) < regenerationTime hd lam l 1 ωz.2} μ ∧
    |∫ ωz in {ωz | (t : ℝ≥0∞) < regenerationTime hd lam l 1 ωz.2},
      F (reduce ωz.1) * G (translate (ωz.2.1 t) (reduce ωz.1)) ∂μ| ≤
      C * Real.exp (-c * lam ^ 2 * (t : ℝ)) *
        (eLpNorm F (ENNReal.ofReal p) (reducedLaw Q)).toReal *
        (eLpNorm G (ENNReal.ofReal p) (reducedLaw Q)).toReal := by
  intro d hd Λ₀ r₀
  obtain ⟨lR, hlR, hsepR, hren'⟩ := hren d hd Λ₀ r₀
  obtain ⟨lV, _hlV, _hsepV, hvar⟩ :=
    sbxS4_remainder_moment_variable_rate_both hrem d hd Λ₀ r₀
  refine ⟨max lR lV, hlR.trans_le (le_max_left _ _),
    hsepR.trans_le (by linarith only [le_max_left lR lV]), ?_⟩
  intro l hl δ hδ₀ hδ₁
  obtain ⟨c₁, C₁, a, M, _hc₁, _hC₁, ha, _hM, hdata⟩ :=
    hren' l ((le_max_left _ _).trans hl) δ hδ₀ hδ₁
  obtain ⟨p, c, C, hp, hc, hC, hvar'⟩ := hvar a ha
  let B := max 1 (max M (C₁ * M))
  have hB1 : 1 ≤ B := le_max_left _ _
  have hB : 0 < B := zero_lt_one.trans_le hB1
  let D := C * Real.exp (C * Real.log B)
  have hD : 0 < D := mul_pos hC (Real.exp_pos _)
  refine ⟨p, c, D, hp, hc, hD, ?_⟩
  intro Q lam h₀ h₁ P K hK hDnonzero F G hF hG hFp hGp t μ hμ
  have hmom : (∫⁻ ωz, if regenerationTime hd lam l 1 ωz.2 = ⊤ then ⊤ else
      ENNReal.ofReal (Real.exp (a * lam ^ 2 *
        (regenerationTime hd lam l 1 ωz.2).toReal)) ∂μ) ≤ ENNReal.ofReal B := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hμ
    rcases hμ with rfl | rfl
    · exact ((hdata Q lam h₀ h₁ P K hK hDnonzero).2.2 1).trans
        (ENNReal.ofReal_le_ofReal (by
          simpa only [pow_one] using
            (le_max_right M (C₁ * M)).trans (le_max_right 1 (max M (C₁ * M)))))
    · exact ((hdata Q lam h₀ h₁ P K hK hDnonzero).2.1 1).trans
        (ENNReal.ofReal_le_ofReal (by
          simpa only [pow_one] using
            (le_max_left M (C₁ * M)).trans (le_max_right 1 (max M (C₁ * M)))))
  have hTm : Measurable (fun ωz : FieldPair d × Regeneration.CoupledSample d =>
      regenerationTime hd lam l 1 ωz.2) :=
    (Regeneration.measurable_regenerationTime (Regeneration.Renewal.regenDelta lam) lam
      (l / lam) (Regeneration.Renewal.forceCoord hd) 1).comp measurable_snd
  have htail := exponential_time_tail μ _ hTm (a * lam ^ 2) B (by positivity) t hmom
  have hprob : μ {ωz | (t : ℝ≥0∞) < regenerationTime hd lam l 1 ωz.2} ≤
      ENNReal.ofReal (Real.exp (Real.log B - a * (lam ^ 2 * (t : ℝ)))) := by
    apply htail.trans
    apply ENNReal.ofReal_le_ofReal
    rw [sub_eq_add_neg, Real.exp_add, Real.exp_log hB]
    have he : -(a * lam ^ 2) * (t : ℝ) = -(a * (lam ^ 2 * (t : ℝ))) := by ring
    simpa only [he] using (le_refl (B * Real.exp (-(a * (lam ^ 2 * (t : ℝ))))))
  have hout := hvar' Q lam h₀ h₁ l δ ((le_max_right _ _).trans hl) hδ₀ hδ₁
    P K hK hDnonzero F G hF hG hFp hGp (Real.log B) t _
      (Real.log_nonneg hB1) μ hμ hprob
  refine ⟨hout.1, ?_⟩
  have he : C * Real.exp (C * Real.log B - c * (lam ^ 2 * (t : ℝ))) =
      D * Real.exp (-c * lam ^ 2 * (t : ℝ)) := by
    dsimp only [D]
    rw [sub_eq_add_neg, Real.exp_add]
    have he : -(c * (lam ^ 2 * (t : ℝ))) = -c * lam ^ 2 * (t : ℝ) := by ring
    rw [he]
    ring
  simpa only [he] using hout.2

/-- At radius `R`, no backtracking alone makes the full observation readable
from the future record. No positive regeneration count is needed. -/
theorem sbxS4_Phi0_record {d : ℕ} (Δ : ℝ≥0) (lam R : ℝ) (i : Fin d)
    (D : (Regeneration.FutureHalfSpace d i R → Mat d × ℝ) →
      C(Regeneration.FutureHalfSpace d i R, Mat d × ℝ))
    (hDr : ∀ f : C(Regeneration.FutureHalfSpace d i R, Mat d × ℝ), D (fun x => f x) = f)
    (G : FieldPair d → ℝ)
    (hG : Measurable[localSigma {x : Vec d | euclideanNorm x < R}] G)
    (ω : FieldPair d) (z : Regeneration.CoupledSample d) (a u : ℝ≥0)
    (hNB : Regeneration.NoBacktracking R (Regeneration.pathTimeShift z.1 a) i) :
    PhiM Δ lam R i D G 0 u (Regeneration.futureRecord Δ R ω z i a) =
      G (translate (z.1 (a + u)) (reduce ω)) := by
  unfold PhiM
  simp only [Regeneration.regenerationTime, zero_le, ↓reduceIte]
  apply observation_record_eq Δ R R i D hDr G hG ω z a u
  intro x hx
  have hpath := coord_gt_of_noBacktracking z.1 i R a u hNB
  have hcoord := (abs_lt.mp
    ((Regeneration.coordinate_abs_le_euclideanNorm x i).trans_lt hx)).1
  simp only [Pi.add_apply, Pi.sub_apply]
  linarith

/-- Bounded full observations factor on each first-cycle slice under either
actual law, using only the authorized environmental factorization statement. -/
theorem sbxS4_bounded_first_cycle_slice
    (hfact : node_rt_u3A_factorizationStmt)
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1) (l δ : ℝ)
    (hl : 0 < l) (hsep : r₀ < 2 * l) (hδ₀ : 0 < δ) (hδ₁ : δ < 1)
    (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K)
    (hD : Regeneration.annealedCoupledLaw Q.measure K
      (regenerationNoReturn hd (l / lam)) ≠ 0)
    (F G : FieldPair d → ℝ)
    (hF : Measurable[localSigma {x : Vec d | euclideanNorm x < l / lam}] F)
    (hG : Measurable[localSigma {x : Vec d | euclideanNorm x < l / lam}] G)
    (hbF : Regeneration.BoundedRealTest F) (hbG : Regeneration.BoundedRealTest G)
    (n : ℕ) (u : ℝ≥0) (μ : Measure (FieldPair d × Regeneration.CoupledSample d))
    (hμ : μ ∈ ({Regeneration.annealedCoupledLaw Q.measure K,
      regenerationConditionedLaw hd Q lam l K hK.1 hD} :
        Set (Measure (FieldPair d × Regeneration.CoupledSample d)))) :
    (∫ q in {q | regenerationTime hd lam l 1 q.2 =
        (((n : ℝ≥0) * Regeneration.Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)},
      F (reduce q.1) *
        G (translate (q.2.1 ((n : ℝ≥0) * Regeneration.Renewal.regenDelta lam + u))
          (reduce q.1)) ∂μ) =
    (∫ q in {q | regenerationTime hd lam l 1 q.2 =
        (((n : ℝ≥0) * Regeneration.Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)},
      F (reduce q.1) ∂μ) *
    ∫ q, G (translate (q.2.1 u) (reduce q.1))
      ∂regenerationConditionedLaw hd Q lam l K hK.1 hD := by
  let Δ := Regeneration.Renewal.regenDelta lam
  let ν := regenerationConditionedLaw hd Q lam l K hK.1 hD
  have hΔ : 0 < Δ := Real.toNNReal_pos.mpr (inv_pos.mpr (sq_pos_of_pos h₀))
  obtain ⟨D, hDm, hDr⟩ :=
    Probability.exists_future_halfSpace_decoder (Regeneration.Renewal.forceCoord hd) (l / lam)
  let Φ := PhiM Δ lam (l / lam) (Regeneration.Renewal.forceCoord hd) D G 0 u
  have hrec0 : ∀ᵐ q ∂ν, Φ (regenerationRecord hd lam l 0 q) =
      G (translate (q.2.1 u) (reduce q.1)) := by
    have hNB : ∀ᵐ q ∂ν,
        Regeneration.NoBacktracking (l / lam) q.2.1 (Regeneration.Renewal.forceCoord hd) :=
      ProbabilityTheory.ae_cond_mem
        ((Regeneration.measurableSet_NoBacktracking (l / lam)
          (Regeneration.Renewal.forceCoord hd)).preimage measurable_snd.fst)
    filter_upwards [hNB] with q hq
    have hrec : regenerationRecord hd lam l 0 q = Regeneration.futureRecord Δ (l / lam)
        q.1 q.2 (Regeneration.Renewal.forceCoord hd) 0 := by
      unfold regenerationRecord Regeneration.Renewal.cycleRecord
      rfl
    rw [hrec]
    have he := sbxS4_Phi0_record Δ lam (l / lam) _ D hDr G hG q.1 q.2 0 u
      (noBacktracking_pathTimeShift_zero _ _ _ hq)
    simpa only [zero_add] using he
  have hrec1 : ∀ q : FieldPair d × Regeneration.CoupledSample d,
      regenerationTime hd lam l 1 q.2 = (((n : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞) →
      Φ (regenerationRecord hd lam l 1 q) =
        G (translate (q.2.1 ((n : ℝ≥0) * Δ + u)) (reduce q.1)) := by
    intro q hq
    have hτ : Regeneration.regenerationTime Δ lam (l / lam) q.2
        (Regeneration.Renewal.forceCoord hd) 1 = (((n : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞) := hq
    have hNB := Regeneration.regenerationTime_succ_noBacktracking Δ hΔ lam (l / lam)
      q.2 (Regeneration.Renewal.forceCoord hd) 0
      (by rw [hτ]; exact ENNReal.coe_ne_top)
    rw [hτ, ENNReal.toNNReal_coe] at hNB
    have hrec : regenerationRecord hd lam l 1 q = Regeneration.futureRecord Δ (l / lam)
        q.1 q.2 (Regeneration.Renewal.forceCoord hd) ((n : ℝ≥0) * Δ) := by
      unfold regenerationRecord Regeneration.Renewal.cycleRecord
      rw [hτ, ENNReal.toNNReal_coe]
    rw [hrec]
    exact sbxS4_Phi0_record Δ lam (l / lam) _ D hDr G hG q.1 q.2 _ u hNB
  have hfa := (hfact d hd Λ₀ r₀ Q lam h₀ h₁ l δ hl hsep hδ₀ hδ₁ P K hK hD).1
    (fun ω => F (reduce ω)) (hF.comp (Probability.measurable_reduce_local _))
    (by obtain ⟨C, hC⟩ := hbF; exact ⟨C, fun ω => hC (reduce ω)⟩)
    Φ (measurable_PhiM Δ lam (l / lam) (l / lam) _ D hDm G hG 0 u)
    (boundedRealTest_PhiM Δ lam (l / lam) _ D G hbG 0 u) n μ hμ
  have hTm : Measurable (fun q : FieldPair d × Regeneration.CoupledSample d =>
      regenerationTime hd lam l 1 q.2) :=
    (Regeneration.measurable_regenerationTime Δ lam (l / lam)
      (Regeneration.Renewal.forceCoord hd) 1).comp measurable_snd
  calc
    _ = (∫ q in {q | regenerationTime hd lam l 1 q.2 =
          (((n : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞)},
        F (reduce q.1) * Φ (regenerationRecord hd lam l 1 q) ∂μ) := by
      apply setIntegral_congr_ae (measurableSet_eq_fun hTm measurable_const)
      exact ae_of_all _ fun q hq => congrArg (F (reduce q.1) * ·) (hrec1 q hq).symm
    _ = _ := by rw [hfa, integral_congr_ae hrec0]

/-- Simultaneous symmetric truncations of both factors have the original
integrable product as their dominator. -/
theorem sbxS4_tendsto_setIntegral_mul_clamps {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (f g : α → ℝ) (hf : Measurable f) (hg : Measurable g)
    (hfg : Integrable (fun x => f x * g x) μ) (s : Set α) :
    Filter.Tendsto (fun n : ℕ => ∫ x in s,
      max (-(n : ℝ)) (min (n : ℝ) (f x)) *
        max (-(n : ℝ)) (min (n : ℝ) (g x)) ∂μ)
      Filter.atTop (𝓝 (∫ x in s, f x * g x ∂μ)) := by
  have habs (x : ℝ) (n : ℕ) : |max (-(n : ℝ)) (min (n : ℝ) x)| ≤ |x| := by
    refine abs_le.mpr ⟨?_, ?_⟩
    · exact le_trans (le_min ((neg_nonpos.mpr (abs_nonneg x)).trans (Nat.cast_nonneg n))
        (neg_abs_le x)) (le_max_right _ _)
    · exact max_le ((neg_nonpos.mpr (Nat.cast_nonneg n)).trans (abs_nonneg x))
        ((min_le_right _ _).trans (le_abs_self _))
  have ht (x : ℝ) : Filter.Tendsto
      (fun n : ℕ => max (-(n : ℝ)) (min (n : ℝ) x)) Filter.atTop (𝓝 x) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [(tendsto_natCast_atTop_atTop :
      Filter.Tendsto (fun n : ℕ => (n : ℝ)) Filter.atTop Filter.atTop).eventually
        (Filter.eventually_ge_atTop |x|)] with n hn
    rw [min_eq_right ((le_abs_self _).trans hn), max_eq_right]
    exact (neg_le_neg hn).trans (neg_abs_le _)
  apply tendsto_integral_of_dominated_convergence (fun x => |f x * g x|)
  · intro n
    exact ((measurable_const.max (measurable_const.min hf)).mul
      (measurable_const.max (measurable_const.min hg))).aestronglyMeasurable
  · exact hfg.integrableOn.abs
  · intro n
    exact ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_mul, abs_mul]
      exact mul_le_mul (habs (f x) n) (habs (g x) n) (abs_nonneg _) (abs_nonneg _)
  · exact ae_of_all _ fun x => (ht (f x)).mul (ht (g x))

/-- The full first-cycle slice identity extends to integrable observations
by simultaneous clamping, with no boundedness assumption on either test. -/
theorem sbxS4_first_cycle_slice_of_integrable
    (hfact : node_rt_u3A_factorizationStmt)
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1) (l δ : ℝ)
    (hl : 0 < l) (hsep : r₀ < 2 * l) (hδ₀ : 0 < δ) (hδ₁ : δ < 1)
    (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K)
    (hD : Regeneration.annealedCoupledLaw Q.measure K
      (regenerationNoReturn hd (l / lam)) ≠ 0)
    (F G : FieldPair d → ℝ)
    (hF : Measurable[localSigma {x : Vec d | euclideanNorm x < l / lam}] F)
    (hG : Measurable[localSigma {x : Vec d | euclideanNorm x < l / lam}] G)
    (n : ℕ) (u : ℝ≥0) (μ : Measure (FieldPair d × Regeneration.CoupledSample d))
    (hμ : μ ∈ ({Regeneration.annealedCoupledLaw Q.measure K,
      regenerationConditionedLaw hd Q lam l K hK.1 hD} :
        Set (Measure (FieldPair d × Regeneration.CoupledSample d))))
    (hiF : Integrable (fun q => F (reduce q.1)) μ)
    (hiFG : Integrable (fun q => F (reduce q.1) *
      G (translate (q.2.1 ((n : ℝ≥0) * Regeneration.Renewal.regenDelta lam + u))
        (reduce q.1))) μ)
    (hiG : Integrable (fun q : FieldPair d × Regeneration.CoupledSample d =>
      G (translate (q.2.1 u) (reduce q.1)))
        (regenerationConditionedLaw hd Q lam l K hK.1 hD)) :
    (∫ q in {q | regenerationTime hd lam l 1 q.2 =
        (((n : ℝ≥0) * Regeneration.Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)},
      F (reduce q.1) *
        G (translate (q.2.1 ((n : ℝ≥0) * Regeneration.Renewal.regenDelta lam + u))
          (reduce q.1)) ∂μ) =
    (∫ q in {q | regenerationTime hd lam l 1 q.2 =
        (((n : ℝ≥0) * Regeneration.Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)},
      F (reduce q.1) ∂μ) *
    ∫ q, G (translate (q.2.1 u) (reduce q.1))
      ∂regenerationConditionedLaw hd Q lam l K hK.1 hD := by
  let Fc := fun (j : ℕ) (ω : FieldPair d) => max (-(j : ℝ)) (min (j : ℝ) (F ω))
  let Gc := fun (j : ℕ) (ω : FieldPair d) => max (-(j : ℝ)) (min (j : ℝ) (G ω))
  have hFg : Measurable F := hF.mono (Probability.localSigma_le_borel _) le_rfl
  have hGg : Measurable G := hG.mono (Probability.localSigma_le_borel _) le_rfl
  have hFr : Measurable (fun q : FieldPair d × Regeneration.CoupledSample d =>
      F (reduce q.1)) := hFg.comp (Probability.measurable_reduce.comp measurable_fst)
  have hobs (v : ℝ≥0) : Measurable
      (fun q : FieldPair d × Regeneration.CoupledSample d =>
        G (translate (q.2.1 v) (reduce q.1))) :=
    hGg.comp (Probability.continuous_translate.measurable.comp
      (((continuous_eval_const v).measurable.comp measurable_snd.fst).prodMk
        (Probability.measurable_reduce.comp measurable_fst)))
  have hb (J : FieldPair d → ℝ) (j : ℕ) :
      Regeneration.BoundedRealTest (fun ω => max (-(j : ℝ)) (min (j : ℝ) (J ω))) := by
    refine ⟨(j : ℝ), fun ω => abs_le.mpr ⟨le_max_left _ _, ?_⟩⟩
    exact max_le ((neg_nonpos.mpr (Nat.cast_nonneg j)).trans (Nat.cast_nonneg j))
      (min_le_left _ _)
  have heq (j : ℕ) := sbxS4_bounded_first_cycle_slice hfact hd Q lam h₀ h₁ l δ hl hsep
    hδ₀ hδ₁ P K hK hD (Fc j) (Gc j)
    (measurable_const.max (measurable_const.min hF))
    (measurable_const.max (measurable_const.min hG)) (hb F j) (hb G j) n u μ hμ
  have hleft := sbxS4_tendsto_setIntegral_mul_clamps μ _ _ hFr (hobs _) hiFG
    {q | regenerationTime hd lam l 1 q.2 =
      (((n : ℝ≥0) * Regeneration.Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)}
  have hGlim := tendsto_setIntegral_clamp
    (regenerationConditionedLaw hd Q lam l K hK.1 hD) _ hiG Set.univ
  simp only [Measure.restrict_univ] at hGlim
  have hright := (tendsto_setIntegral_clamp μ _ hiF
    {q | regenerationTime hd lam l 1 q.2 =
      (((n : ℝ≥0) * Regeneration.Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)}).mul
      hGlim
  exact tendsto_nhds_unique hleft
    (hright.congr' (Filter.Eventually.of_forall fun j => (heq j).symm))

/-- At a phase time, the complement of the first-cycle remainder is the
disjoint union of exactly the first `k + 1` lattice slices. -/
theorem sbxS4_first_cycle_integral_partition {d : ℕ} (hd : 2 ≤ d)
    (lam l : ℝ) (h₀ : 0 < lam)
    (μ : Measure (FieldPair d × Regeneration.CoupledSample d))
    (f : FieldPair d × Regeneration.CoupledSample d → ℝ) (hf : Integrable f μ)
    (s : ℝ≥0) (hs : s < Regeneration.Renewal.regenDelta lam) (k : ℕ) :
    (∫ q, f q ∂μ) =
      (∫ q in {q | ((s + k * Regeneration.Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞) <
          regenerationTime hd lam l 1 q.2}, f q ∂μ) +
      ∑ n ∈ Finset.range (k + 1),
        ∫ q in {q | regenerationTime hd lam l 1 q.2 =
          (((n : ℝ≥0) * Regeneration.Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)}, f q ∂μ := by
  classical
  let Δ := Regeneration.Renewal.regenDelta lam
  let t := s + k * Δ
  let slice := fun n : ℕ => {q : FieldPair d × Regeneration.CoupledSample d |
    regenerationTime hd lam l 1 q.2 = (((n : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞)}
  have hΔ : 0 < Δ := Real.toNNReal_pos.mpr (inv_pos.mpr (sq_pos_of_pos h₀))
  have hTm : Measurable (fun q : FieldPair d × Regeneration.CoupledSample d =>
      regenerationTime hd lam l 1 q.2) :=
    (Regeneration.measurable_regenerationTime Δ lam (l / lam)
      (Regeneration.Renewal.forceCoord hd) 1).comp measurable_snd
  have hslice (n : ℕ) : MeasurableSet (slice n) :=
    measurableSet_eq_fun hTm measurable_const
  have hcover : {q : FieldPair d × Regeneration.CoupledSample d |
      regenerationTime hd lam l 1 q.2 ≤ (t : ℝ≥0∞)} =
        ⋃ n ∈ Finset.range (k + 1), slice n := by
    ext q
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Finset.mem_range, exists_prop]
    constructor
    · intro hq
      have hfin : Regeneration.firstRegenerationTime Δ lam (l / lam) q.2
          (Regeneration.Renewal.forceCoord hd) ≠ ⊤ := by
        have he : regenerationTime hd lam l 1 q.2 =
            Regeneration.firstRegenerationTime Δ lam (l / lam) q.2
              (Regeneration.Renewal.forceCoord hd) :=
          Regeneration.regenerationTime_one _ _ _ _ _
        rw [← he]
        exact ne_top_of_le_ne_top ENNReal.coe_ne_top hq
      obtain ⟨n, hn⟩ := Regeneration.firstRegenerationTime_mem_grid Δ hΔ lam (l / lam)
        q.2 (Regeneration.Renewal.forceCoord hd) hfin
      have hτ : regenerationTime hd lam l 1 q.2 =
          (((n : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞) := by
        change Regeneration.regenerationTime Δ lam (l / lam) q.2
          (Regeneration.Renewal.forceCoord hd) 1 = _
        rw [Regeneration.regenerationTime_one]
        exact hn
      have hnt : (n : ℝ≥0) * Δ ≤ t := ENNReal.coe_le_coe.mp (hτ ▸ hq)
      have hntR : (n : ℝ) * (Δ : ℝ) ≤ (s : ℝ) + (k : ℝ) * (Δ : ℝ) := by
        exact_mod_cast hnt
      have hnlt : (n : ℝ) < (k : ℝ) + 1 := by
        have hsR : (s : ℝ) < (Δ : ℝ) := hs
        have hΔR : 0 < (Δ : ℝ) := hΔ
        nlinarith
      exact ⟨n, by exact_mod_cast hnlt, hτ⟩
    · rintro ⟨n, hn, hq⟩
      have hnt : (n : ℝ≥0) * Δ ≤ t :=
        (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_of_lt_succ hn)
          bot_le).trans (le_add_of_nonneg_left bot_le)
      exact hq.trans_le (ENNReal.coe_le_coe.mpr hnt)
  have hsum := integral_biUnion_finset (μ := μ) (f := f) (Finset.range (k + 1))
    (s := slice) (fun n _ => hslice n)
    (by
      intro n _ m _ hne
      refine Set.disjoint_left.mpr fun q hq hq' => hne ?_
      have he : (n : ℝ≥0) * Δ = (m : ℝ≥0) * Δ :=
        ENNReal.coe_injective (hq.symm.trans hq')
      exact_mod_cast mul_right_cancel₀ hΔ.ne' he)
    (fun _ _ => hf.integrableOn)
  rw [← hcover] at hsum
  have hsplit := integral_add_compl
    (s := {q : FieldPair d × Regeneration.CoupledSample d |
      (t : ℝ≥0∞) < regenerationTime hd lam l 1 q.2})
    (measurableSet_lt measurable_const hTm) hf
  have he : {q : FieldPair d × Regeneration.CoupledSample d |
      (t : ℝ≥0∞) < regenerationTime hd lam l 1 q.2}ᶜ =
      {q | regenerationTime hd lam l 1 q.2 ≤ (t : ℝ≥0∞)} := by
    ext q
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_lt]
  rw [he, hsum] at hsplit
  exact hsplit.symm

/-- The full phase recurrence follows from first-cycle factorization and
actual integrability. The observation includes paths before every later cycle. -/
theorem sbxS4_first_cycle_recurrence_of_integrable
    (hfact : node_rt_u3A_factorizationStmt)
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1) (l δ : ℝ)
    (hl : 0 < l) (hsep : r₀ < 2 * l) (hδ₀ : 0 < δ) (hδ₁ : δ < 1)
    (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K)
    (hD : Regeneration.annealedCoupledLaw Q.measure K
      (regenerationNoReturn hd (l / lam)) ≠ 0)
    (F G : FieldPair d → ℝ)
    (hF : Measurable[localSigma {x : Vec d | euclideanNorm x < l / lam}] F)
    (hG : Measurable[localSigma {x : Vec d | euclideanNorm x < l / lam}] G)
    (μ : Measure (FieldPair d × Regeneration.CoupledSample d))
    (hμ : μ ∈ ({Regeneration.annealedCoupledLaw Q.measure K,
      regenerationConditionedLaw hd Q lam l K hK.1 hD} :
        Set (Measure (FieldPair d × Regeneration.CoupledSample d))))
    (hiF : Integrable (fun q => F (reduce q.1)) μ)
    (hiFG : ∀ v : ℝ≥0, Integrable (fun q => F (reduce q.1) *
      G (translate (q.2.1 v) (reduce q.1))) μ)
    (hiG : ∀ v : ℝ≥0, Integrable (fun q : FieldPair d × Regeneration.CoupledSample d =>
      G (translate (q.2.1 v) (reduce q.1)))
        (regenerationConditionedLaw hd Q lam l K hK.1 hD))
    (s : ℝ≥0) (hs : s < Regeneration.Renewal.regenDelta lam) (k : ℕ) :
    (∫ q, F (reduce q.1) *
      G (translate (q.2.1 (s + k * Regeneration.Renewal.regenDelta lam)) (reduce q.1)) ∂μ) =
    (∫ q in {q | ((s + k * Regeneration.Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞) <
        regenerationTime hd lam l 1 q.2}, F (reduce q.1) *
      G (translate (q.2.1 (s + k * Regeneration.Renewal.regenDelta lam)) (reduce q.1)) ∂μ) +
    ∑ n ∈ Finset.range (k + 1),
      (∫ q in {q | regenerationTime hd lam l 1 q.2 =
        (((n : ℝ≥0) * Regeneration.Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)},
        F (reduce q.1) ∂μ) *
      ∫ q, G (translate (q.2.1 (s + (k - n : ℕ) * Regeneration.Renewal.regenDelta lam))
        (reduce q.1)) ∂regenerationConditionedLaw hd Q lam l K hK.1 hD := by
  rw [sbxS4_first_cycle_integral_partition hd lam l h₀ μ _ (hiFG _) s hs k]
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  have hnk : n ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hn)
  have htime : (n : ℝ≥0) * Regeneration.Renewal.regenDelta lam +
      (s + (k - n : ℕ) * Regeneration.Renewal.regenDelta lam) =
      s + k * Regeneration.Renewal.regenDelta lam := by
    have hcast : (n : ℝ≥0) + ((k - n : ℕ) : ℝ≥0) = k := by
      exact_mod_cast Nat.add_sub_of_le hnk
    calc _ = s + ((n : ℝ≥0) + ((k - n : ℕ) : ℝ≥0)) *
        Regeneration.Renewal.regenDelta lam := by ring
      _ = _ := by rw [hcast]
  simpa only [htime] using
    sbxS4_first_cycle_slice_of_integrable hfact hd Q lam h₀ h₁ l δ hl hsep hδ₀ hδ₁
      P K hK hD F G hF hG n (s + (k - n : ℕ) * Regeneration.Renewal.regenDelta lam)
      μ hμ hiF (hiFG _) (hiG _)

/-- The authorized factorization and remainder inputs produce both literal
full-`Lp` phase recurrences at one structural scale. -/
theorem sbxS4_fixedRadius_recurrences_of_deps
    (hfact : node_rt_u3A_factorizationStmt)
    (hrem : node_rt_u3A_remainder_u2D_momentStmt) :
    ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ),
    ∃ l₀ p : ℝ, 0 < l₀ ∧ r₀ < 2 * l₀ ∧ 2 ≤ p ∧
    ∀ (l δ : ℝ), l₀ ≤ l → 0 < δ → δ < 1 →
    ∀ (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
      (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
      (hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K)
      (hD : Regeneration.annealedCoupledLaw Q.measure K
        (regenerationNoReturn hd (l / lam)) ≠ 0),
    ∀ F G : FieldPair d → ℝ,
      Measurable[localSigma {x : Vec d | euclideanNorm x < l / lam}] F →
      Measurable[localSigma {x : Vec d | euclideanNorm x < l / lam}] G →
      MemLp F (ENNReal.ofReal p) (reducedLaw Q) →
      MemLp G (ENNReal.ofReal p) (reducedLaw Q) →
    let μ := Regeneration.annealedCoupledLaw Q.measure K
    let ν := regenerationConditionedLaw hd Q lam l K hK.1 hD
    let Δ := Regeneration.Renewal.regenDelta lam
    let h := fun t : ℝ≥0 => ∫ q, G (translate (q.2.1 t) (reduce q.1)) ∂ν
    let r := fun t : ℝ≥0 => ∫ q in {q | (t : ℝ≥0∞) < regenerationTime hd lam l 1 q.2},
      G (translate (q.2.1 t) (reduce q.1)) ∂ν
    let hF := fun t : ℝ≥0 => ∫ q, F (reduce q.1) *
      G (translate (q.2.1 t) (reduce q.1)) ∂μ
    let rF := fun t : ℝ≥0 => ∫ q in {q | (t : ℝ≥0∞) < regenerationTime hd lam l 1 q.2},
      F (reduce q.1) * G (translate (q.2.1 t) (reduce q.1)) ∂μ
    let q := fun n : ℕ => ∫ q in {q | regenerationTime hd lam l 1 q.2 =
      (((n : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞)}, F (reduce q.1) ∂μ
    ∀ s : ℝ≥0, s < Δ → ∀ k : ℕ,
      h (s + k * Δ) = r (s + k * Δ) +
        ∑ n ∈ Finset.range (k + 1), regenerationLatticeMass hd Q lam l K hK.1 hD n *
          h (s + (k - n : ℕ) * Δ) ∧
      hF (s + k * Δ) = rF (s + k * Δ) +
        ∑ n ∈ Finset.range (k + 1), q n * h (s + (k - n : ℕ) * Δ) := by
  intro d hd Λ₀ r₀
  obtain ⟨l₀, p, hl₀, hsep, hp, hInt⟩ :=
    sbxS2_covariance_integrable_of_remainder hrem d hd Λ₀ r₀
  refine ⟨l₀, p, hl₀, hsep, hp, ?_⟩
  intro l δ hl hδ₀ hδ₁ Q lam h₀ h₁ P K hK hD F G hF hG hFp hGp
  dsimp only
  intro s hs k
  let μ := Regeneration.annealedCoupledLaw Q.measure K
  let ν := regenerationConditionedLaw hd Q lam l K hK.1 hD
  let := reducedLaw_probability Q
  let : IsProbabilityMeasure ν := regenerationConditionedLaw_probability hd Q lam l K hK.1 hD
  have hFg : Measurable F := hF.mono (Probability.localSigma_le_borel _) le_rfl
  have hGg : Measurable G := hG.mono (Probability.localSigma_le_borel _) le_rfl
  have hFi : Integrable F (reducedLaw Q) := hFp.integrable (by
    rw [← ENNReal.ofReal_one, ENNReal.ofReal_le_ofReal_iff (by positivity)]
    linarith)
  have hFr := (sbxS2_reducedFst_measurePreserving Q K hK.1).integrable_comp_of_integrable hFi
  have hiFG (v : ℝ≥0) := hInt Q lam h₀ h₁ l δ hl hδ₀ hδ₁ P K hK hD F G
    hFg hGg hFp hGp v μ (by simp [μ])
  have hiG (v : ℝ≥0) : Integrable
      (fun q : FieldPair d × Regeneration.CoupledSample d =>
        G (translate (q.2.1 v) (reduce q.1))) ν := by
    simpa only [one_mul] using hInt Q lam h₀ h₁ l δ hl hδ₀ hδ₁ P K hK hD
      (fun _ => 1) G measurable_const hGg (memLp_const 1) hGp v ν (by simp [ν])
  have hlpos := hl₀.trans_le hl
  have hsepl : r₀ < 2 * l := hsep.trans_le (by linarith)
  constructor
  · have hh := sbxS4_first_cycle_recurrence_of_integrable hfact hd Q lam h₀ h₁ l δ
      hlpos hsepl hδ₀ hδ₁ P K hK hD (fun _ => 1) G measurable_const hG ν
      (by simp [ν]) (integrable_const 1) (by simpa only [one_mul] using hiG) hiG s hs k
    have hmass (n : ℕ) :
        (∫ q in {q : FieldPair d × Regeneration.CoupledSample d |
          regenerationTime hd lam l 1 q.2 =
            (((n : ℝ≥0) * Regeneration.Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)},
          (1 : ℝ) ∂ν) = regenerationLatticeMass hd Q lam l K hK.1 hD n := by
      rw [setIntegral_const, smul_eq_mul, mul_one]
      rfl
    simpa only [one_mul, hmass] using hh
  · exact sbxS4_first_cycle_recurrence_of_integrable hfact hd Q lam h₀ h₁ l δ
      hlpos hsepl hδ₀ hδ₁ P K hK hD F G hF hG μ (by simp [μ]) hFr hiFG hiG s hs k

/-- Enlarging a prefactor and decreasing its exponential rate preserves a
nonnegative norm bound. -/
theorem sbxS4_decay_mono (C D c e x N : ℝ) (hC : 0 ≤ C) (hCD : C ≤ D)
    (hec : e ≤ c) (hx : 0 ≤ x) (hN : 0 ≤ N) :
    C * Real.exp (-c * x) * N ≤ D * Real.exp (-e * x) * N := by
  apply mul_le_mul_of_nonneg_right _ hN
  apply mul_le_mul hCD _ (Real.exp_pos _).le (hC.trans hCD)
  exact Real.exp_le_exp.mpr (by nlinarith only [mul_le_mul_of_nonneg_right hec hx])

/-- The actual full-Lp fixed-radius clause, with the exponent and constants
chosen before the law, force, observations and phase. -/
theorem sbxS4_fixedRadius_observations_of_deps
    (hfact : node_rt_u3A_factorizationStmt) (hren : node_rt_u3A_renewalStmt)
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
    ∀ F G : FieldPair d → ℝ,
    Measurable[localSigma {x : Vec d | euclideanNorm x < l / lam}] F →
    Measurable[localSigma {x : Vec d | euclideanNorm x < l / lam}] G →
    MemLp F (ENNReal.ofReal p) (reducedLaw Q) →
    MemLp G (ENNReal.ofReal p) (reducedLaw Q) →
    (∫ ω, F ω ∂reducedLaw Q) = 0 →
    let μ := Regeneration.annealedCoupledLaw Q.measure K
    let ν := regenerationConditionedLaw hd Q lam l K hK.1 hD
    let Δ := Regeneration.Renewal.regenDelta lam
    let pn := regenerationLatticeMass hd Q lam l K hK.1 hD
    let m := ∑' n : ℕ, (n : ℝ) * pn n
    let h := fun t : ℝ≥0 => ∫ ωz, G (translate (ωz.2.1 t) (reduce ωz.1)) ∂ν
    let r := fun t : ℝ≥0 => ∫ ωz in {ωz | (t : ℝ≥0∞) <
      regenerationTime hd lam l 1 ωz.2}, G (translate (ωz.2.1 t) (reduce ωz.1)) ∂ν
    let hF := fun t : ℝ≥0 => ∫ ωz, F (reduce ωz.1) *
      G (translate (ωz.2.1 t) (reduce ωz.1)) ∂μ
    let rF := fun t : ℝ≥0 => ∫ ωz in {ωz | (t : ℝ≥0∞) <
      regenerationTime hd lam l 1 ωz.2}, F (reduce ωz.1) *
        G (translate (ωz.2.1 t) (reduce ωz.1)) ∂μ
    let q := fun n : ℕ => ∫ ωz in {ωz | regenerationTime hd lam l 1 ωz.2 =
      (((n : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞)}, F (reduce ωz.1) ∂μ
    let Nf := (eLpNorm F (ENNReal.ofReal p) (reducedLaw Q)).toReal
    let Ng := (eLpNorm G (ENNReal.ofReal p) (reducedLaw Q)).toReal
    let H := fun s : ℝ≥0 => m⁻¹ * ∑' j : ℕ, r (s + j * Δ)
    Summable q ∧ (∑' n, q n) = 0 ∧
    (∀ n : ℕ, |q n| ≤ C * Real.exp (-c * n) *
      (eLpNorm F 2 (reducedLaw Q)).toReal) ∧
    (∀ t : ℝ≥0, |r t| ≤ C * Real.exp (-c * lam ^ 2 * (t : ℝ)) * Ng ∧
      |rF t| ≤ C * Real.exp (-c * lam ^ 2 * (t : ℝ)) * Nf * Ng) ∧
    ∀ s : ℝ≥0, s < Δ →
      Summable (fun j : ℕ => r (s + j * Δ)) ∧ |H s| ≤ C * Ng ∧
      ∀ k : ℕ,
        h (s + k * Δ) = r (s + k * Δ) +
          ∑ n ∈ Finset.range (k + 1), pn n * h (s + (k - n) * Δ) ∧
        hF (s + k * Δ) = rF (s + k * Δ) +
          ∑ n ∈ Finset.range (k + 1), q n * h (s + (k - n) * Δ) ∧
        |h (s + k * Δ) - H s| ≤ C * Real.exp (-c * k) * Ng ∧
        hF (s + k * Δ) = rF (s + k * Δ) +
          (∑ n ∈ Finset.range (k + 1), q n * (h (s + (k - n) * Δ) - H s)) -
          H s * ∑' n : ℕ, q (k + 1 + n) ∧
        |hF (s + k * Δ)| ≤ C * Real.exp (-c * k) * Nf * Ng := by
  intro d hd Λ₀ r₀
  obtain ⟨lS, hlS, hsepS, hscalar⟩ := sbxS4_fixedRadius_scalar_of_renewal hren d hd Λ₀ r₀
  obtain ⟨lQ, _hlQ, _hsepQ, hslices⟩ :=
    sbxS4_fixedRadius_centered_slices_of_renewal hren d hd Λ₀ r₀
  obtain ⟨lR, _hlR, _hsepR, hremainder⟩ :=
    sbxS4_first_cycle_remainders_of_renewal hren hrem d hd Λ₀ r₀
  obtain ⟨lI, pI, _hlI, _hsepI, hpI, hrecurrence⟩ :=
    sbxS4_fixedRadius_recurrences_of_deps hfact hrem d hd Λ₀ r₀
  have hleS : lS ≤ max (max lS lQ) (max lR lI) :=
    (le_max_left _ _).trans (le_max_left _ _)
  refine ⟨max (max lS lQ) (max lR lI), hlS.trans_le hleS,
    hsepS.trans_le (by linarith only [hleS]), ?_⟩
  intro l hl δ hδ₀ hδ₁
  have hls : lS ≤ l := (le_max_left _ _).trans ((le_max_left _ _).trans hl)
  have hlq : lQ ≤ l := (le_max_right _ _).trans ((le_max_left _ _).trans hl)
  have hlr : lR ≤ l := (le_max_left _ _).trans ((le_max_right _ _).trans hl)
  have hli : lI ≤ l := (le_max_right _ _).trans ((le_max_right _ _).trans hl)
  obtain ⟨cQ, CQ, hcQ, hCQ, hqdata⟩ := hslices l hlq δ hδ₀ hδ₁
  obtain ⟨pR, cR, CR, hpR, hcR, hCR, hrdata⟩ := hremainder l hlr δ hδ₀ hδ₁
  let p := max pR pI
  let b := min cQ cR
  have hb : 0 < b := lt_min hcQ hcR
  obtain ⟨cA, CA, hcA, hCA, hscalar'⟩ := hscalar l hls δ hδ₀ hδ₁ b hb
  let c := min cQ (min cR cA)
  let C := 1 + CQ + CR + CA * CR + CA * (CR + CQ * CR)
  have hC : 0 < C := by dsimp only [C]; positivity
  have hprod : 0 < CA * CR := mul_pos hCA hCR
  have hall : 0 < CA * (CR + CQ * CR) := by positivity
  have hCq : CQ ≤ C := by dsimp only [C]; linarith only [hCR, hprod, hall]
  have hCr : CR ≤ C := by dsimp only [C]; linarith only [hCQ, hprod, hall]
  have hCa : CA * CR ≤ C := by dsimp only [C]; linarith only [hCQ, hCR, hall]
  have hCf : CA * (CR + CQ * CR) ≤ C := by dsimp only [C]; linarith only [hCQ, hCR, hprod]
  have hcq : c ≤ cQ := min_le_left _ _
  have hcr : c ≤ cR := (min_le_right _ _).trans (min_le_left _ _)
  have hca : c ≤ cA := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨p, c, C, hpR.trans (le_max_left _ _), lt_min hcQ (lt_min hcR hcA), hC, ?_⟩
  intro Q lam h₀ h₁ P K hK hD F G hF hG hFp hGp hzero
  let := reducedLaw_probability Q
  let μ := Regeneration.annealedCoupledLaw Q.measure K
  let ν := regenerationConditionedLaw hd Q lam l K hK.1 hD
  let Δ := Regeneration.Renewal.regenDelta lam
  let pn := regenerationLatticeMass hd Q lam l K hK.1 hD
  let m := ∑' n : ℕ, (n : ℝ) * pn n
  let h := fun t : ℝ≥0 => ∫ ωz, G (translate (ωz.2.1 t) (reduce ωz.1)) ∂ν
  let r := fun t : ℝ≥0 => ∫ ωz in {ωz | (t : ℝ≥0∞) <
    regenerationTime hd lam l 1 ωz.2}, G (translate (ωz.2.1 t) (reduce ωz.1)) ∂ν
  let hF' := fun t : ℝ≥0 => ∫ ωz, F (reduce ωz.1) *
    G (translate (ωz.2.1 t) (reduce ωz.1)) ∂μ
  let rF := fun t : ℝ≥0 => ∫ ωz in {ωz | (t : ℝ≥0∞) <
    regenerationTime hd lam l 1 ωz.2}, F (reduce ωz.1) *
      G (translate (ωz.2.1 t) (reduce ωz.1)) ∂μ
  let q := fun n : ℕ => ∫ ωz in {ωz | regenerationTime hd lam l 1 ωz.2 =
    (((n : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞)}, F (reduce ωz.1) ∂μ
  let Nf := (eLpNorm F (ENNReal.ofReal p) (reducedLaw Q)).toReal
  let Ng := (eLpNorm G (ENNReal.ofReal p) (reducedLaw Q)).toReal
  let H := fun s : ℝ≥0 => m⁻¹ * ∑' j : ℕ, r (s + j * Δ)
  change Summable q ∧ (∑' n, q n) = 0 ∧
    (∀ n : ℕ, |q n| ≤ C * Real.exp (-c * n) *
      (eLpNorm F 2 (reducedLaw Q)).toReal) ∧
    (∀ t : ℝ≥0, |r t| ≤ C * Real.exp (-c * lam ^ 2 * (t : ℝ)) * Ng ∧
      |rF t| ≤ C * Real.exp (-c * lam ^ 2 * (t : ℝ)) * Nf * Ng) ∧
    ∀ s : ℝ≥0, s < Δ → Summable (fun j : ℕ => r (s + j * Δ)) ∧
      |H s| ≤ C * Ng ∧ ∀ k : ℕ,
      h (s + k * Δ) = r (s + k * Δ) +
        ∑ n ∈ Finset.range (k + 1), pn n * h (s + (k - n) * Δ) ∧
      hF' (s + k * Δ) = rF (s + k * Δ) +
        ∑ n ∈ Finset.range (k + 1), q n * h (s + (k - n) * Δ) ∧
      |h (s + k * Δ) - H s| ≤ C * Real.exp (-c * k) * Ng ∧
      hF' (s + k * Δ) = rF (s + k * Δ) +
        (∑ n ∈ Finset.range (k + 1), q n * (h (s + (k - n) * Δ) - H s)) -
        H s * ∑' n : ℕ, q (k + 1 + n) ∧
      |hF' (s + k * Δ)| ≤ C * Real.exp (-c * k) * Nf * Ng
  have hFg := hF.mono (Probability.localSigma_le_borel _) le_rfl
  have hGg := hG.mono (Probability.localSigma_le_borel _) le_rfl
  have hpR' : ENNReal.ofReal pR ≤ ENNReal.ofReal p :=
    ENNReal.ofReal_le_ofReal (le_max_left _ _)
  have hpI' : ENNReal.ofReal pI ≤ ENNReal.ofReal p :=
    ENNReal.ofReal_le_ofReal (le_max_right _ _)
  have hnfR : (eLpNorm F (ENNReal.ofReal pR) (reducedLaw Q)).toReal ≤ Nf :=
    ENNReal.toReal_mono hFp.eLpNorm_ne_top (eLpNorm_le_eLpNorm_of_exponent_le hpR')
  have hngR : (eLpNorm G (ENNReal.ofReal pR) (reducedLaw Q)).toReal ≤ Ng :=
    ENNReal.toReal_mono hGp.eLpNorm_ne_top (eLpNorm_le_eLpNorm_of_exponent_le hpR')
  have hnf2 : (eLpNorm F 2 (reducedLaw Q)).toReal ≤ Nf :=
    ENNReal.toReal_mono hFp.eLpNorm_ne_top (eLpNorm_le_eLpNorm_of_exponent_le (by
      simpa only [ENNReal.ofReal_ofNat] using
        ENNReal.ofReal_le_ofReal (hpR.trans (le_max_left pR pI))))
  have hNf : 0 ≤ Nf := ENNReal.toReal_nonneg
  have hNg : 0 ≤ Ng := ENNReal.toReal_nonneg
  have hone : eLpNorm (fun _ : FieldPair d => (1 : ℝ))
      (ENNReal.ofReal pR) (reducedLaw Q) = 1 := by
    rw [eLpNorm_const' 1 (ne_of_gt (ENNReal.ofReal_pos.mpr (by linarith)))
      ENNReal.ofReal_ne_top]
    simp
  have hr (t : ℝ≥0) : |r t| ≤ CR * Real.exp (-cR * lam ^ 2 * (t : ℝ)) * Ng := by
    have hbnd := (hrdata Q lam h₀ h₁ P K hK hD (fun _ => 1) G measurable_const hGg
      (memLp_const 1) (hGp.mono_exponent hpR') t ν (by simp [ν])).2
    simp only [one_mul, hone, ENNReal.toReal_one, mul_one] at hbnd
    exact hbnd.trans (mul_le_mul_of_nonneg_left hngR (by positivity))
  have hrF (t : ℝ≥0) : |rF t| ≤ CR * Real.exp (-cR * lam ^ 2 * (t : ℝ)) * Nf * Ng := by
    have hbnd := (hrdata Q lam h₀ h₁ P K hK hD F G hFg hGg
      (hFp.mono_exponent hpR') (hGp.mono_exponent hpR') t μ (by simp [μ])).2
    apply hbnd.trans
    apply mul_le_mul _ hngR ENNReal.toReal_nonneg (by positivity)
    exact mul_le_mul_of_nonneg_left hnfR (by positivity)
  obtain ⟨hqs, hqzero, hqdec⟩ := hqdata Q lam h₀ h₁ P K hK hD p
    (hpR.trans (le_max_left _ _)) F hFg hFp hzero
  have hrec := hrecurrence l δ hli hδ₀ hδ₁ Q lam h₀ h₁ P K hK hD F G hF hG
    (hFp.mono_exponent hpI') (hGp.mono_exponent hpI')
  have hΔ : lam ^ 2 * (Δ : ℝ) = 1 := by
    dsimp only [Δ, Regeneration.Renewal.regenDelta]
    rw [Real.coe_toNNReal _ (inv_nonneg.mpr (sq_nonneg lam))]
    exact mul_inv_cancel₀ (pow_ne_zero 2 h₀.ne')
  have hsub (j n : ℕ) : ((j - n : ℕ) : ℝ≥0) = (j : ℝ≥0) - (n : ℝ≥0) := by
    rcases le_total n j with hnj | hjn
    · apply NNReal.coe_injective
      rw [NNReal.coe_sub (Nat.cast_le.mpr hnj)]
      simpa only [NNReal.coe_natCast] using (Nat.cast_sub hnj : ((j - n : ℕ) : ℝ) = j - n)
    · rw [Nat.sub_eq_zero_of_le hjn, Nat.cast_zero,
        tsub_eq_zero_of_le (Nat.cast_le.mpr hjn)]
  refine ⟨hqs, hqzero, ?_, ?_, ?_⟩
  · intro n
    exact (hqdec n).trans (sbxS4_decay_mono CQ C cQ c n _ hCQ.le hCq hcq
      (Nat.cast_nonneg n) ENNReal.toReal_nonneg)
  · intro t
    constructor
    · apply (hr t).trans
      simpa only [mul_assoc] using sbxS4_decay_mono CR C cR c (lam ^ 2 * (t : ℝ)) Ng
        hCR.le hCr hcr (by positivity) hNg
    · apply (hrF t).trans
      simpa only [mul_assoc] using sbxS4_decay_mono CR C cR c (lam ^ 2 * (t : ℝ))
        (Nf * Ng) hCR.le hCr hcr (by positivity) (mul_nonneg hNf hNg)
  · intro s hs
    have hrphase (j : ℕ) : |r (s + j * Δ)| ≤ (CR * Ng) * Real.exp (-b * j) := by
      have hbnd := phase_remainder_bound r CR cR lam Ng 0 hCR.le hcR.le hNg Δ hΔ
        (by simpa only [Nat.cast_zero, mul_zero, zero_sub, neg_mul] using hr) s j
      simp only [Nat.cast_zero, mul_zero, zero_sub] at hbnd
      apply hbnd.trans
      have hh := sbxS4_decay_mono CR CR cR b j Ng hCR.le le_rfl (min_le_right _ _)
        (Nat.cast_nonneg j) hNg
      simpa only [neg_mul, mul_neg, mul_comm, mul_left_comm, mul_assoc] using hh
    have hrFphase (j : ℕ) :
        |rF (s + j * Δ)| ≤ (CR * Nf * Ng) * Real.exp (-b * j) := by
      have hbnd := phase_remainder_bound rF CR cR lam (Nf * Ng) 0 hCR.le hcR.le
        (mul_nonneg hNf hNg) Δ hΔ
        (by simpa only [Nat.cast_zero, mul_zero, zero_sub, neg_mul, mul_assoc] using hrF) s j
      simp only [Nat.cast_zero, mul_zero, zero_sub] at hbnd
      apply hbnd.trans
      have hh := sbxS4_decay_mono CR CR cR b j (Nf * Ng) hCR.le le_rfl
        (min_le_right _ _) (Nat.cast_nonneg j) (mul_nonneg hNf hNg)
      simpa only [neg_mul, mul_neg, mul_comm, mul_left_comm, mul_assoc] using hh
    have hqphase (n : ℕ) : |q n| ≤ (CQ * Nf) * Real.exp (-b * n) := by
      apply (hqdec n).trans
      have hh := sbxS4_decay_mono CQ CQ cQ b n
        (eLpNorm F 2 (reducedLaw Q)).toReal hCQ.le le_rfl (min_le_left _ _)
        (Nat.cast_nonneg n) ENNReal.toReal_nonneg
      apply hh.trans
      have hn := mul_le_mul_of_nonneg_left hnf2
        (mul_nonneg hCQ.le (Real.exp_pos (-b * n)).le)
      simpa only [neg_mul, mul_neg, mul_comm, mul_left_comm, mul_assoc] using hn
    obtain ⟨hrs, hH, hbounds⟩ := hscalar' Q lam h₀ h₁ P K hK hD s hs
      (fun j => h (s + j * Δ)) (fun j => r (s + j * Δ))
      (fun j => hF' (s + j * Δ)) (fun j => rF (s + j * Δ)) q
      (CR * Ng) (CR * Nf * Ng) (CQ * Nf) (by positivity) (by positivity) (by positivity)
      (by intro j; simpa only [hsub] using (hrec s hs j).1)
      (by intro j; simpa only [hsub] using (hrec s hs j).2)
      hrphase hrFphase hqphase hqs hqzero
    refine ⟨hrs, ?_, ?_⟩
    · exact hH.trans (by simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_right hCa hNg)
    · intro k
      obtain ⟨hdec, hidentity, hcov⟩ := hbounds k
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · simpa only [hsub] using (hrec s hs k).1
      · simpa only [hsub] using (hrec s hs k).2
      · apply hdec.trans
        have hh := sbxS4_decay_mono (CA * CR) C cA c k Ng (by positivity)
          hCa hca (Nat.cast_nonneg k) hNg
        simpa only [neg_mul, mul_neg, mul_comm, mul_left_comm, mul_assoc] using hh
      · simpa only [hsub] using hidentity
      · apply hcov.trans
        have he : CA * (CR * Nf * Ng + CQ * Nf * (CR * Ng)) =
            (CA * (CR + CQ * CR)) * (Nf * Ng) := by ring
        rw [he]
        have hh := sbxS4_decay_mono (CA * (CR + CQ * CR)) C cA c k
          (Nf * Ng) (by positivity) hCf hca (Nat.cast_nonneg k) (mul_nonneg hNf hNg)
        simpa only [neg_mul, mul_neg, mul_comm, mul_left_comm, mul_assoc] using hh

/-- The literal fixed-radius statement follows from exactly the four
ordered source dependencies. The two renewal clauses use common constants. -/
theorem node_rt_u3A_local_u2D_mixing_u23_fixed_u2D_radius_of_deps
    (hfact : node_rt_u3A_factorizationStmt) (hren : node_rt_u3A_renewalStmt)
    (hrem : node_rt_u3A_remainder_u2D_momentStmt)
    (_htails : node_app_u3A_regen_u2D_tailsStmt) :
    node_rt_u3A_local_u2D_mixing_u23_fixed_u2D_radiusStmt := by
  intro d hd Λ₀ r₀
  obtain ⟨lS, hlS, hsepS, hscalar⟩ := sbxS4_fixedRadius_scalar_of_renewal hren d hd Λ₀ r₀
  obtain ⟨lA, _hlA, _hsepA, hactual⟩ :=
    sbxS4_fixedRadius_observations_of_deps hfact hren hrem d hd Λ₀ r₀
  refine ⟨max lS lA, hlS.trans_le (le_max_left _ _),
    hsepS.trans_le (by linarith only [le_max_left lS lA]), ?_⟩
  intro l hl δ hδ₀ hδ₁ b hb
  obtain ⟨cS, CS, hcS, hCS, hscalar'⟩ :=
    hscalar l ((le_max_left _ _).trans hl) δ hδ₀ hδ₁ b hb
  obtain ⟨p, cA, CA, hp, hcA, hCA, hactual'⟩ :=
    hactual l ((le_max_right _ _).trans hl) δ hδ₀ hδ₁
  let c := min cS cA
  let C := 1 + CS + CA
  have hC : 0 < C := by dsimp only [C]; positivity
  have hCs : CS ≤ C := by dsimp only [C]; linarith only [hCA]
  have hCa : CA ≤ C := by dsimp only [C]; linarith only [hCS]
  have hcs : c ≤ cS := min_le_left _ _
  have hca : c ≤ cA := min_le_right _ _
  refine ⟨p, c, C, hp, lt_min hcS hcA, hC, ?_⟩
  intro Q lam h₀ h₁ P K hK hD
  constructor
  · dsimp only
    intro s hs h r hF rF q R Rf Bq hR hRf hBq hrec hrecF hr hrF hq hqs hqzero
    have hout := hscalar' Q lam h₀ h₁ P K hK hD s hs h r hF rF q R Rf Bq
      hR hRf hBq hrec hrecF hr hrF hq hqs hqzero
    dsimp only at hout ⊢
    obtain ⟨hrs, hH, hbounds⟩ := hout
    refine ⟨hrs, hH.trans (mul_le_mul_of_nonneg_right hCs hR), ?_⟩
    intro j
    obtain ⟨hdec, hidentity, hcov⟩ := hbounds j
    refine ⟨?_, hidentity, ?_⟩
    · apply hdec.trans
      have hh := sbxS4_decay_mono CS C cS c j R hCS.le hCs hcs (Nat.cast_nonneg j) hR
      simpa only [mul_comm, mul_left_comm, mul_assoc] using hh
    · apply hcov.trans
      have hh := sbxS4_decay_mono CS C cS c j (Rf + Bq * R) hCS.le hCs hcs
        (Nat.cast_nonneg j) (add_nonneg hRf (mul_nonneg hBq hR))
      simpa only [mul_comm, mul_left_comm, mul_assoc] using hh
  · intro F G hF hG hFp hGp hzero
    have hout := hactual' Q lam h₀ h₁ P K hK hD F G hF hG hFp hGp hzero
    dsimp only at hout ⊢
    obtain ⟨hqs, hqzero, hqdec, hremdec, hphase⟩ := hout
    refine ⟨hqs, hqzero, ?_, ?_, ?_⟩
    · intro n
      exact (hqdec n).trans (sbxS4_decay_mono CA C cA c n _ hCA.le hCa hca
        (Nat.cast_nonneg n) ENNReal.toReal_nonneg)
    · intro t
      constructor
      · apply (hremdec t).1.trans
        have hh := sbxS4_decay_mono CA C cA c (lam ^ 2 * (t : ℝ))
          (eLpNorm G (ENNReal.ofReal p) (reducedLaw Q)).toReal hCA.le hCa hca
          (by positivity) ENNReal.toReal_nonneg
        simpa only [mul_assoc] using hh
      · apply (hremdec t).2.trans
        have hh := sbxS4_decay_mono CA C cA c (lam ^ 2 * (t : ℝ))
          ((eLpNorm F (ENNReal.ofReal p) (reducedLaw Q)).toReal *
            (eLpNorm G (ENNReal.ofReal p) (reducedLaw Q)).toReal) hCA.le hCa hca
          (by positivity) (by positivity)
        simpa only [mul_assoc] using hh
    · intro s hs
      obtain ⟨hrs, hH, hbounds⟩ := hphase s hs
      refine ⟨hrs, hH.trans (mul_le_mul_of_nonneg_right hCa ENNReal.toReal_nonneg), ?_⟩
      intro k
      obtain ⟨hrec, hrecF, hdec, hidentity, hcov⟩ := hbounds k
      refine ⟨hrec, hrecF, ?_, hidentity, ?_⟩
      · exact hdec.trans (sbxS4_decay_mono CA C cA c k _ hCA.le hCa hca
          (Nat.cast_nonneg k) ENNReal.toReal_nonneg)
      · apply hcov.trans
        have hh := sbxS4_decay_mono CA C cA c k
          ((eLpNorm F (ENNReal.ofReal p) (reducedLaw Q)).toReal *
            (eLpNorm G (ENNReal.ofReal p) (reducedLaw Q)).toReal) hCA.le hCa hca
          (Nat.cast_nonneg k) (by positivity)
        simpa only [mul_assoc] using hh

-- Replay the exact ordered dependency arrow, without an auxiliary premise.
example : node_rt_u3A_factorizationStmt → node_rt_u3A_renewalStmt →
    node_rt_u3A_remainder_u2D_momentStmt → node_app_u3A_regen_u2D_tailsStmt →
    node_rt_u3A_local_u2D_mixing_u23_fixed_u2D_radiusStmt :=
  node_rt_u3A_local_u2D_mixing_u23_fixed_u2D_radius_of_deps

#print axioms sbxS4_fixedRadius_scalar_uniform
#print axioms sbxS4_fixedRadius_scalar_of_renewal
#print axioms sbxS4_manyCycleMoment_of_renewal
#print axioms sbxS4_fixedRadius_centered_slices_of_renewal
#print axioms sbxS4_remainder_moment_variable_rate_both
#print axioms sbxS4_first_cycle_remainders_of_renewal
#print axioms sbxS4_Phi0_record
#print axioms sbxS4_bounded_first_cycle_slice
#print axioms sbxS4_tendsto_setIntegral_mul_clamps
#print axioms sbxS4_first_cycle_slice_of_integrable
#print axioms sbxS4_first_cycle_integral_partition
#print axioms sbxS4_first_cycle_recurrence_of_integrable
#print axioms sbxS4_fixedRadius_recurrences_of_deps

#print axioms sbxS4_decay_mono
#print axioms sbxS4_fixedRadius_observations_of_deps

#print axioms node_rt_u3A_local_u2D_mixing_u23_fixed_u2D_radius_of_deps

#lint

end EinsteinFull.Blueprint
