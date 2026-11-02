import EinsteinFull.Blueprint.G1.Draft.SbxCManyCycleUniformR06
import EinsteinFull.Blueprint.G1.Draft.SbxCPhaseUniformR07
import EinsteinFull.Blueprint.G1.Draft.SbxCKMCenteredSlicesSmoothR01
import EinsteinFull.Calculus.SbxAGMPActionAssemblerR07
import EinsteinFull.Blueprint.G1.Draft.SbxCKFactorUniformR06
import EinsteinFull.Blueprint.G1.Draft.SbxCKMCenteredCovarianceSmoothR02
import EinsteinFull.Blueprint.G1.Draft.SbxCKMCovarianceDecaySmoothR02
import EinsteinFull.Blueprint.G1.Proofs.SbxS4KmPathIdentification
import EinsteinFull.Blueprint.G1.Draft.SbxAUniformCouplingR07
import EinsteinFull.Blueprint.G1.Draft.SbxCLocalMixingUniformR06

/-! Conditional uniform support for the k/m assembly. -/
open MeasureTheory
open scoped NNReal ENNReal Topology
noncomputable section
namespace EinsteinFull.Blueprint.SbxAUniformKMAssemblerR07
open EinsteinRelation EinsteinFull.Work.W5
open EinsteinFull.Blueprint.SbxCKMCovarianceSmoothR01
open EinsteinFull.Blueprint.SbxS5Section3R01
open EinsteinFull.Blueprint.SbxCKMCovarianceDecaySmoothR02

theorem uniform_centered_slices_of_manyCycleMoment
    (hmany : SbxCManyCycleUniformR06.manyCycleSmoothStmt)
    (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ) (hΛ : 1 ≤ Λ₀) (hr : 1 ≤ r₀) :
    ∃ l₀ : ℝ, 0 < l₀ ∧ r₀ < 2 * l₀ ∧
    ∀ l : ℝ, l₀ ≤ l → ∀ δ : ℝ, 0 < δ → δ < 1 →
    ∀ (β : ℕ → ℝ) (hβ : ∀ k, 1 ≤ k → 0 < β k),
    let D : StructuralData d := ⟨Λ₀, r₀, β, hΛ, hr, hβ⟩
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
  obtain ⟨l₀, hl₀, hsep, hmom⟩ := hmany d hd Λ₀ r₀ hΛ hr
  refine ⟨l₀, hl₀, hsep, ?_⟩
  intro l hl δ hδ₀ hδ₁
  obtain ⟨a, M, C, _ha, _hM, _hC, hm⟩ := hmom l hl δ hδ₀ hδ₁
  intro β hβ
  dsimp only
  intro Q hQ lam h₀ h₁ P K hK hD p hp F hF hFp hzero k
  let := reducedLaw_probability Q
  have hmfin : (∫⁻ ωz, regenerationExponentialWeight hd lam l a k ωz.2
      ∂Regeneration.annealedCoupledLaw Q.measure K) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top ((hm β hβ Q hQ lam h₀ h₁ P K hK hD).2 k)
  have hq := sbxS2_centered_regenerationSlice_hasSum hd Q lam l a h₀.ne' K hK.1 k
    hmfin F hF (hFp.integrable (by simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp)) hzero
  exact ⟨hq.summable, hq.tsum_eq⟩

/-- The supplied many-cycle moment yields uniform decay of every nonzero-cycle
coefficient in any finite Lᵖ norm with `2 ≤ p`. -/
theorem uniform_slice_decay_of_manyCycleMoment
    (hmany : SbxCManyCycleUniformR06.manyCycleSmoothStmt)
    (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ) (hΛ : 1 ≤ Λ₀) (hr : 1 ≤ r₀) :
    ∃ l₀ : ℝ, 0 < l₀ ∧ r₀ < 2 * l₀ ∧
    ∀ l : ℝ, l₀ ≤ l → ∀ δ : ℝ, 0 < δ → δ < 1 →
    ∃ a C : ℝ, 0 < a ∧ 0 < C ∧
    ∀ (β : ℕ → ℝ) (hβ : ∀ k, 1 ≤ k → 0 < β k),
    let D : StructuralData d := ⟨Λ₀, r₀, β, hΛ, hr, hβ⟩
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
  obtain ⟨l₀, hl₀, hsep, hmom⟩ := hmany d hd Λ₀ r₀ hΛ hr
  refine ⟨l₀, hl₀, hsep, ?_⟩
  intro l hl δ hδ₀ hδ₁
  obtain ⟨a, M, C, ha, hM, hC, hm⟩ := hmom l hl δ hδ₀ hδ₁
  refine ⟨a, C + M, ha, add_pos hC hM, ?_⟩
  intro β hβ
  dsimp only
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
      (((hm β hβ Q hQ lam h₀ h₁ P K hK hD).2 k).trans (ENNReal.ofReal_le_ofReal hgeom))
  exact hq.trans (mul_le_mul_of_nonneg_left
    (ENNReal.toReal_mono hFp.eLpNorm_ne_top (eLpNorm_le_eLpNorm_of_exponent_le hp'))
      (Real.exp_pos _).le)


/-- The actual all-law remainder theorem supplies uniform smooth-law estimates
from the original regeneration-tail hypothesis. -/
theorem uniform_remainder_of_regeneration_tails
    (htails : node_app_u3A_regen_u2D_tailsStmt) :
  ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ) (hΛ : 1 ≤ Λ₀) (hr : 1 ≤ r₀) (B b : ℝ), 0 < B → 0 < b →
    ∃ l₀ p c C : ℝ, 0 < l₀ ∧ r₀ < 2 * l₀ ∧ 2 ≤ p ∧ 0 < c ∧ 0 < C ∧
    ∀ (β : ℕ → ℝ) (hβ : ∀ k, 1 ≤ k → 0 < β k),
    let D : StructuralData d := ⟨Λ₀, r₀, β, hΛ, hr, hβ⟩
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange), HasSmoothBounds D Q →
    ∀ (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
      (l δ : ℝ), l₀ ≤ l → 0 < δ → δ < 1 →
    ∀ (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
      (hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K)
      (hD : Regeneration.annealedCoupledLaw Q.measure K
        (regenerationNoReturn hd (l / lam)) ≠ 0),
    ∀ F G : FieldPair d → ℝ,
    Measurable F → Measurable G →
    MemLp F (ENNReal.ofReal p) (reducedLaw Q) →
    MemLp G (ENNReal.ofReal p) (reducedLaw Q) →
    ∀ (J : ℝ) (t : ℝ≥0) (A : Set (FieldPair d × Regeneration.CoupledSample d)),
    0 ≤ J → MeasurableSet A →
    Regeneration.annealedCoupledLaw Q.measure K A ≤
      ENNReal.ofReal (B * Real.exp (B * J - b * lam ^ 2 * (t : ℝ))) →
    ∀ μ ∈ ({Regeneration.annealedCoupledLaw Q.measure K,
      regenerationConditionedLaw hd Q lam l K hK.1 hD} :
        Set (Measure (FieldPair d × Regeneration.CoupledSample d))),
      IntegrableOn (fun ωz => F (reduce ωz.1) *
        G (translate (ωz.2.1 t) (reduce ωz.1))) A μ ∧
      |∫ ωz in A, F (reduce ωz.1) * G (translate (ωz.2.1 t) (reduce ωz.1)) ∂μ| ≤
        C * Real.exp (C * J - c * lam ^ 2 * (t : ℝ)) *
          (eLpNorm F (ENNReal.ofReal p) (reducedLaw Q)).toReal *
          (eLpNorm G (ENNReal.ofReal p) (reducedLaw Q)).toReal := by
  intro d hd Λ₀ r₀ hΛ hr B b hB hb
  obtain ⟨l₀, p, c, C, hl₀, hsep, hp, hc, hC, h⟩ :=
    EinsteinFull.s8_remainder_moment_of_regeneration_tails htails d hd Λ₀ r₀ B b hB hb
  exact ⟨l₀, p, c, C, hl₀, hsep, hp, hc, hC, fun _ _ Q _ => h Q⟩


/-- The original tails yield a uniform exponent for the full covariance integrand. -/
theorem uniform_covariance_integrable_of_regeneration_tails
    (htails : node_app_u3A_regen_u2D_tailsStmt) :
    ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ) (hΛ : 1 ≤ Λ₀) (hr : 1 ≤ r₀),
    ∃ l₀ p : ℝ, 0 < l₀ ∧ r₀ < 2 * l₀ ∧ 2 ≤ p ∧
    ∀ (β : ℕ → ℝ) (hβ : ∀ k, 1 ≤ k → 0 < β k),
    let D : StructuralData d := ⟨Λ₀, r₀, β, hΛ, hr, hβ⟩
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange), HasSmoothBounds D Q →
    ∀ (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
      (l δ : ℝ), l₀ ≤ l → 0 < δ → δ < 1 →
    ∀ (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
      (hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K)
      (hD : Regeneration.annealedCoupledLaw Q.measure K
        (regenerationNoReturn hd (l / lam)) ≠ 0),
    ∀ F G : FieldPair d → ℝ, Measurable F → Measurable G →
      MemLp F (ENNReal.ofReal p) (reducedLaw Q) →
      MemLp G (ENNReal.ofReal p) (reducedLaw Q) → ∀ t : ℝ≥0,
    ∀ μ ∈ ({Regeneration.annealedCoupledLaw Q.measure K,
      regenerationConditionedLaw hd Q lam l K hK.1 hD} :
        Set (Measure (FieldPair d × Regeneration.CoupledSample d))),
    Integrable (fun ωz => F (reduce ωz.1) *
      G (translate (ωz.2.1 t) (reduce ωz.1))) μ := by
  intro d hd Λ₀ r₀ hΛ hr
  obtain ⟨l₀, p, c, C, hl₀, hsep, hp, _hc, _hC, hrem⟩ :=
    uniform_remainder_of_regeneration_tails htails d hd Λ₀ r₀ hΛ hr 1 1
      (by norm_num) (by norm_num)
  refine ⟨l₀, p, hl₀, hsep, hp, ?_⟩
  intro β hβ
  dsimp only
  intro Q hQ lam h₀ h₁ l δ hl hδ₀ hδ₁ P K hK hD F G hF hG hFp hGp t μ hμ
  let : IsProbabilityMeasure (Regeneration.annealedCoupledLaw Q.measure K) :=
    Regeneration.annealedCoupledLaw_isProbabilityMeasure Q.measure K hK.1
  have hprob : Regeneration.annealedCoupledLaw Q.measure K Set.univ ≤
      ENNReal.ofReal (1 * Real.exp (1 * (lam ^ 2 * (t : ℝ)) -
        1 * lam ^ 2 * (t : ℝ))) := by simp
  have hint := (hrem β hβ Q hQ lam h₀ h₁ l δ hl hδ₀ hδ₁ P K hK hD
    F G hF hG hFp hGp (lam ^ 2 * (t : ℝ)) t Set.univ
    (mul_nonneg (sq_nonneg lam) t.coe_nonneg) MeasurableSet.univ hprob μ hμ).1
  simpa only [integrableOn_univ] using hint

theorem uniform_covariance_decomposition_of_inputs
    (hfactor : kmKFactorUniformSmoothStmt)
    (htails : node_app_u3A_regen_u2D_tailsStmt) :
    ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ) (hΛ : 1 ≤ Λ₀) (hr : 1 ≤ r₀),
    ∃ l₀ p : ℝ, 0 < l₀ ∧ r₀ < 2 * l₀ ∧ 2 ≤ p ∧
    ∀ (l δ : ℝ), l₀ ≤ l → 0 < δ → δ < 1 →
    ∀ (β : ℕ → ℝ) (hβ : ∀ k, 1 ≤ k → 0 < β k),
    let SD : StructuralData d := ⟨Λ₀, r₀, β, hΛ, hr, hβ⟩
    ∀ (Q : EnvironmentLaw d SD.ellipticity SD.dependenceRange), HasSmoothBounds SD Q →
    ∀ (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
    (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K)
    (hD : Regeneration.annealedCoupledLaw Q.measure K
      (regenerationNoReturn hd (l / lam)) ≠ 0)
    (A : ℝ) (_hA : l ≤ A) (F G : FieldPair d → ℝ)
    (_hF : Measurable[localSigma {x : Vec d | euclideanNorm x < A / lam}] F)
    (_hFp : MemLp F (ENNReal.ofReal p) (reducedLaw Q))
    (_hG : Measurable[localSigma {x : Vec d | euclideanNorm x < A / lam}] G)
    (_hGp : MemLp G (ENNReal.ofReal p) (reducedLaw Q)) (t : ℝ≥0),
    let k : ℕ := max 1 ⌈(A / l + 4) / 10⌉₊
    let m : ℕ := max 1 ⌈(A / l - 1) / 10⌉₊
    let μ := Regeneration.annealedCoupledLaw Q.measure K
    let ν := regenerationConditionedLaw hd Q lam l K hK.1 hD
    let Δ := Regeneration.Renewal.regenDelta lam
    Integrable (fun ωz => F (reduce ωz.1) * G (translate (ωz.2.1 t) (reduce ωz.1))) μ ∧
    (∫ ωz, F (reduce ωz.1) * G (translate (ωz.2.1 t) (reduce ωz.1)) ∂μ) =
      (∫ ωz in {ωz | (t : ℝ≥0∞) < regenerationTime hd lam l (k + m) ωz.2},
        F (reduce ωz.1) * G (translate (ωz.2.1 t) (reduce ωz.1)) ∂μ) +
      ∑ n ∈ Finset.range (⌊(t : ℝ) / (Δ : ℝ)⌋₊ + 1),
        (∫ ωz in {ωz | regenerationTime hd lam l k ωz.2 =
          (((n : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞)}, F (reduce ωz.1) ∂μ) *
        ∫ ωz in {ωz | regenerationTime hd lam l m ωz.2 ≤
            ((t - (n : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞)},
          G (translate (ωz.2.1 (t - (n : ℝ≥0) * Δ)) (reduce ωz.1)) ∂ν := by
  have hfactor' : kmKFactorSmoothStmt := by
    intro d hd SD l δ hl hs hδ₀ hδ₁
    obtain ⟨C, hC, h⟩ := hfactor d hd SD.ellipticity SD.dependenceRange
      SD.one_le_ellipticity SD.one_le_dependenceRange l δ hl hs hδ₀ hδ₁
    exact ⟨C, hC, h SD.derivativeBound SD.derivativeBound_pos⟩
  intro d hd Λ₀ r₀ hΛ hr
  obtain ⟨l₀, p, hl₀, hsep, hp, hInt⟩ :=
    uniform_covariance_integrable_of_regeneration_tails htails d hd Λ₀ r₀ hΛ hr
  refine ⟨l₀, p, hl₀, hsep, hp, ?_⟩
  intro l δ hl hδ₀ hδ₁ β hβ
  dsimp only
  intro Q hQ lam h₀ h₁ P K hK hD A hA F G hF hFp hG hGp t
  let k : ℕ := max 1 ⌈(A / l + 4) / 10⌉₊
  let m : ℕ := max 1 ⌈(A / l - 1) / 10⌉₊
  let μ := Regeneration.annealedCoupledLaw Q.measure K
  let ν := regenerationConditionedLaw hd Q lam l K hK.1 hD
  let Δ := Regeneration.Renewal.regenDelta lam
  let N := ⌊(t : ℝ) / (Δ : ℝ)⌋₊
  let q := fun n : ℕ => ∫ ωz in {ωz | regenerationTime hd lam l k ωz.2 =
    (((n : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞)}, F (reduce ωz.1) ∂μ
  let Cov := fun J : FieldPair d → ℝ => ∫ ωz,
    F (reduce ωz.1) * J (translate (ωz.2.1 t) (reduce ωz.1)) ∂μ
  let Rem := fun J : FieldPair d → ℝ => ∫ ωz in
    {ωz | (t : ℝ≥0∞) < regenerationTime hd lam l (k + m) ωz.2},
    F (reduce ωz.1) * J (translate (ωz.2.1 t) (reduce ωz.1)) ∂μ
  let H := fun (J : FieldPair d → ℝ) (u : ℝ≥0) => ∫ ωz in
    {ωz | regenerationTime hd lam l m ωz.2 ≤ (u : ℝ≥0∞)},
    J (translate (ωz.2.1 u) (reduce ωz.1)) ∂ν
  let Gc := fun (n : ℕ) (ω : FieldPair d) => max (-(n : ℝ)) (min (n : ℝ) (G ω))
  have hFg : Measurable F := hF.mono (Probability.localSigma_le_borel _) le_rfl
  have hGg : Measurable G := hG.mono (Probability.localSigma_le_borel _) le_rfl
  have hFr : Measurable (fun ωz : FieldPair d × Regeneration.CoupledSample d =>
      F (reduce ωz.1)) := hFg.comp (Probability.measurable_reduce.comp measurable_fst)
  have hobs (u : ℝ≥0) : Measurable
      (fun ωz : FieldPair d × Regeneration.CoupledSample d =>
        G (translate (ωz.2.1 u) (reduce ωz.1))) :=
    hGg.comp (Probability.continuous_translate.measurable.comp
      (((continuous_eval_const u).measurable.comp measurable_snd.fst).prodMk
        (Probability.measurable_reduce.comp measurable_fst)))
  have hi := hInt β hβ Q hQ lam h₀ h₁ l δ hl hδ₀ hδ₁ P K hK hD F G hFg hGg hFp hGp
    t μ (by simp [μ])
  have hiG (u : ℝ≥0) : Integrable
      (fun ωz => G (translate (ωz.2.1 u) (reduce ωz.1))) ν := by
    let : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
    simpa only [one_mul] using
      hInt β hβ Q hQ lam h₀ h₁ l δ hl hδ₀ hδ₁ P K hK hD (fun _ => 1) G
        measurable_const hGg (memLp_const 1) hGp u ν (by simp [ν])
  have hGc (n : ℕ) :
      Measurable[localSigma {x : Vec d | euclideanNorm x < A / lam}] (Gc n) :=
    measurable_const.max (measurable_const.min hG)
  have hb (n : ℕ) : Regeneration.BoundedRealTest (Gc n) := by
    refine ⟨(n : ℝ), fun ω => abs_le.mpr ⟨le_max_left _ _, ?_⟩⟩
    exact max_le
      ((neg_nonpos.mpr (Nat.cast_nonneg n)).trans (Nat.cast_nonneg n)) (min_le_left _ _)
  have hCov : Filter.Tendsto (fun n => Cov (Gc n)) Filter.atTop (𝓝 (Cov G)) := by
    simpa only [Cov, Gc, Measure.restrict_univ] using
      sbxS2_tendsto_setIntegral_mul_clamp μ _ _ hFr (hobs t) hi Set.univ
  have hRem : Filter.Tendsto (fun n => Rem (Gc n)) Filter.atTop (𝓝 (Rem G)) :=
    sbxS2_tendsto_setIntegral_mul_clamp μ _ _ hFr (hobs t) hi _
  have hH (u : ℝ≥0) :
      Filter.Tendsto (fun n => H (Gc n) u) Filter.atTop (𝓝 (H G u)) := by
    simpa only [H, Gc, one_mul] using
      sbxS2_tendsto_setIntegral_mul_clamp ν (fun _ => 1) _ measurable_const (hobs u)
        (by simpa only [one_mul] using hiG u) {ωz | regenerationTime hd lam l m ωz.2 ≤
          (u : ℝ≥0∞)}
  have heq (n : ℕ) : Cov (Gc n) = Rem (Gc n) +
      ∑ j ∈ Finset.range (N + 1), q j * H (Gc n) (t - j * Δ) :=
    (smooth_bounded_covariance_decomposition hfactor' hd
      (D := ⟨Λ₀, r₀, β, hΛ, hr, hβ⟩) (hl₀.trans_le hl)
      (hsep.trans_le (by linarith)) hδ₀ hδ₁ Q hQ lam h₀ h₁ P K hK hD A hA p hp F
      (Gc n) hF hFp (hGc n) (hb n) t).2
  have hsum : Filter.Tendsto
      (fun n => ∑ j ∈ Finset.range (N + 1), q j * H (Gc n) (t - j * Δ))
      Filter.atTop (𝓝 (∑ j ∈ Finset.range (N + 1), q j * H G (t - j * Δ))) :=
    tendsto_finsetSum (Finset.range (N + 1))
      (fun j _ => tendsto_const_nhds.mul (hH (t - j * Δ)))
  refine ⟨hi, ?_⟩
  exact tendsto_nhds_unique hCov ((hRem.add hsum).congr'
    (Filter.Eventually.of_forall (fun n => (heq n).symm)))


theorem uniform_centered_covariance_of_inputs
    (hfactor : kmKFactorUniformSmoothStmt)
    (htails : node_app_u3A_regen_u2D_tailsStmt)
    (hmany : SbxCManyCycleUniformR06.manyCycleSmoothStmt) :
    ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ) (hΛ : 1 ≤ Λ₀) (hr : 1 ≤ r₀),
    ∃ l₀ p : ℝ, 0 < l₀ ∧ r₀ < 2 * l₀ ∧ 2 ≤ p ∧
    ∀ (l δ : ℝ), l₀ ≤ l → 0 < δ → δ < 1 →
    ∀ (β : ℕ → ℝ) (hβ : ∀ k, 1 ≤ k → 0 < β k),
    let SD : StructuralData d := ⟨Λ₀, r₀, β, hΛ, hr, hβ⟩
    ∀ (Q : EnvironmentLaw d SD.ellipticity SD.dependenceRange), HasSmoothBounds SD Q →
    ∀ (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
      (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
      (hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K)
      (hD : Regeneration.annealedCoupledLaw Q.measure K
        (regenerationNoReturn hd (l / lam)) ≠ 0)
      (A : ℝ) (_hA : l ≤ A) (F G : FieldPair d → ℝ)
      (_hF : Measurable[localSigma {x : Vec d | euclideanNorm x < A / lam}] F)
      (_hG : Measurable[localSigma {x : Vec d | euclideanNorm x < A / lam}] G)
      (_hFp : MemLp F (ENNReal.ofReal p) (reducedLaw Q))
      (_hGp : MemLp G (ENNReal.ofReal p) (reducedLaw Q))
      (_hzero : (∫ ω, F ω ∂reducedLaw Q) = 0),
    let k : ℕ := max 1 ⌈(A / l + 4) / 10⌉₊
    let m : ℕ := max 1 ⌈(A / l - 1) / 10⌉₊
    let μ := Regeneration.annealedCoupledLaw Q.measure K
    let ν := regenerationConditionedLaw hd Q lam l K hK.1 hD
    let Δ := Regeneration.Renewal.regenDelta lam
    let pn := regenerationLatticeMass hd Q lam l K hK.1 hD
    let mean := ∑' n : ℕ, (n : ℝ) * pn n
    let q := fun n : ℕ => ∫ ωz in {ωz | regenerationTime hd lam l k ωz.2 =
      (((n : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞)}, F (reduce ωz.1) ∂μ
    let hm := fun t : ℝ≥0 => ∫ ωz in {ωz |
      regenerationTime hd lam l m ωz.2 ≤ (t : ℝ≥0∞)},
      G (translate (ωz.2.1 t) (reduce ωz.1)) ∂ν
    let rm := fun t : ℝ≥0 => ∫ ωz in {ωz |
      regenerationTime hd lam l m ωz.2 ≤ (t : ℝ≥0∞) ∧
      (t : ℝ≥0∞) < regenerationTime hd lam l (m + 1) ωz.2},
      G (translate (ωz.2.1 t) (reduce ωz.1)) ∂ν
    let Hm := fun s : ℝ≥0 => mean⁻¹ * ∑' j : ℕ, rm (s + j * Δ)
    let cov := fun t : ℝ≥0 => ∫ ωz, F (reduce ωz.1) *
      G (translate (ωz.2.1 t) (reduce ωz.1)) ∂μ
    let rem := fun t : ℝ≥0 => ∫ ωz in {ωz | (t : ℝ≥0∞) <
      regenerationTime hd lam l (k + m) ωz.2}, F (reduce ωz.1) *
        G (translate (ωz.2.1 t) (reduce ωz.1)) ∂μ
    Summable q ∧ (∑' n, q n) = 0 ∧
    (∀ t : ℝ≥0, Integrable (fun ωz => F (reduce ωz.1) *
        G (translate (ωz.2.1 t) (reduce ωz.1))) μ ∧
      cov t = rem t + ∑ n ∈ Finset.range (⌊(t : ℝ) / (Δ : ℝ)⌋₊ + 1),
        q n * hm (t - n * Δ)) ∧
    ∀ s : ℝ≥0, s < Δ → ∀ j : ℕ,
      cov (s + j * Δ) = rem (s + j * Δ) +
        (∑ n ∈ Finset.range (j + 1), q n * (hm (s + (j - n) * Δ) - Hm s)) -
        Hm s * ∑' n : ℕ, q (j + 1 + n) := by
  intro d hd Λ₀ r₀ hΛ hr
  obtain ⟨lD, p, hlD, hsepD, hp, hDec⟩ :=
    uniform_covariance_decomposition_of_inputs hfactor htails d hd Λ₀ r₀ hΛ hr
  obtain ⟨lM, _hlM, _hsepM, hCenter⟩ :=
    uniform_centered_slices_of_manyCycleMoment hmany d hd Λ₀ r₀ hΛ hr
  refine ⟨max lD lM, p, hlD.trans_le (le_max_left _ _),
    hsepD.trans_le (by linarith only [le_max_left lD lM]), hp, ?_⟩
  intro l δ hl hδ₀ hδ₁ β hβ
  dsimp only
  intro Q hQ lam h₀ h₁ P K hK hD A hA F G hF hG hFp hGp hzero
  let k : ℕ := max 1 ⌈(A / l + 4) / 10⌉₊
  let m : ℕ := max 1 ⌈(A / l - 1) / 10⌉₊
  let μ := Regeneration.annealedCoupledLaw Q.measure K
  let ν := regenerationConditionedLaw hd Q lam l K hK.1 hD
  let Δ := Regeneration.Renewal.regenDelta lam
  let q := fun n : ℕ => ∫ ωz in {ωz | regenerationTime hd lam l k ωz.2 =
    (((n : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞)}, F (reduce ωz.1) ∂μ
  let hm := fun t : ℝ≥0 => ∫ ωz in
    {ωz | regenerationTime hd lam l m ωz.2 ≤ (t : ℝ≥0∞)},
    G (translate (ωz.2.1 t) (reduce ωz.1)) ∂ν
  have hq : Summable q ∧ (∑' n, q n) = 0 :=
    hCenter l ((le_max_right _ _).trans hl) δ hδ₀ hδ₁ β hβ Q hQ lam h₀ h₁ P K hK hD p
      ((by norm_num : (1 : ℝ) ≤ 2).trans hp) F
      (hF.mono (Probability.localSigma_le_borel _) le_rfl) hFp hzero k
  have hcov := hDec l δ ((le_max_left _ _).trans hl) hδ₀ hδ₁ β hβ Q hQ lam h₀ h₁
    P K hK hD A hA F G hF hFp hG hGp
  refine ⟨hq.1, hq.2, hcov, ?_⟩
  intro s hs j
  have hΔ : 0 < Δ := Real.toNNReal_pos.mpr (inv_pos.mpr (sq_pos_of_pos h₀))
  have hΔR : 0 < (Δ : ℝ) := hΔ
  have hsR : (s : ℝ) < (Δ : ℝ) := hs
  have hquot : ((s + j * Δ : ℝ≥0) : ℝ) / (Δ : ℝ) =
      (s : ℝ) / (Δ : ℝ) + (j : ℝ) := by
    simp only [NNReal.coe_add, NNReal.coe_mul, NNReal.coe_natCast, add_div,
      mul_div_cancel_right₀ _ hΔR.ne']
  have hfloor : ⌊((s + j * Δ : ℝ≥0) : ℝ) / (Δ : ℝ)⌋₊ = j := by
    rw [hquot, Nat.floor_add_natCast (by positivity),
      Nat.floor_eq_zero.mpr ((div_lt_one hΔR).mpr hsR), zero_add]
  rw [(hcov (s + j * Δ)).2, hfloor]
  have htimes : (∑ n ∈ Finset.range (j + 1), q n * hm (s + j * Δ - n * Δ)) =
      ∑ n ∈ Finset.range (j + 1), q n * hm (s + (j - n) * Δ) := by
    apply Finset.sum_congr rfl
    intro n hn
    have hnj : n ≤ j := Nat.le_of_lt_succ (Finset.mem_range.mp hn)
    rw [add_tsub_assoc_of_le (mul_le_mul_of_nonneg_right
      (show (n : ℝ≥0) ≤ j by exact_mod_cast hnj) bot_le),
      ← tsub_mul, ← Nat.cast_tsub]
  rw [htimes, sbxS2_centered_convolution q (fun n => hm (s + (j - n) * Δ))
    _ j hq.1 hq.2, add_sub_assoc]

theorem uniform_slice_decay_normalized
    (hmany : SbxCManyCycleUniformR06.manyCycleSmoothStmt)
    (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ) (hΛ : 1 ≤ Λ₀) (hr : 1 ≤ r₀) :
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
    ∀ k : ℕ, 1 ≤ k → ∀ n : ℕ,
    |∫ ωz in {ωz | regenerationTime hd lam l k ωz.2 =
      (((n : ℝ≥0) * Regeneration.Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)},
      F (reduce ωz.1) ∂Regeneration.annealedCoupledLaw Q.measure K| ≤
      C * Real.exp (C * k - c * n) *
        (eLpNorm F (ENNReal.ofReal p) (reducedLaw Q)).toReal := by
  obtain ⟨l₀, hl₀, hsep, hdec⟩ := uniform_slice_decay_of_manyCycleMoment hmany d hd Λ₀ r₀ hΛ hr
  refine ⟨l₀, hl₀, hsep, ?_⟩
  intro l hl δ hδ₀ hδ₁
  obtain ⟨a, Cq, ha, hCq, hq⟩ := hdec l hl δ hδ₀ hδ₁
  refine ⟨a / 2, 1 + Cq, half_pos ha, by positivity, ?_⟩
  intro β hβ
  dsimp only
  intro Q hQ lam h₀ h₁ P K hK hD p hp F hF hFp k hk n
  apply (hq β hβ Q hQ lam h₀ h₁ P K hK hD p hp F hF hFp k hk n).trans
  apply mul_le_mul_of_nonneg_right _ ENNReal.toReal_nonneg
  calc
    Real.exp ((Cq * k - a * n) / 2) ≤
        Real.exp ((1 + Cq) * k - (a / 2) * n) := by
      apply Real.exp_le_exp.mpr
      have hk₀ : (0 : ℝ) ≤ k := Nat.cast_nonneg _
      nlinarith only [hk₀, mul_nonneg hCq.le hk₀]
    _ ≤ (1 + Cq) * Real.exp ((1 + Cq) * k - (a / 2) * n) := by
      nlinarith only [hCq, Real.exp_pos ((1 + Cq) * k - (a / 2) * n)]

theorem uniform_covariance_power_moment_of_tails
    (htails : node_app_u3A_regen_u2D_tailsStmt) :
    ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ) (hΛ : 1 ≤ Λ₀) (hr : 1 ≤ r₀),
    ∃ l₀ p C : ℝ, 0 < l₀ ∧ r₀ < 2 * l₀ ∧ 2 ≤ p ∧ 0 < C ∧
    ∀ (r : ℝ), 0 < r →
    ∀ (β : ℕ → ℝ) (hβ : ∀ k, 1 ≤ k → 0 < β k),
    let SD : StructuralData d := ⟨Λ₀, r₀, β, hΛ, hr, hβ⟩
    ∀ (Q : EnvironmentLaw d SD.ellipticity SD.dependenceRange), HasSmoothBounds SD Q →
    ∀ (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
      (l δ : ℝ), l₀ ≤ l → 0 < δ → δ < 1 →
    ∀ (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
      (hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K)
      (hD : Regeneration.annealedCoupledLaw Q.measure K
        (regenerationNoReturn hd (l / lam)) ≠ 0),
    ∀ F G : FieldPair d → ℝ, Measurable F → Measurable G →
      MemLp F (ENNReal.ofReal (p * r)) (reducedLaw Q) →
      MemLp G (ENNReal.ofReal (p * r)) (reducedLaw Q) → ∀ t : ℝ≥0,
    ∀ μ ∈ ({Regeneration.annealedCoupledLaw Q.measure K,
      regenerationConditionedLaw hd Q lam l K hK.1 hD} :
        Set (Measure (FieldPair d × Regeneration.CoupledSample d))),
      Integrable (fun ωz => ‖F (reduce ωz.1) *
        G (translate (ωz.2.1 t) (reduce ωz.1))‖ ^ r) μ ∧
      (∫ ωz, ‖F (reduce ωz.1) *
        G (translate (ωz.2.1 t) (reduce ωz.1))‖ ^ r ∂μ) ≤
        C * Real.exp (C * lam ^ 2 * (t : ℝ)) *
          (eLpNorm F (ENNReal.ofReal (p * r)) (reducedLaw Q)).toReal ^ r *
          (eLpNorm G (ENNReal.ofReal (p * r)) (reducedLaw Q)).toReal ^ r := by
  intro d hd Λ₀ r₀ hΛ hr
  obtain ⟨l₀, p, c, C, hl₀, hsep, hp, hc, hC, hrem'⟩ :=
    uniform_remainder_of_regeneration_tails htails d hd Λ₀ r₀ hΛ hr 1 1 (by norm_num) (by norm_num)
  refine ⟨l₀, p, C, hl₀, hsep, hp, hC, ?_⟩
  intro r hr β hβ
  dsimp only
  intro Q hQ lam h₀ h₁ l δ hl hδ₀ hδ₁ P K hK hD F G hF hG hFp hGp t μ hμ
  have hp₀ : 0 ≤ p := le_trans (by norm_num) hp
  have hpow (f : FieldPair d → ℝ)
      (hfp : MemLp f (ENNReal.ofReal (p * r)) (reducedLaw Q)) :
      MemLp (fun ω => ‖f ω‖ ^ r) (ENNReal.ofReal p) (reducedLaw Q) := by
    rw [memLp_iff, eLpNorm_norm_rpow f hfp.aestronglyMeasurable hr,
      ← ENNReal.ofReal_mul hp₀]
    exact ENNReal.rpow_lt_top_of_nonneg hr.le hfp.eLpNorm_ne_top
  have hnorm (f : FieldPair d → ℝ)
      (hfp : MemLp f (ENNReal.ofReal (p * r)) (reducedLaw Q)) :
      (eLpNorm (fun ω => ‖f ω‖ ^ r) (ENNReal.ofReal p) (reducedLaw Q)).toReal =
        (eLpNorm f (ENNReal.ofReal (p * r)) (reducedLaw Q)).toReal ^ r := by
    rw [eLpNorm_norm_rpow f hfp.aestronglyMeasurable hr,
      ← ENNReal.ofReal_mul hp₀, ENNReal.toReal_rpow]
  let : IsProbabilityMeasure (Regeneration.annealedCoupledLaw Q.measure K) :=
    Regeneration.annealedCoupledLaw_isProbabilityMeasure Q.measure K hK.1
  have hprob : Regeneration.annealedCoupledLaw Q.measure K Set.univ ≤
      ENNReal.ofReal (1 * Real.exp (1 * (lam ^ 2 * (t : ℝ)) -
        1 * lam ^ 2 * (t : ℝ))) := by simp
  have hmain := hrem' β hβ Q hQ lam h₀ h₁ l δ hl hδ₀ hδ₁ P K hK hD
    (fun ω => ‖F ω‖ ^ r) (fun ω => ‖G ω‖ ^ r)
    (hF.norm.pow_const r) (hG.norm.pow_const r) (hpow F hFp) (hpow G hGp)
    (lam ^ 2 * (t : ℝ)) t Set.univ (by positivity) MeasurableSet.univ hprob μ hμ
  simp only [integrableOn_univ, Measure.restrict_univ, hnorm F hFp,
    hnorm G hGp] at hmain
  have hident : (fun ωz : FieldPair d × Regeneration.CoupledSample d =>
      ‖F (reduce ωz.1) * G (translate (ωz.2.1 t) (reduce ωz.1))‖ ^ r) =
      (fun ωz => ‖F (reduce ωz.1)‖ ^ r *
        ‖G (translate (ωz.2.1 t) (reduce ωz.1))‖ ^ r) := by
    funext ωz
    rw [norm_mul, Real.mul_rpow (norm_nonneg _) (norm_nonneg _)]
  rw [hident]
  refine ⟨hmain.1, ?_⟩
  have hnonneg : 0 ≤ ∫ ωz, ‖F (reduce ωz.1)‖ ^ r *
      ‖G (translate (ωz.2.1 t) (reduce ωz.1))‖ ^ r ∂μ :=
    integral_nonneg fun _ => by positivity
  rw [abs_of_nonneg hnonneg] at hmain
  apply hmain.2.trans
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hC.le
  have htime : 0 ≤ lam ^ 2 * (t : ℝ) := by positivity
  nlinarith only [mul_nonneg hc.le htime]


theorem uniform_remainder_variable_rate_of_tails
    (htails : node_app_u3A_regen_u2D_tailsStmt) :
    ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ) (hΛ : 1 ≤ Λ₀) (hr : 1 ≤ r₀),
    ∃ l₀ : ℝ, 0 < l₀ ∧ r₀ < 2 * l₀ ∧
    ∀ a : ℝ, 0 < a → ∃ p c C : ℝ, 2 ≤ p ∧ 0 < c ∧ 0 < C ∧
    ∀ (β : ℕ → ℝ) (hβ : ∀ k, 1 ≤ k → 0 < β k),
    let SD : StructuralData d := ⟨Λ₀, r₀, β, hΛ, hr, hβ⟩
    ∀ (Q : EnvironmentLaw d SD.ellipticity SD.dependenceRange), HasSmoothBounds SD Q →
    ∀ (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
      (l δ : ℝ), l₀ ≤ l → 0 < δ → δ < 1 →
    ∀ (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
      (_hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K)
      (_hD : Regeneration.annealedCoupledLaw Q.measure K
        (regenerationNoReturn hd (l / lam)) ≠ 0),
    ∀ F G : FieldPair d → ℝ, Measurable F → Measurable G →
      MemLp F (ENNReal.ofReal p) (reducedLaw Q) →
      MemLp G (ENNReal.ofReal p) (reducedLaw Q) →
    ∀ (J : ℝ) (t : ℝ≥0) (E : Set (FieldPair d × Regeneration.CoupledSample d)),
      0 ≤ J → Regeneration.annealedCoupledLaw Q.measure K E ≤
        ENNReal.ofReal (Real.exp (J - a * lam ^ 2 * (t : ℝ))) →
      IntegrableOn (fun ωz => F (reduce ωz.1) *
        G (translate (ωz.2.1 t) (reduce ωz.1))) E
        (Regeneration.annealedCoupledLaw Q.measure K) ∧
      |∫ ωz in E, F (reduce ωz.1) *
        G (translate (ωz.2.1 t) (reduce ωz.1))
          ∂Regeneration.annealedCoupledLaw Q.measure K| ≤
        C * Real.exp (C * J - c * lam ^ 2 * (t : ℝ)) *
          (eLpNorm F (ENNReal.ofReal p) (reducedLaw Q)).toReal *
          (eLpNorm G (ENNReal.ofReal p) (reducedLaw Q)).toReal := by
  intro d hd Λ₀ r₀ hΛ hr
  obtain ⟨l₀, p₀, D, hl₀, hsep, hp₀, hDpos, hmoment⟩ :=
    uniform_covariance_power_moment_of_tails htails d hd Λ₀ r₀ hΛ hr
  refine ⟨l₀, hl₀, hsep, ?_⟩
  intro a ha
  obtain ⟨r, c, C, hr, hc, hC, hscalar⟩ :=
    sbxS2_power_interpolation_constants D a hDpos ha
  have hr₁ : 1 < r := lt_of_lt_of_le (by norm_num) hr
  have hr₀ : 0 < r := lt_trans zero_lt_one hr₁
  have hp₀pos : 0 ≤ p₀ := le_trans (by norm_num) hp₀
  refine ⟨p₀ * r, c, C, ?_, hc, hC, ?_⟩
  · exact hp₀.trans (le_mul_of_one_le_right hp₀pos hr₁.le)
  intro β hβ
  dsimp only
  intro Q hQ lam h₀ h₁ l δ hl hδ₀ hδ₁ P K hK hD F G hF hG hFp hGp J t E hJ hprob
  let μ := Regeneration.annealedCoupledLaw Q.measure K
  let f := fun ωz : FieldPair d × Regeneration.CoupledSample d =>
    F (reduce ωz.1) * G (translate (ωz.2.1 t) (reduce ωz.1))
  have hfm : Measurable f :=
    ((hF.comp Probability.measurable_reduce).comp measurable_fst).mul
      (hG.comp (Probability.continuous_translate.measurable.comp
        (((continuous_eval_const t).measurable.comp measurable_snd.fst).prodMk
          (Probability.measurable_reduce.comp measurable_fst))))
  have hpower := hmoment r hr₀ β hβ Q hQ lam h₀ h₁ l δ hl hδ₀ hδ₁ P K hK hD
    F G hF hG hFp hGp t μ (Set.mem_insert _ _)
  let : IsProbabilityMeasure μ :=
    Regeneration.annealedCoupledLaw_isProbabilityMeasure Q.measure K hK.1
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

theorem uniform_regeneration_remainder_decay_of_inputs
    (hmany : SbxCManyCycleUniformR06.manyCycleSmoothStmt)
    (htails : node_app_u3A_regen_u2D_tailsStmt) :
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
        (regenerationNoReturn hd (l / lam)) ≠ 0),
    ∀ F G : FieldPair d → ℝ, Measurable F → Measurable G →
      MemLp F (ENNReal.ofReal p) (reducedLaw Q) →
      MemLp G (ENNReal.ofReal p) (reducedLaw Q) → ∀ j : ℕ, 1 ≤ j → ∀ t : ℝ≥0,
      IntegrableOn (fun ωz => F (reduce ωz.1) *
        G (translate (ωz.2.1 t) (reduce ωz.1)))
        {ωz | (t : ℝ≥0∞) < regenerationTime hd lam l j ωz.2}
        (Regeneration.annealedCoupledLaw Q.measure K) ∧
      |∫ ωz in {ωz | (t : ℝ≥0∞) < regenerationTime hd lam l j ωz.2},
        F (reduce ωz.1) * G (translate (ωz.2.1 t) (reduce ωz.1))
          ∂Regeneration.annealedCoupledLaw Q.measure K| ≤
        C * Real.exp (C * j - c * lam ^ 2 * (t : ℝ)) *
          (eLpNorm F (ENNReal.ofReal p) (reducedLaw Q)).toReal *
          (eLpNorm G (ENNReal.ofReal p) (reducedLaw Q)).toReal := by
  intro d hd Λ₀ r₀ hΛ hr
  obtain ⟨lR, hlR, hsep, hrate⟩ := uniform_remainder_variable_rate_of_tails htails d hd Λ₀ r₀ hΛ hr
  obtain ⟨lM, hlM, _hsepM, hmoment⟩ := hmany d hd Λ₀ r₀ hΛ hr
  refine ⟨max lR lM, lt_of_lt_of_le hlR (le_max_left _ _),
    hsep.trans_le (mul_le_mul_of_nonneg_left (le_max_left _ _) (by norm_num)), ?_⟩
  intro l hl δ hδ₀ hδ₁
  have hlR' := (le_max_left lR lM).trans hl
  have hlM' := (le_max_right lR lM).trans hl
  obtain ⟨a, M, S, ha, hM, hS, hm⟩ := hmoment l hlM' δ hδ₀ hδ₁
  obtain ⟨p, c, C, hp, hc, hC, hbound⟩ := hrate a ha
  let D := 1 + C + C * (S + M)
  have hDpos : 0 < D := by dsimp only [D]; positivity
  have hCD : C ≤ D := by dsimp only [D]; nlinarith only [mul_pos hC (add_pos hS hM)]
  have hcycle : C * (S + M) ≤ D := by dsimp only [D]; linarith only [hC]
  refine ⟨p, c, D, hp, hc, hDpos, ?_⟩
  intro β hβ
  dsimp only
  intro Q hQ lam h₀ h₁ P K hK hD F G hF hG hFp hGp j hj t
  let μ := Regeneration.annealedCoupledLaw Q.measure K
  let J := (S + M) * (j : ℝ)
  have hJ : 0 ≤ J := by dsimp only [J]; positivity
  have hj' : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hgeom : S * M ^ j ≤ Real.exp J := by
    have hself : S ≤ Real.exp S := by linarith only [Real.add_one_le_exp S]
    have hSp : S ≤ Real.exp (S * j) :=
      hself.trans (Real.exp_le_exp.mpr (by nlinarith only [hS.le, hj']))
    have hMp : M ≤ Real.exp M := by linarith only [Real.add_one_le_exp M]
    calc
      _ ≤ Real.exp (S * j) * Real.exp M ^ j :=
        mul_le_mul hSp (pow_le_pow_left₀ hM.le hMp j)
          (pow_nonneg hM.le j) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; dsimp only [J]; ring
  have htail : μ {ωz | (t : ℝ≥0∞) < regenerationTime hd lam l j ωz.2} ≤
      ENNReal.ofReal (Real.exp (J - a * lam ^ 2 * (t : ℝ))) := by
    have hm' := ((hm β hβ Q hQ lam h₀ h₁ P K hK hD).2 j).trans
      (ENNReal.ofReal_le_ofReal hgeom)
    have ht := exponential_time_tail μ
      (fun ωz : FieldPair d × Regeneration.CoupledSample d =>
        regenerationTime hd lam l j ωz.2)
      ((Regeneration.measurable_regenerationTime _ _ _ _ _).comp measurable_snd)
      (a * lam ^ 2) (Real.exp J) (by positivity) t hm'
    simpa only [← Real.exp_add, neg_mul, sub_eq_add_neg] using ht
  have hb := hbound β hβ Q hQ lam h₀ h₁ l δ hlR' hδ₀ hδ₁ P K hK hD
    F G hF hG hFp hGp J t _ hJ htail
  refine ⟨hb.1, hb.2.trans ?_⟩
  apply mul_le_mul_of_nonneg_right _ ENNReal.toReal_nonneg
  apply mul_le_mul_of_nonneg_right _ ENNReal.toReal_nonneg
  apply mul_le_mul hCD (Real.exp_le_exp.mpr ?_) (Real.exp_pos _).le hDpos.le
  dsimp only [J]
  nlinarith only [mul_le_mul_of_nonneg_right hcycle (Nat.cast_nonneg j : (0 : ℝ) ≤ j)]


theorem uniform_covariance_sub_remainder_decay_of_inputs
    (hfactor : kmKFactorUniformSmoothStmt)
    (htails : node_app_u3A_regen_u2D_tailsStmt)
    (hmany : SbxCManyCycleUniformR06.manyCycleSmoothStmt)
    (hphase : SbxCPhaseUniformR07.phaseUniformStmt) :
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
    let k : ℕ := max 1 ⌈(A / l + 4) / 10⌉₊
    let m : ℕ := max 1 ⌈(A / l - 1) / 10⌉₊
    let μ := Regeneration.annealedCoupledLaw Q.measure K
    let Δ := Regeneration.Renewal.regenDelta lam
    let cov := fun t : ℝ≥0 => ∫ ωz, F (reduce ωz.1) *
      G (translate (ωz.2.1 t) (reduce ωz.1)) ∂μ
    let rem := fun t : ℝ≥0 => ∫ ωz in {ωz | (t : ℝ≥0∞) <
      regenerationTime hd lam l (k + m) ωz.2}, F (reduce ωz.1) *
        G (translate (ωz.2.1 t) (reduce ωz.1)) ∂μ
    ∀ s : ℝ≥0, s < Δ → ∀ j : ℕ,
      |cov (s + j * Δ) - rem (s + j * Δ)| ≤
        C * Real.exp (C * (k + m) - c * j) *
          (eLpNorm F (ENNReal.ofReal p) (reducedLaw Q)).toReal *
          (eLpNorm G (ENNReal.ofReal p) (reducedLaw Q)).toReal := by
  intro d hd Λ₀ r₀ hΛ hr
  obtain ⟨lD, pD, hlD, hsepD, hpD, hcenter⟩ :=
    uniform_centered_covariance_of_inputs hfactor htails hmany d hd Λ₀ r₀ hΛ hr
  obtain ⟨lM, _hlM, _hsepM, hdecay⟩ :=
    uniform_slice_decay_of_manyCycleMoment hmany d hd Λ₀ r₀ hΛ hr
  obtain ⟨lP, _hlP, _hsepP, hph⟩ := hphase d hd Λ₀ r₀ hΛ hr
  refine ⟨max lD (max lM lP), hlD.trans_le (le_max_left _ _),
    hsepD.trans_le (by linarith only [le_max_left lD (max lM lP)]), ?_⟩
  intro l hl δ hδ₀ hδ₁
  have hlD' : lD ≤ l := (le_max_left _ _).trans hl
  have hlM' : lM ≤ l := (le_max_left _ _).trans ((le_max_right _ _).trans hl)
  have hlP' : lP ≤ l := (le_max_right _ _).trans ((le_max_right _ _).trans hl)
  have hlpos : 0 < l := hlD.trans_le hlD'
  obtain ⟨a, Cq, ha, hCq, hqd⟩ := hdecay l hlM' δ hδ₀ hδ₁
  obtain ⟨pP, b, Cp, hpP, hb, hCp, hpd⟩ := hph l hlP' δ hδ₀ hδ₁
  let p := max pD pP
  let c := min (a / 2) b / 2
  let B := (1 + 2 / min (a / 2) b) + (1 - Real.exp (-(a / 2)))⁻¹
  have ha' : 0 < a / 2 := half_pos ha
  have hmin : 0 < min (a / 2) b := lt_min ha' hb
  have hden : 0 < 1 - Real.exp (-(a / 2)) :=
    sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_neg_of_pos ha'))
  have hB : 0 < B := by dsimp only [B]; positivity
  let C := 1 + Cp * B + Cq + Cp
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨p, c, C, hpD.trans (le_max_left _ _), half_pos hmin, hC, ?_⟩
  intro β hβ
  dsimp only
  intro Q hQ lam h₀ h₁ P K hK hD A hA F G hF hG hFp hGp hzero
  let := reducedLaw_probability Q
  let k : ℕ := max 1 ⌈(A / l + 4) / 10⌉₊
  let m : ℕ := max 1 ⌈(A / l - 1) / 10⌉₊
  let μ := Regeneration.annealedCoupledLaw Q.measure K
  let ν := regenerationConditionedLaw hd Q lam l K hK.1 hD
  let Δ := Regeneration.Renewal.regenDelta lam
  let q := fun n : ℕ => ∫ ωz in {ωz | regenerationTime hd lam l k ωz.2 =
    (((n : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞)}, F (reduce ωz.1) ∂μ
  let hm := fun t : ℝ≥0 => ∫ ωz in {ωz |
    regenerationTime hd lam l m ωz.2 ≤ (t : ℝ≥0∞)},
    G (translate (ωz.2.1 t) (reduce ωz.1)) ∂ν
  let rm := fun t : ℝ≥0 => ∫ ωz in {ωz |
    regenerationTime hd lam l m ωz.2 ≤ (t : ℝ≥0∞) ∧
    (t : ℝ≥0∞) < regenerationTime hd lam l (m + 1) ωz.2},
    G (translate (ωz.2.1 t) (reduce ωz.1)) ∂ν
  let Hm := fun s : ℝ≥0 => (∑' n : ℕ, (n : ℝ) *
    regenerationLatticeMass hd Q lam l K hK.1 hD n)⁻¹ * ∑' j : ℕ, rm (s + j * Δ)
  let Nf := (eLpNorm F (ENNReal.ofReal p) (reducedLaw Q)).toReal
  let Ng := (eLpNorm G (ENNReal.ofReal p) (reducedLaw Q)).toReal
  have hpD' : ENNReal.ofReal pD ≤ ENNReal.ofReal p :=
    ENNReal.ofReal_le_ofReal (le_max_left _ _)
  have hpP' : ENNReal.ofReal pP ≤ ENNReal.ofReal p :=
    ENNReal.ofReal_le_ofReal (le_max_right _ _)
  have hNg : (eLpNorm G (ENNReal.ofReal pP) (reducedLaw Q)).toReal ≤ Ng :=
    ENNReal.toReal_mono hGp.eLpNorm_ne_top (eLpNorm_le_eLpNorm_of_exponent_le hpP')
  have hco := hcenter l δ hlD' hδ₀ hδ₁ β hβ Q hQ lam h₀ h₁ P K hK hD A hA F G hF hG
    (hFp.mono_exponent hpD') (hGp.mono_exponent hpD') hzero
  have hsupport : 10 * (m : ℝ) * l - l - A ≥ -2 * l := by
    have hx : (A / l - 1) / 10 ≤ (m : ℝ) := (Nat.le_ceil _).trans
      (by exact_mod_cast le_max_right 1 ⌈(A / l - 1) / 10⌉₊)
    have hdiv : A / l ≤ 10 * (m : ℝ) + 1 := by linarith
    have := (div_le_iff₀ hlpos).mp hdiv
    nlinarith
  have hpa := hpd β hβ Q hQ lam h₀ h₁ P K hK hD A m hA (le_max_left _ _) hsupport G hG
    (hGp.mono_exponent hpP')
  intro s hs j
  have hpa' := hpa.2 s hs
  let Rq := Real.exp (Cq * k / 2) * Nf
  let Rh := Cp * Real.exp (Cp * m) * Ng
  have hRq : 0 ≤ Rq := by dsimp only [Rq, Nf]; positivity
  have hRh : 0 ≤ Rh := by dsimp only [Rh, Ng]; positivity
  have hq : ∀ n : ℕ, |q n| ≤ Rq * Real.exp (-(a / 2) * n) := by
    intro n
    calc _ ≤ Real.exp ((Cq * k - a * n) / 2) * Nf :=
        hqd β hβ Q hQ lam h₀ h₁ P K hK hD p (hpD.trans (le_max_left _ _)) F
          (hF.mono (Probability.localSigma_le_borel _) le_rfl) hFp k (le_max_left _ _) n
      _ = _ := by
        dsimp only [Rq]
        rw [show (Cq * k - a * n) / 2 = Cq * k / 2 + (-(a / 2) * n) by ring,
          Real.exp_add]
        ring
  have hh : ∀ n : ℕ, |hm (s + n * Δ) - Hm s| ≤ Rh * Real.exp (-b * n) := by
    intro n
    calc _ ≤ Cp * Real.exp (Cp * m - b * n) *
          (eLpNorm G (ENNReal.ofReal pP) (reducedLaw Q)).toReal := (hpa'.2.2 n).2.2
      _ ≤ Cp * Real.exp (Cp * m - b * n) * Ng :=
        mul_le_mul_of_nonneg_left hNg (by positivity)
      _ = _ := by
        dsimp only [Rh]
        rw [show Cp * m - b * n = Cp * m + (-b * n) by ring, Real.exp_add]
        ring
  have hH : |Hm s| ≤ Rh := hpa'.2.1.trans
    (mul_le_mul_of_nonneg_left hNg (by positivity))
  have hest := sbxS2_centered_convolution_decay q (fun n => hm (s + n * Δ))
    (Hm s) Rq Rh (a / 2) b hRq hRh ha' hb hq hh hH j
  simp only [Nat.cast_tsub] at hest
  have heq := hco.2.2.2 s hs j
  have hid : (∫ ωz, F (reduce ωz.1) * G (translate
        (ωz.2.1 (s + j * Δ)) (reduce ωz.1)) ∂μ) -
      (∫ ωz in {ωz | ((s + j * Δ : ℝ≥0) : ℝ≥0∞) <
        regenerationTime hd lam l (k + m) ωz.2}, F (reduce ωz.1) *
          G (translate (ωz.2.1 (s + j * Δ)) (reduce ωz.1)) ∂μ) =
      (∑ n ∈ Finset.range (j + 1), q n * (hm (s + (j - n) * Δ) - Hm s)) -
        Hm s * ∑' n : ℕ, q (j + 1 + n) := by linarith only [heq]
  rw [hid]
  apply hest.trans
  have hcoeff : Cp * B ≤ C := by dsimp only [C]; linarith
  have hexp : Cq * k / 2 + Cp * m ≤ C * (k + m) := by
    have hk₀ : (0 : ℝ) ≤ k := Nat.cast_nonneg _
    have hm₀ : (0 : ℝ) ≤ m := Nat.cast_nonneg _
    have hCq' : Cq / 2 ≤ C := by dsimp only [C]; nlinarith only [hCp, hCq, hB, mul_pos hCp hB]
    have hCp' : Cp ≤ C := by dsimp only [C]; linarith only [hCq, mul_pos hCp hB]
    nlinarith only [mul_nonneg (sub_nonneg.mpr hCq') hk₀,
      mul_nonneg (sub_nonneg.mpr hCp') hm₀]
  calc
    Rq * Rh * B * Real.exp (-(min (a / 2) b / 2) * j) =
        (Cp * B) * Real.exp (Cq * k / 2 + Cp * m - c * j) * Nf * Ng := by
      dsimp only [Rq, Rh, c]
      simp only [sub_eq_add_neg, neg_mul, Real.exp_add]
      ring
    _ ≤ C * Real.exp (C * (k + m) - c * j) * Nf * Ng := by
      gcongr



theorem uniform_covariance_sub_remainder_time_decay_of_inputs
    (hfactor : kmKFactorUniformSmoothStmt)
    (htails : node_app_u3A_regen_u2D_tailsStmt)
    (hmany : SbxCManyCycleUniformR06.manyCycleSmoothStmt)
    (hphase : SbxCPhaseUniformR07.phaseUniformStmt) :
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
    let k : ℕ := max 1 ⌈(A / l + 4) / 10⌉₊
    let m : ℕ := max 1 ⌈(A / l - 1) / 10⌉₊
    let μ := Regeneration.annealedCoupledLaw Q.measure K
    let cov := fun t : ℝ≥0 => ∫ ωz, F (reduce ωz.1) *
      G (translate (ωz.2.1 t) (reduce ωz.1)) ∂μ
    let rem := fun t : ℝ≥0 => ∫ ωz in {ωz | (t : ℝ≥0∞) <
      regenerationTime hd lam l (k + m) ωz.2}, F (reduce ωz.1) *
        G (translate (ωz.2.1 t) (reduce ωz.1)) ∂μ
    ∀ t : ℝ≥0, |cov t - rem t| ≤
      C * Real.exp (C * (k + m) - c * lam ^ 2 * (t : ℝ)) *
        (eLpNorm F (ENNReal.ofReal p) (reducedLaw Q)).toReal *
        (eLpNorm G (ENNReal.ofReal p) (reducedLaw Q)).toReal := by
  intro d hd Λ₀ r₀ hΛ hr
  obtain ⟨l₀, hl₀, hsep, hdec⟩ :=
    uniform_covariance_sub_remainder_decay_of_inputs hfactor htails hmany hphase d hd Λ₀ r₀ hΛ hr
  refine ⟨l₀, hl₀, hsep, ?_⟩
  intro l hl δ hδ₀ hδ₁
  obtain ⟨p, c, C, hp, hc, hC, hbound⟩ := hdec l hl δ hδ₀ hδ₁
  let D := C * Real.exp c + C
  have hDpos : 0 < D := by dsimp only [D]; positivity
  have hCD : C ≤ D := by dsimp only [D]; linarith only [mul_pos hC (Real.exp_pos c)]
  refine ⟨p, c, D, hp, hc, hDpos, ?_⟩
  intro β hβ
  dsimp only
  intro Q hQ lam h₀ h₁ P K hK hD A hA F G hF hG hFp hGp hzero
  intro t
  let Δ := Regeneration.Renewal.regenDelta lam
  have hΔ : 0 < (Δ : ℝ) := Real.toNNReal_pos.mpr (inv_pos.mpr (sq_pos_of_pos h₀))
  have hΔcoe : (Δ : ℝ) = (lam ^ 2)⁻¹ :=
    Real.coe_toNNReal _ (inv_nonneg.mpr (sq_nonneg lam))
  let j : ℕ := ⌊(t : ℝ) / (Δ : ℝ)⌋₊
  have hfloor : (j : ℝ) ≤ (t : ℝ) / (Δ : ℝ) := Nat.floor_le (by positivity)
  have hupper : (t : ℝ) / (Δ : ℝ) < (j : ℝ) + 1 := Nat.lt_floor_add_one _
  have hmul : (j : ℝ≥0) * Δ ≤ t := by
    apply NNReal.coe_le_coe.mp
    simpa only [NNReal.coe_mul, NNReal.coe_natCast] using (le_div_iff₀ hΔ).mp hfloor
  let s := t - (j : ℝ≥0) * Δ
  have hsum : s + j * Δ = t := tsub_add_cancel_of_le hmul
  have hs : s < Δ := by
    have ht : (t : ℝ) < ((j : ℝ) + 1) * (Δ : ℝ) := (div_lt_iff₀ hΔ).mp hupper
    have hsumR := congrArg (fun x : ℝ≥0 => (x : ℝ)) hsum
    simp only [NNReal.coe_add, NNReal.coe_mul, NNReal.coe_natCast] at hsumR
    change (s : ℝ) < (Δ : ℝ)
    nlinarith only [ht, hsumR]
  have htime : lam ^ 2 * (t : ℝ) < (j : ℝ) + 1 := by
    simpa only [hΔcoe, div_inv_eq_mul, mul_comm] using hupper
  have hmain := hbound β hβ Q hQ lam h₀ h₁ P K hK hD A hA F G hF hG hFp hGp hzero s hs j
  rw [hsum] at hmain
  apply hmain.trans
  apply mul_le_mul_of_nonneg_right _ ENNReal.toReal_nonneg
  apply mul_le_mul_of_nonneg_right _ ENNReal.toReal_nonneg
  let N : ℝ := (max 1 ⌈(A / l + 4) / 10⌉₊ : ℕ) +
    (max 1 ⌈(A / l - 1) / 10⌉₊ : ℕ)
  change C * Real.exp (C * N - c * j) ≤
    D * Real.exp (D * N - c * lam ^ 2 * (t : ℝ))
  have hcycle : C * N ≤ D * N :=
    mul_le_mul_of_nonneg_right hCD (by positivity)
  calc
    C * Real.exp (C * N - c * j) ≤
        C * Real.exp (D * N - c * lam ^ 2 * (t : ℝ) + c) := by
      apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hC.le
      nlinarith only [hcycle, mul_lt_mul_of_pos_left htime hc]
    _ = (C * Real.exp c) * Real.exp (D * N - c * lam ^ 2 * (t : ℝ)) := by
      rw [Real.exp_add]
      ring
    _ ≤ D * Real.exp (D * N - c * lam ^ 2 * (t : ℝ)) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      dsimp only [D]
      linarith only [hC]



theorem uniform_covariance_and_remainder_decay_of_inputs
    (hfactor : kmKFactorUniformSmoothStmt)
    (htails : node_app_u3A_regen_u2D_tailsStmt)
    (hmany : SbxCManyCycleUniformR06.manyCycleSmoothStmt)
    (hphase : SbxCPhaseUniformR07.phaseUniformStmt) :
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
    let k : ℕ := max 1 ⌈(A / l + 4) / 10⌉₊
    let m : ℕ := max 1 ⌈(A / l - 1) / 10⌉₊
    let μ := Regeneration.annealedCoupledLaw Q.measure K
    let cov := fun t : ℝ≥0 => ∫ ωz, F (reduce ωz.1) *
      G (translate (ωz.2.1 t) (reduce ωz.1)) ∂μ
    let rem := fun t : ℝ≥0 => ∫ ωz in {ωz | (t : ℝ≥0∞) <
      regenerationTime hd lam l (k + m) ωz.2}, F (reduce ωz.1) *
        G (translate (ωz.2.1 t) (reduce ωz.1)) ∂μ
    ∀ t : ℝ≥0,
      (|rem t| ≤
      C * Real.exp (C * (k + m) - c * lam ^ 2 * (t : ℝ)) *
        (eLpNorm F (ENNReal.ofReal p) (reducedLaw Q)).toReal *
        (eLpNorm G (ENNReal.ofReal p) (reducedLaw Q)).toReal) ∧
      |cov t| ≤ C * Real.exp (C * (k + m) - c * lam ^ 2 * (t : ℝ)) *
        (eLpNorm F (ENNReal.ofReal p) (reducedLaw Q)).toReal *
        (eLpNorm G (ENNReal.ofReal p) (reducedLaw Q)).toReal := by
  intro d hd Λ₀ r₀ hΛ hr
  obtain ⟨lD, hlD, hsepD, hdec⟩ :=
    uniform_covariance_sub_remainder_time_decay_of_inputs hfactor htails hmany hphase d hd Λ₀ r₀ hΛ hr
  obtain ⟨lR, _hlR, _hsepR, hremdec⟩ :=
    uniform_regeneration_remainder_decay_of_inputs hmany htails d hd Λ₀ r₀ hΛ hr
  refine ⟨max lD lR, hlD.trans_le (le_max_left _ _),
    hsepD.trans_le (by linarith only [le_max_left lD lR]), ?_⟩
  intro l hl δ hδ₀ hδ₁
  obtain ⟨pD, cD, CD, hpD, hcD, hCD, hboundD⟩ :=
    hdec l ((le_max_left _ _).trans hl) δ hδ₀ hδ₁
  obtain ⟨pR, cR, CR, _hpR, hcR, hCR, hboundR⟩ :=
    hremdec l ((le_max_right _ _).trans hl) δ hδ₀ hδ₁
  let p := max pD pR
  let c := min cD cR
  let C := 1 + CD + CR
  have hC : 0 < C := by dsimp only [C]; positivity
  have hDC : CD ≤ C := by dsimp only [C]; linarith only [hCR]
  have hRC : CR ≤ C := by dsimp only [C]; linarith only [hCD]
  refine ⟨p, c, C, hpD.trans (le_max_left _ _), lt_min hcD hcR, hC, ?_⟩
  intro β hβ
  dsimp only
  intro Q hQ lam h₀ h₁ P K hK hD A hA F G hF hG hFp hGp hzero
  let := reducedLaw_probability Q
  let k : ℕ := max 1 ⌈(A / l + 4) / 10⌉₊
  let m : ℕ := max 1 ⌈(A / l - 1) / 10⌉₊
  let μ := Regeneration.annealedCoupledLaw Q.measure K
  let cov := fun t : ℝ≥0 => ∫ ωz, F (reduce ωz.1) *
    G (translate (ωz.2.1 t) (reduce ωz.1)) ∂μ
  let rem := fun t : ℝ≥0 => ∫ ωz in {ωz | (t : ℝ≥0∞) <
    regenerationTime hd lam l (k + m) ωz.2}, F (reduce ωz.1) *
      G (translate (ωz.2.1 t) (reduce ωz.1)) ∂μ
  let Nf := (eLpNorm F (ENNReal.ofReal p) (reducedLaw Q)).toReal
  let Ng := (eLpNorm G (ENNReal.ofReal p) (reducedLaw Q)).toReal
  have hpD' : ENNReal.ofReal pD ≤ ENNReal.ofReal p :=
    ENNReal.ofReal_le_ofReal (le_max_left _ _)
  have hpR' : ENNReal.ofReal pR ≤ ENNReal.ofReal p :=
    ENNReal.ofReal_le_ofReal (le_max_right _ _)
  have hnormF (q : ℝ) (hq : ENNReal.ofReal q ≤ ENNReal.ofReal p) :
      (eLpNorm F (ENNReal.ofReal q) (reducedLaw Q)).toReal ≤ Nf :=
    ENNReal.toReal_mono hFp.eLpNorm_ne_top (eLpNorm_le_eLpNorm_of_exponent_le hq)
  have hnormG (q : ℝ) (hq : ENNReal.ofReal q ≤ ENNReal.ofReal p) :
      (eLpNorm G (ENNReal.ofReal q) (reducedLaw Q)).toReal ≤ Ng :=
    ENNReal.toReal_mono hGp.eLpNorm_ne_top (eLpNorm_le_eLpNorm_of_exponent_le hq)
  have hbD := hboundD β hβ Q hQ lam h₀ h₁ P K hK hD A hA F G hF hG
    (hFp.mono_exponent hpD') (hGp.mono_exponent hpD') hzero
  have hbR := hboundR β hβ Q hQ lam h₀ h₁ P K hK hD F G
    (hF.mono (Probability.localSigma_le_borel _) le_rfl)
    (hG.mono (Probability.localSigma_le_borel _) le_rfl)
    (hFp.mono_exponent hpR') (hGp.mono_exponent hpR') (k + m)
    (by dsimp only [k, m]; omega)
  intro t
  let E := Real.exp (C * (k + m) - c * lam ^ 2 * (t : ℝ))
  have hdiff : |cov t - rem t| ≤ CD * E * Nf * Ng := by
    apply (hbD t).trans
    simpa only [E, mul_assoc, Nat.cast_add] using sbxS2_exp_decay_product_mono CD C cD c
      (k + m) (lam ^ 2 * (t : ℝ)) _ _ Nf Ng hCD.le hDC (min_le_left _ _)
      (by positivity) (by positivity) ENNReal.toReal_nonneg ENNReal.toReal_nonneg
      (hnormF _ hpD') (hnormG _ hpD')
  have hrest : |rem t| ≤ CR * E * Nf * Ng := by
    apply (hbR t).2.trans
    simpa only [E, mul_assoc, Nat.cast_add] using sbxS2_exp_decay_product_mono CR C cR c
      (k + m) (lam ^ 2 * (t : ℝ)) _ _ Nf Ng hCR.le hRC (min_le_right _ _)
      (by positivity) (by positivity) ENNReal.toReal_nonneg ENNReal.toReal_nonneg
      (hnormF _ hpR') (hnormG _ hpR')
  have hE : 0 ≤ E := (Real.exp_pos _).le
  refine ⟨hrest.trans ?_, ?_⟩
  · change CR * E * Nf * Ng ≤ C * E * Nf * Ng
    gcongr
  · calc
      |cov t| = |(cov t - rem t) + rem t| := by congr 1; ring
      _ ≤ |cov t - rem t| + |rem t| := abs_add_le _ _
      _ ≤ CD * E * Nf * Ng + CR * E * Nf * Ng := add_le_add hdiff hrest
      _ = (CD + CR) * E * Nf * Ng := by ring
      _ ≤ C * E * Nf * Ng := by
        have hsum : CD + CR ≤ C := by dsimp only [C]; linarith
        gcongr



theorem uniform_positiveKmFullRange_of_inputs
    (hfactor : kmKFactorUniformSmoothStmt)
    (htails : node_app_u3A_regen_u2D_tailsStmt)
    (hmany : SbxCManyCycleUniformR06.manyCycleSmoothStmt)
    (hphase : SbxCPhaseUniformR07.phaseUniformStmt) :
    ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ) (hΛ : 1 ≤ Λ₀) (hr : 1 ≤ r₀),
    ∃ l₀ : ℝ, 0 < l₀ ∧ r₀ < 2 * l₀ ∧
    ∀ l : ℝ, l₀ ≤ l → ∀ δ : ℝ, 0 < δ → δ < 1 →
    ∃ p c C : ℝ, 2 ≤ p ∧ 0 < c ∧ 0 < C ∧
      ∀ (β : ℕ → ℝ) (hβ : ∀ k, 1 ≤ k → 0 < β k),
      let SD : StructuralData d := ⟨Λ₀, r₀, β, hΛ, hr, hβ⟩
      SmoothPositiveKmBound hd SD l δ p c C 1 := by
  intro d hd Λ₀ r₀ hΛ hr
  obtain ⟨lA, pA, hlA, hsepA, hpA, halgebra⟩ :=
    uniform_centered_covariance_of_inputs hfactor htails hmany d hd Λ₀ r₀ hΛ hr
  obtain ⟨lQ, _hlQ, _hsepQ, hslice⟩ :=
    uniform_slice_decay_normalized hmany d hd Λ₀ r₀ hΛ hr
  obtain ⟨lB, _hlB, _hsepB, hdecay⟩ :=
    uniform_covariance_and_remainder_decay_of_inputs hfactor htails hmany hphase d hd Λ₀ r₀ hΛ hr
  refine ⟨max lA (max lQ lB), hlA.trans_le (le_max_left _ _),
    hsepA.trans_le (by linarith only [le_max_left lA (max lQ lB)]), ?_⟩
  intro l hl δ hδ₀ hδ₁
  have hlA' : lA ≤ l := (le_max_left _ _).trans hl
  have hlQ' : lQ ≤ l := (le_max_left _ _).trans ((le_max_right _ _).trans hl)
  have hlB' : lB ≤ l := (le_max_right _ _).trans ((le_max_right _ _).trans hl)
  have hlpos : 0 < l := hlA.trans_le hlA'
  obtain ⟨cQ, CQ, hcQ, hCQ, hq⟩ := hslice l hlQ' δ hδ₀ hδ₁
  obtain ⟨pB, cB, CB, _hpB, hcB, hCB, hb⟩ := hdecay l hlB' δ hδ₀ hδ₁
  let p := max pA pB
  let c := min cQ cB
  let C := 1 + CQ + CB + (4 + 1 / l)
  have hcyclepos : 0 < 4 + 1 / l := by positivity
  have hC : 0 < C := by dsimp only [C]; positivity
  have hQC : CQ ≤ C := by dsimp only [C]; linarith only [hCB, hcyclepos]
  have hBC : CB ≤ C := by dsimp only [C]; linarith only [hCQ, hcyclepos]
  have hcycleC : 4 + 1 / l ≤ C := by dsimp only [C]; linarith only [hCQ, hCB]
  have hp : 2 ≤ p := hpA.trans (le_max_left _ _)
  refine ⟨p, c, C, hp, lt_min hcQ hcB, hC, ?_⟩
  intro β hβ
  dsimp only [SmoothPositiveKmBound]
  intro Q hQ lam h₀ h₁ _hlam P K hK hD A hA F G hF hG hFp hGp hzero
  let := reducedLaw_probability Q
  let k : ℕ := max 1 ⌈(A / l + 4) / 10⌉₊
  let m : ℕ := max 1 ⌈(A / l - 1) / 10⌉₊
  let Nf := (eLpNorm F (ENNReal.ofReal p) (reducedLaw Q)).toReal
  let Ng := (eLpNorm G (ENNReal.ofReal p) (reducedLaw Q)).toReal
  have hpA' : ENNReal.ofReal pA ≤ ENNReal.ofReal p :=
    ENNReal.ofReal_le_ofReal (le_max_left _ _)
  have hpB' : ENNReal.ofReal pB ≤ ENNReal.ofReal p :=
    ENNReal.ofReal_le_ofReal (le_max_right _ _)
  have hNf : (eLpNorm F (ENNReal.ofReal pB) (reducedLaw Q)).toReal ≤ Nf :=
    ENNReal.toReal_mono hFp.eLpNorm_ne_top (eLpNorm_le_eLpNorm_of_exponent_le hpB')
  have hNg : (eLpNorm G (ENNReal.ofReal pB) (reducedLaw Q)).toReal ≤ Ng :=
    ENNReal.toReal_mono hGp.eLpNorm_ne_top (eLpNorm_le_eLpNorm_of_exponent_le hpB')
  have ha := halgebra l δ hlA' hδ₀ hδ₁ β hβ Q hQ lam h₀ h₁ P K hK hD A hA F G hF hG
    (hFp.mono_exponent hpA') (hGp.mono_exponent hpA') hzero
  have hdcy := hb β hβ Q hQ lam h₀ h₁ P K hK hD A hA F G hF hG
    (hFp.mono_exponent hpB') (hGp.mono_exponent hpB') hzero
  refine ⟨?_, ha.1, ha.2.1, ?_, ?_, ha.2.2.2⟩
  · apply (sbxS2_prescribed_cycles_le l A hlpos hA).trans
    exact mul_le_mul_of_nonneg_right hcycleC (by linarith only [hlpos, hA])
  · intro n
    have hs := hq β hβ Q hQ lam h₀ h₁ P K hK hD p hp F
      (hF.mono (Probability.localSigma_le_borel _) le_rfl) hFp k
      (le_max_left _ _) n
    apply hs.trans
    have he : CQ * (k : ℝ) - cQ * n ≤ C * (k : ℝ) - c * n :=
      sub_le_sub (mul_le_mul_of_nonneg_right hQC (Nat.cast_nonneg _))
        (mul_le_mul_of_nonneg_right (min_le_left _ _) (Nat.cast_nonneg _))
    apply mul_le_mul_of_nonneg_right _ ENNReal.toReal_nonneg
    exact mul_le_mul hQC (Real.exp_le_exp.mpr he) (Real.exp_pos _).le hC.le
  · intro t
    refine ⟨(ha.2.2.1 t).1, (ha.2.2.1 t).2, ?_, ?_⟩
    · apply (hdcy t).1.trans
      calc
        _ ≤ CB * Real.exp (C * (k + m) - c * lam ^ 2 * (t : ℝ)) * Nf * Ng := by
          simpa only [mul_assoc] using sbxS2_exp_decay_product_mono CB C cB c
            ((k : ℝ) + m) (lam ^ 2 * (t : ℝ)) _ _ Nf Ng hCB.le hBC
            (min_le_right _ _) (by positivity) (by positivity)
            ENNReal.toReal_nonneg ENNReal.toReal_nonneg hNf hNg
        _ ≤ C * Real.exp (C * (k + m) - c * lam ^ 2 * (t : ℝ)) * Nf * Ng := by
          gcongr
    · apply (hdcy t).2.trans
      calc
        _ ≤ CB * Real.exp (C * (k + m) - c * lam ^ 2 * (t : ℝ)) * Nf * Ng := by
          simpa only [mul_assoc] using sbxS2_exp_decay_product_mono CB C cB c
            ((k : ℝ) + m) (lam ^ 2 * (t : ℝ)) _ _ Nf Ng hCB.le hBC
            (min_le_right _ _) (by positivity) (by positivity)
            ENNReal.toReal_nonneg ENNReal.toReal_nonneg hNf hNg
        _ ≤ C * Real.exp (C * (k + m) - c * lam ^ 2 * (t : ℝ)) * Nf * Ng := by
          gcongr



theorem uniform_positiveKm_clause_of_inputs
    (hfactor : kmKFactorUniformSmoothStmt)
    (htails : node_app_u3A_regen_u2D_tailsStmt)
    (hmany : SbxCManyCycleUniformR06.manyCycleSmoothStmt)
    (hphase : SbxCPhaseUniformR07.phaseUniformStmt) :
  ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ) (hΛ : 1 ≤ Λ₀) (hr : 1 ≤ r₀),
    ∃ l₀ : ℝ, 0 < l₀ ∧ r₀ < 2 * l₀ ∧
    ∀ l : ℝ, l₀ ≤ l → ∀ δ : ℝ, 0 < δ → δ < 1 →
    ∃ p c C : ℝ, 2 ≤ p ∧ 0 < c ∧ 0 < C ∧
    ∀ (β : ℕ → ℝ) (hβ : ∀ k, 1 ≤ k → 0 < β k),
    let D : StructuralData d := ⟨Λ₀, r₀, β, hΛ, hr, hβ⟩
    ∀ Q : EnvironmentLaw d D.ellipticity D.dependenceRange, HasSmoothBounds D Q →
    ∀ (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1),
      ∀ (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
        (hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K)
        (hD : Regeneration.annealedCoupledLaw Q.measure K
          (regenerationNoReturn hd (l / lam)) ≠ 0),
      ∀ A : ℝ, l ≤ A → ∀ F G : FieldPair d → ℝ,
      Measurable[localSigma {x : Vec d | euclideanNorm x < A / lam}] F →
      Measurable[localSigma {x : Vec d | euclideanNorm x < A / lam}] G →
      MemLp F (ENNReal.ofReal p) (reducedLaw Q) →
      MemLp G (ENNReal.ofReal p) (reducedLaw Q) →
      (∫ ω, F ω ∂reducedLaw Q) = 0 →
      let k : ℕ := max 1 ⌈(A / l + 4) / 10⌉₊
      let m : ℕ := max 1 ⌈(A / l - 1) / 10⌉₊
      let μ := Regeneration.annealedCoupledLaw Q.measure K
      let ν := regenerationConditionedLaw hd Q lam l K hK.1 hD
      let Δ := Regeneration.Renewal.regenDelta lam
      let pn := regenerationLatticeMass hd Q lam l K hK.1 hD
      let mean := ∑' n : ℕ, (n : ℝ) * pn n
      let q := fun n : ℕ => ∫ ωz in {ωz | regenerationTime hd lam l k ωz.2 =
        (((n : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞)}, F (reduce ωz.1) ∂μ
      let hm := fun t : ℝ≥0 => ∫ ωz in {ωz |
        regenerationTime hd lam l m ωz.2 ≤ (t : ℝ≥0∞)},
        G (translate (ωz.2.1 t) (reduce ωz.1)) ∂ν
      let rm := fun t : ℝ≥0 => ∫ ωz in {ωz |
        regenerationTime hd lam l m ωz.2 ≤ (t : ℝ≥0∞) ∧
        (t : ℝ≥0∞) < regenerationTime hd lam l (m + 1) ωz.2},
        G (translate (ωz.2.1 t) (reduce ωz.1)) ∂ν
      let Hm := fun s : ℝ≥0 => mean⁻¹ * ∑' j : ℕ, rm (s + j * Δ)
      let cov := fun t : ℝ≥0 => ∫ ωz, F (reduce ωz.1) *
        G (translate (ωz.2.1 t) (reduce ωz.1)) ∂μ
      let rem := fun t : ℝ≥0 => ∫ ωz in {ωz | (t : ℝ≥0∞) <
        regenerationTime hd lam l (k + m) ωz.2}, F (reduce ωz.1) *
          G (translate (ωz.2.1 t) (reduce ωz.1)) ∂μ
      let Nf := (eLpNorm F (ENNReal.ofReal p) (reducedLaw Q)).toReal
      let Ng := (eLpNorm G (ENNReal.ofReal p) (reducedLaw Q)).toReal
      (k + m : ℝ) ≤ C * (1 + A) ∧
      Summable q ∧ (∑' n, q n) = 0 ∧
      (∀ n : ℕ, |q n| ≤ C * Real.exp (C * k - c * n) * Nf) ∧
      (∀ t : ℝ≥0,
        Integrable (fun ωz => F (reduce ωz.1) *
          G (translate (ωz.2.1 t) (reduce ωz.1))) μ ∧
        cov t = rem t + ∑ n ∈ Finset.range (⌊(t : ℝ) / (Δ : ℝ)⌋₊ + 1),
          q n * hm (t - n * Δ) ∧
        |rem t| ≤ C * Real.exp (C * (k + m) - c * lam ^ 2 * (t : ℝ)) * Nf * Ng ∧
        |cov t| ≤ C * Real.exp (C * (k + m) - c * lam ^ 2 * (t : ℝ)) * Nf * Ng) ∧
      ∀ s : ℝ≥0, s < Δ → ∀ j : ℕ,
        cov (s + j * Δ) = rem (s + j * Δ) +
          (∑ n ∈ Finset.range (j + 1), q n * (hm (s + (j - n) * Δ) - Hm s)) -
          Hm s * ∑' n : ℕ, q (j + 1 + n) := by
  intro d hd Λ₀ r₀ hΛ hr
  obtain ⟨l₀, hl₀, hsep, hbound⟩ :=
    uniform_positiveKmFullRange_of_inputs hfactor htails hmany hphase d hd Λ₀ r₀ hΛ hr
  refine ⟨l₀, hl₀, hsep, ?_⟩
  intro l hl δ hδ₀ hδ₁
  obtain ⟨p, c, C, hp, hc, hC, hpositive⟩ := hbound l hl δ hδ₀ hδ₁
  refine ⟨p, c, C, hp, hc, hC, ?_⟩
  intro β hβ
  dsimp only
  intro Q hQ lam h₀ h₁
  exact hpositive β hβ Q hQ lam h₀ h₁ h₁



theorem uniform_covariance_radius_decay_of_inputs
    (hfactor : kmKFactorUniformSmoothStmt)
    (htails : node_app_u3A_regen_u2D_tailsStmt)
    (hmany : SbxCManyCycleUniformR06.manyCycleSmoothStmt)
    (hphase : SbxCPhaseUniformR07.phaseUniformStmt) :
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
    uniform_covariance_and_remainder_decay_of_inputs hfactor htails hmany hphase d hd Λ₀ r₀ hΛ hr
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
  intro Q hQ lam h₀ h₁ P K hK hD' A hA F G hF hG hFp hGp hzero
  intro t
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



theorem uniform_positive_complex_path_covariance_of_inputs
    (hfactor : kmKFactorUniformSmoothStmt)
    (htails : node_app_u3A_regen_u2D_tailsStmt)
    (hmany : SbxCManyCycleUniformR06.manyCycleSmoothStmt)
    (hphase : SbxCPhaseUniformR07.phaseUniformStmt) :
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
    uniform_covariance_radius_decay_of_inputs hfactor htails hmany hphase d hd Λ₀ r₀ hΛ hr
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



theorem uniform_complex_path_product_growth_of_tails
    (htails : node_app_u3A_regen_u2D_tailsStmt) :
    ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ) (hΛ : 1 ≤ Λ₀) (hr : 1 ≤ r₀),
    ∃ l₀ p C : ℝ, 0 < l₀ ∧ r₀ < 2 * l₀ ∧ 2 ≤ p ∧ 0 < C ∧
    ∀ (β : ℕ → ℝ) (hβ : ∀ k, 1 ≤ k → 0 < β k),
    let D : StructuralData d := ⟨Λ₀, r₀, β, hΛ, hr, hβ⟩
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange), HasSmoothBounds D Q →
    ∀ (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
      (l δ : ℝ), l₀ ≤ l → 0 < δ → δ < 1 →
    ∀ (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
      (_hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K)
      (_hD : Regeneration.annealedCoupledLaw Q.measure K
        (regenerationNoReturn hd (l / lam)) ≠ 0)
      (F G : FieldPair d → ℂ),
    Measurable F → Measurable G →
    MemLp F (ENNReal.ofReal p) (reducedLaw Q) →
    MemLp G (ENNReal.ofReal p) (reducedLaw Q) → ∀ t : ℝ≥0,
    Integrable (fun w => F (reduce w.1) * G (sbxS4CoupledEndpoint t w))
      (Regeneration.annealedCoupledLaw Q.measure K) ∧
    (∫ w, F (reduce w.1) * G (sbxS4CoupledEndpoint t w)
      ∂Regeneration.annealedCoupledLaw Q.measure K) =
      (∫ ω, F (reduce ω) *
        (∫ γ : Path d, G (translate (γ t) (reduce ω)) ∂P (0, ω)) ∂Q.measure) ∧
    (∫ w, ‖F (reduce w.1) * G (sbxS4CoupledEndpoint t w)‖
      ∂Regeneration.annealedCoupledLaw Q.measure K) ≤
      C * Real.exp (C * lam ^ 2 * (t : ℝ)) *
        (eLpNorm F (ENNReal.ofReal p) (reducedLaw Q)).toReal *
        (eLpNorm G (ENNReal.ofReal p) (reducedLaw Q)).toReal := by
  intro d hd Λ₀ r₀ hΛ hr
  obtain ⟨l₀, p, c, C, hl₀, hsep, hp, hc, hC, hrem⟩ :=
    uniform_remainder_of_regeneration_tails htails d hd Λ₀ r₀ hΛ hr 1 1 zero_lt_one zero_lt_one
  refine ⟨l₀, p, C, hl₀, hsep, hp, hC, ?_⟩
  intro β hβ
  dsimp only
  intro Q hQ lam h₀ h₁ l δ hl hδ₀ hδ₁ P K hK hD F G hF hG hFp hGp t
  have := Regeneration.annealedCoupledLaw_isProbabilityMeasure Q.measure K hK.1
  have hwhole : Regeneration.annealedCoupledLaw Q.measure K Set.univ ≤
      ENNReal.ofReal (1 * Real.exp (1 * (lam ^ 2 * (t : ℝ)) -
        1 * lam ^ 2 * (t : ℝ))) := by
    simp only [one_mul, sub_self, Real.exp_zero, ENNReal.ofReal_one, measure_univ, le_rfl]
  obtain ⟨hprod, hbound⟩ := hrem β hβ Q hQ lam h₀ h₁ l δ hl hδ₀ hδ₁ P K hK hD
    (fun ω => ‖F ω‖) (fun ω => ‖G ω‖) hF.norm hG.norm hFp.norm hGp.norm
    (lam ^ 2 * (t : ℝ)) t Set.univ (by positivity) MeasurableSet.univ hwhole
    (Regeneration.annealedCoupledLaw Q.measure K) (Set.mem_insert _ _)
  have hnorm : Integrable (fun w => ‖F (reduce w.1) * G (sbxS4CoupledEndpoint t w)‖)
      (Regeneration.annealedCoupledLaw Q.measure K) := by
    simpa only [IntegrableOn, Measure.restrict_univ, norm_mul, sbxS4CoupledEndpoint] using hprod
  have hcomplex := (integrable_norm_iff
    (((hF.comp (Probability.measurable_reduce.comp measurable_fst)).mul
      (hG.comp (sbxS4_measurable_coupledEndpoint t))).aestronglyMeasurable)).mp hnorm
  refine ⟨hcomplex, sbxS4_coupled_product_integral_eq_supplied hd Q lam l δ h₀.le h₁
    P K hK t hG hcomplex, ?_⟩
  have hb : |∫ w, ‖F (reduce w.1) * G (sbxS4CoupledEndpoint t w)‖
      ∂Regeneration.annealedCoupledLaw Q.measure K| ≤
      C * Real.exp (C * lam ^ 2 * (t : ℝ) - c * lam ^ 2 * (t : ℝ)) *
        (eLpNorm F (ENNReal.ofReal p) (reducedLaw Q)).toReal *
        (eLpNorm G (ENNReal.ofReal p) (reducedLaw Q)).toReal := by
    simpa only [Measure.restrict_univ, norm_mul, sbxS4CoupledEndpoint,
      eLpNorm_norm F hFp.aestronglyMeasurable, eLpNorm_norm G hGp.aestronglyMeasurable,
      mul_assoc] using hbound
  refine (le_abs_self _).trans (hb.trans ?_)
  apply mul_le_mul_of_nonneg_right _ ENNReal.toReal_nonneg
  apply mul_le_mul_of_nonneg_right _ ENNReal.toReal_nonneg
  apply mul_le_mul_of_nonneg_left _ hC.le
  exact Real.exp_le_exp.mpr (sub_le_self _ (by positivity))


theorem uniform_coupled_endpoint_memLp_two_of_tails
    (htails : node_app_u3A_regen_u2D_tailsStmt) :
    ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ) (hΛ : 1 ≤ Λ₀) (hr : 1 ≤ r₀),
    ∃ l₀ p C : ℝ, 0 < l₀ ∧ r₀ < 2 * l₀ ∧ 2 ≤ p ∧ 0 < C ∧
    ∀ (β : ℕ → ℝ) (hβ : ∀ k, 1 ≤ k → 0 < β k),
    let D : StructuralData d := ⟨Λ₀, r₀, β, hΛ, hr, hβ⟩
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange), HasSmoothBounds D Q →
    ∀ (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
      (l δ : ℝ), l₀ ≤ l → 0 < δ → δ < 1 →
    ∀ (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
      (_hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K)
      (_hD : Regeneration.annealedCoupledLaw Q.measure K
        (regenerationNoReturn hd (l / lam)) ≠ 0)
      (F : FieldPair d → ℂ),
    Measurable F → MemLp F (2 * ENNReal.ofReal p) (reducedLaw Q) → ∀ t : ℝ≥0,
    MemLp (fun w => F (sbxS4CoupledEndpoint t w)) 2
      (Regeneration.annealedCoupledLaw Q.measure K) ∧
    (∀ᵐ ω ∂Q.measure,
      MemLp (fun γ : Path d => F (translate (γ t) (reduce ω))) 2 (P (0, ω))) ∧
    (∫ w, ‖F (sbxS4CoupledEndpoint t w)‖ ^ 2
      ∂Regeneration.annealedCoupledLaw Q.measure K) ≤
      C * Real.exp (C * lam ^ 2 * (t : ℝ)) *
        (eLpNorm F (2 * ENNReal.ofReal p) (reducedLaw Q)).toReal ^ 2 := by
  intro d hd Λ₀ r₀ hΛ hr
  obtain ⟨l₀, p, C, hl₀, hsep, hp, hC, hgrowth⟩ :=
    uniform_complex_path_product_growth_of_tails htails d hd Λ₀ r₀ hΛ hr
  refine ⟨l₀, p, C, hl₀, hsep, hp, hC, ?_⟩
  intro β hβ
  dsimp only
  intro Q hQ lam h₀ h₁ l δ hl hδ₀ hδ₁ P K hK hD F hF hFp t
  have := reducedLaw_probability Q
  have hp0 : 0 < p := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) hp
  have hsquare : MemLp (fun ω => ‖F ω‖ ^ 2) (ENNReal.ofReal p) (reducedLaw Q) := by
    convert hFp.norm_rpow_div (2 : ℝ≥0∞) using 1
    · ext ω
      simp only [ENNReal.toReal_ofNat, Real.rpow_two]
    · rw [div_eq_mul_inv, mul_comm (2 : ℝ≥0∞), mul_assoc,
        ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, mul_one]
  have hcast : AEStronglyMeasurable
      (fun ω => ((‖F ω‖ ^ 2 : ℝ) : ℂ)) (reducedLaw Q) :=
    Complex.continuous_ofReal.comp_aestronglyMeasurable hsquare.aestronglyMeasurable
  have hcastnorm : ∀ᵐ ω ∂reducedLaw Q, ‖((‖F ω‖ ^ 2 : ℝ) : ℂ)‖ = ‖‖F ω‖ ^ 2‖ :=
    Filter.Eventually.of_forall fun ω => Complex.norm_real _
  have hcastLp : MemLp (fun ω => ((‖F ω‖ ^ 2 : ℝ) : ℂ))
      (ENNReal.ofReal p) (reducedLaw Q) :=
    (memLp_congr_norm hcast hsquare.aestronglyMeasurable hcastnorm).mpr hsquare
  have hnorm : eLpNorm (fun ω => ((‖F ω‖ ^ 2 : ℝ) : ℂ))
      (ENNReal.ofReal p) (reducedLaw Q) =
      eLpNorm F (2 * ENNReal.ofReal p) (reducedLaw Q) ^ 2 := by
    rw [eLpNorm_congr_norm_ae hcast hsquare.aestronglyMeasurable hcastnorm]
    simpa only [Real.rpow_two, ENNReal.ofReal_ofNat, ENNReal.rpow_two,
      mul_comm] using (eLpNorm_norm_rpow F hFp.aestronglyMeasurable (by norm_num : (0 : ℝ) < 2)
        (p := ENNReal.ofReal p))
  obtain ⟨hprod, _hpair, hb⟩ := hgrowth β hβ Q hQ lam h₀ h₁ l δ hl hδ₀ hδ₁ P K hK hD
    (fun _ => 1) (fun ω => ((‖F ω‖ ^ 2 : ℝ) : ℂ)) measurable_const
    (Complex.continuous_ofReal.measurable.comp (hF.norm.pow_const 2))
    (memLp_const 1) hcastLp t
  have hsquareEnd : Integrable (fun w => ‖F (sbxS4CoupledEndpoint t w)‖ ^ 2)
      (Regeneration.annealedCoupledLaw Q.measure K) := by
    simpa only [one_mul, Complex.norm_real, Real.norm_eq_abs, abs_sq] using hprod.norm
  have hFend := (memLp_two_iff_integrable_sq_norm
    (hF.comp (sbxS4_measurable_coupledEndpoint t)).aestronglyMeasurable).mpr hsquareEnd
  refine ⟨hFend, sbxS4_supplied_endpoint_memLp_two_of_coupled hd Q lam l δ h₀.le h₁
    P K hK t hF hFend, ?_⟩
  have hone : eLpNorm (fun _ : FieldPair d => (1 : ℂ)) (ENNReal.ofReal p)
      (reducedLaw Q) = 1 := by
    rw [eLpNorm_const _ (ENNReal.ofReal_pos.mpr hp0).ne' (NeZero.ne _), measure_univ,
      ENNReal.one_rpow, mul_one]
    norm_num
  simpa only [one_mul, Complex.norm_real, Real.norm_eq_abs, abs_sq, hone,
    ENNReal.toReal_one, mul_one, hnorm, ENNReal.toReal_pow] using hb




/-- The actual GMP action identifies the semigroup covariance with the supplied
coupled covariance whenever the endpoint is square integrable. -/
theorem supplied_covariance_eq_forced_of_endpoint_memLp
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam l δ : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h0 h1 P K)
    (t : ℝ≥0) (F G : Lp ℂ 2 (reducedLaw Q))
    (hend : MemLp (fun w => G (sbxS4CoupledEndpoint t w)) 2
      (Regeneration.annealedCoupledLaw Q.measure K)) :
    (∫ ω, F ω * forcedComplexEvolution Q (Regeneration.Renewal.forceCoord hd)
      (lam : ℂ) t G ω ∂reducedLaw Q) =
      ∫ w, F (reduce w.1) * G (sbxS4CoupledEndpoint t w)
        ∂Regeneration.annealedCoupledLaw Q.measure K := by
  have hpair := (sbxS4_L2_pairing_eq_supplied hd Q lam l δ h0 h1 P K hK t
    (Lp.memLp F) (Lp.stronglyMeasurable G).measurable hend).2
  have ha := EinsteinFull.s8_gmp_reduced_kernel_action_at hd Q lam h0 h1 P hK.2.2.1 t G
  have hi : EinsteinRelation.External.GantertSection7Support.firstCoordinateIndex hd =
      Regeneration.Renewal.forceCoord hd := by
    apply Fin.ext
    rfl
  rw [hi] at ha
  calc
    _ = ∫ ω, F (reduce ω) * forcedComplexEvolution Q
        (Regeneration.Renewal.forceCoord hd) (lam : ℂ) t G (reduce ω) ∂Q.measure := by
      exact integral_map Probability.measurable_reduce.aemeasurable
        ((Lp.stronglyMeasurable F).aestronglyMeasurable.mul
          (Lp.stronglyMeasurable _).aestronglyMeasurable)
    _ = ∫ ω, F (reduce ω) *
        (∫ γ : Path d, G (translate (γ t) (reduce ω)) ∂P (0, ω)) ∂Q.measure := by
      apply integral_congr_ae
      filter_upwards [ha] with ω hω
      rw [hω.2]
    _ = _ := hpair.symm


/-- Uniform positive-force semigroup covariance, for a supplied coupling. -/
theorem uniform_positive_semigroup_covariance_of_inputs
    (hfactor : kmKFactorUniformSmoothStmt)
    (htails : node_app_u3A_regen_u2D_tailsStmt)
    (hmany : SbxCManyCycleUniformR06.manyCycleSmoothStmt)
    (hphase : SbxCPhaseUniformR07.phaseUniformStmt) :
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
    uniform_positive_complex_path_covariance_of_inputs hfactor htails hmany hphase d hd Λ₀ r₀ hΛ hr
  obtain ⟨lR, pR, CR, hlR, hsR, hpR, hCR, hgrowth⟩ :=
    uniform_coupled_endpoint_memLp_two_of_tails htails d hd Λ₀ r₀ hΛ hr
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
  have hpR' : 2 * ENNReal.ofReal pR ≤ ENNReal.ofReal (max pD (2 * pR)) := by
    rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    exact ENNReal.ofReal_le_ofReal (le_max_right _ _)
  have hend := (hgrowth β hβ Q hQ lam h0 h1 l δ hlR' hδ0 hδ1 P K hK hD G
    (Lp.stronglyMeasurable G).measurable (hGp.mono_exponent hpR') t).1
  have heq := supplied_covariance_eq_forced_of_endpoint_memLp hd Q lam l δ h0.le h1 P K hK t F G hend
  have hb := hbound β hβ Q hQ lam h0 h1 P K hK hD A hA F G hFl hGl
    (hFp.mono_exponent hpD') (hGp.mono_exponent hpD') hmean t
  have hFnorm := ENNReal.toReal_mono hFp.eLpNorm_ne_top
    (eLpNorm_le_eLpNorm_of_exponent_le (f := (F : FieldPair d → ℂ)) hpD')
  have hGnorm := ENNReal.toReal_mono hGp.eLpNorm_ne_top
    (eLpNorm_le_eLpNorm_of_exponent_le (f := (G : FieldPair d → ℂ)) hpD')
  rw [hS.eq_forcedComplexEvolution, heq]
  exact hb.trans (mul_le_mul
    (mul_le_mul_of_nonneg_left hFnorm (mul_nonneg hC.le (Real.exp_pos _).le))
    hGnorm ENNReal.toReal_nonneg (by positivity))


open EinsteinRelation.Regeneration
open EinsteinRelation.External.GantertSection7Support
open EinsteinFull.External.Source.GMP

/-- Conditional uniform k/m assembly, with the literal full-duration setwise
lower bound as its remaining coupling hypothesis. -/
theorem uniform_kmDecomp_of_inputs_and_setwise
    (hfactor : kmKFactorUniformSmoothStmt)
    (htails : node_app_u3A_regen_u2D_tailsStmt)
    (hmany : SbxCManyCycleUniformR06.manyCycleSmoothStmt)
    (hphase : SbxCPhaseUniformR07.phaseUniformStmt)
    (hsetwise : ∀ (d : ℕ) (hd : 2 ≤ d) (Λ r : ℝ),
      ∀ l : ℝ, 1 ≤ l → ∃ c : ℝ, 0 < c ∧
      ∀ (D : StructuralData d), D.ellipticity = Λ → D.dependenceRange = r →
      ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange), HasSmoothBounds D Q →
      ∀ (μ : ℝ) (h0 : 0 < μ) (h1 : μ ≤ 1),
        ∃ P : QuenchedPathLaws d,
          IsGMPReducedKernel hd Q.ellipticity_parameter Q μ h0.le h1 P ∧
          ∀ᵐ ω ∂Q.measure, ∀ x : Vec d,
            ENNReal.ofReal (c * μ ^ d) •
              (volume : Measure (Vec d)).restrict
                (endpointBall (Renewal.forceCoord hd) (l / μ) x) ≤
            ((P (x, ω)).restrict {γ | ∀ t : ℝ≥0, t ≤ Renewal.regenDelta μ →
              γ t ∈ couplingRegion (Renewal.forceCoord hd) (l / μ) x}).map
                (fun γ => γ (Renewal.regenDelta μ))) :
    SbxCLocalMixingUniformR06.kmDecompUniformFullRangeSmoothStmt := by
  intro d hd Λ₀ r₀ hΛ hr
  obtain ⟨L, hL, hsepL, hcoupling⟩ :=
    SbxAUniformCouplingR07.uniform_coupling_half_mass_of_setwise_lower htails hsetwise d hd Λ₀ r₀
  obtain ⟨lD, hlD, hsepD, hdecay⟩ :=
    uniform_positive_semigroup_covariance_of_inputs hfactor htails hmany hphase d hd Λ₀ r₀ hΛ hr
  obtain ⟨lK, hlK, hsepK, hkm⟩ :=
    uniform_positiveKmFullRange_of_inputs hfactor htails hmany hphase d hd Λ₀ r₀ hΛ hr
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

end EinsteinFull.Blueprint.SbxAUniformKMAssemblerR07
