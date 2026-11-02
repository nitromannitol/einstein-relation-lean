import EinsteinFull.Blueprint.G1.Draft.S3SmoothScope
import EinsteinFull.Calculus.CLForcedLLNV2

/-! Draft smooth-scope Section 3 interfaces. These conditional statements have not
been reviewed or adopted as graph reductions. -/

open MeasureTheory
open scoped NNReal ENNReal Topology

namespace EinsteinFull.Blueprint.SbxS5Section3R01
open EinsteinRelation
open EinsteinFull.Work.W5

/-- Literal k/m decomposition restricted to laws satisfying the smooth bounds. -/
def kmDecompSmoothStmt : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d),
    ∃ l₀ : ℝ, 0 < l₀ ∧ D.dependenceRange < 2 * l₀ ∧
    ∀ l : ℝ, l₀ ≤ l → ∀ δ : ℝ, 0 < δ → δ < 1 →
    ∃ p c C lam₀ : ℝ, 2 ≤ p ∧ 0 < c ∧ 0 < C ∧ 0 < lam₀ ∧ lam₀ ≤ 1 ∧
    ∀ Q : EnvironmentLaw d D.ellipticity D.dependenceRange, HasSmoothBounds D Q →
    (∀ (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1), lam ≤ lam₀ →
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
          Hm s * ∑' n : ℕ, q (j + 1 + n)) ∧
    (∀ lam : ℝ, 0 < |lam| → |lam| ≤ lam₀ →
      ∀ S : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      IsComplexEnvironmentSemigroup Q (Regeneration.Renewal.forceCoord hd) (lam : ℂ) S →
      ∀ A : ℝ, l ≤ A → ∀ F G : Lp ℂ 2 (reducedLaw Q),
      IsRealLocalObservation Q (A / |lam|) F →
      IsRealLocalObservation Q (A / |lam|) G →
      MemLp (F : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q) →
      MemLp (G : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q) →
      (∫ ω, F ω ∂reducedLaw Q) = 0 → ∀ t : ℝ≥0,
      ‖∫ ω, F ω * S t G ω ∂reducedLaw Q‖ ≤
        C * Real.exp (C * A - c * lam ^ 2 * (t : ℝ)) *
          (eLpNorm (F : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q)).toReal *
          (eLpNorm (G : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q)).toReal)


/-- Literal phase-error statement restricted to smooth laws. -/
def phaseErrorSmoothStmt : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d),
    ∃ l₀ : ℝ, 0 < l₀ ∧ D.dependenceRange < 2 * l₀ ∧
    ∀ l : ℝ, l₀ ≤ l → ∀ δ : ℝ, 0 < δ → δ < 1 →
    ∃ p c C : ℝ, 2 ≤ p ∧ 0 < c ∧ 0 < C ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange), HasSmoothBounds D Q →
    ∀ (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
      (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
      (hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K)
      (hD : Regeneration.annealedCoupledLaw Q.measure K
        (regenerationNoReturn hd (l / lam)) ≠ 0),
    ∀ (A : ℝ) (m : ℕ), l ≤ A → 1 ≤ m → 10 * (m : ℝ) * l - l - A ≥ -2 * l →
    ∀ G : FieldPair d → ℝ,
    Measurable[localSigma {x : Vec d | euclideanNorm x < A / lam}] G →
    MemLp G (ENNReal.ofReal p) (reducedLaw Q) →
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
    let Ng := (eLpNorm G (ENNReal.ofReal p) (reducedLaw Q)).toReal
    let Hm := fun s : ℝ≥0 => mean⁻¹ * ∑' j : ℕ, rm (s + j * Δ)
    (∀ t : ℝ≥0, |rm t| ≤ C * Real.exp (C * m - c * lam ^ 2 * (t : ℝ)) * Ng) ∧
    ∀ s : ℝ≥0, s < Δ →
      Summable (fun j : ℕ => rm (s + j * Δ)) ∧
      |Hm s| ≤ C * Real.exp (C * m) * Ng ∧
      ∀ j : ℕ,
        hm (s + j * Δ) = rm (s + j * Δ) +
          ∑ n ∈ Finset.range (j + 1), pn n * hm (s + (j - n) * Δ) ∧
        hm (s + j * Δ) - Hm s =
          (∑ n ∈ Finset.range (j + 1),
            ((∑' a : ℕ, EinsteinFull.latticeConvolutionPower pn a (j - n)) - mean⁻¹) *
              rm (s + n * Δ)) - mean⁻¹ * ∑' n : ℕ, rm (s + (j + 1 + n) * Δ) ∧
        |hm (s + j * Δ) - Hm s| ≤ C * Real.exp (C * m - c * j) * Ng


/-- Coupling existence and nonreturn uniformly over smooth laws. -/
def couplingNonreturnSmoothStmt : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d),
  ∃ L : ℝ, 0 < L ∧ D.dependenceRange < 2 * L ∧
  ∀ l : ℝ, L ≤ l →
  ∃ δa lamc : ℝ, 0 < δa ∧ δa < 1 ∧ 0 < lamc ∧ lamc ≤ 1 ∧
  ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange), HasSmoothBounds D Q →
  ∀ (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1),
    lam ≤ lamc → ∃ (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d),
    ∃ _hK : IsRegenerationCoupling hd Q lam l δa h0.le h1 P K,
      Regeneration.annealedCoupledLaw Q.measure K
        (regenerationNoReturn hd (l / lam)) ≠ 0


/-- The all-law k/m statement implies its smooth restriction. -/
theorem kmDecompSmooth_of_all (h : node_rt_u3A_km_u2D_decompStmt) :
    kmDecompSmoothStmt := by
  intro d hd D
  obtain ⟨l₀, hl₀, hsep, h⟩ := h d hd D.ellipticity D.dependenceRange
  refine ⟨l₀, hl₀, hsep, ?_⟩
  intro l hl δ hδ0 hδ1
  obtain ⟨p, c, C, lam₀, hp, hc, hC, hla, hla1, hQ⟩ := h l hl δ hδ0 hδ1
  exact ⟨p, c, C, lam₀, hp, hc, hC, hla, hla1, fun Q _ => hQ Q⟩

/-- The all-law phase statement implies its smooth restriction. -/
theorem phaseErrorSmooth_of_all (h : node_rt_u3A_local_u2D_mixing_u23_phase_u2D_errorStmt) :
    phaseErrorSmoothStmt := by
  intro d hd D
  obtain ⟨l₀, hl₀, hsep, h⟩ := h d hd D.ellipticity D.dependenceRange
  refine ⟨l₀, hl₀, hsep, ?_⟩
  intro l hl δ hδ0 hδ1
  obtain ⟨p, c, C, hp, hc, hC, hQ⟩ := h l hl δ hδ0 hδ1
  exact ⟨p, c, C, hp, hc, hC, fun Q _ => hQ Q⟩

/-- The all-law coupling statement implies its smooth restriction. -/
theorem couplingNonreturnSmooth_of_all (h : S3KMAdmissibleCouplingNonreturn) :
    couplingNonreturnSmoothStmt := by
  intro d hd D
  obtain ⟨L, hL, hsep, h⟩ := h d hd D.ellipticity D.dependenceRange
  refine ⟨L, hL, hsep, ?_⟩
  intro l hl
  obtain ⟨δ, lam, hδ0, hδ1, hlam, hlam1, hQ⟩ := h l hl
  exact ⟨δ, lam, hδ0, hδ1, hlam, hlam1, fun Q _ => hQ Q⟩

open EinsteinFull.SbxS10KmReflection

/-- Reflection transfers the positive-force estimate within the smooth class. -/
theorem smooth_positive_covariance_bound_iff_signed {d : ℕ} (D : StructuralData d)
    (i : Fin d) (l p c C lam₀ : ℝ) :
    (∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange), HasSmoothBounds D Q →
      ∀ (lam : ℝ), 0 < lam → lam ≤ lam₀ →
      ∀ S : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      IsComplexEnvironmentSemigroup Q i (lam : ℂ) S →
      ∀ A : ℝ, l ≤ A → ∀ F G : Lp ℂ 2 (reducedLaw Q),
      IsRealLocalObservation Q (A / lam) F →
      IsRealLocalObservation Q (A / lam) G →
      MemLp (F : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q) →
      MemLp (G : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q) →
      (∫ ω, F ω ∂reducedLaw Q) = 0 → ∀ t : ℝ≥0,
      ‖∫ ω, F ω * S t G ω ∂reducedLaw Q‖ ≤
        C * Real.exp (C * A - c * lam ^ 2 * (t : ℝ)) *
          (eLpNorm (F : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q)).toReal *
          (eLpNorm (G : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q)).toReal) ↔
    (∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange), HasSmoothBounds D Q →
      ∀ (lam : ℝ), 0 < |lam| → |lam| ≤ lam₀ →
      ∀ S : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      IsComplexEnvironmentSemigroup Q i (lam : ℂ) S →
      ∀ A : ℝ, l ≤ A → ∀ F G : Lp ℂ 2 (reducedLaw Q),
      IsRealLocalObservation Q (A / |lam|) F →
      IsRealLocalObservation Q (A / |lam|) G →
      MemLp (F : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q) →
      MemLp (G : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q) →
      (∫ ω, F ω ∂reducedLaw Q) = 0 → ∀ t : ℝ≥0,
      ‖∫ ω, F ω * S t G ω ∂reducedLaw Q‖ ≤
        C * Real.exp (C * A - c * lam ^ 2 * (t : ℝ)) *
          (eLpNorm (F : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q)).toReal *
          (eLpNorm (G : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q)).toReal) := by
  constructor
  · intro hpositive Q hQ lam h0 h1 S hS A hA F G hF hG hFp hGp hmean t
    by_cases hpos : 0 < lam
    · simp only [abs_of_pos hpos] at h1 hF hG
      exact hpositive Q hQ lam hpos h1 S hS A hA F G hF hG hFp hGp hmean t
    · have hneg : lam < 0 := lt_of_le_of_ne (le_of_not_gt hpos) (abs_pos.mp h0)
      have hSr : IsComplexEnvironmentSemigroup (reflectedEnvironmentLaw Q) i
          ((|lam| : ℝ) : ℂ) (reflectedSemigroup Q S) := by
        simpa only [abs_of_neg hneg, Complex.ofReal_neg] using isSemigroup_reflected Q hS
      have hmeanr : (∫ ω, (pullback Q).symm F ω
          ∂reducedLaw (reflectedEnvironmentLaw Q)) = 0 :=
        (integral_pullback_symm Q F).trans hmean
      have hb := hpositive (reflectedEnvironmentLaw Q) (clr_reflected_hasSmoothBounds D Q hQ) |lam| h0 h1
        (reflectedSemigroup Q S) hSr A hA ((pullback Q).symm F) ((pullback Q).symm G)
        (realLocal_pullback_symm Q hF) (realLocal_pullback_symm Q hG)
        (memLp_pullback_symm Q hFp) (memLp_pullback_symm Q hGp) hmeanr t
      rw [← covariance_reflected Q S t F G] at hb
      simpa only [eLpNorm_pullback_symm, sq_abs] using hb
  · intro hsigned Q hQ lam h0 h1 S hS A hA F G hF hG hFp hGp hmean t
    exact hsigned Q hQ lam (by simpa only [abs_of_pos h0] using h0)
      (by simpa only [abs_of_pos h0] using h1) S hS A hA F G
      (by simpa only [abs_of_pos h0] using hF)
      (by simpa only [abs_of_pos h0] using hG) hFp hGp hmean t


/-- Moment promotion and signed-force transport within the smooth class. -/
theorem smooth_positive_covariance_bound_mono_signed
    {d : ℕ} (D : StructuralData d) (i : Fin d) {l p c C lam₀ p' c' C' lam₀' : ℝ}
    (hl : 0 < l) (hC : 0 ≤ C) (hpp : p ≤ p') (hcc : c' ≤ c)
    (hCC : C ≤ C') (hlam : lam₀' ≤ lam₀)
    (hpositive : (∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange), HasSmoothBounds D Q →
      ∀ (lam : ℝ), 0 < lam → lam ≤ lam₀ →
      ∀ S : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      IsComplexEnvironmentSemigroup Q i (lam : ℂ) S →
      ∀ A : ℝ, l ≤ A → ∀ F G : Lp ℂ 2 (reducedLaw Q),
      IsRealLocalObservation Q (A / lam) F →
      IsRealLocalObservation Q (A / lam) G →
      MemLp (F : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q) →
      MemLp (G : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q) →
      (∫ ω, F ω ∂reducedLaw Q) = 0 → ∀ t : ℝ≥0,
      ‖∫ ω, F ω * S t G ω ∂reducedLaw Q‖ ≤
        C * Real.exp (C * A - c * lam ^ 2 * (t : ℝ)) *
          (eLpNorm (F : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q)).toReal *
          (eLpNorm (G : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q)).toReal)) :
    (∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange), HasSmoothBounds D Q →
      ∀ (lam : ℝ), 0 < |lam| → |lam| ≤ lam₀' →
      ∀ S : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      IsComplexEnvironmentSemigroup Q i (lam : ℂ) S →
      ∀ A : ℝ, l ≤ A → ∀ F G : Lp ℂ 2 (reducedLaw Q),
      IsRealLocalObservation Q (A / |lam|) F →
      IsRealLocalObservation Q (A / |lam|) G →
      MemLp (F : FieldPair d → ℂ) (ENNReal.ofReal p') (reducedLaw Q) →
      MemLp (G : FieldPair d → ℂ) (ENNReal.ofReal p') (reducedLaw Q) →
      (∫ ω, F ω ∂reducedLaw Q) = 0 → ∀ t : ℝ≥0,
      ‖∫ ω, F ω * S t G ω ∂reducedLaw Q‖ ≤
        C' * Real.exp (C' * A - c' * lam ^ 2 * (t : ℝ)) *
          (eLpNorm (F : FieldPair d → ℂ) (ENNReal.ofReal p') (reducedLaw Q)).toReal *
          (eLpNorm (G : FieldPair d → ℂ) (ENNReal.ofReal p') (reducedLaw Q)).toReal) := by
  apply (smooth_positive_covariance_bound_iff_signed D
    i l p' c' C' lam₀').mp
  intro Q hQ lam h₀ hlam' S hS A hA F G hF hG hFp hGp hzero t
  let := reducedLaw_probability Q
  have hpp' := ENNReal.ofReal_le_ofReal hpp
  have hNf := ENNReal.toReal_mono hFp.eLpNorm_ne_top
    (eLpNorm_le_eLpNorm_of_exponent_le (f := (F : FieldPair d → ℂ)) hpp')
  have hNg := ENNReal.toReal_mono hGp.eLpNorm_ne_top
    (eLpNorm_le_eLpNorm_of_exponent_le (f := (G : FieldPair d → ℂ)) hpp')
  have hb := hpositive Q hQ lam h₀ (hlam'.trans hlam) S hS A hA F G hF hG
    (hFp.mono_exponent hpp') (hGp.mono_exponent hpp') hzero t
  apply hb.trans
  simpa only [mul_assoc] using sbxS4_exp_decay_product_mono C C' c c' A
    (lam ^ 2 * (t : ℝ))
    (eLpNorm (F : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q)).toReal
    (eLpNorm (G : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q)).toReal
    (eLpNorm (F : FieldPair d → ℂ) (ENNReal.ofReal p') (reducedLaw Q)).toReal
    (eLpNorm (G : FieldPair d → ℂ) (ENNReal.ofReal p') (reducedLaw Q)).toReal
    hC hCC hcc (hl.le.trans hA) (by positivity)
    ENNReal.toReal_nonneg ENNReal.toReal_nonneg hNf hNg


/-- Smooth remainder moments imply integrability of the coupled covariance. -/
theorem smooth_covariance_integrable_of_remainder
    (hrem : node_rt_u3A_remainder_u2D_momentStmtV3) :
    ∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d),
    ∃ l₀ p : ℝ, 0 < l₀ ∧ D.dependenceRange < 2 * l₀ ∧ 2 ≤ p ∧
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
  intro d hd D
  obtain ⟨l₀, p, c, C, hl₀, hsep, hp, _hc, _hC, hrem'⟩ :=
    hrem d hd D 1 1 (by norm_num) (by norm_num)
  refine ⟨l₀, p, hl₀, hsep, hp, ?_⟩
  intro Q hQ lam h₀ h₁ l δ hl hδ₀ hδ₁ P K hK hD F G hF hG hFp hGp t μ hμ
  let : IsProbabilityMeasure (Regeneration.annealedCoupledLaw Q.measure K) :=
    Regeneration.annealedCoupledLaw_isProbabilityMeasure Q.measure K hK.1
  have hprob : Regeneration.annealedCoupledLaw Q.measure K Set.univ ≤
      ENNReal.ofReal (1 * Real.exp (1 * (lam ^ 2 * (t : ℝ)) -
        1 * lam ^ 2 * (t : ℝ))) := by simp
  have hint := (hrem' Q hQ lam h₀ h₁ l δ hl hδ₀ hδ₁ P K hK hD
    F G hF hG hFp hGp (lam ^ 2 * (t : ℝ)) t Set.univ
    (mul_nonneg (sq_nonneg lam) t.coe_nonneg) MeasurableSet.univ hprob μ hμ).1
  simpa only [integrableOn_univ] using hint


theorem smooth_complex_path_product_growth_of_remainder
    (hrem : node_rt_u3A_remainder_u2D_momentStmtV3) :
    ∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d),
    ∃ l₀ p C : ℝ, 0 < l₀ ∧ D.dependenceRange < 2 * l₀ ∧ 2 ≤ p ∧ 0 < C ∧
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
  intro d hd D
  obtain ⟨l₀, p, c, C, hl₀, hsep, hp, hc, hC, hr⟩ :=
    hrem d hd D 1 1 zero_lt_one zero_lt_one
  refine ⟨l₀, p, C, hl₀, hsep, hp, hC, ?_⟩
  intro Q hQ lam h₀ h₁ l δ hl hδ₀ hδ₁ P K hK hD F G hF hG hFp hGp t
  have := Regeneration.annealedCoupledLaw_isProbabilityMeasure Q.measure K hK.1
  have hwhole : Regeneration.annealedCoupledLaw Q.measure K Set.univ ≤
      ENNReal.ofReal (1 * Real.exp (1 * (lam ^ 2 * (t : ℝ)) -
        1 * lam ^ 2 * (t : ℝ))) := by
    simp only [one_mul, sub_self, Real.exp_zero, ENNReal.ofReal_one, measure_univ, le_rfl]
  obtain ⟨hprod, hbound⟩ := hr Q hQ lam h₀ h₁ l δ hl hδ₀ hδ₁ P K hK hD
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


theorem smooth_coupled_endpoint_memLp_two_of_remainder
    (hrem : node_rt_u3A_remainder_u2D_momentStmtV3) :
    ∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d),
    ∃ l₀ p C : ℝ, 0 < l₀ ∧ D.dependenceRange < 2 * l₀ ∧ 2 ≤ p ∧ 0 < C ∧
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
  intro d hd D
  obtain ⟨l₀, p, C, hl₀, hsep, hp, hC, hgrowth⟩ :=
    smooth_complex_path_product_growth_of_remainder hrem d hd D
  refine ⟨l₀, p, C, hl₀, hsep, hp, hC, ?_⟩
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
  obtain ⟨hprod, _hpair, hb⟩ := hgrowth Q hQ lam h₀ h₁ l δ hl hδ₀ hδ₁ P K hK hD
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


theorem smooth_supplied_average_growth_of_remainder
    (hrem : node_rt_u3A_remainder_u2D_momentStmtV3) :
    ∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d),
    ∃ l₀ p C : ℝ, 0 < l₀ ∧ D.dependenceRange < 2 * l₀ ∧ 2 ≤ p ∧ 0 < C ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange), HasSmoothBounds D Q →
    ∀ (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
      (l δ : ℝ), l₀ ≤ l → 0 < δ → δ < 1 →
    ∀ (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
      (_hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K)
      (_hD : Regeneration.annealedCoupledLaw Q.measure K
        (regenerationNoReturn hd (l / lam)) ≠ 0)
      (F : FieldPair d → ℂ),
    Measurable F → MemLp F (2 * ENNReal.ofReal p) (reducedLaw Q) → ∀ t : ℝ≥0,
    MemLp (fun ω => ∫ γ : Path d, F (translate (γ t) (reduce ω)) ∂P (0, ω)) 2 Q.measure ∧
    (∫ ω, ‖∫ γ : Path d, F (translate (γ t) (reduce ω)) ∂P (0, ω)‖ ^ 2 ∂Q.measure) ≤
      C * Real.exp (C * lam ^ 2 * (t : ℝ)) *
        (eLpNorm F (2 * ENNReal.ofReal p) (reducedLaw Q)).toReal ^ 2 := by
  intro d hd D
  obtain ⟨l₀, p, C, hl₀, hsep, hp, hC, hgrowth⟩ :=
    smooth_coupled_endpoint_memLp_two_of_remainder hrem d hd D
  refine ⟨l₀, p, C, hl₀, hsep, hp, hC, ?_⟩
  intro Q hQ lam h₀ h₁ l δ hl hδ₀ hδ₁ P K hK hD F hF hFp t
  obtain ⟨hend, _hquenched, hbound⟩ :=
    hgrowth Q hQ lam h₀ h₁ l δ hl hδ₀ hδ₁ P K hK hD F hF hFp t
  obtain ⟨hmean, hmeanbound⟩ :=
    sbxS4_supplied_average_memLp_two_of_coupled hd Q lam l δ h₀.le h₁ P K hK t hF hend
  exact ⟨hmean, hmeanbound.trans hbound⟩


theorem smooth_supplied_average_operator_of_remainder
    (hrem : node_rt_u3A_remainder_u2D_momentStmtV3) :
    ∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d),
    ∃ l₀ p C : ℝ, 0 < l₀ ∧ D.dependenceRange < 2 * l₀ ∧ ∃ hp : 2 ≤ p, 0 < C ∧
    letI : Fact (1 ≤ 2 * ENNReal.ofReal p) := ⟨by
      have h : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
        simpa only [ENNReal.ofReal_one] using
          (ENNReal.ofReal_le_ofReal (show (1 : ℝ) ≤ p by linarith))
      exact h.trans (le_mul_of_one_le_left (by positivity) (by norm_num))⟩
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange), HasSmoothBounds D Q →
    ∀ (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
      (l δ : ℝ), l₀ ≤ l → 0 < δ → δ < 1 →
    ∀ (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
      (_hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K)
      (_hD : Regeneration.annealedCoupledLaw Q.measure K
        (regenerationNoReturn hd (l / lam)) ≠ 0) (t : ℝ≥0),
    ∃ T : Lp ℂ (2 * ENNReal.ofReal p) (reducedLaw Q) →L[ℂ] Lp ℂ 2 Q.measure,
      (∀ F, T F =ᵐ[Q.measure]
        fun ω => ∫ γ : Path d, F (translate (γ t) (reduce ω)) ∂P (0, ω)) ∧
      (∀ F, ‖T F‖ ^ 2 ≤ C * Real.exp (C * lam ^ 2 * (t : ℝ)) * ‖F‖ ^ 2) ∧
      ‖T‖ ≤ Real.sqrt (C * Real.exp (C * lam ^ 2 * (t : ℝ))) := by
  intro d hd D
  obtain ⟨l₀, p, C, hl₀, hsep, hp, hC, hgrowth⟩ :=
    smooth_coupled_endpoint_memLp_two_of_remainder hrem d hd D
  refine ⟨l₀, p, C, hl₀, hsep, hp, hC, ?_⟩
  letI : Fact (1 ≤ 2 * ENNReal.ofReal p) := ⟨by
    have h : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
      simpa only [ENNReal.ofReal_one] using
          (ENNReal.ofReal_le_ofReal (show (1 : ℝ) ≤ p by linarith))
    exact h.trans (le_mul_of_one_le_left (by positivity) (by norm_num))⟩
  intro Q hQ lam h₀ h₁ l δ hl hδ₀ hδ₁ P K hK hD t
  let M : Lp ℂ (2 * ENNReal.ofReal p) (reducedLaw Q) → FieldPair d → ℂ :=
    fun F ω => ∫ γ : Path d, F (translate (γ t) (reduce ω)) ∂P (0, ω)
  have hdata (F : Lp ℂ (2 * ENNReal.ofReal p) (reducedLaw Q)) :
      (∀ᵐ ω ∂Q.measure,
        Integrable (fun γ : Path d => F (translate (γ t) (reduce ω))) (P (0, ω))) ∧
      MemLp (M F) 2 Q.measure ∧
      (∫ ω, ‖M F ω‖ ^ 2 ∂Q.measure) ≤
        C * Real.exp (C * lam ^ 2 * (t : ℝ)) * ‖F‖ ^ 2 := by
    have hF : Measurable F := (Lp.stronglyMeasurable F).measurable
    obtain ⟨hend, hquenched, hbound⟩ :=
      hgrowth Q hQ lam h₀ h₁ l δ hl hδ₀ hδ₁ P K hK hD F hF (Lp.memLp F) t
    obtain ⟨hmean, hmeanbound⟩ :=
      sbxS4_supplied_average_memLp_two_of_coupled hd Q lam l δ h₀.le h₁ P K hK t hF hend
    have hprob := hK.2.2.1
    have hi : ∀ᵐ ω ∂Q.measure,
        Integrable (fun γ : Path d => F (translate (γ t) (reduce ω))) (P (0, ω)) := by
      filter_upwards [hquenched, hprob] with ω hω hP
      obtain ⟨_, R, hR⟩ := hP
      have : IsProbabilityMeasure (P (0, ω)) := by
        rw [hR 0]
        exact R.pathLaw_isMarkovKernel.isProbabilityMeasure 0
      exact hω.integrable (by norm_num)
    exact ⟨hi, hmean, by simpa only [Lp.norm_def] using hmeanbound.trans hbound⟩
  let L : Lp ℂ (2 * ENNReal.ofReal p) (reducedLaw Q) →ₗ[ℂ] Lp ℂ 2 Q.measure :=
    { toFun := fun F => (hdata F).2.1.toLp (M F)
      map_add' := by
        intro F G
        apply Lp.ext
        have he := SbxS4Dynkin.ae_eq_at_supplied_endpoint hd Q lam h₀.le h₁ P
          hK.2.2.1 t (Lp.stronglyMeasurable (F + G)).measurable
          ((Lp.stronglyMeasurable F).measurable.add (Lp.stronglyMeasurable G).measurable)
          (Lp.coeFn_add F G)
        filter_upwards [(hdata (F + G)).2.1.coeFn_toLp,
          Lp.coeFn_add ((hdata F).2.1.toLp (M F)) ((hdata G).2.1.toLp (M G)),
          (hdata F).2.1.coeFn_toLp, (hdata G).2.1.coeFn_toLp,
          (hdata F).1, (hdata G).1, he] with ω hsum hadd hF hG hiF hiG he
        rw [hsum, hadd]
        change M (F + G) ω = ((hdata F).2.1.toLp (M F)) ω +
          ((hdata G).2.1.toLp (M G)) ω
        rw [hF, hG]
        exact (integral_congr_ae he).trans (integral_add hiF hiG)
      map_smul' := by
        intro c F
        apply Lp.ext
        have he := SbxS4Dynkin.ae_eq_at_supplied_endpoint hd Q lam h₀.le h₁ P
          hK.2.2.1 t (Lp.stronglyMeasurable (c • F)).measurable
          ((Lp.stronglyMeasurable F).measurable.const_smul c) (Lp.coeFn_smul c F)
        filter_upwards [(hdata (c • F)).2.1.coeFn_toLp,
          Lp.coeFn_smul c ((hdata F).2.1.toLp (M F)),
          (hdata F).2.1.coeFn_toLp, he] with ω hsmul hcoe hF he
        rw [hsmul]
        change M (c • F) ω = (c • (hdata F).2.1.toLp (M F)) ω
        rw [hcoe]
        change M (c • F) ω = c • ((hdata F).2.1.toLp (M F)) ω
        rw [hF]
        exact (integral_congr_ae he).trans (integral_smul c _) }
  have hbound (F : Lp ℂ (2 * ENNReal.ofReal p) (reducedLaw Q)) :
      ‖L F‖ ^ 2 ≤ C * Real.exp (C * lam ^ 2 * (t : ℝ)) * ‖F‖ ^ 2 := by
    rw [sbxS4_L2_norm_sq]
    have he := (hdata F).2.1.coeFn_toLp
    exact (integral_congr_ae (he.mono fun _ h => congrArg (fun z : ℂ => ‖z‖ ^ 2) h)).le.trans
      (hdata F).2.2
  let A := C * Real.exp (C * lam ^ 2 * (t : ℝ))
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hnorm_bound (F : Lp ℂ (2 * ENNReal.ofReal p) (reducedLaw Q)) :
      ‖L F‖ ≤ Real.sqrt A * ‖F‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
    simpa only [mul_pow, Real.sq_sqrt hA] using hbound F
  let T := L.mkContinuous (Real.sqrt A) hnorm_bound
  exact ⟨T, fun F => (hdata F).2.1.coeFn_toLp, hbound,
    T.opNorm_le_bound (Real.sqrt_nonneg _) hnorm_bound⟩



theorem smooth_sbxS2_covariance_decomposition_of_deps
    (hfactor : node_rt_u3A_k_u2D_factorStmt)
    (hrem : node_rt_u3A_remainder_u2D_momentStmtV3) :
    ∀ (d : ℕ) (hd : 2 ≤ d) (SD : StructuralData d),
    ∃ l₀ p : ℝ, 0 < l₀ ∧ SD.dependenceRange < 2 * l₀ ∧ 2 ≤ p ∧
    ∀ (l δ : ℝ), l₀ ≤ l → 0 < δ → δ < 1 →
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
  intro d hd SD
  obtain ⟨l₀, p, hl₀, hsep, hp, hInt⟩ :=
    smooth_covariance_integrable_of_remainder hrem d hd SD
  refine ⟨l₀, p, hl₀, hsep, hp, ?_⟩
  intro l δ hl hδ₀ hδ₁ Q hQ lam h₀ h₁ P K hK hD A hA F G hF hFp hG hGp t
  dsimp only
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
  have hi := hInt Q hQ lam h₀ h₁ l δ hl hδ₀ hδ₁ P K hK hD F G hFg hGg hFp hGp
    t μ (by simp [μ])
  have hiG (u : ℝ≥0) : Integrable
      (fun ωz => G (translate (ωz.2.1 u) (reduce ωz.1))) ν := by
    let : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
    simpa only [one_mul] using
      hInt Q hQ lam h₀ h₁ l δ hl hδ₀ hδ₁ P K hK hD (fun _ => 1) G
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
    (sbxS2_bounded_covariance_decomposition hfactor hd (hl₀.trans_le hl)
      (hsep.trans_le (by linarith)) hδ₀ hδ₁ Q lam h₀ h₁ P K hK hD A hA p hp F
      (Gc n) hF hFp (hGc n) (hb n) t).2
  have hsum : Filter.Tendsto
      (fun n => ∑ j ∈ Finset.range (N + 1), q j * H (Gc n) (t - j * Δ))
      Filter.atTop (𝓝 (∑ j ∈ Finset.range (N + 1), q j * H G (t - j * Δ))) :=
    tendsto_finsetSum (Finset.range (N + 1))
      (fun j _ => tendsto_const_nhds.mul (hH (t - j * Δ)))
  refine ⟨hi, ?_⟩
  exact tendsto_nhds_unique hCov ((hRem.add hsum).congr'
    (Filter.Eventually.of_forall (fun n => (heq n).symm)))


theorem smooth_sbxS2_centered_covariance_of_deps
    (hfactor : node_rt_u3A_k_u2D_factorStmt)
    (hmany : node_rt_u3A_many_u2D_cycle_u2D_momentStmt)
    (hrem : node_rt_u3A_remainder_u2D_momentStmtV3) :
    ∀ (d : ℕ) (hd : 2 ≤ d) (SD : StructuralData d),
    ∃ l₀ p : ℝ, 0 < l₀ ∧ SD.dependenceRange < 2 * l₀ ∧ 2 ≤ p ∧
    ∀ (l δ : ℝ), l₀ ≤ l → 0 < δ → δ < 1 →
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
  intro d hd SD
  obtain ⟨lD, p, hlD, hsepD, hp, hDec⟩ :=
    smooth_sbxS2_covariance_decomposition_of_deps hfactor hrem d hd SD
  obtain ⟨lM, _hlM, _hsepM, hCenter⟩ :=
    sbxS2_centered_slices_of_manyCycleMoment hmany d hd SD.ellipticity SD.dependenceRange
  refine ⟨max lD lM, p, hlD.trans_le (le_max_left _ _),
    hsepD.trans_le (by linarith only [le_max_left lD lM]), hp, ?_⟩
  intro l δ hl hδ₀ hδ₁ Q hQ lam h₀ h₁ P K hK hD A hA F G hF hG hFp hGp hzero
  dsimp only
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
    hCenter l ((le_max_right _ _).trans hl) δ hδ₀ hδ₁ Q lam h₀ h₁ P K hK hD p
      ((by norm_num : (1 : ℝ) ≤ 2).trans hp) F
      (hF.mono (Probability.localSigma_le_borel _) le_rfl) hFp hzero k
  have hcov := hDec l δ ((le_max_left _ _).trans hl) hδ₀ hδ₁ Q hQ lam h₀ h₁
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



theorem smooth_sbxS2_covariance_sub_remainder_decay_of_deps
    (hfactor : node_rt_u3A_k_u2D_factorStmt)
    (hphase : phaseErrorSmoothStmt)
    (hmany : node_rt_u3A_many_u2D_cycle_u2D_momentStmt)
    (hrem : node_rt_u3A_remainder_u2D_momentStmtV3) :
    ∀ (d : ℕ) (hd : 2 ≤ d) (SD : StructuralData d),
    ∃ l₀ : ℝ, 0 < l₀ ∧ SD.dependenceRange < 2 * l₀ ∧
    ∀ l : ℝ, l₀ ≤ l → ∀ δ : ℝ, 0 < δ → δ < 1 →
    ∃ p c C : ℝ, 2 ≤ p ∧ 0 < c ∧ 0 < C ∧
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
  intro d hd SD
  obtain ⟨lD, pD, hlD, hsepD, hpD, hcenter⟩ :=
    smooth_sbxS2_centered_covariance_of_deps hfactor hmany hrem d hd SD
  obtain ⟨lM, _hlM, _hsepM, hdecay⟩ :=
    sbxS2_slice_decay_of_manyCycleMoment hmany d hd SD.ellipticity SD.dependenceRange
  obtain ⟨lP, _hlP, _hsepP, hph⟩ := hphase d hd SD
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
  intro Q hQ lam h₀ h₁ P K hK hD A hA F G hF hG hFp hGp hzero
  let := reducedLaw_probability Q
  dsimp only
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
  have hco := hcenter l δ hlD' hδ₀ hδ₁ Q hQ lam h₀ h₁ P K hK hD A hA F G hF hG
    (hFp.mono_exponent hpD') (hGp.mono_exponent hpD') hzero
  have hsupport : 10 * (m : ℝ) * l - l - A ≥ -2 * l := by
    have hx : (A / l - 1) / 10 ≤ (m : ℝ) := (Nat.le_ceil _).trans
      (by exact_mod_cast le_max_right 1 ⌈(A / l - 1) / 10⌉₊)
    have hdiv : A / l ≤ 10 * (m : ℝ) + 1 := by linarith
    have := (div_le_iff₀ hlpos).mp hdiv
    nlinarith
  have hpa := hpd Q hQ lam h₀ h₁ P K hK hD A m hA (le_max_left _ _) hsupport G hG
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
        hqd Q lam h₀ h₁ P K hK hD p (hpD.trans (le_max_left _ _)) F
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


theorem smooth_sbxS2_covariance_sub_remainder_time_decay_of_deps
    (hfactor : node_rt_u3A_k_u2D_factorStmt)
    (hphase : phaseErrorSmoothStmt)
    (hmany : node_rt_u3A_many_u2D_cycle_u2D_momentStmt)
    (hrem : node_rt_u3A_remainder_u2D_momentStmtV3) :
    ∀ (d : ℕ) (hd : 2 ≤ d) (SD : StructuralData d),
    ∃ l₀ : ℝ, 0 < l₀ ∧ SD.dependenceRange < 2 * l₀ ∧
    ∀ l : ℝ, l₀ ≤ l → ∀ δ : ℝ, 0 < δ → δ < 1 →
    ∃ p c C : ℝ, 2 ≤ p ∧ 0 < c ∧ 0 < C ∧
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
  intro d hd SD
  obtain ⟨l₀, hl₀, hsep, hdec⟩ :=
    smooth_sbxS2_covariance_sub_remainder_decay_of_deps hfactor hphase hmany hrem d hd SD
  refine ⟨l₀, hl₀, hsep, ?_⟩
  intro l hl δ hδ₀ hδ₁
  obtain ⟨p, c, C, hp, hc, hC, hbound⟩ := hdec l hl δ hδ₀ hδ₁
  let D := C * Real.exp c + C
  have hDpos : 0 < D := by dsimp only [D]; positivity
  have hCD : C ≤ D := by dsimp only [D]; linarith only [mul_pos hC (Real.exp_pos c)]
  refine ⟨p, c, D, hp, hc, hDpos, ?_⟩
  intro Q hQ lam h₀ h₁ P K hK hD A hA F G hF hG hFp hGp hzero
  dsimp only
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
  have hmain := hbound Q hQ lam h₀ h₁ P K hK hD A hA F G hF hG hFp hGp hzero s hs j
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


theorem smooth_sbxS2_covariance_power_moment_of_remainder
    (hrem : node_rt_u3A_remainder_u2D_momentStmtV3) :
    ∀ (d : ℕ) (hd : 2 ≤ d) (SD : StructuralData d),
    ∃ l₀ p C : ℝ, 0 < l₀ ∧ SD.dependenceRange < 2 * l₀ ∧ 2 ≤ p ∧ 0 < C ∧
    ∀ (r : ℝ), 0 < r →
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
  intro d hd SD
  obtain ⟨l₀, p, c, C, hl₀, hsep, hp, hc, hC, hrem'⟩ :=
    hrem d hd SD 1 1 (by norm_num) (by norm_num)
  refine ⟨l₀, p, C, hl₀, hsep, hp, hC, ?_⟩
  intro r hr Q hQ lam h₀ h₁ l δ hl hδ₀ hδ₁ P K hK hD F G hF hG hFp hGp t μ hμ
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
  have hmain := hrem' Q hQ lam h₀ h₁ l δ hl hδ₀ hδ₁ P K hK hD
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



theorem smooth_sbxS2_remainder_moment_variable_rate
    (hrem : node_rt_u3A_remainder_u2D_momentStmtV3) :
    ∀ (d : ℕ) (hd : 2 ≤ d) (SD : StructuralData d),
    ∃ l₀ : ℝ, 0 < l₀ ∧ SD.dependenceRange < 2 * l₀ ∧
    ∀ a : ℝ, 0 < a → ∃ p c C : ℝ, 2 ≤ p ∧ 0 < c ∧ 0 < C ∧
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
  intro d hd SD
  obtain ⟨l₀, p₀, D, hl₀, hsep, hp₀, hDpos, hmoment⟩ :=
    smooth_sbxS2_covariance_power_moment_of_remainder hrem d hd SD
  refine ⟨l₀, hl₀, hsep, ?_⟩
  intro a ha
  obtain ⟨r, c, C, hr, hc, hC, hscalar⟩ :=
    sbxS2_power_interpolation_constants D a hDpos ha
  have hr₁ : 1 < r := lt_of_lt_of_le (by norm_num) hr
  have hr₀ : 0 < r := lt_trans zero_lt_one hr₁
  have hp₀pos : 0 ≤ p₀ := le_trans (by norm_num) hp₀
  refine ⟨p₀ * r, c, C, ?_, hc, hC, ?_⟩
  · exact hp₀.trans (le_mul_of_one_le_right hp₀pos hr₁.le)
  intro Q hQ lam h₀ h₁ l δ hl hδ₀ hδ₁ P K hK hD F G hF hG hFp hGp J t E hJ hprob
  let μ := Regeneration.annealedCoupledLaw Q.measure K
  let f := fun ωz : FieldPair d × Regeneration.CoupledSample d =>
    F (reduce ωz.1) * G (translate (ωz.2.1 t) (reduce ωz.1))
  have hfm : Measurable f :=
    ((hF.comp Probability.measurable_reduce).comp measurable_fst).mul
      (hG.comp (Probability.continuous_translate.measurable.comp
        (((continuous_eval_const t).measurable.comp measurable_snd.fst).prodMk
          (Probability.measurable_reduce.comp measurable_fst))))
  have hpower := hmoment r hr₀ Q hQ lam h₀ h₁ l δ hl hδ₀ hδ₁ P K hK hD
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


theorem smooth_sbxS2_regeneration_remainder_decay_of_deps
    (hmany : node_rt_u3A_many_u2D_cycle_u2D_momentStmt)
    (hrem : node_rt_u3A_remainder_u2D_momentStmtV3) :
    ∀ (d : ℕ) (hd : 2 ≤ d) (SD : StructuralData d),
    ∃ l₀ : ℝ, 0 < l₀ ∧ SD.dependenceRange < 2 * l₀ ∧
    ∀ l : ℝ, l₀ ≤ l → ∀ δ : ℝ, 0 < δ → δ < 1 →
    ∃ p c C : ℝ, 2 ≤ p ∧ 0 < c ∧ 0 < C ∧
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
  intro d hd SD
  obtain ⟨lR, hlR, hsep, hrate⟩ := smooth_sbxS2_remainder_moment_variable_rate hrem d hd SD
  obtain ⟨lM, hlM, _hsepM, hmoment⟩ := hmany d hd SD.ellipticity SD.dependenceRange
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
    have hm' := ((hm Q lam h₀ h₁ P K hK hD).2 j).trans
      (ENNReal.ofReal_le_ofReal hgeom)
    have ht := exponential_time_tail μ
      (fun ωz : FieldPair d × Regeneration.CoupledSample d =>
        regenerationTime hd lam l j ωz.2)
      ((Regeneration.measurable_regenerationTime _ _ _ _ _).comp measurable_snd)
      (a * lam ^ 2) (Real.exp J) (by positivity) t hm'
    simpa only [← Real.exp_add, neg_mul, sub_eq_add_neg] using ht
  have hb := hbound Q hQ lam h₀ h₁ l δ hlR' hδ₀ hδ₁ P K hK hD
    F G hF hG hFp hGp J t _ hJ htail
  refine ⟨hb.1, hb.2.trans ?_⟩
  apply mul_le_mul_of_nonneg_right _ ENNReal.toReal_nonneg
  apply mul_le_mul_of_nonneg_right _ ENNReal.toReal_nonneg
  apply mul_le_mul hCD (Real.exp_le_exp.mpr ?_) (Real.exp_pos _).le hDpos.le
  dsimp only [J]
  nlinarith only [mul_le_mul_of_nonneg_right hcycle (Nat.cast_nonneg j : (0 : ℝ) ≤ j)]



theorem smooth_sbxS2_covariance_and_remainder_decay_of_deps
    (hfactor : node_rt_u3A_k_u2D_factorStmt)
    (hphase : phaseErrorSmoothStmt)
    (hmany : node_rt_u3A_many_u2D_cycle_u2D_momentStmt)
    (hrem : node_rt_u3A_remainder_u2D_momentStmtV3) :
    ∀ (d : ℕ) (hd : 2 ≤ d) (SD : StructuralData d),
    ∃ l₀ : ℝ, 0 < l₀ ∧ SD.dependenceRange < 2 * l₀ ∧
    ∀ l : ℝ, l₀ ≤ l → ∀ δ : ℝ, 0 < δ → δ < 1 →
    ∃ p c C : ℝ, 2 ≤ p ∧ 0 < c ∧ 0 < C ∧
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
  intro d hd SD
  obtain ⟨lD, hlD, hsepD, hdec⟩ :=
    smooth_sbxS2_covariance_sub_remainder_time_decay_of_deps hfactor hphase hmany hrem d hd SD
  obtain ⟨lR, _hlR, _hsepR, hremdec⟩ :=
    smooth_sbxS2_regeneration_remainder_decay_of_deps hmany hrem d hd SD
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
  intro Q hQ lam h₀ h₁ P K hK hD A hA F G hF hG hFp hGp hzero
  let := reducedLaw_probability Q
  dsimp only
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
  have hbD := hboundD Q hQ lam h₀ h₁ P K hK hD A hA F G hF hG
    (hFp.mono_exponent hpD') (hGp.mono_exponent hpD') hzero
  have hbR := hboundR Q hQ lam h₀ h₁ P K hK hD F G
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



theorem smooth_sbxS2_positive_km_decomp_of_deps
    (hfactor : node_rt_u3A_k_u2D_factorStmt)
    (hphase : phaseErrorSmoothStmt)
    (hmany : node_rt_u3A_many_u2D_cycle_u2D_momentStmt)
    (hrem : node_rt_u3A_remainder_u2D_momentStmtV3) :
  ∀ (d : ℕ) (hd : 2 ≤ d) (SD : StructuralData d),
    ∃ l₀ : ℝ, 0 < l₀ ∧ SD.dependenceRange < 2 * l₀ ∧
    ∀ l : ℝ, l₀ ≤ l → ∀ δ : ℝ, 0 < δ → δ < 1 →
    ∃ p c C lam₀ : ℝ, 2 ≤ p ∧ 0 < c ∧ 0 < C ∧ 0 < lam₀ ∧ lam₀ ≤ 1 ∧
    ∀ Q : EnvironmentLaw d SD.ellipticity SD.dependenceRange, HasSmoothBounds SD Q →
    ∀ (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1), lam ≤ lam₀ →
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
  intro d hd SD
  obtain ⟨lA, pA, hlA, hsepA, hpA, halgebra⟩ :=
    smooth_sbxS2_centered_covariance_of_deps hfactor hmany hrem d hd SD
  obtain ⟨lQ, _hlQ, _hsepQ, hslice⟩ :=
    sbxS2_slice_decay_normalized_of_manyCycleMoment hmany d hd SD.ellipticity SD.dependenceRange
  obtain ⟨lB, _hlB, _hsepB, hdecay⟩ :=
    smooth_sbxS2_covariance_and_remainder_decay_of_deps hfactor hphase hmany hrem d hd SD
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
  refine ⟨p, c, C, 1, hp, lt_min hcQ hcB, hC, by norm_num, le_rfl, ?_⟩
  intro Q hQ lam h₀ h₁ _hlam P K hK hD A hA F G hF hG hFp hGp hzero
  let := reducedLaw_probability Q
  dsimp only
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
  have ha := halgebra l δ hlA' hδ₀ hδ₁ Q hQ lam h₀ h₁ P K hK hD A hA F G hF hG
    (hFp.mono_exponent hpA') (hGp.mono_exponent hpA') hzero
  have hdcy := hb Q hQ lam h₀ h₁ P K hK hD A hA F G hF hG
    (hFp.mono_exponent hpB') (hGp.mono_exponent hpB') hzero
  refine ⟨?_, ha.1, ha.2.1, ?_, ?_, ha.2.2.2⟩
  · apply (sbxS2_prescribed_cycles_le l A hlpos hA).trans
    exact mul_le_mul_of_nonneg_right hcycleC (by linarith only [hlpos, hA])
  · intro n
    have hs := hq Q lam h₀ h₁ P K hK hD p hp F
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


theorem smooth_sbxS2_covariance_radius_decay_of_deps
    (hfactor : node_rt_u3A_k_u2D_factorStmt)
    (hphase : phaseErrorSmoothStmt)
    (hmany : node_rt_u3A_many_u2D_cycle_u2D_momentStmt)
    (hrem : node_rt_u3A_remainder_u2D_momentStmtV3) :
    ∀ (d : ℕ) (hd : 2 ≤ d) (SD : StructuralData d),
    ∃ l₀ : ℝ, 0 < l₀ ∧ SD.dependenceRange < 2 * l₀ ∧
    ∀ l : ℝ, l₀ ≤ l → ∀ δ : ℝ, 0 < δ → δ < 1 →
    ∃ p c C : ℝ, 2 ≤ p ∧ 0 < c ∧ 0 < C ∧
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
  intro d hd SD
  obtain ⟨l₀, hl₀, hsep, hdecay⟩ :=
    smooth_sbxS2_covariance_and_remainder_decay_of_deps hfactor hphase hmany hrem d hd SD
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
  intro Q hQ lam h₀ h₁ P K hK hD' A hA F G hF hG hFp hGp hzero
  dsimp only
  intro t
  apply ((hb Q hQ lam h₀ h₁ P K hK hD' A hA F G hF hG hFp hGp hzero t).2).trans
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



theorem smooth_sbxS4_positive_complex_path_covariance_of_deps
    (hfactor : node_rt_u3A_k_u2D_factorStmt)
    (hphase : phaseErrorSmoothStmt)
    (hmany : node_rt_u3A_many_u2D_cycle_u2D_momentStmt)
    (hrem : node_rt_u3A_remainder_u2D_momentStmtV3) :
    ∀ (d : ℕ) (hd : 2 ≤ d) (SD : StructuralData d),
    ∃ l₀ : ℝ, 0 < l₀ ∧ SD.dependenceRange < 2 * l₀ ∧
    ∀ l : ℝ, l₀ ≤ l → ∀ δ : ℝ, 0 < δ → δ < 1 →
    ∃ p c C : ℝ, 2 ≤ p ∧ 0 < c ∧ 0 < C ∧
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
  intro d hd SD
  obtain ⟨l₀, hl₀, hsep, hdecay⟩ :=
    smooth_sbxS2_covariance_radius_decay_of_deps hfactor hphase hmany hrem d hd SD
  refine ⟨l₀, hl₀, hsep, ?_⟩
  intro l hl δ hδ₀ hδ₁
  obtain ⟨p, c, C, hp, hc, hC, hb⟩ := hdecay l hl δ hδ₀ hδ₁
  refine ⟨p, c, C, hp, hc, hC, ?_⟩
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
  have hbound := hb Q hQ lam h₀ h₁ P K hK hD A hA f g hf hg hfp hgp hfzero t
  rw [hfnorm, hgnorm] at hbound
  exact hbound


theorem smooth_sbxS4_positive_complex_integrable_covariance_of_deps
    (hfactor : node_rt_u3A_k_u2D_factorStmt)
    (hphase : phaseErrorSmoothStmt)
    (hmany : node_rt_u3A_many_u2D_cycle_u2D_momentStmt)
    (hrem : node_rt_u3A_remainder_u2D_momentStmtV3) :
    ∀ (d : ℕ) (hd : 2 ≤ d) (SD : StructuralData d),
    ∃ l₀ : ℝ, 0 < l₀ ∧ SD.dependenceRange < 2 * l₀ ∧
    ∀ l : ℝ, l₀ ≤ l → ∀ δ : ℝ, 0 < δ → δ < 1 →
    ∃ p c C : ℝ, 2 ≤ p ∧ 0 < c ∧ 0 < C ∧
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
    Integrable (fun w => F (reduce w.1) * G (sbxS4CoupledEndpoint t w))
      (Regeneration.annealedCoupledLaw Q.measure K) ∧
    ‖∫ w, F (reduce w.1) * G (sbxS4CoupledEndpoint t w)
      ∂Regeneration.annealedCoupledLaw Q.measure K‖ ≤
      C * Real.exp (C * A - c * lam ^ 2 * (t : ℝ)) *
        (eLpNorm (F : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q)).toReal *
        (eLpNorm (G : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q)).toReal := by
  intro d hd SD
  obtain ⟨lD, hlD, hsepD, hdecay⟩ :=
    smooth_sbxS4_positive_complex_path_covariance_of_deps hfactor hphase hmany hrem d hd SD
  obtain ⟨lR, pR, _CR, _hlR, _hsepR, _hpR, _hCR, hgrowth⟩ :=
    smooth_complex_path_product_growth_of_remainder hrem d hd SD
  refine ⟨max lD lR, hlD.trans_le (le_max_left _ _),
    hsepD.trans_le (by linarith only [le_max_left lD lR]), ?_⟩
  intro l hl δ hδ₀ hδ₁
  have hlD' : lD ≤ l := (le_max_left _ _).trans hl
  have hlR' : lR ≤ l := (le_max_right _ _).trans hl
  obtain ⟨pD, c, C, hpD, hc, hC, hb⟩ := hdecay l hlD' δ hδ₀ hδ₁
  refine ⟨max pD pR, c, C, hpD.trans (le_max_left _ _), hc, hC, ?_⟩
  intro Q hQ lam h₀ h₁ P K hK hD A hA F G hFl hGl hFp hGp hzero t
  have := reducedLaw_probability Q
  have hpD' : ENNReal.ofReal pD ≤ ENNReal.ofReal (max pD pR) :=
    ENNReal.ofReal_le_ofReal (le_max_left _ _)
  have hpR' : ENNReal.ofReal pR ≤ ENNReal.ofReal (max pD pR) :=
    ENNReal.ofReal_le_ofReal (le_max_right _ _)
  have hint := (hgrowth Q hQ lam h₀ h₁ l δ hlR' hδ₀ hδ₁ P K hK hD F G
    (Lp.stronglyMeasurable F).measurable (Lp.stronglyMeasurable G).measurable
    (hFp.mono_exponent hpR') (hGp.mono_exponent hpR') t).1
  refine ⟨hint, ?_⟩
  have hbound := hb Q hQ lam h₀ h₁ P K hK hD A hA F G hFl hGl
    (hFp.mono_exponent hpD') (hGp.mono_exponent hpD') hzero t
  have hFnorm := ENNReal.toReal_mono hFp.eLpNorm_ne_top
    (eLpNorm_le_eLpNorm_of_exponent_le (f := (F : FieldPair d → ℂ)) hpD')
  have hGnorm := ENNReal.toReal_mono hGp.eLpNorm_ne_top
    (eLpNorm_le_eLpNorm_of_exponent_le (f := (G : FieldPair d → ℂ)) hpD')
  exact hbound.trans (mul_le_mul
    (mul_le_mul_of_nonneg_left hFnorm (mul_nonneg hC.le (Real.exp_pos _).le))
    hGnorm ENNReal.toReal_nonneg (by positivity))



theorem smooth_c16_km_positive_covariance_of_requested_action
    (hfactor : node_rt_u3A_k_u2D_factorStmt)
    (hphase : phaseErrorSmoothStmt)
    (hmany : node_rt_u3A_many_u2D_cycle_u2D_momentStmt)
    (hrem : node_rt_u3A_remainder_u2D_momentStmtV3) :
    ∀ (d : ℕ) (hd : 2 ≤ d) (SD : StructuralData d),
    ∃ l₀ : ℝ, 0 < l₀ ∧ SD.dependenceRange < 2 * l₀ ∧
    ∀ l : ℝ, l₀ ≤ l → ∀ δ : ℝ, 0 < δ → δ < 1 →
    ∃ p c C : ℝ, 2 ≤ p ∧ 0 < c ∧ 0 < C ∧
    ∀ (Q : EnvironmentLaw d SD.ellipticity SD.dependenceRange), HasSmoothBounds SD Q →
    letI := reducedLaw_probability Q
    ∀ (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1)
      (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
      (_hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K)
      (_hD : Regeneration.annealedCoupledLaw Q.measure K
        (regenerationNoReturn hd (l / lam)) ≠ 0)
      (_hrequested : (∀ᵐ ω ∂Q.measure, SolvesMartingaleProblem
        (reducedGenerator (Regeneration.Renewal.forceCoord hd) ω lam) 0 (P (0, ω))) →
        ∀ (t : ℝ≥0) (f : BoundedContinuousFunction (FieldPair d) ℂ),
        (fun ω => ∫ γ : Path d, f (translate (γ t) (reduce ω)) ∂P (0, ω)) =ᵐ[Q.measure]
          fun ω => forcedComplexEvolution Q (Regeneration.Renewal.forceCoord hd)
            (lam : ℂ) t (BoundedContinuousFunction.toLp 2 (reducedLaw Q) ℂ f) (reduce ω))
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
  intro d hd SD
  obtain ⟨lD, hlD, hsD, hdecay⟩ :=
    smooth_sbxS4_positive_complex_integrable_covariance_of_deps hfactor hphase hmany hrem d hd SD
  obtain ⟨lR, pR, CR, hlR, hsR, hpR, hCR, hgrowth⟩ :=
    smooth_coupled_endpoint_memLp_two_of_remainder hrem d hd SD
  obtain ⟨lT, pT, CT, hlT, hsT, hpT, hCT, hoperator⟩ :=
    smooth_supplied_average_operator_of_remainder hrem d hd SD
  refine ⟨max lD (max lR lT), hlD.trans_le (le_max_left _ _),
    hsD.trans_le (by linarith only [le_max_left lD (max lR lT)]), ?_⟩
  intro l hl δ hδ0 hδ1
  have hlD' := (le_max_left lD (max lR lT)).trans hl
  have hlR' := (le_max_left lR lT).trans ((le_max_right lD (max lR lT)).trans hl)
  have hlT' := (le_max_right lR lT).trans ((le_max_right lD (max lR lT)).trans hl)
  obtain ⟨pD, c, C, hpD, hc, hC, hbound⟩ := hdecay l hlD' δ hδ0 hδ1
  refine ⟨max pD (max (2 * pR) (2 * pT)), c, C,
    hpD.trans (le_max_left _ _), hc, hC, ?_⟩
  intro Q hQ
  let := reducedLaw_probability Q
  intro lam h0 h1 P K hK hD hrequested S hS A hA F G hFl hGl hFp hGp hmean t
  let p := max pD (max (2 * pR) (2 * pT))
  have hpD' : ENNReal.ofReal pD ≤ ENNReal.ofReal p :=
    ENNReal.ofReal_le_ofReal (le_max_left _ _)
  have hpR' : 2 * ENNReal.ofReal pR ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    exact ENNReal.ofReal_le_ofReal ((le_max_left _ _).trans (le_max_right _ _))
  have hpT' : 2 * ENNReal.ofReal pT ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    exact ENNReal.ofReal_le_ofReal ((le_max_right _ _).trans (le_max_right _ _))
  have hq : (2 : ℝ≥0∞) ≤ 2 * ENNReal.ofReal pT := by
    have h : (1 : ℝ≥0∞) ≤ ENNReal.ofReal pT := by
      simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal (show (1 : ℝ) ≤ pT by linarith)
    simpa using mul_le_mul_of_nonneg_left h (show (0 : ℝ≥0∞) ≤ 2 by norm_num)
  have hqfin : 2 * ENNReal.ofReal pT ≠ ∞ := by
    exact ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top
  let : Fact (1 ≤ 2 * ENNReal.ofReal pT) := ⟨le_trans (by norm_num) hq⟩
  obtain ⟨T, hrep, _, _⟩ := hoperator Q hQ lam h0 h1 l δ hlT' hδ0 hδ1 P K hK hD t
  have hend := (hgrowth Q hQ lam h0 h1 l δ hlR' hδ0 hδ1 P K hK hD G
    (Lp.stronglyMeasurable G).measurable (hGp.mono_exponent hpR') t).1
  have heq := c16_km_actual_covariance_of_requested_action hd Q
    (2 * ENNReal.ofReal pT) hq hqfin lam t P K l δ h0.le h1 hK hrequested T hrep
    F G (hGp.mono_exponent hpT') hend
  have hb := (hbound Q hQ lam h0 h1 P K hK hD A hA F G hFl hGl
    (hFp.mono_exponent hpD') (hGp.mono_exponent hpD') hmean t).2
  have hFnorm := ENNReal.toReal_mono hFp.eLpNorm_ne_top
    (eLpNorm_le_eLpNorm_of_exponent_le (f := (F : FieldPair d → ℂ)) hpD')
  have hGnorm := ENNReal.toReal_mono hGp.eLpNorm_ne_top
    (eLpNorm_le_eLpNorm_of_exponent_le (f := (G : FieldPair d → ℂ)) hpD')
  rw [hS.eq_forcedComplexEvolution, heq]
  exact hb.trans (mul_le_mul
    (mul_le_mul_of_nonneg_left hFnorm (mul_nonneg hC.le (Real.exp_pos _).le))
    hGnorm ENNReal.toReal_nonneg (by positivity))



def SmoothPositiveKmBound {d : ℕ} (hd : 2 ≤ d) (SD : StructuralData d)
    (l δ p c C lam₀ : ℝ) : Prop :=
    ∀ Q : EnvironmentLaw d SD.ellipticity SD.dependenceRange, HasSmoothBounds SD Q →
    ∀ (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1), lam ≤ lam₀ →
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
          Hm s * ∑' n : ℕ, q (j + 1 + n)


theorem smooth_positive_km_bound_mono {d : ℕ} (hd : 2 ≤ d) (SD : StructuralData d)
    {l δ p c C lam₀ p' c' C' lam₀' : ℝ}
    (hl : 0 < l) (hC : 0 ≤ C) (hpp : p ≤ p') (hcc : c' ≤ c)
    (hCC : C ≤ C') (hlam : lam₀' ≤ lam₀)
    (hb : SmoothPositiveKmBound hd SD l δ p c C lam₀) :
    SmoothPositiveKmBound hd SD l δ p' c' C' lam₀' := by
  intro Q hQ lam h₀ h₁ hlam' P K hK hD A hA F G hF hG hFp hGp hzero
  let := reducedLaw_probability Q
  have hpp' := ENNReal.ofReal_le_ofReal hpp
  have hNf := ENNReal.toReal_mono hFp.eLpNorm_ne_top
    (eLpNorm_le_eLpNorm_of_exponent_le (f := F) hpp')
  have hNg := ENNReal.toReal_mono hGp.eLpNorm_ne_top
    (eLpNorm_le_eLpNorm_of_exponent_le (f := G) hpp')
  have ha := hb Q hQ lam h₀ h₁ (hlam'.trans hlam) P K hK hD A hA F G hF hG
    (hFp.mono_exponent hpp') (hGp.mono_exponent hpp') hzero
  dsimp only at ha ⊢
  refine ⟨ha.1.trans ?_, ha.2.1, ha.2.2.1, ?_, ?_, ha.2.2.2.2.2⟩
  · exact mul_le_mul_of_nonneg_right hCC (by linarith only [hl, hA])
  · intro n
    apply (ha.2.2.2.1 n).trans
    have hm := sbxS4_exp_decay_product_mono C C' c c'
      (max 1 ⌈(A / l + 4) / 10⌉₊ : ℕ) n
      (eLpNorm F (ENNReal.ofReal p) (reducedLaw Q)).toReal 1
      (eLpNorm F (ENNReal.ofReal p') (reducedLaw Q)).toReal 1
      hC hCC hcc (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      ENNReal.toReal_nonneg zero_le_one hNf le_rfl
    simpa only [mul_one] using hm
  · intro t
    have ht := ha.2.2.2.2.1 t
    refine ⟨ht.1, ht.2.1, ht.2.2.1.trans ?_, ht.2.2.2.trans ?_⟩ <;>
      simpa only [mul_assoc] using sbxS4_exp_decay_product_mono C C' c c'
        ((max 1 ⌈(A / l + 4) / 10⌉₊ : ℕ) + (max 1 ⌈(A / l - 1) / 10⌉₊ : ℕ) : ℝ)
        (lam ^ 2 * (t : ℝ))
        (eLpNorm F (ENNReal.ofReal p) (reducedLaw Q)).toReal
        (eLpNorm G (ENNReal.ofReal p) (reducedLaw Q)).toReal
        (eLpNorm F (ENNReal.ofReal p') (reducedLaw Q)).toReal
        (eLpNorm G (ENNReal.ofReal p') (reducedLaw Q)).toReal
        hC hCC hcc (by positivity) (by positivity)
        ENNReal.toReal_nonneg ENNReal.toReal_nonneg hNf hNg



/-- Conditional smooth k/m decomposition from the graph inputs and smooth coupling. -/
theorem kmDecompSmooth_of_deps
    (hcoupling : couplingNonreturnSmoothStmt)
    (hfactor : node_rt_u3A_k_u2D_factorStmt)
    (hphase : phaseErrorSmoothStmt)
    (hmany : node_rt_u3A_many_u2D_cycle_u2D_momentStmt)
    (htail : node_app_u3A_regen_u2D_tailsStmt)
    (hreal : node_e_u3A_generators_u23_real_u2D_semigroupStmtV2) :
    kmDecompSmoothStmt := by
  have hrem := node_rt_u3A_remainder_u2D_moment_of_depsV3 htail hreal
  have hact := gmpReducedKernelActionSmooth_of_real hreal
  intro d hd D
  obtain ⟨L, hL, hsepL, hcoupling⟩ := hcoupling d hd D
  obtain ⟨lD, hlD, hsepD, hdecay⟩ :=
    smooth_c16_km_positive_covariance_of_requested_action hfactor hphase hmany hrem d hd D
  obtain ⟨lK, hlK, hsepK, hkm⟩ :=
    smooth_sbxS2_positive_km_decomp_of_deps hfactor hphase hmany hrem d hd D
  refine ⟨max lK (max L lD), hlK.trans_le (le_max_left _ _),
    hsepK.trans_le (by linarith only [le_max_left lK (max L lD)]), ?_⟩
  intro l hl δ hδ0 hδ1
  have hlK' : lK ≤ l := (le_max_left _ _).trans hl
  have hlL : L ≤ l := (le_max_left _ _).trans ((le_max_right _ _).trans hl)
  have hlD' : lD ≤ l := (le_max_right _ _).trans ((le_max_right _ _).trans hl)
  obtain ⟨δa, lamc, hδa0, hδa1, hlamc, hlamc1, hexists⟩ := hcoupling l hlL
  obtain ⟨pD, cD, CD, hpD, hcD, hCD, hcov⟩ := hdecay l hlD' δa hδa0 hδa1
  obtain ⟨pK, cK, CK, lamK, hpK, hcK, hCK, hlamK, hlamK1, hk⟩ :=
    hkm l hlK' δ hδ0 hδ1
  have hk' : SmoothPositiveKmBound hd D l δ pK cK CK lamK := hk
  let p := max pK pD
  let c := min cK cD
  let C := max CK CD
  let lam₀ := min lamK lamc
  have hpositive : ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange),
      HasSmoothBounds D Q → ∀ (lam : ℝ), 0 < lam → lam ≤ lamc →
      ∀ S : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      IsComplexEnvironmentSemigroup Q (Regeneration.Renewal.forceCoord hd) (lam : ℂ) S →
      ∀ A : ℝ, l ≤ A → ∀ F G : Lp ℂ 2 (reducedLaw Q),
      IsRealLocalObservation Q (A / lam) F → IsRealLocalObservation Q (A / lam) G →
      MemLp (F : FieldPair d → ℂ) (ENNReal.ofReal pD) (reducedLaw Q) →
      MemLp (G : FieldPair d → ℂ) (ENNReal.ofReal pD) (reducedLaw Q) →
      (∫ ω, F ω ∂reducedLaw Q) = 0 → ∀ t : ℝ≥0,
      ‖∫ ω, F ω * S t G ω ∂reducedLaw Q‖ ≤
        CD * Real.exp (CD * A - cD * lam ^ 2 * (t : ℝ)) *
          (eLpNorm (F : FieldPair d → ℂ) (ENNReal.ofReal pD) (reducedLaw Q)).toReal *
          (eLpNorm (G : FieldPair d → ℂ) (ENNReal.ofReal pD) (reducedLaw Q)).toReal := by
    intro Q hQ lam h0 hle S hS A hA F G hF hG hFp hGp hzero t
    letI := reducedLaw_probability Q
    have h1 : lam ≤ 1 := hle.trans hlamc1
    obtain ⟨P, K, hK, hD⟩ := hexists Q hQ lam h0 h1 hle
    have hrequested : (∀ᵐ ω ∂Q.measure, SolvesMartingaleProblem
        (reducedGenerator (Regeneration.Renewal.forceCoord hd) ω lam) 0 (P (0, ω))) →
        ∀ (t : ℝ≥0) (f : BoundedContinuousFunction (FieldPair d) ℂ),
        (fun ω => ∫ γ : Path d, f (translate (γ t) (reduce ω)) ∂P (0, ω)) =ᵐ[Q.measure]
          fun ω => forcedComplexEvolution Q (Regeneration.Renewal.forceCoord hd)
            (lam : ℂ) t (BoundedContinuousFunction.toLp 2 (reducedLaw Q) ℂ f) (reduce ω) := by
      intro _ t f
      let F := BoundedContinuousFunction.toLp 2 (reducedLaw Q) ℂ f
      filter_upwards [hact d hd D Q hQ lam h0.le h1 P hK.2.2.1 t F,
        SbxS4Dynkin.ae_eq_at_supplied_endpoint hd Q lam h0.le h1 P hK.2.2.1 t
          (Lp.stronglyMeasurable F).measurable f.continuous.measurable
          (BoundedContinuousFunction.coeFn_toLp 2 (reducedLaw Q) ℂ f)] with ω hω hF
      calc ∫ γ : Path d, f (translate (γ t) (reduce ω)) ∂P (0, ω)
          = ∫ γ : Path d, F (translate (γ t) (reduce ω)) ∂P (0, ω) :=
            integral_congr_ae (hF.mono fun _ h => h.symm)
        _ = _ := hω.2.symm
    exact hcov Q hQ lam h0 h1 P K hK hD hrequested S hS A hA F G hF hG hFp hGp hzero t
  have hsigned := smooth_positive_covariance_bound_mono_signed D
    (Regeneration.Renewal.forceCoord hd)
    (l := l) (p := pD) (c := cD) (C := CD) (lam₀ := lamc)
    (p' := p) (c' := c) (C' := C) (lam₀' := lam₀)
    (hlK.trans_le hlK') hCD.le (le_max_right _ _) (min_le_right _ _)
    (le_max_right _ _) (min_le_right _ _) hpositive
  have hkm' := smooth_positive_km_bound_mono hd D (p' := p) (c' := c) (C' := C)
    (lam₀' := lam₀) (hlK.trans_le hlK') hCK.le
    (le_max_left _ _) (min_le_left _ _) (le_max_left _ _) (min_le_left _ _) hk'
  refine ⟨p, c, C, lam₀, hpK.trans (le_max_left _ _), lt_min hcK hcD,
    hCK.trans_le (le_max_left _ _), lt_min hlamK hlamc,
    (min_le_left _ _).trans hlamK1, ?_⟩
  intro Q hQ
  exact ⟨hkm' Q hQ, hsigned Q hQ⟩


end EinsteinFull.Blueprint.SbxS5Section3R01
