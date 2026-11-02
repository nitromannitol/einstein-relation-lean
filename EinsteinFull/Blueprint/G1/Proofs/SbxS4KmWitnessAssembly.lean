import EinsteinFull.Blueprint.G1.Proofs.SbxS4KmPathIdentification
import EinsteinFull.Blueprint.G1.Proofs.SbxS10KmReflection
import Mathlib.Tactic.Linter.Lint

/-!
Common structural witnesses for the two actual positive-force estimates used by
`rt:km-decomp`. The regeneration and path estimates retain their literal laws
and observations. No coupling existence or canonical semigroup identification
is asserted here. The auxiliary splitting parameter is selected before the law.
-/

open MeasureTheory
open scoped NNReal ENNReal

namespace EinsteinFull.Blueprint
open EinsteinRelation

/-- The literal positive-force regeneration conjunct, with fixed witnesses. -/
def SbxS4PositiveKmBound {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
    (l δ p c C lam₀ : ℝ) : Prop :=
    ∀ Q : EnvironmentLaw d Λ₀ r₀,
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

/-- The actual integrable complex path covariance bound at fixed witnesses. -/
def SbxS4PositivePathBound {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
    (l δ p c C : ℝ) : Prop :=
    ∀ (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
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
        (eLpNorm (G : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q)).toReal

/-- Simultaneously enlarge the prefactor, spatial growth and moment bounds,
while reducing the decay rate. The time and spatial quantities stay nonnegative. -/
theorem sbxS4_exp_decay_product_mono (C D c e N t X Y U V : ℝ)
    (hC : 0 ≤ C) (hCD : C ≤ D) (hec : e ≤ c) (hN : 0 ≤ N) (ht : 0 ≤ t)
    (hX : 0 ≤ X) (hY : 0 ≤ Y) (hXU : X ≤ U) (hYV : Y ≤ V) :
    C * Real.exp (C * N - c * t) * X * Y ≤
      D * Real.exp (D * N - e * t) * U * V := by
  have hU := hX.trans hXU
  have hV := hY.trans hYV
  apply (sbxS2_exp_decay_product_mono C D c e N t X Y U V
    hC hCD hec hN ht hX hY hXU hYV).trans
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hCD (Real.exp_pos _).le) hU) hV

/-- Moment promotion, rate reduction and cutoff restriction preserve every
identity and bound in the literal regeneration conjunction. -/
theorem sbxS4_positive_km_bound_mono {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
    {l δ p c C lam₀ p' c' C' lam₀' : ℝ}
    (hl : 0 < l) (hC : 0 ≤ C) (hpp : p ≤ p') (hcc : c' ≤ c)
    (hCC : C ≤ C') (hlam : lam₀' ≤ lam₀)
    (hb : SbxS4PositiveKmBound (Λ₀ := Λ₀) (r₀ := r₀) hd l δ p c C lam₀) :
    SbxS4PositiveKmBound (Λ₀ := Λ₀) (r₀ := r₀) hd l δ p' c' C' lam₀' := by
  intro Q lam h₀ h₁ hlam' P K hK hD A hA F G hF hG hFp hGp hzero
  let := reducedLaw_probability Q
  have hpp' := ENNReal.ofReal_le_ofReal hpp
  have hNf := ENNReal.toReal_mono hFp.eLpNorm_ne_top
    (eLpNorm_le_eLpNorm_of_exponent_le (f := F) hpp')
  have hNg := ENNReal.toReal_mono hGp.eLpNorm_ne_top
    (eLpNorm_le_eLpNorm_of_exponent_le (f := G) hpp')
  have ha := hb Q lam h₀ h₁ (hlam'.trans hlam) P K hK hD A hA F G hF hG
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

/-- Moment promotion and exponential monotonicity preserve genuine path
integrability and the literal complex covariance estimate. -/
theorem sbxS4_positive_path_bound_mono {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
    {l δ p c C p' c' C' : ℝ}
    (hl : 0 < l) (hC : 0 ≤ C) (hpp : p ≤ p') (hcc : c' ≤ c) (hCC : C ≤ C')
    (hb : SbxS4PositivePathBound (Λ₀ := Λ₀) (r₀ := r₀) hd l δ p c C) :
    SbxS4PositivePathBound (Λ₀ := Λ₀) (r₀ := r₀) hd l δ p' c' C' := by
  intro Q lam h₀ h₁ P K hK hD A hA F G hF hG hFp hGp hzero t
  let := reducedLaw_probability Q
  have hpp' := ENNReal.ofReal_le_ofReal hpp
  have hNf := ENNReal.toReal_mono hFp.eLpNorm_ne_top
    (eLpNorm_le_eLpNorm_of_exponent_le (f := (F : FieldPair d → ℂ)) hpp')
  have hNg := ENNReal.toReal_mono hGp.eLpNorm_ne_top
    (eLpNorm_le_eLpNorm_of_exponent_le (f := (G : FieldPair d → ℂ)) hpp')
  have ha := hb Q lam h₀ h₁ P K hK hD A hA F G hF hG
    (hFp.mono_exponent hpp') (hGp.mono_exponent hpp') hzero t
  refine ⟨ha.1, ha.2.trans ?_⟩
  simpa only [mul_assoc] using sbxS4_exp_decay_product_mono C C' c c' A
    (lam ^ 2 * (t : ℝ))
    (eLpNorm (F : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q)).toReal
    (eLpNorm (G : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q)).toReal
    (eLpNorm (F : FieldPair d → ℂ) (ENNReal.ofReal p') (reducedLaw Q)).toReal
    (eLpNorm (G : FieldPair d → ℂ) (ENNReal.ofReal p') (reducedLaw Q)).toReal
    hC hCC hcc (hl.le.trans hA) (by positivity)
    ENNReal.toReal_nonneg ENNReal.toReal_nonneg hNf hNg

/-- One structural threshold and one tuple of witnesses serve the complete
regeneration conjunction and the integrable complex path bound. The auxiliary
splitting parameter may differ from the target splitting parameter and is fixed
before the witnesses, law, force, radius and observations. This is support for
`rt:km-decomp`, with exactly its four graph inputs, rather than its reduction. -/
theorem sbxS4_common_positive_witnesses_of_deps
    (hfactor : node_rt_u3A_k_u2D_factorStmt)
    (hphase : node_rt_u3A_local_u2D_mixing_u23_phase_u2D_errorStmt)
    (hmany : node_rt_u3A_many_u2D_cycle_u2D_momentStmt)
    (hrem : node_rt_u3A_remainder_u2D_momentStmt) :
    ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ),
    ∃ l₀ : ℝ, 0 < l₀ ∧ r₀ < 2 * l₀ ∧
    ∀ l : ℝ, l₀ ≤ l → ∀ δ : ℝ, 0 < δ → δ < 1 →
    ∀ δa : ℝ, 0 < δa → δa < 1 →
    ∃ p c C lam₀ : ℝ, 2 ≤ p ∧ 0 < c ∧ 0 < C ∧ 0 < lam₀ ∧ lam₀ ≤ 1 ∧
      SbxS4PositiveKmBound (Λ₀ := Λ₀) (r₀ := r₀) hd l δ p c C lam₀ ∧
      SbxS4PositivePathBound (Λ₀ := Λ₀) (r₀ := r₀) hd l δa p c C := by
  intro d hd Λ₀ r₀
  obtain ⟨lK, hlK, hsepK, hkm⟩ :=
    sbxS2_positive_km_decomp_of_deps hfactor hphase hmany hrem d hd Λ₀ r₀
  obtain ⟨lP, _hlP, _hsepP, hpath⟩ :=
    sbxS4_positive_complex_integrable_covariance_of_deps hfactor hphase hmany hrem
      d hd Λ₀ r₀
  refine ⟨max lK lP, hlK.trans_le (le_max_left _ _),
    hsepK.trans_le (by linarith only [le_max_left lK lP]), ?_⟩
  intro l hl δ hδ₀ hδ₁ δa hδa₀ hδa₁
  have hlK' := (le_max_left lK lP).trans hl
  have hlP' := (le_max_right lK lP).trans hl
  have hlpos := hlK.trans_le hlK'
  obtain ⟨pK, cK, CK, lamK, hpK, hcK, hCK, hlamK, hlamK1, hK⟩ :=
    hkm l hlK' δ hδ₀ hδ₁
  obtain ⟨pP, cP, CP, _hpP, hcP, hCP, hP⟩ := hpath l hlP' δa hδa₀ hδa₁
  let C := 1 + CK + CP
  have hC : 0 < C := by dsimp only [C]; positivity
  have hKC : CK ≤ C := by dsimp only [C]; linarith only [hCP]
  have hPC : CP ≤ C := by dsimp only [C]; linarith only [hCK]
  refine ⟨max pK pP, min cK cP, C, lamK,
    hpK.trans (le_max_left _ _), lt_min hcK hcP, hC, hlamK, hlamK1, ?_, ?_⟩
  · exact sbxS4_positive_km_bound_mono hd hlpos hCK.le (le_max_left _ _)
      (min_le_left _ _) hKC le_rfl hK
  · exact sbxS4_positive_path_bound_mono hd hlpos hCP.le (le_max_right _ _)
      (min_le_right _ _) hPC hP

/-- A uniform positive-force semigroup estimate can use promoted moments,
a smaller rate and cutoff, and a larger growth constant for both force signs.
Reflection transports the actual law and keeps the radius `A / |lam|` exact.
This estimate transformer supplies no path-to-semigroup identification. -/
theorem sbxS4_positive_covariance_bound_mono_signed
    {d : ℕ} {Λ r₀ : ℝ} (i : Fin d) {l p c C lam₀ p' c' C' lam₀' : ℝ}
    (hl : 0 < l) (hC : 0 ≤ C) (hpp : p ≤ p') (hcc : c' ≤ c)
    (hCC : C ≤ C') (hlam : lam₀' ≤ lam₀)
    (hpositive : (∀ (Q : EnvironmentLaw d Λ r₀) (lam : ℝ), 0 < lam → lam ≤ lam₀ →
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
    (∀ (Q : EnvironmentLaw d Λ r₀) (lam : ℝ), 0 < |lam| → |lam| ≤ lam₀' →
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
  apply (EinsteinFull.SbxS10KmReflection.positive_covariance_bound_iff_signed
    i l p' c' C' lam₀').mp
  intro Q lam h₀ hlam' S hS A hA F G hF hG hFp hGp hzero t
  let := reducedLaw_probability Q
  have hpp' := ENNReal.ofReal_le_ofReal hpp
  have hNf := ENNReal.toReal_mono hFp.eLpNorm_ne_top
    (eLpNorm_le_eLpNorm_of_exponent_le (f := (F : FieldPair d → ℂ)) hpp')
  have hNg := ENNReal.toReal_mono hGp.eLpNorm_ne_top
    (eLpNorm_le_eLpNorm_of_exponent_le (f := (G : FieldPair d → ℂ)) hpp')
  have hb := hpositive Q lam h₀ (hlam'.trans hlam) S hS A hA F G hF hG
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

/-- The exact frozen statement is equivalent to its uniform positive-force
form, using the same structural and analytic witnesses in both conjuncts.
Only reflection of the actual joint law is used; no coupling is manufactured
and no path covariance is identified with the canonical evolution. -/
theorem sbxS4_km_decomp_iff_positive :
    node_rt_u3A_km_u2D_decompStmt ↔
    (∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ),
    ∃ l₀ : ℝ, 0 < l₀ ∧ r₀ < 2 * l₀ ∧
    ∀ l : ℝ, l₀ ≤ l → ∀ δ : ℝ, 0 < δ → δ < 1 →
    ∃ p c C lam₀ : ℝ, 2 ≤ p ∧ 0 < c ∧ 0 < C ∧ 0 < lam₀ ∧ lam₀ ≤ 1 ∧
      SbxS4PositiveKmBound (Λ₀ := Λ₀) (r₀ := r₀) hd l δ p c C lam₀ ∧
      (∀ (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ), 0 < lam → lam ≤ lam₀ →
      ∀ S : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      IsComplexEnvironmentSemigroup Q (Regeneration.Renewal.forceCoord hd) (lam : ℂ) S →
      ∀ A : ℝ, l ≤ A → ∀ F G : Lp ℂ 2 (reducedLaw Q),
      IsRealLocalObservation Q (A / lam) F →
      IsRealLocalObservation Q (A / lam) G →
      MemLp (F : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q) →
      MemLp (G : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q) →
      (∫ ω, F ω ∂reducedLaw Q) = 0 → ∀ t : ℝ≥0,
      ‖∫ ω, F ω * S t G ω ∂reducedLaw Q‖ ≤
        C * Real.exp (C * A - c * lam ^ 2 * (t : ℝ)) *
          (eLpNorm (F : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q)).toReal *
          (eLpNorm (G : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q)).toReal)) := by
  constructor
  · intro h d hd Λ₀ r₀
    obtain ⟨l₀, hl₀, hsep, hb⟩ := h d hd Λ₀ r₀
    refine ⟨l₀, hl₀, hsep, ?_⟩
    intro l hl δ hδ₀ hδ₁
    obtain ⟨p, c, C, lam₀, hp, hc, hC, hlam₀, hlam₁, hQ⟩ := hb l hl δ hδ₀ hδ₁
    refine ⟨p, c, C, lam₀, hp, hc, hC, hlam₀, hlam₁, ?_, ?_⟩
    · exact fun Q => (hQ Q).1
    · exact (EinsteinFull.SbxS10KmReflection.positive_covariance_bound_iff_signed
        (Regeneration.Renewal.forceCoord hd) l p c C lam₀).mpr (fun Q => (hQ Q).2)
  · intro h d hd Λ₀ r₀
    obtain ⟨l₀, hl₀, hsep, hb⟩ := h d hd Λ₀ r₀
    refine ⟨l₀, hl₀, hsep, ?_⟩
    intro l hl δ hδ₀ hδ₁
    obtain ⟨p, c, C, lam₀, hp, hc, hC, hlam₀, hlam₁, hkm, hpositive⟩ :=
      hb l hl δ hδ₀ hδ₁
    refine ⟨p, c, C, lam₀, hp, hc, hC, hlam₀, hlam₁, ?_⟩
    intro Q
    exact ⟨hkm Q,
      (EinsteinFull.SbxS10KmReflection.positive_covariance_bound_iff_signed
        (Regeneration.Renewal.forceCoord hd) l p c C lam₀).mp hpositive Q⟩

/-- The shared positive witnesses can satisfy additional structural, moment,
rate, growth and force-cutoff requirements selected before the law. These
numerical parameters can accommodate restrictions of a future identification
proof without assuming any identification or existence of a coupling. -/
theorem sbxS4_common_positive_witnesses_with_constraints_of_deps
    (hfactor : node_rt_u3A_k_u2D_factorStmt)
    (hphase : node_rt_u3A_local_u2D_mixing_u23_phase_u2D_errorStmt)
    (hmany : node_rt_u3A_many_u2D_cycle_u2D_momentStmt)
    (hrem : node_rt_u3A_remainder_u2D_momentStmt) :
    ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ L : ℝ),
    ∃ l₀ : ℝ, 0 < l₀ ∧ r₀ < 2 * l₀ ∧ L ≤ l₀ ∧
    ∀ l : ℝ, l₀ ≤ l → ∀ δ : ℝ, 0 < δ → δ < 1 →
    ∀ δa : ℝ, 0 < δa → δa < 1 →
    ∀ (pmin cmax Cmin η : ℝ), 0 < cmax → 0 < η →
    ∃ p c C lam₀ : ℝ,
      2 ≤ p ∧ pmin ≤ p ∧ 0 < c ∧ c ≤ cmax ∧ 0 < C ∧ Cmin ≤ C ∧
      0 < lam₀ ∧ lam₀ ≤ 1 ∧ lam₀ ≤ η ∧
      SbxS4PositiveKmBound (Λ₀ := Λ₀) (r₀ := r₀) hd l δ p c C lam₀ ∧
      SbxS4PositivePathBound (Λ₀ := Λ₀) (r₀ := r₀) hd l δa p c C := by
  intro d hd Λ₀ r₀ L
  obtain ⟨lB, hlB, hsepB, hb⟩ :=
    sbxS4_common_positive_witnesses_of_deps hfactor hphase hmany hrem d hd Λ₀ r₀
  refine ⟨max lB L, hlB.trans_le (le_max_left _ _),
    hsepB.trans_le (by linarith only [le_max_left lB L]), le_max_right _ _, ?_⟩
  intro l hl δ hδ₀ hδ₁ δa hδa₀ hδa₁ pmin cmax Cmin η hcmax hη
  have hlB' := (le_max_left lB L).trans hl
  have hlpos := hlB.trans_le hlB'
  obtain ⟨pB, cB, CB, lamB, hpB, hcB, hCB, hlamB, hlamB1, hkm, hpath⟩ :=
    hb l hlB' δ hδ₀ hδ₁ δa hδa₀ hδa₁
  refine ⟨max pB pmin, min cB cmax, max CB Cmin, min lamB η,
    hpB.trans (le_max_left _ _), le_max_right _ _, lt_min hcB hcmax,
    min_le_right _ _, hCB.trans_le (le_max_left _ _), le_max_right _ _,
    lt_min hlamB hη, (min_le_left _ _).trans hlamB1, min_le_right _ _, ?_, ?_⟩
  · exact sbxS4_positive_km_bound_mono hd hlpos hCB.le (le_max_left _ _)
      (min_le_left _ _) (le_max_left _ _) (min_le_left _ _) hkm
  · exact sbxS4_positive_path_bound_mono hd hlpos hCB.le (le_max_left _ _)
      (min_le_left _ _) (le_max_left _ _) hpath

#print axioms SbxS4PositiveKmBound
#print axioms SbxS4PositivePathBound
#print axioms sbxS4_exp_decay_product_mono
#print axioms sbxS4_positive_km_bound_mono
#print axioms sbxS4_positive_path_bound_mono
#print axioms sbxS4_common_positive_witnesses_of_deps
#print axioms sbxS4_positive_covariance_bound_mono_signed
#print axioms sbxS4_km_decomp_iff_positive
#print axioms sbxS4_common_positive_witnesses_with_constraints_of_deps

end EinsteinFull.Blueprint

#lint
