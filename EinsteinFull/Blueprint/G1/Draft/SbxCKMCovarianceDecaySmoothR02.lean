import EinsteinFull.Blueprint.G1.Draft.SbxCKMCenteredSlicesSmoothR01
import EinsteinFull.Blueprint.G1.Draft.SbxS5KMSmoothR01

/-! Conditional smooth-law covariance decay. This is draft support, not an adopted reduction. -/
open MeasureTheory
open scoped NNReal ENNReal Topology
noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local instance 2000] EinsteinRelation.instMeasurableSpaceMat
namespace EinsteinFull.Blueprint.SbxCKMCovarianceDecaySmoothR02
open EinsteinRelation
open EinsteinFull.Work.W5

/-- The full centered covariance identity, restricted to smooth laws. -/
def centeredCovarianceInputStmt : Prop :=
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
        Hm s * ∑' n : ℕ, q (j + 1 + n)

/-- Smooth covariance decay from the centered identity, cycle moments and phase estimate. -/
theorem covariance_sub_remainder_decay_from_smooth_inputs
    (hcenter : centeredCovarianceInputStmt)
    (hmany : SbxCKMCenteredSlicesSmoothR01.centeredManyCycleSmoothStmt)
    (hphase : SbxS5Section3R01.phaseErrorSmoothStmt) :
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
    hcenter d hd SD
  obtain ⟨lM, _hlM, _hsepM, hdecay⟩ :=
    SbxCKMCenteredSlicesSmoothR01.smooth_slice_decay_of_manyCycleMoment hmany d hd SD
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
        hqd Q hQ lam h₀ h₁ P K hK hD p (hpD.trans (le_max_left _ _)) F
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

end EinsteinFull.Blueprint.SbxCKMCovarianceDecaySmoothR02
