import EinsteinFull.Calculus.SbxAKMAlgebraFromPredecessorsR10
import EinsteinFull.Calculus.SbxAKMMomentFromRemainderR09

/-! Uniform positive-force estimates from the four predecessor statements. -/
open MeasureTheory
open scoped NNReal ENNReal Topology
noncomputable section
namespace EinsteinFull.Blueprint.SbxAKMPositiveFromPredecessorsR10
open EinsteinRelation EinsteinFull.Work.W5
open EinsteinFull.Blueprint.SbxCKMCovarianceSmoothR01
open EinsteinFull.Blueprint.SbxS5Section3R01
open EinsteinFull.Blueprint.SbxCKMCovarianceDecaySmoothR02
open EinsteinFull.Blueprint.SbxAUniformKMAssemblerR07
open EinsteinFull.Blueprint.SbxAKMAlgebraFromPredecessorsR10
open EinsteinFull.Blueprint.SbxAKMMomentFromRemainderR09

theorem a_uniform_regeneration_remainder_decay_of_predecessors
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
  obtain ⟨lR, hlR, hsep, hrate⟩ := a_uniform_remainder_variable_rate_of_remainder hrem d hd Λ₀ r₀ hΛ hr
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


theorem a_uniform_covariance_sub_remainder_decay_of_predecessors
    (hfactor : node_rt_u3A_k_u2D_factorStmt)
    (hrem : node_rt_u3A_remainder_u2D_momentStmt)
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
    a_uniform_centered_covariance_of_exact_predecessors hfactor hrem hmany d hd Λ₀ r₀ hΛ hr
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



theorem a_uniform_covariance_sub_remainder_time_decay_of_predecessors
    (hfactor : node_rt_u3A_k_u2D_factorStmt)
    (hrem : node_rt_u3A_remainder_u2D_momentStmt)
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
    a_uniform_covariance_sub_remainder_decay_of_predecessors hfactor hrem hmany hphase d hd Λ₀ r₀ hΛ hr
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



theorem a_uniform_covariance_and_remainder_decay_of_predecessors
    (hfactor : node_rt_u3A_k_u2D_factorStmt)
    (hrem : node_rt_u3A_remainder_u2D_momentStmt)
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
    a_uniform_covariance_sub_remainder_time_decay_of_predecessors hfactor hrem hmany hphase d hd Λ₀ r₀ hΛ hr
  obtain ⟨lR, _hlR, _hsepR, hremdec⟩ :=
    a_uniform_regeneration_remainder_decay_of_predecessors hmany hrem d hd Λ₀ r₀ hΛ hr
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



theorem a_uniform_positiveKmFullRange_of_predecessors
    (hfactor : node_rt_u3A_k_u2D_factorStmt)
    (hrem : node_rt_u3A_remainder_u2D_momentStmt)
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
    a_uniform_centered_covariance_of_exact_predecessors hfactor hrem hmany d hd Λ₀ r₀ hΛ hr
  obtain ⟨lQ, _hlQ, _hsepQ, hslice⟩ :=
    uniform_slice_decay_normalized hmany d hd Λ₀ r₀ hΛ hr
  obtain ⟨lB, _hlB, _hsepB, hdecay⟩ :=
    a_uniform_covariance_and_remainder_decay_of_predecessors hfactor hrem hmany hphase d hd Λ₀ r₀ hΛ hr
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



theorem a_uniform_positiveKm_clause_of_exact_predecessors
    (hfactor : node_rt_u3A_k_u2D_factorStmt)
    (hphase : SbxCPhaseUniformR07.phaseUniformStmt)
    (hmany : SbxCManyCycleUniformR06.manyCycleSmoothStmt)
    (hrem : node_rt_u3A_remainder_u2D_momentStmt) :
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
    a_uniform_positiveKmFullRange_of_predecessors hfactor hrem hmany hphase d hd Λ₀ r₀ hΛ hr
  refine ⟨l₀, hl₀, hsep, ?_⟩
  intro l hl δ hδ₀ hδ₁
  obtain ⟨p, c, C, hp, hc, hC, hpositive⟩ := hbound l hl δ hδ₀ hδ₁
  refine ⟨p, c, C, hp, hc, hC, ?_⟩
  intro β hβ
  dsimp only
  intro Q hQ lam h₀ h₁
  exact hpositive β hβ Q hQ lam h₀ h₁ h₁



end EinsteinFull.Blueprint.SbxAKMPositiveFromPredecessorsR10

