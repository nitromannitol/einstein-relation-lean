import EinsteinFull.Blueprint.G1.Draft.SbxCKMCenteredSlicesSmoothR01

/-! Conditional centered covariance from the literal decomposition and smooth slice moments.
These statements are draft support, not adopted reductions. -/
open MeasureTheory
open scoped NNReal ENNReal Topology
noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local instance 2000] EinsteinRelation.instMeasurableSpaceMat
namespace EinsteinFull.Blueprint.SbxCKMCenteredCovarianceSmoothR02
open EinsteinRelation
open EinsteinFull.Work.W5

/-- The full covariance decomposition, restricted to smooth laws. -/
def covarianceDecompositionInputStmt : Prop :=
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
          G (translate (ωz.2.1 (t - (n : ℝ≥0) * Δ)) (reduce ωz.1)) ∂ν

/-- Centering the covariance decomposition using the smooth many-cycle moment. -/
theorem centered_covariance_from_decomposition
    (hdecomp : covarianceDecompositionInputStmt)
    (hmany : SbxCKMCenteredSlicesSmoothR01.centeredManyCycleSmoothStmt) :
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
    hdecomp d hd SD
  obtain ⟨lM, _hlM, _hsepM, hCenter⟩ :=
    SbxCKMCenteredSlicesSmoothR01.smooth_centered_slices_of_manyCycleMoment hmany d hd SD
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
    hCenter l ((le_max_right _ _).trans hl) δ hδ₀ hδ₁ Q hQ lam h₀ h₁ P K hK hD p
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


end EinsteinFull.Blueprint.SbxCKMCenteredCovarianceSmoothR02
