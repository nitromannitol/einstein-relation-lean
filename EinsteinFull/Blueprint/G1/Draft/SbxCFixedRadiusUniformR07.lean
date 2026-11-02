import EinsteinFull.Blueprint.G1.Draft.SbxCFixedRadiusRootR02
import EinsteinFull.Blueprint.Roots.Draft.SbxCRenewalUniformR06

/-! Draft fixed-radius uniform contracts and conditional assembly. -/
open MeasureTheory
open scoped NNReal ENNReal Topology
namespace EinsteinFull.Blueprint.SbxCFixedRadiusUniformR07
open EinsteinRelation EinsteinFull.Blueprint

def fixedScalarUniformInputStmt : Prop :=
    ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ) (hΛ : 1 ≤ Λ₀) (hr : 1 ≤ r₀),
    ∃ l₀ : ℝ, 0 < l₀ ∧ r₀ < 2 * l₀ ∧
    ∀ l : ℝ, l₀ ≤ l → ∀ δ : ℝ, 0 < δ → δ < 1 →
    ∀ b : ℝ, 0 < b →
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    ∀ (β : ℕ → ℝ) (hβ : ∀ k, 1 ≤ k → 0 < β k),
    let D : StructuralData d := ⟨Λ₀, r₀, β, hΛ, hr, hβ⟩
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (_hQ : HasSmoothBounds D Q) (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
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
      |hF j| ≤ C * (Rf + Bq * R) * Real.exp (-c * j)

def fixedObservationsUniformInputStmt : Prop :=
    ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ) (hΛ : 1 ≤ Λ₀) (hr : 1 ≤ r₀),
    ∃ l₀ : ℝ, 0 < l₀ ∧ r₀ < 2 * l₀ ∧
    ∀ l : ℝ, l₀ ≤ l → ∀ δ : ℝ, 0 < δ → δ < 1 →
    ∃ p c C : ℝ, 2 ≤ p ∧ 0 < c ∧ 0 < C ∧
    ∀ (β : ℕ → ℝ) (hβ : ∀ k, 1 ≤ k → 0 < β k),
    let SD : StructuralData d := ⟨Λ₀, r₀, β, hΛ, hr, hβ⟩
    ∀ (Q : EnvironmentLaw d SD.ellipticity SD.dependenceRange) (_hQ : HasSmoothBounds SD Q) (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
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
        |hF (s + k * Δ)| ≤ C * Real.exp (-c * k) * Nf * Ng

def fixedRadiusUniformStmtV3 : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ) (hΛ : 1 ≤ Λ₀) (hr : 1 ≤ r₀),
    ∃ l₀ : ℝ, 0 < l₀ ∧ r₀ < 2 * l₀ ∧
    ∀ l : ℝ, l₀ ≤ l → ∀ δ : ℝ, 0 < δ → δ < 1 →
    ∀ b : ℝ, 0 < b →
    ∃ p c C : ℝ, 2 ≤ p ∧ 0 < c ∧ 0 < C ∧
    ∀ (β : ℕ → ℝ) (hβ : ∀ k, 1 ≤ k → 0 < β k),
    let D : StructuralData d := ⟨Λ₀, r₀, β, hΛ, hr, hβ⟩
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (_hQ : HasSmoothBounds D Q) (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
      (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
      (hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K)
      (hD : Regeneration.annealedCoupledLaw Q.measure K
        (regenerationNoReturn hd (l / lam)) ≠ 0),
    (let Δ := Regeneration.Renewal.regenDelta lam
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
       |hF j| ≤ C * (Rf + Bq * R) * Real.exp (-c * j)) ∧
    (∀ F G : FieldPair d → ℝ,
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
        |hF (s + k * Δ)| ≤ C * Real.exp (-c * k) * Nf * Ng)


theorem fixedRadiusUniform_from_scalar_observations
    (hscalar : fixedScalarUniformInputStmt) (hobservations : fixedObservationsUniformInputStmt) :
    fixedRadiusUniformStmtV3 := by
  intro d hd Λ₀ r₀ hΛ hr
  obtain ⟨lS, hlS, hsepS, hscalar⟩ := hscalar d hd Λ₀ r₀ hΛ hr
  obtain ⟨lA, _hlA, _hsepA, hactual⟩ :=
    hobservations d hd Λ₀ r₀ hΛ hr
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
  intro β hβ D Q hQ lam h₀ h₁ P K hK hD
  constructor
  · dsimp only
    intro s hs h r hF rF q R Rf Bq hR hRf hBq hrec hrecF hr hrF hq hqs hqzero
    have hout := hscalar' β hβ Q hQ lam h₀ h₁ P K hK hD s hs h r hF rF q R Rf Bq
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
    have hout := hactual' β hβ Q hQ lam h₀ h₁ P K hK hD F G hF hG hFp hGp hzero
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

/-- The full scalar output follows from the canonical uniform renewal input. -/
theorem fixedScalarUniform_of_renewal
    (hren : SbxCRenewalUniformR06.renewalUniformStmt) : fixedScalarUniformInputStmt := by
  intro d hd Λ₀ r₀ hΛ hr
  obtain ⟨l₀, hl₀, hsep, hren'⟩ := hren d hd Λ₀ r₀ hΛ hr
  refine ⟨l₀, hl₀, hsep, ?_⟩
  intro l hl δ hδ₀ hδ₁ b hb
  obtain ⟨c₁, C₁, a, M, hc₁, hC₁, _, _, hdata⟩ := hren' l hl δ hδ₀ hδ₁
  obtain ⟨c, C, hc, hC, hscalar⟩ :=
    sbxS4_fixedRadius_scalar_uniform C₁ c₁ b hC₁ hc₁ hb
  refine ⟨c, C, hc, hC, ?_⟩
  intro β hβ D Q hQ lam h₀ h₁ P K hK hD
  let pn := regenerationLatticeMass hd Q lam l K hK.1 hD
  have hp : pn 0 = 0 :=
    regenerationLatticeMass_zero hd Q lam l h₀ (hl₀.trans_le hl) K hK.1 hD
  have hmean : (∑' n : ℕ, pn n * (n : ℝ)) = ∑' n : ℕ, (n : ℝ) * pn n :=
    tsum_congr (fun n => mul_comm _ _)
  have hU : ∀ n : ℕ, |(∑' j : ℕ, latticeConvolutionPower pn j n) -
      (∑' n : ℕ, (n : ℝ) * pn n)⁻¹| ≤ C₁ * Real.exp (-c₁ * n) := by
    have h := (hdata β hβ Q hQ lam h₀ h₁ P K hK hD).1
    change ∀ n : ℕ, |(∑' j : ℕ, latticeConvolutionPower pn j n) -
      (∑' n : ℕ, pn n * (n : ℝ))⁻¹| ≤ C₁ * Real.exp (-c₁ * n) at h
    rwa [hmean] at h
  dsimp only
  intro s _hs
  exact hscalar pn _ hp hU

end EinsteinFull.Blueprint.SbxCFixedRadiusUniformR07
