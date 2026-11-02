import EinsteinFull.Blueprint.G1.Draft.S3SmoothScope
import EinsteinFull.Blueprint.G1.Proofs.SbxS4FixedRadius
import EinsteinFull.Blueprint.G1.Proofs.SbxS9PhaseError
import EinsteinFull.Blueprint.Roots.Proofs.W4Queue0345_2

/-! Draft smooth-law contracts and conditional consumers; not reviewed or adopted. -/
open MeasureTheory
open scoped NNReal ENNReal Topology
namespace EinsteinFull.Blueprint.SbxS6Section3R01
open EinsteinRelation EinsteinFull.Blueprint

def node_rt_u3A_local_u2D_mixing_u23_fixed_u2D_radiusStmtV3 : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d),
    ∃ l₀ : ℝ, 0 < l₀ ∧ D.dependenceRange < 2 * l₀ ∧
    ∀ l : ℝ, l₀ ≤ l → ∀ δ : ℝ, 0 < δ → δ < 1 →
    ∀ b : ℝ, 0 < b →
    ∃ p c C : ℝ, 2 ≤ p ∧ 0 < c ∧ 0 < C ∧
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


def node_rt_u3A_local_u2D_mixing_u23_phase_u2D_errorStmtV3 : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d),
    ∃ l₀ : ℝ, 0 < l₀ ∧ D.dependenceRange < 2 * l₀ ∧
    ∀ l : ℝ, l₀ ≤ l → ∀ δ : ℝ, 0 < δ → δ < 1 →
    ∃ p c C : ℝ, 2 ≤ p ∧ 0 < c ∧ 0 < C ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (_hQ : HasSmoothBounds D Q) (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
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


def node_rt_u3A_km_u2D_decompStmtV3 : Prop :=
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


def node_rt_u3A_local_u2D_mixingStmtV3 : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d),
    ∃ l p c C lam₀ : ℝ,
      0 < l ∧ D.dependenceRange < 2 * l ∧ 2 ≤ p ∧ 0 < c ∧ 0 < C ∧
      0 < lam₀ ∧ lam₀ ≤ 1 ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (_hQ : HasSmoothBounds D Q) (lam : ℝ),
      0 < |lam| → |lam| ≤ lam₀ →
    ∀ P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ (lam : ℂ) P →
    ∀ A : ℝ, l ≤ A → ∀ F G : Lp ℂ 2 (reducedLaw Q),
      IsRealLocalObservation Q (A / |lam|) F →
      IsRealLocalObservation Q (A / |lam|) G →
      MemLp (F : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q) →
      MemLp (G : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q) →
      (∫ ω, F ω ∂reducedLaw Q) = 0 → ∀ t : ℝ≥0,
      ‖∫ ω, F ω * P t G ω ∂reducedLaw Q‖ ≤
        C * Real.exp (C * A - c * lam ^ 2 * (t : ℝ)) *
          (eLpNorm (F : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q)).toReal *
          (eLpNorm (G : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q)).toReal


/-- Conditional on the literal smooth k/m decomposition, extract its signed-force clause. -/
theorem local_mixing_of_smooth_km
    (hkm : node_rt_u3A_km_u2D_decompStmtV3) :
    node_rt_u3A_local_u2D_mixingStmtV3 := by
  intro d hd D
  obtain ⟨l, hl, hr, hscale⟩ := hkm d hd D
  obtain ⟨p, c, C, lam₀, hp, hc, hC, hlam, hlam_one, hcov⟩ :=
    hscale l le_rfl (1 / 2) (by norm_num) (by norm_num)
  refine ⟨l, p, c, C, lam₀, hl, hr, hp, hc, hC, hlam, hlam_one, ?_⟩
  intro Q hQ lam hpos hsmall P hP
  exact (hcov Q hQ).2 lam hpos hsmall P hP


theorem smooth_covariance_power_moment
    (hrem : node_rt_u3A_remainder_u2D_momentStmtV3) :
    ∀ (d : ℕ) (hd : 2 ≤ d) (SD : StructuralData d),
    ∃ l₀ p C : ℝ, 0 < l₀ ∧ SD.dependenceRange < 2 * l₀ ∧ 2 ≤ p ∧ 0 < C ∧
    ∀ (r : ℝ), 0 < r →
    ∀ (Q : EnvironmentLaw d SD.ellipticity SD.dependenceRange) (_hQ : HasSmoothBounds SD Q) (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
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

theorem smooth_remainder_variable_rate_both
    (hrem : node_rt_u3A_remainder_u2D_momentStmtV3) :
    ∀ (d : ℕ) (hd : 2 ≤ d) (SD : StructuralData d),
    ∃ l₀ : ℝ, 0 < l₀ ∧ SD.dependenceRange < 2 * l₀ ∧
    ∀ a : ℝ, 0 < a → ∃ p c C : ℝ, 2 ≤ p ∧ 0 < c ∧ 0 < C ∧
    ∀ (Q : EnvironmentLaw d SD.ellipticity SD.dependenceRange) (_hQ : HasSmoothBounds SD Q) (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
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
  intro d hd SD
  obtain ⟨l₀, p₀, D, hl₀, hsep, hp₀, hDpos, hmoment⟩ :=
    smooth_covariance_power_moment hrem d hd SD
  refine ⟨l₀, hl₀, hsep, ?_⟩
  intro a ha
  obtain ⟨r, c, C, hr, hc, hC, hscalar⟩ :=
    sbxS2_power_interpolation_constants D a hDpos ha
  have hr₁ : 1 < r := lt_of_lt_of_le (by norm_num) hr
  have hr₀ : 0 < r := lt_trans zero_lt_one hr₁
  refine ⟨p₀ * r, c, C,
    hp₀.trans (le_mul_of_one_le_right (by linarith only [hp₀]) hr₁.le), hc, hC, ?_⟩
  intro Q hQ lam h₀ h₁ l δ hl hδ₀ hδ₁ P K hK hD F G hF hG hFp hGp J t E hJ μ hμ hprob
  let f := fun ωz : FieldPair d × Regeneration.CoupledSample d =>
    F (reduce ωz.1) * G (translate (ωz.2.1 t) (reduce ωz.1))
  have ht : Measurable (fun ωz : FieldPair d × Regeneration.CoupledSample d =>
      ωz.2.1 t) := (continuous_eval_const t).measurable.comp measurable_snd.fst
  have hred : Measurable (fun ωz : FieldPair d × Regeneration.CoupledSample d =>
      reduce ωz.1) := Probability.measurable_reduce.comp measurable_fst
  have hfm : Measurable f := (hF.comp hred).mul
    (hG.comp (Probability.continuous_translate.measurable.comp (ht.prodMk hred)))
  have hpower := hmoment r hr₀ Q hQ lam h₀ h₁ l δ hl hδ₀ hδ₁ P K hK hD
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

theorem smooth_translated_integrable
    (hrem : node_rt_u3A_remainder_u2D_momentStmtV3) :
    ∀ (d : ℕ) (hd : 2 ≤ d) (SD : StructuralData d),
    ∃ l₀ p : ℝ, 0 < l₀ ∧ SD.dependenceRange < 2 * l₀ ∧ 2 ≤ p ∧
    ∀ (Q : EnvironmentLaw d SD.ellipticity SD.dependenceRange) (_hQ : HasSmoothBounds SD Q) (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
      (l δ : ℝ), l₀ ≤ l → 0 < δ → δ < 1 →
    ∀ (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
      (hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K)
      (hD : Regeneration.annealedCoupledLaw Q.measure K
        (regenerationNoReturn hd (l / lam)) ≠ 0),
    ∀ G : FieldPair d → ℝ, Measurable G →
      MemLp G (ENNReal.ofReal p) (reducedLaw Q) → ∀ t : ℝ≥0,
    ∀ μ ∈ ({Regeneration.annealedCoupledLaw Q.measure K,
      regenerationConditionedLaw hd Q lam l K hK.1 hD} :
        Set (Measure (FieldPair d × Regeneration.CoupledSample d))),
      Integrable (fun ωz => G (translate (ωz.2.1 t) (reduce ωz.1))) μ := by
  intro d hd SD
  obtain ⟨l₀, p, c, C, hl₀, hsep, hp, _hc, _hC, hrem'⟩ :=
    hrem d hd SD 1 1 (by norm_num) (by norm_num)
  refine ⟨l₀, p, hl₀, hsep, hp, ?_⟩
  intro Q hQ lam h₀ h₁ l δ hl hδ₀ hδ₁ P K hK hD G hG hLp t μ hμ
  let : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  let : IsProbabilityMeasure (Regeneration.annealedCoupledLaw Q.measure K) :=
    Regeneration.annealedCoupledLaw_isProbabilityMeasure Q.measure K hK.1
  have hprob : Regeneration.annealedCoupledLaw Q.measure K Set.univ ≤
      ENNReal.ofReal (1 * Real.exp (1 * (lam ^ 2 * (t : ℝ)) -
        1 * lam ^ 2 * (t : ℝ))) := by simp
  have hint := (hrem' Q hQ lam h₀ h₁ l δ hl hδ₀ hδ₁ P K hK hD
    (fun _ => 1) G measurable_const hG (memLp_const 1) hLp
    (lam ^ 2 * (t : ℝ)) t Set.univ (mul_nonneg (sq_nonneg lam) t.coe_nonneg)
    MeasurableSet.univ hprob μ hμ).1
  simpa only [one_mul, integrableOn_univ] using hint

theorem smooth_m_renewal_eq_memLp
    (hmren : node_rt_u3A_m_u2D_renewalStmt)
    (hrem : node_rt_u3A_remainder_u2D_momentStmtV3) :
    ∀ (d : ℕ) (hd : 2 ≤ d) (SD : StructuralData d),
    ∃ l₀ p : ℝ, 0 < l₀ ∧ SD.dependenceRange < 2 * l₀ ∧ 2 ≤ p ∧
    ∀ (Q : EnvironmentLaw d SD.ellipticity SD.dependenceRange) (_hQ : HasSmoothBounds SD Q) (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
      (l δ : ℝ), l₀ ≤ l → 0 < δ → δ < 1 →
    ∀ (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
      (hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K)
      (hD : Regeneration.annealedCoupledLaw Q.measure K
        (regenerationNoReturn hd (l / lam)) ≠ 0)
      (A : ℝ) (m : ℕ), 1 ≤ m →
      10 * (m : ℝ) * l - l - A ≥ -2 * l →
    ∀ G : FieldPair d → ℝ,
      Measurable[localSigma {x : Vec d | euclideanNorm x < A / lam}] G →
      MemLp G (ENNReal.ofReal p) (reducedLaw Q) →
    let ν := regenerationConditionedLaw hd Q lam l K hK.1 hD
    let Δ := Regeneration.Renewal.regenDelta lam
    let pn := regenerationLatticeMass hd Q lam l K hK.1 hD
    let h := fun t : ℝ≥0 => ∫ ωz in
      {ωz | regenerationTime hd lam l m ωz.2 ≤ (t : ℝ≥0∞)},
      G (translate (ωz.2.1 t) (reduce ωz.1)) ∂ν
    let r := fun t : ℝ≥0 => ∫ ωz in
      {ωz | regenerationTime hd lam l m ωz.2 ≤ (t : ℝ≥0∞) ∧
        (t : ℝ≥0∞) < regenerationTime hd lam l (m + 1) ωz.2},
      G (translate (ωz.2.1 t) (reduce ωz.1)) ∂ν
    ∀ t : ℝ≥0, h t = r t +
      ∑ n ∈ Finset.range (⌊(t : ℝ) / (Δ : ℝ)⌋₊ + 1), pn n * h (t - n * Δ) := by
  intro d hd SD
  obtain ⟨l₀, p, hl₀, hsep, hp, hInt⟩ :=
    smooth_translated_integrable hrem d hd SD
  refine ⟨l₀, p, hl₀, hsep, hp, ?_⟩
  intro Q hQ lam h₀ h₁ l δ hl hδ₀ hδ₁ P K hK hD A m hm hs G hG hLp
  let ν := regenerationConditionedLaw hd Q lam l K hK.1 hD
  let Δ := Regeneration.Renewal.regenDelta lam
  let pn := regenerationLatticeMass hd Q lam l K hK.1 hD
  let H := fun (F : FieldPair d → ℝ) (t : ℝ≥0) => ∫ ωz in
    {ωz | regenerationTime hd lam l m ωz.2 ≤ (t : ℝ≥0∞)},
    F (translate (ωz.2.1 t) (reduce ωz.1)) ∂ν
  let R := fun (F : FieldPair d → ℝ) (t : ℝ≥0) => ∫ ωz in
    {ωz | regenerationTime hd lam l m ωz.2 ≤ (t : ℝ≥0∞) ∧
      (t : ℝ≥0∞) < regenerationTime hd lam l (m + 1) ωz.2},
    F (translate (ωz.2.1 t) (reduce ωz.1)) ∂ν
  let Gk := fun (n : ℕ) (ω : FieldPair d) => max (-(n : ℝ)) (min (n : ℝ) (G ω))
  have hGk (n : ℕ) :
      Measurable[localSigma {x : Vec d | euclideanNorm x < A / lam}] (Gk n) :=
    measurable_const.max (measurable_const.min hG)
  have hb (n : ℕ) : Regeneration.BoundedRealTest (Gk n) := by
    refine ⟨(n : ℝ), fun ω => abs_le.mpr ⟨le_max_left _ _, ?_⟩⟩
    exact max_le
      ((neg_nonpos.mpr (Nat.cast_nonneg n)).trans (Nat.cast_nonneg n)) (min_le_left _ _)
  have hi (t : ℝ≥0) :
      Integrable (fun ωz => G (translate (ωz.2.1 t) (reduce ωz.1))) ν :=
    hInt Q hQ lam h₀ h₁ l δ hl hδ₀ hδ₁ P K hK hD G
      (hG.mono (Probability.localSigma_le_borel _) le_rfl) hLp t ν (by simp [ν])
  have hH (t : ℝ≥0) : Filter.Tendsto (fun n => H (Gk n) t)
      Filter.atTop (𝓝 (H G t)) :=
    tendsto_setIntegral_clamp ν _ (hi t) _
  have hR (t : ℝ≥0) : Filter.Tendsto (fun n => R (Gk n) t)
      Filter.atTop (𝓝 (R G t)) :=
    tendsto_setIntegral_clamp ν _ (hi t) _
  change ∀ t, H G t = R G t +
    ∑ n ∈ Finset.range (⌊(t : ℝ) / (Δ : ℝ)⌋₊ + 1), pn n * H G (t - n * Δ)
  intro t
  have heq (n : ℕ) : H (Gk n) t = R (Gk n) t +
      ∑ k ∈ Finset.range (⌊(t : ℝ) / (Δ : ℝ)⌋₊ + 1),
        pn k * H (Gk n) (t - k * Δ) :=
    m_renewal_eq_of_support hmren d hd SD.ellipticity SD.dependenceRange l δ (hl₀.trans_le hl)
      (hsep.trans_le (by linarith)) hδ₀ hδ₁ Q lam h₀ h₁ P K hK hD A m hm hs
      (Gk n) (hGk n) (hb n) t
  have hsum : Filter.Tendsto
      (fun n : ℕ => ∑ k ∈ Finset.range (⌊(t : ℝ) / (Δ : ℝ)⌋₊ + 1),
        pn k * H (Gk n) (t - k * Δ)) Filter.atTop
      (𝓝 (∑ k ∈ Finset.range (⌊(t : ℝ) / (Δ : ℝ)⌋₊ + 1),
        pn k * H G (t - k * Δ))) :=
    tendsto_finsetSum (Finset.range (⌊(t : ℝ) / (Δ : ℝ)⌋₊ + 1))
      (fun k _ => tendsto_const_nhds.mul (hH (t - k * Δ)))
  exact tendsto_nhds_unique (hH t) (((hR t).add hsum).congr'
    (Filter.Eventually.of_forall (fun n => (heq n).symm)))


theorem smooth_covariance_integrable
    (hrem : node_rt_u3A_remainder_u2D_momentStmtV3) :
    ∀ (d : ℕ) (hd : 2 ≤ d) (SD : StructuralData d),
    ∃ l₀ p : ℝ, 0 < l₀ ∧ SD.dependenceRange < 2 * l₀ ∧ 2 ≤ p ∧
    ∀ (Q : EnvironmentLaw d SD.ellipticity SD.dependenceRange) (_hQ : HasSmoothBounds SD Q) (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
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
  intro d hd SD
  obtain ⟨l₀, p, c, C, hl₀, hsep, hp, _hc, _hC, hrem'⟩ :=
    hrem d hd SD 1 1 (by norm_num) (by norm_num)
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

theorem smooth_first_cycle_remainders
    (hren : node_rt_u3A_renewalStmt) (hrem : node_rt_u3A_remainder_u2D_momentStmtV3) :
    ∀ (d : ℕ) (hd : 2 ≤ d) (SD : StructuralData d),
    ∃ l₀ : ℝ, 0 < l₀ ∧ SD.dependenceRange < 2 * l₀ ∧
    ∀ l : ℝ, l₀ ≤ l → ∀ δ : ℝ, 0 < δ → δ < 1 →
    ∃ p c C : ℝ, 2 ≤ p ∧ 0 < c ∧ 0 < C ∧
    ∀ (Q : EnvironmentLaw d SD.ellipticity SD.dependenceRange) (_hQ : HasSmoothBounds SD Q) (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
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
  intro d hd SD
  obtain ⟨lR, hlR, hsepR, hren'⟩ := hren d hd SD.ellipticity SD.dependenceRange
  obtain ⟨lV, _hlV, _hsepV, hvar⟩ :=
    smooth_remainder_variable_rate_both hrem d hd SD
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
  intro Q hQ lam h₀ h₁ P K hK hDnonzero F G hF hG hFp hGp t μ hμ
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
  have hout := hvar' Q hQ lam h₀ h₁ l δ ((le_max_right _ _).trans hl) hδ₀ hδ₁
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

theorem smooth_fixed_recurrences
    (hfact : node_rt_u3A_factorizationStmt)
    (hrem : node_rt_u3A_remainder_u2D_momentStmtV3) :
    ∀ (d : ℕ) (hd : 2 ≤ d) (SD : StructuralData d),
    ∃ l₀ p : ℝ, 0 < l₀ ∧ SD.dependenceRange < 2 * l₀ ∧ 2 ≤ p ∧
    ∀ (l δ : ℝ), l₀ ≤ l → 0 < δ → δ < 1 →
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
  intro d hd SD
  obtain ⟨l₀, p, hl₀, hsep, hp, hInt⟩ :=
    smooth_covariance_integrable hrem d hd SD
  refine ⟨l₀, p, hl₀, hsep, hp, ?_⟩
  intro l δ hl hδ₀ hδ₁ Q hQ lam h₀ h₁ P K hK hD F G hF hG hFp hGp
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
  have hiFG (v : ℝ≥0) := hInt Q hQ lam h₀ h₁ l δ hl hδ₀ hδ₁ P K hK hD F G
    hFg hGg hFp hGp v μ (by simp [μ])
  have hiG (v : ℝ≥0) : Integrable
      (fun q : FieldPair d × Regeneration.CoupledSample d =>
        G (translate (q.2.1 v) (reduce q.1))) ν := by
    simpa only [one_mul] using hInt Q hQ lam h₀ h₁ l δ hl hδ₀ hδ₁ P K hK hD
      (fun _ => 1) G measurable_const hGg (memLp_const 1) hGp v ν (by simp [ν])
  have hlpos := hl₀.trans_le hl
  have hsepl : SD.dependenceRange < 2 * l := hsep.trans_le (by linarith)
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

theorem smooth_fixed_observations
    (hfact : node_rt_u3A_factorizationStmt) (hren : node_rt_u3A_renewalStmt)
    (hrem : node_rt_u3A_remainder_u2D_momentStmtV3) :
    ∀ (d : ℕ) (hd : 2 ≤ d) (SD : StructuralData d),
    ∃ l₀ : ℝ, 0 < l₀ ∧ SD.dependenceRange < 2 * l₀ ∧
    ∀ l : ℝ, l₀ ≤ l → ∀ δ : ℝ, 0 < δ → δ < 1 →
    ∃ p c C : ℝ, 2 ≤ p ∧ 0 < c ∧ 0 < C ∧
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
        |hF (s + k * Δ)| ≤ C * Real.exp (-c * k) * Nf * Ng := by
  intro d hd SD
  obtain ⟨lS, hlS, hsepS, hscalar⟩ := sbxS4_fixedRadius_scalar_of_renewal hren d hd SD.ellipticity SD.dependenceRange
  obtain ⟨lQ, _hlQ, _hsepQ, hslices⟩ :=
    sbxS4_fixedRadius_centered_slices_of_renewal hren d hd SD.ellipticity SD.dependenceRange
  obtain ⟨lR, _hlR, _hsepR, hremainder⟩ :=
    smooth_first_cycle_remainders hren hrem d hd SD
  obtain ⟨lI, pI, _hlI, _hsepI, hpI, hrecurrence⟩ :=
    smooth_fixed_recurrences hfact hrem d hd SD
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
  intro Q hQ lam h₀ h₁ P K hK hD F G hF hG hFp hGp hzero
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
    have hbnd := (hrdata Q hQ lam h₀ h₁ P K hK hD (fun _ => 1) G measurable_const hGg
      (memLp_const 1) (hGp.mono_exponent hpR') t ν (by simp [ν])).2
    simp only [one_mul, hone, ENNReal.toReal_one, mul_one] at hbnd
    exact hbnd.trans (mul_le_mul_of_nonneg_left hngR (by positivity))
  have hrF (t : ℝ≥0) : |rF t| ≤ CR * Real.exp (-cR * lam ^ 2 * (t : ℝ)) * Nf * Ng := by
    have hbnd := (hrdata Q hQ lam h₀ h₁ P K hK hD F G hFg hGg
      (hFp.mono_exponent hpR') (hGp.mono_exponent hpR') t μ (by simp [μ])).2
    apply hbnd.trans
    apply mul_le_mul _ hngR ENNReal.toReal_nonneg (by positivity)
    exact mul_le_mul_of_nonneg_left hnfR (by positivity)
  obtain ⟨hqs, hqzero, hqdec⟩ := hqdata Q lam h₀ h₁ P K hK hD p
    (hpR.trans (le_max_left _ _)) F hFg hFp hzero
  have hrec := hrecurrence l δ hli hδ₀ hδ₁ Q hQ lam h₀ h₁ P K hK hD F G hF hG
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

theorem smooth_fixed_of_deps
    (hfact : node_rt_u3A_factorizationStmt) (hren : node_rt_u3A_renewalStmt)
    (hrem : node_rt_u3A_remainder_u2D_momentStmtV3)
    (_htails : node_app_u3A_regen_u2D_tailsStmt) :
    node_rt_u3A_local_u2D_mixing_u23_fixed_u2D_radiusStmtV3 := by
  intro d hd SD
  obtain ⟨lS, hlS, hsepS, hscalar⟩ := sbxS4_fixedRadius_scalar_of_renewal hren d hd SD.ellipticity SD.dependenceRange
  obtain ⟨lA, _hlA, _hsepA, hactual⟩ :=
    smooth_fixed_observations hfact hren hrem d hd SD
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
  intro Q hQ lam h₀ h₁ P K hK hD
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
    have hout := hactual' Q hQ lam h₀ h₁ P K hK hD F G hF hG hFp hGp hzero
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

theorem smooth_conditioned_variable_rate
    (hrem : node_rt_u3A_remainder_u2D_momentStmtV3) :
    ∀ (d : ℕ) (hd : 2 ≤ d) (SD : StructuralData d),
    ∃ l₀ : ℝ, 0 < l₀ ∧ SD.dependenceRange < 2 * l₀ ∧
    ∀ a : ℝ, 0 < a → ∃ p c C : ℝ, 2 ≤ p ∧ 0 < c ∧ 0 < C ∧
    ∀ (Q : EnvironmentLaw d SD.ellipticity SD.dependenceRange) (_hQ : HasSmoothBounds SD Q) (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
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
  intro d hd SD
  obtain ⟨l₀, p₀, D, hl₀, hsep, hp₀, hDpos, hmoment⟩ :=
    smooth_covariance_power_moment hrem d hd SD
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
  let μ := regenerationConditionedLaw hd Q lam l K hK.1 hD
  let f := fun ωz : FieldPair d × Regeneration.CoupledSample d =>
    F (reduce ωz.1) * G (translate (ωz.2.1 t) (reduce ωz.1))
  have hfm : Measurable f :=
    ((hF.comp Probability.measurable_reduce).comp measurable_fst).mul
      (hG.comp (Probability.continuous_translate.measurable.comp
        (((continuous_eval_const t).measurable.comp measurable_snd.fst).prodMk
          (Probability.measurable_reduce.comp measurable_fst))))
  have hpower := hmoment r hr₀ Q hQ lam h₀ h₁ l δ hl hδ₀ hδ₁ P K hK hD
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

theorem smooth_conditioned_cycle_remainder
    (hren : node_rt_u3A_renewalStmt)
    (hrem : node_rt_u3A_remainder_u2D_momentStmtV3) :
    ∀ (d : ℕ) (hd : 2 ≤ d) (SD : StructuralData d),
    ∃ l₀ : ℝ, 0 < l₀ ∧ SD.dependenceRange < 2 * l₀ ∧
    ∀ l : ℝ, l₀ ≤ l → ∀ δ : ℝ, 0 < δ → δ < 1 →
    ∃ p c C : ℝ, 2 ≤ p ∧ 0 < c ∧ 0 < C ∧
    ∀ (Q : EnvironmentLaw d SD.ellipticity SD.dependenceRange) (_hQ : HasSmoothBounds SD Q) (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
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
  intro d hd SD
  obtain ⟨L₀, hL₀, hsep₀, hevent⟩ :=
    smooth_conditioned_variable_rate hrem d hd SD
  obtain ⟨L₁, _hL₁, _hsep₁, htail⟩ := renewal_cycle_tails hren d hd SD.ellipticity SD.dependenceRange
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
  intro Q hQ lam h₀ h₁ P K hK hD m G hG hLp t
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
  have hout := hevent' Q hQ lam h₀ h₁ l δ hl₀ hδ₀ hδ₁ P K hK hD
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

theorem smooth_phase_of_deps
    (hmren : node_rt_u3A_m_u2D_renewalStmt)
    (hren : node_rt_u3A_renewalStmt)
    (hrem : node_rt_u3A_remainder_u2D_momentStmtV3)
    (_hfixed : node_rt_u3A_local_u2D_mixing_u23_fixed_u2D_radiusStmtV3) :
    node_rt_u3A_local_u2D_mixing_u23_phase_u2D_errorStmtV3 := by
  intro d hd SD
  obtain ⟨L₀, p₀, hL₀, hsep₀, hp₀, hrenew⟩ :=
    smooth_m_renewal_eq_memLp hmren hrem d hd SD
  obtain ⟨L₁, _hL₁, _hsep₁, hcycle⟩ :=
    smooth_conditioned_cycle_remainder hren hrem d hd SD
  obtain ⟨L₂, _hL₂, _hsep₂, hren'⟩ := hren d hd SD.ellipticity SD.dependenceRange
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
  intro Q hQ lam h₀ h₁ P K hK hD A m _hA hmpos hsupp G hG hLp
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
    have hbnd := hcycle' Q hQ lam h₀ h₁ P K hK hD
      m G (hG.mono (Probability.localSigma_le_borel _) le_rfl) hLp₁ t
    exact hbnd.trans (mul_le_mul_of_nonneg_left hNg
      (mul_nonneg hC₀.le (Real.exp_pos _).le))
  have hh : ∀ t : ℝ≥0, hm t = rm t +
      ∑ n ∈ Finset.range (⌊(t : ℝ) / (Δ : ℝ)⌋₊ + 1), pn n * hm (t - n * Δ) :=
    hrenew Q hQ lam h₀ h₁ l δ hl₀ hδ₀ hδ₁ P K hK hD A m hmpos hsupp G hG hLp₀
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


end EinsteinFull.Blueprint.SbxS6Section3R01
