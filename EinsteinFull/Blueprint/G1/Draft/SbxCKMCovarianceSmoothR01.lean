import EinsteinFull.Blueprint.G1.Draft.SbxS5KMSmoothR01
import EinsteinFull.Blueprint.G1.Proofs.SbxS2KmDecomp

/-! Conditional smooth-law covariance decomposition. Draft, not an adopted reduction. -/
open MeasureTheory
open scoped NNReal ENNReal Topology
noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local instance 2000] EinsteinRelation.instMeasurableSpaceMat
namespace EinsteinFull.Blueprint.SbxCKMCovarianceSmoothR01
open EinsteinRelation
open EinsteinFull.Work.W5
open EinsteinFull.Blueprint.SbxS5Section3R01

/-- The literal k-factorization restricted to smooth laws. -/
def kmKFactorSmoothStmt : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) (l δ : ℝ)
    (_hl : 0 < l) (_hsep : D.dependenceRange < 2 * l) (_hδ₀ : 0 < δ) (_hδ₁ : δ < 1),
  ∃ C : ℝ, 0 < C ∧
  ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (_hQ : HasSmoothBounds D Q) (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
    (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K),
  let Δ := Regeneration.Renewal.regenDelta lam
  let R := l / lam
  let i := Regeneration.Renewal.forceCoord hd
  let tupleEvent := fun (k n : ℕ) (a : Fin (k + 1) → ℕ) =>
    {z : Regeneration.CoupledSample d |
      a 0 = 0 ∧ a (Fin.last k) = n ∧
      (∀ j : Fin k, a j.castSucc + 2 ≤ a j.succ) ∧
      (∀ j : Fin k,
        Regeneration.sampleTimeShift Δ z ((a j.castSucc : ℝ≥0) * Δ) ∈
          Regeneration.forcedBitTrialEvent Δ lam R i (a j.succ - a j.castSucc - 1)) ∧
      (∀ j : Fin k, j.val + 1 < k → z.2 (a j.succ - 1) = true) ∧
      (∀ j : Fin k, j.val + 1 < k → ∀ u : ℝ≥0,
        (a j.succ : ℝ≥0) * Δ ≤ u → u ≤ ((n - 1 : ℕ) : ℝ≥0) * Δ →
        z.1 ((a j.succ : ℝ≥0) * Δ) i - R < z.1 u i)}
  let Γ := fun k n => ⋃ a : Fin (k + 1) → Fin (n + 1),
    tupleEvent k n (fun j => (a j).val)
  ∀ hD : Regeneration.annealedCoupledLaw Q.measure K
      (regenerationNoReturn hd R) ≠ 0,
  ∀ A : ℝ, l ≤ A →
    let k := max 1 ⌈(A / l + 4) / 10⌉₊
    (k : ℝ) ≤ C * (1 + A) ∧
    (∀ n : ℕ, 2 * k ≤ n → ∀ y : Vec d, ∀ b : Bool,
      ∃ V : FieldPair d → ℝ,
        Measurable[localSigma {x : Vec d | x i ≤ y i - 4 * R}] V ∧
        (fun ω => ∫ z,
          (if z ∈ Γ k n ∧
              y ∈ Regeneration.endpointBall i R (z.1 (((n - 1 : ℕ) : ℝ≥0) * Δ)) ∧
              (b = true → ∀ u : ℝ≥0, u ≤ ((n - 1 : ℕ) : ℝ≥0) * Δ →
                -R < z.1 u i)
            then (1 : ℝ) else 0) ∂K (0, ω)) =ᵐ[Q.measure] V) ∧
    ∀ (p : ℝ), 2 ≤ p → ∀ F : FieldPair d → ℝ,
      Measurable[localSigma {x : Vec d | euclideanNorm x < A / lam}] F →
      MemLp F (ENNReal.ofReal p) Q.measure →
      ∀ Φ : Regeneration.FutureState d i R → ℝ,
        Measurable Φ → Regeneration.BoundedRealTest Φ → ∀ n : ℕ,
      ∀ μ ∈ ({Regeneration.annealedCoupledLaw Q.measure K,
        regenerationConditionedLaw hd Q lam l K hK.1 hD} :
          Set (Measure (FieldPair d × Regeneration.CoupledSample d))),
        (∫ ωz in {ωz | regenerationTime hd lam l k ωz.2 =
            (((n : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞)},
          F ωz.1 * Φ (regenerationRecord hd lam l k ωz) ∂μ) =
        (∫ ωz, Φ (regenerationRecord hd lam l 0 ωz)
          ∂regenerationConditionedLaw hd Q lam l K hK.1 hD) *
        ∫ ωz in {ωz | regenerationTime hd lam l k ωz.2 =
            (((n : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞)}, F ωz.1 ∂μ

theorem smooth_reduced_kFactor (hfactor : kmKFactorSmoothStmt)
    {d : ℕ} (hd : 2 ≤ d) {D : StructuralData d} {l δ : ℝ}
    (hl : 0 < l) (hsep : D.dependenceRange < 2 * l) (hδ₀ : 0 < δ) (hδ₁ : δ < 1)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q) (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
    (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K)
    (hD : Regeneration.annealedCoupledLaw Q.measure K
      (regenerationNoReturn hd (l / lam)) ≠ 0)
    (A : ℝ) (hA : l ≤ A) (p : ℝ) (hp : 2 ≤ p) (F : FieldPair d → ℝ)
    (hF : Measurable[localSigma {x : Vec d | euclideanNorm x < A / lam}] F)
    (hFp : MemLp F (ENNReal.ofReal p) (reducedLaw Q))
    (Φ : Regeneration.FutureState d (Regeneration.Renewal.forceCoord hd) (l / lam) → ℝ)
    (hΦ : Measurable Φ) (hbΦ : Regeneration.BoundedRealTest Φ) (n : ℕ)
    (μ : Measure (FieldPair d × Regeneration.CoupledSample d))
    (hμ : μ ∈ ({Regeneration.annealedCoupledLaw Q.measure K,
      regenerationConditionedLaw hd Q lam l K hK.1 hD} : Set (Measure _))) :
    let k : ℕ := max 1 ⌈(A / l + 4) / 10⌉₊
    (∫ ωz in {ωz | regenerationTime hd lam l k ωz.2 =
        (((n : ℝ≥0) * Regeneration.Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)},
      F (reduce ωz.1) * Φ (regenerationRecord hd lam l k ωz) ∂μ) =
      (∫ ωz, Φ (regenerationRecord hd lam l 0 ωz)
        ∂regenerationConditionedLaw hd Q lam l K hK.1 hD) *
      ∫ ωz in {ωz | regenerationTime hd lam l k ωz.2 =
        (((n : ℝ≥0) * Regeneration.Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)},
        F (reduce ωz.1) ∂μ := by
  obtain ⟨C, _, hC⟩ := hfactor d hd D l δ hl hsep hδ₀ hδ₁
  exact (hC Q hQ lam h₀ h₁ P K hK hD A hA).2.2 p hp (F ∘ reduce)
    (hF.comp (Probability.measurable_reduce_local _))
    (hFp.comp_of_map Probability.measurable_reduce.aemeasurable) Φ hΦ hbΦ n μ hμ

theorem smooth_bounded_covariance_slice (hfactor : kmKFactorSmoothStmt)
    {d : ℕ} (hd : 2 ≤ d) {D : StructuralData d} {l δ : ℝ}
    (hl : 0 < l) (hsep : D.dependenceRange < 2 * l) (hδ₀ : 0 < δ) (hδ₁ : δ < 1)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q) (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
    (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K)
    (hD : Regeneration.annealedCoupledLaw Q.measure K
      (regenerationNoReturn hd (l / lam)) ≠ 0)
    (A : ℝ) (hA : l ≤ A) (p : ℝ) (hp : 2 ≤ p) (F G : FieldPair d → ℝ)
    (hF : Measurable[localSigma {x : Vec d | euclideanNorm x < A / lam}] F)
    (hFp : MemLp F (ENNReal.ofReal p) (reducedLaw Q))
    (hG : Measurable[localSigma {x : Vec d | euclideanNorm x < A / lam}] G)
    (hbG : Regeneration.BoundedRealTest G) (n : ℕ) (t : ℝ≥0)
    (hnt : (n : ℝ≥0) * Regeneration.Renewal.regenDelta lam ≤ t) :
    let k : ℕ := max 1 ⌈(A / l + 4) / 10⌉₊
    let m : ℕ := max 1 ⌈(A / l - 1) / 10⌉₊
    let μ := Regeneration.annealedCoupledLaw Q.measure K
    let ν := regenerationConditionedLaw hd Q lam l K hK.1 hD
    (∫ ωz in {ωz | regenerationTime hd lam l k ωz.2 =
        (((n : ℝ≥0) * Regeneration.Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)} ∩
        {ωz | regenerationTime hd lam l (k + m) ωz.2 ≤ (t : ℝ≥0∞)},
      F (reduce ωz.1) * G (translate (ωz.2.1 t) (reduce ωz.1)) ∂μ) =
      (∫ ωz in {ωz | regenerationTime hd lam l k ωz.2 =
        (((n : ℝ≥0) * Regeneration.Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)},
        F (reduce ωz.1) ∂μ) *
      ∫ ωz in {ωz | regenerationTime hd lam l m ωz.2 ≤
          ((t - (n : ℝ≥0) * Regeneration.Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)},
        G (translate (ωz.2.1 (t - (n : ℝ≥0) * Regeneration.Renewal.regenDelta lam))
          (reduce ωz.1)) ∂ν := by
  classical
  dsimp only
  let Δ := Regeneration.Renewal.regenDelta lam
  let k : ℕ := max 1 ⌈(A / l + 4) / 10⌉₊
  let m : ℕ := max 1 ⌈(A / l - 1) / 10⌉₊
  let μ := Regeneration.annealedCoupledLaw Q.measure K
  let ν := regenerationConditionedLaw hd Q lam l K hK.1 hD
  let u : ℝ≥0 := t - (n : ℝ≥0) * Δ
  let slice : Set (FieldPair d × Regeneration.CoupledSample d) :=
    {q | regenerationTime hd lam l k q.2 = (((n : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞)}
  let E : Set (FieldPair d × Regeneration.CoupledSample d) :=
    {q | regenerationTime hd lam l (k + m) q.2 ≤ (t : ℝ≥0∞)}
  let Em : Set (FieldPair d × Regeneration.CoupledSample d) :=
    {q | regenerationTime hd lam l m q.2 ≤ (u : ℝ≥0∞)}
  let obs := fun (v : ℝ≥0) (q : FieldPair d × Regeneration.CoupledSample d) =>
    G (translate (q.2.1 v) (reduce q.1))
  have hm : 1 ≤ m := le_max_left _ _
  have hρ : A / lam ≤ (10 * (m : ℝ) + 1) * (l / lam) := by
    have hx : (A / l - 1) / 10 ≤ (m : ℝ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast le_max_right 1 ⌈(A / l - 1) / 10⌉₊)
    calc A / lam = (A / l) * (l / lam) := by field_simp
         _ ≤ (10 * (m : ℝ) + 1) * (l / lam) :=
           mul_le_mul_of_nonneg_right (by linarith) (div_nonneg hl.le h₀.le)
  have hs := sliceChar_of_slices hd Q lam h₀ h₁ l δ hl hsep hδ₀ hδ₁ P K hK
  obtain ⟨D, hDm, hDr⟩ := Probability.exists_future_halfSpace_decoder
    (Regeneration.Renewal.forceCoord hd) (l / lam)
  let Φ := PhiM Δ lam (l / lam) (Regeneration.Renewal.forceCoord hd) D G m u
  have hτ (j : ℕ) : Measurable (fun q : FieldPair d × Regeneration.CoupledSample d =>
      regenerationTime hd lam l j q.2) :=
    (Regeneration.measurable_regenerationTime Δ lam (l / lam)
      (Regeneration.Renewal.forceCoord hd) j).comp measurable_snd
  have hslice : MeasurableSet slice := hτ k (measurableSet_singleton _)
  have hE : MeasurableSet E := measurableSet_le (hτ (k + m)) measurable_const
  have hEm : MeasurableSet Em := measurableSet_le (hτ m) measurable_const
  have hgain := ae_gain_annealed hd Q lam h₀ h₁ l δ P K hK
  have hac : ν ≪ μ := ProbabilityTheory.cond_absolutelyContinuous
  have hrecord : ∀ᵐ q ∂μ, q ∈ slice →
      E.indicator (fun q => F (reduce q.1) * obs t q) q =
        F (reduce q.1) * Φ (regenerationRecord hd lam l k q) := by
    filter_upwards [hgain] with q hq hqmem
    have heq := sbxS2_PhiM_record_on_slice hd lam l (A / lam) h₀ hl hs D hDr G hG
      k m n hm hρ q.1 q.2 t hq hqmem hnt
    change Φ (regenerationRecord hd lam l k q) = if q ∈ E then obs t q else 0 at heq
    rw [Set.indicator_apply, heq, mul_ite, mul_zero]
  have hrecord0 : ∀ᵐ q ∂ν, Φ (regenerationRecord hd lam l 0 q) = Em.indicator (obs u) q := by
    filter_upwards [hac.ae_le hgain] with q hq
    have heq := sbxS2_PhiM_record_on_slice hd lam l (A / lam) h₀ hl hs D hDr G hG
      0 m 0 hm hρ q.1 q.2 u hq (by simp [regenerationTime, Regeneration.regenerationTime])
      (by simp)
    simpa only [Φ, Em, obs, Set.mem_ofPred_eq, Nat.zero_add, Nat.cast_zero, zero_mul,
      tsub_zero, Set.indicator_apply]
      using heq
  have hfactor' := smooth_reduced_kFactor hfactor hd hl hsep hδ₀ hδ₁ Q hQ lam h₀ h₁ P K
    hK hD A hA p hp F hF hFp Φ
    (measurable_PhiM Δ lam (l / lam) (A / lam) _ D hDm G hG m u)
    (boundedRealTest_PhiM Δ lam (l / lam) _ D G hbG m u) n μ (Set.mem_insert _ _)
  change (∫ q in slice ∩ E, F (reduce q.1) * obs t q ∂μ) =
    (∫ q in slice, F (reduce q.1) ∂μ) * ∫ q in Em, obs u q ∂ν
  calc
    _ = ∫ q in slice, E.indicator (fun q => F (reduce q.1) * obs t q) q ∂μ :=
      (setIntegral_indicator hE).symm
    _ = ∫ q in slice, F (reduce q.1) * Φ (regenerationRecord hd lam l k q) ∂μ :=
      setIntegral_congr_ae hslice hrecord
    _ = (∫ q, Φ (regenerationRecord hd lam l 0 q) ∂ν) *
        ∫ q in slice, F (reduce q.1) ∂μ := hfactor'
    _ = _ := by rw [integral_congr_ae hrecord0, integral_indicator hEm, mul_comm]

theorem smooth_bounded_covariance_decomposition (hfactor : kmKFactorSmoothStmt)
    {d : ℕ} (hd : 2 ≤ d) {D : StructuralData d} {l δ : ℝ}
    (hl : 0 < l) (hsep : D.dependenceRange < 2 * l) (hδ₀ : 0 < δ) (hδ₁ : δ < 1)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q) (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
    (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K)
    (hD : Regeneration.annealedCoupledLaw Q.measure K
      (regenerationNoReturn hd (l / lam)) ≠ 0)
    (A : ℝ) (hA : l ≤ A) (p : ℝ) (hp : 2 ≤ p) (F G : FieldPair d → ℝ)
    (hF : Measurable[localSigma {x : Vec d | euclideanNorm x < A / lam}] F)
    (hFp : MemLp F (ENNReal.ofReal p) (reducedLaw Q))
    (hG : Measurable[localSigma {x : Vec d | euclideanNorm x < A / lam}] G)
    (hbG : Regeneration.BoundedRealTest G) (t : ℝ≥0) :
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
  classical
  dsimp only
  let k : ℕ := max 1 ⌈(A / l + 4) / 10⌉₊
  let m : ℕ := max 1 ⌈(A / l - 1) / 10⌉₊
  let μ := Regeneration.annealedCoupledLaw Q.measure K
  let Δ := Regeneration.Renewal.regenDelta lam
  let f := fun ωz : FieldPair d × Regeneration.CoupledSample d =>
    F (reduce ωz.1) * G (translate (ωz.2.1 t) (reduce ωz.1))
  let E : Set (FieldPair d × Regeneration.CoupledSample d) :=
    {q | regenerationTime hd lam l (k + m) q.2 ≤ (t : ℝ≥0∞)}
  let slice := fun n : ℕ => {q : FieldPair d × Regeneration.CoupledSample d |
    regenerationTime hd lam l k q.2 = (((n : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞)}
  let N := ⌊(t : ℝ) / (Δ : ℝ)⌋₊
  have hΔ : 0 < Δ := Real.toNNReal_pos.mpr (inv_pos.mpr (sq_pos_of_pos h₀))
  let := reducedLaw_probability Q
  have hFi : Integrable F (reducedLaw Q) := hFp.integrable (by
    rw [← ENNReal.ofReal_one, ENNReal.ofReal_le_ofReal_iff (by positivity)]
    linarith)
  have hGg : Measurable G := hG.mono (Probability.localSigma_le_borel _) le_rfl
  have hint := sbxS2_integrable_bounded_observation Q K hK.1 F G hFi hGg hbG t
  refine ⟨hint, ?_⟩
  have hτ (j : ℕ) : Measurable (fun q : FieldPair d × Regeneration.CoupledSample d =>
      regenerationTime hd lam l j q.2) :=
    (Regeneration.measurable_regenerationTime Δ lam (l / lam)
      (Regeneration.Renewal.forceCoord hd) j).comp measurable_snd
  have hE : MeasurableSet E := measurableSet_le (hτ (k + m)) measurable_const
  have hslice (n : ℕ) : MeasurableSet (slice n) := hτ k (measurableSet_singleton _)
  have hnt (n : ℕ) (hn : n ∈ Finset.range (N + 1)) : (n : ℝ≥0) * Δ ≤ t := by
    have hnN : n ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
    have hnreal : (n : ℝ) ≤ (t : ℝ) / (Δ : ℝ) :=
      (Nat.cast_le.mpr hnN).trans (Nat.floor_le (by positivity))
    have hmul : (n : ℝ) * (Δ : ℝ) ≤ (t : ℝ) := by
      rwa [le_div_iff₀ (by exact_mod_cast hΔ)] at hnreal
    exact_mod_cast hmul
  have hcover : E = ⋃ n ∈ Finset.range (N + 1), slice n ∩ E := by
    ext q
    simp only [Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · intro hq
      have hmono : Monotone (fun j => regenerationTime hd lam l j q.2) :=
        monotone_nat_of_le_succ fun j => regenerationTime_le_succ Δ lam (l / lam)
          (Regeneration.Renewal.forceCoord hd) j q.2
      have hkt : regenerationTime hd lam l k q.2 ≤ (t : ℝ≥0∞) :=
        (hmono (Nat.le_add_right k m)).trans hq
      have hkfin : Regeneration.regenerationTime Δ lam (l / lam) q.2
          (Regeneration.Renewal.forceCoord hd) k ≠ ⊤ :=
        ne_top_of_le_ne_top ENNReal.coe_ne_top hkt
      obtain ⟨n, hn⟩ := Regeneration.regenerationTime_mem_grid Δ hΔ lam (l / lam)
        q.2 (Regeneration.Renewal.forceCoord hd) k hkfin
      have hkn : regenerationTime hd lam l k q.2 =
          (((n : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞) := hn
      rw [hkn] at hkt
      have hnr : (n : ℝ) ≤ (t : ℝ) / (Δ : ℝ) := by
        rw [le_div_iff₀ (by exact_mod_cast hΔ)]
        exact_mod_cast ENNReal.coe_le_coe.mp hkt
      exact ⟨n, Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.le_floor hnr)), hkn, hq⟩
    · rintro ⟨_, _, _, hq⟩
      exact hq
  have hsum : (∫ q in E, f q ∂μ) =
      ∑ n ∈ Finset.range (N + 1), ∫ q in slice n ∩ E, f q ∂μ := by
    have h := integral_biUnion_finset (μ := μ) (f := f) (Finset.range (N + 1))
      (s := fun n => slice n ∩ E) (fun n _ => (hslice n).inter hE)
      (by
        intro n _ n' _ hne
        refine Set.disjoint_left.mpr fun q hq hq' => hne ?_
        have heq : (n : ℝ≥0) * Δ = (n' : ℝ≥0) * Δ :=
          ENNReal.coe_injective (hq.1.symm.trans hq'.1)
        exact_mod_cast mul_right_cancel₀ hΔ.ne' heq)
      (fun _ _ => hint.integrableOn)
    rw [← hcover] at h
    exact h
  have hsplit : (∫ q, f q ∂μ) = (∫ q in Eᶜ, f q ∂μ) + ∫ q in E, f q ∂μ := by
    rw [add_comm, integral_add_compl hE hint]
  have hEc : Eᶜ = {q | (t : ℝ≥0∞) < regenerationTime hd lam l (k + m) q.2} := by
    ext q
    change (¬ regenerationTime hd lam l (k + m) q.2 ≤ (t : ℝ≥0∞)) ↔ _
    exact not_le
  change (∫ q, f q ∂μ) = _
  rw [hsplit, hEc, hsum]
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  exact smooth_bounded_covariance_slice hfactor hd hl hsep hδ₀ hδ₁ Q hQ lam h₀ h₁ P K hK hD
    A hA p hp F G hF hFp hG hbG n t (hnt n hn)

theorem smooth_sbxS2_covariance_decomposition_of_deps
    (hfactor : kmKFactorSmoothStmt)
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
    (smooth_bounded_covariance_decomposition hfactor hd (hl₀.trans_le hl)
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



end EinsteinFull.Blueprint.SbxCKMCovarianceSmoothR01
