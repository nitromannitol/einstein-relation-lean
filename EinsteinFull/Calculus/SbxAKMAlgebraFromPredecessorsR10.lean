import EinsteinFull.Calculus.SbxAUniformKMAssemblerR07
import EinsteinFull.Blueprint.G1.node_rt_u3A_k_u2D_factor
import EinsteinFull.Blueprint.G1.node_rt_u3A_remainder_u2D_moment

open MeasureTheory
open scoped NNReal ENNReal Topology
noncomputable section
namespace EinsteinFull.Blueprint.SbxAKMAlgebraFromPredecessorsR10
open EinsteinRelation EinsteinFull.Work.W5
open EinsteinFull.Blueprint.SbxCKMCovarianceSmoothR01
open EinsteinFull.Blueprint.SbxS5Section3R01
open EinsteinFull.Blueprint.SbxCKMCovarianceDecaySmoothR02
open EinsteinFull.Blueprint.SbxAUniformKMAssemblerR07

private theorem uniform_covariance_integrable_of_remainder
    (hrem : node_rt_u3A_remainder_u2D_momentStmt) :
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
    hrem d hd Λ₀ r₀ 1 1 (by norm_num) (by norm_num)
  refine ⟨l₀, p, hl₀, hsep, hp, ?_⟩
  intro β hβ
  dsimp only
  intro Q hQ lam h₀ h₁ l δ hl hδ₀ hδ₁ P K hK hD F G hF hG hFp hGp t μ hμ
  let : IsProbabilityMeasure (Regeneration.annealedCoupledLaw Q.measure K) :=
    Regeneration.annealedCoupledLaw_isProbabilityMeasure Q.measure K hK.1
  have hprob : Regeneration.annealedCoupledLaw Q.measure K Set.univ ≤
      ENNReal.ofReal (1 * Real.exp (1 * (lam ^ 2 * (t : ℝ)) -
        1 * lam ^ 2 * (t : ℝ))) := by simp
  have hint := (hrem Q lam h₀ h₁ l δ hl hδ₀ hδ₁ P K hK hD
    F G hF hG hFp hGp (lam ^ 2 * (t : ℝ)) t Set.univ
    (mul_nonneg (sq_nonneg lam) t.coe_nonneg) MeasurableSet.univ hprob μ hμ).1
  simpa only [integrableOn_univ] using hint

theorem a_uniform_covariance_decomposition_of_exact_predecessors
    (hfactor : node_rt_u3A_k_u2D_factorStmt)
    (hrem : node_rt_u3A_remainder_u2D_momentStmt)
    (_hmany : SbxCManyCycleUniformR06.manyCycleSmoothStmt) :
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
    obtain ⟨C, hC, h⟩ := hfactor d hd SD.ellipticity SD.dependenceRange l δ hl hs hδ₀ hδ₁
    refine ⟨C, hC, ?_⟩
    intro Q _hQ lam h₀ h₁ P K hK
    exact h Q lam h₀ h₁ P K hK
  intro d hd Λ₀ r₀ hΛ hr
  obtain ⟨l₀, p, hl₀, hsep, hp, hInt⟩ :=
    uniform_covariance_integrable_of_remainder hrem d hd Λ₀ r₀ hΛ hr
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


theorem a_uniform_centered_covariance_of_exact_predecessors
    (hfactor : node_rt_u3A_k_u2D_factorStmt)
    (hrem : node_rt_u3A_remainder_u2D_momentStmt)
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
    a_uniform_covariance_decomposition_of_exact_predecessors hfactor hrem hmany d hd Λ₀ r₀ hΛ hr
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

end EinsteinFull.Blueprint.SbxAKMAlgebraFromPredecessorsR10
