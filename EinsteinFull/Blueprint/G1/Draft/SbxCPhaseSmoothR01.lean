import EinsteinFull.Blueprint.G1.Draft.SbxS6LocalMixingSmoothR01

/-! Draft smooth-law phase-error consumer; not reviewed or adopted.
The prior ordered graph also contains a fixed-radius input, unused by its proof. -/
open MeasureTheory
open scoped NNReal ENNReal Topology
namespace EinsteinFull.Blueprint.SbxCPhaseSmoothR01
open EinsteinRelation EinsteinFull.Blueprint SbxS6Section3R01

def phaseRenewalSmoothStmt : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d),
    ∃ l₀ : ℝ, 0 < l₀ ∧ D.dependenceRange < 2 * l₀ ∧
    ∀ l : ℝ, l₀ ≤ l → ∀ δ : ℝ, 0 < δ → δ < 1 →
    ∃ c C a M : ℝ, 0 < c ∧ 0 < C ∧ 0 < a ∧ 0 < M ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (_hQ : HasSmoothBounds D Q) (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
      (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d),
    ∀ hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K,
    ∀ hD : Regeneration.annealedCoupledLaw Q.measure K
      (regenerationNoReturn hd (l / lam)) ≠ 0,
      let p := regenerationLatticeMass hd Q lam l K hK.1 hD
      let m := ∑' n : ℕ, p n * (n : ℝ)
      (∀ n : ℕ, |(∑' j : ℕ, latticeConvolutionPower p j n) - m⁻¹| ≤
        C * Real.exp (-c * n)) ∧
      (∀ j : ℕ,
        (∫⁻ ωz, if regenerationTime hd lam l j ωz.2 = ⊤ then ⊤ else
          ENNReal.ofReal (Real.exp (a * lam ^ 2 *
            (regenerationTime hd lam l j ωz.2).toReal))
          ∂regenerationConditionedLaw hd Q lam l K hK.1 hD) ≤ ENNReal.ofReal (M ^ j)) ∧
      (∀ j : ℕ,
        (∫⁻ ωz, if regenerationTime hd lam l j ωz.2 = ⊤ then ⊤ else
          ENNReal.ofReal (Real.exp (a * lam ^ 2 *
            (regenerationTime hd lam l j ωz.2).toReal))
          ∂Regeneration.annealedCoupledLaw Q.measure K) ≤
            ENNReal.ofReal (C * M ^ j))


def phaseMRenewalSmoothStmt : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) (l δ : ℝ)
    (_hl : 0 < l) (_hsep : D.dependenceRange < 2 * l) (_hδ₀ : 0 < δ) (_hδ₁ : δ < 1),
  ∃ C : ℝ, 0 < C ∧
  ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (_hQ : HasSmoothBounds D Q) (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
    (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K),
  let Δ := Regeneration.Renewal.regenDelta lam
  let R := l / lam
  let i := Regeneration.Renewal.forceCoord hd
  ∀ hD : Regeneration.annealedCoupledLaw Q.measure K
      (regenerationNoReturn hd R) ≠ 0,
  let ν := regenerationConditionedLaw hd Q lam l K hK.1 hD
  ∀ A : ℝ, l ≤ A →
    let m := max 1 ⌈(A / l - 1) / 10⌉₊
    (m : ℝ) ≤ C * (1 + A) ∧
    ∀ G : FieldPair d → ℝ,
      Measurable[localSigma {x : Vec d | euclideanNorm x < A / lam}] G →
      Regeneration.BoundedRealTest G →
    let obs := fun (t : ℝ≥0) (ωz : FieldPair d × Regeneration.CoupledSample d) =>
      G (translate (ωz.2.1 t) (reduce ωz.1))
    let h := fun t : ℝ≥0 => ∫ ωz in
      {ωz | regenerationTime hd lam l m ωz.2 ≤ (t : ℝ≥0∞)}, obs t ωz ∂ν
    let r := fun t : ℝ≥0 => ∫ ωz in
      {ωz | regenerationTime hd lam l m ωz.2 ≤ (t : ℝ≥0∞) ∧
        (t : ℝ≥0∞) < regenerationTime hd lam l (m + 1) ωz.2}, obs t ωz ∂ν
    ∀ t : ℝ≥0,
      (∃ Φ : Regeneration.FutureState d i R → ℝ,
        Measurable Φ ∧ Regeneration.BoundedRealTest Φ ∧
        (fun ωz => ({ωz | regenerationTime hd lam l m ωz.2 ≤ (t : ℝ≥0∞)}.indicator
          (obs t)) ωz) =ᵐ[ν] (fun ωz => Φ (regenerationRecord hd lam l 0 ωz))) ∧
      (∀ᵐ ωz ∂ν, regenerationTime hd lam l m ωz.2 ≤ (t : ℝ≥0∞) →
        ∀ x : Vec d, euclideanNorm (x - ωz.2.1 t) < A / lam → -2 * R ≤ x i) ∧
      h t = r t + ∑ n ∈ Finset.range (⌊(t : ℝ) / (Δ : ℝ)⌋₊ + 1),
        regenerationLatticeMass hd Q lam l K hK.1 hD n * h (t - (n : ℝ≥0) * Δ)

theorem smooth_m_renewal_eq_of_support (hren : phaseMRenewalSmoothStmt)
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) (l δ : ℝ)
    (hl : 0 < l) (hsep : D.dependenceRange < 2 * l) (hδ₀ : 0 < δ) (hδ₁ : δ < 1)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q) (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
    (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K)
    (hD : Regeneration.annealedCoupledLaw Q.measure K
      (regenerationNoReturn hd (l / lam)) ≠ 0)
    (A : ℝ) (m : ℕ) (hm : 1 ≤ m)
    (hsupport : 10 * (m : ℝ) * l - l - A ≥ -2 * l)
    (G : FieldPair d → ℝ)
    (hG : Measurable[localSigma {x : Vec d | euclideanNorm x < A / lam}] G)
    (hbG : Regeneration.BoundedRealTest G) :
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
  let A' := (10 * (m : ℝ) + 1) * l
  have hm₀ : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hA' : l ≤ A' := by dsimp only [A']; nlinarith only [mul_nonneg hm₀ hl.le]
  have hAA' : A ≤ A' := by dsimp only [A']; linarith only [hsupport]
  have hquot : (A' / l - 1) / 10 = (m : ℝ) := by
    dsimp only [A']
    rw [mul_div_cancel_right₀ _ hl.ne']
    ring
  have hcanonical : max 1 ⌈(A' / l - 1) / 10⌉₊ = m := by
    rw [hquot, Nat.ceil_natCast, max_eq_right hm]
  have hG' : Measurable[localSigma {x : Vec d | euclideanNorm x < A' / lam}] G :=
    hG.mono (Probability.localSigma_mono (fun x hx =>
      lt_of_lt_of_le hx (div_le_div_of_nonneg_right hAA' h₀.le))) le_rfl
  obtain ⟨_, _, hren'⟩ := hren d hd D l δ hl hsep hδ₀ hδ₁
  have hresult := (hren' Q hQ lam h₀ h₁ P K hK hD A' hA').2
  rw [hcanonical] at hresult
  dsimp only
  intro t
  exact (hresult G hG' hbG t).2.2

theorem phase_renewal_cycle_tails (hren : phaseRenewalSmoothStmt) :
    ∀ (d : ℕ) (hd : 2 ≤ d) (SD : StructuralData d),
    ∃ l₀ : ℝ, 0 < l₀ ∧ SD.dependenceRange < 2 * l₀ ∧
    ∀ l : ℝ, l₀ ≤ l → ∀ δ : ℝ, 0 < δ → δ < 1 →
    ∃ a C : ℝ, 0 < a ∧ 0 < C ∧
    ∀ (Q : EnvironmentLaw d SD.ellipticity SD.dependenceRange) (_hQ : HasSmoothBounds SD Q) (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
      (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
      (hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K)
      (hD : Regeneration.annealedCoupledLaw Q.measure K
        (regenerationNoReturn hd (l / lam)) ≠ 0),
    ∀ (m : ℕ) (t : ℝ≥0),
      regenerationConditionedLaw hd Q lam l K hK.1 hD
        {ωz | regenerationTime hd lam l m ωz.2 ≤ (t : ℝ≥0∞) ∧
          (t : ℝ≥0∞) < regenerationTime hd lam l (m + 1) ωz.2} ≤
        ENNReal.ofReal (C * Real.exp (C * m - a * lam ^ 2 * (t : ℝ))) := by
  intro d hd SD
  obtain ⟨l₀, hl₀, hsep, hren'⟩ := hren d hd SD
  refine ⟨l₀, hl₀, hsep, ?_⟩
  intro l hl δ hδ₀ hδ₁
  obtain ⟨_, _, a, M, _, _, ha, hM, hmoment⟩ := hren' l hl δ hδ₀ hδ₁
  obtain ⟨C, hC, hcycle⟩ := geometric_cycle_bound M 1 hM
  refine ⟨a, C, ha, hC, ?_⟩
  intro Q hQ lam h₀ h₁ P K hK hD m t
  have htail := regeneration_cycle_tail_of_moment d hd lam l a (M ^ (m + 1)) ha.le m
    (regenerationConditionedLaw hd Q lam l K hK.1 hD)
    ((hmoment Q hQ lam h₀ h₁ P K hK hD).2.1 (m + 1)) t
  apply htail.trans
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ (C * Real.exp (C * m)) * Real.exp (-a * lam ^ 2 * (t : ℝ)) :=
      mul_le_mul_of_nonneg_right (by simpa only [one_mul] using hcycle m)
        (Real.exp_pos _).le
    _ = _ := by simp only [sub_eq_add_neg, Real.exp_add, neg_mul, mul_assoc]

theorem phase_m_renewal_eq_memLp
    (hmren : phaseMRenewalSmoothStmt)
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
    smooth_m_renewal_eq_of_support hmren d hd SD l δ (hl₀.trans_le hl)
      (hsep.trans_le (by linarith)) hδ₀ hδ₁ Q hQ lam h₀ h₁ P K hK hD A m hm hs
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

theorem phase_conditioned_cycle_remainder
    (hren : phaseRenewalSmoothStmt)
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
  obtain ⟨L₁, _hL₁, _hsep₁, htail⟩ := phase_renewal_cycle_tails hren d hd SD
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
    apply (htail' Q hQ lam h₀ h₁ P K hK hD m t).trans
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

theorem phase_of_smooth_deps
    (hmren : phaseMRenewalSmoothStmt)
    (hren : phaseRenewalSmoothStmt)
    (hrem : node_rt_u3A_remainder_u2D_momentStmtV3)
    :
    node_rt_u3A_local_u2D_mixing_u23_phase_u2D_errorStmtV3 := by
  intro d hd SD
  obtain ⟨L₀, p₀, hL₀, hsep₀, hp₀, hrenew⟩ :=
    phase_m_renewal_eq_memLp hmren hrem d hd SD
  obtain ⟨L₁, _hL₁, _hsep₁, hcycle⟩ :=
    phase_conditioned_cycle_remainder hren hrem d hd SD
  obtain ⟨L₂, _hL₂, _hsep₂, hren'⟩ := hren d hd SD
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
  have hactual := hren'' Q hQ lam h₀ h₁ P K hK hD
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


end EinsteinFull.Blueprint.SbxCPhaseSmoothR01
