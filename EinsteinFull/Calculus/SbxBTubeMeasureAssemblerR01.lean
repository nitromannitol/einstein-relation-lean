import EinsteinFull.Work.W1.GMPKilledEndpointSupport
import EinsteinFull.Calculus.SbxS4KilledTranslationR02
import EinsteinFull.Calculus.F2S3Section3TubeProbabilityAssemblerTakeover01
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real

open CompactlySupportedContinuousMap Filter Function Set TopologicalSpace MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BoundedContinuousFunction CompactlySupported Topology

namespace EinsteinFull
open EinsteinRelation EinsteinRelation.Diffusion
open EinsteinRelation.External.GantertSection7Support

/-- Local comparison from nonnegative compact tests. The two measures need
only be finite on compact sets; outer regularity of the upper measure and
inner regularity of the lower measure are explicit. -/
theorem b_measure_le_of_local_compact_tests
    {α : Type*} [TopologicalSpace α] [T2Space α] [MeasurableSpace α] [BorelSpace α]
    [LocallyCompactSpace α] (μ ν : Measure α) [ν.OuterRegular]
    [IsFiniteMeasureOnCompacts ν] [IsFiniteMeasureOnCompacts μ] [μ.InnerRegular]
    (U : Set α) (hU : IsOpen U)
    (htest : ∀ f : C_c(α, ℝ), (∀ x, 0 ≤ f x) → tsupport f ⊆ U →
      ∫ x, f x ∂μ ≤ ∫ x, f x ∂ν)
    (A : Set α) (hA : MeasurableSet A) (hAU : A ⊆ U) : μ A ≤ ν A := by
  have hcompact : ∀ K : Set α, IsCompact K → K ⊆ U → μ K ≤ ν K := by
    intro K hK hKU
    refine ENNReal.le_of_forall_pos_le_add fun ε hε hν => ?_
    have hνK : ν K ≠ ⊤ := hν.ne
    have hμK : μ K ≠ ⊤ := hK.measure_lt_top.ne
    obtain ⟨W, hKW, hWo, hWbound⟩ : ∃ W ⊇ K, IsOpen W ∧ ν W ≤ ν K + ε :=
      exists_isOpen_le_add K ν (ne_of_gt (ENNReal.coe_lt_coe.mpr hε))
    let V := W ∩ U
    have hKV : K ⊆ V := fun x hx => ⟨hKW hx, hKU hx⟩
    have hVo : IsOpen V := hWo.inter hU
    have hVbound : ν V ≤ ν K + ε :=
      (measure_mono (show V ⊆ W from inter_subset_left)).trans hWbound
    suffices μ.real K ≤ ν.real K + ε by
      rwa [← ENNReal.toReal_le_toReal, ENNReal.toReal_add, ENNReal.coe_toReal]
      all_goals finiteness
    have hVlt : ν V < ⊤ := hVbound.trans_lt (by finiteness)
    obtain ⟨f, hfK, hfV, hfrange⟩ :
        ∃ f : C_c(α, ℝ), Set.EqOn (⇑f) 1 K ∧ tsupport ⇑f ⊆ V ∧
          ∀ x : α, f x ∈ Set.Icc 0 1 := by
      obtain ⟨f, hf1, hf2, hf3⟩ :=
        exists_continuousMap_one_of_isCompact_subset_isOpen hK hVo hKV
      exact ⟨⟨f, hasCompactSupport_def.mpr hf2⟩, hf1, hf3⟩
    have hfUpper (x : α) : f x ≤ V.indicator 1 x := by
      by_cases hx : x ∈ tsupport f
      · simp [hfV hx, (hfrange x).2]
      · simp [image_eq_zero_of_notMem_tsupport hx, Set.indicator_nonneg]
    have hfLower (x : α) : K.indicator 1 x ≤ f x := by
      by_cases hx : x ∈ K
      · simp [hx, hfK hx]
      · simp [hx, (hfrange x).1]
    calc
      μ.real K = ∫ x, K.indicator 1 x ∂μ :=
        (integral_indicator_one hK.measurableSet).symm
      _ ≤ ∫ x, f x ∂μ := by
        refine integral_mono ?_ f.integrable hfLower
        exact (continuousOn_const.integrableOn_compact hK).integrable_indicator hK.measurableSet
      _ ≤ ∫ x, f x ∂ν := htest f (fun x => (hfrange x).1)
        (hfV.trans inter_subset_right)
      _ ≤ ∫ x, V.indicator 1 x ∂ν := by
        refine integral_mono f.integrable ?_ hfUpper
        exact IntegrableOn.integrable_indicator integrableOn_const hVo.measurableSet
      _ ≤ (ν K).toReal + ↑ε := by
        rwa [integral_indicator_one hVo.measurableSet, measureReal_def,
          ← ENNReal.coe_toReal, ← ENNReal.toReal_add, ENNReal.toReal_le_toReal]
        all_goals finiteness
  rw [hA.measure_eq_iSup_isCompact μ]
  refine iSup_le fun K => iSup_le fun hKA => iSup_le fun hK => ?_
  exact (hcompact K hK (hKA.trans hAU)).trans (measure_mono hKA)


/-- A finite Euclidean measure satisfying the local compact-test inequality
has the corresponding setwise lower bound. -/
theorem b_euclidean_setwise_of_compact_tests {d : ℕ}
    (ν : Measure (Vec d)) [IsFiniteMeasure ν] (U : Set (Vec d)) (hU : IsOpen U)
    (c : ℝ) (hc : 0 ≤ c)
    (htest : ∀ f : C_c(Vec d, ℝ), (∀ x, 0 ≤ f x) → tsupport f ⊆ U →
      c * ∫ x, f x ∂(volume : Measure (Vec d)) ≤ ∫ x, f x ∂ν)
    (A : Set (Vec d)) (hA : MeasurableSet A) (hAU : A ⊆ U) :
    ENNReal.ofReal c * volume A ≤ ν A := by
  letI : IsFiniteMeasureOnCompacts (ENNReal.ofReal c • (volume : Measure (Vec d))) :=
    IsFiniteMeasureOnCompacts.smul _ ENNReal.ofReal_ne_top
  have ht : ∀ f : C_c(Vec d, ℝ), (∀ x, 0 ≤ f x) → tsupport f ⊆ U →
      ∫ x, f x ∂(ENNReal.ofReal c • (volume : Measure (Vec d))) ≤ ∫ x, f x ∂ν := by
    intro f hf hfU
    simpa only [integral_smul_measure, ENNReal.toReal_ofReal hc, smul_eq_mul] using htest f hf hfU
  have hb := b_measure_le_of_local_compact_tests
    (ENNReal.ofReal c • (volume : Measure (Vec d))) ν U hU ht A hA hAU
  simpa only [Measure.smul_apply, smul_eq_mul] using hb

/-- Compact-test bounds imply setwise lower bounds for each actual killed GMP row. -/
theorem b_tube_setwise_of_row_testing
    {d : ℕ} {hd : 2 ≤ d} {L : ℝ} {hL : 1 ≤ L}
    {ω : FieldPair d} {hω : IsRegular L ω}
    {lam : ℝ} {h0 : 0 ≤ lam} {h1 : lam ≤ 1}
    (r : GantertFixedEnvironmentRealization hd L hL ω hω lam h0 h1)
    (U : Set (Vec d)) (hU : IsOpen U) (t : ℝ≥0) (start : Vec d)
    (V : Set (Vec d)) (hV : IsOpen V) (c : ℝ) (hc : 0 ≤ c)
    (htest : ∀ f : C_c(Vec d, ℝ), (∀ x, 0 ≤ f x) → tsupport f ⊆ V →
      c * ∫ x, f x ∂(volume : Measure (Vec d)) ≤
        ∫ x, f x ∂(gmpKilledEndpointKernel r U hU t start))
    (A : Set (Vec d)) (hA : MeasurableSet A) (hAV : A ⊆ V) :
    ENNReal.ofReal c * volume A ≤ gmpKilledEndpointKernel r U hU t start A := by
  letI := isFiniteKernel_gmpKilledEndpointKernel r U hU t
  exact b_euclidean_setwise_of_compact_tests _ V hV c hc htest A hA hAV

/-- Changing the clock by the square of any nonzero signed force preserves
strict survival in a literal spatially scaled open domain. -/
theorem b_signed_rescaled_survival_iff {d : ℕ} (lam : ℝ) (hlam : lam ≠ 0)
    (U : Set (Vec d)) (hU : IsOpen U) (h : ℝ) (hh : 0 ≤ h) (Y : Path d) :
    (((h / lam ^ 2).toNNReal : ℝ≥0∞) <
        localityExitTime ((fun x : Vec d => lam • x) ⁻¹' U) Y) ↔
      ∀ u : ℝ≥0, (u : ℝ) ≤ h →
        lam • Y ((u : ℝ) / lam ^ 2).toNNReal ∈ U := by
  have hq : 0 < lam ^ 2 := sq_pos_of_ne_zero hlam
  have hopen : IsOpen ((fun x : Vec d => lam • x) ⁻¹' U) :=
    hU.preimage (continuous_id.const_smul lam)
  rw [lt_localityExitTime_iff _ hopen]
  constructor
  · intro hY u hu
    apply hY
    apply NNReal.coe_le_coe.mp
    rw [Real.coe_toNNReal _ (div_nonneg u.coe_nonneg hq.le),
      Real.coe_toNNReal _ (div_nonneg hh hq.le)]
    exact div_le_div_of_nonneg_right hu hq.le
  · intro hY t ht
    let u : ℝ≥0 := ⟨(t : ℝ) * lam ^ 2, mul_nonneg t.coe_nonneg hq.le⟩
    have hu : (u : ℝ) ≤ h := by
      have ht' : (t : ℝ) ≤ h / lam ^ 2 := by
        have ht' := NNReal.coe_le_coe.mpr ht
        rwa [Real.coe_toNNReal _ (div_nonneg hh hq.le)] at ht'
      exact (le_div_iff₀ hq).mp ht'
    have htime : ((u : ℝ) / lam ^ 2).toNNReal = t := by
      change ((t : ℝ) * lam ^ 2 / lam ^ 2).toNNReal = t
      rw [mul_div_cancel_right₀ _ hq.ne', Real.toNNReal_coe]
    change lam • Y t ∈ U
    simpa only [htime] using hY u hu


/-- A compact-test bound for a killed physical path row transports to the
literal rescaled tube event for either sign of a nonzero force. -/
theorem b_signed_scaled_tube_setwise_of_row_testing {d : ℕ}
    (lam : ℝ) (hlam : lam ≠ 0) (h : ℝ) (hh : 0 ≤ h)
    (U V : Set (Vec d)) (hU : IsOpen U) (hV : IsOpen V)
    (P : Measure (Path d)) [IsFiniteMeasure P] (c : ℝ) (hc : 0 ≤ c)
    (htest : ∀ f : C_c(Vec d, ℝ), (∀ x, 0 ≤ f x) →
      tsupport f ⊆ (fun x : Vec d => lam • x) ⁻¹' V →
      (c * |lam| ^ d) * ∫ x, f x ∂(volume : Measure (Vec d)) ≤
        ∫ x, f x ∂((P.restrict {Y | (((h / lam ^ 2).toNNReal : ℝ≥0∞) <
          localityExitTime ((fun x : Vec d => lam • x) ⁻¹' U) Y)}).map
            (pathPosition (h / lam ^ 2).toNNReal)))
    (A : Set (Vec d)) (hA : MeasurableSet A) (hAV : A ⊆ V) :
    ENNReal.ofReal c * volume A ≤ P {Y | (∀ u : ℝ≥0, (u : ℝ) ≤ h →
      lam • Y ((u : ℝ) / lam ^ 2).toNNReal ∈ U) ∧
      lam • Y (h / lam ^ 2).toNNReal ∈ A} := by
  let t : ℝ≥0 := (h / lam ^ 2).toNNReal
  let S : Set (Path d) := {Y | (t : ℝ≥0∞) <
    localityExitTime ((fun x : Vec d => lam • x) ⁻¹' U) Y}
  let ν : Measure (Vec d) := (P.restrict S).map (pathPosition t)
  have hm : Measurable (fun x : Vec d => lam • x) :=
    (continuous_id.const_smul lam).measurable
  have hopen : IsOpen ((fun x : Vec d => lam • x) ⁻¹' V) :=
    hV.preimage (continuous_id.const_smul lam)
  have hbound := b_euclidean_setwise_of_compact_tests ν _ hopen (c * |lam| ^ d)
    (mul_nonneg hc (pow_nonneg (abs_nonneg _) _)) (by simpa [ν, S, t] using htest)
    ((fun x : Vec d => lam • x) ⁻¹' A) (hA.preimage hm)
    (Set.preimage_mono hAV)
  have hvolume : volume ((fun x : Vec d => lam • x) ⁻¹' A) =
      ENNReal.ofReal |(lam ^ d)⁻¹| * volume A := by
    simpa only [Module.finrank_pi, Fintype.card_fin] using
      (Measure.addHaar_preimage_smul (volume : Measure (Vec d)) hlam A)
  have hcoeff : ENNReal.ofReal (c * |lam| ^ d) * ENNReal.ofReal |(lam ^ d)⁻¹| =
      ENNReal.ofReal c := by
    rw [← ENNReal.ofReal_mul (mul_nonneg hc (pow_nonneg (abs_nonneg _) _))]
    congr 1
    rw [abs_inv, abs_pow, mul_assoc,
      mul_inv_cancel₀ (pow_ne_zero _ (abs_ne_zero.mpr hlam)), mul_one]
  have hevent : ν ((fun x : Vec d => lam • x) ⁻¹' A) =
      P {Y | (∀ u : ℝ≥0, (u : ℝ) ≤ h →
        lam • Y ((u : ℝ) / lam ^ 2).toNNReal ∈ U) ∧
        lam • Y (h / lam ^ 2).toNNReal ∈ A} := by
    dsimp only [ν]
    rw [Measure.map_apply (measurable_pathPosition t) (hA.preimage hm),
      Measure.restrict_apply ((hA.preimage hm).preimage (measurable_pathPosition t))]
    congr 1
    ext Y
    change (lam • Y t ∈ A ∧ (t : ℝ≥0∞) <
      localityExitTime ((fun x : Vec d => lam • x) ⁻¹' U) Y) ↔ _
    rw [and_comm]
    exact and_congr (b_signed_rescaled_survival_iff lam hlam U hU h hh Y) Iff.rfl
  calc
    ENNReal.ofReal c * volume A =
        (ENNReal.ofReal (c * |lam| ^ d) * ENNReal.ofReal |(lam ^ d)⁻¹|) * volume A := by
          rw [hcoeff]
    _ = ENNReal.ofReal (c * |lam| ^ d) *
        volume ((fun x : Vec d => lam • x) ⁻¹' A) := by rw [hvolume, mul_assoc]
    _ ≤ ν ((fun x : Vec d => lam • x) ⁻¹' A) := hbound
    _ = _ := hevent

/-- The conditional compact-test estimate for the actual signed regular path
law gives the setwise one-step hypothesis used in tube chaining. -/
theorem b_signed_regular_tube_setwise_of_row_testing {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (hlam : lam ≠ 0) (h : ℝ) (hh : 0 ≤ h)
    (U V : Set (Vec d)) (hU : IsOpen U) (hV : IsOpen V)
    (start : Vec d) (c : ℝ) (hc : 0 ≤ c)
    (htest : ∀ f : C_c(Vec d, ℝ), (∀ x, 0 ≤ f x) →
      tsupport f ⊆ (fun x : Vec d => lam • x) ⁻¹' V →
      (c * |lam| ^ d) * ∫ x, f x ∂(volume : Measure (Vec d)) ≤
        ∫ x, f x ∂((((s4SignedRegularPathLaw hd ω lam Λ hΛ hω) start).restrict
          {Y | (((h / lam ^ 2).toNNReal : ℝ≥0∞) <
            localityExitTime ((fun x : Vec d => lam • x) ⁻¹' U) Y)}).map
              (pathPosition (h / lam ^ 2).toNNReal)))
    (A : Set (Vec d)) (hA : MeasurableSet A) (hAV : A ⊆ V) :
    ENNReal.ofReal c * volume A ≤
      (s4SignedRegularPathLaw hd ω lam Λ hΛ hω) start
        {Y | (∀ u : ℝ≥0, (u : ℝ) ≤ h →
          lam • Y ((u : ℝ) / lam ^ 2).toNNReal ∈ U) ∧
          lam • Y (h / lam ^ 2).toNNReal ∈ A} := by
  letI : IsMarkovKernel (s4SignedRegularPathLaw hd ω lam Λ hΛ hω) :=
    s4_signed_regular_pathLaw_markov hd ω lam Λ hΛ hω
  exact b_signed_scaled_tube_setwise_of_row_testing lam hlam h hh U V hU hV
    ((s4SignedRegularPathLaw hd ω lam Λ hΛ hω) start) c hc htest A hA hAV


/-- Uniform compact-test lower bounds for the actual killed rows along the two
Section 3 tubes. The constant precedes the environment law and force. -/
noncomputable def bTubeCompactRowTestingInput : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ l : ℝ), 0 < l →
    let i := Regeneration.Renewal.forceCoord hd
    let ε := l / 32
    let γ₂ : ℝ → Vec d := fun u =>
      min ((25 * l / 4) * u) (25 * l / 8) • unitVector i
    let γ₃ : ℝ → Vec d := fun u => if u ≤ 1 then 0 else γ₂ (u - 1)
    let γ : ℕ → ℝ → Vec d := fun j => if j = 2 then γ₂ else γ₃
    ∀ (B C : ℝ) (N : ℕ), 0 < B → 1 ≤ C → 0 < N →
      (∀ j : ℕ, j = 2 ∨ j = 3 →
        let h : ℝ := ((j : ℝ) - 1) / N
        0 < h ∧ (N : ℝ) * h = (j : ℝ) - 1 ∧
        (∀ u : ℝ, 0 ≤ u → u ≤ (j : ℝ) - 1 →
          euclideanNorm (γ j u) + ε < B) ∧
        (∀ k : ℕ, k < N → ∀ u : ℝ,
          (k : ℝ) * h ≤ u → u ≤ (k + 1 : ℕ) * h →
          euclideanNorm (γ j u - γ j ((k : ℝ) * h)) ≤ ε / 16)) →
      ∃ cstar : ℝ, 0 < cstar ∧
      ∀ (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
        (P : QuenchedPathLaws d),
      IsGMPReducedKernel hd Q.ellipticity_parameter Q lam h₀.le h₁ P →
      ∀ᵐ ω ∂Q.measure, ∀ j : ℕ, j = 2 ∨ j = 3 →
        let h : ℝ := ((j : ℝ) - 1) / N
        let c : ℕ → Vec d := fun k => γ j ((k : ℝ) * h)
        ∀ k : ℕ, k < N → ∀ x : Vec d,
          euclideanNorm (x - c k) < ε / 16 →
          ∀ f : C_c(Vec d, ℝ), (∀ y, 0 ≤ f y) →
            tsupport f ⊆ (fun y : Vec d => lam • y) ⁻¹'
              {y | euclideanNorm (y - c (k + 1)) < ε / 16} →
            (cstar * |lam| ^ d) * ∫ y, f y ∂(volume : Measure (Vec d)) ≤
              ∫ y, f y ∂(((P (lam⁻¹ • x, ω)).restrict
                {Y | (((h / lam ^ 2).toNNReal : ℝ≥0∞) < localityExitTime
                  ((fun y : Vec d => lam • y) ⁻¹'
                    {y | euclideanNorm (y - c k) < ε / 2}) Y)}).map
                    (pathPosition (h / lam ^ 2).toNNReal))

/-- Compact-test bounds imply the actual setwise hypotheses for both tubes. -/
theorem b_tube_killed_endpoint_of_compact_row_testing
    (hrows : bTubeCompactRowTestingInput) : s3TubeKilledEndpointInput := by
  dsimp only [s3TubeKilledEndpointInput]
  intro d hd Λ₀ r₀ l hl B C N hB hC hN hgeom
  obtain ⟨cstar, hc, htests⟩ := hrows d hd Λ₀ r₀ l hl B C N hB hC hN hgeom
  refine ⟨cstar, hc, ?_⟩
  intro Q lam h₀ h₁ P hP
  filter_upwards [htests Q lam h₀ h₁ P hP, hP] with ω htestsω hreal
  obtain ⟨hω, G, hG⟩ := hreal
  intro j hj k hk x hx A hA hAV
  letI : IsFiniteMeasure (P (lam⁻¹ • x, ω)) := by
    rw [hG]
    letI := G.pathLaw_isMarkovKernel
    infer_instance
  have hopen (z : Vec d) (r : ℝ) : IsOpen {y : Vec d | euclideanNorm (y - z) < r} :=
    isOpen_lt ((Calculus.Feller.continuous_euclideanNorm d).comp
      (continuous_id.sub continuous_const)) continuous_const
  simpa only [Set.mem_setOf_eq] using
    (b_signed_scaled_tube_setwise_of_row_testing lam h₀.ne' _ (hgeom j hj).1.le
      _ _ (hopen _ _) (hopen _ _) (P (lam⁻¹ • x, ω)) cstar hc.le
      (htestsω j hj k hk x hx) A hA hAV)

/-- The Section 3 source tube follows conditionally from compact-test bounds. -/
theorem b_tube_probability_of_compact_row_testing
    (hrows : bTubeCompactRowTestingInput) :
    Blueprint.node_rt_u3A_renewal_u23_tube_u2D_probabilityStmt :=
  s3_tube_probability_of_killed_endpoint (b_tube_killed_endpoint_of_compact_row_testing hrows)

end EinsteinFull
