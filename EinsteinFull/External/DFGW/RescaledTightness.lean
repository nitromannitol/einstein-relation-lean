import EinsteinFull.External.DFGW.ScaleTransfer
import LatticeProb.Prob.PathModulusContinuity

/-! # Tightness of the diffusively rescaled path laws

Coordinatewise moduli of continuity at small scales, continuity of the paths at scales bounded
away from zero, and a common starting point give one compact set of continuous paths carrying all
but a prescribed mass of every rescaled law and of the limit law (Arzelà–Ascoli, through
`LatticeProb.isTightMeasureSet_of_pathModuli`).
-/

open MeasureTheory ProbabilityTheory Filter EinsteinRelation
open scoped NNReal ENNReal Topology

namespace EinsteinFull.External.DFGW

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {d : ℕ}

/-- The rescaled path depends measurably on a measurable continuous path. -/
theorem measurable_rescalePath_comp {Y : Ω → Path d} (hY : Measurable Y) (ε : ℝ) :
    Measurable fun ω => rescalePath ε (Y ω) := by
  apply ContinuousMap.measurable_iff_eval.2
  intro t
  exact ((continuous_eval_const _).measurable.comp hY).const_smul ε

/-- At scales bounded away from zero, the rescaled path laws have uniformly small modulus
events, by continuity of the paths of the single law of `Y`. -/
theorem exists_pathModulusFailure_le_of_le_scale [IsProbabilityMeasure P] {Y : Ω → Path d}
    (hY : Measurable Y) {ε₁ L κ : ℝ} (hε₁ : 0 < ε₁) (hL : 0 < L) (hκ : 0 < κ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, ε₁ ≤ ε → ε ≤ 1 →
      (P.map fun ω => rescalePath ε (Y ω)) (LatticeProb.pathModulusFailure L δ.toNNReal) ≤
        ENNReal.ofReal κ := by
  let L' : ℝ := max L (ε₁⁻¹ ^ 2 * L)
  have hL' : 0 < L' := lt_of_lt_of_le hL (le_max_left _ _)
  let ν : Measure (Path d) := P.map Y
  have : IsProbabilityMeasure ν := (Measure.isProbabilityMeasure_map_iff hY.aemeasurable).2
    inferInstance
  have hlim := LatticeProb.tendsto_measure_pathModulusFailure (E := Vec d) ν hL'
  obtain ⟨δ', hδ', hδ'pos⟩ := ((hlim.eventually
    (Iic_mem_nhds (ENNReal.ofReal_pos.2 hκ))).and self_mem_nhdsWithin).exists
  have hδ'pos : 0 < δ' := hδ'pos
  have hc₁ : 0 < ε₁⁻¹ ^ 2 := by positivity
  refine ⟨δ' / ε₁⁻¹ ^ 2, div_pos hδ'pos hc₁, fun ε hε₁ε hε1 => ?_⟩
  have hε : 0 < ε := hε₁.trans_le hε₁ε
  have hmeasA := (LatticeProb.isOpen_pathModulusFailure (E := Vec d) L
    (δ' / ε₁⁻¹ ^ 2).toNNReal).measurableSet
  have hmeasB := (LatticeProb.isOpen_pathModulusFailure (E := Vec d) L' δ'.toNNReal).measurableSet
  rw [Measure.map_apply (measurable_rescalePath_comp hY ε) hmeasA]
  refine le_trans (measure_mono ?_) ((Measure.map_apply hY hmeasB).symm.le.trans hδ')
  rintro ω ⟨s, t, hs, ht, hst, hlt⟩
  set c : ℝ := ε⁻¹ ^ 2 with hc
  have hcpos : 0 < c := by positivity
  have hcle : c ≤ ε₁⁻¹ ^ 2 := by
    have h1 : ε⁻¹ ≤ ε₁⁻¹ := inv_anti₀ hε₁ hε₁ε
    exact pow_le_pow_left₀ (inv_nonneg.2 hε.le) h1 2
  have hcoe (v : ℝ≥0) : ((c.toNNReal * v : ℝ≥0) : ℝ) = c * v := by
    rw [NNReal.coe_mul, Real.coe_toNNReal _ hcpos.le]
  refine ⟨c.toNNReal * s, c.toNNReal * t, ?_, ?_, ?_, ?_⟩
  · rw [hcoe]
    calc
      c * s ≤ ε₁⁻¹ ^ 2 * L := mul_le_mul hcle hs s.coe_nonneg hc₁.le
      _ ≤ L' := le_max_right _ _
  · rw [hcoe]
    calc
      c * t ≤ ε₁⁻¹ ^ 2 * L := mul_le_mul hcle ht t.coe_nonneg hc₁.le
      _ ≤ L' := le_max_right _ _
  · rw [hcoe, hcoe, ← mul_sub, abs_mul, abs_of_pos hcpos, Real.coe_toNNReal _ hδ'pos.le]
    rw [Real.coe_toNNReal _ (div_pos hδ'pos hc₁).le] at hst
    calc
      c * |(s : ℝ) - t| ≤ ε₁⁻¹ ^ 2 * (δ' / ε₁⁻¹ ^ 2) :=
        mul_le_mul hcle hst (abs_nonneg _) hc₁.le
      _ = δ' := by field_simp
  · have hdist : dist (rescalePath ε (Y ω) s) (rescalePath ε (Y ω) t) =
        ε * dist (Y ω (c.toNNReal * s)) (Y ω (c.toNNReal * t)) := by
      change dist (ε • Y ω ((ε⁻¹ ^ 2).toNNReal * s)) (ε • Y ω ((ε⁻¹ ^ 2).toNNReal * t)) = _
      rw [dist_smul₀, Real.norm_eq_abs, abs_of_pos hε]
    rw [hdist] at hlt
    have hLL : 1 / L' ≤ 1 / L := one_div_le_one_div_of_le hL (le_max_left _ _)
    have hd := dist_nonneg (x := Y ω (c.toNNReal * s)) (y := Y ω (c.toNNReal * t))
    nlinarith

/-- A positive lower bound for finitely many positive numbers, at most one. -/
theorem exists_pos_le_forall_fin (f : Fin d → ℝ) (hf : ∀ i, 0 < f i) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ ∀ i, c ≤ f i := by
  classical
  let s : Finset ℝ := Finset.univ.image f ∪ {1}
  have hs : s.Nonempty := ⟨1, by simp [s]⟩
  refine ⟨s.min' hs, ?_, Finset.min'_le _ _ (by simp [s]), fun i =>
    Finset.min'_le _ _ (by simp [s])⟩
  rw [Finset.lt_min'_iff]
  intro y hy
  simp only [s, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and,
    Finset.mem_singleton] at hy
  rcases hy with ⟨i, rfl⟩ | rfl
  · exact hf i
  · exact one_pos

/-- **Tightness of the rescaled laws.** Suppose that for every coordinate, horizon `L ≥ 1` and
`ρ, κ > 0` the rescaled coordinate paths have oscillation larger than `ρ` at some scale `δ` on
`[0, L]` with probability at most `κ`, uniformly in all small scales, that the paths start at the
origin, and that the limit law starts at the origin. Then for every `δ > 0` one compact set of
paths carries all but `δ` of the limit law and of the rescaled laws at all small scales. -/
theorem exists_isCompact_rescaled_laws [IsProbabilityMeasure P] {Y : Ω → Path d}
    (hY : Measurable Y) (hY0 : ∀ᵐ ω ∂P, Y ω 0 = 0)
    (hosc : ∀ (i : Fin d) {L ρ κ : ℝ}, 1 ≤ L → 0 < ρ → 0 < κ →
      ∃ δ : ℝ, 0 < δ ∧ ∃ ε₁ : ℝ, 0 < ε₁ ∧ ε₁ ≤ 1 ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₁ →
        P.real {ω | ∃ s t : ℝ≥0, (s : ℝ) ≤ L ∧ (t : ℝ) ≤ L ∧ |(s : ℝ) - t| ≤ δ ∧
          ρ < |rescalePath ε (Y ω) s i - rescalePath ε (Y ω) t i|} ≤ κ)
    (W : Measure (Path d)) [IsProbabilityMeasure W] (hW0 : ∀ᵐ γ ∂W, γ 0 = 0) :
    ∀ δ : ℝ, 0 < δ → ∃ K : Set (Path d), IsCompact K ∧ W Kᶜ ≤ ENNReal.ofReal δ ∧
      ∀ᶠ ε : ℝ in 𝓝[>] 0, (P.map fun ω => rescalePath ε (Y ω)) Kᶜ ≤ ENNReal.ofReal δ := by
  let Q : ℝ → Measure (Path d) := fun ε => P.map fun ω => rescalePath ε (Y ω)
  let S : Set (Measure (Path d)) := insert W (Q '' Set.Ioc 0 1)
  have hstart : ∀ ζ : ℝ, 0 < ζ → ∃ R : ℝ, ∀ μ ∈ S,
      μ {f : C(ℝ≥0, Vec d) | R < dist (f 0) 0} ≤ ENNReal.ofReal ζ := by
    intro ζ _
    refine ⟨0, fun μ hμ => ?_⟩
    have hopen : MeasurableSet {f : C(ℝ≥0, Vec d) | 0 < dist (f 0) 0} :=
      (isOpen_lt continuous_const
        ((continuous_eval_const (0 : ℝ≥0)).dist continuous_const)).measurableSet
    have hzero : μ {f : C(ℝ≥0, Vec d) | 0 < dist (f 0) 0} = 0 := by
      rcases hμ with rfl | ⟨ε, _, rfl⟩
      · apply measure_mono_null _ (ae_iff.1 hW0)
        intro f hf hf0
        simp only [Set.mem_ofPred_eq, hf0, dist_self, lt_self_iff_false] at hf
      · change (P.map fun ω => rescalePath ε (Y ω)) _ = 0
        rw [Measure.map_apply (measurable_rescalePath_comp hY ε) hopen]
        apply measure_mono_null _ (ae_iff.1 hY0)
        intro ω hω hω0
        have h0 : rescalePath ε (Y ω) 0 = 0 := by
          change ε • Y ω ((ε⁻¹ ^ 2).toNNReal * 0) = 0
          rw [mul_zero, hω0, smul_zero]
        simp only [Set.mem_preimage, Set.mem_ofPred_eq, h0, dist_self,
          lt_self_iff_false] at hω
    rw [hzero]
    exact zero_le
  have hmod : ∀ L : ℝ, 0 < L → ∃ δ : ℝ≥0, 0 < δ ∧ ∀ μ ∈ S,
      μ (LatticeProb.pathModulusFailure L δ) ≤ ENNReal.ofReal (1 / L) := by
    intro L hL
    let L₁ : ℝ := max L 1
    let κ : ℝ := (1 / L) / (d + 1)
    have hκ : 0 < κ := by positivity
    choose δf hδf ε₁f hε₁f _ hbound using fun i : Fin d =>
      hosc i (L := L₁) (ρ := 1 / L) (κ := κ) (le_max_right _ _) (by positivity) hκ
    obtain ⟨δ₁, hδ₁, _, hδ₁le⟩ := exists_pos_le_forall_fin δf hδf
    obtain ⟨ε₁, hε₁, _, hε₁le⟩ := exists_pos_le_forall_fin ε₁f hε₁f
    obtain ⟨δ₂, hδ₂, hlarge⟩ := exists_pathModulusFailure_le_of_le_scale (P := P) hY hε₁ hL
      (show 0 < 1 / L by positivity)
    have hWlim := LatticeProb.tendsto_measure_pathModulusFailure (E := Vec d) W hL
    obtain ⟨δ₃, hδ₃, hδ₃pos⟩ := ((hWlim.eventually
      (Iic_mem_nhds (ENNReal.ofReal_pos.2 (show 0 < 1 / L by positivity)))).and
        self_mem_nhdsWithin).exists
    have hδ₃pos : 0 < δ₃ := hδ₃pos
    let δ : ℝ := min δ₁ (min δ₂ δ₃)
    have hδ : 0 < δ := lt_min hδ₁ (lt_min hδ₂ hδ₃pos)
    refine ⟨δ.toNNReal, Real.toNNReal_pos.2 hδ, ?_⟩
    have hmono {δ' : ℝ} (h : δ ≤ δ') (μ : Measure (Path d)) :
        μ (LatticeProb.pathModulusFailure L δ.toNNReal) ≤
          μ (LatticeProb.pathModulusFailure L δ'.toNNReal) :=
      measure_mono (LatticeProb.pathModulusFailure_mono_scale L (Real.toNNReal_le_toNNReal h))
    rintro μ (rfl | ⟨ε, ⟨hε0, hε1⟩, rfl⟩)
    · exact (hmono ((min_le_right _ _).trans (min_le_right _ _)) μ).trans hδ₃
    · by_cases hεs : ε ≤ ε₁
      · let E : Fin d → Set Ω := fun i => {ω | ∃ s t : ℝ≥0, (s : ℝ) ≤ L₁ ∧ (t : ℝ) ≤ L₁ ∧
          |(s : ℝ) - t| ≤ δf i ∧
          1 / L < |rescalePath ε (Y ω) s i - rescalePath ε (Y ω) t i|}
        have hsub : (fun ω => rescalePath ε (Y ω)) ⁻¹'
            LatticeProb.pathModulusFailure L δ.toNNReal ⊆ ⋃ i, E i := by
          rintro ω ⟨s, t, hs, ht, hst, hlt⟩
          have hex : ∃ i, 1 / L < dist (rescalePath ε (Y ω) s i)
              (rescalePath ε (Y ω) t i) := by
            by_contra hnone
            push Not at hnone
            have h := (dist_pi_le_iff (show (0 : ℝ) ≤ 1 / L by positivity)).2 hnone
            linarith
          obtain ⟨i, hi⟩ := hex
          rw [Real.dist_eq] at hi
          refine Set.mem_iUnion.2 ⟨i, s, t, hs.trans (le_max_left _ _),
            ht.trans (le_max_left _ _), ?_, hi⟩
          rw [Real.coe_toNNReal _ hδ.le] at hst
          exact hst.trans ((min_le_left _ _).trans (hδ₁le i))
        have hE (i : Fin d) : P (E i) ≤ ENNReal.ofReal κ := by
          rw [ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) hκ.le]
          exact hbound i ε hε0 (hεs.trans (hε₁le i))
        change (P.map fun ω => rescalePath ε (Y ω)) _ ≤ _
        rw [Measure.map_apply (measurable_rescalePath_comp hY ε)
          (LatticeProb.isOpen_pathModulusFailure (E := Vec d) L δ.toNNReal).measurableSet]
        calc
          _ ≤ P (⋃ i, E i) := measure_mono hsub
          _ ≤ ∑ i, P (E i) := measure_iUnion_fintype_le _ _
          _ ≤ ∑ _i : Fin d, ENNReal.ofReal κ := Finset.sum_le_sum fun i _ => hE i
          _ = ENNReal.ofReal (d * κ) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
              ENNReal.ofReal_mul (Nat.cast_nonneg d), ENNReal.ofReal_natCast]
          _ ≤ ENNReal.ofReal (1 / L) := by
            apply ENNReal.ofReal_le_ofReal
            have hd : (d : ℝ) / (d + 1) ≤ 1 := by
              rw [div_le_one (by positivity)]
              linarith
            calc
              (d : ℝ) * κ = (d : ℝ) / (d + 1) * (1 / L) := by
                dsimp only [κ]
                ring
              _ ≤ 1 * (1 / L) := mul_le_mul_of_nonneg_right hd (by positivity)
              _ = 1 / L := one_mul _
      · push Not at hεs
        exact (hmono ((min_le_right _ _).trans (min_le_left _ _)) _).trans
          (hlarge ε hεs.le hε1)
  have hT : IsTightMeasureSet S := LatticeProb.isTightMeasureSet_of_pathModuli S 0 hstart hmod
  intro δ hδ
  obtain ⟨K, hK, hKS⟩ := isTightMeasureSet_iff_exists_isCompact_measure_compl_le.1 hT
    (ENNReal.ofReal δ) (ENNReal.ofReal_pos.2 hδ)
  refine ⟨K, hK, hKS W (Set.mem_insert _ _), ?_⟩
  filter_upwards [Ioc_mem_nhdsGT one_pos] with ε hε
  exact hKS (Q ε) (Set.mem_insert_of_mem _ ⟨ε, hε, rfl⟩)

end EinsteinFull.External.DFGW
