import EinsteinFull.Blueprint.G1.Proofs.S3MRenewal
import EinsteinFull.Blueprint.G1.Draft.SbxCPhaseSmoothR01
import EinsteinFull.Blueprint.Foundation.Draft.SbxCFactorizationSmoothR01

/-! Draft uniform m-renewal consumer, conditional on smooth factorization. -/
open MeasureTheory
open scoped NNReal ENNReal
namespace EinsteinFull.Blueprint.SbxCMRenewalUniformR06
open EinsteinRelation EinsteinFull.Blueprint
open EinsteinRelation.Regeneration (CoupledSample sampleTimeShift pathTimeShift
  forcedBitTrialEvent NoBacktracking finiteHistorySigma firstRegenerationTime couplingRegion
  gridIndex recenterSample)

def phaseMRenewalSmoothStmt : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ) (hΛ : 1 ≤ Λ₀) (hr : 1 ≤ r₀) (l δ : ℝ)
    (_hl : 0 < l) (_hsep : r₀ < 2 * l) (_hδ₀ : 0 < δ) (_hδ₁ : δ < 1),
  ∃ C : ℝ, 0 < C ∧
  ∀ (β : ℕ → ℝ) (hβ : ∀ k, 1 ≤ k → 0 < β k),
  let D : StructuralData d := ⟨Λ₀, r₀, β, hΛ, hr, hβ⟩
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

/-- The m-renewal statement follows from smooth environmental factorization. -/
theorem mRenewal_of_smooth_factorization
    (hfact : SbxCFactorizationR01.environmentalFactorizationSmoothStmt) :
    phaseMRenewalSmoothStmt := by
  classical
  intro d hd Λ₀ r₀ hΛ hr₀ l δ hl hsep hδ₀ hδ₁
  refine ⟨3 + 1 / l, by positivity, ?_⟩
  intro β hβ
  dsimp only
  let SD : StructuralData d := ⟨Λ₀, r₀, β, hΛ, hr₀, hβ⟩
  intro Q hQ lam h₀ h₁ P K hK
  intro hD A hA
  obtain ⟨m, hmdef⟩ : ∃ m : ℕ, m = max 1 ⌈(A / l - 1) / 10⌉₊ := ⟨_, rfl⟩
  rw [← hmdef]
  have hm1 : 1 ≤ m := by rw [hmdef]; exact le_max_left _ _
  have hΔ : 0 < Regeneration.Renewal.regenDelta lam :=
    Real.toNNReal_pos.mpr (inv_pos.mpr (sq_pos_of_pos h₀))
  have hR : 0 < l / lam := div_pos hl h₀
  have hA0 : 0 ≤ A := by linarith
  refine ⟨?_, ?_⟩
  · have hx0 : 0 ≤ (A / l - 1) / 10 := by
      have : 1 ≤ A / l := by rw [le_div_iff₀ hl]; linarith
      linarith
    have hceil : (⌈(A / l - 1) / 10⌉₊ : ℝ) < (A / l - 1) / 10 + 1 := Nat.ceil_lt_add_one hx0
    have hk' : (m : ℝ) ≤ (A / l - 1) / 10 + 1 := by
      rw [hmdef, Nat.cast_max]
      exact max_le (by simp only [Nat.cast_one]; linarith) hceil.le
    have hu : 0 ≤ 1 / l := by positivity
    have hAl : A / l = A * (1 / l) := by ring
    nlinarith [mul_nonneg hA0 hu]
  · intro G hGloc hbG t
    have hs := sliceChar_of_slices hd Q lam h₀ h₁ l δ hl hsep hδ₀ hδ₁ P K hK
    obtain ⟨D, hDm, hDr⟩ :=
      Probability.exists_future_halfSpace_decoder (Regeneration.Renewal.forceCoord hd) (l / lam)
    have hρ : A / lam ≤ (10 * (m : ℝ) + 1) * (l / lam) := by
      have hxk : (A / l - 1) / 10 ≤ (m : ℝ) := by
        have h5 : (⌈(A / l - 1) / 10⌉₊ : ℝ) ≤ (m : ℝ) := by
          rw [hmdef]
          exact_mod_cast le_max_right _ _
        exact (Nat.le_ceil _).trans h5
      calc A / lam = (A / l) * (l / lam) := by field_simp
        _ ≤ (10 * (m : ℝ) + 1) * (l / lam) :=
          mul_le_mul_of_nonneg_right (by linarith) (div_nonneg hl.le h₀.le)
    haveI hμprob : IsProbabilityMeasure (Regeneration.annealedCoupledLaw Q.measure K) :=
      Regeneration.annealedCoupledLaw_isProbabilityMeasure Q.measure K hK.1
    haveI hνprob : IsProbabilityMeasure (regenerationConditionedLaw hd Q lam l K hK.1 hD) :=
      ProbabilityTheory.cond_isProbabilityMeasure hD
    have hac : regenerationConditionedLaw hd Q lam l K hK.1 hD ≪
        Regeneration.annealedCoupledLaw Q.measure K :=
      ProbabilityTheory.cond_absolutelyContinuous
    have hgain := hac.ae_le (ae_gain_annealed hd Q lam h₀ h₁ l δ P K hK)
    have hstart := hac.ae_le
      (Regeneration.ae_origin_start_of_isGMPReducedKernel hd Q lam h₀.le h₁ P K hK.1 hK.2.1
        hK.2.2.1)
    have hGg : Measurable G := hGloc.mono (Probability.localSigma_le_borel _) le_rfl
    have hobsm : ∀ u : ℝ≥0, Measurable (fun q : FieldPair d × CoupledSample d =>
        G (translate (q.2.1 u) (reduce q.1))) := fun u =>
      hGg.comp (Probability.continuous_translate.measurable.comp
        ((((continuous_eval_const u).measurable).comp measurable_snd.fst).prodMk
          (Probability.measurable_reduce.comp measurable_fst)))
    obtain ⟨CG, hCG⟩ := hbG
    have hobsint : ∀ u : ℝ≥0, Integrable (fun q : FieldPair d × CoupledSample d =>
        G (translate (q.2.1 u) (reduce q.1))) (regenerationConditionedLaw hd Q lam l K hK.1 hD) :=
      fun u => Integrable.of_bound (hobsm u).aestronglyMeasurable CG
        (ae_of_all _ fun q => by rw [Real.norm_eq_abs]; exact hCG _)
    have hmeasτ : ∀ j : ℕ, Measurable (fun q : FieldPair d × CoupledSample d =>
        regenerationTime hd lam l j q.2) := fun j =>
      (Regeneration.measurable_regenerationTime (Regeneration.Renewal.regenDelta lam) lam
        (l / lam) (Regeneration.Renewal.forceCoord hd) j).comp measurable_snd
    -- the observable at the first record
    have hrec0 : ∀ u : ℝ≥0, ∀ᵐ q ∂regenerationConditionedLaw hd Q lam l K hK.1 hD,
        ({q : FieldPair d × CoupledSample d | regenerationTime hd lam l m q.2 ≤ (u : ℝ≥0∞)}.indicator
          (fun q => G (translate (q.2.1 u) (reduce q.1)))) q =
        PhiM (Regeneration.Renewal.regenDelta lam) lam (l / lam)
          (Regeneration.Renewal.forceCoord hd) D G m u (regenerationRecord hd lam l 0 q) := by
      intro u
      filter_upwards [hgain] with q hq
      have hrec : regenerationRecord hd lam l 0 q = Regeneration.futureRecord
          (Regeneration.Renewal.regenDelta lam) (l / lam) q.1 q.2
          (Regeneration.Renewal.forceCoord hd) 0 := by
        have h0 : Regeneration.regenerationTime (Regeneration.Renewal.regenDelta lam) lam
            (l / lam) q.2 (Regeneration.Renewal.forceCoord hd) 0 = 0 := rfl
        unfold regenerationRecord Regeneration.Renewal.cycleRecord
        rw [h0, ENNReal.toNNReal_zero]
      rw [hrec, PhiM_record _ hΔ lam (l / lam) (A / lam) h₀ hR _ hs D hDr G hGloc m hm1 hρ
        q.1 q.2 0 u (by rw [Regeneration.sampleTimeShift_zero]; exact hq),
        Regeneration.sampleTimeShift_zero, zero_add]
      by_cases h : regenerationTime hd lam l m q.2 ≤ (u : ℝ≥0∞)
      · have h' : Regeneration.regenerationTime (Regeneration.Renewal.regenDelta lam) lam
            (l / lam) q.2 (Regeneration.Renewal.forceCoord hd) m ≤ (u : ℝ≥0∞) := h
        rw [Set.indicator_of_mem (show q ∈ {q : FieldPair d × CoupledSample d |
          regenerationTime hd lam l m q.2 ≤ (u : ℝ≥0∞)} from h), if_pos h']
      · have h' : ¬ Regeneration.regenerationTime (Regeneration.Renewal.regenDelta lam) lam
            (l / lam) q.2 (Regeneration.Renewal.forceCoord hd) m ≤ (u : ℝ≥0∞) := h
        rw [Set.indicator_of_notMem (show q ∉ {q : FieldPair d × CoupledSample d |
          regenerationTime hd lam l m q.2 ≤ (u : ℝ≥0∞)} from h), if_neg h']
    refine ⟨⟨PhiM (Regeneration.Renewal.regenDelta lam) lam (l / lam)
      (Regeneration.Renewal.forceCoord hd) D G m t,
      measurable_PhiM _ lam _ (A / lam) _ D hDm G hGloc m t,
      boundedRealTest_PhiM _ lam _ _ D G ⟨CG, hCG⟩ m t, hrec0 t⟩, ?_, ?_⟩
    · -- the support of the observation
      filter_upwards [hgain, hstart] with q hq hq0 hτ x hx
      have hsup := support_after_regen (Regeneration.Renewal.regenDelta lam) hΔ lam (l / lam)
        h₀ hR (Regeneration.Renewal.forceCoord hd) hs m hm1 (A / lam) hρ q.2 hq t hτ
        (x - q.2.1 t) hx
      rw [hq0] at hsup
      simpa using hsup
    · -- the renewal equation
      set Δ := Regeneration.Renewal.regenDelta lam with hΔdef
      set ν := regenerationConditionedLaw hd Q lam l K hK.1 hD with hνdef
      let Em : ℝ≥0 → Set (FieldPair d × CoupledSample d) := fun u =>
        {q | regenerationTime hd lam l m q.2 ≤ (u : ℝ≥0∞)}
      let Em1 : Set (FieldPair d × CoupledSample d) :=
        {q | regenerationTime hd lam l (m + 1) q.2 ≤ (t : ℝ≥0∞)}
      let Emp : Set (FieldPair d × CoupledSample d) :=
        {q | regenerationTime hd lam l m q.2 ≤ (t : ℝ≥0∞) ∧
          (t : ℝ≥0∞) < regenerationTime hd lam l (m + 1) q.2}
      let slice : ℕ → Set (FieldPair d × CoupledSample d) := fun n =>
        {q | regenerationTime hd lam l 1 q.2 = (((n : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞)}
      have hEm : ∀ u, MeasurableSet (Em u) := fun u =>
        measurableSet_le (hmeasτ m) measurable_const
      have hEm1 : MeasurableSet Em1 := measurableSet_le (hmeasτ (m + 1)) measurable_const
      have hslice : ∀ n, MeasurableSet (slice n) := fun n =>
        measurableSet_eq_fun (hmeasτ 1) measurable_const
      have hunion : Em t = Emp ∪ Em1 := by
        ext q
        simp only [Em, Emp, Em1, Set.mem_setOf_eq, Set.mem_union]
        constructor
        · intro h
          by_cases h' : (t : ℝ≥0∞) < regenerationTime hd lam l (m + 1) q.2
          · exact Or.inl ⟨h, h'⟩
          · exact Or.inr (not_lt.mp h')
        · rintro (h | h)
          · exact h.1
          · exact (regenerationTime_le_succ Δ lam (l / lam) (Regeneration.Renewal.forceCoord hd)
              m q.2).trans h
      have hdisj : Disjoint Emp Em1 :=
        Set.disjoint_left.mpr fun q hq1 hq2 => absurd hq1.2 (not_lt.mpr hq2)
      have hA : (∫ q in Em t, G (translate (q.2.1 t) (reduce q.1)) ∂ν) =
          (∫ q in Emp, G (translate (q.2.1 t) (reduce q.1)) ∂ν) +
            ∫ q in Em1, G (translate (q.2.1 t) (reduce q.1)) ∂ν := by
        rw [hunion]
        exact setIntegral_union hdisj hEm1 (hobsint t).integrableOn (hobsint t).integrableOn
      have hcover : Em1 = ⋃ n ∈ Finset.range (⌊(t : ℝ) / (Δ : ℝ)⌋₊ + 1), (slice n ∩ Em1) := by
        ext q
        simp only [Set.mem_iUnion, Set.mem_inter_iff, Finset.mem_range, exists_prop]
        constructor
        · intro hq
          have hassoc := regenerationTime_succ_first Δ hΔ lam (l / lam)
            (Regeneration.Renewal.forceCoord hd) m q.2
          have hq' : Regeneration.regenerationTime Δ lam (l / lam) q.2
              (Regeneration.Renewal.forceCoord hd) (m + 1) ≤ (t : ℝ≥0∞) := hq
          rw [hassoc] at hq'
          have hFt := le_self_add.trans hq'
          have hFfin : firstRegenerationTime Δ lam (l / lam) q.2
              (Regeneration.Renewal.forceCoord hd) ≠ ⊤ :=
            ne_top_of_le_ne_top ENNReal.coe_ne_top hFt
          obtain ⟨n, hn⟩ := Regeneration.firstRegenerationTime_mem_grid Δ hΔ lam (l / lam) q.2
            (Regeneration.Renewal.forceCoord hd) hFfin
          rw [hn] at hFt
          have hnt : (n : ℝ≥0) * Δ ≤ t := ENNReal.coe_le_coe.mp hFt
          have hnr : (n : ℝ) ≤ (t : ℝ) / (Δ : ℝ) := by
            rw [le_div_iff₀ (by exact_mod_cast hΔ)]
            exact_mod_cast hnt
          refine ⟨n, Nat.lt_succ_of_le (Nat.le_floor hnr), ?_, hq⟩
          change Regeneration.regenerationTime Δ lam (l / lam) q.2
            (Regeneration.Renewal.forceCoord hd) 1 = _
          rw [Regeneration.regenerationTime_one]
          exact hn
        · rintro ⟨n, _, _, hq⟩
          exact hq
      have hB : (∫ q in Em1, G (translate (q.2.1 t) (reduce q.1)) ∂ν) =
          ∑ n ∈ Finset.range (⌊(t : ℝ) / (Δ : ℝ)⌋₊ + 1),
            ∫ q in slice n ∩ Em1, G (translate (q.2.1 t) (reduce q.1)) ∂ν := by
        have h := integral_biUnion_finset (μ := ν)
          (f := fun q : FieldPair d × CoupledSample d => G (translate (q.2.1 t) (reduce q.1)))
          (Finset.range (⌊(t : ℝ) / (Δ : ℝ)⌋₊ + 1)) (s := fun n => slice n ∩ Em1)
          (fun n _ => (hslice n).inter hEm1)
          (by
            intro n _ n' _ hne
            refine Set.disjoint_left.mpr fun q hq hq' => hne ?_
            have h1 : ((n : ℝ≥0) * Δ : ℝ≥0) = ((n' : ℝ≥0) * Δ : ℝ≥0) :=
              ENNReal.coe_injective (hq.1.symm.trans hq'.1)
            exact_mod_cast mul_right_cancel₀ hΔ.ne' h1)
          (fun n _ => (hobsint t).integrableOn)
        rw [← hcover] at h
        exact h
      have hC : ∀ n ∈ Finset.range (⌊(t : ℝ) / (Δ : ℝ)⌋₊ + 1),
          (∫ q in slice n ∩ Em1, G (translate (q.2.1 t) (reduce q.1)) ∂ν) =
            regenerationLatticeMass hd Q lam l K hK.1 hD n *
              ∫ q in Em (t - (n : ℝ≥0) * Δ),
                G (translate (q.2.1 (t - (n : ℝ≥0) * Δ)) (reduce q.1)) ∂ν := by
        intro n hn
        by_cases hn2 : n ≤ 1
        · have hempty : slice n = ∅ :=
            node_rt_u3A_factorization_u23_small_u2D_indices_of_deps d hd lam l h₀ hl n hn2
          have hp : regenerationLatticeMass hd Q lam l K hK.1 hD n = 0 := by
            unfold regenerationLatticeMass
            change ν.real (slice n) = 0
            rw [hempty]
            simp
          rw [hp, zero_mul, hempty, Set.empty_inter, Measure.restrict_empty,
            integral_zero_measure]
        · have hn' : 2 ≤ n := by omega
          have hnN : n ≤ ⌊(t : ℝ) / (Δ : ℝ)⌋₊ := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
          have hnt : (n : ℝ≥0) * Δ ≤ t := by
            have h1 : (n : ℝ) ≤ (t : ℝ) / (Δ : ℝ) :=
              (Nat.cast_le.mpr hnN).trans (Nat.floor_le (by positivity))
            have h2 : (n : ℝ) * (Δ : ℝ) ≤ (t : ℝ) := by
              rwa [le_div_iff₀ (by exact_mod_cast hΔ)] at h1
            exact_mod_cast h2
          set u : ℝ≥0 := t - (n : ℝ≥0) * Δ with hu
          have hpos : (n : ℝ≥0) * Δ + u = t := add_tsub_cancel_of_le hnt
          have hgain_n : ∀ᵐ q ∂ν, q ∈ slice n →
              (Em1.indicator (fun q => G (translate (q.2.1 t) (reduce q.1)))) q =
                PhiM Δ lam (l / lam) (Regeneration.Renewal.forceCoord hd) D G m u
                  (regenerationRecord hd lam l 1 q) := by
            filter_upwards [hgain] with q hq hmem
            have hτ1 : Regeneration.regenerationTime Δ lam (l / lam) q.2
                (Regeneration.Renewal.forceCoord hd) 1 = (((n : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞) := hmem
            have hF : firstRegenerationTime Δ lam (l / lam) q.2
                (Regeneration.Renewal.forceCoord hd) = (((n : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞) := by
              rwa [Regeneration.regenerationTime_one] at hτ1
            have hrec : regenerationRecord hd lam l 1 q = Regeneration.futureRecord Δ (l / lam)
                q.1 q.2 (Regeneration.Renewal.forceCoord hd) ((n : ℝ≥0) * Δ) := by
              unfold regenerationRecord Regeneration.Renewal.cycleRecord
              rw [hτ1, ENNReal.toNNReal_coe]
            rw [hrec, PhiM_record Δ hΔ lam (l / lam) (A / lam) h₀ hR _ hs D hDr G hGloc m hm1 hρ
              q.1 q.2 ((n : ℝ≥0) * Δ) u (gain_shift Δ hΔ (l / lam) _ q.2 n hq)]
            have hassoc := regenerationTime_succ_first Δ hΔ lam (l / lam)
              (Regeneration.Renewal.forceCoord hd) m q.2
            rw [hF, ENNReal.toNNReal_coe] at hassoc
            have hiff : regenerationTime hd lam l (m + 1) q.2 ≤ (t : ℝ≥0∞) ↔
                Regeneration.regenerationTime Δ lam (l / lam)
                  (sampleTimeShift Δ q.2 ((n : ℝ≥0) * Δ)) (Regeneration.Renewal.forceCoord hd) m ≤
                  (u : ℝ≥0∞) := by
              change Regeneration.regenerationTime Δ lam (l / lam) q.2
                (Regeneration.Renewal.forceCoord hd) (m + 1) ≤ _ ↔ _
              rw [hassoc]
              exact coe_add_le_coe_iff _ _ _ hnt
            by_cases h : regenerationTime hd lam l (m + 1) q.2 ≤ (t : ℝ≥0∞)
            · have h2 := hiff.mp h
              rw [Set.indicator_of_mem (show q ∈ Em1 from h), if_pos h2, hpos]
            · have h2 := fun h2 => h (hiff.mpr h2)
              rw [Set.indicator_of_notMem (show q ∉ Em1 from h), if_neg h2]
          have hfa := (hfact d hd SD Q hQ lam h₀ h₁ l δ hl hsep hδ₀ hδ₁ P K hK hD).1
            (fun _ => (1 : ℝ)) measurable_const ⟨1, fun _ => by norm_num⟩
            (PhiM Δ lam (l / lam) (Regeneration.Renewal.forceCoord hd) D G m u)
            (measurable_PhiM Δ lam (l / lam) (A / lam) _ D hDm G hGloc m u)
            (boundedRealTest_PhiM Δ lam (l / lam) _ D G ⟨CG, hCG⟩ m u) n ν
            (Set.mem_insert_of_mem _ (Set.mem_singleton _))
          have hrecu : (∫ q, PhiM Δ lam (l / lam) (Regeneration.Renewal.forceCoord hd) D G m u
              (regenerationRecord hd lam l 0 q) ∂ν) =
              ∫ q in Em u, G (translate (q.2.1 u) (reduce q.1)) ∂ν := by
            rw [← integral_indicator (hEm u)]
            exact (integral_congr_ae (hrec0 u)).symm
          have hmass : (∫ q in slice n, (1 : ℝ) ∂ν) =
              regenerationLatticeMass hd Q lam l K hK.1 hD n := by
            unfold regenerationLatticeMass
            change (∫ q in slice n, (1 : ℝ) ∂ν) = ν.real (slice n)
            rw [setIntegral_const, smul_eq_mul, mul_one]
          calc (∫ q in slice n ∩ Em1, G (translate (q.2.1 t) (reduce q.1)) ∂ν)
              = ∫ q in slice n,
                  (Em1.indicator (fun q => G (translate (q.2.1 t) (reduce q.1)))) q ∂ν :=
                (setIntegral_indicator hEm1).symm
            _ = ∫ q in slice n, 1 * PhiM Δ lam (l / lam) (Regeneration.Renewal.forceCoord hd) D G
                  m u (regenerationRecord hd lam l 1 q) ∂ν := by
                simp only [one_mul]
                exact setIntegral_congr_ae (hslice n)
                  (by filter_upwards [hgain_n] with q hq hmem; exact hq hmem)
            _ = (∫ q in slice n, (1 : ℝ) ∂ν) * ∫ q, PhiM Δ lam (l / lam)
                  (Regeneration.Renewal.forceCoord hd) D G m u
                  (regenerationRecord hd lam l 0 q) ∂ν := hfa
            _ = _ := by rw [hmass, hrecu]
      have hfinal : (∫ q in Em t, G (translate (q.2.1 t) (reduce q.1)) ∂ν) =
          (∫ q in Emp, G (translate (q.2.1 t) (reduce q.1)) ∂ν) +
            ∑ n ∈ Finset.range (⌊(t : ℝ) / (Δ : ℝ)⌋₊ + 1),
              regenerationLatticeMass hd Q lam l K hK.1 hD n *
                ∫ q in Em (t - (n : ℝ≥0) * Δ),
                  G (translate (q.2.1 (t - (n : ℝ≥0) * Δ)) (reduce q.1)) ∂ν := by
        rw [hA, hB, Finset.sum_congr rfl hC]
      exact hfinal

end EinsteinFull.Blueprint.SbxCMRenewalUniformR06
