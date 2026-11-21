import EinsteinFull.PhysicalRegeneration.Regeneration.AnnealedHistoryRestart
import EinsteinFull.PhysicalRegeneration.Calculus.C10S3StoppedTubeProducer
import EinsteinFull.Calculus.C10S3StoppedTubeProducer
import EinsteinFull.Regeneration.RecordCycleObservables
import EinsteinFull.Regeneration.AbsoluteWindowMaximum
import EinsteinFull.Work.W5.UniformLatticeRenewalProof
import EinsteinRelation.Regeneration.FirstRegenerationFiniteness

/-!
# Moments of the first regeneration cycle of the physical coupling

GMP 2012, Lemma 5.8 and the proof of Proposition 5.9: under the law conditioned on no return,
the first regeneration time and the maximal displacement up to it are integrable. The duration
is bounded by its exponential moment. The maximal displacement up to `τ₁ = Nλ⁻²` is at most the
sum of the maximal displacements over the windows `[kλ⁻², (k + 1)λ⁻²]`, `k < N`; each window
restarts at its grid time, where the window maximum has a uniform exponential moment, and the
window counts only on `τ₁ > kλ⁻²`, whose probability decays exponentially in `k`.
-/

open MeasureTheory ProbabilityTheory EinsteinRelation EinsteinRelation.Regeneration
open scoped NNReal ENNReal

attribute [local instance 2000] EinsteinRelation.instMeasurableSpaceMat

namespace EinsteinFull.Regeneration

variable {d : ℕ}

theorem abs_sub_le_absoluteCoordinateMaximum (j : Fin d) {t u : ℝ≥0} (hu : u ≤ t)
    (γ : Path d) : |γ u j - γ 0 j| ≤ absoluteCoordinateMaximum j t γ := by
  unfold absoluteCoordinateMaximum
  apply le_csSup
  · exact (isCompact_Icc.image (continuous_abs.comp
      (((continuous_apply j).comp γ.continuous).sub continuous_const))).bddAbove
  · exact ⟨u, ⟨zero_le, hu⟩, rfl⟩

/-- The maximal displacement up to `Nλ⁻²` is at most the sum of the maximal displacements over
the windows of length `λ⁻²` before it. -/
theorem absoluteCoordinateMaximum_le_sum_windows (j : Fin d) (Δ : ℝ≥0) (γ : Path d) (N : ℕ) :
    absoluteCoordinateMaximum j ((N : ℝ≥0) * Δ) γ ≤
      ∑ k ∈ Finset.range N, absoluteCoordinateMaximum j Δ (pathTimeShift γ ((k : ℝ≥0) * Δ)) := by
  have key : ∀ n : ℕ, ∀ u : ℝ≥0, u ≤ (n : ℝ≥0) * Δ → |γ u j - γ 0 j| ≤
      ∑ k ∈ Finset.range n, absoluteCoordinateMaximum j Δ (pathTimeShift γ ((k : ℝ≥0) * Δ)) := by
    intro n
    induction n with
    | zero =>
      intro u hu
      have hu0 : u = 0 := by simpa using hu
      subst hu0
      simp
    | succ n ih =>
      intro u hu
      rw [Finset.sum_range_succ]
      by_cases hun : u ≤ (n : ℝ≥0) * Δ
      · exact (ih u hun).trans (le_add_of_nonneg_right (absoluteCoordinateMaximum_nonneg _ _ _))
      · rw [not_le] at hun
        have hv : u - (n : ℝ≥0) * Δ ≤ Δ := by
          rw [tsub_le_iff_left]
          calc u ≤ ((n + 1 : ℕ) : ℝ≥0) * Δ := hu
            _ = (n : ℝ≥0) * Δ + Δ := by push_cast; ring
        have hu' : (n : ℝ≥0) * Δ + (u - (n : ℝ≥0) * Δ) = u := add_tsub_cancel_of_le hun.le
        have h1 : |γ u j - γ ((n : ℝ≥0) * Δ) j| ≤
            absoluteCoordinateMaximum j Δ (pathTimeShift γ ((n : ℝ≥0) * Δ)) := by
          have h := abs_sub_le_absoluteCoordinateMaximum j hv (pathTimeShift γ ((n : ℝ≥0) * Δ))
          have e1 : (pathTimeShift γ ((n : ℝ≥0) * Δ)) (u - (n : ℝ≥0) * Δ) = γ u := by
            change γ ((n : ℝ≥0) * Δ + (u - (n : ℝ≥0) * Δ)) = γ u
            rw [hu']
          have e0 : (pathTimeShift γ ((n : ℝ≥0) * Δ)) 0 = γ ((n : ℝ≥0) * Δ) := by
            change γ ((n : ℝ≥0) * Δ + 0) = _
            rw [add_zero]
          rw [e1, e0] at h
          exact h
        have h2 := ih ((n : ℝ≥0) * Δ) le_rfl
        calc |γ u j - γ 0 j|
            ≤ |γ u j - γ ((n : ℝ≥0) * Δ) j| + |γ ((n : ℝ≥0) * Δ) j - γ 0 j| :=
              abs_sub_le _ _ _
          _ ≤ _ := by linarith
  refine csSup_le ⟨_, ⟨0, ⟨le_rfl, zero_le⟩, rfl⟩⟩ ?_
  rintro _ ⟨u, ⟨_, hu⟩, rfl⟩
  exact key N u hu

theorem recordMaximum_iteratedRecord_zero (Δ : ℝ≥0) (lam R : ℝ) (i j : Fin d)
    (q : FieldPair d × CoupledSample d) :
    recordMaximum Δ lam R i j (iteratedRecord Δ lam R i 0 q) =
      absoluteCoordinateMaximum j (firstRegenerationTime Δ lam R q.2 i).toNNReal q.2.1 := by
  have h0 : EinsteinRelation.Regeneration.regenerationTime Δ lam R q.2 i 0 = 0 := rfl
  have h1 : firstRegenerationTime Δ lam R
      (recordSample (iteratedRecord Δ lam R i 0 q)) i = firstRegenerationTime Δ lam R q.2 i := by
    rw [firstRegenerationTime_iteratedRecord, h0, ENNReal.toNNReal_zero, sampleTimeShift_zero]
  simp only [recordMaximum]
  rw [h1]
  simp only [absoluteCoordinateMaximum, iteratedRecord, futureRecord, h0, ENNReal.toNNReal_zero,
    zero_add, ContinuousMap.coe_mk, Pi.sub_apply, sub_sub_sub_cancel_right]

theorem recordDuration_iteratedRecord_zero (Δ : ℝ≥0) (lam R : ℝ) (i : Fin d)
    (q : FieldPair d × CoupledSample d) :
    recordDuration Δ lam R i (iteratedRecord Δ lam R i 0 q) =
      ((firstRegenerationTime Δ lam R q.2 i).toNNReal : ℝ) := by
  have h0 : EinsteinRelation.Regeneration.regenerationTime Δ lam R q.2 i 0 = 0 := rfl
  have h1 : firstRegenerationTime Δ lam R
      (recordSample (iteratedRecord Δ lam R i 0 q)) i = firstRegenerationTime Δ lam R q.2 i := by
    rw [firstRegenerationTime_iteratedRecord, h0, ENNReal.toNNReal_zero, sampleTimeShift_zero]
  simp only [recordDuration]
  rw [h1]

/-- The first regeneration time is integrable under the conditioned law, from its exponential
moment. -/
theorem physical_record_duration_integrable {Λ₀ r₀ : ℝ} (hd : 2 ≤ d)
    (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h₀ : 0 < lam) (l : ℝ)
    (K : CoupledQuenchedLaws d) (hK : HasProbabilityLaws Q.measure K)
    (hD : annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam)) ≠ 0)
    (a M : ℝ) (ha : 0 < a)
    (hmom : (∫⁻ ωz, Work.W5.regenerationExponentialWeight hd lam l a 1 ωz.2
      ∂regenerationConditionedLaw hd Q lam l K hK hD) ≤ ENNReal.ofReal M) :
    Integrable (fun q => recordDuration (Renewal.regenDelta lam) lam (l / lam)
      (Renewal.forceCoord hd)
      (iteratedRecord (Renewal.regenDelta lam) lam (l / lam) (Renewal.forceCoord hd) 0 q))
      (regenerationConditionedLaw hd Q lam l K hK hD) := by
  have hf : Measurable (fun q => recordDuration (Renewal.regenDelta lam) lam (l / lam)
      (Renewal.forceCoord hd)
      (iteratedRecord (Renewal.regenDelta lam) lam (l / lam) (Renewal.forceCoord hd) 0 q)) :=
    (measurable_recordDuration _ _ _ _).comp (measurable_iteratedRecord _ _ _ _ 0)
  have hpos : 0 < a * lam ^ 2 := by positivity
  have hpt : ∀ q : FieldPair d × CoupledSample d,
      ENNReal.ofReal (recordDuration (Renewal.regenDelta lam) lam (l / lam)
        (Renewal.forceCoord hd)
        (iteratedRecord (Renewal.regenDelta lam) lam (l / lam) (Renewal.forceCoord hd) 0 q)) ≤
      ENNReal.ofReal (1 / (a * lam ^ 2)) *
        Work.W5.regenerationExponentialWeight hd lam l a 1 q.2 := by
    intro q
    rw [recordDuration_iteratedRecord_zero]
    have hrt : EinsteinFull.regenerationTime hd lam l 1 q.2 = firstRegenerationTime
        (Renewal.regenDelta lam) lam (l / lam) q.2 (Renewal.forceCoord hd) := by
      simp only [EinsteinFull.regenerationTime, regenerationTime_one]
    unfold Work.W5.regenerationExponentialWeight
    rw [hrt]
    split_ifs with hτ
    · rw [ENNReal.mul_top (ENNReal.ofReal_pos.mpr (by positivity)).ne']
      exact le_top
    · rw [← ENNReal.ofReal_mul (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      change ((firstRegenerationTime (Renewal.regenDelta lam) lam (l / lam) q.2
          (Renewal.forceCoord hd)).toNNReal : ℝ) ≤ 1 / (a * lam ^ 2) * Real.exp (a * lam ^ 2 *
          ((firstRegenerationTime (Renewal.regenDelta lam) lam (l / lam) q.2
            (Renewal.forceCoord hd)).toNNReal : ℝ))
      set x := ((firstRegenerationTime (Renewal.regenDelta lam) lam (l / lam) q.2
          (Renewal.forceCoord hd)).toNNReal : ℝ)
      have hexp := Real.add_one_le_exp (a * lam ^ 2 * x)
      rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hpos]
      have hc : x * (a * lam ^ 2) = a * lam ^ 2 * x := by ring
      linarith
  have hlint : (∫⁻ q, ENNReal.ofReal (recordDuration (Renewal.regenDelta lam) lam (l / lam)
      (Renewal.forceCoord hd)
      (iteratedRecord (Renewal.regenDelta lam) lam (l / lam) (Renewal.forceCoord hd) 0 q))
      ∂regenerationConditionedLaw hd Q lam l K hK hD) ≠ ⊤ := by
    have hle : (∫⁻ q, ENNReal.ofReal (recordDuration (Renewal.regenDelta lam) lam (l / lam)
        (Renewal.forceCoord hd)
        (iteratedRecord (Renewal.regenDelta lam) lam (l / lam) (Renewal.forceCoord hd) 0 q))
        ∂regenerationConditionedLaw hd Q lam l K hK hD) ≤
        ENNReal.ofReal (1 / (a * lam ^ 2)) * ENNReal.ofReal M := by
      refine (lintegral_mono fun q => hpt q).trans ?_
      rw [lintegral_const_mul (ENNReal.ofReal (1 / (a * lam ^ 2)))
        (f := fun q : FieldPair d × CoupledSample d =>
          Work.W5.regenerationExponentialWeight hd lam l a 1 q.2)
        ((Work.W5.measurable_regenerationExponentialWeight hd lam l a 1).comp measurable_snd)]
      exact mul_le_mul_right hmom _
    exact (hle.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)).ne
  exact (integrable_toReal_of_lintegral_ne_top hf.ennreal_ofReal.aemeasurable hlint).congr
    (ae_of_all _ fun q => ENNReal.toReal_ofReal (NNReal.coe_nonneg _))

/-- The maximal displacement of the first cycle is integrable under the conditioned law: each
window of length `λ⁻²` before `τ₁` restarts with a uniform exponential moment of its maximum,
and it counts only on `τ₁ > kλ⁻²`. -/
theorem physical_record_maximum_integrable {Λ₀ r₀ : ℝ} (hd : 2 ≤ d)
    (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1) (l δ : ℝ)
    (hl : 0 < l) (hsep : r₀ < 2 * l) (hδ₀ : 0 < δ) (hδ₁ : δ < 1)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : IsRegenerationCouplingPhys hd Q lam l δ h₀.le h₁ P K)
    (hD : annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam)) ≠ 0)
    (c C : ℝ) (hc : 0 < c) (hC : 0 < C)
    (htail : ∀ t : ℝ, 0 ≤ t → annealedCoupledLaw Q.measure K
        {ωz | ENNReal.ofReal t < EinsteinFull.regenerationTime hd lam l 1 ωz.2} ≤
          ENNReal.ofReal (C * Real.exp (-c * lam ^ 2 * t)))
    (b Cw : ℝ) (hb : 0 < b) (hCw : 0 < Cw)
    (hwin : ∀ᵐ ω ∂Q.measure, ∀ (x : Vec d) (j : Fin d),
      Integrable (fun γ : Path d => Real.exp (b * (lam *
        absoluteCoordinateMaximum j (Renewal.regenDelta lam) γ))) (P (x, ω)) ∧
      (∫ γ, Real.exp (b * (lam * absoluteCoordinateMaximum j (Renewal.regenDelta lam) γ))
        ∂P (x, ω)) ≤ Cw)
    (j : Fin d) :
    Integrable (fun q => recordMaximum (Renewal.regenDelta lam) lam (l / lam)
      (Renewal.forceCoord hd) j
      (iteratedRecord (Renewal.regenDelta lam) lam (l / lam) (Renewal.forceCoord hd) 0 q))
      (regenerationConditionedLaw hd Q lam l K hK.1 hD) := by
  have : IsProbabilityMeasure (annealedCoupledLaw Q.measure K) :=
    annealedCoupledLaw_isProbabilityMeasure Q.measure K hK.1
  have hΔ : 0 < Renewal.regenDelta lam := EinsteinRelation.regenDelta_pos h₀
  have hΔlam : lam ^ 2 * (Renewal.regenDelta lam : ℝ) = 1 := by
    rw [Renewal.regenDelta, Real.coe_toNNReal _ (inv_nonneg.mpr (sq_nonneg lam))]
    exact mul_inv_cancel₀ (pow_ne_zero 2 h₀.ne')
  have hMγ : Measurable fun γ : Path d =>
      absoluteCoordinateMaximum j (Renewal.regenDelta lam) γ :=
    (continuous_absoluteCoordinateMaximum j).measurable.comp
      (measurable_const.prodMk measurable_id)
  let W : ℕ → FieldPair d × CoupledSample d → ℝ := fun k q =>
    absoluteCoordinateMaximum j (Renewal.regenDelta lam)
      (sampleTimeShift (Renewal.regenDelta lam) q.2 ((k : ℝ≥0) * Renewal.regenDelta lam)).1
  have hW : ∀ k, Measurable (W k) := fun k =>
    hMγ.comp (measurable_fst.comp ((measurable_sampleTimeShift _).comp
      (measurable_const.prodMk measurable_snd)))
  have hW0 : ∀ k q, 0 ≤ W k q := fun k q => absoluteCoordinateMaximum_nonneg _ _ _
  let A : ℕ → Set (FieldPair d × CoupledSample d) := fun k =>
    {ωz | ENNReal.ofReal (((k : ℝ≥0) * Renewal.regenDelta lam : ℝ≥0) : ℝ) <
      EinsteinFull.regenerationTime hd lam l 1 ωz.2}
  have hA : ∀ k, MeasurableSet (A k) := fun k =>
    measurableSet_lt measurable_const
      ((Regeneration.measurable_regenerationTime _ lam _ _ 1).comp measurable_snd)
  have hpath : ∀ q : FieldPair d × CoupledSample d,
      ENNReal.ofReal (recordMaximum (Renewal.regenDelta lam) lam (l / lam)
        (Renewal.forceCoord hd) j
        (iteratedRecord (Renewal.regenDelta lam) lam (l / lam) (Renewal.forceCoord hd) 0 q)) ≤
      ∑' k, ENNReal.ofReal (W k q) * (A k).indicator 1 q := by
    intro q
    rw [recordMaximum_iteratedRecord_zero]
    by_cases hτ : firstRegenerationTime (Renewal.regenDelta lam) lam (l / lam) q.2
        (Renewal.forceCoord hd) = ⊤
    · rw [hτ, ENNReal.toNNReal_top]
      have h0 := absoluteCoordinateMaximum_le_sum_windows j (Renewal.regenDelta lam) q.2.1 0
      simp only [Nat.cast_zero, zero_mul, Finset.range_zero, Finset.sum_empty] at h0
      rw [ENNReal.ofReal_of_nonpos h0]
      exact zero_le
    · obtain ⟨m, hm⟩ := firstRegenerationTime_eq_succ_grid_of_ne_top _ hΔ lam (l / lam) q.2
        _ hτ
      rw [hm, ENNReal.toNNReal_coe]
      have hle := absoluteCoordinateMaximum_le_sum_windows j (Renewal.regenDelta lam) q.2.1
        (m + 1)
      calc ENNReal.ofReal (absoluteCoordinateMaximum j
            (((m + 1 : ℕ) : ℝ≥0) * Renewal.regenDelta lam) q.2.1)
          ≤ ENNReal.ofReal (∑ k ∈ Finset.range (m + 1), W k q) := ENNReal.ofReal_le_ofReal hle
        _ = ∑ k ∈ Finset.range (m + 1), ENNReal.ofReal (W k q) :=
          ENNReal.ofReal_sum_of_nonneg fun k _ => hW0 k q
        _ = ∑ k ∈ Finset.range (m + 1), ENNReal.ofReal (W k q) * (A k).indicator 1 q := by
          refine Finset.sum_congr rfl fun k hk => ?_
          have hkA : q ∈ A k := by
            change ENNReal.ofReal _ < EinsteinFull.regenerationTime hd lam l 1 q.2
            rw [ENNReal.ofReal_coe_nnreal]
            simp only [EinsteinFull.regenerationTime, regenerationTime_one]
            rw [hm]
            exact ENNReal.coe_lt_coe.mpr (mul_lt_mul_of_pos_right
              (by exact_mod_cast Finset.mem_range.mp hk) hΔ)
          rw [Set.indicator_of_mem hkA, Pi.one_apply, mul_one]
        _ ≤ ∑' k, ENNReal.ofReal (W k q) * (A k).indicator 1 q := ENNReal.sum_le_tsum _
  have hr0 : 0 < Real.exp (-c / 2) := Real.exp_pos _
  have hamgm : ∀ k q, ENNReal.ofReal (W k q) * (A k).indicator 1 q ≤
      ENNReal.ofReal (Real.exp (-c / 2) ^ k) * ENNReal.ofReal (W k q) ^ 2 +
        ENNReal.ofReal ((Real.exp (-c / 2) ^ k)⁻¹) * (A k).indicator 1 q := by
    intro k q
    by_cases hq : q ∈ A k
    · simp only [Set.indicator_of_mem hq, Pi.one_apply, mul_one]
      have he : 0 < Real.exp (-c / 2) ^ k := pow_pos hr0 k
      rw [← ENNReal.ofReal_pow (hW0 k q), ← ENNReal.ofReal_mul he.le,
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      have hinv : Real.exp (-c / 2) ^ k * (Real.exp (-c / 2) ^ k)⁻¹ = 1 :=
        mul_inv_cancel₀ he.ne'
      have key : Real.exp (-c / 2) ^ k * W k q ≤ Real.exp (-c / 2) ^ k *
          (Real.exp (-c / 2) ^ k * W k q ^ 2 + (Real.exp (-c / 2) ^ k)⁻¹) := by
        rw [mul_add, hinv]
        nlinarith [sq_nonneg (Real.exp (-c / 2) ^ k * W k q - 1), mul_nonneg he.le (hW0 k q)]
      exact le_of_mul_le_mul_left key he
    · simp only [Set.indicator_of_notMem hq, mul_zero, add_zero]
      exact zero_le
  have hwinμ : ∀ᵐ q ∂annealedCoupledLaw Q.measure K, ∀ (x : Vec d) (j : Fin d),
      Integrable (fun γ : Path d => Real.exp (b * (lam *
        absoluteCoordinateMaximum j (Renewal.regenDelta lam) γ))) (P (x, q.1)) ∧
      (∫ γ, Real.exp (b * (lam * absoluteCoordinateMaximum j (Renewal.regenDelta lam) γ))
        ∂P (x, q.1)) ≤ Cw := by
    have hmap := EinsteinFull.Blueprint.c10_s3_annealed_environment_map Q K hK.1
    rw [← hmap] at hwin
    exact ae_of_ae_map measurable_fst.aemeasurable hwin
  have hsqpt : ∀ y : ℝ, 0 ≤ y → y ^ 2 ≤ 2 / (b * lam) ^ 2 * Real.exp (b * (lam * y)) := by
    intro y hy
    have hbl : 0 < b * lam := mul_pos hb h₀
    have hz : 0 ≤ b * lam * y := mul_nonneg hbl.le hy
    have hq := Real.quadratic_le_exp_of_nonneg hz
    rw [show b * (lam * y) = b * lam * y by ring, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    nlinarith [hq, hz]
  have hexpm : Measurable fun γ : Path d => ENNReal.ofReal (Real.exp (b * (lam *
      absoluteCoordinateMaximum j (Renewal.regenDelta lam) γ))) :=
    (Real.measurable_exp.comp (measurable_const.mul (measurable_const.mul hMγ))).ennreal_ofReal
  have hsq : ∀ k, ∫⁻ q, ENNReal.ofReal (W k q) ^ 2 ∂annealedCoupledLaw Q.measure K ≤
      ENNReal.ofReal (2 / (b * lam) ^ 2 * Cw) := by
    intro k
    have hG : Measurable (fun p : CoupledSample d × CoupledSample d =>
        ENNReal.ofReal (absoluteCoordinateMaximum j (Renewal.regenDelta lam) p.2.1) ^ 2) :=
      ((hMγ.comp measurable_snd.fst).ennreal_ofReal).pow_const 2
    have hr := lintegral_history_restart_phys hd Q lam h₀ h₁ l δ hl hsep hδ₀ hδ₁ P K hK k _ hG
    refine (le_of_eq hr).trans ?_
    calc _ ≤ ∫⁻ _q, ENNReal.ofReal (2 / (b * lam) ^ 2 * Cw) ∂annealedCoupledLaw Q.measure K := by
          apply lintegral_mono_ae
          filter_upwards [EinsteinFull.Blueprint.c10_s3_grid_endpoint_path_marginal_phys hd Q lam
            h₀ h₁ l δ P K hK k, hwinμ] with q hmarg hWq
          obtain ⟨hint, hle⟩ := hWq (q.2.1 ((k : ℝ≥0) * Renewal.regenDelta lam)) j
          show ∫⁻ w, ENNReal.ofReal (absoluteCoordinateMaximum j (Renewal.regenDelta lam) w.1) ^ 2
            ∂K (q.2.1 ((k : ℝ≥0) * Renewal.regenDelta lam), q.1) ≤ _
          rw [← lintegral_map (f := fun γ : Path d =>
            ENNReal.ofReal (absoluteCoordinateMaximum j (Renewal.regenDelta lam) γ) ^ 2)
            (hMγ.ennreal_ofReal.pow_const 2) measurable_fst, hmarg]
          calc ∫⁻ γ, ENNReal.ofReal (absoluteCoordinateMaximum j (Renewal.regenDelta lam) γ) ^ 2
                ∂P (q.2.1 ((k : ℝ≥0) * Renewal.regenDelta lam), q.1)
              ≤ ∫⁻ γ, ENNReal.ofReal (2 / (b * lam) ^ 2) * ENNReal.ofReal (Real.exp (b * (lam *
                  absoluteCoordinateMaximum j (Renewal.regenDelta lam) γ)))
                ∂P (q.2.1 ((k : ℝ≥0) * Renewal.regenDelta lam), q.1) := by
                apply lintegral_mono
                intro γ
                dsimp only
                rw [← ENNReal.ofReal_pow (absoluteCoordinateMaximum_nonneg _ _ _),
                  ← ENNReal.ofReal_mul (by positivity)]
                exact ENNReal.ofReal_le_ofReal (hsqpt _ (absoluteCoordinateMaximum_nonneg _ _ _))
            _ = ENNReal.ofReal (2 / (b * lam) ^ 2) * ENNReal.ofReal (∫ γ, Real.exp (b * (lam *
                  absoluteCoordinateMaximum j (Renewal.regenDelta lam) γ))
                ∂P (q.2.1 ((k : ℝ≥0) * Renewal.regenDelta lam), q.1)) := by
                rw [lintegral_const_mul _ hexpm, ofReal_integral_eq_lintegral_ofReal hint
                  (Filter.Eventually.of_forall fun γ => (Real.exp_pos _).le)]
            _ ≤ ENNReal.ofReal (2 / (b * lam) ^ 2) * ENNReal.ofReal Cw :=
                mul_le_mul_right (ENNReal.ofReal_le_ofReal hle) _
            _ = ENNReal.ofReal (2 / (b * lam) ^ 2 * Cw) := by
                rw [← ENNReal.ofReal_mul (by positivity)]
      _ = ENNReal.ofReal (2 / (b * lam) ^ 2 * Cw) := by
          rw [lintegral_const, measure_univ, mul_one]
  have htailk : ∀ k : ℕ, annealedCoupledLaw Q.measure K (A k) ≤
      ENNReal.ofReal (C * (Real.exp (-c / 2) ^ 2) ^ k) := by
    intro k
    refine (htail _ (NNReal.coe_nonneg _)).trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
    congr 1
    rw [← pow_mul, ← Real.exp_nat_mul]
    congr 1
    push_cast
    linear_combination (-c * (k : ℝ)) * hΔlam
  have hmk : ∀ k, Measurable fun q : FieldPair d × CoupledSample d =>
      ENNReal.ofReal (Real.exp (-c / 2) ^ k) * ENNReal.ofReal (W k q) ^ 2 +
        ENNReal.ofReal ((Real.exp (-c / 2) ^ k)⁻¹) * (A k).indicator 1 q := fun k =>
    (((hW k).ennreal_ofReal.pow_const 2).const_mul _).add
      ((measurable_one.indicator (hA k)).const_mul _)
  have hνle : ∀ f : FieldPair d × CoupledSample d → ℝ≥0∞,
      ∫⁻ q, f q ∂regenerationConditionedLaw hd Q lam l K hK.1 hD ≤
        (annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam)))⁻¹ *
          ∫⁻ q, f q ∂annealedCoupledLaw Q.measure K := by
    intro f
    change ∫⁻ q, f q ∂((annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam)))⁻¹ •
      (annealedCoupledLaw Q.measure K).restrict (regenerationNoReturn hd (l / lam))) ≤ _
    rw [lintegral_smul_measure]
    exact mul_le_mul_right (setLIntegral_le_lintegral _ _) _
  have hK₂ : 0 ≤ 2 / (b * lam) ^ 2 * Cw + C := by positivity
  have hterm : ∀ k : ℕ, ENNReal.ofReal (Real.exp (-c / 2) ^ k) *
        ENNReal.ofReal (2 / (b * lam) ^ 2 * Cw) +
      ENNReal.ofReal ((Real.exp (-c / 2) ^ k)⁻¹) *
        ENNReal.ofReal (C * (Real.exp (-c / 2) ^ 2) ^ k) =
      ENNReal.ofReal (2 / (b * lam) ^ 2 * Cw + C) * ENNReal.ofReal (Real.exp (-c / 2)) ^ k := by
    intro k
    have he : Real.exp (-c / 2) ^ k ≠ 0 := pow_ne_zero _ hr0.ne'
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_pow hr0.le,
      ← ENNReal.ofReal_mul hK₂]
    congr 1
    rw [← pow_mul, mul_comm 2 k, pow_mul]
    field_simp
  have hr1 : ENNReal.ofReal (Real.exp (-c / 2)) < 1 :=
    ENNReal.ofReal_lt_one.mpr (Real.exp_lt_one_iff.mpr (by linarith))
  have hfin : (∫⁻ q, ENNReal.ofReal (recordMaximum (Renewal.regenDelta lam) lam (l / lam)
      (Renewal.forceCoord hd) j
      (iteratedRecord (Renewal.regenDelta lam) lam (l / lam) (Renewal.forceCoord hd) 0 q))
      ∂regenerationConditionedLaw hd Q lam l K hK.1 hD) ≠ ⊤ := by
    refine ((hνle _).trans_lt ?_).ne
    refine ENNReal.mul_lt_top (ENNReal.inv_lt_top.mpr (pos_iff_ne_zero.mpr hD)) ?_
    calc ∫⁻ q, ENNReal.ofReal (recordMaximum (Renewal.regenDelta lam) lam (l / lam)
          (Renewal.forceCoord hd) j
          (iteratedRecord (Renewal.regenDelta lam) lam (l / lam) (Renewal.forceCoord hd) 0 q))
          ∂annealedCoupledLaw Q.measure K
        ≤ ∫⁻ q, ∑' k, (ENNReal.ofReal (Real.exp (-c / 2) ^ k) * ENNReal.ofReal (W k q) ^ 2 +
            ENNReal.ofReal ((Real.exp (-c / 2) ^ k)⁻¹) * (A k).indicator 1 q)
          ∂annealedCoupledLaw Q.measure K :=
          lintegral_mono fun q => (hpath q).trans (ENNReal.tsum_le_tsum fun k => hamgm k q)
      _ = ∑' k, (ENNReal.ofReal (Real.exp (-c / 2) ^ k) *
            ∫⁻ q, ENNReal.ofReal (W k q) ^ 2 ∂annealedCoupledLaw Q.measure K +
          ENNReal.ofReal ((Real.exp (-c / 2) ^ k)⁻¹) * annealedCoupledLaw Q.measure K (A k)) := by
          rw [lintegral_tsum fun k => (hmk k).aemeasurable]
          congr 1
          funext k
          rw [lintegral_add_left (((hW k).ennreal_ofReal.pow_const 2).const_mul _),
            lintegral_const_mul _ ((hW k).ennreal_ofReal.pow_const 2),
            lintegral_const_mul _ (measurable_one.indicator (hA k)),
            lintegral_indicator_one (hA k)]
      _ ≤ ∑' k : ℕ, ENNReal.ofReal (2 / (b * lam) ^ 2 * Cw + C) *
            ENNReal.ofReal (Real.exp (-c / 2)) ^ k := by
          refine ENNReal.tsum_le_tsum fun k => ?_
          rw [← hterm k]
          exact add_le_add (mul_le_mul_right (hsq k) _) (mul_le_mul_right (htailk k) _)
      _ < ⊤ := by
          rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
          exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
            (ENNReal.inv_lt_top.mpr (tsub_pos_of_lt hr1))
  have hf : Measurable fun q => recordMaximum (Renewal.regenDelta lam) lam (l / lam)
      (Renewal.forceCoord hd) j
      (iteratedRecord (Renewal.regenDelta lam) lam (l / lam) (Renewal.forceCoord hd) 0 q) :=
    (measurable_recordMaximum _ _ _ _ j).comp (measurable_iteratedRecord _ _ _ _ 0)
  refine (integrable_toReal_of_lintegral_ne_top hf.ennreal_ofReal.aemeasurable hfin).congr
    (ae_of_all _ fun q => ENNReal.toReal_ofReal ?_)
  rw [recordMaximum_iteratedRecord_zero]
  exact absoluteCoordinateMaximum_nonneg _ _ _

end EinsteinFull.Regeneration
