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

end EinsteinFull.Regeneration
