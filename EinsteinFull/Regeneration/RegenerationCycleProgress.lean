import EinsteinFull.Regeneration.FirstRegenerationMaximum

/-!
# Positive displacement in every regeneration cycle

The successful bridge and trial geometry force each finite cycle to advance in the force
coordinate. This is the positivity step for the regeneration velocity in Gantert–Mathieu–
Piatnitski, Proposition 5.9.
-/

open MeasureTheory EinsteinRelation EinsteinRelation.Regeneration
open scoped NNReal ENNReal

namespace EinsteinFull.Regeneration

/-- Successful-bridge support is preserved by shifting the coupled sample by a grid time. -/
theorem successful_bridge_support_shift_grid {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ)
    (R : ℝ) (z : CoupledSample d) (i : Fin d)
    (hbridge : ∀ n : ℕ, z.2 n = true → ∀ t : ℝ≥0,
      (n : ℝ≥0) * Δ ≤ t → t ≤ ((n + 1 : ℕ) : ℝ≥0) * Δ →
        z.1 t ∈ couplingRegion i R (z.1 ((n : ℝ≥0) * Δ))) (m : ℕ) :
    ∀ n : ℕ, (sampleTimeShift Δ z ((m : ℝ≥0) * Δ)).2 n = true → ∀ t : ℝ≥0,
      (n : ℝ≥0) * Δ ≤ t → t ≤ ((n + 1 : ℕ) : ℝ≥0) * Δ →
        (sampleTimeShift Δ z ((m : ℝ≥0) * Δ)).1 t ∈
          couplingRegion i R ((sampleTimeShift Δ z ((m : ℝ≥0) * Δ)).1 ((n : ℝ≥0) * Δ)) := by
  intro n hn t ht ht'
  have hbit : z.2 (m + n) = true := by
    simpa [sampleTimeShift, gridIndex_mul Δ hΔ] using hn
  have hstart : ((m + n : ℕ) : ℝ≥0) * Δ = (m : ℝ≥0) * Δ + (n : ℝ≥0) * Δ := by
    push_cast
    ring
  have hend : ((m + n + 1 : ℕ) : ℝ≥0) * Δ =
      (m : ℝ≥0) * Δ + ((n + 1 : ℕ) : ℝ≥0) * Δ := by
    push_cast
    ring
  have h := hbridge (m + n) hbit ((m : ℝ≥0) * Δ + t)
    (by rw [hstart]; gcongr) (by rw [hend]; gcongr)
  simpa [sampleTimeShift, pathTimeShift, Nat.cast_add, add_mul] using h

/-- Every finite regeneration cycle advances strictly more than `R` along the force. -/
theorem regeneration_cycle_displacement_gt {d : ℕ}
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (lam R : ℝ) (hlam : 0 < lam) (hR : 0 < R)
    (z : CoupledSample d) (i : Fin d)
    (hbridge : ∀ n : ℕ, z.2 n = true → ∀ t : ℝ≥0,
      (n : ℝ≥0) * Δ ≤ t → t ≤ ((n + 1 : ℕ) : ℝ≥0) * Δ →
        z.1 t ∈ couplingRegion i R (z.1 ((n : ℝ≥0) * Δ)))
    (k : ℕ) (hfin : regenerationTime Δ lam R z i (k + 1) ≠ ⊤) :
    R < z.1 (regenerationTime Δ lam R z i (k + 1)).toNNReal i -
      z.1 (regenerationTime Δ lam R z i k).toNNReal i := by
  have hk : regenerationTime Δ lam R z i k ≠ ⊤ := by
    intro htop
    apply hfin
    rw [regenerationTime, ite_eq_left htop]
  have hstep : firstRegenerationTime Δ lam R
      (sampleTimeShift Δ z (regenerationTime Δ lam R z i k).toNNReal) i ≠ ⊤ := by
    intro htop
    apply hfin
    rw [regenerationTime, ite_eq_right hk, htop, add_top]
  obtain ⟨m, hm⟩ := regenerationTime_mem_grid Δ hΔ lam R z i k hk
  have ht : (regenerationTime Δ lam R z i k).toNNReal = (m : ℝ≥0) * Δ := by
    rw [hm, ENNReal.toNNReal_coe]
  have hshift := successful_bridge_support_shift_grid Δ hΔ R z i hbridge m
  have hpos := first_regeneration_displacement_gt Δ hΔ lam R hlam hR
    (sampleTimeShift Δ z ((m : ℝ≥0) * Δ)) i (by simpa [ht] using hstep) hshift
  have hnext : (regenerationTime Δ lam R z i (k + 1)).toNNReal =
      (m : ℝ≥0) * Δ +
        (firstRegenerationTime Δ lam R (sampleTimeShift Δ z ((m : ℝ≥0) * Δ)) i).toNNReal := by
    rw [regenerationTime, ite_eq_right hk, ENNReal.toNNReal_add hk hstep, ht]
  rw [hnext, ht]
  simpa [sampleTimeShift, pathTimeShift] using hpos

/-- Under the annealed coupling, every finite regeneration cycle advances strictly more than
`R` along the force. -/
theorem ae_regeneration_cycle_displacement_gt {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (K : CoupledQuenchedLaws d) (hK : HasProbabilityLaws Q K)
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (lam R : ℝ) (hlam : 0 < lam) (hR : 0 < R)
    (i : Fin d) (hsupport : HasSuccessfulBridgeSupport Q Δ i R K) :
    ∀ᵐ ωz ∂annealedCoupledLaw Q K, ∀ k : ℕ,
      regenerationTime Δ lam R ωz.2 i (k + 1) ≠ ⊤ →
        R < ωz.2.1 (regenerationTime Δ lam R ωz.2 i (k + 1)).toNNReal i -
          ωz.2.1 (regenerationTime Δ lam R ωz.2 i k).toNNReal i := by
  apply ae_all_iff.mpr
  intro k
  have hτ (n : ℕ) := (measurable_regenerationTime Δ lam R i n).comp
    (measurable_snd : Measurable (Prod.snd : FieldPair d × CoupledSample d → _))
  have hx (n : ℕ) := measurable_path_eval.comp ((hτ n).ennreal_toNNReal.prodMk measurable_snd.fst)
  have hm : MeasurableSet {ωz : FieldPair d × CoupledSample d |
      regenerationTime Δ lam R ωz.2 i (k + 1) ≠ ⊤ →
        R < ωz.2.1 (regenerationTime Δ lam R ωz.2 i (k + 1)).toNNReal i -
          ωz.2.1 (regenerationTime Δ lam R ωz.2 i k).toNNReal i} :=
    ((hτ (k + 1)) (measurableSet_singleton ⊤)).compl.imp
      (measurableSet_lt measurable_const
        (((measurable_pi_apply i).comp (hx (k + 1))).sub ((measurable_pi_apply i).comp (hx k))))
  apply Measure.ae_compProd_of_ae_ae hm
  filter_upwards [hK.1, hsupport.1] with ω hprob hsupp
  have : IsProbabilityMeasure (originCoupledLaw K ω) := hprob
  rw [Probability.probabilityPart_eq_of_isProbabilityMeasure (originCoupledLaw K) ω]
  filter_upwards [hsupp] with z hz
  exact fun hfin => regeneration_cycle_displacement_gt Δ hΔ lam R hlam hR z i hz k hfin

/-- An integrable finite cycle has strictly positive expected displacement in the force
coordinate. -/
theorem regeneration_cycle_expected_displacement_pos {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (K : CoupledQuenchedLaws d) (hK : HasProbabilityLaws Q K)
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (lam R : ℝ) (hlam : 0 < lam) (hR : 0 < R)
    (i : Fin d) (hsupport : HasSuccessfulBridgeSupport Q Δ i R K) (k : ℕ)
    (hfinite : ∀ᵐ ωz ∂annealedCoupledLaw Q K,
      regenerationTime Δ lam R ωz.2 i (k + 1) ≠ ⊤)
    (hint : Integrable (fun ωz : FieldPair d × CoupledSample d =>
      ωz.2.1 (regenerationTime Δ lam R ωz.2 i (k + 1)).toNNReal i -
        ωz.2.1 (regenerationTime Δ lam R ωz.2 i k).toNNReal i) (annealedCoupledLaw Q K)) :
    0 < ∫ ωz : FieldPair d × CoupledSample d,
      (ωz.2.1 (regenerationTime Δ lam R ωz.2 i (k + 1)).toNNReal i -
        ωz.2.1 (regenerationTime Δ lam R ωz.2 i k).toNNReal i) ∂annealedCoupledLaw Q K := by
  have : IsProbabilityMeasure (annealedCoupledLaw Q K) :=
    annealedCoupledLaw_isProbabilityMeasure Q K hK
  have hbound : ∀ᵐ ωz ∂annealedCoupledLaw Q K, R ≤
      ωz.2.1 (regenerationTime Δ lam R ωz.2 i (k + 1)).toNNReal i -
        ωz.2.1 (regenerationTime Δ lam R ωz.2 i k).toNNReal i := by
    filter_upwards [hfinite,
      ae_regeneration_cycle_displacement_gt Q K hK Δ hΔ lam R hlam hR i hsupport] with ωz hf hp
    exact (hp k hf).le
  have h := integral_mono_ae (integrable_const R) hint hbound
  simpa using lt_of_lt_of_le hR (by simpa using h)

end EinsteinFull.Regeneration
