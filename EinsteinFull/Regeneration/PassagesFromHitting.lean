import EinsteinFull.Calculus.C2S3UnboundedPassages
import EinsteinFull.Regeneration.NoReturnFromHitting

/-!
# Finite passages from forward-hitting bounds

The forward-hitting estimate in Gantert–Mathieu–Piatnitski, Lemma 4.2, implies
that every level is reached and consequently that all restarted passages are finite.
-/

open MeasureTheory Filter EinsteinRelation EinsteinRelation.Regeneration
open scoped NNReal ENNReal Topology

namespace EinsteinFull.Regeneration

/-- An exponential forward-hitting bound implies almost-sure finite hitting at each nonnegative level. -/
theorem ae_firstHittingAbove_ne_top_of_bound {d : ℕ}
    (μ : Measure (FieldPair d × CoupledSample d)) (i : Fin d)
    (lam κ C : ℝ) (hlam : 0 < lam) (hκ : 0 < κ)
    (hhit : ∀ (T : ℝ≥0) (a : ℝ), 0 ≤ a →
      μ {ωz | (T : ℝ≥0∞) ≤ firstHittingAbove ωz.2.1 i a} ≤
        ENNReal.ofReal (C * Real.exp (-κ * lam ^ 2 * T + lam * a)))
    (a : ℝ) (ha : 0 ≤ a) :
    ∀ᵐ ωz ∂μ, firstHittingAbove ωz.2.1 i a ≠ ⊤ := by
  have hrate : 0 < κ * lam ^ 2 := by positivity
  have harg : Tendsto (fun n : ℕ => -(κ * lam ^ 2) * (n : ℝ)) atTop atBot := by
    exact (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)
      |>.const_mul_atTop_of_neg (neg_lt_zero.mpr hrate)
  have hlim : Tendsto (fun n : ℕ => ENNReal.ofReal
      (C * Real.exp (-κ * lam ^ 2 * (n : ℝ) + lam * a))) atTop (𝓝 0) := by
    have h := ENNReal.tendsto_ofReal
      ((Real.tendsto_exp_atBot.comp harg).mul_const (C * Real.exp (lam * a)))
    simpa only [Real.exp_add, neg_mul, mul_zero, zero_mul, ENNReal.ofReal_zero,
      Function.comp_apply, mul_comm, mul_left_comm, mul_assoc] using h
  have hzero : μ {ωz | firstHittingAbove ωz.2.1 i a = ⊤} = 0 := by
    apply le_antisymm _ zero_le
    apply ge_of_tendsto' hlim
    intro n
    calc
      μ {ωz | firstHittingAbove ωz.2.1 i a = ⊤} ≤
          μ {ωz | ((n : ℝ≥0) : ℝ≥0∞) ≤ firstHittingAbove ωz.2.1 i a} :=
        measure_mono (fun x h => by
          change firstHittingAbove x.2.1 i a = ⊤ at h
          change ((n : ℝ≥0) : ℝ≥0∞) ≤ firstHittingAbove x.2.1 i a
          rw [h]
          exact le_top)
      _ ≤ _ := by simpa using hhit (n : ℝ≥0) a ha
  rw [ae_iff]
  simpa only [not_not] using hzero

/-- Forward-hitting bounds give all actual passages after any finite path-dependent restart. -/
theorem ae_shifted_passages_finite_of_forward_hitting_bound {d : ℕ}
    (μ : Measure (FieldPair d × CoupledSample d)) (i : Fin d)
    (lam κ C : ℝ) (hlam : 0 < lam) (hκ : 0 < κ)
    (hhit : ∀ (T : ℝ≥0) (a : ℝ), 0 ≤ a →
      μ {ωz | (T : ℝ≥0∞) ≤ firstHittingAbove ωz.2.1 i a} ≤
        ENNReal.ofReal (C * Real.exp (-κ * lam ^ 2 * T + lam * a))) :
    ∀ᵐ ωz ∂μ, ∀ (Δ : ℝ≥0) (R : ℝ) (s : ℝ≥0) (a : ℝ) (n : ℕ),
      passageSequence Δ lam R a (pathTimeShift ωz.2.1 s) i n ≠ ⊤ := by
  have hall : ∀ᵐ ωz ∂μ, ∀ k : ℕ, firstHittingAbove ωz.2.1 i (k : ℝ) ≠ ⊤ := by
    exact ae_all_iff.mpr (fun k =>
      ae_firstHittingAbove_ne_top_of_bound μ i lam κ C hlam hκ hhit k (Nat.cast_nonneg k))
  filter_upwards [hall] with ωz hωz Δ R s a n
  apply EinsteinFull.Blueprint.c2_s3_shifted_passages_finite_of_unbounded Δ lam R ωz.2.1 i _ s a n
  intro B
  obtain ⟨k, hk⟩ := exists_nat_ge B
  have hfin := hωz k
  have hle : firstHittingAbove ωz.2.1 i (k : ℝ) ≤
      ((firstHittingAbove ωz.2.1 i (k : ℝ)).toNNReal : ℝ≥0∞) :=
    (ENNReal.coe_toNNReal hfin).symm.le
  obtain ⟨t, _, ht⟩ := (firstHittingAbove_le_iff ωz.2.1 i (k : ℝ) _).mp hle
  exact ⟨t, hk.trans ht⟩

end EinsteinFull.Regeneration
