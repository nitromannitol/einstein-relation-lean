import EinsteinFull.Work.W5.RenewalCoefficientDecaySupport
import EinsteinFull.Frozen.RegenerationConditionedLawProbability
import EinsteinRelation.Regeneration.RegenerationGrid
import EinsteinRelation.Regeneration.TrialBounds
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-!
# Actual regeneration lattice law and moment transfer

These are ordinary support results for the uniform renewal proof. Finiteness
and moment hypotheses below are explicit intermediate data, not new inputs to
Lemma 3.2. No independence or factorization assertion is assumed or proved here.
-/

open MeasureTheory Filter
open scoped NNReal ENNReal

namespace EinsteinFull.Work.W5

open EinsteinRelation

/-- The literal extended exponential weight; infinity is retained at an infinite time. -/
noncomputable def regenerationExponentialWeight {d : ℕ} (hd : 2 ≤ d)
    (lam l a : ℝ) (j : ℕ) (z : Regeneration.CoupledSample d) : ℝ≥0∞ :=
  if regenerationTime hd lam l j z = ⊤ then ⊤ else
    ENNReal.ofReal (Real.exp (a * lam ^ 2 * (regenerationTime hd lam l j z).toReal))

/-- Measurability uses the actual trial recursion, including its infinite branch. -/
theorem measurable_regenerationExponentialWeight {d : ℕ} (hd : 2 ≤ d)
    (lam l a : ℝ) (j : ℕ) :
    Measurable (regenerationExponentialWeight hd lam l a j) := by
  have ht := Regeneration.measurable_regenerationTime
    (Regeneration.Renewal.regenDelta lam) lam (l / lam)
    (Regeneration.Renewal.forceCoord hd) j
  exact Measurable.ite (ht (measurableSet_singleton ⊤)) measurable_const
    (measurable_id.const_mul (a * lam ^ 2) |>.comp ht.ennreal_toReal |>.exp |>.ennreal_ofReal)

/-- The physical time scale cancels exactly for either sign of a nonzero force. -/
theorem regeneration_scaled_grid_time (lam : ℝ) (hlam : lam ≠ 0) (n : ℕ) :
    lam ^ 2 *
      ((((n : ℝ≥0) * Regeneration.Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞).toReal) =
      (n : ℝ) := by
  rw [ENNReal.coe_toReal, NNReal.coe_mul, Regeneration.Renewal.regenDelta,
    Real.coe_toNNReal _ (inv_nonneg.mpr (sq_nonneg lam))]
  push_cast
  field_simp

/-- Exact exponential scaling on a genuine grid slice, with no finiteness fallback. -/
theorem regenerationExponentialWeight_on_grid {d : ℕ} (hd : 2 ≤ d)
    (lam l a : ℝ) (hlam : lam ≠ 0) (j n : ℕ) (z : Regeneration.CoupledSample d)
    (ht : regenerationTime hd lam l j z =
      (((n : ℝ≥0) * Regeneration.Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)) :
    regenerationExponentialWeight hd lam l a j z = ENNReal.ofReal (Real.exp (a * n)) := by
  rw [regenerationExponentialWeight, ht, if_neg ENNReal.coe_ne_top, mul_assoc,
    regeneration_scaled_grid_time lam hlam n]

/-- A finite extended moment proves almost-sure finiteness of the actual time. -/
theorem regenerationTime_ne_top_ae_of_exponentialMoment {d : ℕ} (hd : 2 ≤ d)
    (lam l a : ℝ) (j : ℕ) (μ : Measure (FieldPair d × Regeneration.CoupledSample d))
    (hm : (∫⁻ ωz, regenerationExponentialWeight hd lam l a j ωz.2 ∂μ) ≠ ⊤) :
    ∀ᵐ ωz ∂μ, regenerationTime hd lam l j ωz.2 ≠ ⊤ := by
  have hf := ae_lt_top ((measurable_regenerationExponentialWeight hd lam l a j).comp
    measurable_snd) hm
  filter_upwards [hf] with ωz hωz
  intro ht
  change regenerationExponentialWeight hd lam l a j ωz.2 < ⊤ at hωz
  simp only [regenerationExponentialWeight, ht, if_true, lt_self_iff_false] at hωz

/-- Countable-slice integration for any actual regeneration iterate and any measure.
Only almost-sure finiteness is needed; all grid support comes from the trial definition. -/
theorem regeneration_grid_lintegral {d : ℕ} (hd : 2 ≤ d)
    (lam l : ℝ) (hlam : lam ≠ 0) (j : ℕ)
    (μ : Measure (FieldPair d × Regeneration.CoupledSample d))
    (hf : ∀ᵐ ωz ∂μ, regenerationTime hd lam l j ωz.2 ≠ ⊤) (f : ℝ≥0∞ → ℝ≥0∞) :
    (∫⁻ ωz, f (regenerationTime hd lam l j ωz.2) ∂μ) =
      ∑' n : ℕ, f (((n : ℝ≥0) * Regeneration.Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞) *
        μ {ωz | regenerationTime hd lam l j ωz.2 =
          (((n : ℝ≥0) * Regeneration.Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)} := by
  let s := fun n : ℕ => {ωz : FieldPair d × Regeneration.CoupledSample d |
    regenerationTime hd lam l j ωz.2 =
      (((n : ℝ≥0) * Regeneration.Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)}
  have hΔ : 0 < Regeneration.Renewal.regenDelta lam :=
    Real.toNNReal_pos.mpr (inv_pos.mpr (sq_pos_of_ne_zero hlam))
  have ht : Measurable (fun ωz : FieldPair d × Regeneration.CoupledSample d =>
      regenerationTime hd lam l j ωz.2) :=
    (Regeneration.measurable_regenerationTime _ _ _ _ _).comp measurable_snd
  have hs (n : ℕ) : MeasurableSet (s n) := ht (measurableSet_singleton _)
  have hdis : Pairwise (fun m n => Disjoint (s m) (s n)) := by
    intro m n hmn
    apply Set.disjoint_left.mpr
    intro ωz hm hn
    have hmul := ENNReal.coe_inj.mp (hm.symm.trans hn)
    have hcast := mul_right_cancel₀ hΔ.ne' hmul
    exact hmn (by exact_mod_cast hcast)
  have hcover : ∀ᵐ ωz ∂μ, ωz ∈ ⋃ n, s n := by
    filter_upwards [hf] with ωz hωz
    obtain ⟨n, hn⟩ := Regeneration.regenerationTime_mem_grid _ hΔ _ _ ωz.2 _ j hωz
    exact Set.mem_iUnion.mpr ⟨n, hn⟩
  calc
    _ = ∫⁻ ωz in ⋃ n, s n, f (regenerationTime hd lam l j ωz.2) ∂μ := by
      rw [Measure.restrict_eq_self_of_ae_mem hcover]
    _ = ∑' n, ∫⁻ ωz in s n, f (regenerationTime hd lam l j ωz.2) ∂μ :=
      lintegral_iUnion hs hdis _
    _ = _ := by
      apply tsum_congr
      intro n
      rw [setLIntegral_congr_fun (hs n) (fun _ h => congrArg f h), setLIntegral_const]

/-- The actual conditioned lattice masses sum to one once finiteness is proved. -/
theorem regenerationLatticeMass_hasSum_of_finite {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (lam l : ℝ) (hlam : lam ≠ 0)
    (K : Regeneration.CoupledQuenchedLaws d)
    (hK : Regeneration.HasProbabilityLaws Q.measure K)
    (hD : Regeneration.annealedCoupledLaw Q.measure K
      (regenerationNoReturn hd (l / lam)) ≠ 0)
    (hf : ∀ᵐ ωz ∂regenerationConditionedLaw hd Q lam l K hK hD,
      regenerationTime hd lam l 1 ωz.2 ≠ ⊤) :
    HasSum (regenerationLatticeMass hd Q lam l K hK hD) 1 := by
  let μ := regenerationConditionedLaw hd Q lam l K hK hD
  letI : IsProbabilityMeasure μ := regenerationConditionedLaw_probability hd Q lam l K hK hD
  have he := regeneration_grid_lintegral hd lam l hlam 1 μ hf (fun _ => 1)
  simp only [lintegral_one, measure_univ, one_mul] at he
  have hs := ENNReal.summable_toReal (he.symm ▸ ENNReal.one_ne_top)
  have ht := ENNReal.tsum_toReal_eq (f := fun n : ℕ => μ {ωz |
    regenerationTime hd lam l 1 ωz.2 =
      (((n : ℝ≥0) * Regeneration.Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)})
    (fun n => measure_ne_top μ _)
  rw [← he, ENNReal.toReal_one] at ht
  exact ht ▸ hs.hasSum

/-- The exponential integral equals the literal weighted grid masses, for any
measure and every iterate. No cycle law is identified with the first-cycle law. -/
theorem regeneration_exponentialMoment_eq_tsum {d : ℕ} (hd : 2 ≤ d)
    (lam l a : ℝ) (hlam : lam ≠ 0) (j : ℕ)
    (μ : Measure (FieldPair d × Regeneration.CoupledSample d))
    (hf : ∀ᵐ ωz ∂μ, regenerationTime hd lam l j ωz.2 ≠ ⊤) :
    (∫⁻ ωz, regenerationExponentialWeight hd lam l a j ωz.2 ∂μ) =
      ∑' n : ℕ, ENNReal.ofReal (Real.exp (a * n)) *
        μ {ωz | regenerationTime hd lam l j ωz.2 =
          (((n : ℝ≥0) * Regeneration.Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)} := by
  classical
  change (∫⁻ ωz, (if regenerationTime hd lam l j ωz.2 = ⊤ then ⊤ else
    ENNReal.ofReal (Real.exp (a * lam ^ 2 *
      (regenerationTime hd lam l j ωz.2).toReal))) ∂μ) = _
  rw [regeneration_grid_lintegral hd lam l hlam j μ hf
    (fun t => if t = ⊤ then ⊤ else ENNReal.ofReal (Real.exp (a * lam ^ 2 * t.toReal)))]
  apply tsum_congr
  intro n
  rw [if_neg ENNReal.coe_ne_top, mul_assoc, regeneration_scaled_grid_time lam hlam n]

/-- A finite actual conditional moment supplies the summable real exponential
moment required by the analytic renewal theorem, with exact value. -/
theorem regenerationLatticeMass_exponential_hasSum {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (lam l a : ℝ) (hlam : lam ≠ 0)
    (K : Regeneration.CoupledQuenchedLaws d)
    (hK : Regeneration.HasProbabilityLaws Q.measure K)
    (hD : Regeneration.annealedCoupledLaw Q.measure K
      (regenerationNoReturn hd (l / lam)) ≠ 0)
    (hm : (∫⁻ ωz, regenerationExponentialWeight hd lam l a 1 ωz.2
      ∂regenerationConditionedLaw hd Q lam l K hK hD) ≠ ⊤) :
    HasSum (fun n : ℕ => regenerationLatticeMass hd Q lam l K hK hD n * Real.exp (a * n))
      (∫⁻ ωz, regenerationExponentialWeight hd lam l a 1 ωz.2
        ∂regenerationConditionedLaw hd Q lam l K hK hD).toReal := by
  let μ := regenerationConditionedLaw hd Q lam l K hK hD
  letI : IsProbabilityMeasure μ := regenerationConditionedLaw_probability hd Q lam l K hK hD
  have hf := regenerationTime_ne_top_ae_of_exponentialMoment hd lam l a 1 μ hm
  have he := regeneration_exponentialMoment_eq_tsum hd lam l a hlam 1 μ hf
  have hs := ENNReal.summable_toReal (he ▸ hm)
  have ht := ENNReal.tsum_toReal_eq (f := fun n : ℕ =>
    ENNReal.ofReal (Real.exp (a * n)) * μ {ωz |
      regenerationTime hd lam l 1 ωz.2 =
        (((n : ℝ≥0) * Regeneration.Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)})
    (fun n => ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top μ _))
  rw [← he] at ht
  have hh := ht.symm ▸ hs.hasSum
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le,
    mul_comm, regenerationLatticeMass, measureReal_def] using hh

/-- Normalization is derived from the actual moment bound, not assumed of p. -/
theorem regenerationLatticeMass_hasSum_of_exponentialMoment {d : ℕ} (hd : 2 ≤ d)
    {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (lam l a : ℝ) (hlam : lam ≠ 0)
    (K : Regeneration.CoupledQuenchedLaws d)
    (hK : Regeneration.HasProbabilityLaws Q.measure K)
    (hD : Regeneration.annealedCoupledLaw Q.measure K
      (regenerationNoReturn hd (l / lam)) ≠ 0)
    (hm : (∫⁻ ωz, regenerationExponentialWeight hd lam l a 1 ωz.2
      ∂regenerationConditionedLaw hd Q lam l K hK hD) ≠ ⊤) :
    HasSum (regenerationLatticeMass hd Q lam l K hK hD) 1 :=
  regenerationLatticeMass_hasSum_of_finite hd Q lam l hlam K hK hD
    (regenerationTime_ne_top_ae_of_exponentialMoment hd lam l a 1 _ hm)

/-- The actual time cannot be in the zeroth or first slice, by the trial geometry. -/
theorem regenerationLatticeMass_eq_zero_of_lt_two {d : ℕ} (hd : 2 ≤ d)
    {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (lam l : ℝ)
    (hlam : 0 < lam) (hl : 0 < l) (K : Regeneration.CoupledQuenchedLaws d)
    (hK : Regeneration.HasProbabilityLaws Q.measure K)
    (hD : Regeneration.annealedCoupledLaw Q.measure K
      (regenerationNoReturn hd (l / lam)) ≠ 0) (n : ℕ) (hn : n < 2) :
    regenerationLatticeMass hd Q lam l K hK hD n = 0 := by
  have hΔ : 0 < Regeneration.Renewal.regenDelta lam :=
    Real.toNNReal_pos.mpr (inv_pos.mpr (sq_pos_of_pos hlam))
  have he : {ωz : FieldPair d × Regeneration.CoupledSample d |
      regenerationTime hd lam l 1 ωz.2 =
        (((n : ℝ≥0) * Regeneration.Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)} = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro ωz ht
    have hb := Regeneration.nat_two_step_le_regenerationTime _ hΔ lam (l / lam)
      hlam (div_pos hl hlam) ωz.2 (Regeneration.Renewal.forceCoord hd) 1
    simp only [Nat.cast_one, one_mul] at hb
    change 2 * (Regeneration.Renewal.regenDelta lam : ℝ≥0∞) ≤
      regenerationTime hd lam l 1 ωz.2 at hb
    rw [ht] at hb
    have hb' : (2 : ℝ≥0) * Regeneration.Renewal.regenDelta lam ≤
        (n : ℝ≥0) * Regeneration.Renewal.regenDelta lam := by exact_mod_cast hb
    have hge : (2 : ℝ≥0) ≤ (n : ℝ≥0) := (mul_le_mul_iff_left₀ hΔ).mp hb'
    have : 2 ≤ n := by exact_mod_cast hge
    omega
  unfold regenerationLatticeMass
  rw [he, measureReal_empty]

/-- Exact conditioning normalization for arbitrary nonnegative integrands.
The restricted integral is retained, so no cycle independence is implied. -/
theorem regenerationConditioned_lintegral_mul_mass {d : ℕ} (hd : 2 ≤ d)
    {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (lam l : ℝ)
    (K : Regeneration.CoupledQuenchedLaws d)
    (hK : Regeneration.HasProbabilityLaws Q.measure K)
    (hD : Regeneration.annealedCoupledLaw Q.measure K
      (regenerationNoReturn hd (l / lam)) ≠ 0)
    (f : FieldPair d × Regeneration.CoupledSample d → ℝ≥0∞) :
    Regeneration.annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam)) *
      (∫⁻ ωz, f ωz ∂regenerationConditionedLaw hd Q lam l K hK hD) =
        ∫⁻ ωz in regenerationNoReturn hd (l / lam), f ωz
          ∂Regeneration.annealedCoupledLaw Q.measure K := by
  letI := Regeneration.annealedCoupledLaw_isProbabilityMeasure Q.measure K hK
  rw [regenerationConditionedLaw, ProbabilityTheory.cond, lintegral_smul_measure,
    smul_eq_mul, ← mul_assoc, ENNReal.mul_inv_cancel hD (measure_ne_top _ _), one_mul]

/-- An annealed moment and no-return mass bound give the corresponding conditional
moment at the SAME exponent. The constants may be fixed before the actual law. -/
theorem regenerationConditioned_exponentialMoment_le_of_annealed {d : ℕ} (hd : 2 ≤ d)
    {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (lam l a c₀ M₀ : ℝ)
    (hc₀ : 0 < c₀)
    (K : Regeneration.CoupledQuenchedLaws d)
    (hK : Regeneration.HasProbabilityLaws Q.measure K)
    (hD : Regeneration.annealedCoupledLaw Q.measure K
      (regenerationNoReturn hd (l / lam)) ≠ 0)
    (hc : ENNReal.ofReal c₀ ≤ Regeneration.annealedCoupledLaw Q.measure K
      (regenerationNoReturn hd (l / lam))) (j : ℕ)
    (hm : (∫⁻ ωz, regenerationExponentialWeight hd lam l a j ωz.2
      ∂Regeneration.annealedCoupledLaw Q.measure K) ≤ ENNReal.ofReal M₀) :
    (∫⁻ ωz, regenerationExponentialWeight hd lam l a j ωz.2
      ∂regenerationConditionedLaw hd Q lam l K hK hD) ≤ ENNReal.ofReal (M₀ / c₀) := by
  rw [regenerationConditionedLaw, ProbabilityTheory.cond, lintegral_smul_measure, smul_eq_mul]
  calc
    _ ≤ (ENNReal.ofReal c₀)⁻¹ * ENNReal.ofReal M₀ :=
      mul_le_mul' (ENNReal.inv_le_inv.mpr hc) ((lintegral_mono'
        Measure.restrict_le_self (le_refl _)).trans hm)
    _ = ENNReal.ofReal (M₀ / c₀) := by
      rw [← ENNReal.ofReal_inv_of_pos hc₀, ← ENNReal.ofReal_mul (inv_pos.mpr hc₀).le,
        div_eq_mul_inv, mul_comm]

/-- The real first-cycle exponential sum keeps the supplied structural bound. -/
theorem regenerationLatticeMass_exponential_tsum_le {d : ℕ} (hd : 2 ≤ d)
    {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (lam l a M : ℝ)
    (hlam : lam ≠ 0) (hM : 0 ≤ M)
    (K : Regeneration.CoupledQuenchedLaws d)
    (hK : Regeneration.HasProbabilityLaws Q.measure K)
    (hD : Regeneration.annealedCoupledLaw Q.measure K
      (regenerationNoReturn hd (l / lam)) ≠ 0)
    (hm : (∫⁻ ωz, regenerationExponentialWeight hd lam l a 1 ωz.2
      ∂regenerationConditionedLaw hd Q lam l K hK hD) ≤ ENNReal.ofReal M) :
    (∑' n : ℕ, regenerationLatticeMass hd Q lam l K hK hD n * Real.exp (a * n)) ≤ M := by
  have hs := regenerationLatticeMass_exponential_hasSum hd Q lam l a hlam K hK hD
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hm)
  rw [hs.tsum_eq]
  exact ENNReal.toReal_le_of_le_ofReal hM hm

/-- Consumer of actual first-cycle data for the generic analytic estimate.
All decay constants are chosen before the environment, force, coupling and n.
The moment and two-mass data remain internal proof obligations, not additional
hypotheses of the frozen numbered result. -/
theorem exists_actual_renewal_decay_of_first_cycle_data (ε a M : ℝ)
    (hε : 0 < ε) (ha : 0 < a) (hM : 0 < M) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
        (lam l : ℝ), lam ≠ 0 →
      ∀ (K : Regeneration.CoupledQuenchedLaws d)
        (hK : Regeneration.HasProbabilityLaws Q.measure K)
        (hD : Regeneration.annealedCoupledLaw Q.measure K
          (regenerationNoReturn hd (l / lam)) ≠ 0),
      ε ≤ regenerationLatticeMass hd Q lam l K hK hD 2 →
      ε ≤ regenerationLatticeMass hd Q lam l K hK hD 3 →
      (∫⁻ ωz, regenerationExponentialWeight hd lam l a 1 ωz.2
        ∂regenerationConditionedLaw hd Q lam l K hK hD) ≤ ENNReal.ofReal M →
      ∀ n : ℕ,
        |(∑' j : ℕ, latticeConvolutionPower (regenerationLatticeMass hd Q lam l K hK hD) j n) -
          (∑' k : ℕ, regenerationLatticeMass hd Q lam l K hK hD k * (k : ℝ))⁻¹| ≤
            C * Real.exp (-c * n) := by
  obtain ⟨c, C, hc, hC, hdecay⟩ := exists_uniform_renewal_coefficient_decay ε a M hε ha hM
  refine ⟨c, C, hc, hC, ?_⟩
  intro d hd Λ₀ r₀ Q lam l hlam K hK hD h2 h3 hm
  have hfin := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hm
  exact hdecay (regenerationLatticeMass hd Q lam l K hK hD)
    (regenerationLatticeMass_nonneg hd Q lam l K hK hD)
    (regenerationLatticeMass_hasSum_of_exponentialMoment hd Q lam l a hlam K hK hD hfin).tsum_eq
    h2 h3 (regenerationLatticeMass_exponential_hasSum hd Q lam l a hlam K hK hD hfin).summable
    (regenerationLatticeMass_exponential_tsum_le hd Q lam l a M hlam hM.le K hK hD hm)

/-- The conditional first-cycle mass is the exact annealed slice restricted to D,
divided by its no-return probability. The unrestricted first-cycle mass is distinct. -/
theorem regenerationLatticeMass_eq_annealed_ratio {d : ℕ} (hd : 2 ≤ d)
    {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (lam l : ℝ)
    (K : Regeneration.CoupledQuenchedLaws d)
    (hK : Regeneration.HasProbabilityLaws Q.measure K)
    (hD : Regeneration.annealedCoupledLaw Q.measure K
      (regenerationNoReturn hd (l / lam)) ≠ 0) (n : ℕ) :
    regenerationLatticeMass hd Q lam l K hK hD n =
      (Regeneration.annealedCoupledLaw Q.measure K).real
        (regenerationNoReturn hd (l / lam) ∩ {ωz |
          regenerationTime hd lam l 1 ωz.2 =
            (((n : ℝ≥0) * Regeneration.Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)}) /
      (Regeneration.annealedCoupledLaw Q.measure K).real
        (regenerationNoReturn hd (l / lam)) := by
  have ht : Measurable (fun ωz : FieldPair d × Regeneration.CoupledSample d =>
      regenerationTime hd lam l 1 ωz.2) :=
    (Regeneration.measurable_regenerationTime _ _ _ _ _).comp measurable_snd
  have hs : MeasurableSet {ωz : FieldPair d × Regeneration.CoupledSample d |
      regenerationTime hd lam l 1 ωz.2 =
        (((n : ℝ≥0) * Regeneration.Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)} :=
    ht (measurableSet_singleton _)
  unfold regenerationLatticeMass regenerationConditionedLaw
  rw [measureReal_def, ProbabilityTheory.cond_apply' hs,
    ENNReal.toReal_mul, ENNReal.toReal_inv, div_eq_mul_inv, mul_comm]
  rfl

end EinsteinFull.Work.W5
