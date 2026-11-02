import EinsteinFull.Blueprint.Foundation.node_app_u3A_factorization_u23_coupling_u2D_scope
import EinsteinFull.Blueprint.Foundation.node_app_u3A_regen_u2D_tails
import EinsteinFull.Work.W1.RegenerationReuseSupport
import EinsteinRelation.Regeneration.FiniteHistoryTrialEvent
import EinsteinRelation.Probability.FiniteHistoryStopping
import EinsteinRelation.Probability.FiniteHistoryFiltration

/-!
Support for `app:factorization#coupling-scope`, paper/main.tex:1474–1487,
1516–1523. The literal recursion supplies measurability, the lower grid bound,
and the complete future record at every finite time. Conditioning transfers
annealed almost-everywhere finiteness. The supplied tail dependency proves the
first-cycle assertion above its construction-scale threshold. Fixed-trial
prebridges belong to the exact stopped history, and their fresh-bit masses
decompose the finite-start event into disjoint deterministic grid slices.

This module does not prove the exact node reduction: arbitrary-scale and
later-cycle annealed finiteness remain unresolved. In particular, no renewal
invariance or independent-cycle premise is introduced here.
-/

open MeasureTheory
open scoped NNReal ENNReal

namespace EinsteinFull.Blueprint

open EinsteinRelation

/-- Both literal objects are measurable, including on the infinite-time branch. -/
theorem coupling_scope_measurable {d : ℕ} (hd : 2 ≤ d) (lam l : ℝ) (k : ℕ) :
    Measurable (regenerationTime hd lam l k) ∧
      Measurable (regenerationRecord hd lam l k) :=
  ⟨measurable_regenerationTime hd lam l k, measurable_regenerationRecord hd lam l k⟩

/-- Pointwise characterization of finite iterates, retaining the exact `2*k`
bound and both restricted reduced fields in the record. -/
theorem coupling_scope_finite_iff_grid_record {d : ℕ} (hd : 2 ≤ d)
    (lam l : ℝ) (hlam : 0 < lam) (hl : 0 < l) (k : ℕ)
    (q : FieldPair d × Regeneration.CoupledSample d) :
    regenerationTime hd lam l k q.2 ≠ ⊤ ↔
      ∃ n : ℕ, 2 * k ≤ n ∧
        regenerationTime hd lam l k q.2 =
          (((n : ℝ≥0) * Regeneration.Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞) ∧
        regenerationRecord hd lam l k q =
          Regeneration.futureRecord (Regeneration.Renewal.regenDelta lam) (l / lam)
            q.1 q.2 (Regeneration.Renewal.forceCoord hd)
            ((n : ℝ≥0) * Regeneration.Renewal.regenDelta lam) := by
  constructor
  · intro hfin
    have hΔ : 0 < Regeneration.Renewal.regenDelta lam :=
      Real.toNNReal_pos.mpr (inv_pos.mpr (sq_pos_of_pos hlam))
    obtain ⟨n, hn⟩ := Regeneration.regenerationTime_mem_grid _ hΔ lam (l / lam)
      q.2 (Regeneration.Renewal.forceCoord hd) k hfin
    change regenerationTime hd lam l k q.2 = _ at hn
    have hb := Regeneration.nat_two_step_le_regenerationTime _ hΔ lam (l / lam)
      hlam (div_pos hl hlam) q.2 (Regeneration.Renewal.forceCoord hd) k
    change (k : ℝ≥0∞) * (2 * (Regeneration.Renewal.regenDelta lam : ℝ≥0∞)) ≤
      regenerationTime hd lam l k q.2 at hb
    rw [hn] at hb
    have hb' : ((2 * k : ℕ) : ℝ≥0) * Regeneration.Renewal.regenDelta lam ≤
        (n : ℝ≥0) * Regeneration.Renewal.regenDelta lam := by
      have hb'' : ((2 * k : ℕ) : ℝ≥0∞) *
          (Regeneration.Renewal.regenDelta lam : ℝ≥0∞) ≤
          (((n : ℝ≥0) * Regeneration.Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞) := by
        simpa only [Nat.cast_mul, Nat.cast_ofNat, mul_assoc, mul_comm, mul_left_comm]
          using hb
      exact_mod_cast hb''
    have hkn : 2 * k ≤ n := by
      exact_mod_cast (mul_le_mul_iff_left₀ hΔ).mp hb'
    refine ⟨n, hkn, hn, ?_⟩
    change Regeneration.futureRecord _ _ q.1 q.2 _
      (regenerationTime hd lam l k q.2).toNNReal = _
    rw [hn, ENNReal.toNNReal_coe]
  · rintro ⟨n, _, hn, _⟩
    rw [hn]
    exact ENNReal.coe_ne_top

/-- Under any measure, the finite-grid/record conclusion is equivalent to
almost-everywhere finiteness; this equivalence supplies no finiteness premise. -/
theorem coupling_scope_ae_finite_iff_grid_record {d : ℕ} (hd : 2 ≤ d)
    (lam l : ℝ) (hlam : 0 < lam) (hl : 0 < l) (k : ℕ)
    (ρ : Measure (FieldPair d × Regeneration.CoupledSample d)) :
    (∀ᵐ q ∂ρ, regenerationTime hd lam l k q.2 ≠ ⊤) ↔
      ∀ᵐ q ∂ρ, ∃ n : ℕ, 2 * k ≤ n ∧
        regenerationTime hd lam l k q.2 =
          (((n : ℝ≥0) * Regeneration.Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞) ∧
        regenerationRecord hd lam l k q =
          Regeneration.futureRecord (Regeneration.Renewal.regenDelta lam) (l / lam)
            q.1 q.2 (Regeneration.Renewal.forceCoord hd)
            ((n : ℝ≥0) * Regeneration.Renewal.regenDelta lam) :=
  Filter.eventually_congr (Filter.Eventually.of_forall fun q =>
    coupling_scope_finite_iff_grid_record hd lam l hlam hl k q)

/-- The two-law finiteness obligation is exactly its annealed part, since the
literal D-conditioned law is absolutely continuous with respect to that law. -/
theorem coupling_scope_both_laws_finite_iff {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (lam l : ℝ)
    (K : Regeneration.CoupledQuenchedLaws d)
    (hK : Regeneration.HasProbabilityLaws Q.measure K)
    (hD : Regeneration.annealedCoupledLaw Q.measure K
      (regenerationNoReturn hd (l / lam)) ≠ 0) (k : ℕ) :
    (∀ ρ ∈ ({Regeneration.annealedCoupledLaw Q.measure K,
        regenerationConditionedLaw hd Q lam l K hK hD} :
          Set (Measure (FieldPair d × Regeneration.CoupledSample d))),
      ∀ᵐ q ∂ρ, regenerationTime hd lam l k q.2 ≠ ⊤) ↔
      ∀ᵐ q ∂Regeneration.annealedCoupledLaw Q.measure K,
        regenerationTime hd lam l k q.2 ≠ ⊤ := by
  constructor
  · intro h
    exact h _ (Set.mem_insert _ _)
  · intro h ρ hρ
    rcases Set.mem_insert_iff.mp hρ with hρ | hρ
    · subst ρ
      exact h
    · have hρ' := Set.mem_singleton_iff.mp hρ
      subst ρ
      exact (regenerationConditionedLaw_absolutelyContinuous hd Q lam l K hK hD).ae_le h

/-- The literal conclusion at cycle zero holds everywhere, at every scale. -/
theorem coupling_scope_zero_grid_record {d : ℕ} (hd : 2 ≤ d) (lam l : ℝ)
    (q : FieldPair d × Regeneration.CoupledSample d) :
    ∃ n : ℕ, 2 * 0 ≤ n ∧
      regenerationTime hd lam l 0 q.2 =
        (((n : ℝ≥0) * Regeneration.Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞) ∧
      regenerationRecord hd lam l 0 q =
        Regeneration.futureRecord (Regeneration.Renewal.regenDelta lam) (l / lam)
          q.1 q.2 (Regeneration.Renewal.forceCoord hd)
          ((n : ℝ≥0) * Regeneration.Renewal.regenDelta lam) := by
  refine ⟨0, le_rfl, ?_, ?_⟩
  · simp only [regenerationTime, Regeneration.regenerationTime, Nat.cast_zero,
      zero_mul, ENNReal.coe_zero]
  · change Regeneration.futureRecord _ _ q.1 q.2 _
      (Regeneration.regenerationTime _ lam (l / lam) q.2 _ 0).toNNReal = _
    simp only [Regeneration.regenerationTime, ENNReal.toNNReal_zero, Nat.cast_zero,
      zero_mul]

/-- A deterministic propagation step: exhaustion at every deterministic grid
shift implies finite iterates. The exhaustion hypothesis remains an internal
analytic obligation, not a new input to the node reduction. -/
theorem coupling_scope_finite_of_grid_exhaustion {d : ℕ} (hd : 2 ≤ d)
    (lam l : ℝ) (hlam : 0 < lam) (z : Regeneration.CoupledSample d)
    (hgrid : ∀ m : ℕ,
      Regeneration.firstRegenerationTime (Regeneration.Renewal.regenDelta lam)
        lam (l / lam)
        (Regeneration.sampleTimeShift (Regeneration.Renewal.regenDelta lam) z
          ((m : ℝ≥0) * Regeneration.Renewal.regenDelta lam))
        (Regeneration.Renewal.forceCoord hd) ≠ ⊤) :
    ∀ k : ℕ, regenerationTime hd lam l k z ≠ ⊤ := by
  have hΔ : 0 < Regeneration.Renewal.regenDelta lam :=
    Real.toNNReal_pos.mpr (inv_pos.mpr (sq_pos_of_pos hlam))
  intro k
  induction k with
  | zero => exact ENNReal.zero_ne_top
  | succ k ih =>
    obtain ⟨m, hm⟩ := Regeneration.regenerationTime_mem_grid _ hΔ lam (l / lam)
      z (Regeneration.Renewal.forceCoord hd) k ih
    have ht : (regenerationTime hd lam l k z).toNNReal =
        (m : ℝ≥0) * Regeneration.Renewal.regenDelta lam := by
      change regenerationTime hd lam l k z = _ at hm
      rw [hm, ENNReal.toNNReal_coe]
    change Regeneration.regenerationTime _ lam (l / lam) z _ (k + 1) ≠ ⊤
    have hprev : Regeneration.regenerationTime (Regeneration.Renewal.regenDelta lam)
        lam (l / lam) z (Regeneration.Renewal.forceCoord hd) k ≠ ⊤ := ih
    rw [Regeneration.regenerationTime, ite_eq_right hprev]
    change regenerationTime hd lam l k z +
      Regeneration.firstRegenerationTime _ lam (l / lam)
        (Regeneration.sampleTimeShift _ z (regenerationTime hd lam l k z).toNNReal) _ ≠ ⊤
    rw [ht]
    exact ENNReal.add_ne_top.mpr ⟨ih, hgrid m⟩

/-- Countable intersection lets deterministic-grid exhaustion propagate to
every cycle on one full-measure set. No random-endpoint law is assumed. -/
theorem coupling_scope_ae_finite_of_grid_exhaustion {d : ℕ} (hd : 2 ≤ d)
    (lam l : ℝ) (hlam : 0 < lam)
    (ρ : Measure (FieldPair d × Regeneration.CoupledSample d))
    (hgrid : ∀ m : ℕ, ∀ᵐ q ∂ρ,
      Regeneration.firstRegenerationTime (Regeneration.Renewal.regenDelta lam)
        lam (l / lam)
        (Regeneration.sampleTimeShift (Regeneration.Renewal.regenDelta lam) q.2
          ((m : ℝ≥0) * Regeneration.Renewal.regenDelta lam))
        (Regeneration.Renewal.forceCoord hd) ≠ ⊤) :
    ∀ᵐ q ∂ρ, ∀ k : ℕ, regenerationTime hd lam l k q.2 ≠ ⊤ := by
  filter_upwards [ae_all_iff.mpr hgrid] with q hq
  exact coupling_scope_finite_of_grid_exhaustion hd lam l hlam q.2 hq

/-- The actual tail dependency gives the full grid/record assertion for the
first cycle at its construction scales, with an arbitrary supplied nonzero-D
witness. This is support for the node, not the all-scale/all-cycle reduction. -/
theorem coupling_scope_first_cycle_of_regen_tails
    (htails : node_app_u3A_regen_u2D_tailsStmt)
    (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ) :
    ∃ l₀ : ℝ, 0 < l₀ ∧ r₀ < 2 * l₀ ∧
      ∀ l : ℝ, l₀ ≤ l → ∀ δ : ℝ, 0 < δ → δ < 1 →
      ∀ (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
        (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
        (hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K)
        (hD : Regeneration.annealedCoupledLaw Q.measure K
          (regenerationNoReturn hd (l / lam)) ≠ 0),
      ∀ ρ ∈ ({Regeneration.annealedCoupledLaw Q.measure K,
          regenerationConditionedLaw hd Q lam l K hK.1 hD} :
            Set (Measure (FieldPair d × Regeneration.CoupledSample d))),
        ∀ᵐ q ∂ρ, ∃ n : ℕ, 2 * 1 ≤ n ∧
          regenerationTime hd lam l 1 q.2 =
            (((n : ℝ≥0) * Regeneration.Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞) ∧
          regenerationRecord hd lam l 1 q =
            Regeneration.futureRecord (Regeneration.Renewal.regenDelta lam) (l / lam)
              q.1 q.2 (Regeneration.Renewal.forceCoord hd)
              ((n : ℝ≥0) * Regeneration.Renewal.regenDelta lam) := by
  obtain ⟨l₀, hl₀, hsep, htail⟩ := htails d hd Λ₀ r₀
  refine ⟨l₀, hl₀, hsep, ?_⟩
  intro l hll δ hδ₀ hδ₁ Q lam h₀ h₁ P K hK hD ρ hρ
  obtain ⟨c, C, a, M, _, _, _, _, _, hm⟩ := htail l hll δ hδ₀ hδ₁
  obtain ⟨_, _, _, hmoment, _⟩ := hm Q lam h₀ h₁ P K hK
  have hfinite := Work.W5.regenerationTime_ne_top_ae_of_exponentialMoment
    hd lam l a 1 (Regeneration.annealedCoupledLaw Q.measure K)
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hmoment)
  have hboth := (coupling_scope_both_laws_finite_iff hd Q lam l K hK.1 hD 1).mpr hfinite
  exact (coupling_scope_ae_finite_iff_grid_record hd lam l h₀
    (lt_of_lt_of_le hl₀ hll) 1 ρ).mp (hboth ρ hρ)

/-- Exact identification of the unresolved analytic obligation, with the
original ordered parameter and nonzero-D scope. This is an equivalence, not a
reduction from the tail dependency or a new literature input. -/
theorem coupling_scope_iff_annealed_finite :
    node_app_u3A_factorization_u23_coupling_u2D_scopeStmt ↔
      ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ)
        (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
        (l δ : ℝ), 0 < l → r₀ < 2 * l → 0 < δ → δ < 1 →
        ∀ (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
          (_hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K),
        Regeneration.annealedCoupledLaw Q.measure K
          (regenerationNoReturn hd (l / lam)) ≠ 0 →
        ∀ k : ℕ, ∀ᵐ q ∂Regeneration.annealedCoupledLaw Q.measure K,
          regenerationTime hd lam l k q.2 ≠ ⊤ := by
  constructor
  · intro h d hd Λ₀ r₀ Q lam h₀ h₁ l δ hl hsep hδ₀ hδ₁ P K hK hD k
    have hscope := h d hd Λ₀ r₀ Q lam h₀ h₁ l δ hl hsep hδ₀ hδ₁ P K hK hD k
    exact (coupling_scope_ae_finite_iff_grid_record hd lam l h₀ hl k _).mpr
      (hscope.2.2 _ (Set.mem_insert _ _))
  · intro h d hd Λ₀ r₀ Q lam h₀ h₁ l δ hl hsep hδ₀ hδ₁ P K hK hD
    dsimp only
    intro k
    refine ⟨(coupling_scope_measurable hd lam l k).1,
      (coupling_scope_measurable hd lam l k).2, ?_⟩
    intro ρ hρ
    have hfinite := h d hd Λ₀ r₀ Q lam h₀ h₁ l δ hl hsep hδ₀ hδ₁ P K hK hD k
    exact (coupling_scope_ae_finite_iff_grid_record hd lam l h₀ hl k ρ).mp
      ((coupling_scope_both_laws_finite_iff hd Q lam l K hK.1 hD k).mpr hfinite ρ hρ)

/-- The fixed-trial prebridge event: only bit `m` is forced, and the
literal trial index `j` is retained rather than existentially quantified. -/
def couplingScopeTrialPrebridge {d : ℕ} (Δ : ℝ≥0) (lam R : ℝ)
    (i : Fin d) (j m : ℕ) : Set (Regeneration.CoupledSample d) :=
  {z | Regeneration.trialStartSequence Δ lam R (Regeneration.forceSampleBit m z) i j =
    ((((m + 1 : ℕ) : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞)}

/-- Fixed-trial prebridges are globally measurable, before restricting to the
exact history sigma-algebra. -/
theorem coupling_scope_measurableSet_trial_prebridge {d : ℕ} (Δ : ℝ≥0)
    (lam R : ℝ) (i : Fin d) (j m : ℕ) :
    MeasurableSet (couplingScopeTrialPrebridge Δ lam R i j m) :=
  measurableSet_eq_fun
    ((Regeneration.measurable_trialStartSequence Δ lam R i j).comp
      (Regeneration.measurable_forceSampleBit m)) measurable_const

/-- A fixed-trial prebridge depends only on the path through `mΔ` and the
bits strictly before `m`; the bit at `m` is forced on both histories. -/
theorem coupling_scope_mem_trial_prebridge_stoppedHistory_iff {d : ℕ}
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (lam R : ℝ) (hR : 0 < R) (i : Fin d)
    (j m : ℕ) (z : Regeneration.CoupledSample d) :
    z ∈ couplingScopeTrialPrebridge Δ lam R i j m ↔
      Probability.stoppedHistorySample Δ m z ∈ couplingScopeTrialPrebridge Δ lam R i j m := by
  have hpre : ∀ t ∈ Set.Icc (0 : ℝ≥0) ((m : ℝ≥0) * Δ),
      (Regeneration.forceSampleBit m z).1 t =
        (Regeneration.forceSampleBit m (Probability.stoppedHistorySample Δ m z)).1 t := by
    intro t ht
    exact (Probability.stoppedHistorySample_path Δ m z t ht.2).symm
  have hbits : ∀ k : ℕ, (k : ℝ≥0) * Δ ≤ (m : ℝ≥0) * Δ →
      (Regeneration.forceSampleBit m z).2 k =
        (Regeneration.forceSampleBit m (Probability.stoppedHistorySample Δ m z)).2 k := by
    intro k hk
    have hkm : k ≤ m := by
      exact_mod_cast (mul_le_mul_iff_left₀ hΔ).mp hk
    by_cases heq : k = m
    · subst k
      simp only [Regeneration.forceSampleBit, Function.update_self]
    · have hlt : k < m := lt_of_le_of_ne hkm heq
      simp only [Regeneration.forceSampleBit, Function.update_of_ne heq,
        Probability.stoppedHistorySample_bit Δ m z k hlt]
  have htime : (((m + 1 : ℕ) : ℝ≥0) * Δ) = (m : ℝ≥0) * Δ + Δ := by
    rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul]
  change Regeneration.trialStartSequence Δ lam R (Regeneration.forceSampleBit m z) i j = _ ↔
    Regeneration.trialStartSequence Δ lam R
      (Regeneration.forceSampleBit m (Probability.stoppedHistorySample Δ m z)) i j = _
  constructor
  · intro hn
    have heq := Regeneration.trialStartSequence_eq_of_prefix Δ hΔ lam R hR
      (Regeneration.forceSampleBit m z)
      (Regeneration.forceSampleBit m (Probability.stoppedHistorySample Δ m z)) i j
      ((m : ℝ≥0) * Δ) hpre hbits (by rw [hn, htime])
    exact heq.symm.trans hn
  · intro hn
    have heq := Regeneration.trialStartSequence_eq_of_prefix Δ hΔ lam R hR
      (Regeneration.forceSampleBit m (Probability.stoppedHistorySample Δ m z))
      (Regeneration.forceSampleBit m z) i j ((m : ℝ≥0) * Δ)
      (fun t ht => (hpre t ht).symm) (fun k hk => (hbits k hk).symm)
      (by rw [hn, htime])
    exact heq.symm.trans hn

/-- The fixed-trial prebridge is measurable for the exact finite history,
with Bernoulli indices strictly below `m`. -/
theorem coupling_scope_measurableSet_trial_prebridge_finiteHistory {d : ℕ}
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (lam R : ℝ) (hR : 0 < R)
    (i : Fin d) (j m : ℕ) :
    @MeasurableSet (Regeneration.CoupledSample d) (Regeneration.finiteHistorySigma Δ m)
      (couplingScopeTrialPrebridge Δ lam R i j m) := by
  have hset : couplingScopeTrialPrebridge Δ lam R i j m =
      Probability.stoppedHistorySample Δ m ⁻¹' couplingScopeTrialPrebridge Δ lam R i j m := by
    ext z
    exact coupling_scope_mem_trial_prebridge_stoppedHistory_iff Δ hΔ lam R hR i j m z
  rw [hset]
  exact Probability.measurable_stoppedHistorySample Δ m
    (coupling_scope_measurableSet_trial_prebridge Δ lam R i j m)

/-- An actual fixed-trial start at `(m+1)Δ` is exactly its prebridge together
with the actual successful bit `m`. No finite-start assumption is used. -/
theorem coupling_scope_trial_start_slice_iff {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ)
    (lam R : ℝ) (z : Regeneration.CoupledSample d) (i : Fin d) (j m : ℕ) :
    Regeneration.trialStartSequence Δ lam R z i j =
        ((((m + 1 : ℕ) : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞) ↔
      z ∈ couplingScopeTrialPrebridge Δ lam R i j m ∧ z.2 m = true := by
  constructor
  · intro ht
    have hb := Regeneration.trialStartSequence_last_bit Δ hΔ lam R z i j m ht
    refine ⟨?_, hb⟩
    change Regeneration.trialStartSequence Δ lam R (Regeneration.forceSampleBit m z) i j = _
    rw [Regeneration.forceSampleBit_eq_self m z hb]
    exact ht
  · rintro ⟨ht, hb⟩
    change Regeneration.trialStartSequence Δ lam R (Regeneration.forceSampleBit m z) i j = _ at ht
    rwa [Regeneration.forceSampleBit_eq_self m z hb] at ht

/-- The actual annealed mass of a fixed-trial start slice is `δ` times its
fixed-trial prebridge mass, by the supplied coupling's finite-history freshness. -/
theorem coupling_scope_measure_trial_start_slice {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (K : Regeneration.CoupledQuenchedLaws d) (hK : Regeneration.HasProbabilityLaws Q K)
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (δ : ℝ) (hδ : 0 ≤ δ)
    (hFresh : Regeneration.HasFreshBits Q Δ δ K) (lam R : ℝ) (hR : 0 < R)
    (i : Fin d) (j m : ℕ) :
    Regeneration.annealedCoupledLaw Q K
      {q | Regeneration.trialStartSequence Δ lam R q.2 i j =
        ((((m + 1 : ℕ) : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞)} =
      ENNReal.ofReal δ * Regeneration.annealedCoupledLaw Q K
        {q | q.2 ∈ couplingScopeTrialPrebridge Δ lam R i j m} := by
  have hset : {q : FieldPair d × Regeneration.CoupledSample d |
      Regeneration.trialStartSequence Δ lam R q.2 i j =
        ((((m + 1 : ℕ) : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞)} =
      {q | q.2 ∈ couplingScopeTrialPrebridge Δ lam R i j m ∧ q.2.2 m = true} := by
    ext q
    exact coupling_scope_trial_start_slice_iff Δ hΔ lam R q.2 i j m
  rw [hset]
  exact Regeneration.measure_annealed_fresh_bit Q K hK Δ δ hδ hFresh m _
    (coupling_scope_measurableSet_trial_prebridge_finiteHistory Δ hΔ lam R hR i j m)

/-- Specialization to the actual Section 3 coupling uses its existing freshness
clause, without adding a premise to the coupling-scope node. -/
theorem coupling_scope_measure_trial_start_slice_of_coupling {d : ℕ} (hd : 2 ≤ d)
    {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (lam l δ : ℝ)
    (h₀ : 0 < lam) (h₁ : lam ≤ 1) (hl : 0 < l) (hδ : 0 ≤ δ)
    (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K) (j m : ℕ) :
    Regeneration.annealedCoupledLaw Q.measure K
      {q | Regeneration.trialStartSequence (Regeneration.Renewal.regenDelta lam)
        lam (l / lam) q.2 (Regeneration.Renewal.forceCoord hd) j =
          ((((m + 1 : ℕ) : ℝ≥0) * Regeneration.Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)} =
      ENNReal.ofReal δ * Regeneration.annealedCoupledLaw Q.measure K
        {q | q.2 ∈ couplingScopeTrialPrebridge (Regeneration.Renewal.regenDelta lam)
          lam (l / lam) (Regeneration.Renewal.forceCoord hd) j m} :=
  coupling_scope_measure_trial_start_slice Q.measure K hK.1 _
    (Real.toNNReal_pos.mpr (inv_pos.mpr (sq_pos_of_pos h₀))) δ hδ hK.2.2.2.1
    lam (l / lam) (div_pos hl h₀) _ j m

/-- Distinct grid endpoints give disjoint actual slices of any fixed trial,
including when that trial can be infinite on other samples. -/
theorem coupling_scope_disjoint_trial_start_slices {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ)
    (lam R : ℝ) (i : Fin d) (j : ℕ) :
    Pairwise fun m n : ℕ => Disjoint
      {z : Regeneration.CoupledSample d | Regeneration.trialStartSequence Δ lam R z i j =
        ((((m + 1 : ℕ) : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞)}
      {z : Regeneration.CoupledSample d | Regeneration.trialStartSequence Δ lam R z i j =
        ((((n + 1 : ℕ) : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞)} := by
  intro m n hmn
  refine Set.disjoint_left.mpr ?_
  intro z hm hn
  have heq : ((m + 1 : ℕ) : ℝ≥0) * Δ = ((n + 1 : ℕ) : ℝ≥0) * Δ :=
    ENNReal.coe_inj.mp (hm.symm.trans hn)
  have hcast : ((m + 1 : ℕ) : ℝ≥0) = ((n + 1 : ℕ) : ℝ≥0) :=
    mul_right_cancel₀ hΔ.ne' heq
  have hnat : m + 1 = n + 1 := by exact_mod_cast hcast
  exact hmn (Nat.add_right_cancel hnat)

/-- Finite starts decompose into fixed-trial prebridges and their actual last
bits. Grid attainment and the positive lower bound are proved by the literal
recursion, rather than assumed as candidate finiteness. -/
theorem coupling_scope_trial_start_finite_iff {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ)
    (lam R : ℝ) (hlam : 0 < lam) (hR : 0 < R)
    (z : Regeneration.CoupledSample d) (i : Fin d) (j : ℕ) :
    Regeneration.trialStartSequence Δ lam R z i j ≠ ⊤ ↔
      ∃ m : ℕ, z ∈ couplingScopeTrialPrebridge Δ lam R i j m ∧ z.2 m = true := by
  constructor
  · intro hfin
    obtain ⟨k, hk⟩ := Regeneration.trialStartSequence_mem_grid Δ hΔ lam R z i j hfin
    have hb := Regeneration.two_step_le_trialStartSequence Δ hΔ lam R hlam hR z i j
    rw [hk] at hb
    have hb' : (2 : ℝ≥0) * Δ ≤ (k : ℝ≥0) * Δ := by exact_mod_cast hb
    have hk2 : 2 ≤ k := by exact_mod_cast (mul_le_mul_iff_left₀ hΔ).mp hb'
    cases k with
    | zero => omega
    | succ m => exact ⟨m, (coupling_scope_trial_start_slice_iff Δ hΔ lam R z i j m).mp hk⟩
  · rintro ⟨m, hm⟩
    rw [(coupling_scope_trial_start_slice_iff Δ hΔ lam R z i j m).mpr hm]
    exact ENNReal.coe_ne_top

/-- Summing the disjoint deterministic slices gives the finite-start mass as
the sum of their fresh-bit prebridge masses. This identity does not assert
that the fixed trial is almost surely finite. -/
theorem coupling_scope_measure_trial_start_finite {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (K : Regeneration.CoupledQuenchedLaws d) (hK : Regeneration.HasProbabilityLaws Q K)
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (δ : ℝ) (hδ : 0 ≤ δ)
    (hFresh : Regeneration.HasFreshBits Q Δ δ K) (lam R : ℝ)
    (hlam : 0 < lam) (hR : 0 < R) (i : Fin d) (j : ℕ) :
    Regeneration.annealedCoupledLaw Q K
      {q | Regeneration.trialStartSequence Δ lam R q.2 i j ≠ ⊤} =
      ∑' m : ℕ, ENNReal.ofReal δ * Regeneration.annealedCoupledLaw Q K
        {q | q.2 ∈ couplingScopeTrialPrebridge Δ lam R i j m} := by
  let A : ℕ → Set (FieldPair d × Regeneration.CoupledSample d) := fun m =>
    {q | Regeneration.trialStartSequence Δ lam R q.2 i j =
      ((((m + 1 : ℕ) : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞)}
  have hset : {q : FieldPair d × Regeneration.CoupledSample d |
      Regeneration.trialStartSequence Δ lam R q.2 i j ≠ ⊤} = ⋃ m, A m := by
    ext q
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    rw [coupling_scope_trial_start_finite_iff Δ hΔ lam R hlam hR q.2 i j]
    exact exists_congr fun m => (coupling_scope_trial_start_slice_iff Δ hΔ lam R q.2 i j m).symm
  have hdisj : Pairwise fun m n => Disjoint (A m) (A n) := by
    intro m n hmn
    exact Set.disjoint_left.mpr fun _ hm hn =>
      Set.disjoint_left.mp (coupling_scope_disjoint_trial_start_slices Δ hΔ lam R i j hmn)
        hm hn
  have hmeas : ∀ m, MeasurableSet (A m) := fun _ =>
    measurableSet_eq_fun ((Regeneration.measurable_trialStartSequence Δ lam R i j).comp
      measurable_snd) measurable_const
  rw [hset, measure_iUnion hdisj hmeas]
  exact tsum_congr fun m =>
    coupling_scope_measure_trial_start_slice Q K hK Δ hΔ δ hδ hFresh lam R hR i j m

/-- The actual candidate sequence after a deterministic grid restart, with
its level read from the original sample's past. -/
noncomputable def couplingScopeCandidate {d : ℕ} (Δ : ℝ≥0) (lam R : ℝ)
    (A : Regeneration.CoupledSample d → ℝ) (m : ℕ) (i : Fin d)
    (n : ℕ) (z : Regeneration.CoupledSample d) : ℝ≥0∞ :=
  Regeneration.roundedCandidateSequence Δ lam R (A z)
    (Regeneration.sampleTimeShift Δ z ((m : ℝ≥0) * Δ)) i n

/-- A finite prefix of actual selected false coins. Each witness is an exact
finite candidate grid index; infinite candidates contribute no selected coin. -/
def couplingScopeCandidateFalsePrefix {d : ℕ} (Δ : ℝ≥0) (lam R : ℝ)
    (A : Regeneration.CoupledSample d → ℝ) (m : ℕ) (i : Fin d)
    (N : ℕ) : Set (Regeneration.CoupledSample d) :=
  {z | ∀ j < N, ∃ k : ℕ,
    couplingScopeCandidate Δ lam R A m i j z = (((k : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞) ∧
      z.2 (m + k) = false}

/-- The next candidate is selected, while all earlier selected coins are false;
the coin at the displayed next candidate has not yet been tested. -/
def couplingScopeCandidatePrebit {d : ℕ} (Δ : ℝ≥0) (lam R : ℝ)
    (A : Regeneration.CoupledSample d → ℝ) (m : ℕ) (i : Fin d)
    (N k : ℕ) : Set (Regeneration.CoupledSample d) :=
  {z | couplingScopeCandidate Δ lam R A m i N z =
      (((k : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞) ∧
    z ∈ couplingScopeCandidateFalsePrefix Δ lam R A m i N}

/-- Actual candidate chronology holds even when a later candidate is infinite. -/
theorem coupling_scope_candidate_monotone {d : ℕ} (Δ : ℝ≥0) (lam R : ℝ)
    (A : Regeneration.CoupledSample d → ℝ) (m : ℕ) (i : Fin d)
    (z : Regeneration.CoupledSample d) :
    Monotone (fun n => couplingScopeCandidate Δ lam R A m i n z) := by
  apply monotone_nat_of_le_succ
  intro n
  unfold couplingScopeCandidate
  by_cases ht : Regeneration.roundedCandidateSequence Δ lam R (A z)
      (Regeneration.sampleTimeShift Δ z ((m : ℝ≥0) * Δ)) i n = ⊤
  · rw [Regeneration.roundedCandidateSequence, ite_eq_left ht]
    exact le_top
  · rw [Regeneration.roundedCandidateSequence, ite_eq_right ht]
    exact le_add_right le_rfl

/-- Distinct finite candidates are strictly ordered: every further candidate
adds at least one positive grid step. The initial level need not be positive. -/
theorem coupling_scope_candidate_lt {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ)
    (lam R : ℝ) (hlam : 0 < lam) (hR : 0 < R)
    (A : Regeneration.CoupledSample d → ℝ) (m : ℕ) (i : Fin d)
    (z : Regeneration.CoupledSample d) {j N : ℕ} (hjN : j < N)
    (hfin : couplingScopeCandidate Δ lam R A m i j z ≠ ⊤) :
    couplingScopeCandidate Δ lam R A m i j z <
      couplingScopeCandidate Δ lam R A m i N z := by
  have hstep := Regeneration.step_le_firstRoundedCandidate Δ hΔ lam R (3 * lam * R) hR
    (div_pos (mul_pos (mul_pos (by norm_num) hlam) hR) hlam)
    (Regeneration.pathTimeShift
      (Regeneration.sampleTimeShift Δ z ((m : ℝ≥0) * Δ)).1
      (couplingScopeCandidate Δ lam R A m i j z).toNNReal) i
  have hlt : couplingScopeCandidate Δ lam R A m i j z <
      couplingScopeCandidate Δ lam R A m i j z + (Δ : ℝ≥0∞) := by
    rw [← ENNReal.coe_toNNReal hfin, ← ENNReal.coe_add]
    exact ENNReal.coe_lt_coe.mpr (lt_add_of_pos_right _ hΔ)
  have hnext : couplingScopeCandidate Δ lam R A m i j z <
      couplingScopeCandidate Δ lam R A m i (j + 1) z := by
    have hfin' := hfin
    unfold couplingScopeCandidate at hfin' ⊢
    rw [Regeneration.roundedCandidateSequence, ite_eq_right hfin']
    exact hlt.trans_le (add_le_add le_rfl hstep)
  exact hnext.trans_le (coupling_scope_candidate_monotone Δ lam R A m i z hjN)

/-- Joint measurability retains the actual history-dependent level. -/
theorem coupling_scope_measurable_candidate {d : ℕ} (Δ : ℝ≥0) (lam R : ℝ)
    (A : Regeneration.CoupledSample d → ℝ) (hA : Measurable A)
    (m : ℕ) (i : Fin d) (n : ℕ) :
    Measurable (couplingScopeCandidate Δ lam R A m i n) :=
  (Regeneration.measurable_roundedCandidateSequence Δ lam R i n).comp
    (hA.prodMk ((Regeneration.measurable_sampleTimeShift Δ).comp
      (measurable_const.prodMk measurable_id)))

/-- The finite guarded false prefix is a countable combination of actual
candidate slices and actual coordinate-coin events. -/
theorem coupling_scope_measurableSet_candidate_false_prefix {d : ℕ}
    (Δ : ℝ≥0) (lam R : ℝ) (A : Regeneration.CoupledSample d → ℝ)
    (hA : Measurable A) (m : ℕ) (i : Fin d) (N : ℕ) :
    MeasurableSet (couplingScopeCandidateFalsePrefix Δ lam R A m i N) := by
  simp only [couplingScopeCandidateFalsePrefix, Set.ofPred_forall, Set.ofPred_exists]
  apply MeasurableSet.iInter
  intro j
  apply MeasurableSet.iInter
  intro _hj
  apply MeasurableSet.iUnion
  intro k
  exact (measurableSet_eq_fun
    (coupling_scope_measurable_candidate Δ lam R A hA m i j) measurable_const).inter
    (measurableSet_eq_fun ((measurable_pi_apply (m + k)).comp measurable_snd)
      measurable_const)

/-- Global measurability of the pre-bit slices. -/
theorem coupling_scope_measurableSet_candidate_prebit {d : ℕ}
    (Δ : ℝ≥0) (lam R : ℝ) (A : Regeneration.CoupledSample d → ℝ)
    (hA : Measurable A) (m : ℕ) (i : Fin d) (N k : ℕ) :
    MeasurableSet (couplingScopeCandidatePrebit Δ lam R A m i N k) :=
  (measurableSet_eq_fun (coupling_scope_measurable_candidate Δ lam R A hA m i N)
    measurable_const).inter
    (coupling_scope_measurableSet_candidate_false_prefix Δ lam R A hA m i N)

/-- Prefix comparison for the actual candidates after a deterministic restart.
Only the path through the displayed candidate and the original level are used. -/
theorem coupling_scope_candidate_eq_of_prefix {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ)
    (lam R : ℝ) (hR : 0 < R) (A : Regeneration.CoupledSample d → ℝ)
    (m : ℕ) (i : Fin d) (n k : ℕ) (z z' : Regeneration.CoupledSample d)
    (hAeq : A z = A z')
    (hpre : ∀ t ∈ Set.Icc (0 : ℝ≥0) (((m + k : ℕ) : ℝ≥0) * Δ), z.1 t = z'.1 t)
    (hle : couplingScopeCandidate Δ lam R A m i n z ≤
      (((k : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞)) :
    couplingScopeCandidate Δ lam R A m i n z =
      couplingScopeCandidate Δ lam R A m i n z' := by
  unfold couplingScopeCandidate at hle ⊢
  rw [← hAeq]
  apply Regeneration.roundedCandidateSequence_eq_of_prefix Δ hΔ lam R (A z) hR
    _ _ i n ((k : ℝ≥0) * Δ) _ hle
  intro t ht
  apply hpre ((m : ℝ≥0) * Δ + t)
  refine ⟨zero_le, ?_⟩
  calc (m : ℝ≥0) * Δ + t ≤ (m : ℝ≥0) * Δ + (k : ℝ≥0) * Δ :=
      add_le_add le_rfl ht.2
    _ = ((m + k : ℕ) : ℝ≥0) * Δ := by rw [Nat.cast_add, add_mul]

/-- A selected-index slice and all previous false choices transfer between
histories agreeing before the currently selected coin. -/
theorem coupling_scope_candidate_prebit_of_prefix {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ)
    (lam R : ℝ) (hlam : 0 < lam) (hR : 0 < R)
    (A : Regeneration.CoupledSample d → ℝ) (m : ℕ) (i : Fin d) (N k : ℕ)
    (z z' : Regeneration.CoupledSample d) (hAeq : A z = A z')
    (hpre : ∀ t ∈ Set.Icc (0 : ℝ≥0) (((m + k : ℕ) : ℝ≥0) * Δ), z.1 t = z'.1 t)
    (hbits : ∀ r < m + k, z.2 r = z'.2 r)
    (hz : z ∈ couplingScopeCandidatePrebit Δ lam R A m i N k) :
    z' ∈ couplingScopeCandidatePrebit Δ lam R A m i N k := by
  obtain ⟨ht, hfalse⟩ := hz
  have hcur := coupling_scope_candidate_eq_of_prefix Δ hΔ lam R hR A m i N k
    z z' hAeq hpre (le_of_eq ht)
  refine ⟨hcur.symm.trans ht, ?_⟩
  intro j hj
  obtain ⟨r, hr, hb⟩ := hfalse j hj
  have hfin : couplingScopeCandidate Δ lam R A m i j z ≠ ⊤ :=
    hr ▸ ENNReal.coe_ne_top
  have hlt := coupling_scope_candidate_lt Δ hΔ lam R hlam hR A m i z hj hfin
  rw [hr, ht, ENNReal.coe_lt_coe] at hlt
  have hrk : r < k := by
    exact_mod_cast (mul_lt_mul_iff_left₀ hΔ).mp hlt
  have heq := coupling_scope_candidate_eq_of_prefix Δ hΔ lam R hR A m i j k
    z z' hAeq hpre (by rw [hr]; exact ENNReal.coe_le_coe.mpr hlt.le)
  exact ⟨r, heq.symm.trans hr, (hbits (m + r) (Nat.add_lt_add_left hrk m)).symm.trans hb⟩

/-- The actual pre-bit slice is measurable in the exact finite history at the
absolute selected index, even for a history-dependent restart level. -/
theorem coupling_scope_measurableSet_candidate_prebit_finiteHistory {d : ℕ}
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (lam R : ℝ) (hlam : 0 < lam) (hR : 0 < R)
    (A : Regeneration.CoupledSample d → ℝ) (m : ℕ)
    (hA : @Measurable (Regeneration.CoupledSample d) ℝ
      (Regeneration.finiteHistorySigma Δ m) inferInstance A)
    (i : Fin d) (N k : ℕ) :
    @MeasurableSet (Regeneration.CoupledSample d)
      (Regeneration.finiteHistorySigma Δ (m + k))
      (couplingScopeCandidatePrebit Δ lam R A m i N k) := by
  have hAmk := hA.mono (Regeneration.finiteHistorySigma_mono Δ (Nat.le_add_right m k)) le_rfl
  have hAg := hA.mono (Probability.finiteHistorySigma_le Δ m) le_rfl
  have hset : couplingScopeCandidatePrebit Δ lam R A m i N k =
      Probability.stoppedHistorySample Δ (m + k) ⁻¹'
        couplingScopeCandidatePrebit Δ lam R A m i N k := by
    ext z
    have hAeq := (Probability.finiteHistory_test_stopped Δ (m + k) A hAmk z).symm
    have hpre : ∀ t ∈ Set.Icc (0 : ℝ≥0) (((m + k : ℕ) : ℝ≥0) * Δ),
        z.1 t = (Probability.stoppedHistorySample Δ (m + k) z).1 t :=
      fun t ht => (Probability.stoppedHistorySample_path Δ (m + k) z t ht.2).symm
    have hbits : ∀ r < m + k,
        z.2 r = (Probability.stoppedHistorySample Δ (m + k) z).2 r :=
      fun r hr => (Probability.stoppedHistorySample_bit Δ (m + k) z r hr).symm
    constructor
    · exact coupling_scope_candidate_prebit_of_prefix Δ hΔ lam R hlam hR A m i N k
        z _ hAeq hpre hbits
    · exact coupling_scope_candidate_prebit_of_prefix Δ hΔ lam R hlam hR A m i N k
        _ z hAeq.symm (fun t ht => (hpre t ht).symm) (fun r hr => (hbits r hr).symm)
  rw [hset]
  exact Probability.measurable_stoppedHistorySample Δ (m + k)
    (coupling_scope_measurableSet_candidate_prebit Δ lam R A hAg m i N k)

/-- The false-bit complement of the actual fresh-bit identity, for any exact
past event. Finiteness of the probability measure justifies cancellation. -/
theorem coupling_scope_measure_false_bit {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (K : Regeneration.CoupledQuenchedLaws d) (hK : Regeneration.HasProbabilityLaws Q K)
    (Δ : ℝ≥0) (δ : ℝ) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hFresh : Regeneration.HasFreshBits Q Δ δ K) (n : ℕ)
    (B : Set (Regeneration.CoupledSample d))
    (hB : @MeasurableSet (Regeneration.CoupledSample d)
      (Regeneration.finiteHistorySigma Δ n) B) :
    Regeneration.annealedCoupledLaw Q K {q | q.2 ∈ B ∧ q.2.2 n = false} =
      ENNReal.ofReal (1 - δ) * Regeneration.annealedCoupledLaw Q K {q | q.2 ∈ B} := by
  have : IsProbabilityMeasure (Regeneration.annealedCoupledLaw Q K) :=
    Regeneration.annealedCoupledLaw_isProbabilityMeasure Q K hK
  let μ := Regeneration.annealedCoupledLaw Q K
  have hBg : MeasurableSet B := Probability.finiteHistorySigma_le Δ n B hB
  have hf : MeasurableSet {q : FieldPair d × Regeneration.CoupledSample d |
      q.2 ∈ B ∧ q.2.2 n = false} :=
    (measurable_snd hBg).inter
      (measurableSet_eq_fun ((measurable_pi_apply n).comp measurable_snd.snd) measurable_const)
  have hsplit : {q : FieldPair d × Regeneration.CoupledSample d | q.2 ∈ B} =
      {q | q.2 ∈ B ∧ q.2.2 n = true} ∪ {q | q.2 ∈ B ∧ q.2.2 n = false} := by
    ext q
    simp only [Set.mem_ofPred_eq, Set.mem_union]
    cases q.2.2 n <;> simp
  have hd : Disjoint {q : FieldPair d × Regeneration.CoupledSample d |
      q.2 ∈ B ∧ q.2.2 n = true} {q | q.2 ∈ B ∧ q.2.2 n = false} := by
    exact Set.disjoint_left.mpr fun q ht hf => Bool.noConfusion (ht.2.symm.trans hf.2)
  have hsum : μ {q | q.2 ∈ B} =
      ENNReal.ofReal δ * μ {q | q.2 ∈ B} + μ {q | q.2 ∈ B ∧ q.2.2 n = false} := by
    conv_lhs => rw [hsplit]
    rw [measure_union hd hf, Regeneration.measure_annealed_fresh_bit Q K hK Δ δ hδ hFresh n B hB]
  have hc : ENNReal.ofReal δ + ENNReal.ofReal (1 - δ) = 1 := by
    rw [← ENNReal.ofReal_add hδ (sub_nonneg.mpr hδ1)]
    simp only [add_sub_cancel, ENNReal.ofReal_one]
  have heq : ENNReal.ofReal δ * μ {q | q.2 ∈ B} +
        μ {q | q.2 ∈ B ∧ q.2.2 n = false} =
      ENNReal.ofReal δ * μ {q | q.2 ∈ B} +
        ENNReal.ofReal (1 - δ) * μ {q | q.2 ∈ B} := by
    rw [← hsum, ← add_mul, hc, one_mul]
  exact (ENNReal.add_right_inj (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (measure_ne_top μ _))).mp heq

/-- Exact deterministic-index slicing of the next selected false coin. -/
theorem coupling_scope_candidate_false_prefix_succ {d : ℕ}
    (Δ : ℝ≥0) (lam R : ℝ) (A : Regeneration.CoupledSample d → ℝ)
    (m : ℕ) (i : Fin d) (N : ℕ) :
    couplingScopeCandidateFalsePrefix Δ lam R A m i (N + 1) =
      ⋃ k : ℕ, {z | z ∈ couplingScopeCandidatePrebit Δ lam R A m i N k ∧
        z.2 (m + k) = false} := by
  ext z
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
  constructor
  · intro hz
    obtain ⟨k, hk, hb⟩ := hz N (Nat.lt_succ_self N)
    exact ⟨k, ⟨hk, fun j hj => hz j (Nat.lt_succ_of_lt hj)⟩, hb⟩
  · rintro ⟨k, ⟨hk, hprev⟩, hb⟩ j hj
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with hj | rfl
    · exact hprev j hj
    · exact ⟨k, hk, hb⟩

/-- At a fixed candidate number, distinct exact grid selections are disjoint. -/
theorem coupling_scope_disjoint_candidate_prebits {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ)
    (lam R : ℝ) (A : Regeneration.CoupledSample d → ℝ) (m : ℕ) (i : Fin d) (N : ℕ) :
    Pairwise fun k r : ℕ => Disjoint (couplingScopeCandidatePrebit Δ lam R A m i N k)
      (couplingScopeCandidatePrebit Δ lam R A m i N r) := by
  intro k r hkr
  refine Set.disjoint_left.mpr fun z hk hr => ?_
  have heq := ENNReal.coe_inj.mp (hk.1.symm.trans hr.1)
  have hcast := mul_right_cancel₀ hΔ.ne' heq
  exact hkr (by exact_mod_cast hcast)

/-- Summing the actual pre-bit slices gives a contraction for a finite
selected false prefix; no candidate-finiteness premise is used. -/
theorem coupling_scope_measure_candidate_false_prefix_step {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (K : Regeneration.CoupledQuenchedLaws d) (hK : Regeneration.HasProbabilityLaws Q K)
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (δ : ℝ) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hFresh : Regeneration.HasFreshBits Q Δ δ K)
    (lam R : ℝ) (hlam : 0 < lam) (hR : 0 < R)
    (A : Regeneration.CoupledSample d → ℝ) (m : ℕ)
    (hA : @Measurable (Regeneration.CoupledSample d) ℝ
      (Regeneration.finiteHistorySigma Δ m) inferInstance A)
    (i : Fin d) (N : ℕ) :
    Regeneration.annealedCoupledLaw Q K
        {q | q.2 ∈ couplingScopeCandidateFalsePrefix Δ lam R A m i (N + 1)} ≤
      ENNReal.ofReal (1 - δ) * Regeneration.annealedCoupledLaw Q K
        {q | q.2 ∈ couplingScopeCandidateFalsePrefix Δ lam R A m i N} := by
  let μ := Regeneration.annealedCoupledLaw Q K
  let B : ℕ → Set (FieldPair d × Regeneration.CoupledSample d) := fun k =>
    {q | q.2 ∈ couplingScopeCandidatePrebit Δ lam R A m i N k}
  have hAg := hA.mono (Probability.finiteHistorySigma_le Δ m) le_rfl
  have hmeas : ∀ k, MeasurableSet (B k) := fun k => measurable_snd
    (coupling_scope_measurableSet_candidate_prebit Δ lam R A hAg m i N k)
  have hdisj : Pairwise fun k r => Disjoint (B k) (B r) := by
    intro k r hkr
    exact Set.disjoint_left.mpr fun q hk hr => Set.disjoint_left.mp
      (coupling_scope_disjoint_candidate_prebits Δ hΔ lam R A m i N hkr) hk hr
  have hset : {q : FieldPair d × Regeneration.CoupledSample d |
      q.2 ∈ couplingScopeCandidateFalsePrefix Δ lam R A m i (N + 1)} =
      ⋃ k : ℕ, {q | q.2 ∈ couplingScopeCandidatePrebit Δ lam R A m i N k ∧
        q.2.2 (m + k) = false} := by
    ext q
    simp only [coupling_scope_candidate_false_prefix_succ, Set.mem_iUnion, Set.mem_ofPred_eq]
  calc μ {q | q.2 ∈ couplingScopeCandidateFalsePrefix Δ lam R A m i (N + 1)}
      ≤ ∑' k : ℕ, μ {q | q.2 ∈ couplingScopeCandidatePrebit Δ lam R A m i N k ∧
          q.2.2 (m + k) = false} := by rw [hset]; exact measure_iUnion_le _
    _ = ∑' k : ℕ, ENNReal.ofReal (1 - δ) * μ (B k) := by
      apply tsum_congr
      intro k
      exact coupling_scope_measure_false_bit Q K hK Δ δ hδ hδ1 hFresh (m + k) _
        (coupling_scope_measurableSet_candidate_prebit_finiteHistory
          Δ hΔ lam R hlam hR A m hA i N k)
    _ = ENNReal.ofReal (1 - δ) * ∑' k : ℕ, μ (B k) := ENNReal.tsum_mul_left
    _ = ENNReal.ofReal (1 - δ) * μ (⋃ k : ℕ, B k) := by
      rw [measure_iUnion hdisj hmeas]
    _ ≤ ENNReal.ofReal (1 - δ) *
        μ {q | q.2 ∈ couplingScopeCandidateFalsePrefix Δ lam R A m i N} := by
      apply mul_le_mul_right
      apply measure_mono
      intro q hq
      obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hq
      exact hk.2

/-- Geometric bound for the finite selected-prefix event, including its honest
finite-candidate guards and any exact-past measurable level at a grid restart. -/
theorem coupling_scope_measure_candidate_false_prefix_le {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (K : Regeneration.CoupledQuenchedLaws d) (hK : Regeneration.HasProbabilityLaws Q K)
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (δ : ℝ) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hFresh : Regeneration.HasFreshBits Q Δ δ K)
    (lam R : ℝ) (hlam : 0 < lam) (hR : 0 < R)
    (A : Regeneration.CoupledSample d → ℝ) (m : ℕ)
    (hA : @Measurable (Regeneration.CoupledSample d) ℝ
      (Regeneration.finiteHistorySigma Δ m) inferInstance A)
    (i : Fin d) (N : ℕ) :
    Regeneration.annealedCoupledLaw Q K
        {q | q.2 ∈ couplingScopeCandidateFalsePrefix Δ lam R A m i N} ≤
      ENNReal.ofReal (1 - δ) ^ N := by
  induction N with
  | zero =>
    have : IsProbabilityMeasure (Regeneration.annealedCoupledLaw Q K) :=
      Regeneration.annealedCoupledLaw_isProbabilityMeasure Q K hK
    simp only [couplingScopeCandidateFalsePrefix, Nat.not_lt_zero, IsEmpty.forall_iff,
      implies_true, Set.mem_univ, Set.ofPred_true, measure_univ, pow_zero, le_refl]
  | succ N ih =>
    calc _ ≤ ENNReal.ofReal (1 - δ) * Regeneration.annealedCoupledLaw Q K
          {q | q.2 ∈ couplingScopeCandidateFalsePrefix Δ lam R A m i N} :=
        coupling_scope_measure_candidate_false_prefix_step Q K hK Δ hΔ δ hδ hδ1 hFresh
          lam R hlam hR A m hA i N
      _ ≤ ENNReal.ofReal (1 - δ) * ENNReal.ofReal (1 - δ) ^ N := mul_le_mul_right ih _
      _ = ENNReal.ofReal (1 - δ) ^ (N + 1) := (pow_succ' _ _).symm

/-- The grid-slice prefix is exactly the finite-candidate/actual-shifted-coin
prefix; the witness convention introduces no new candidate indices. -/
theorem coupling_scope_candidate_false_prefix_iff {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ)
    (lam R : ℝ) (A : Regeneration.CoupledSample d → ℝ) (m : ℕ) (i : Fin d) (N : ℕ)
    (z : Regeneration.CoupledSample d) :
    z ∈ couplingScopeCandidateFalsePrefix Δ lam R A m i N ↔
      ∀ j < N, couplingScopeCandidate Δ lam R A m i j z ≠ ⊤ ∧
        (Regeneration.sampleTimeShift Δ z ((m : ℝ≥0) * Δ)).2
          (Regeneration.gridIndex Δ (couplingScopeCandidate Δ lam R A m i j z).toNNReal) =
          false := by
  constructor
  · intro hz j hj
    obtain ⟨k, hk, hb⟩ := hz j hj
    refine ⟨hk ▸ ENNReal.coe_ne_top, ?_⟩
    rw [hk, ENNReal.toNNReal_coe, Regeneration.gridIndex_mul Δ hΔ k]
    simpa only [Regeneration.sampleTimeShift, Regeneration.gridIndex_mul Δ hΔ m] using hb
  · intro hz j hj
    obtain ⟨hfin, hb⟩ := hz j hj
    obtain ⟨k, hk⟩ := Regeneration.roundedCandidateSequence_mem_grid Δ hΔ lam R (A z)
      (Regeneration.sampleTimeShift Δ z ((m : ℝ≥0) * Δ)) i j hfin
    refine ⟨k, hk, ?_⟩
    change couplingScopeCandidate Δ lam R A m i j z = _ at hk
    rw [hk, ENNReal.toNNReal_coe, Regeneration.gridIndex_mul Δ hΔ k] at hb
    simpa only [Regeneration.sampleTimeShift, Regeneration.gridIndex_mul Δ hΔ m] using hb

/-- The actual Section 3 coupling supplies the fresh-bit clause for the
selected-prefix bound. Its level may depend on the exact history at restart. -/
theorem coupling_scope_selected_false_prefix_le_of_coupling {d : ℕ} (hd : 2 ≤ d)
    {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (lam l δ : ℝ)
    (h₀ : 0 < lam) (h₁ : lam ≤ 1) (hl : 0 < l) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K)
    (A : Regeneration.CoupledSample d → ℝ) (m : ℕ)
    (hA : @Measurable (Regeneration.CoupledSample d) ℝ
      (Regeneration.finiteHistorySigma (Regeneration.Renewal.regenDelta lam) m) inferInstance A)
    (N : ℕ) :
    let Δ := Regeneration.Renewal.regenDelta lam
    let R := l / lam
    let i := Regeneration.Renewal.forceCoord hd
    Regeneration.annealedCoupledLaw Q.measure K {q | ∀ j < N,
      couplingScopeCandidate Δ lam R A m i j q.2 ≠ ⊤ ∧
        (Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)).2
          (Regeneration.gridIndex Δ (couplingScopeCandidate Δ lam R A m i j q.2).toNNReal) =
          false} ≤ ENNReal.ofReal (1 - δ) ^ N := by
  dsimp only
  have hΔ : 0 < Regeneration.Renewal.regenDelta lam :=
    Real.toNNReal_pos.mpr (inv_pos.mpr (sq_pos_of_pos h₀))
  have hset : {q : FieldPair d × Regeneration.CoupledSample d | ∀ j < N,
      couplingScopeCandidate (Regeneration.Renewal.regenDelta lam) lam (l / lam) A m
        (Regeneration.Renewal.forceCoord hd) j q.2 ≠ ⊤ ∧
      (Regeneration.sampleTimeShift (Regeneration.Renewal.regenDelta lam) q.2
        ((m : ℝ≥0) * Regeneration.Renewal.regenDelta lam)).2
        (Regeneration.gridIndex (Regeneration.Renewal.regenDelta lam)
          (couplingScopeCandidate (Regeneration.Renewal.regenDelta lam) lam (l / lam) A m
            (Regeneration.Renewal.forceCoord hd) j q.2).toNNReal) = false} =
      {q | q.2 ∈ couplingScopeCandidateFalsePrefix (Regeneration.Renewal.regenDelta lam)
        lam (l / lam) A m (Regeneration.Renewal.forceCoord hd) N} := by
    ext q
    exact (coupling_scope_candidate_false_prefix_iff _ hΔ lam (l / lam) A m _ N q.2).symm
  rw [hset]
  exact coupling_scope_measure_candidate_false_prefix_le Q.measure K hK.1 _ hΔ
    δ hδ hδ1 hK.2.2.2.1 lam (l / lam) h₀ (div_pos hl h₀) A m hA _ N

/-- Conditional qualitative exhaustion: outside a null set, finiteness of
all actual rounded candidates entails finiteness of the successful candidate.
The still-missing analytic candidate-finiteness producer is not assumed here. -/
theorem coupling_scope_ae_successful_candidate_finite_of_candidates {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (K : Regeneration.CoupledQuenchedLaws d) (hK : Regeneration.HasProbabilityLaws Q K)
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hFresh : Regeneration.HasFreshBits Q Δ δ K)
    (lam R : ℝ) (hlam : 0 < lam) (hR : 0 < R)
    (A : Regeneration.CoupledSample d → ℝ) (m : ℕ)
    (hA : @Measurable (Regeneration.CoupledSample d) ℝ
      (Regeneration.finiteHistorySigma Δ m) inferInstance A) (i : Fin d) :
    ∀ᵐ q ∂Regeneration.annealedCoupledLaw Q K,
      (∀ n, couplingScopeCandidate Δ lam R A m i n q.2 ≠ ⊤) →
        Regeneration.firstSuccessfulCandidate Δ lam R (A q.2)
          (Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)) i ≠ ⊤ := by
  classical
  rw [ae_iff]
  simp only [not_imp, not_not]
  apply le_antisymm _ zero_le
  apply ge_of_tendsto' (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one
    (ENNReal.ofReal_lt_one.mpr (by linarith : 1 - δ < 1)))
  intro N
  apply le_trans (measure_mono ?_)
    (coupling_scope_measure_candidate_false_prefix_le Q K hK Δ hΔ δ hδ.le hδ1 hFresh
      lam R hlam hR A m hA i N)
  intro q hq
  apply (coupling_scope_candidate_false_prefix_iff Δ hΔ lam R A m i N q.2).mpr
  intro j _hj
  refine ⟨hq.1 j, ?_⟩
  have hn : ¬ Regeneration.IsSuccessfulCandidate Δ lam R (A q.2)
      (Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)) i j := by
    intro hs
    have hle : Regeneration.firstSuccessfulCandidate Δ lam R (A q.2)
        (Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)) i ≤
        couplingScopeCandidate Δ lam R A m i j q.2 :=
      iInf_le_of_le j (iInf_le_of_le hs le_rfl)
    rw [hq.2] at hle
    exact hq.1 j (top_le_iff.mp hle)
  have hb : ¬ (Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)).2
      (Regeneration.gridIndex Δ (couplingScopeCandidate Δ lam R A m i j q.2).toNNReal) =
        true := fun hb => hn ⟨hq.1 j, hb⟩
  exact Bool.eq_false_iff.mpr hb

#print axioms couplingScopeCandidate
#print axioms couplingScopeCandidateFalsePrefix
#print axioms couplingScopeCandidatePrebit
#print axioms coupling_scope_candidate_monotone
#print axioms coupling_scope_candidate_lt
#print axioms coupling_scope_measurable_candidate
#print axioms coupling_scope_measurableSet_candidate_false_prefix
#print axioms coupling_scope_measurableSet_candidate_prebit
#print axioms coupling_scope_candidate_eq_of_prefix
#print axioms coupling_scope_candidate_prebit_of_prefix
#print axioms coupling_scope_measurableSet_candidate_prebit_finiteHistory
#print axioms coupling_scope_measure_false_bit
#print axioms coupling_scope_candidate_false_prefix_succ
#print axioms coupling_scope_disjoint_candidate_prebits
#print axioms coupling_scope_measure_candidate_false_prefix_step
#print axioms coupling_scope_measure_candidate_false_prefix_le
#print axioms coupling_scope_candidate_false_prefix_iff
#print axioms coupling_scope_selected_false_prefix_le_of_coupling
#print axioms coupling_scope_ae_successful_candidate_finite_of_candidates
#print axioms coupling_scope_disjoint_trial_start_slices
#print axioms coupling_scope_trial_start_finite_iff
#print axioms coupling_scope_measure_trial_start_finite
#print axioms couplingScopeTrialPrebridge
#print axioms coupling_scope_measurableSet_trial_prebridge
#print axioms coupling_scope_mem_trial_prebridge_stoppedHistory_iff
#print axioms coupling_scope_measurableSet_trial_prebridge_finiteHistory
#print axioms coupling_scope_trial_start_slice_iff
#print axioms coupling_scope_measure_trial_start_slice
#print axioms coupling_scope_measure_trial_start_slice_of_coupling
#print axioms coupling_scope_measurable
#print axioms coupling_scope_finite_iff_grid_record
#print axioms coupling_scope_ae_finite_iff_grid_record
#print axioms coupling_scope_both_laws_finite_iff
#print axioms coupling_scope_zero_grid_record
#print axioms coupling_scope_finite_of_grid_exhaustion
#print axioms coupling_scope_ae_finite_of_grid_exhaustion
#print axioms coupling_scope_first_cycle_of_regen_tails
#print axioms coupling_scope_iff_annealed_finite
#lint

end EinsteinFull.Blueprint
