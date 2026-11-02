import EinsteinFull.Blueprint.G1.Proofs.S3KFactorBounded
import EinsteinFull.Blueprint.G1.node_rt_u3A_km_u2D_decomp
import EinsteinFull.Blueprint.G1.node_rt_u3A_many_u2D_cycle_u2D_moment
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import EinsteinFull.Frozen.ReducedLawProbability
import Mathlib.Tactic.Linarith
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import EinsteinFull.Blueprint.G1.Proofs.S3MRenewal
import EinsteinFull.Blueprint.G1.node_rt_u3A_k_u2D_factor
import EinsteinFull.Blueprint.G1.node_rt_u3A_remainder_u2D_moment
import EinsteinFull.Blueprint.G1.Proofs.S3RenewalEstimates
import EinsteinFull.Blueprint.G1.Proofs.SbxS5PhaseError
import EinsteinFull.Blueprint.G1.node_rt_u3A_local_u2D_mixing_u23_phase_u2D_error

/-!
# Actual regeneration-slice sums and centered convolution

Support for `rt:km-decomp`. The coefficients below are the literal slice
integrals, with the original field reduced inside the integrand. Finite moments
are used only to establish almost-sure finiteness of the actual trial time.
These results do not identify the path evolution with an environment semigroup.
-/

open MeasureTheory
open scoped NNReal ENNReal Topology

namespace EinsteinFull.Blueprint

open EinsteinRelation
open EinsteinFull.Work.W5

/-- Integration over all actual lattice slices reconstructs the original integral. -/
theorem sbxS2_regenerationSlice_hasSum {d : ℕ} (hd : 2 ≤ d)
    (lam l : ℝ) (hlam : lam ≠ 0) (k : ℕ)
    (μ : Measure (FieldPair d × Regeneration.CoupledSample d))
    (hf : ∀ᵐ ωz ∂μ, regenerationTime hd lam l k ωz.2 ≠ ⊤)
    (f : FieldPair d × Regeneration.CoupledSample d → ℝ) (hint : Integrable f μ) :
    HasSum (fun n : ℕ => ∫ ωz in {ωz | regenerationTime hd lam l k ωz.2 =
      (((n : ℝ≥0) * Regeneration.Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)},
      f ωz ∂μ) (∫ ωz, f ωz ∂μ) := by
  let s := fun n : ℕ => {ωz : FieldPair d × Regeneration.CoupledSample d |
    regenerationTime hd lam l k ωz.2 =
      (((n : ℝ≥0) * Regeneration.Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)}
  have hΔ : 0 < Regeneration.Renewal.regenDelta lam :=
    Real.toNNReal_pos.mpr (inv_pos.mpr (sq_pos_of_ne_zero hlam))
  have ht : Measurable (fun ωz : FieldPair d × Regeneration.CoupledSample d =>
      regenerationTime hd lam l k ωz.2) :=
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
    obtain ⟨n, hn⟩ := Regeneration.regenerationTime_mem_grid _ hΔ _ _ ωz.2 _ k hωz
    exact Set.mem_iUnion.mpr ⟨n, hn⟩
  have hsum := hasSum_integral_iUnion hs hdis hint.integrableOn
  rw [Measure.restrict_eq_self_of_ae_mem hcover] at hsum
  exact hsum

/-- A finite extended exponential moment supplies the finiteness needed above. -/
theorem sbxS2_regenerationSlice_hasSum_of_moment {d : ℕ} (hd : 2 ≤ d)
    (lam l a : ℝ) (hlam : lam ≠ 0) (k : ℕ)
    (μ : Measure (FieldPair d × Regeneration.CoupledSample d))
    (hm : (∫⁻ ωz, regenerationExponentialWeight hd lam l a k ωz.2 ∂μ) ≠ ⊤)
    (f : FieldPair d × Regeneration.CoupledSample d → ℝ) (hint : Integrable f μ) :
    HasSum (fun n : ℕ => ∫ ωz in {ωz | regenerationTime hd lam l k ωz.2 =
      (((n : ℝ≥0) * Regeneration.Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)},
      f ωz ∂μ) (∫ ωz, f ωz ∂μ) :=
  sbxS2_regenerationSlice_hasSum hd lam l hlam k μ
    (regenerationTime_ne_top_ae_of_exponentialMoment hd lam l a k μ hm) f hint

/-- A finite actual moment controls each literal lattice-slice mass. -/
theorem sbxS2_regenerationSlice_mass_le {d : ℕ} (hd : 2 ≤ d)
    (lam l a B : ℝ) (hlam : lam ≠ 0) (k n : ℕ)
    (μ : Measure (FieldPair d × Regeneration.CoupledSample d))
    (hm : (∫⁻ ωz, regenerationExponentialWeight hd lam l a k ωz.2 ∂μ) ≤
      ENNReal.ofReal B) :
    μ {ωz | regenerationTime hd lam l k ωz.2 =
      (((n : ℝ≥0) * Regeneration.Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)} ≤
      ENNReal.ofReal (B * Real.exp (-(a * n))) := by
  have hf := regenerationTime_ne_top_ae_of_exponentialMoment hd lam l a k μ
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hm)
  have he := regeneration_exponentialMoment_eq_tsum hd lam l a hlam k μ hf
  have ht : ENNReal.ofReal (Real.exp (a * n)) *
      μ {ωz | regenerationTime hd lam l k ωz.2 =
        (((n : ℝ≥0) * Regeneration.Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)} ≤
      ENNReal.ofReal B := (ENNReal.le_tsum n).trans (he ▸ hm)
  have hc : ENNReal.ofReal (Real.exp (-(a * n))) *
      ENNReal.ofReal (Real.exp (a * n)) = 1 := by
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    simp only [neg_add_cancel, Real.exp_zero, ENNReal.ofReal_one]
  calc
    _ = ENNReal.ofReal (Real.exp (-(a * n))) *
        (ENNReal.ofReal (Real.exp (a * n)) * _) := by
      rw [← mul_assoc, hc, one_mul]
    _ ≤ ENNReal.ofReal (Real.exp (-(a * n))) * ENNReal.ofReal B :=
      mul_le_mul_right ht _
    _ = _ := by rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, mul_comm]

/-- The actual annealed coupling has exactly the original environment marginal,
including the origin-a.e. probability qualifier on the supplied raw kernel. -/
theorem sbxS2_map_fst_annealed {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (K : Regeneration.CoupledQuenchedLaws d)
    (hK : Regeneration.HasProbabilityLaws Q.measure K) :
    (Regeneration.annealedCoupledLaw Q.measure K).map Prod.fst = Q.measure := by
  ext s hs
  rw [Measure.map_apply measurable_fst hs]
  rw [show (Prod.fst : FieldPair d × Regeneration.CoupledSample d → FieldPair d) ⁻¹' s =
    s ×ˢ Set.univ by ext x; simp]
  change (Q.measure.compProd (Probability.probabilityPart
    (Regeneration.originCoupledLaw K))) (s ×ˢ Set.univ) = Q.measure s
  rw [Measure.compProd_apply_prod hs MeasurableSet.univ]
  calc
    _ = ∫⁻ _ω in s, (1 : ℝ≥0∞) ∂Q.measure := by
      apply setLIntegral_congr_fun_ae hs
      filter_upwards [hK.1,
        Probability.probabilityPart_ae_eq Q.measure (Regeneration.originCoupledLaw K) hK.1]
        with ω hω heq _hωs
      rw [heq]
      exact hω.measure_univ
    _ = _ := by simp only [lintegral_one, Measure.restrict_apply_univ]

/-- Reducing the actual first marginal gives exactly the prescribed reduced law. -/
theorem sbxS2_reducedFst_measurePreserving {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (K : Regeneration.CoupledQuenchedLaws d)
    (hK : Regeneration.HasProbabilityLaws Q.measure K) :
    MeasurePreserving (fun ωz : FieldPair d × Regeneration.CoupledSample d => reduce ωz.1)
      (Regeneration.annealedCoupledLaw Q.measure K) (reducedLaw Q) := by
  exact (show MeasurePreserving reduce Q.measure (reducedLaw Q) from
    ⟨Probability.measurable_reduce, rfl⟩).comp
      ⟨measurable_fst, sbxS2_map_fst_annealed Q K hK⟩

/-- All finite-moment norms of the literal reduced first coordinate are preserved. -/
theorem sbxS2_eLpNorm_reducedFst {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (K : Regeneration.CoupledQuenchedLaws d)
    (hK : Regeneration.HasProbabilityLaws Q.measure K)
    (F : FieldPair d → ℝ) (p : ℝ≥0∞)
    (hF : AEStronglyMeasurable F (reducedLaw Q)) :
    eLpNorm (fun ωz : FieldPair d × Regeneration.CoupledSample d => F (reduce ωz.1)) p
      (Regeneration.annealedCoupledLaw Q.measure K) = eLpNorm F p (reducedLaw Q) :=
  eLpNorm_comp_measurePreserving hF (sbxS2_reducedFst_measurePreserving Q K hK)

/-- The literal slice integral obeys the square-root event-mass estimate, with
the norm taken under the prescribed reduced law rather than a new carrier. -/
theorem sbxS2_regenerationSlice_enorm_le {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (lam l : ℝ)
    (K : Regeneration.CoupledQuenchedLaws d)
    (hK : Regeneration.HasProbabilityLaws Q.measure K)
    (k n : ℕ) (F : FieldPair d → ℝ) (hF : Measurable F) :
    ‖∫ ωz in {ωz | regenerationTime hd lam l k ωz.2 =
      (((n : ℝ≥0) * Regeneration.Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)},
      F (reduce ωz.1) ∂Regeneration.annealedCoupledLaw Q.measure K‖ₑ ≤
      eLpNorm F 2 (reducedLaw Q) *
        (Regeneration.annealedCoupledLaw Q.measure K
          {ωz | regenerationTime hd lam l k ωz.2 =
            (((n : ℝ≥0) * Regeneration.Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)}) ^
          (1 / 2 : ℝ) := by
  let μ := Regeneration.annealedCoupledLaw Q.measure K
  let s := {ωz : FieldPair d × Regeneration.CoupledSample d |
    regenerationTime hd lam l k ωz.2 =
      (((n : ℝ≥0) * Regeneration.Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)}
  let f := fun ωz : FieldPair d × Regeneration.CoupledSample d => F (reduce ωz.1)
  have hfm : Measurable f := (hF.comp Probability.measurable_reduce).comp measurable_fst
  have hb := eLpNorm_le_eLpNorm_mul_rpow_measure_univ
    (μ := μ.restrict s) (f := f) (show (1 : ℝ≥0∞) ≤ 2 by norm_num)
      hfm.aestronglyMeasurable
  have he : (1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal : ℝ) = 1 / 2 := by
    norm_num
  rw [he, Measure.restrict_apply_univ] at hb
  calc
    ‖∫ ωz in s, f ωz ∂μ‖ₑ ≤ eLpNorm f 1 (μ.restrict s) := by
      rw [eLpNorm_one_eq_lintegral_enorm hfm.aestronglyMeasurable]
      exact enorm_integral_le_lintegral_enorm f
    _ ≤ eLpNorm f 2 (μ.restrict s) * μ s ^ (1 / 2 : ℝ) := hb
    _ ≤ eLpNorm f 2 μ * μ s ^ (1 / 2 : ℝ) :=
      mul_le_mul_left (eLpNorm_mono_measure f Measure.restrict_le_self) _
    _ = _ := by rw [sbxS2_eLpNorm_reducedFst Q K hK F 2 hF.aestronglyMeasurable]

/-- A many-cycle exponential moment gives exponential decay of the actual
coefficient, measured by the original reduced observable's finite L² norm. -/
theorem sbxS2_regenerationSlice_abs_le {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (lam l a C : ℝ) (hlam : lam ≠ 0)
    (K : Regeneration.CoupledQuenchedLaws d)
    (hK : Regeneration.HasProbabilityLaws Q.measure K) (k n : ℕ)
    (F : FieldPair d → ℝ) (hF : Measurable F) (hFp : MemLp F 2 (reducedLaw Q))
    (hm : (∫⁻ ωz, regenerationExponentialWeight hd lam l a k ωz.2
      ∂Regeneration.annealedCoupledLaw Q.measure K) ≤
        ENNReal.ofReal (Real.exp (C * k))) :
    |∫ ωz in {ωz | regenerationTime hd lam l k ωz.2 =
      (((n : ℝ≥0) * Regeneration.Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)},
      F (reduce ωz.1) ∂Regeneration.annealedCoupledLaw Q.measure K| ≤
      Real.exp ((C * k - a * n) / 2) * (eLpNorm F 2 (reducedLaw Q)).toReal := by
  have hs := sbxS2_regenerationSlice_mass_le hd lam l a (Real.exp (C * k)) hlam k n
    (Regeneration.annealedCoupledLaw Q.measure K) hm
  have hq := (sbxS2_regenerationSlice_enorm_le hd Q lam l K hK k n F hF).trans
    (mul_le_mul_right (ENNReal.rpow_le_rpow hs (by norm_num : (0 : ℝ) ≤ 1 / 2)) _)
  have ht : (eLpNorm F 2 (reducedLaw Q) *
      ENNReal.ofReal (Real.exp (C * k) * Real.exp (-(a * n))) ^ (1 / 2 : ℝ)) ≠ ⊤ :=
    ENNReal.mul_ne_top hFp.eLpNorm_ne_top
      (ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top)
  have hh := ENNReal.toReal_mono ht hq
  rw [toReal_enorm, Real.norm_eq_abs, ENNReal.toReal_mul, ← ENNReal.toReal_rpow,
    ENNReal.toReal_ofReal (by positivity :
      0 ≤ Real.exp (C * k) * Real.exp (-(a * n)))] at hh
  have he : (Real.exp (C * k) * Real.exp (-(a * n))) ^ (1 / 2 : ℝ) =
      Real.exp ((C * k - a * n) / 2) := by
    rw [← Real.exp_add, ← Real.exp_mul]
    congr 1
    ring
  rw [he] at hh
  simpa only [mul_comm] using hh

/-- The unbounded integrable first marginal under the actual coupled law. -/
theorem sbxS2_integral_fst_annealed {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (K : Regeneration.CoupledQuenchedLaws d)
    (hK : Regeneration.HasProbabilityLaws Q.measure K)
    (f : FieldPair d → ℝ) (hint : Integrable f Q.measure) :
    (∫ ωz, f ωz.1 ∂Regeneration.annealedCoupledLaw Q.measure K) =
      ∫ ω, f ω ∂Q.measure := by
  have hm := sbxS2_map_fst_annealed Q K hK
  have hfmap : AEStronglyMeasurable f
      ((Regeneration.annealedCoupledLaw Q.measure K).map Prod.fst) := by
    rw [hm]
    exact hint.aestronglyMeasurable
  simpa only [hm] using (integral_map measurable_fst.aemeasurable hfmap).symm

/-- The reduced observable is retained literally in every actual slice coefficient. -/
theorem sbxS2_centered_regenerationSlice_hasSum {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (lam l a : ℝ) (hlam : lam ≠ 0)
    (K : Regeneration.CoupledQuenchedLaws d)
    (hK : Regeneration.HasProbabilityLaws Q.measure K) (k : ℕ)
    (hm : (∫⁻ ωz, regenerationExponentialWeight hd lam l a k ωz.2
      ∂Regeneration.annealedCoupledLaw Q.measure K) ≠ ⊤)
    (F : FieldPair d → ℝ) (hF : Measurable F) (hint : Integrable F (reducedLaw Q))
    (hzero : (∫ ω, F ω ∂reducedLaw Q) = 0) :
    HasSum (fun n : ℕ => ∫ ωz in {ωz | regenerationTime hd lam l k ωz.2 =
      (((n : ℝ≥0) * Regeneration.Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)},
      F (reduce ωz.1) ∂Regeneration.annealedCoupledLaw Q.measure K) 0 := by
  have hFr : Measurable (fun ω => F (reduce ω)) := hF.comp Probability.measurable_reduce
  have hFir : Integrable (fun ω => F (reduce ω)) Q.measure :=
    (integrable_map_measure hF.aestronglyMeasurable
      Probability.measurable_reduce.aemeasurable).mp hint
  have hz : (∫ ωz, F (reduce ωz.1)
      ∂Regeneration.annealedCoupledLaw Q.measure K) = 0 := by
    rw [sbxS2_integral_fst_annealed Q K hK _ hFir]
    rw [reducedLaw, integral_map Probability.measurable_reduce.aemeasurable
      hF.aestronglyMeasurable] at hzero
    exact hzero
  rw [← hz]
  exact sbxS2_regenerationSlice_hasSum_of_moment hd lam l a hlam k
    (Regeneration.annealedCoupledLaw Q.measure K) hm _
    (integrable_fst_annealed Q K _ hFr hFir)

/-- The supplied many-cycle moment dependency proves summability and centering
for every actual cycle index, including the prescribed `k` in `rt:km-decomp`. -/
theorem sbxS2_centered_slices_of_manyCycleMoment
    (hmany : node_rt_u3A_many_u2D_cycle_u2D_momentStmt)
    (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ) :
    ∃ l₀ : ℝ, 0 < l₀ ∧ r₀ < 2 * l₀ ∧
    ∀ l : ℝ, l₀ ≤ l → ∀ δ : ℝ, 0 < δ → δ < 1 →
    ∀ (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
      (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
      (_hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K)
      (_hD : Regeneration.annealedCoupledLaw Q.measure K
        (regenerationNoReturn hd (l / lam)) ≠ 0)
      (p : ℝ), 1 ≤ p → ∀ F : FieldPair d → ℝ,
    Measurable F → MemLp F (ENNReal.ofReal p) (reducedLaw Q) →
    (∫ ω, F ω ∂reducedLaw Q) = 0 → ∀ k : ℕ,
    let q := fun n : ℕ => ∫ ωz in {ωz | regenerationTime hd lam l k ωz.2 =
      (((n : ℝ≥0) * Regeneration.Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)},
      F (reduce ωz.1) ∂Regeneration.annealedCoupledLaw Q.measure K
    Summable q ∧ (∑' n, q n) = 0 := by
  obtain ⟨l₀, hl₀, hsep, hmom⟩ := hmany d hd Λ₀ r₀
  refine ⟨l₀, hl₀, hsep, ?_⟩
  intro l hl δ hδ₀ hδ₁
  obtain ⟨a, M, C, _ha, _hM, _hC, hm⟩ := hmom l hl δ hδ₀ hδ₁
  intro Q lam h₀ h₁ P K hK hD p hp F hF hFp hzero k
  let := reducedLaw_probability Q
  have hmfin : (∫⁻ ωz, regenerationExponentialWeight hd lam l a k ωz.2
      ∂Regeneration.annealedCoupledLaw Q.measure K) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top ((hm Q lam h₀ h₁ P K hK hD).2 k)
  have hq := sbxS2_centered_regenerationSlice_hasSum hd Q lam l a h₀.ne' K hK.1 k
    hmfin F hF (hFp.integrable (by simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp)) hzero
  exact ⟨hq.summable, hq.tsum_eq⟩

/-- The supplied many-cycle moment yields uniform decay of every nonzero-cycle
coefficient in any finite Lᵖ norm with `2 ≤ p`. -/
theorem sbxS2_slice_decay_of_manyCycleMoment
    (hmany : node_rt_u3A_many_u2D_cycle_u2D_momentStmt)
    (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ) :
    ∃ l₀ : ℝ, 0 < l₀ ∧ r₀ < 2 * l₀ ∧
    ∀ l : ℝ, l₀ ≤ l → ∀ δ : ℝ, 0 < δ → δ < 1 →
    ∃ a C : ℝ, 0 < a ∧ 0 < C ∧
    ∀ (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
      (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
      (_hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K)
      (_hD : Regeneration.annealedCoupledLaw Q.measure K
        (regenerationNoReturn hd (l / lam)) ≠ 0)
      (p : ℝ), 2 ≤ p → ∀ F : FieldPair d → ℝ,
    Measurable F → MemLp F (ENNReal.ofReal p) (reducedLaw Q) →
    ∀ k : ℕ, 1 ≤ k → ∀ n : ℕ,
    |∫ ωz in {ωz | regenerationTime hd lam l k ωz.2 =
      (((n : ℝ≥0) * Regeneration.Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)},
      F (reduce ωz.1) ∂Regeneration.annealedCoupledLaw Q.measure K| ≤
      Real.exp ((C * k - a * n) / 2) *
        (eLpNorm F (ENNReal.ofReal p) (reducedLaw Q)).toReal := by
  obtain ⟨l₀, hl₀, hsep, hmom⟩ := hmany d hd Λ₀ r₀
  refine ⟨l₀, hl₀, hsep, ?_⟩
  intro l hl δ hδ₀ hδ₁
  obtain ⟨a, M, C, ha, hM, hC, hm⟩ := hmom l hl δ hδ₀ hδ₁
  refine ⟨a, C + M, ha, add_pos hC hM, ?_⟩
  intro Q lam h₀ h₁ P K hK hD p hp F hF hFp k hk n
  let := reducedLaw_probability Q
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hCexp : C ≤ Real.exp (C * k) := by
    have hself : C ≤ Real.exp C := by linarith only [Real.add_one_le_exp C]
    apply hself.trans
    apply Real.exp_le_exp.mpr
    nlinarith only [hC.le, hk']
  have hMexp : M ≤ Real.exp M := by linarith only [Real.add_one_le_exp M]
  have hgeom : C * M ^ k ≤ Real.exp ((C + M) * k) := by
    calc
      _ ≤ Real.exp (C * k) * Real.exp M ^ k :=
        mul_le_mul hCexp (pow_le_pow_left₀ hM.le hMexp k)
          (pow_nonneg hM.le k) (Real.exp_pos _).le
      _ = _ := by
        rw [← Real.exp_nat_mul, ← Real.exp_add]
        congr 1
        ring
  have hp' : (2 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    simpa using ENNReal.ofReal_le_ofReal hp
  have hq := sbxS2_regenerationSlice_abs_le hd Q lam l a (C + M) h₀.ne' K hK.1
    k n F hF (hFp.mono_exponent hp')
      (((hm Q lam h₀ h₁ P K hK hD).2 k).trans (ENNReal.ofReal_le_ofReal hgeom))
  exact hq.trans (mul_le_mul_of_nonneg_left
    (ENNReal.toReal_mono hFp.eLpNorm_ne_top (eLpNorm_le_eLpNorm_of_exponent_le hp'))
      (Real.exp_pos _).le)

/-- The prescribed two cycle counts have a bound depending only on the radius
and the fixed positive regeneration length. -/
theorem sbxS2_prescribed_cycles_le (l A : ℝ) (hl : 0 < l) (hA : l ≤ A) :
    let k : ℕ := max 1 ⌈(A / l + 4) / 10⌉₊
    let m : ℕ := max 1 ⌈(A / l - 1) / 10⌉₊
    (k + m : ℝ) ≤ (4 + 1 / l) * (1 + A) := by
  have hA₀ : 0 ≤ A := hl.le.trans hA
  have hAl : 1 ≤ A / l := (le_div_iff₀ hl).mpr (by simpa only [one_mul] using hA)
  have hk := Nat.ceil_lt_add_one (show 0 ≤ (A / l + 4) / 10 by linarith)
  have hm := Nat.ceil_lt_add_one (show 0 ≤ (A / l - 1) / 10 by linarith)
  have hk' : (max 1 ⌈(A / l + 4) / 10⌉₊ : ℝ) ≤ (A / l + 4) / 10 + 1 := by
    exact max_le (by linarith) hk.le
  have hm' : (max 1 ⌈(A / l - 1) / 10⌉₊ : ℝ) ≤ (A / l - 1) / 10 + 1 := by
    exact max_le (by linarith) hm.le
  dsimp only
  simp only [Nat.cast_max, Nat.cast_one]
  have hi : 0 ≤ 1 / l := by positivity
  have hAl' : A / l = A * (1 / l) := by ring
  nlinarith only [hk', hm', hA₀, hi, hAl', mul_nonneg hA₀ hi]

/-- Centering a finite convolution restores exactly the omitted tail. -/
theorem sbxS2_centered_convolution (q h : ℕ → ℝ) (H : ℝ) (j : ℕ)
    (hq : Summable q) (hzero : (∑' n, q n) = 0) :
    (∑ n ∈ Finset.range (j + 1), q n * h n) =
      (∑ n ∈ Finset.range (j + 1), q n * (h n - H)) -
        H * ∑' n : ℕ, q (j + 1 + n) := by
  have htail : (∑ n ∈ Finset.range (j + 1), q n) +
      (∑' n : ℕ, q (j + 1 + n)) = 0 := by
    simpa only [Nat.add_comm, hzero] using hq.sum_add_tsum_nat_add (j + 1)
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
  have htailH := congrArg (fun x : ℝ => H * x) htail
  nlinarith only [htailH]

/-- The supplied `k`-factor identity applies to the literal reduced observable. -/
theorem sbxS2_reduced_kFactor (hfactor : node_rt_u3A_k_u2D_factorStmt)
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ l δ : ℝ}
    (hl : 0 < l) (hsep : r₀ < 2 * l) (hδ₀ : 0 < δ) (hδ₁ : δ < 1)
    (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
    (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K)
    (hD : Regeneration.annealedCoupledLaw Q.measure K
      (regenerationNoReturn hd (l / lam)) ≠ 0)
    (A : ℝ) (hA : l ≤ A) (p : ℝ) (hp : 2 ≤ p) (F : FieldPair d → ℝ)
    (hF : Measurable[localSigma {x : Vec d | euclideanNorm x < A / lam}] F)
    (hFp : MemLp F (ENNReal.ofReal p) (reducedLaw Q))
    (Φ : Regeneration.FutureState d (Regeneration.Renewal.forceCoord hd) (l / lam) → ℝ)
    (hΦ : Measurable Φ) (hbΦ : Regeneration.BoundedRealTest Φ) (n : ℕ)
    (μ : Measure (FieldPair d × Regeneration.CoupledSample d))
    (hμ : μ ∈ ({Regeneration.annealedCoupledLaw Q.measure K,
      regenerationConditionedLaw hd Q lam l K hK.1 hD} : Set (Measure _))) :
    let k : ℕ := max 1 ⌈(A / l + 4) / 10⌉₊
    (∫ ωz in {ωz | regenerationTime hd lam l k ωz.2 =
        (((n : ℝ≥0) * Regeneration.Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)},
      F (reduce ωz.1) * Φ (regenerationRecord hd lam l k ωz) ∂μ) =
      (∫ ωz, Φ (regenerationRecord hd lam l 0 ωz)
        ∂regenerationConditionedLaw hd Q lam l K hK.1 hD) *
      ∫ ωz in {ωz | regenerationTime hd lam l k ωz.2 =
        (((n : ℝ≥0) * Regeneration.Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)},
        F (reduce ωz.1) ∂μ := by
  obtain ⟨C, _, hC⟩ := hfactor d hd Λ₀ r₀ l δ hl hsep hδ₀ hδ₁
  exact (hC Q lam h₀ h₁ P K hK hD A hA).2.2 p hp (F ∘ reduce)
    (hF.comp (Probability.measurable_reduce_local _))
    (hFp.comp_of_map Probability.measurable_reduce.aemeasurable) Φ hΦ hbΦ n μ hμ

/-- Splitting the actual regeneration clock after any finite cycle. -/
theorem sbxS2_regenerationTime_add {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ)
    (lam R : ℝ) (i : Fin d) (z : Regeneration.CoupledSample d)
    (k m : ℕ) (hk : Regeneration.regenerationTime Δ lam R z i k ≠ ⊤) :
    Regeneration.regenerationTime Δ lam R z i (k + m) =
      Regeneration.regenerationTime Δ lam R z i k +
        Regeneration.regenerationTime Δ lam R
          (Regeneration.sampleTimeShift Δ z
            (Regeneration.regenerationTime Δ lam R z i k).toNNReal) i m := by
  obtain ⟨n, hn⟩ := Regeneration.regenerationTime_mem_grid Δ hΔ lam R z i k hk
  have hnat : (Regeneration.regenerationTime Δ lam R z i k).toNNReal =
      (n : ℝ≥0) * Δ := by rw [hn, ENNReal.toNNReal_coe]
  induction m with
  | zero => simp [Regeneration.regenerationTime]
  | succ m ih =>
    let w := Regeneration.sampleTimeShift Δ z
      (Regeneration.regenerationTime Δ lam R z i k).toNNReal
    by_cases hm : Regeneration.regenerationTime Δ lam R w i m = ⊤
    · have hkm : Regeneration.regenerationTime Δ lam R z i (k + m) = ⊤ := by
        rw [ih, hm, add_top]
      rw [Nat.add_succ, Regeneration.regenerationTime, ite_eq_left hkm,
        Regeneration.regenerationTime, ite_eq_left hm, add_top]
    · have hkm : Regeneration.regenerationTime Δ lam R z i (k + m) ≠ ⊤ := by
        rw [ih]
        exact ENNReal.add_ne_top.mpr ⟨hk, hm⟩
      have hshift : Regeneration.sampleTimeShift Δ z
          (Regeneration.regenerationTime Δ lam R z i (k + m)).toNNReal =
          Regeneration.sampleTimeShift Δ w
            (Regeneration.regenerationTime Δ lam R w i m).toNNReal := by
        rw [ih, ENNReal.toNNReal_add hk hm, hnat,
          sampleTimeShift_add_grid Δ hΔ z n]
        simp only [w, hnat]
      rw [Nat.add_succ, regenerationTime_succ_eq _ _ _ _ _ _ hkm,
        hshift, ih, regenerationTime_succ_eq _ _ _ _ _ _ hm, add_assoc]

/-- On an actual `k`-slice, the recorded future test is the `k+m` observation. -/
theorem sbxS2_PhiM_record_on_slice {d : ℕ} (hd : 2 ≤ d)
    (lam l ρ : ℝ) (h₀ : 0 < lam) (hl : 0 < l)
    (hs : SliceChar (Regeneration.Renewal.regenDelta lam) lam (l / lam)
      (Regeneration.Renewal.forceCoord hd))
    (D : (Regeneration.FutureHalfSpace d (Regeneration.Renewal.forceCoord hd) (l / lam) →
      Mat d × ℝ) → C(Regeneration.FutureHalfSpace d
        (Regeneration.Renewal.forceCoord hd) (l / lam), Mat d × ℝ))
    (hDr : ∀ f : C(Regeneration.FutureHalfSpace d
      (Regeneration.Renewal.forceCoord hd) (l / lam), Mat d × ℝ), D (fun x => f x) = f)
    (G : FieldPair d → ℝ)
    (hG : Measurable[localSigma {x : Vec d | euclideanNorm x < ρ}] G)
    (k m n : ℕ) (hm : 1 ≤ m) (hρ : ρ ≤ (10 * (m : ℝ) + 1) * (l / lam))
    (ω : FieldPair d) (z : Regeneration.CoupledSample d) (t : ℝ≥0)
    (hgain : ∀ j : ℕ, z.2 j = true →
      z.1 ((j : ℝ≥0) * Regeneration.Renewal.regenDelta lam)
          (Regeneration.Renewal.forceCoord hd) + 8 * (l / lam) ≤
        z.1 (((j + 1 : ℕ) : ℝ≥0) * Regeneration.Renewal.regenDelta lam)
          (Regeneration.Renewal.forceCoord hd))
    (hk : regenerationTime hd lam l k z =
      (((n : ℝ≥0) * Regeneration.Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞))
    (hnt : (n : ℝ≥0) * Regeneration.Renewal.regenDelta lam ≤ t) :
    PhiM (Regeneration.Renewal.regenDelta lam) lam (l / lam)
      (Regeneration.Renewal.forceCoord hd) D G m
        (t - (n : ℝ≥0) * Regeneration.Renewal.regenDelta lam)
        (regenerationRecord hd lam l k (ω, z)) =
      if regenerationTime hd lam l (k + m) z ≤ (t : ℝ≥0∞) then
        G (translate (z.1 t) (reduce ω)) else 0 := by
  change Regeneration.regenerationTime (Regeneration.Renewal.regenDelta lam)
    lam (l / lam) z (Regeneration.Renewal.forceCoord hd) k = _ at hk
  have hΔ : 0 < Regeneration.Renewal.regenDelta lam :=
    Real.toNNReal_pos.mpr (inv_pos.mpr (sq_pos_of_pos h₀))
  have hrec : regenerationRecord hd lam l k (ω, z) = Regeneration.futureRecord
      (Regeneration.Renewal.regenDelta lam) (l / lam) ω z
        (Regeneration.Renewal.forceCoord hd)
        ((n : ℝ≥0) * Regeneration.Renewal.regenDelta lam) := by
    unfold regenerationRecord Regeneration.Renewal.cycleRecord
    rw [hk, ENNReal.toNNReal_coe]
  rw [hrec, PhiM_record _ hΔ lam (l / lam) ρ h₀ (div_pos hl h₀) _ hs D hDr
    G hG m hm hρ ω z _ _ (gain_shift _ hΔ _ _ z n hgain)]
  have hkfin : Regeneration.regenerationTime (Regeneration.Renewal.regenDelta lam)
      lam (l / lam) z (Regeneration.Renewal.forceCoord hd) k ≠ ⊤ := by
    rw [show Regeneration.regenerationTime _ _ _ _ _ k =
      (((n : ℝ≥0) * Regeneration.Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞) from hk]
    exact ENNReal.coe_ne_top
  have hadd := sbxS2_regenerationTime_add _ hΔ lam (l / lam)
    (Regeneration.Renewal.forceCoord hd) z k m hkfin
  change regenerationTime hd lam l (k + m) z = _ at hadd
  rw [hk, ENNReal.toNNReal_coe] at hadd
  have hiff : regenerationTime hd lam l (k + m) z ≤ (t : ℝ≥0∞) ↔
      Regeneration.regenerationTime (Regeneration.Renewal.regenDelta lam) lam (l / lam)
        (Regeneration.sampleTimeShift (Regeneration.Renewal.regenDelta lam) z
          ((n : ℝ≥0) * Regeneration.Renewal.regenDelta lam))
        (Regeneration.Renewal.forceCoord hd) m ≤
        ((t - (n : ℝ≥0) * Regeneration.Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞) := by
    rw [hadd]
    exact coe_add_le_coe_iff _ _ _ hnt
  rw [add_tsub_cancel_of_le hnt]
  simp only [← hiff]

/-- Bounded future observables factor on each literal `k`-regeneration slice. -/
theorem sbxS2_bounded_covariance_slice (hfactor : node_rt_u3A_k_u2D_factorStmt)
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ l δ : ℝ}
    (hl : 0 < l) (hsep : r₀ < 2 * l) (hδ₀ : 0 < δ) (hδ₁ : δ < 1)
    (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
    (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K)
    (hD : Regeneration.annealedCoupledLaw Q.measure K
      (regenerationNoReturn hd (l / lam)) ≠ 0)
    (A : ℝ) (hA : l ≤ A) (p : ℝ) (hp : 2 ≤ p) (F G : FieldPair d → ℝ)
    (hF : Measurable[localSigma {x : Vec d | euclideanNorm x < A / lam}] F)
    (hFp : MemLp F (ENNReal.ofReal p) (reducedLaw Q))
    (hG : Measurable[localSigma {x : Vec d | euclideanNorm x < A / lam}] G)
    (hbG : Regeneration.BoundedRealTest G) (n : ℕ) (t : ℝ≥0)
    (hnt : (n : ℝ≥0) * Regeneration.Renewal.regenDelta lam ≤ t) :
    let k : ℕ := max 1 ⌈(A / l + 4) / 10⌉₊
    let m : ℕ := max 1 ⌈(A / l - 1) / 10⌉₊
    let μ := Regeneration.annealedCoupledLaw Q.measure K
    let ν := regenerationConditionedLaw hd Q lam l K hK.1 hD
    (∫ ωz in {ωz | regenerationTime hd lam l k ωz.2 =
        (((n : ℝ≥0) * Regeneration.Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)} ∩
        {ωz | regenerationTime hd lam l (k + m) ωz.2 ≤ (t : ℝ≥0∞)},
      F (reduce ωz.1) * G (translate (ωz.2.1 t) (reduce ωz.1)) ∂μ) =
      (∫ ωz in {ωz | regenerationTime hd lam l k ωz.2 =
        (((n : ℝ≥0) * Regeneration.Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)},
        F (reduce ωz.1) ∂μ) *
      ∫ ωz in {ωz | regenerationTime hd lam l m ωz.2 ≤
          ((t - (n : ℝ≥0) * Regeneration.Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)},
        G (translate (ωz.2.1 (t - (n : ℝ≥0) * Regeneration.Renewal.regenDelta lam))
          (reduce ωz.1)) ∂ν := by
  classical
  dsimp only
  let Δ := Regeneration.Renewal.regenDelta lam
  let k : ℕ := max 1 ⌈(A / l + 4) / 10⌉₊
  let m : ℕ := max 1 ⌈(A / l - 1) / 10⌉₊
  let μ := Regeneration.annealedCoupledLaw Q.measure K
  let ν := regenerationConditionedLaw hd Q lam l K hK.1 hD
  let u : ℝ≥0 := t - (n : ℝ≥0) * Δ
  let slice : Set (FieldPair d × Regeneration.CoupledSample d) :=
    {q | regenerationTime hd lam l k q.2 = (((n : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞)}
  let E : Set (FieldPair d × Regeneration.CoupledSample d) :=
    {q | regenerationTime hd lam l (k + m) q.2 ≤ (t : ℝ≥0∞)}
  let Em : Set (FieldPair d × Regeneration.CoupledSample d) :=
    {q | regenerationTime hd lam l m q.2 ≤ (u : ℝ≥0∞)}
  let obs := fun (v : ℝ≥0) (q : FieldPair d × Regeneration.CoupledSample d) =>
    G (translate (q.2.1 v) (reduce q.1))
  have hm : 1 ≤ m := le_max_left _ _
  have hρ : A / lam ≤ (10 * (m : ℝ) + 1) * (l / lam) := by
    have hx : (A / l - 1) / 10 ≤ (m : ℝ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast le_max_right 1 ⌈(A / l - 1) / 10⌉₊)
    calc A / lam = (A / l) * (l / lam) := by field_simp
         _ ≤ (10 * (m : ℝ) + 1) * (l / lam) :=
           mul_le_mul_of_nonneg_right (by linarith) (div_nonneg hl.le h₀.le)
  have hs := sliceChar_of_slices hd Q lam h₀ h₁ l δ hl hsep hδ₀ hδ₁ P K hK
  obtain ⟨D, hDm, hDr⟩ := Probability.exists_future_halfSpace_decoder
    (Regeneration.Renewal.forceCoord hd) (l / lam)
  let Φ := PhiM Δ lam (l / lam) (Regeneration.Renewal.forceCoord hd) D G m u
  have hτ (j : ℕ) : Measurable (fun q : FieldPair d × Regeneration.CoupledSample d =>
      regenerationTime hd lam l j q.2) :=
    (Regeneration.measurable_regenerationTime Δ lam (l / lam)
      (Regeneration.Renewal.forceCoord hd) j).comp measurable_snd
  have hslice : MeasurableSet slice := hτ k (measurableSet_singleton _)
  have hE : MeasurableSet E := measurableSet_le (hτ (k + m)) measurable_const
  have hEm : MeasurableSet Em := measurableSet_le (hτ m) measurable_const
  have hgain := ae_gain_annealed hd Q lam h₀ h₁ l δ P K hK
  have hac : ν ≪ μ := ProbabilityTheory.cond_absolutelyContinuous
  have hrecord : ∀ᵐ q ∂μ, q ∈ slice →
      E.indicator (fun q => F (reduce q.1) * obs t q) q =
        F (reduce q.1) * Φ (regenerationRecord hd lam l k q) := by
    filter_upwards [hgain] with q hq hqmem
    have heq := sbxS2_PhiM_record_on_slice hd lam l (A / lam) h₀ hl hs D hDr G hG
      k m n hm hρ q.1 q.2 t hq hqmem hnt
    change Φ (regenerationRecord hd lam l k q) = if q ∈ E then obs t q else 0 at heq
    rw [Set.indicator_apply, heq, mul_ite, mul_zero]
  have hrecord0 : ∀ᵐ q ∂ν, Φ (regenerationRecord hd lam l 0 q) = Em.indicator (obs u) q := by
    filter_upwards [hac.ae_le hgain] with q hq
    have heq := sbxS2_PhiM_record_on_slice hd lam l (A / lam) h₀ hl hs D hDr G hG
      0 m 0 hm hρ q.1 q.2 u hq (by simp [regenerationTime, Regeneration.regenerationTime])
      (by simp)
    simpa only [Φ, Em, obs, Set.mem_ofPred_eq, Nat.zero_add, Nat.cast_zero, zero_mul,
      tsub_zero, Set.indicator_apply]
      using heq
  have hfactor' := sbxS2_reduced_kFactor hfactor hd hl hsep hδ₀ hδ₁ Q lam h₀ h₁ P K
    hK hD A hA p hp F hF hFp Φ
    (measurable_PhiM Δ lam (l / lam) (A / lam) _ D hDm G hG m u)
    (boundedRealTest_PhiM Δ lam (l / lam) _ D G hbG m u) n μ (Set.mem_insert _ _)
  change (∫ q in slice ∩ E, F (reduce q.1) * obs t q ∂μ) =
    (∫ q in slice, F (reduce q.1) ∂μ) * ∫ q in Em, obs u q ∂ν
  calc
    _ = ∫ q in slice, E.indicator (fun q => F (reduce q.1) * obs t q) q ∂μ :=
      (setIntegral_indicator hE).symm
    _ = ∫ q in slice, F (reduce q.1) * Φ (regenerationRecord hd lam l k q) ∂μ :=
      setIntegral_congr_ae hslice hrecord
    _ = (∫ q, Φ (regenerationRecord hd lam l 0 q) ∂ν) *
        ∫ q in slice, F (reduce q.1) ∂μ := hfactor'
    _ = _ := by rw [integral_congr_ae hrecord0, integral_indicator hEm, mul_comm]

/-- An integrable reduced first observable times a bounded actual observation is integrable. -/
theorem sbxS2_integrable_bounded_observation {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (K : Regeneration.CoupledQuenchedLaws d)
    (hK : Regeneration.HasProbabilityLaws Q.measure K)
    (F G : FieldPair d → ℝ) (hFi : Integrable F (reducedLaw Q))
    (hG : Measurable G) (hbG : Regeneration.BoundedRealTest G) (t : ℝ≥0) :
    Integrable (fun ωz : FieldPair d × Regeneration.CoupledSample d =>
      F (reduce ωz.1) * G (translate (ωz.2.1 t) (reduce ωz.1)))
      (Regeneration.annealedCoupledLaw Q.measure K) := by
  have hFr := (sbxS2_reducedFst_measurePreserving Q K hK).integrable_comp_of_integrable hFi
  have hobs : Measurable (fun ωz : FieldPair d × Regeneration.CoupledSample d =>
      G (translate (ωz.2.1 t) (reduce ωz.1))) :=
    hG.comp (Probability.continuous_translate.measurable.comp
      (((continuous_eval_const t).measurable.comp measurable_snd.fst).prodMk
        (Probability.measurable_reduce.comp measurable_fst)))
  obtain ⟨C, hC⟩ := hbG
  exact hFr.mul_bdd hobs.aestronglyMeasurable
    (ae_of_all _ fun ωz => by
      simpa only [Real.norm_eq_abs] using (hC (translate (ωz.2.1 t) (reduce ωz.1))))

/-- The actual positive-force covariance decomposition for bounded `G`.
The left observable retains the target's full `Lp` assumption. -/
theorem sbxS2_bounded_covariance_decomposition (hfactor : node_rt_u3A_k_u2D_factorStmt)
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ l δ : ℝ}
    (hl : 0 < l) (hsep : r₀ < 2 * l) (hδ₀ : 0 < δ) (hδ₁ : δ < 1)
    (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
    (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K)
    (hD : Regeneration.annealedCoupledLaw Q.measure K
      (regenerationNoReturn hd (l / lam)) ≠ 0)
    (A : ℝ) (hA : l ≤ A) (p : ℝ) (hp : 2 ≤ p) (F G : FieldPair d → ℝ)
    (hF : Measurable[localSigma {x : Vec d | euclideanNorm x < A / lam}] F)
    (hFp : MemLp F (ENNReal.ofReal p) (reducedLaw Q))
    (hG : Measurable[localSigma {x : Vec d | euclideanNorm x < A / lam}] G)
    (hbG : Regeneration.BoundedRealTest G) (t : ℝ≥0) :
    let k : ℕ := max 1 ⌈(A / l + 4) / 10⌉₊
    let m : ℕ := max 1 ⌈(A / l - 1) / 10⌉₊
    let μ := Regeneration.annealedCoupledLaw Q.measure K
    let ν := regenerationConditionedLaw hd Q lam l K hK.1 hD
    let Δ := Regeneration.Renewal.regenDelta lam
    Integrable (fun ωz => F (reduce ωz.1) * G (translate (ωz.2.1 t) (reduce ωz.1))) μ ∧
    (∫ ωz, F (reduce ωz.1) * G (translate (ωz.2.1 t) (reduce ωz.1)) ∂μ) =
      (∫ ωz in {ωz | (t : ℝ≥0∞) < regenerationTime hd lam l (k + m) ωz.2},
        F (reduce ωz.1) * G (translate (ωz.2.1 t) (reduce ωz.1)) ∂μ) +
      ∑ n ∈ Finset.range (⌊(t : ℝ) / (Δ : ℝ)⌋₊ + 1),
        (∫ ωz in {ωz | regenerationTime hd lam l k ωz.2 =
          (((n : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞)}, F (reduce ωz.1) ∂μ) *
        ∫ ωz in {ωz | regenerationTime hd lam l m ωz.2 ≤
            ((t - (n : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞)},
          G (translate (ωz.2.1 (t - (n : ℝ≥0) * Δ)) (reduce ωz.1)) ∂ν := by
  classical
  dsimp only
  let k : ℕ := max 1 ⌈(A / l + 4) / 10⌉₊
  let m : ℕ := max 1 ⌈(A / l - 1) / 10⌉₊
  let μ := Regeneration.annealedCoupledLaw Q.measure K
  let Δ := Regeneration.Renewal.regenDelta lam
  let f := fun ωz : FieldPair d × Regeneration.CoupledSample d =>
    F (reduce ωz.1) * G (translate (ωz.2.1 t) (reduce ωz.1))
  let E : Set (FieldPair d × Regeneration.CoupledSample d) :=
    {q | regenerationTime hd lam l (k + m) q.2 ≤ (t : ℝ≥0∞)}
  let slice := fun n : ℕ => {q : FieldPair d × Regeneration.CoupledSample d |
    regenerationTime hd lam l k q.2 = (((n : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞)}
  let N := ⌊(t : ℝ) / (Δ : ℝ)⌋₊
  have hΔ : 0 < Δ := Real.toNNReal_pos.mpr (inv_pos.mpr (sq_pos_of_pos h₀))
  let := reducedLaw_probability Q
  have hFi : Integrable F (reducedLaw Q) := hFp.integrable (by
    rw [← ENNReal.ofReal_one, ENNReal.ofReal_le_ofReal_iff (by positivity)]
    linarith)
  have hGg : Measurable G := hG.mono (Probability.localSigma_le_borel _) le_rfl
  have hint := sbxS2_integrable_bounded_observation Q K hK.1 F G hFi hGg hbG t
  refine ⟨hint, ?_⟩
  have hτ (j : ℕ) : Measurable (fun q : FieldPair d × Regeneration.CoupledSample d =>
      regenerationTime hd lam l j q.2) :=
    (Regeneration.measurable_regenerationTime Δ lam (l / lam)
      (Regeneration.Renewal.forceCoord hd) j).comp measurable_snd
  have hE : MeasurableSet E := measurableSet_le (hτ (k + m)) measurable_const
  have hslice (n : ℕ) : MeasurableSet (slice n) := hτ k (measurableSet_singleton _)
  have hnt (n : ℕ) (hn : n ∈ Finset.range (N + 1)) : (n : ℝ≥0) * Δ ≤ t := by
    have hnN : n ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
    have hnreal : (n : ℝ) ≤ (t : ℝ) / (Δ : ℝ) :=
      (Nat.cast_le.mpr hnN).trans (Nat.floor_le (by positivity))
    have hmul : (n : ℝ) * (Δ : ℝ) ≤ (t : ℝ) := by
      rwa [le_div_iff₀ (by exact_mod_cast hΔ)] at hnreal
    exact_mod_cast hmul
  have hcover : E = ⋃ n ∈ Finset.range (N + 1), slice n ∩ E := by
    ext q
    simp only [Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · intro hq
      have hmono : Monotone (fun j => regenerationTime hd lam l j q.2) :=
        monotone_nat_of_le_succ fun j => regenerationTime_le_succ Δ lam (l / lam)
          (Regeneration.Renewal.forceCoord hd) j q.2
      have hkt : regenerationTime hd lam l k q.2 ≤ (t : ℝ≥0∞) :=
        (hmono (Nat.le_add_right k m)).trans hq
      have hkfin : Regeneration.regenerationTime Δ lam (l / lam) q.2
          (Regeneration.Renewal.forceCoord hd) k ≠ ⊤ :=
        ne_top_of_le_ne_top ENNReal.coe_ne_top hkt
      obtain ⟨n, hn⟩ := Regeneration.regenerationTime_mem_grid Δ hΔ lam (l / lam)
        q.2 (Regeneration.Renewal.forceCoord hd) k hkfin
      have hkn : regenerationTime hd lam l k q.2 =
          (((n : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞) := hn
      rw [hkn] at hkt
      have hnr : (n : ℝ) ≤ (t : ℝ) / (Δ : ℝ) := by
        rw [le_div_iff₀ (by exact_mod_cast hΔ)]
        exact_mod_cast ENNReal.coe_le_coe.mp hkt
      exact ⟨n, Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.le_floor hnr)), hkn, hq⟩
    · rintro ⟨_, _, _, hq⟩
      exact hq
  have hsum : (∫ q in E, f q ∂μ) =
      ∑ n ∈ Finset.range (N + 1), ∫ q in slice n ∩ E, f q ∂μ := by
    have h := integral_biUnion_finset (μ := μ) (f := f) (Finset.range (N + 1))
      (s := fun n => slice n ∩ E) (fun n _ => (hslice n).inter hE)
      (by
        intro n _ n' _ hne
        refine Set.disjoint_left.mpr fun q hq hq' => hne ?_
        have heq : (n : ℝ≥0) * Δ = (n' : ℝ≥0) * Δ :=
          ENNReal.coe_injective (hq.1.symm.trans hq'.1)
        exact_mod_cast mul_right_cancel₀ hΔ.ne' heq)
      (fun _ _ => hint.integrableOn)
    rw [← hcover] at h
    exact h
  have hsplit : (∫ q, f q ∂μ) = (∫ q in Eᶜ, f q ∂μ) + ∫ q in E, f q ∂μ := by
    rw [add_comm, integral_add_compl hE hint]
  have hEc : Eᶜ = {q | (t : ℝ≥0∞) < regenerationTime hd lam l (k + m) q.2} := by
    ext q
    change (¬ regenerationTime hd lam l (k + m) q.2 ≤ (t : ℝ≥0∞)) ↔ _
    exact not_le
  change (∫ q, f q ∂μ) = _
  rw [hsplit, hEc, hsum]
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  exact sbxS2_bounded_covariance_slice hfactor hd hl hsep hδ₀ hδ₁ Q lam h₀ h₁ P K hK hD
    A hA p hp F G hF hFp hG hbG n t (hnt n hn)

/-- The supplied remainder estimate on the whole sample space gives actual
covariance integrability at every finite time under both laws. -/
theorem sbxS2_covariance_integrable_of_remainder
    (hrem : node_rt_u3A_remainder_u2D_momentStmt) :
    ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ),
    ∃ l₀ p : ℝ, 0 < l₀ ∧ r₀ < 2 * l₀ ∧ 2 ≤ p ∧
    ∀ (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
      (l δ : ℝ), l₀ ≤ l → 0 < δ → δ < 1 →
    ∀ (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
      (hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K)
      (hD : Regeneration.annealedCoupledLaw Q.measure K
        (regenerationNoReturn hd (l / lam)) ≠ 0),
    ∀ F G : FieldPair d → ℝ, Measurable F → Measurable G →
      MemLp F (ENNReal.ofReal p) (reducedLaw Q) →
      MemLp G (ENNReal.ofReal p) (reducedLaw Q) → ∀ t : ℝ≥0,
    ∀ μ ∈ ({Regeneration.annealedCoupledLaw Q.measure K,
      regenerationConditionedLaw hd Q lam l K hK.1 hD} :
        Set (Measure (FieldPair d × Regeneration.CoupledSample d))),
      Integrable (fun ωz => F (reduce ωz.1) *
        G (translate (ωz.2.1 t) (reduce ωz.1))) μ := by
  intro d hd Λ₀ r₀
  obtain ⟨l₀, p, c, C, hl₀, hsep, hp, _hc, _hC, hrem'⟩ :=
    hrem d hd Λ₀ r₀ 1 1 (by norm_num) (by norm_num)
  refine ⟨l₀, p, hl₀, hsep, hp, ?_⟩
  intro Q lam h₀ h₁ l δ hl hδ₀ hδ₁ P K hK hD F G hF hG hFp hGp t μ hμ
  let : IsProbabilityMeasure (Regeneration.annealedCoupledLaw Q.measure K) :=
    Regeneration.annealedCoupledLaw_isProbabilityMeasure Q.measure K hK.1
  have hprob : Regeneration.annealedCoupledLaw Q.measure K Set.univ ≤
      ENNReal.ofReal (1 * Real.exp (1 * (lam ^ 2 * (t : ℝ)) -
        1 * lam ^ 2 * (t : ℝ))) := by simp
  have hint := (hrem' Q lam h₀ h₁ l δ hl hδ₀ hδ₁ P K hK hD
    F G hF hG hFp hGp (lam ^ 2 * (t : ℝ)) t Set.univ
    (mul_nonneg (sq_nonneg lam) t.coe_nonneg) MeasurableSet.univ hprob μ hμ).1
  simpa only [integrableOn_univ] using hint

/-- Clamping the second factor commutes with a set integral of an integrable
product; the original product supplies domination. -/
theorem sbxS2_tendsto_setIntegral_mul_clamp {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (f g : α → ℝ) (hf : Measurable f) (hg : Measurable g)
    (hfg : Integrable (fun x => f x * g x) μ) (s : Set α) :
    Filter.Tendsto (fun n : ℕ => ∫ x in s,
      f x * max (-(n : ℝ)) (min (n : ℝ) (g x)) ∂μ)
      Filter.atTop (𝓝 (∫ x in s, f x * g x ∂μ)) := by
  apply tendsto_integral_of_dominated_convergence (fun x => |f x * g x|)
  · intro n
    exact (hf.mul (measurable_const.max (measurable_const.min hg))).aestronglyMeasurable
  · exact hfg.integrableOn.abs
  · intro n
    exact Filter.Eventually.of_forall (fun x => by
      rw [Real.norm_eq_abs, abs_mul, abs_mul]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg (f x))
      refine abs_le.mpr ⟨?_, ?_⟩
      · exact le_trans (le_min
          ((neg_nonpos.mpr (abs_nonneg (g x))).trans (Nat.cast_nonneg n))
          (neg_abs_le (g x))) (le_max_right _ _)
      · exact max_le
          ((neg_nonpos.mpr (Nat.cast_nonneg n)).trans (abs_nonneg (g x)))
          ((min_le_right _ _).trans (le_abs_self _)))
  · exact Filter.Eventually.of_forall (fun x => by
      apply tendsto_const_nhds.congr'
      filter_upwards [(tendsto_natCast_atTop_atTop :
        Filter.Tendsto (fun n : ℕ => (n : ℝ)) Filter.atTop Filter.atTop).eventually
          (Filter.eventually_ge_atTop |g x|)] with n hn
      rw [min_eq_right ((le_abs_self _).trans hn), max_eq_right]
      exact (neg_le_neg hn).trans (neg_abs_le _))

/-- The actual covariance decomposition for full local `Lp` tests follows
from the supplied factorization and remainder dependencies. -/
theorem sbxS2_covariance_decomposition_of_deps
    (hfactor : node_rt_u3A_k_u2D_factorStmt)
    (hrem : node_rt_u3A_remainder_u2D_momentStmt) :
    ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ),
    ∃ l₀ p : ℝ, 0 < l₀ ∧ r₀ < 2 * l₀ ∧ 2 ≤ p ∧
    ∀ (l δ : ℝ), l₀ ≤ l → 0 < δ → δ < 1 →
    ∀ (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
    (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K)
    (hD : Regeneration.annealedCoupledLaw Q.measure K
      (regenerationNoReturn hd (l / lam)) ≠ 0)
    (A : ℝ) (_hA : l ≤ A) (F G : FieldPair d → ℝ)
    (_hF : Measurable[localSigma {x : Vec d | euclideanNorm x < A / lam}] F)
    (_hFp : MemLp F (ENNReal.ofReal p) (reducedLaw Q))
    (_hG : Measurable[localSigma {x : Vec d | euclideanNorm x < A / lam}] G)
    (_hGp : MemLp G (ENNReal.ofReal p) (reducedLaw Q)) (t : ℝ≥0),
    let k : ℕ := max 1 ⌈(A / l + 4) / 10⌉₊
    let m : ℕ := max 1 ⌈(A / l - 1) / 10⌉₊
    let μ := Regeneration.annealedCoupledLaw Q.measure K
    let ν := regenerationConditionedLaw hd Q lam l K hK.1 hD
    let Δ := Regeneration.Renewal.regenDelta lam
    Integrable (fun ωz => F (reduce ωz.1) * G (translate (ωz.2.1 t) (reduce ωz.1))) μ ∧
    (∫ ωz, F (reduce ωz.1) * G (translate (ωz.2.1 t) (reduce ωz.1)) ∂μ) =
      (∫ ωz in {ωz | (t : ℝ≥0∞) < regenerationTime hd lam l (k + m) ωz.2},
        F (reduce ωz.1) * G (translate (ωz.2.1 t) (reduce ωz.1)) ∂μ) +
      ∑ n ∈ Finset.range (⌊(t : ℝ) / (Δ : ℝ)⌋₊ + 1),
        (∫ ωz in {ωz | regenerationTime hd lam l k ωz.2 =
          (((n : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞)}, F (reduce ωz.1) ∂μ) *
        ∫ ωz in {ωz | regenerationTime hd lam l m ωz.2 ≤
            ((t - (n : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞)},
          G (translate (ωz.2.1 (t - (n : ℝ≥0) * Δ)) (reduce ωz.1)) ∂ν := by
  intro d hd Λ₀ r₀
  obtain ⟨l₀, p, hl₀, hsep, hp, hInt⟩ :=
    sbxS2_covariance_integrable_of_remainder hrem d hd Λ₀ r₀
  refine ⟨l₀, p, hl₀, hsep, hp, ?_⟩
  intro l δ hl hδ₀ hδ₁ Q lam h₀ h₁ P K hK hD A hA F G hF hFp hG hGp t
  dsimp only
  let k : ℕ := max 1 ⌈(A / l + 4) / 10⌉₊
  let m : ℕ := max 1 ⌈(A / l - 1) / 10⌉₊
  let μ := Regeneration.annealedCoupledLaw Q.measure K
  let ν := regenerationConditionedLaw hd Q lam l K hK.1 hD
  let Δ := Regeneration.Renewal.regenDelta lam
  let N := ⌊(t : ℝ) / (Δ : ℝ)⌋₊
  let q := fun n : ℕ => ∫ ωz in {ωz | regenerationTime hd lam l k ωz.2 =
    (((n : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞)}, F (reduce ωz.1) ∂μ
  let Cov := fun J : FieldPair d → ℝ => ∫ ωz,
    F (reduce ωz.1) * J (translate (ωz.2.1 t) (reduce ωz.1)) ∂μ
  let Rem := fun J : FieldPair d → ℝ => ∫ ωz in
    {ωz | (t : ℝ≥0∞) < regenerationTime hd lam l (k + m) ωz.2},
    F (reduce ωz.1) * J (translate (ωz.2.1 t) (reduce ωz.1)) ∂μ
  let H := fun (J : FieldPair d → ℝ) (u : ℝ≥0) => ∫ ωz in
    {ωz | regenerationTime hd lam l m ωz.2 ≤ (u : ℝ≥0∞)},
    J (translate (ωz.2.1 u) (reduce ωz.1)) ∂ν
  let Gc := fun (n : ℕ) (ω : FieldPair d) => max (-(n : ℝ)) (min (n : ℝ) (G ω))
  have hFg : Measurable F := hF.mono (Probability.localSigma_le_borel _) le_rfl
  have hGg : Measurable G := hG.mono (Probability.localSigma_le_borel _) le_rfl
  have hFr : Measurable (fun ωz : FieldPair d × Regeneration.CoupledSample d =>
      F (reduce ωz.1)) := hFg.comp (Probability.measurable_reduce.comp measurable_fst)
  have hobs (u : ℝ≥0) : Measurable
      (fun ωz : FieldPair d × Regeneration.CoupledSample d =>
        G (translate (ωz.2.1 u) (reduce ωz.1))) :=
    hGg.comp (Probability.continuous_translate.measurable.comp
      (((continuous_eval_const u).measurable.comp measurable_snd.fst).prodMk
        (Probability.measurable_reduce.comp measurable_fst)))
  have hi := hInt Q lam h₀ h₁ l δ hl hδ₀ hδ₁ P K hK hD F G hFg hGg hFp hGp
    t μ (by simp [μ])
  have hiG (u : ℝ≥0) : Integrable
      (fun ωz => G (translate (ωz.2.1 u) (reduce ωz.1))) ν := by
    let : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
    simpa only [one_mul] using
      hInt Q lam h₀ h₁ l δ hl hδ₀ hδ₁ P K hK hD (fun _ => 1) G
        measurable_const hGg (memLp_const 1) hGp u ν (by simp [ν])
  have hGc (n : ℕ) :
      Measurable[localSigma {x : Vec d | euclideanNorm x < A / lam}] (Gc n) :=
    measurable_const.max (measurable_const.min hG)
  have hb (n : ℕ) : Regeneration.BoundedRealTest (Gc n) := by
    refine ⟨(n : ℝ), fun ω => abs_le.mpr ⟨le_max_left _ _, ?_⟩⟩
    exact max_le
      ((neg_nonpos.mpr (Nat.cast_nonneg n)).trans (Nat.cast_nonneg n)) (min_le_left _ _)
  have hCov : Filter.Tendsto (fun n => Cov (Gc n)) Filter.atTop (𝓝 (Cov G)) := by
    simpa only [Cov, Gc, Measure.restrict_univ] using
      sbxS2_tendsto_setIntegral_mul_clamp μ _ _ hFr (hobs t) hi Set.univ
  have hRem : Filter.Tendsto (fun n => Rem (Gc n)) Filter.atTop (𝓝 (Rem G)) :=
    sbxS2_tendsto_setIntegral_mul_clamp μ _ _ hFr (hobs t) hi _
  have hH (u : ℝ≥0) :
      Filter.Tendsto (fun n => H (Gc n) u) Filter.atTop (𝓝 (H G u)) := by
    simpa only [H, Gc, one_mul] using
      sbxS2_tendsto_setIntegral_mul_clamp ν (fun _ => 1) _ measurable_const (hobs u)
        (by simpa only [one_mul] using hiG u) {ωz | regenerationTime hd lam l m ωz.2 ≤
          (u : ℝ≥0∞)}
  have heq (n : ℕ) : Cov (Gc n) = Rem (Gc n) +
      ∑ j ∈ Finset.range (N + 1), q j * H (Gc n) (t - j * Δ) :=
    (sbxS2_bounded_covariance_decomposition hfactor hd (hl₀.trans_le hl)
      (hsep.trans_le (by linarith)) hδ₀ hδ₁ Q lam h₀ h₁ P K hK hD A hA p hp F
      (Gc n) hF hFp (hGc n) (hb n) t).2
  have hsum : Filter.Tendsto
      (fun n => ∑ j ∈ Finset.range (N + 1), q j * H (Gc n) (t - j * Δ))
      Filter.atTop (𝓝 (∑ j ∈ Finset.range (N + 1), q j * H G (t - j * Δ))) :=
    tendsto_finsetSum (Finset.range (N + 1))
      (fun j _ => tendsto_const_nhds.mul (hH (t - j * Δ)))
  refine ⟨hi, ?_⟩
  exact tendsto_nhds_unique hCov ((hRem.add hsum).congr'
    (Filter.Eventually.of_forall (fun n => (heq n).symm)))

/-- The actual covariance has the centered phase decomposition, including the
literal omitted tail. Only the supplied dependencies produce its ingredients. -/
theorem sbxS2_centered_covariance_of_deps
    (hfactor : node_rt_u3A_k_u2D_factorStmt)
    (hmany : node_rt_u3A_many_u2D_cycle_u2D_momentStmt)
    (hrem : node_rt_u3A_remainder_u2D_momentStmt) :
    ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ),
    ∃ l₀ p : ℝ, 0 < l₀ ∧ r₀ < 2 * l₀ ∧ 2 ≤ p ∧
    ∀ (l δ : ℝ), l₀ ≤ l → 0 < δ → δ < 1 →
    ∀ (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
      (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
      (hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K)
      (hD : Regeneration.annealedCoupledLaw Q.measure K
        (regenerationNoReturn hd (l / lam)) ≠ 0)
      (A : ℝ) (_hA : l ≤ A) (F G : FieldPair d → ℝ)
      (_hF : Measurable[localSigma {x : Vec d | euclideanNorm x < A / lam}] F)
      (_hG : Measurable[localSigma {x : Vec d | euclideanNorm x < A / lam}] G)
      (_hFp : MemLp F (ENNReal.ofReal p) (reducedLaw Q))
      (_hGp : MemLp G (ENNReal.ofReal p) (reducedLaw Q))
      (_hzero : (∫ ω, F ω ∂reducedLaw Q) = 0),
    let k : ℕ := max 1 ⌈(A / l + 4) / 10⌉₊
    let m : ℕ := max 1 ⌈(A / l - 1) / 10⌉₊
    let μ := Regeneration.annealedCoupledLaw Q.measure K
    let ν := regenerationConditionedLaw hd Q lam l K hK.1 hD
    let Δ := Regeneration.Renewal.regenDelta lam
    let pn := regenerationLatticeMass hd Q lam l K hK.1 hD
    let mean := ∑' n : ℕ, (n : ℝ) * pn n
    let q := fun n : ℕ => ∫ ωz in {ωz | regenerationTime hd lam l k ωz.2 =
      (((n : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞)}, F (reduce ωz.1) ∂μ
    let hm := fun t : ℝ≥0 => ∫ ωz in {ωz |
      regenerationTime hd lam l m ωz.2 ≤ (t : ℝ≥0∞)},
      G (translate (ωz.2.1 t) (reduce ωz.1)) ∂ν
    let rm := fun t : ℝ≥0 => ∫ ωz in {ωz |
      regenerationTime hd lam l m ωz.2 ≤ (t : ℝ≥0∞) ∧
      (t : ℝ≥0∞) < regenerationTime hd lam l (m + 1) ωz.2},
      G (translate (ωz.2.1 t) (reduce ωz.1)) ∂ν
    let Hm := fun s : ℝ≥0 => mean⁻¹ * ∑' j : ℕ, rm (s + j * Δ)
    let cov := fun t : ℝ≥0 => ∫ ωz, F (reduce ωz.1) *
      G (translate (ωz.2.1 t) (reduce ωz.1)) ∂μ
    let rem := fun t : ℝ≥0 => ∫ ωz in {ωz | (t : ℝ≥0∞) <
      regenerationTime hd lam l (k + m) ωz.2}, F (reduce ωz.1) *
        G (translate (ωz.2.1 t) (reduce ωz.1)) ∂μ
    Summable q ∧ (∑' n, q n) = 0 ∧
    (∀ t : ℝ≥0, Integrable (fun ωz => F (reduce ωz.1) *
        G (translate (ωz.2.1 t) (reduce ωz.1))) μ ∧
      cov t = rem t + ∑ n ∈ Finset.range (⌊(t : ℝ) / (Δ : ℝ)⌋₊ + 1),
        q n * hm (t - n * Δ)) ∧
    ∀ s : ℝ≥0, s < Δ → ∀ j : ℕ,
      cov (s + j * Δ) = rem (s + j * Δ) +
        (∑ n ∈ Finset.range (j + 1), q n * (hm (s + (j - n) * Δ) - Hm s)) -
        Hm s * ∑' n : ℕ, q (j + 1 + n) := by
  intro d hd Λ₀ r₀
  obtain ⟨lD, p, hlD, hsepD, hp, hDec⟩ :=
    sbxS2_covariance_decomposition_of_deps hfactor hrem d hd Λ₀ r₀
  obtain ⟨lM, _hlM, _hsepM, hCenter⟩ :=
    sbxS2_centered_slices_of_manyCycleMoment hmany d hd Λ₀ r₀
  refine ⟨max lD lM, p, hlD.trans_le (le_max_left _ _),
    hsepD.trans_le (by linarith only [le_max_left lD lM]), hp, ?_⟩
  intro l δ hl hδ₀ hδ₁ Q lam h₀ h₁ P K hK hD A hA F G hF hG hFp hGp hzero
  dsimp only
  let k : ℕ := max 1 ⌈(A / l + 4) / 10⌉₊
  let m : ℕ := max 1 ⌈(A / l - 1) / 10⌉₊
  let μ := Regeneration.annealedCoupledLaw Q.measure K
  let ν := regenerationConditionedLaw hd Q lam l K hK.1 hD
  let Δ := Regeneration.Renewal.regenDelta lam
  let q := fun n : ℕ => ∫ ωz in {ωz | regenerationTime hd lam l k ωz.2 =
    (((n : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞)}, F (reduce ωz.1) ∂μ
  let hm := fun t : ℝ≥0 => ∫ ωz in
    {ωz | regenerationTime hd lam l m ωz.2 ≤ (t : ℝ≥0∞)},
    G (translate (ωz.2.1 t) (reduce ωz.1)) ∂ν
  have hq : Summable q ∧ (∑' n, q n) = 0 :=
    hCenter l ((le_max_right _ _).trans hl) δ hδ₀ hδ₁ Q lam h₀ h₁ P K hK hD p
      ((by norm_num : (1 : ℝ) ≤ 2).trans hp) F
      (hF.mono (Probability.localSigma_le_borel _) le_rfl) hFp hzero k
  have hcov := hDec l δ ((le_max_left _ _).trans hl) hδ₀ hδ₁ Q lam h₀ h₁
    P K hK hD A hA F G hF hFp hG hGp
  refine ⟨hq.1, hq.2, hcov, ?_⟩
  intro s hs j
  have hΔ : 0 < Δ := Real.toNNReal_pos.mpr (inv_pos.mpr (sq_pos_of_pos h₀))
  have hΔR : 0 < (Δ : ℝ) := hΔ
  have hsR : (s : ℝ) < (Δ : ℝ) := hs
  have hquot : ((s + j * Δ : ℝ≥0) : ℝ) / (Δ : ℝ) =
      (s : ℝ) / (Δ : ℝ) + (j : ℝ) := by
    simp only [NNReal.coe_add, NNReal.coe_mul, NNReal.coe_natCast, add_div,
      mul_div_cancel_right₀ _ hΔR.ne']
  have hfloor : ⌊((s + j * Δ : ℝ≥0) : ℝ) / (Δ : ℝ)⌋₊ = j := by
    rw [hquot, Nat.floor_add_natCast (by positivity),
      Nat.floor_eq_zero.mpr ((div_lt_one hΔR).mpr hsR), zero_add]
  rw [(hcov (s + j * Δ)).2, hfloor]
  have htimes : (∑ n ∈ Finset.range (j + 1), q n * hm (s + j * Δ - n * Δ)) =
      ∑ n ∈ Finset.range (j + 1), q n * hm (s + (j - n) * Δ) := by
    apply Finset.sum_congr rfl
    intro n hn
    have hnj : n ≤ j := Nat.le_of_lt_succ (Finset.mem_range.mp hn)
    rw [add_tsub_assoc_of_le (mul_le_mul_of_nonneg_right
      (show (n : ℝ≥0) ≤ j by exact_mod_cast hnj) bot_le),
      ← tsub_mul, ← Nat.cast_tsub]
  rw [htimes, sbxS2_centered_convolution q (fun n => hm (s + (j - n) * Δ))
    _ j hq.1 hq.2, add_sub_assoc]

/-- Exponential bounds for the two centered factors control both the finite
convolution and the omitted infinite tail. -/
theorem sbxS2_centered_convolution_decay (q h : ℕ → ℝ) (H Rq Rh a b : ℝ)
    (hRq : 0 ≤ Rq) (hRh : 0 ≤ Rh) (ha : 0 < a) (hb : 0 < b)
    (hq : ∀ n : ℕ, |q n| ≤ Rq * Real.exp (-a * n))
    (hh : ∀ n : ℕ, |h n - H| ≤ Rh * Real.exp (-b * n)) (hH : |H| ≤ Rh)
    (j : ℕ) :
    |(∑ n ∈ Finset.range (j + 1), q n * (h (j - n) - H)) -
        H * ∑' n : ℕ, q (j + 1 + n)| ≤
      Rq * Rh * ((1 + 2 / min a b) + (1 - Real.exp (-a))⁻¹) *
        Real.exp (-(min a b / 2) * j) := by
  have hρ : Real.exp (-a) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hρ₀ : 0 < Real.exp (-a) := Real.exp_pos _
  have hden : 0 < 1 - Real.exp (-a) := sub_pos.mpr hρ
  have hmin : 0 < min a b := lt_min ha hb
  have hgeom (n : ℕ) : Real.exp (-a * n) = Real.exp (-a) ^ n := by
    rw [mul_comm, Real.exp_nat_mul]
  have htail : |∑' n : ℕ, q (j + 1 + n)| ≤
      Rq * Real.exp (-a * (j + 1 : ℕ)) * (1 - Real.exp (-a))⁻¹ := by
    have hbound := tsum_of_norm_bounded
      ((hasSum_geometric_of_lt_one hρ₀.le hρ).mul_left
        (Rq * Real.exp (-a * (j + 1 : ℕ))))
      (f := fun n : ℕ => q (j + 1 + n)) (fun n => by
        rw [Real.norm_eq_abs]
        calc |q (j + 1 + n)| ≤ Rq * Real.exp (-a * (j + 1 + n : ℕ)) := hq _
          _ = Rq * Real.exp (-a * (j + 1 : ℕ)) * Real.exp (-a) ^ n := by
            rw [hgeom, pow_add, hgeom]
            ring)
    simpa only [Real.norm_eq_abs] using hbound
  have hrate : Real.exp (-a * (j + 1 : ℕ)) ≤
      Real.exp (-(min a b / 2) * j) := by
    apply Real.exp_le_exp.mpr
    push_cast
    have hma := min_le_left a b
    have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg _
    nlinarith
  have hfinite : |∑ n ∈ Finset.range (j + 1), q n * (h (j - n) - H)| ≤
      Rq * Rh * (1 + 2 / min a b) * Real.exp (-(min a b / 2) * j) := by
    calc _ ≤ ∑ n ∈ Finset.range (j + 1), |q n * (h (j - n) - H)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ n ∈ Finset.range (j + 1), Rq * Rh *
          (Real.exp (-b * (j - n : ℕ)) * Real.exp (-a * n)) := by
        apply Finset.sum_le_sum
        intro n _hn
        rw [abs_mul]
        calc _ ≤ (Rq * Real.exp (-a * n)) *
              (Rh * Real.exp (-b * (j - n : ℕ))) :=
            mul_le_mul (hq n) (hh _) (abs_nonneg _) (by positivity)
          _ = _ := by ring
      _ = Rq * Rh * ∑ n ∈ Finset.range (j + 1),
          Real.exp (-b * (j - n : ℕ)) * Real.exp (-a * n) := by
        rw [Finset.mul_sum]
      _ ≤ Rq * Rh * (((j : ℝ) + 1) * Real.exp (-min a b * j)) := by
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg hRq hRh)
        simpa only [min_comm] using sum_conv_exp_le b a hb ha j
      _ ≤ Rq * Rh * ((1 + 2 / min a b) * Real.exp (-(min a b / 2) * j)) :=
        mul_le_mul_of_nonneg_left (lin_exp_le _ hmin j) (mul_nonneg hRq hRh)
      _ = _ := by ring
  calc _ ≤ |∑ n ∈ Finset.range (j + 1), q n * (h (j - n) - H)| +
        |H * ∑' n : ℕ, q (j + 1 + n)| := abs_sub _ _
    _ ≤ Rq * Rh * (1 + 2 / min a b) * Real.exp (-(min a b / 2) * j) +
        Rh * (Rq * Real.exp (-a * (j + 1 : ℕ)) * (1 - Real.exp (-a))⁻¹) := by
      apply add_le_add hfinite
      rw [abs_mul]
      exact mul_le_mul hH htail (abs_nonneg _) hRh
    _ ≤ Rq * Rh * (1 + 2 / min a b) * Real.exp (-(min a b / 2) * j) +
        Rh * (Rq * Real.exp (-(min a b / 2) * j) * (1 - Real.exp (-a))⁻¹) := by
      gcongr
    _ = _ := by ring

/-- The four supplied dependencies give decay of the actual covariance after
subtracting its literal early-regeneration remainder. This does not estimate
that remainder or identify an arbitrary environment semigroup. -/
theorem sbxS2_covariance_sub_remainder_decay_of_deps
    (hfactor : node_rt_u3A_k_u2D_factorStmt)
    (hphase : node_rt_u3A_local_u2D_mixing_u23_phase_u2D_errorStmt)
    (hmany : node_rt_u3A_many_u2D_cycle_u2D_momentStmt)
    (hrem : node_rt_u3A_remainder_u2D_momentStmt) :
    ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ),
    ∃ l₀ : ℝ, 0 < l₀ ∧ r₀ < 2 * l₀ ∧
    ∀ l : ℝ, l₀ ≤ l → ∀ δ : ℝ, 0 < δ → δ < 1 →
    ∃ p c C : ℝ, 2 ≤ p ∧ 0 < c ∧ 0 < C ∧
    ∀ (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
      (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
      (_hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K)
      (_hD : Regeneration.annealedCoupledLaw Q.measure K
        (regenerationNoReturn hd (l / lam)) ≠ 0)
      (A : ℝ), l ≤ A → ∀ F G : FieldPair d → ℝ,
    Measurable[localSigma {x : Vec d | euclideanNorm x < A / lam}] F →
    Measurable[localSigma {x : Vec d | euclideanNorm x < A / lam}] G →
    MemLp F (ENNReal.ofReal p) (reducedLaw Q) →
    MemLp G (ENNReal.ofReal p) (reducedLaw Q) →
    (∫ ω, F ω ∂reducedLaw Q) = 0 →
    let k : ℕ := max 1 ⌈(A / l + 4) / 10⌉₊
    let m : ℕ := max 1 ⌈(A / l - 1) / 10⌉₊
    let μ := Regeneration.annealedCoupledLaw Q.measure K
    let Δ := Regeneration.Renewal.regenDelta lam
    let cov := fun t : ℝ≥0 => ∫ ωz, F (reduce ωz.1) *
      G (translate (ωz.2.1 t) (reduce ωz.1)) ∂μ
    let rem := fun t : ℝ≥0 => ∫ ωz in {ωz | (t : ℝ≥0∞) <
      regenerationTime hd lam l (k + m) ωz.2}, F (reduce ωz.1) *
        G (translate (ωz.2.1 t) (reduce ωz.1)) ∂μ
    ∀ s : ℝ≥0, s < Δ → ∀ j : ℕ,
      |cov (s + j * Δ) - rem (s + j * Δ)| ≤
        C * Real.exp (C * (k + m) - c * j) *
          (eLpNorm F (ENNReal.ofReal p) (reducedLaw Q)).toReal *
          (eLpNorm G (ENNReal.ofReal p) (reducedLaw Q)).toReal := by
  intro d hd Λ₀ r₀
  obtain ⟨lD, pD, hlD, hsepD, hpD, hcenter⟩ :=
    sbxS2_centered_covariance_of_deps hfactor hmany hrem d hd Λ₀ r₀
  obtain ⟨lM, _hlM, _hsepM, hdecay⟩ :=
    sbxS2_slice_decay_of_manyCycleMoment hmany d hd Λ₀ r₀
  obtain ⟨lP, _hlP, _hsepP, hph⟩ := hphase d hd Λ₀ r₀
  refine ⟨max lD (max lM lP), hlD.trans_le (le_max_left _ _),
    hsepD.trans_le (by linarith only [le_max_left lD (max lM lP)]), ?_⟩
  intro l hl δ hδ₀ hδ₁
  have hlD' : lD ≤ l := (le_max_left _ _).trans hl
  have hlM' : lM ≤ l := (le_max_left _ _).trans ((le_max_right _ _).trans hl)
  have hlP' : lP ≤ l := (le_max_right _ _).trans ((le_max_right _ _).trans hl)
  have hlpos : 0 < l := hlD.trans_le hlD'
  obtain ⟨a, Cq, ha, hCq, hqd⟩ := hdecay l hlM' δ hδ₀ hδ₁
  obtain ⟨pP, b, Cp, hpP, hb, hCp, hpd⟩ := hph l hlP' δ hδ₀ hδ₁
  let p := max pD pP
  let c := min (a / 2) b / 2
  let B := (1 + 2 / min (a / 2) b) + (1 - Real.exp (-(a / 2)))⁻¹
  have ha' : 0 < a / 2 := half_pos ha
  have hmin : 0 < min (a / 2) b := lt_min ha' hb
  have hden : 0 < 1 - Real.exp (-(a / 2)) :=
    sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_neg_of_pos ha'))
  have hB : 0 < B := by dsimp only [B]; positivity
  let C := 1 + Cp * B + Cq + Cp
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨p, c, C, hpD.trans (le_max_left _ _), half_pos hmin, hC, ?_⟩
  intro Q lam h₀ h₁ P K hK hD A hA F G hF hG hFp hGp hzero
  let := reducedLaw_probability Q
  dsimp only
  let k : ℕ := max 1 ⌈(A / l + 4) / 10⌉₊
  let m : ℕ := max 1 ⌈(A / l - 1) / 10⌉₊
  let μ := Regeneration.annealedCoupledLaw Q.measure K
  let ν := regenerationConditionedLaw hd Q lam l K hK.1 hD
  let Δ := Regeneration.Renewal.regenDelta lam
  let q := fun n : ℕ => ∫ ωz in {ωz | regenerationTime hd lam l k ωz.2 =
    (((n : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞)}, F (reduce ωz.1) ∂μ
  let hm := fun t : ℝ≥0 => ∫ ωz in {ωz |
    regenerationTime hd lam l m ωz.2 ≤ (t : ℝ≥0∞)},
    G (translate (ωz.2.1 t) (reduce ωz.1)) ∂ν
  let rm := fun t : ℝ≥0 => ∫ ωz in {ωz |
    regenerationTime hd lam l m ωz.2 ≤ (t : ℝ≥0∞) ∧
    (t : ℝ≥0∞) < regenerationTime hd lam l (m + 1) ωz.2},
    G (translate (ωz.2.1 t) (reduce ωz.1)) ∂ν
  let Hm := fun s : ℝ≥0 => (∑' n : ℕ, (n : ℝ) *
    regenerationLatticeMass hd Q lam l K hK.1 hD n)⁻¹ * ∑' j : ℕ, rm (s + j * Δ)
  let Nf := (eLpNorm F (ENNReal.ofReal p) (reducedLaw Q)).toReal
  let Ng := (eLpNorm G (ENNReal.ofReal p) (reducedLaw Q)).toReal
  have hpD' : ENNReal.ofReal pD ≤ ENNReal.ofReal p :=
    ENNReal.ofReal_le_ofReal (le_max_left _ _)
  have hpP' : ENNReal.ofReal pP ≤ ENNReal.ofReal p :=
    ENNReal.ofReal_le_ofReal (le_max_right _ _)
  have hNg : (eLpNorm G (ENNReal.ofReal pP) (reducedLaw Q)).toReal ≤ Ng :=
    ENNReal.toReal_mono hGp.eLpNorm_ne_top (eLpNorm_le_eLpNorm_of_exponent_le hpP')
  have hco := hcenter l δ hlD' hδ₀ hδ₁ Q lam h₀ h₁ P K hK hD A hA F G hF hG
    (hFp.mono_exponent hpD') (hGp.mono_exponent hpD') hzero
  have hsupport : 10 * (m : ℝ) * l - l - A ≥ -2 * l := by
    have hx : (A / l - 1) / 10 ≤ (m : ℝ) := (Nat.le_ceil _).trans
      (by exact_mod_cast le_max_right 1 ⌈(A / l - 1) / 10⌉₊)
    have hdiv : A / l ≤ 10 * (m : ℝ) + 1 := by linarith
    have := (div_le_iff₀ hlpos).mp hdiv
    nlinarith
  have hpa := hpd Q lam h₀ h₁ P K hK hD A m hA (le_max_left _ _) hsupport G hG
    (hGp.mono_exponent hpP')
  intro s hs j
  have hpa' := hpa.2 s hs
  let Rq := Real.exp (Cq * k / 2) * Nf
  let Rh := Cp * Real.exp (Cp * m) * Ng
  have hRq : 0 ≤ Rq := by dsimp only [Rq, Nf]; positivity
  have hRh : 0 ≤ Rh := by dsimp only [Rh, Ng]; positivity
  have hq : ∀ n : ℕ, |q n| ≤ Rq * Real.exp (-(a / 2) * n) := by
    intro n
    calc _ ≤ Real.exp ((Cq * k - a * n) / 2) * Nf :=
        hqd Q lam h₀ h₁ P K hK hD p (hpD.trans (le_max_left _ _)) F
          (hF.mono (Probability.localSigma_le_borel _) le_rfl) hFp k (le_max_left _ _) n
      _ = _ := by
        dsimp only [Rq]
        rw [show (Cq * k - a * n) / 2 = Cq * k / 2 + (-(a / 2) * n) by ring,
          Real.exp_add]
        ring
  have hh : ∀ n : ℕ, |hm (s + n * Δ) - Hm s| ≤ Rh * Real.exp (-b * n) := by
    intro n
    calc _ ≤ Cp * Real.exp (Cp * m - b * n) *
          (eLpNorm G (ENNReal.ofReal pP) (reducedLaw Q)).toReal := (hpa'.2.2 n).2.2
      _ ≤ Cp * Real.exp (Cp * m - b * n) * Ng :=
        mul_le_mul_of_nonneg_left hNg (by positivity)
      _ = _ := by
        dsimp only [Rh]
        rw [show Cp * m - b * n = Cp * m + (-b * n) by ring, Real.exp_add]
        ring
  have hH : |Hm s| ≤ Rh := hpa'.2.1.trans
    (mul_le_mul_of_nonneg_left hNg (by positivity))
  have hest := sbxS2_centered_convolution_decay q (fun n => hm (s + n * Δ))
    (Hm s) Rq Rh (a / 2) b hRq hRh ha' hb hq hh hH j
  simp only [Nat.cast_tsub] at hest
  have heq := hco.2.2.2 s hs j
  have hid : (∫ ωz, F (reduce ωz.1) * G (translate
        (ωz.2.1 (s + j * Δ)) (reduce ωz.1)) ∂μ) -
      (∫ ωz in {ωz | ((s + j * Δ : ℝ≥0) : ℝ≥0∞) <
        regenerationTime hd lam l (k + m) ωz.2}, F (reduce ωz.1) *
          G (translate (ωz.2.1 (s + j * Δ)) (reduce ωz.1)) ∂μ) =
      (∑ n ∈ Finset.range (j + 1), q n * (hm (s + (j - n) * Δ) - Hm s)) -
        Hm s * ∑' n : ℕ, q (j + 1 + n) := by linarith only [heq]
  rw [hid]
  apply hest.trans
  have hcoeff : Cp * B ≤ C := by dsimp only [C]; linarith
  have hexp : Cq * k / 2 + Cp * m ≤ C * (k + m) := by
    have hk₀ : (0 : ℝ) ≤ k := Nat.cast_nonneg _
    have hm₀ : (0 : ℝ) ≤ m := Nat.cast_nonneg _
    have hCq' : Cq / 2 ≤ C := by dsimp only [C]; nlinarith only [hCp, hCq, hB, mul_pos hCp hB]
    have hCp' : Cp ≤ C := by dsimp only [C]; linarith only [hCq, mul_pos hCp hB]
    nlinarith only [mul_nonneg (sub_nonneg.mpr hCq') hk₀,
      mul_nonneg (sub_nonneg.mpr hCp') hm₀]
  calc
    Rq * Rh * B * Real.exp (-(min (a / 2) b / 2) * j) =
        (Cp * B) * Real.exp (Cq * k / 2 + Cp * m - c * j) * Nf * Ng := by
      dsimp only [Rq, Rh, c]
      simp only [sub_eq_add_neg, neg_mul, Real.exp_add]
      ring
    _ ≤ C * Real.exp (C * (k + m) - c * j) * Nf * Ng := by
      gcongr

/-- The actual slice bound in the normalization used by `rt:km-decomp`. -/
theorem sbxS2_slice_decay_normalized_of_manyCycleMoment
    (hmany : node_rt_u3A_many_u2D_cycle_u2D_momentStmt)
    (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ) :
    ∃ l₀ : ℝ, 0 < l₀ ∧ r₀ < 2 * l₀ ∧
    ∀ l : ℝ, l₀ ≤ l → ∀ δ : ℝ, 0 < δ → δ < 1 →
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    ∀ (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
      (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
      (_hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K)
      (_hD : Regeneration.annealedCoupledLaw Q.measure K
        (regenerationNoReturn hd (l / lam)) ≠ 0)
      (p : ℝ), 2 ≤ p → ∀ F : FieldPair d → ℝ,
    Measurable F → MemLp F (ENNReal.ofReal p) (reducedLaw Q) →
    ∀ k : ℕ, 1 ≤ k → ∀ n : ℕ,
    |∫ ωz in {ωz | regenerationTime hd lam l k ωz.2 =
      (((n : ℝ≥0) * Regeneration.Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)},
      F (reduce ωz.1) ∂Regeneration.annealedCoupledLaw Q.measure K| ≤
      C * Real.exp (C * k - c * n) *
        (eLpNorm F (ENNReal.ofReal p) (reducedLaw Q)).toReal := by
  obtain ⟨l₀, hl₀, hsep, hdec⟩ := sbxS2_slice_decay_of_manyCycleMoment hmany d hd Λ₀ r₀
  refine ⟨l₀, hl₀, hsep, ?_⟩
  intro l hl δ hδ₀ hδ₁
  obtain ⟨a, Cq, ha, hCq, hq⟩ := hdec l hl δ hδ₀ hδ₁
  refine ⟨a / 2, 1 + Cq, half_pos ha, by positivity, ?_⟩
  intro Q lam h₀ h₁ P K hK hD p hp F hF hFp k hk n
  apply (hq Q lam h₀ h₁ P K hK hD p hp F hF hFp k hk n).trans
  apply mul_le_mul_of_nonneg_right _ ENNReal.toReal_nonneg
  calc
    Real.exp ((Cq * k - a * n) / 2) ≤
        Real.exp ((1 + Cq) * k - (a / 2) * n) := by
      apply Real.exp_le_exp.mpr
      have hk₀ : (0 : ℝ) ≤ k := Nat.cast_nonneg _
      nlinarith only [hk₀, mul_nonneg hCq.le hk₀]
    _ ≤ (1 + Cq) * Real.exp ((1 + Cq) * k - (a / 2) * n) := by
      nlinarith only [hCq, Real.exp_pos ((1 + Cq) * k - (a / 2) * n)]

/-- The actual covariance minus its early-regeneration remainder decays at all
continuous times, with structural thresholds and the prescribed cycle counts. -/
theorem sbxS2_covariance_sub_remainder_time_decay_of_deps
    (hfactor : node_rt_u3A_k_u2D_factorStmt)
    (hphase : node_rt_u3A_local_u2D_mixing_u23_phase_u2D_errorStmt)
    (hmany : node_rt_u3A_many_u2D_cycle_u2D_momentStmt)
    (hrem : node_rt_u3A_remainder_u2D_momentStmt) :
    ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ),
    ∃ l₀ : ℝ, 0 < l₀ ∧ r₀ < 2 * l₀ ∧
    ∀ l : ℝ, l₀ ≤ l → ∀ δ : ℝ, 0 < δ → δ < 1 →
    ∃ p c C : ℝ, 2 ≤ p ∧ 0 < c ∧ 0 < C ∧
    ∀ (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
      (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
      (_hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K)
      (_hD : Regeneration.annealedCoupledLaw Q.measure K
        (regenerationNoReturn hd (l / lam)) ≠ 0)
      (A : ℝ), l ≤ A → ∀ F G : FieldPair d → ℝ,
    Measurable[localSigma {x : Vec d | euclideanNorm x < A / lam}] F →
    Measurable[localSigma {x : Vec d | euclideanNorm x < A / lam}] G →
    MemLp F (ENNReal.ofReal p) (reducedLaw Q) →
    MemLp G (ENNReal.ofReal p) (reducedLaw Q) →
    (∫ ω, F ω ∂reducedLaw Q) = 0 →
    let k : ℕ := max 1 ⌈(A / l + 4) / 10⌉₊
    let m : ℕ := max 1 ⌈(A / l - 1) / 10⌉₊
    let μ := Regeneration.annealedCoupledLaw Q.measure K
    let cov := fun t : ℝ≥0 => ∫ ωz, F (reduce ωz.1) *
      G (translate (ωz.2.1 t) (reduce ωz.1)) ∂μ
    let rem := fun t : ℝ≥0 => ∫ ωz in {ωz | (t : ℝ≥0∞) <
      regenerationTime hd lam l (k + m) ωz.2}, F (reduce ωz.1) *
        G (translate (ωz.2.1 t) (reduce ωz.1)) ∂μ
    ∀ t : ℝ≥0, |cov t - rem t| ≤
      C * Real.exp (C * (k + m) - c * lam ^ 2 * (t : ℝ)) *
        (eLpNorm F (ENNReal.ofReal p) (reducedLaw Q)).toReal *
        (eLpNorm G (ENNReal.ofReal p) (reducedLaw Q)).toReal := by
  intro d hd Λ₀ r₀
  obtain ⟨l₀, hl₀, hsep, hdec⟩ :=
    sbxS2_covariance_sub_remainder_decay_of_deps hfactor hphase hmany hrem d hd Λ₀ r₀
  refine ⟨l₀, hl₀, hsep, ?_⟩
  intro l hl δ hδ₀ hδ₁
  obtain ⟨p, c, C, hp, hc, hC, hbound⟩ := hdec l hl δ hδ₀ hδ₁
  let D := C * Real.exp c + C
  have hDpos : 0 < D := by dsimp only [D]; positivity
  have hCD : C ≤ D := by dsimp only [D]; linarith only [mul_pos hC (Real.exp_pos c)]
  refine ⟨p, c, D, hp, hc, hDpos, ?_⟩
  intro Q lam h₀ h₁ P K hK hD A hA F G hF hG hFp hGp hzero
  dsimp only
  intro t
  let Δ := Regeneration.Renewal.regenDelta lam
  have hΔ : 0 < (Δ : ℝ) := Real.toNNReal_pos.mpr (inv_pos.mpr (sq_pos_of_pos h₀))
  have hΔcoe : (Δ : ℝ) = (lam ^ 2)⁻¹ :=
    Real.coe_toNNReal _ (inv_nonneg.mpr (sq_nonneg lam))
  let j : ℕ := ⌊(t : ℝ) / (Δ : ℝ)⌋₊
  have hfloor : (j : ℝ) ≤ (t : ℝ) / (Δ : ℝ) := Nat.floor_le (by positivity)
  have hupper : (t : ℝ) / (Δ : ℝ) < (j : ℝ) + 1 := Nat.lt_floor_add_one _
  have hmul : (j : ℝ≥0) * Δ ≤ t := by
    apply NNReal.coe_le_coe.mp
    simpa only [NNReal.coe_mul, NNReal.coe_natCast] using (le_div_iff₀ hΔ).mp hfloor
  let s := t - (j : ℝ≥0) * Δ
  have hsum : s + j * Δ = t := tsub_add_cancel_of_le hmul
  have hs : s < Δ := by
    have ht : (t : ℝ) < ((j : ℝ) + 1) * (Δ : ℝ) := (div_lt_iff₀ hΔ).mp hupper
    have hsumR := congrArg (fun x : ℝ≥0 => (x : ℝ)) hsum
    simp only [NNReal.coe_add, NNReal.coe_mul, NNReal.coe_natCast] at hsumR
    change (s : ℝ) < (Δ : ℝ)
    nlinarith only [ht, hsumR]
  have htime : lam ^ 2 * (t : ℝ) < (j : ℝ) + 1 := by
    simpa only [hΔcoe, div_inv_eq_mul, mul_comm] using hupper
  have hmain := hbound Q lam h₀ h₁ P K hK hD A hA F G hF hG hFp hGp hzero s hs j
  rw [hsum] at hmain
  apply hmain.trans
  apply mul_le_mul_of_nonneg_right _ ENNReal.toReal_nonneg
  apply mul_le_mul_of_nonneg_right _ ENNReal.toReal_nonneg
  let N : ℝ := (max 1 ⌈(A / l + 4) / 10⌉₊ : ℕ) +
    (max 1 ⌈(A / l - 1) / 10⌉₊ : ℕ)
  change C * Real.exp (C * N - c * j) ≤
    D * Real.exp (D * N - c * lam ^ 2 * (t : ℝ))
  have hcycle : C * N ≤ D * N :=
    mul_le_mul_of_nonneg_right hCD (by positivity)
  calc
    C * Real.exp (C * N - c * j) ≤
        C * Real.exp (D * N - c * lam ^ 2 * (t : ℝ) + c) := by
      apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hC.le
      nlinarith only [hcycle, mul_lt_mul_of_pos_left htime hc]
    _ = (C * Real.exp c) * Real.exp (D * N - c * lam ^ 2 * (t : ℝ)) := by
      rw [Real.exp_add]
      ring
    _ ≤ D * Real.exp (D * N - c * lam ^ 2 * (t : ℝ)) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      dsimp only [D]
      linarith only [hC]

/-- Hölder bounds a literal event integral by an unrestricted higher moment.
The moment exponent is independent of the event's exponential rate. -/
theorem sbxS2_setIntegral_abs_le_moment {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (f : α → ℝ) (hf : AEStronglyMeasurable f μ)
    (s : Set α) (r H T : ℝ) (hr : 1 < r)
    (hi : Integrable (fun x => ‖f x‖ ^ r) μ)
    (hH : (∫ x, ‖f x‖ ^ r ∂μ) ≤ H)
    (hT₀ : 0 ≤ T) (hT : μ s ≤ ENNReal.ofReal T) :
    |∫ x in s, f x ∂μ| ≤ H ^ (1 / r) * T ^ (1 - 1 / r) := by
  have hr₀ : 0 < r := lt_trans zero_lt_one hr
  have hrE : (ENNReal.ofReal r) ≠ 0 := by positivity
  have hfr : MemLp f (ENNReal.ofReal r) μ := by
    apply (integrable_norm_rpow_iff hf hrE ENNReal.ofReal_ne_top).mp
    simpa only [ENNReal.toReal_ofReal hr₀.le] using hi
  have he : 0 ≤ 1 - 1 / r := by
    have := (div_le_one hr₀).mpr hr.le
    linarith
  have hb := eLpNorm_le_eLpNorm_mul_rpow_measure_univ
    (μ := μ.restrict s) (f := f)
    (show (1 : ℝ≥0∞) ≤ ENNReal.ofReal r by
      simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hr.le) hf.restrict
  simp only [ENNReal.toReal_one, ENNReal.toReal_ofReal hr₀.le, div_one,
    Measure.restrict_apply_univ] at hb
  have hnorm : eLpNorm f (ENNReal.ofReal r) μ ≤ ENNReal.ofReal (H ^ (1 / r)) := by
    rw [hfr.eLpNorm_eq_integral_rpow_norm hrE ENNReal.ofReal_ne_top]
    simp only [ENNReal.toReal_ofReal hr₀.le]
    apply ENNReal.ofReal_le_ofReal
    simpa only [one_div] using Real.rpow_le_rpow
      (integral_nonneg fun _ => by positivity) hH (inv_nonneg.mpr hr₀.le)
  have hbound : ‖∫ x in s, f x ∂μ‖ₑ ≤
      ENNReal.ofReal (H ^ (1 / r)) * (ENNReal.ofReal T) ^ (1 - 1 / r) := by
    calc
      _ ≤ eLpNorm f 1 (μ.restrict s) := by
        rw [eLpNorm_one_eq_lintegral_enorm hf.restrict]
        exact enorm_integral_le_lintegral_enorm f
      _ ≤ eLpNorm f (ENNReal.ofReal r) (μ.restrict s) * μ s ^ (1 - 1 / r) := hb
      _ ≤ eLpNorm f (ENNReal.ofReal r) μ * μ s ^ (1 - 1 / r) :=
        mul_le_mul_left (eLpNorm_mono_measure f Measure.restrict_le_self) _
      _ ≤ _ := mul_le_mul' hnorm (ENNReal.rpow_le_rpow hT he)
  have ht : (ENNReal.ofReal (H ^ (1 / r)) *
      (ENNReal.ofReal T) ^ (1 - 1 / r)) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.rpow_ne_top_of_nonneg he
      ENNReal.ofReal_ne_top)
  have hh := ENNReal.toReal_mono ht hbound
  have hH₀ : 0 ≤ H := (integral_nonneg fun _ => by positivity).trans hH
  simpa only [toReal_enorm, Real.norm_eq_abs, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (Real.rpow_nonneg hH₀ (1 / r)),
    ← ENNReal.toReal_rpow, ENNReal.toReal_ofReal hT₀] using hh

/-- Higher observable powers turn the fixed structural remainder estimate into
an unrestricted higher-moment estimate. The exponent is chosen after the
structural threshold, so its root can have arbitrarily small growth rate. -/
theorem sbxS2_covariance_power_moment_of_remainder
    (hrem : node_rt_u3A_remainder_u2D_momentStmt) :
    ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ),
    ∃ l₀ p C : ℝ, 0 < l₀ ∧ r₀ < 2 * l₀ ∧ 2 ≤ p ∧ 0 < C ∧
    ∀ (r : ℝ), 0 < r →
    ∀ (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
      (l δ : ℝ), l₀ ≤ l → 0 < δ → δ < 1 →
    ∀ (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
      (hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K)
      (hD : Regeneration.annealedCoupledLaw Q.measure K
        (regenerationNoReturn hd (l / lam)) ≠ 0),
    ∀ F G : FieldPair d → ℝ, Measurable F → Measurable G →
      MemLp F (ENNReal.ofReal (p * r)) (reducedLaw Q) →
      MemLp G (ENNReal.ofReal (p * r)) (reducedLaw Q) → ∀ t : ℝ≥0,
    ∀ μ ∈ ({Regeneration.annealedCoupledLaw Q.measure K,
      regenerationConditionedLaw hd Q lam l K hK.1 hD} :
        Set (Measure (FieldPair d × Regeneration.CoupledSample d))),
      Integrable (fun ωz => ‖F (reduce ωz.1) *
        G (translate (ωz.2.1 t) (reduce ωz.1))‖ ^ r) μ ∧
      (∫ ωz, ‖F (reduce ωz.1) *
        G (translate (ωz.2.1 t) (reduce ωz.1))‖ ^ r ∂μ) ≤
        C * Real.exp (C * lam ^ 2 * (t : ℝ)) *
          (eLpNorm F (ENNReal.ofReal (p * r)) (reducedLaw Q)).toReal ^ r *
          (eLpNorm G (ENNReal.ofReal (p * r)) (reducedLaw Q)).toReal ^ r := by
  intro d hd Λ₀ r₀
  obtain ⟨l₀, p, c, C, hl₀, hsep, hp, hc, hC, hrem'⟩ :=
    hrem d hd Λ₀ r₀ 1 1 (by norm_num) (by norm_num)
  refine ⟨l₀, p, C, hl₀, hsep, hp, hC, ?_⟩
  intro r hr Q lam h₀ h₁ l δ hl hδ₀ hδ₁ P K hK hD F G hF hG hFp hGp t μ hμ
  have hp₀ : 0 ≤ p := le_trans (by norm_num) hp
  have hpow (f : FieldPair d → ℝ)
      (hfp : MemLp f (ENNReal.ofReal (p * r)) (reducedLaw Q)) :
      MemLp (fun ω => ‖f ω‖ ^ r) (ENNReal.ofReal p) (reducedLaw Q) := by
    rw [memLp_iff, eLpNorm_norm_rpow f hfp.aestronglyMeasurable hr,
      ← ENNReal.ofReal_mul hp₀]
    exact ENNReal.rpow_lt_top_of_nonneg hr.le hfp.eLpNorm_ne_top
  have hnorm (f : FieldPair d → ℝ)
      (hfp : MemLp f (ENNReal.ofReal (p * r)) (reducedLaw Q)) :
      (eLpNorm (fun ω => ‖f ω‖ ^ r) (ENNReal.ofReal p) (reducedLaw Q)).toReal =
        (eLpNorm f (ENNReal.ofReal (p * r)) (reducedLaw Q)).toReal ^ r := by
    rw [eLpNorm_norm_rpow f hfp.aestronglyMeasurable hr,
      ← ENNReal.ofReal_mul hp₀, ENNReal.toReal_rpow]
  let : IsProbabilityMeasure (Regeneration.annealedCoupledLaw Q.measure K) :=
    Regeneration.annealedCoupledLaw_isProbabilityMeasure Q.measure K hK.1
  have hprob : Regeneration.annealedCoupledLaw Q.measure K Set.univ ≤
      ENNReal.ofReal (1 * Real.exp (1 * (lam ^ 2 * (t : ℝ)) -
        1 * lam ^ 2 * (t : ℝ))) := by simp
  have hmain := hrem' Q lam h₀ h₁ l δ hl hδ₀ hδ₁ P K hK hD
    (fun ω => ‖F ω‖ ^ r) (fun ω => ‖G ω‖ ^ r)
    (hF.norm.pow_const r) (hG.norm.pow_const r) (hpow F hFp) (hpow G hGp)
    (lam ^ 2 * (t : ℝ)) t Set.univ (by positivity) MeasurableSet.univ hprob μ hμ
  simp only [integrableOn_univ, Measure.restrict_univ, hnorm F hFp,
    hnorm G hGp] at hmain
  have hident : (fun ωz : FieldPair d × Regeneration.CoupledSample d =>
      ‖F (reduce ωz.1) * G (translate (ωz.2.1 t) (reduce ωz.1))‖ ^ r) =
      (fun ωz => ‖F (reduce ωz.1)‖ ^ r *
        ‖G (translate (ωz.2.1 t) (reduce ωz.1))‖ ^ r) := by
    funext ωz
    rw [norm_mul, Real.mul_rpow (norm_nonneg _) (norm_nonneg _)]
  rw [hident]
  refine ⟨hmain.1, ?_⟩
  have hnonneg : 0 ≤ ∫ ωz, ‖F (reduce ωz.1)‖ ^ r *
      ‖G (translate (ωz.2.1 t) (reduce ωz.1))‖ ^ r ∂μ :=
    integral_nonneg fun _ => by positivity
  rw [abs_of_nonneg hnonneg] at hmain
  apply hmain.2.trans
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hC.le
  have htime : 0 ≤ lam ^ 2 * (t : ℝ) := by positivity
  nlinarith only [mul_nonneg hc.le htime]

/-- Increasing a moment exponent absorbs any fixed growth rate into a later
positive event-decay rate. All constants are uniform in the event and time. -/
theorem sbxS2_power_interpolation_constants (D a : ℝ) (hD : 0 < D) (ha : 0 < a) :
    ∃ r c C : ℝ, 2 ≤ r ∧ 0 < c ∧ 0 < C ∧
    ∀ J u X Y : ℝ, 0 ≤ J → 0 ≤ u → 0 ≤ X → 0 ≤ Y →
      (D * Real.exp (D * u) * X ^ r * Y ^ r) ^ (1 / r) *
        (Real.exp (J - a * u)) ^ (1 - 1 / r) ≤
      C * Real.exp (C * J - c * u) * X * Y := by
  let r := 2 + 4 * D / a
  have hr : 2 ≤ r := by
    dsimp only [r]
    exact le_add_of_nonneg_right (by positivity)
  have hr₀ : 0 < r := lt_of_lt_of_le (by norm_num) hr
  have hinv : 0 < 1 / r := one_div_pos.mpr hr₀
  have hinv₂ : 1 / r ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hr
  have hgrowth : D * (1 / r) ≤ a / 4 := by
    rw [mul_one_div]
    apply (div_le_div_iff₀ hr₀ (by norm_num : (0 : ℝ) < 4)).mpr
    have heq : a * (4 * D / a) = 4 * D := by field_simp
    dsimp only [r]
    nlinarith only [ha, heq]
  let C := 1 + D ^ (1 / r)
  have hroot : 0 < D ^ (1 / r) := Real.rpow_pos_of_pos hD _
  have hC : 0 < C := by dsimp only [C]; positivity
  have hC₁ : 1 ≤ C := by dsimp only [C]; linarith only [hroot]
  refine ⟨r, a / 4, C, hr, by positivity, hC, ?_⟩
  intro J u X Y hJ hu hX hY
  have hXroot : (X ^ r) ^ (1 / r) = X := by
    rw [← Real.rpow_mul hX, mul_one_div_cancel hr₀.ne', Real.rpow_one]
  have hYroot : (Y ^ r) ^ (1 / r) = Y := by
    rw [← Real.rpow_mul hY, mul_one_div_cancel hr₀.ne', Real.rpow_one]
  have hexp : D * u * (1 / r) + (J - a * u) * (1 - 1 / r) ≤
      C * J - a / 4 * u := by
    have hJu := mul_le_mul_of_nonneg_left hinv₂ (mul_nonneg ha.le hu)
    have hDu := mul_le_mul_of_nonneg_right hgrowth hu
    have hJr := mul_nonneg hJ hinv.le
    have hCJ := mul_le_mul_of_nonneg_right hC₁ hJ
    nlinarith only [hJu, hDu, hJr, hCJ]
  calc
    _ = D ^ (1 / r) *
        Real.exp (D * u * (1 / r) + (J - a * u) * (1 - 1 / r)) * X * Y := by
      rw [Real.mul_rpow (by positivity) (Real.rpow_nonneg hY _),
        Real.mul_rpow (by positivity) (Real.rpow_nonneg hX _),
        Real.mul_rpow hD.le (Real.exp_pos _).le, hXroot, hYroot,
        ← Real.exp_mul, ← Real.exp_mul, Real.exp_add]
      ring
    _ ≤ C * Real.exp (C * J - a / 4 * u) * X * Y := by
      apply mul_le_mul_of_nonneg_right _ hY
      apply mul_le_mul_of_nonneg_right _ hX
      exact mul_le_mul (by dsimp only [C]; linarith only [hroot])
        (Real.exp_le_exp.mpr hexp) (Real.exp_pos _).le hC.le

/-- For the annealed law, a single structural threshold suffices for every
later positive event-tail rate. Higher observable integrability compensates for
the rate without interchanging the threshold and rate quantifiers. -/
theorem sbxS2_remainder_moment_variable_rate
    (hrem : node_rt_u3A_remainder_u2D_momentStmt) :
    ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ),
    ∃ l₀ : ℝ, 0 < l₀ ∧ r₀ < 2 * l₀ ∧
    ∀ a : ℝ, 0 < a → ∃ p c C : ℝ, 2 ≤ p ∧ 0 < c ∧ 0 < C ∧
    ∀ (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
      (l δ : ℝ), l₀ ≤ l → 0 < δ → δ < 1 →
    ∀ (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
      (_hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K)
      (_hD : Regeneration.annealedCoupledLaw Q.measure K
        (regenerationNoReturn hd (l / lam)) ≠ 0),
    ∀ F G : FieldPair d → ℝ, Measurable F → Measurable G →
      MemLp F (ENNReal.ofReal p) (reducedLaw Q) →
      MemLp G (ENNReal.ofReal p) (reducedLaw Q) →
    ∀ (J : ℝ) (t : ℝ≥0) (E : Set (FieldPair d × Regeneration.CoupledSample d)),
      0 ≤ J → Regeneration.annealedCoupledLaw Q.measure K E ≤
        ENNReal.ofReal (Real.exp (J - a * lam ^ 2 * (t : ℝ))) →
      IntegrableOn (fun ωz => F (reduce ωz.1) *
        G (translate (ωz.2.1 t) (reduce ωz.1))) E
        (Regeneration.annealedCoupledLaw Q.measure K) ∧
      |∫ ωz in E, F (reduce ωz.1) *
        G (translate (ωz.2.1 t) (reduce ωz.1))
          ∂Regeneration.annealedCoupledLaw Q.measure K| ≤
        C * Real.exp (C * J - c * lam ^ 2 * (t : ℝ)) *
          (eLpNorm F (ENNReal.ofReal p) (reducedLaw Q)).toReal *
          (eLpNorm G (ENNReal.ofReal p) (reducedLaw Q)).toReal := by
  intro d hd Λ₀ r₀
  obtain ⟨l₀, p₀, D, hl₀, hsep, hp₀, hDpos, hmoment⟩ :=
    sbxS2_covariance_power_moment_of_remainder hrem d hd Λ₀ r₀
  refine ⟨l₀, hl₀, hsep, ?_⟩
  intro a ha
  obtain ⟨r, c, C, hr, hc, hC, hscalar⟩ :=
    sbxS2_power_interpolation_constants D a hDpos ha
  have hr₁ : 1 < r := lt_of_lt_of_le (by norm_num) hr
  have hr₀ : 0 < r := lt_trans zero_lt_one hr₁
  have hp₀pos : 0 ≤ p₀ := le_trans (by norm_num) hp₀
  refine ⟨p₀ * r, c, C, ?_, hc, hC, ?_⟩
  · exact hp₀.trans (le_mul_of_one_le_right hp₀pos hr₁.le)
  intro Q lam h₀ h₁ l δ hl hδ₀ hδ₁ P K hK hD F G hF hG hFp hGp J t E hJ hprob
  let μ := Regeneration.annealedCoupledLaw Q.measure K
  let f := fun ωz : FieldPair d × Regeneration.CoupledSample d =>
    F (reduce ωz.1) * G (translate (ωz.2.1 t) (reduce ωz.1))
  have hfm : Measurable f :=
    ((hF.comp Probability.measurable_reduce).comp measurable_fst).mul
      (hG.comp (Probability.continuous_translate.measurable.comp
        (((continuous_eval_const t).measurable.comp measurable_snd.fst).prodMk
          (Probability.measurable_reduce.comp measurable_fst))))
  have hpower := hmoment r hr₀ Q lam h₀ h₁ l δ hl hδ₀ hδ₁ P K hK hD
    F G hF hG hFp hGp t μ (Set.mem_insert _ _)
  let : IsProbabilityMeasure μ :=
    Regeneration.annealedCoupledLaw_isProbabilityMeasure Q.measure K hK.1
  have hfr : MemLp f (ENNReal.ofReal r) μ := by
    apply (integrable_norm_rpow_iff hfm.aestronglyMeasurable (by positivity)
      ENNReal.ofReal_ne_top).mp
    simpa only [ENNReal.toReal_ofReal hr₀.le] using hpower.1
  refine ⟨(MemLp.integrable (q := ENNReal.ofReal r) ?_ hfr).integrableOn, ?_⟩
  · simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hr₁.le
  have hb := sbxS2_setIntegral_abs_le_moment μ f hfm.aestronglyMeasurable E r
    (D * Real.exp (D * lam ^ 2 * (t : ℝ)) *
      (eLpNorm F (ENNReal.ofReal (p₀ * r)) (reducedLaw Q)).toReal ^ r *
      (eLpNorm G (ENNReal.ofReal (p₀ * r)) (reducedLaw Q)).toReal ^ r)
    (Real.exp (J - a * lam ^ 2 * (t : ℝ))) hr₁ hpower.1 hpower.2
    (Real.exp_pos _).le hprob
  apply hb.trans
  simpa only [mul_assoc] using hscalar J (lam ^ 2 * (t : ℝ))
    (eLpNorm F (ENNReal.ofReal (p₀ * r)) (reducedLaw Q)).toReal
    (eLpNorm G (ENNReal.ofReal (p₀ * r)) (reducedLaw Q)).toReal
    hJ (by positivity) ENNReal.toReal_nonneg ENNReal.toReal_nonneg

/-- The actual early-regeneration remainder decays with a structural threshold.
The observable exponent is selected after the many-cycle tail rate, rather than
using that rate to choose a new structural threshold. -/
theorem sbxS2_regeneration_remainder_decay_of_deps
    (hmany : node_rt_u3A_many_u2D_cycle_u2D_momentStmt)
    (hrem : node_rt_u3A_remainder_u2D_momentStmt) :
    ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ),
    ∃ l₀ : ℝ, 0 < l₀ ∧ r₀ < 2 * l₀ ∧
    ∀ l : ℝ, l₀ ≤ l → ∀ δ : ℝ, 0 < δ → δ < 1 →
    ∃ p c C : ℝ, 2 ≤ p ∧ 0 < c ∧ 0 < C ∧
    ∀ (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
      (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
      (_hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K)
      (_hD : Regeneration.annealedCoupledLaw Q.measure K
        (regenerationNoReturn hd (l / lam)) ≠ 0),
    ∀ F G : FieldPair d → ℝ, Measurable F → Measurable G →
      MemLp F (ENNReal.ofReal p) (reducedLaw Q) →
      MemLp G (ENNReal.ofReal p) (reducedLaw Q) → ∀ j : ℕ, 1 ≤ j → ∀ t : ℝ≥0,
      IntegrableOn (fun ωz => F (reduce ωz.1) *
        G (translate (ωz.2.1 t) (reduce ωz.1)))
        {ωz | (t : ℝ≥0∞) < regenerationTime hd lam l j ωz.2}
        (Regeneration.annealedCoupledLaw Q.measure K) ∧
      |∫ ωz in {ωz | (t : ℝ≥0∞) < regenerationTime hd lam l j ωz.2},
        F (reduce ωz.1) * G (translate (ωz.2.1 t) (reduce ωz.1))
          ∂Regeneration.annealedCoupledLaw Q.measure K| ≤
        C * Real.exp (C * j - c * lam ^ 2 * (t : ℝ)) *
          (eLpNorm F (ENNReal.ofReal p) (reducedLaw Q)).toReal *
          (eLpNorm G (ENNReal.ofReal p) (reducedLaw Q)).toReal := by
  intro d hd Λ₀ r₀
  obtain ⟨lR, hlR, hsep, hrate⟩ := sbxS2_remainder_moment_variable_rate hrem d hd Λ₀ r₀
  obtain ⟨lM, hlM, _hsepM, hmoment⟩ := hmany d hd Λ₀ r₀
  refine ⟨max lR lM, lt_of_lt_of_le hlR (le_max_left _ _),
    hsep.trans_le (mul_le_mul_of_nonneg_left (le_max_left _ _) (by norm_num)), ?_⟩
  intro l hl δ hδ₀ hδ₁
  have hlR' := (le_max_left lR lM).trans hl
  have hlM' := (le_max_right lR lM).trans hl
  obtain ⟨a, M, S, ha, hM, hS, hm⟩ := hmoment l hlM' δ hδ₀ hδ₁
  obtain ⟨p, c, C, hp, hc, hC, hbound⟩ := hrate a ha
  let D := 1 + C + C * (S + M)
  have hDpos : 0 < D := by dsimp only [D]; positivity
  have hCD : C ≤ D := by dsimp only [D]; nlinarith only [mul_pos hC (add_pos hS hM)]
  have hcycle : C * (S + M) ≤ D := by dsimp only [D]; linarith only [hC]
  refine ⟨p, c, D, hp, hc, hDpos, ?_⟩
  intro Q lam h₀ h₁ P K hK hD F G hF hG hFp hGp j hj t
  let μ := Regeneration.annealedCoupledLaw Q.measure K
  let J := (S + M) * (j : ℝ)
  have hJ : 0 ≤ J := by dsimp only [J]; positivity
  have hj' : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hgeom : S * M ^ j ≤ Real.exp J := by
    have hself : S ≤ Real.exp S := by linarith only [Real.add_one_le_exp S]
    have hSp : S ≤ Real.exp (S * j) :=
      hself.trans (Real.exp_le_exp.mpr (by nlinarith only [hS.le, hj']))
    have hMp : M ≤ Real.exp M := by linarith only [Real.add_one_le_exp M]
    calc
      _ ≤ Real.exp (S * j) * Real.exp M ^ j :=
        mul_le_mul hSp (pow_le_pow_left₀ hM.le hMp j)
          (pow_nonneg hM.le j) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; dsimp only [J]; ring
  have htail : μ {ωz | (t : ℝ≥0∞) < regenerationTime hd lam l j ωz.2} ≤
      ENNReal.ofReal (Real.exp (J - a * lam ^ 2 * (t : ℝ))) := by
    have hm' := ((hm Q lam h₀ h₁ P K hK hD).2 j).trans
      (ENNReal.ofReal_le_ofReal hgeom)
    have ht := exponential_time_tail μ
      (fun ωz : FieldPair d × Regeneration.CoupledSample d =>
        regenerationTime hd lam l j ωz.2)
      ((Regeneration.measurable_regenerationTime _ _ _ _ _).comp measurable_snd)
      (a * lam ^ 2) (Real.exp J) (by positivity) t hm'
    simpa only [← Real.exp_add, neg_mul, sub_eq_add_neg] using ht
  have hb := hbound Q lam h₀ h₁ l δ hlR' hδ₀ hδ₁ P K hK hD
    F G hF hG hFp hGp J t _ hJ htail
  refine ⟨hb.1, hb.2.trans ?_⟩
  apply mul_le_mul_of_nonneg_right _ ENNReal.toReal_nonneg
  apply mul_le_mul_of_nonneg_right _ ENNReal.toReal_nonneg
  apply mul_le_mul hCD (Real.exp_le_exp.mpr ?_) (Real.exp_pos _).le hDpos.le
  dsimp only [J]
  nlinarith only [mul_le_mul_of_nonneg_right hcycle (Nat.cast_nonneg j : (0 : ℝ) ≤ j)]

/-- Increasing the growth constant and observable bounds, or decreasing the
positive decay rate, preserves the exponential product estimate. -/
theorem sbxS2_exp_decay_product_mono (C D c e N t X Y U V : ℝ)
    (hC : 0 ≤ C) (hCD : C ≤ D) (hec : e ≤ c) (hN : 0 ≤ N) (ht : 0 ≤ t)
    (hX : 0 ≤ X) (hY : 0 ≤ Y) (hXU : X ≤ U) (hYV : Y ≤ V) :
    C * Real.exp (C * N - c * t) * X * Y ≤
      C * Real.exp (D * N - e * t) * U * V := by
  have he : C * N - c * t ≤ D * N - e * t :=
    sub_le_sub (mul_le_mul_of_nonneg_right hCD hN)
      (mul_le_mul_of_nonneg_right hec ht)
  have hU : 0 ≤ U := hX.trans hXU
  calc
    _ ≤ C * Real.exp (D * N - e * t) * X * Y := by
      gcongr
    _ ≤ C * Real.exp (D * N - e * t) * U * V := by
      gcongr

/-- The actual regeneration remainder and covariance obey common continuous-time
bounds. All constants precede the law, force, coupling and observables. -/
theorem sbxS2_covariance_and_remainder_decay_of_deps
    (hfactor : node_rt_u3A_k_u2D_factorStmt)
    (hphase : node_rt_u3A_local_u2D_mixing_u23_phase_u2D_errorStmt)
    (hmany : node_rt_u3A_many_u2D_cycle_u2D_momentStmt)
    (hrem : node_rt_u3A_remainder_u2D_momentStmt) :
    ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ),
    ∃ l₀ : ℝ, 0 < l₀ ∧ r₀ < 2 * l₀ ∧
    ∀ l : ℝ, l₀ ≤ l → ∀ δ : ℝ, 0 < δ → δ < 1 →
    ∃ p c C : ℝ, 2 ≤ p ∧ 0 < c ∧ 0 < C ∧
    ∀ (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
      (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
      (_hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K)
      (_hD : Regeneration.annealedCoupledLaw Q.measure K
        (regenerationNoReturn hd (l / lam)) ≠ 0)
      (A : ℝ), l ≤ A → ∀ F G : FieldPair d → ℝ,
    Measurable[localSigma {x : Vec d | euclideanNorm x < A / lam}] F →
    Measurable[localSigma {x : Vec d | euclideanNorm x < A / lam}] G →
    MemLp F (ENNReal.ofReal p) (reducedLaw Q) →
    MemLp G (ENNReal.ofReal p) (reducedLaw Q) →
    (∫ ω, F ω ∂reducedLaw Q) = 0 →
    let k : ℕ := max 1 ⌈(A / l + 4) / 10⌉₊
    let m : ℕ := max 1 ⌈(A / l - 1) / 10⌉₊
    let μ := Regeneration.annealedCoupledLaw Q.measure K
    let cov := fun t : ℝ≥0 => ∫ ωz, F (reduce ωz.1) *
      G (translate (ωz.2.1 t) (reduce ωz.1)) ∂μ
    let rem := fun t : ℝ≥0 => ∫ ωz in {ωz | (t : ℝ≥0∞) <
      regenerationTime hd lam l (k + m) ωz.2}, F (reduce ωz.1) *
        G (translate (ωz.2.1 t) (reduce ωz.1)) ∂μ
    ∀ t : ℝ≥0,
      (|rem t| ≤
      C * Real.exp (C * (k + m) - c * lam ^ 2 * (t : ℝ)) *
        (eLpNorm F (ENNReal.ofReal p) (reducedLaw Q)).toReal *
        (eLpNorm G (ENNReal.ofReal p) (reducedLaw Q)).toReal) ∧
      |cov t| ≤ C * Real.exp (C * (k + m) - c * lam ^ 2 * (t : ℝ)) *
        (eLpNorm F (ENNReal.ofReal p) (reducedLaw Q)).toReal *
        (eLpNorm G (ENNReal.ofReal p) (reducedLaw Q)).toReal := by
  intro d hd Λ₀ r₀
  obtain ⟨lD, hlD, hsepD, hdec⟩ :=
    sbxS2_covariance_sub_remainder_time_decay_of_deps hfactor hphase hmany hrem d hd Λ₀ r₀
  obtain ⟨lR, _hlR, _hsepR, hremdec⟩ :=
    sbxS2_regeneration_remainder_decay_of_deps hmany hrem d hd Λ₀ r₀
  refine ⟨max lD lR, hlD.trans_le (le_max_left _ _),
    hsepD.trans_le (by linarith only [le_max_left lD lR]), ?_⟩
  intro l hl δ hδ₀ hδ₁
  obtain ⟨pD, cD, CD, hpD, hcD, hCD, hboundD⟩ :=
    hdec l ((le_max_left _ _).trans hl) δ hδ₀ hδ₁
  obtain ⟨pR, cR, CR, _hpR, hcR, hCR, hboundR⟩ :=
    hremdec l ((le_max_right _ _).trans hl) δ hδ₀ hδ₁
  let p := max pD pR
  let c := min cD cR
  let C := 1 + CD + CR
  have hC : 0 < C := by dsimp only [C]; positivity
  have hDC : CD ≤ C := by dsimp only [C]; linarith only [hCR]
  have hRC : CR ≤ C := by dsimp only [C]; linarith only [hCD]
  refine ⟨p, c, C, hpD.trans (le_max_left _ _), lt_min hcD hcR, hC, ?_⟩
  intro Q lam h₀ h₁ P K hK hD A hA F G hF hG hFp hGp hzero
  let := reducedLaw_probability Q
  dsimp only
  let k : ℕ := max 1 ⌈(A / l + 4) / 10⌉₊
  let m : ℕ := max 1 ⌈(A / l - 1) / 10⌉₊
  let μ := Regeneration.annealedCoupledLaw Q.measure K
  let cov := fun t : ℝ≥0 => ∫ ωz, F (reduce ωz.1) *
    G (translate (ωz.2.1 t) (reduce ωz.1)) ∂μ
  let rem := fun t : ℝ≥0 => ∫ ωz in {ωz | (t : ℝ≥0∞) <
    regenerationTime hd lam l (k + m) ωz.2}, F (reduce ωz.1) *
      G (translate (ωz.2.1 t) (reduce ωz.1)) ∂μ
  let Nf := (eLpNorm F (ENNReal.ofReal p) (reducedLaw Q)).toReal
  let Ng := (eLpNorm G (ENNReal.ofReal p) (reducedLaw Q)).toReal
  have hpD' : ENNReal.ofReal pD ≤ ENNReal.ofReal p :=
    ENNReal.ofReal_le_ofReal (le_max_left _ _)
  have hpR' : ENNReal.ofReal pR ≤ ENNReal.ofReal p :=
    ENNReal.ofReal_le_ofReal (le_max_right _ _)
  have hnormF (q : ℝ) (hq : ENNReal.ofReal q ≤ ENNReal.ofReal p) :
      (eLpNorm F (ENNReal.ofReal q) (reducedLaw Q)).toReal ≤ Nf :=
    ENNReal.toReal_mono hFp.eLpNorm_ne_top (eLpNorm_le_eLpNorm_of_exponent_le hq)
  have hnormG (q : ℝ) (hq : ENNReal.ofReal q ≤ ENNReal.ofReal p) :
      (eLpNorm G (ENNReal.ofReal q) (reducedLaw Q)).toReal ≤ Ng :=
    ENNReal.toReal_mono hGp.eLpNorm_ne_top (eLpNorm_le_eLpNorm_of_exponent_le hq)
  have hbD := hboundD Q lam h₀ h₁ P K hK hD A hA F G hF hG
    (hFp.mono_exponent hpD') (hGp.mono_exponent hpD') hzero
  have hbR := hboundR Q lam h₀ h₁ P K hK hD F G
    (hF.mono (Probability.localSigma_le_borel _) le_rfl)
    (hG.mono (Probability.localSigma_le_borel _) le_rfl)
    (hFp.mono_exponent hpR') (hGp.mono_exponent hpR') (k + m)
    (by dsimp only [k, m]; omega)
  intro t
  let E := Real.exp (C * (k + m) - c * lam ^ 2 * (t : ℝ))
  have hdiff : |cov t - rem t| ≤ CD * E * Nf * Ng := by
    apply (hbD t).trans
    simpa only [E, mul_assoc, Nat.cast_add] using sbxS2_exp_decay_product_mono CD C cD c
      (k + m) (lam ^ 2 * (t : ℝ)) _ _ Nf Ng hCD.le hDC (min_le_left _ _)
      (by positivity) (by positivity) ENNReal.toReal_nonneg ENNReal.toReal_nonneg
      (hnormF _ hpD') (hnormG _ hpD')
  have hrest : |rem t| ≤ CR * E * Nf * Ng := by
    apply (hbR t).2.trans
    simpa only [E, mul_assoc, Nat.cast_add] using sbxS2_exp_decay_product_mono CR C cR c
      (k + m) (lam ^ 2 * (t : ℝ)) _ _ Nf Ng hCR.le hRC (min_le_right _ _)
      (by positivity) (by positivity) ENNReal.toReal_nonneg ENNReal.toReal_nonneg
      (hnormF _ hpR') (hnormG _ hpR')
  have hE : 0 ≤ E := (Real.exp_pos _).le
  refine ⟨hrest.trans ?_, ?_⟩
  · change CR * E * Nf * Ng ≤ C * E * Nf * Ng
    gcongr
  · calc
      |cov t| = |(cov t - rem t) + rem t| := by congr 1; ring
      _ ≤ |cov t - rem t| + |rem t| := abs_add_le _ _
      _ ≤ CD * E * Nf * Ng + CR * E * Nf * Ng := add_le_add hdiff hrest
      _ = (CD + CR) * E * Nf * Ng := by ring
      _ ≤ C * E * Nf * Ng := by
        have hsum : CD + CR ≤ C := by dsimp only [C]; linarith
        gcongr

/-- The complete positive-force regeneration conjunction of `rt:km-decomp`,
with a single exponent, rate, constant and structural threshold. This support
result does not assert the signed-force environment-semigroup conjunct. -/
theorem sbxS2_positive_km_decomp_of_deps
    (hfactor : node_rt_u3A_k_u2D_factorStmt)
    (hphase : node_rt_u3A_local_u2D_mixing_u23_phase_u2D_errorStmt)
    (hmany : node_rt_u3A_many_u2D_cycle_u2D_momentStmt)
    (hrem : node_rt_u3A_remainder_u2D_momentStmt) :
  ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ),
    ∃ l₀ : ℝ, 0 < l₀ ∧ r₀ < 2 * l₀ ∧
    ∀ l : ℝ, l₀ ≤ l → ∀ δ : ℝ, 0 < δ → δ < 1 →
    ∃ p c C lam₀ : ℝ, 2 ≤ p ∧ 0 < c ∧ 0 < C ∧ 0 < lam₀ ∧ lam₀ ≤ 1 ∧
    ∀ Q : EnvironmentLaw d Λ₀ r₀,
    ∀ (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1), lam ≤ lam₀ →
      ∀ (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
        (hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K)
        (hD : Regeneration.annealedCoupledLaw Q.measure K
          (regenerationNoReturn hd (l / lam)) ≠ 0),
      ∀ A : ℝ, l ≤ A → ∀ F G : FieldPair d → ℝ,
      Measurable[localSigma {x : Vec d | euclideanNorm x < A / lam}] F →
      Measurable[localSigma {x : Vec d | euclideanNorm x < A / lam}] G →
      MemLp F (ENNReal.ofReal p) (reducedLaw Q) →
      MemLp G (ENNReal.ofReal p) (reducedLaw Q) →
      (∫ ω, F ω ∂reducedLaw Q) = 0 →
      let k : ℕ := max 1 ⌈(A / l + 4) / 10⌉₊
      let m : ℕ := max 1 ⌈(A / l - 1) / 10⌉₊
      let μ := Regeneration.annealedCoupledLaw Q.measure K
      let ν := regenerationConditionedLaw hd Q lam l K hK.1 hD
      let Δ := Regeneration.Renewal.regenDelta lam
      let pn := regenerationLatticeMass hd Q lam l K hK.1 hD
      let mean := ∑' n : ℕ, (n : ℝ) * pn n
      let q := fun n : ℕ => ∫ ωz in {ωz | regenerationTime hd lam l k ωz.2 =
        (((n : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞)}, F (reduce ωz.1) ∂μ
      let hm := fun t : ℝ≥0 => ∫ ωz in {ωz |
        regenerationTime hd lam l m ωz.2 ≤ (t : ℝ≥0∞)},
        G (translate (ωz.2.1 t) (reduce ωz.1)) ∂ν
      let rm := fun t : ℝ≥0 => ∫ ωz in {ωz |
        regenerationTime hd lam l m ωz.2 ≤ (t : ℝ≥0∞) ∧
        (t : ℝ≥0∞) < regenerationTime hd lam l (m + 1) ωz.2},
        G (translate (ωz.2.1 t) (reduce ωz.1)) ∂ν
      let Hm := fun s : ℝ≥0 => mean⁻¹ * ∑' j : ℕ, rm (s + j * Δ)
      let cov := fun t : ℝ≥0 => ∫ ωz, F (reduce ωz.1) *
        G (translate (ωz.2.1 t) (reduce ωz.1)) ∂μ
      let rem := fun t : ℝ≥0 => ∫ ωz in {ωz | (t : ℝ≥0∞) <
        regenerationTime hd lam l (k + m) ωz.2}, F (reduce ωz.1) *
          G (translate (ωz.2.1 t) (reduce ωz.1)) ∂μ
      let Nf := (eLpNorm F (ENNReal.ofReal p) (reducedLaw Q)).toReal
      let Ng := (eLpNorm G (ENNReal.ofReal p) (reducedLaw Q)).toReal
      (k + m : ℝ) ≤ C * (1 + A) ∧
      Summable q ∧ (∑' n, q n) = 0 ∧
      (∀ n : ℕ, |q n| ≤ C * Real.exp (C * k - c * n) * Nf) ∧
      (∀ t : ℝ≥0,
        Integrable (fun ωz => F (reduce ωz.1) *
          G (translate (ωz.2.1 t) (reduce ωz.1))) μ ∧
        cov t = rem t + ∑ n ∈ Finset.range (⌊(t : ℝ) / (Δ : ℝ)⌋₊ + 1),
          q n * hm (t - n * Δ) ∧
        |rem t| ≤ C * Real.exp (C * (k + m) - c * lam ^ 2 * (t : ℝ)) * Nf * Ng ∧
        |cov t| ≤ C * Real.exp (C * (k + m) - c * lam ^ 2 * (t : ℝ)) * Nf * Ng) ∧
      ∀ s : ℝ≥0, s < Δ → ∀ j : ℕ,
        cov (s + j * Δ) = rem (s + j * Δ) +
          (∑ n ∈ Finset.range (j + 1), q n * (hm (s + (j - n) * Δ) - Hm s)) -
          Hm s * ∑' n : ℕ, q (j + 1 + n) := by
  intro d hd Λ₀ r₀
  obtain ⟨lA, pA, hlA, hsepA, hpA, halgebra⟩ :=
    sbxS2_centered_covariance_of_deps hfactor hmany hrem d hd Λ₀ r₀
  obtain ⟨lQ, _hlQ, _hsepQ, hslice⟩ :=
    sbxS2_slice_decay_normalized_of_manyCycleMoment hmany d hd Λ₀ r₀
  obtain ⟨lB, _hlB, _hsepB, hdecay⟩ :=
    sbxS2_covariance_and_remainder_decay_of_deps hfactor hphase hmany hrem d hd Λ₀ r₀
  refine ⟨max lA (max lQ lB), hlA.trans_le (le_max_left _ _),
    hsepA.trans_le (by linarith only [le_max_left lA (max lQ lB)]), ?_⟩
  intro l hl δ hδ₀ hδ₁
  have hlA' : lA ≤ l := (le_max_left _ _).trans hl
  have hlQ' : lQ ≤ l := (le_max_left _ _).trans ((le_max_right _ _).trans hl)
  have hlB' : lB ≤ l := (le_max_right _ _).trans ((le_max_right _ _).trans hl)
  have hlpos : 0 < l := hlA.trans_le hlA'
  obtain ⟨cQ, CQ, hcQ, hCQ, hq⟩ := hslice l hlQ' δ hδ₀ hδ₁
  obtain ⟨pB, cB, CB, _hpB, hcB, hCB, hb⟩ := hdecay l hlB' δ hδ₀ hδ₁
  let p := max pA pB
  let c := min cQ cB
  let C := 1 + CQ + CB + (4 + 1 / l)
  have hcyclepos : 0 < 4 + 1 / l := by positivity
  have hC : 0 < C := by dsimp only [C]; positivity
  have hQC : CQ ≤ C := by dsimp only [C]; linarith only [hCB, hcyclepos]
  have hBC : CB ≤ C := by dsimp only [C]; linarith only [hCQ, hcyclepos]
  have hcycleC : 4 + 1 / l ≤ C := by dsimp only [C]; linarith only [hCQ, hCB]
  have hp : 2 ≤ p := hpA.trans (le_max_left _ _)
  refine ⟨p, c, C, 1, hp, lt_min hcQ hcB, hC, by norm_num, le_rfl, ?_⟩
  intro Q lam h₀ h₁ _hlam P K hK hD A hA F G hF hG hFp hGp hzero
  let := reducedLaw_probability Q
  dsimp only
  let k : ℕ := max 1 ⌈(A / l + 4) / 10⌉₊
  let m : ℕ := max 1 ⌈(A / l - 1) / 10⌉₊
  let Nf := (eLpNorm F (ENNReal.ofReal p) (reducedLaw Q)).toReal
  let Ng := (eLpNorm G (ENNReal.ofReal p) (reducedLaw Q)).toReal
  have hpA' : ENNReal.ofReal pA ≤ ENNReal.ofReal p :=
    ENNReal.ofReal_le_ofReal (le_max_left _ _)
  have hpB' : ENNReal.ofReal pB ≤ ENNReal.ofReal p :=
    ENNReal.ofReal_le_ofReal (le_max_right _ _)
  have hNf : (eLpNorm F (ENNReal.ofReal pB) (reducedLaw Q)).toReal ≤ Nf :=
    ENNReal.toReal_mono hFp.eLpNorm_ne_top (eLpNorm_le_eLpNorm_of_exponent_le hpB')
  have hNg : (eLpNorm G (ENNReal.ofReal pB) (reducedLaw Q)).toReal ≤ Ng :=
    ENNReal.toReal_mono hGp.eLpNorm_ne_top (eLpNorm_le_eLpNorm_of_exponent_le hpB')
  have ha := halgebra l δ hlA' hδ₀ hδ₁ Q lam h₀ h₁ P K hK hD A hA F G hF hG
    (hFp.mono_exponent hpA') (hGp.mono_exponent hpA') hzero
  have hdcy := hb Q lam h₀ h₁ P K hK hD A hA F G hF hG
    (hFp.mono_exponent hpB') (hGp.mono_exponent hpB') hzero
  refine ⟨?_, ha.1, ha.2.1, ?_, ?_, ha.2.2.2⟩
  · apply (sbxS2_prescribed_cycles_le l A hlpos hA).trans
    exact mul_le_mul_of_nonneg_right hcycleC (by linarith only [hlpos, hA])
  · intro n
    have hs := hq Q lam h₀ h₁ P K hK hD p hp F
      (hF.mono (Probability.localSigma_le_borel _) le_rfl) hFp k
      (le_max_left _ _) n
    apply hs.trans
    have he : CQ * (k : ℝ) - cQ * n ≤ C * (k : ℝ) - c * n :=
      sub_le_sub (mul_le_mul_of_nonneg_right hQC (Nat.cast_nonneg _))
        (mul_le_mul_of_nonneg_right (min_le_left _ _) (Nat.cast_nonneg _))
    apply mul_le_mul_of_nonneg_right _ ENNReal.toReal_nonneg
    exact mul_le_mul hQC (Real.exp_le_exp.mpr he) (Real.exp_pos _).le hC.le
  · intro t
    refine ⟨(ha.2.2.1 t).1, (ha.2.2.1 t).2, ?_, ?_⟩
    · apply (hdcy t).1.trans
      calc
        _ ≤ CB * Real.exp (C * (k + m) - c * lam ^ 2 * (t : ℝ)) * Nf * Ng := by
          simpa only [mul_assoc] using sbxS2_exp_decay_product_mono CB C cB c
            ((k : ℝ) + m) (lam ^ 2 * (t : ℝ)) _ _ Nf Ng hCB.le hBC
            (min_le_right _ _) (by positivity) (by positivity)
            ENNReal.toReal_nonneg ENNReal.toReal_nonneg hNf hNg
        _ ≤ C * Real.exp (C * (k + m) - c * lam ^ 2 * (t : ℝ)) * Nf * Ng := by
          gcongr
    · apply (hdcy t).2.trans
      calc
        _ ≤ CB * Real.exp (C * (k + m) - c * lam ^ 2 * (t : ℝ)) * Nf * Ng := by
          simpa only [mul_assoc] using sbxS2_exp_decay_product_mono CB C cB c
            ((k : ℝ) + m) (lam ^ 2 * (t : ℝ)) _ _ Nf Ng hCB.le hBC
            (min_le_right _ _) (by positivity) (by positivity)
            ENNReal.toReal_nonneg ENNReal.toReal_nonneg hNf hNg
        _ ≤ C * Real.exp (C * (k + m) - c * lam ^ 2 * (t : ℝ)) * Nf * Ng := by
          gcongr

/-- The actual positive-force path covariance has the spatial-radius growth
factor appearing in the final mixing estimate. -/
theorem sbxS2_covariance_radius_decay_of_deps
    (hfactor : node_rt_u3A_k_u2D_factorStmt)
    (hphase : node_rt_u3A_local_u2D_mixing_u23_phase_u2D_errorStmt)
    (hmany : node_rt_u3A_many_u2D_cycle_u2D_momentStmt)
    (hrem : node_rt_u3A_remainder_u2D_momentStmt) :
    ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ),
    ∃ l₀ : ℝ, 0 < l₀ ∧ r₀ < 2 * l₀ ∧
    ∀ l : ℝ, l₀ ≤ l → ∀ δ : ℝ, 0 < δ → δ < 1 →
    ∃ p c C : ℝ, 2 ≤ p ∧ 0 < c ∧ 0 < C ∧
    ∀ (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
      (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
      (_hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K)
      (_hD : Regeneration.annealedCoupledLaw Q.measure K
        (regenerationNoReturn hd (l / lam)) ≠ 0)
      (A : ℝ), l ≤ A → ∀ F G : FieldPair d → ℝ,
    Measurable[localSigma {x : Vec d | euclideanNorm x < A / lam}] F →
    Measurable[localSigma {x : Vec d | euclideanNorm x < A / lam}] G →
    MemLp F (ENNReal.ofReal p) (reducedLaw Q) →
    MemLp G (ENNReal.ofReal p) (reducedLaw Q) →
    (∫ ω, F ω ∂reducedLaw Q) = 0 →
    let μ := Regeneration.annealedCoupledLaw Q.measure K
    let cov := fun t : ℝ≥0 => ∫ ωz, F (reduce ωz.1) *
      G (translate (ωz.2.1 t) (reduce ωz.1)) ∂μ
    ∀ t : ℝ≥0, |cov t| ≤
      C * Real.exp (C * A - c * lam ^ 2 * (t : ℝ)) *
        (eLpNorm F (ENNReal.ofReal p) (reducedLaw Q)).toReal *
        (eLpNorm G (ENNReal.ofReal p) (reducedLaw Q)).toReal := by
  intro d hd Λ₀ r₀
  obtain ⟨l₀, hl₀, hsep, hdecay⟩ :=
    sbxS2_covariance_and_remainder_decay_of_deps hfactor hphase hmany hrem d hd Λ₀ r₀
  refine ⟨l₀, hl₀, hsep, ?_⟩
  intro l hl δ hδ₀ hδ₁
  have hlpos : 0 < l := hl₀.trans_le hl
  obtain ⟨p, c, C, hp, hc, hC, hb⟩ := hdecay l hl δ hδ₀ hδ₁
  let D := 1 + C + C * (4 + 1 / l) * (1 + 1 / l)
  have hD : 0 < D := by dsimp only [D]; positivity
  have hCD : C ≤ D := by
    dsimp only [D]
    have : 0 < C * (4 + 1 / l) * (1 + 1 / l) := by positivity
    linarith only [this]
  have hDC : C * (4 + 1 / l) * (1 + 1 / l) ≤ D := by
    dsimp only [D]
    linarith only [hC]
  refine ⟨p, c, D, hp, hc, hD, ?_⟩
  intro Q lam h₀ h₁ P K hK hD' A hA F G hF hG hFp hGp hzero
  dsimp only
  intro t
  apply ((hb Q lam h₀ h₁ P K hK hD' A hA F G hF hG hFp hGp hzero t).2).trans
  apply mul_le_mul_of_nonneg_right _ ENNReal.toReal_nonneg
  apply mul_le_mul_of_nonneg_right _ ENNReal.toReal_nonneg
  apply mul_le_mul hCD (Real.exp_le_exp.mpr ?_) (Real.exp_pos _).le hD.le
  apply sub_le_sub_right
  have hcycle := sbxS2_prescribed_cycles_le l A hlpos hA
  have hApos : 0 < A := hlpos.trans_le hA
  have hAl : 1 ≤ A / l := (le_div_iff₀ hlpos).mpr (by simpa only [one_mul] using hA)
  calc
    _ ≤ C * ((4 + 1 / l) * (1 + A)) := mul_le_mul_of_nonneg_left hcycle hC.le
    _ ≤ C * ((4 + 1 / l) * ((1 + 1 / l) * A)) := by
      apply mul_le_mul_of_nonneg_left _ hC.le
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have hAlmul : 1 ≤ (1 / l) * A := by
        simpa only [div_eq_mul_inv, one_mul, mul_one, mul_comm] using hAl
      nlinarith only [hAlmul]
    _ = (C * (4 + 1 / l) * (1 + 1 / l)) * A := by ring
    _ ≤ D * A := mul_le_mul_of_nonneg_right hDC hApos.le

#print axioms sbxS2_covariance_radius_decay_of_deps

#print axioms sbxS2_positive_km_decomp_of_deps

#print axioms sbxS2_exp_decay_product_mono
#print axioms sbxS2_covariance_and_remainder_decay_of_deps

#print axioms sbxS2_regeneration_remainder_decay_of_deps
#print axioms sbxS2_remainder_moment_variable_rate
#print axioms sbxS2_power_interpolation_constants
#print axioms sbxS2_covariance_power_moment_of_remainder
#print axioms sbxS2_setIntegral_abs_le_moment
#print axioms sbxS2_covariance_sub_remainder_time_decay_of_deps
#print axioms sbxS2_slice_decay_normalized_of_manyCycleMoment
#print axioms sbxS2_covariance_sub_remainder_decay_of_deps
#print axioms sbxS2_centered_convolution_decay
#print axioms sbxS2_centered_covariance_of_deps
#print axioms sbxS2_covariance_decomposition_of_deps
#print axioms sbxS2_covariance_integrable_of_remainder
#print axioms sbxS2_tendsto_setIntegral_mul_clamp
#print axioms sbxS2_integrable_bounded_observation
#print axioms sbxS2_bounded_covariance_decomposition
#print axioms sbxS2_bounded_covariance_slice
#print axioms sbxS2_PhiM_record_on_slice
#print axioms sbxS2_reduced_kFactor
#print axioms sbxS2_regenerationTime_add
#print axioms sbxS2_regenerationSlice_hasSum
#print axioms sbxS2_regenerationSlice_hasSum_of_moment
#print axioms sbxS2_regenerationSlice_mass_le
#print axioms sbxS2_map_fst_annealed
#print axioms sbxS2_reducedFst_measurePreserving
#print axioms sbxS2_eLpNorm_reducedFst
#print axioms sbxS2_regenerationSlice_enorm_le
#print axioms sbxS2_regenerationSlice_abs_le
#print axioms sbxS2_integral_fst_annealed
#print axioms sbxS2_centered_regenerationSlice_hasSum
#print axioms sbxS2_centered_slices_of_manyCycleMoment
#print axioms sbxS2_slice_decay_of_manyCycleMoment
#print axioms sbxS2_prescribed_cycles_le
#print axioms sbxS2_centered_convolution
#lint

end EinsteinFull.Blueprint
