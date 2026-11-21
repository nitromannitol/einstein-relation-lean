import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.IdentDistrib

/-!
# Independence of cycle observables of a regenerative record sequence

Let `Y k` be the future record at the `k`-th regeneration time, so that a measurable shift `Θ`
carries `Y k` to `Y (k + 1)`. Suppose that every record `Y k`, `k ≥ 1`, has the law of `Y 0`
under the conditioned law `ν`, and that under `ν` a first-cycle observable `c (Y 0)` is
independent of the next record `Y 1`. Then the observables `c (Y k)`, `k ≥ 1`, are pairwise
independent and identically distributed. This is the step from the regeneration factorization
to the independence of the cycles (GMP 2012, Theorem 5.6; Shen 2003, Theorem 2.5).
-/

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

namespace EinsteinFull.Regeneration

variable {Ω S β : Type*} [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace β]

omit [MeasurableSpace S] in
/-- The iterated shift carries each record to a later one, almost surely. -/
theorem ae_iterate_record_eq (ρ : Measure Ω) (Y : ℕ → Ω → S) (Θ : S → S)
    (hΘ : ∀ k, ∀ᵐ ω ∂ρ, Θ (Y k ω) = Y (k + 1) ω) (k m : ℕ) :
    ∀ᵐ ω ∂ρ, Θ^[m] (Y k ω) = Y (k + m) ω := by
  induction m with
  | zero => exact Filter.Eventually.of_forall fun ω => rfl
  | succ m ih =>
    filter_upwards [ih, hΘ (k + m)] with ω h1 h2
    rw [Function.iterate_succ_apply', h1, h2]
    rfl

/-- Cycle observables of a regenerative record sequence are pairwise independent and
identically distributed. -/
theorem indepFun_identDistrib_of_record_factorization
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (Y : ℕ → Ω → S) (hY : ∀ k, Measurable (Y k)) (Θ : S → S) (hΘm : Measurable Θ)
    (hΘμ : ∀ k, ∀ᵐ ω ∂μ, Θ (Y k ω) = Y (k + 1) ω)
    (hΘν : ∀ k, ∀ᵐ ω ∂ν, Θ (Y k ω) = Y (k + 1) ω)
    (hμ : ∀ k, 1 ≤ k → μ.map (Y k) = ν.map (Y 0))
    (hν : ∀ k, 1 ≤ k → ν.map (Y k) = ν.map (Y 0))
    (c : S → β) (hc : Measurable c)
    (hfac : (fun ω => c (Y 0 ω)) ⟂ᵢ[ν] Y 1) :
    (∀ j k, j < k → (fun ω => c (Y (j + 1) ω)) ⟂ᵢ[μ] fun ω => c (Y (k + 1) ω)) ∧
      ∀ k, IdentDistrib (fun ω => c (Y (k + 1) ω)) (fun ω => c (Y 1 ω)) μ μ := by
  have hlaw : ∀ k, μ.map (fun ω => c (Y (k + 1) ω)) = ν.map (fun ω => c (Y 0 ω)) := by
    intro k
    have h1 : (fun ω => c (Y (k + 1) ω)) = c ∘ Y (k + 1) := rfl
    have h2 : (fun ω => c (Y 0 ω)) = c ∘ Y 0 := rfl
    rw [h1, h2, ← Measure.map_map hc (hY _), ← Measure.map_map hc (hY _), hμ (k + 1) (by omega)]
  refine ⟨fun j k hjk => ?_, fun k => ?_⟩
  · obtain ⟨m, rfl⟩ : ∃ m, k = j + (m + 1) := ⟨k - j - 1, by omega⟩
    have hf : AEMeasurable (fun ω => c (Y (j + 1) ω)) μ := (hc.comp (hY _)).aemeasurable
    have hg : AEMeasurable (fun ω => c (Y (j + (m + 1) + 1) ω)) μ :=
      (hc.comp (hY _)).aemeasurable
    rw [indepFun_iff_map_prod_eq_prod_map_map hf hg, hlaw, hlaw]
    let p : S → β × β := fun s => (c s, c (Θ^[m + 1] s))
    have hp : Measurable p := hc.prodMk (hc.comp (hΘm.iterate (m + 1)))
    have hpair : μ.map (fun ω => (c (Y (j + 1) ω), c (Y (j + (m + 1) + 1) ω))) =
        (μ.map (Y (j + 1))).map p := by
      rw [Measure.map_map hp (hY _)]
      apply Measure.map_congr
      filter_upwards [ae_iterate_record_eq μ Y Θ hΘμ (j + 1) (m + 1)] with ω hω
      rw [show j + (m + 1) + 1 = j + 1 + (m + 1) by omega]
      simp only [Function.comp_apply, p, hω]
    rw [hpair, hμ (j + 1) (by omega), Measure.map_map hp (hY _)]
    have hνpair : ν.map (p ∘ Y 0) = ν.map (fun ω => (c (Y 0 ω), c (Θ^[m] (Y 1 ω)))) := by
      apply Measure.map_congr
      filter_upwards [hΘν 0] with ω hω
      simp only [Function.comp_apply, p, Function.iterate_succ_apply, hω, zero_add]
    have hind : (fun ω => c (Y 0 ω)) ⟂ᵢ[ν] fun ω => c (Θ^[m] (Y 1 ω)) :=
      hfac.comp measurable_id (hc.comp (hΘm.iterate m))
    have hprod := (indepFun_iff_map_prod_eq_prod_map_map (hc.comp (hY 0)).aemeasurable
      (hc.comp ((hΘm.iterate m).comp (hY 1))).aemeasurable).1 hind
    rw [hνpair]
    refine hprod.trans ?_
    congr 1
    have h1 : (fun ω => c (Θ^[m] (Y 1 ω))) =ᵐ[ν] fun ω => c (Y (1 + m) ω) := by
      filter_upwards [ae_iterate_record_eq ν Y Θ hΘν 1 m] with ω hω
      rw [hω]
    rw [show (c ∘ Θ^[m] ∘ Y 1) = fun ω => c (Θ^[m] (Y 1 ω)) from rfl, Measure.map_congr h1]
    have h2 : (fun ω => c (Y (1 + m) ω)) = c ∘ Y (1 + m) := rfl
    have h3 : (fun ω => c (Y 0 ω)) = c ∘ Y 0 := rfl
    rw [h2, h3, ← Measure.map_map hc (hY _), ← Measure.map_map hc (hY _), hν (1 + m) (by omega)]
  · refine ⟨(hc.comp (hY _)).aemeasurable, (hc.comp (hY _)).aemeasurable, ?_⟩
    rw [hlaw k, ← hlaw 0]

end EinsteinFull.Regeneration
