import EinsteinRelation.Regeneration.RegenerationShiftObservables
import EinsteinRelation.Probability.StoppedHistory
import EinsteinRelation.Probability.FiniteHistoryMeasurability
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

/-!
# Joint-test extension of deterministic restart

Source `paper/main.tex:383–397`. The frozen deterministic restart identity is
stated for products of a past test and a future test. Equality of finite
measures on measurable rectangles extends it to arbitrary bounded joint
tests. The resulting formula uses the actual quenched law whenever it is
a probability measure at almost every actual restart position.
-/

open MeasureTheory Function
open scoped NNReal ENNReal

noncomputable section

namespace EinsteinRelation.Regeneration

/-- Product-test restart identifies the joint law of the observed past and
the future (`paper/main.tex:383–397`). -/
theorem map_pair_eq_restart_of_product_tests {Ω α β : Type*}
    [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → α) (Y : Ω → β)
    (hX : Measurable X) (hY : Measurable Y)
    (L : ProbabilityTheory.Kernel Ω β) [ProbabilityTheory.IsFiniteKernel L]
    (h : ∀ (H : α → ℝ) (Φ : β → ℝ), Measurable H → BoundedRealTest H →
      Measurable Φ → BoundedRealTest Φ →
      (∫ z, H (X z) * Φ (Y z) ∂μ) = ∫ z, H (X z) * (∫ w, Φ w ∂L z) ∂μ) :
    μ.map (fun z => (X z, Y z)) =
      (μ.compProd L).map (fun q => (X q.1, q.2)) := by
  classical
  let f := fun z => (X z, Y z)
  let g := fun q : Ω × β => (X q.1, q.2)
  have hf : Measurable f := hX.prodMk hY
  have hg : Measurable g := (hX.comp measurable_fst).prodMk measurable_snd
  apply Measure.ext_prod
  intro s t hs ht
  let H : α → ℝ := s.indicator (fun _ => 1)
  let Φ : β → ℝ := t.indicator (fun _ => 1)
  have hHm : Measurable H := measurable_const.indicator hs
  have hΦm : Measurable Φ := measurable_const.indicator ht
  have hHb : BoundedRealTest H := ⟨1, fun x => by by_cases hx : x ∈ s <;> simp [H, hx]⟩
  have hΦb : BoundedRealTest Φ := ⟨1, fun x => by by_cases hx : x ∈ t <;> simp [Φ, hx]⟩
  let I : α × β → ℝ := (s ×ˢ t).indicator (fun _ => 1)
  have hIm : Measurable I := measurable_const.indicator (hs.prod ht)
  have hIb : ∀ q, ‖I q‖ ≤ 1 := fun q => by
    by_cases hq : q ∈ s ×ˢ t <;> simp [I, hq]
  have hprod : ∀ x y, I (x, y) = H x * Φ y := by
    intro x y
    by_cases hx : x ∈ s <;> by_cases hy : y ∈ t <;> simp [I, H, Φ, hx, hy]
  have hint : Integrable (I ∘ g) (μ.compProd L) :=
    Integrable.of_bound (hIm.comp hg).aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun q => hIb (g q))
  have heq : (∫ q, I q ∂μ.map f) = ∫ q, I q ∂(μ.compProd L).map g := by
    rw [integral_map hf.aemeasurable hIm.aestronglyMeasurable,
      integral_map hg.aemeasurable hIm.aestronglyMeasurable]
    change (∫ z, I (f z) ∂μ) = ∫ q, (I ∘ g) q ∂μ.compProd L
    rw [Measure.integral_compProd hint]
    simp only [f, g, Function.comp_def, hprod, integral_const_mul]
    exact h H Φ hHm hHb hΦm hΦb
  have heq' : ((μ.map f) (s ×ˢ t)).toReal =
      (((μ.compProd L).map g) (s ×ˢ t)).toReal := by
    simpa only [I, integral_indicator (hs.prod ht),
      setIntegral_one_eq_measureReal, measureReal_def] using heq
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top (μ.map f) _)
    (measure_ne_top ((μ.compProd L).map g) _)).mp heq'

/-- Deterministic restart applies to every bounded measurable joint test of
the stopped exact past and the future. Probability at the actual restart
points is a separate a.e. property, supplied by positive-time endpoint density. -/
theorem integral_joint_of_deterministicRestartAt {d : ℕ} (Δ : ℝ≥0)
    (K : CoupledQuenchedLaws d) (xω : Vec d × FieldPair d)
    [IsProbabilityMeasure (K xω)] (hRestart : DeterministicRestartAt Δ K xω) (n : ℕ)
    (hprob : ∀ᵐ z ∂K xω,
      IsProbabilityMeasure (K (z.1 ((n : ℝ≥0) * Δ), xω.2)))
    (F : CoupledSample d × CoupledSample d → ℝ) (hF : Measurable F)
    (hb : BoundedRealTest F) :
    (∫ z, F (Probability.stoppedHistorySample Δ n z,
      sampleTimeShift Δ z ((n : ℝ≥0) * Δ)) ∂K xω) =
      ∫ z, ∫ w, F (Probability.stoppedHistorySample Δ n z, w)
        ∂K (z.1 ((n : ℝ≥0) * Δ), xω.2) ∂K xω := by
  let X := Probability.stoppedHistorySample (d := d) Δ n
  let Y := fun z : CoupledSample d => sampleTimeShift Δ z ((n : ℝ≥0) * Δ)
  let L : ProbabilityTheory.Kernel (CoupledSample d) (CoupledSample d) :=
    (Probability.probabilityPart K).comap
    (fun z : CoupledSample d => (z.1 ((n : ℝ≥0) * Δ), xω.2))
    (((continuous_eval_const _).measurable.comp measurable_fst).prodMk measurable_const)
  have hXpast := Probability.measurable_stoppedHistorySample (d := d) Δ n
  have hX : Measurable X := hXpast.mono (Probability.finiteHistorySigma_le Δ n) le_rfl
  have hY : Measurable Y := (measurable_sampleTimeShift Δ).comp
    (measurable_const.prodMk measurable_id)
  have hLeq : ∀ᵐ z ∂K xω, L z = K (z.1 ((n : ℝ≥0) * Δ), xω.2) := by
    filter_upwards [hprob] with z hz
    haveI := hz
    exact Probability.probabilityPart_eq_of_isProbabilityMeasure K _
  have hlaw := map_pair_eq_restart_of_product_tests (K xω) X Y hX hY L ?_
  · have hFjoint : Measurable (fun q : CoupledSample d × CoupledSample d => F (X q.1, q.2)) :=
      hF.comp ((hX.comp measurable_fst).prodMk measurable_snd)
    obtain ⟨C, hC⟩ := hb
    have hint : Integrable (fun q : CoupledSample d × CoupledSample d => F (X q.1, q.2))
        ((K xω).compProd L) :=
      Integrable.of_bound hFjoint.aestronglyMeasurable C
        (Filter.Eventually.of_forall fun q => by rw [Real.norm_eq_abs]; exact hC _)
    have heq := congrArg (fun ν : Measure (CoupledSample d × CoupledSample d) => ∫ q, F q ∂ν) hlaw
    have hmapg : Measurable (fun q : CoupledSample d × CoupledSample d => (X q.1, q.2)) :=
      (hX.comp measurable_fst).prodMk measurable_snd
    rw [integral_map (hX.prodMk hY).aemeasurable hF.aestronglyMeasurable,
      integral_map hmapg.aemeasurable hF.aestronglyMeasurable,
      Measure.integral_compProd hint] at heq
    refine heq.trans (integral_congr_ae ?_)
    filter_upwards [hLeq] with z hz
    rw [hz]
  · intro H Φ hH hbH hΦ hbΦ
    have hbHX : BoundedRealTest (H ∘ X) := by
      obtain ⟨C, hC⟩ := hbH
      exact ⟨C, fun z => hC (X z)⟩
    refine (hRestart n (H ∘ X) Φ (hH.comp hXpast) hbHX hΦ hbΦ).trans ?_
    apply integral_congr_ae
    filter_upwards [hLeq] with z hz
    rw [hz]
    rfl


end EinsteinRelation.Regeneration
