import EinsteinFull.Regeneration.KilledBridgeKernel

/-!
# The canonical joint path and first-coin law

This is one interval of the split construction: the two literal bridge kernels
are tagged by their coins and mixed with the source weights. Its path marginal
is the original path law, and conditioning on the coin recovers the exact
branch kernels. Iterating the segments into a whole path/coin sequence is a
separate obligation.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

noncomputable section
namespace EinsteinFull.Regeneration
open EinsteinRelation EinsteinRelation.Regeneration

/-- The actual successful/failed path kernels tagged by the first coin.
The environment and starting point remain joint kernel parameters. -/
def oneIntervalSplitKernel {d : ℕ} (Δ : ℝ≥0) (δ R : ℝ) (i : Fin d)
    (hδ : 0 ≤ δ) (hR : 0 < R) (P : QuenchedPathLaws d) [IsFiniteKernel P]
    (hminor : ∀ ω : FieldPair d,
      EinsteinFull.External.Source.GMP.HasSourceMinorization
        (fun x => P (x, ω)) Δ δ R i) :
    Kernel (Vec d × FieldPair d) (Path d × Bool) where
  toFun a :=
    ENNReal.ofReal δ • ((killedBridgeKernel Δ R i P) a).map (fun γ => (γ, true)) +
    ENNReal.ofReal (1 - δ) •
      ((failedKilledBridgeKernel Δ δ R i hδ hR P hminor) a).map (fun γ => (γ, false))
  measurable' := by
    apply Measure.measurable_of_measurable_coe
    intro A hA
    have ht : Measurable (fun γ : Path d => (γ, true)) :=
      measurable_id.prodMk measurable_const
    have hf₀ : Measurable (fun γ : Path d => (γ, false)) :=
      measurable_id.prodMk measurable_const
    have hs := Kernel.measurable_coe
      ((killedBridgeKernel Δ R i P).map (fun γ => (γ, true))) hA
    have hf := Kernel.measurable_coe
      ((failedKilledBridgeKernel Δ δ R i hδ hR P hminor).map (fun γ => (γ, false))) hA
    simp only [Kernel.map_apply _ ht] at hs
    simp only [Kernel.map_apply _ hf₀] at hf
    have h : Measurable (fun a : Vec d × FieldPair d =>
        ENNReal.ofReal δ * (((killedBridgeKernel Δ R i P) a).map (fun γ => (γ, true))) A +
        ENNReal.ofReal (1 - δ) *
          (((failedKilledBridgeKernel Δ δ R i hδ hR P hminor) a).map
            (fun γ => (γ, false))) A) :=
      (hs.const_mul _).add (hf.const_mul _)
    simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul]
    exact h

/-- The fibre formula uses the literal successful and failed bridge laws. -/
theorem oneIntervalSplitKernel_apply {d : ℕ} (Δ : ℝ≥0) (δ R : ℝ) (i : Fin d)
    (hδ : 0 ≤ δ) (hR : 0 < R) (P : QuenchedPathLaws d) [IsFiniteKernel P]
    (hminor : ∀ ω : FieldPair d,
      EinsteinFull.External.Source.GMP.HasSourceMinorization
        (fun x => P (x, ω)) Δ δ R i) (a : Vec d × FieldPair d) :
    oneIntervalSplitKernel Δ δ R i hδ hR P hminor a =
      ENNReal.ofReal δ • (Renewal.killedBridgeMixture Δ R i P a.1 a.2).map
        (fun γ => (γ, true)) +
      ENNReal.ofReal (1 - δ) • (failedKilledBridgeLaw Δ δ R i P a.1 a.2).map
        (fun γ => (γ, false)) := by
  simp only [oneIntervalSplitKernel, Kernel.coe_mk, killedBridgeKernel_apply Δ R i hR,
    failedKilledBridgeKernel_apply]

/-- Forgetting the first coin recovers the original path law exactly. -/
theorem map_oneIntervalSplitKernel_fst {d : ℕ} (Δ : ℝ≥0) (δ R : ℝ) (i : Fin d)
    (hδ₀ : 0 < δ) (hδ₁ : δ < 1) (hR : 0 < R)
    (P : QuenchedPathLaws d) [IsMarkovKernel P]
    (hminor : ∀ ω : FieldPair d,
      EinsteinFull.External.Source.GMP.HasSourceMinorization
        (fun x => P (x, ω)) Δ δ R i) (a : Vec d × FieldPair d) :
    (oneIntervalSplitKernel Δ δ R i hδ₀.le hR P hminor a).map Prod.fst = P a := by
  have ht : Measurable (fun γ : Path d => (γ, true)) :=
    measurable_id.prodMk measurable_const
  have hf : Measurable (fun γ : Path d => (γ, false)) :=
    measurable_id.prodMk measurable_const
  rw [oneIntervalSplitKernel_apply, Measure.map_add _ _ measurable_fst,
    Measure.map_smul _ measurable_fst.aemeasurable,
    Measure.map_smul _ measurable_fst.aemeasurable,
    Measure.map_map measurable_fst ht, Measure.map_map measurable_fst hf]
  change ENNReal.ofReal δ •
      (Renewal.killedBridgeMixture Δ R i P a.1 a.2).map id +
      ENNReal.ofReal (1 - δ) • (failedKilledBridgeLaw Δ δ R i P a.1 a.2).map id = P a
  simp only [Measure.map_id]
  exact killedBridge_split_mixture_eq_pathLaw P a.2 Δ δ R i hδ₀ hδ₁ (hminor a.2) a.1

/-- The joint first-coin kernel is Markov, with no selected coupling assumed. -/
theorem isMarkovKernel_oneIntervalSplitKernel {d : ℕ} (Δ : ℝ≥0)
    (δ R : ℝ) (i : Fin d) (hδ₀ : 0 < δ) (hδ₁ : δ < 1) (hR : 0 < R)
    (P : QuenchedPathLaws d) [IsMarkovKernel P]
    (hminor : ∀ ω : FieldPair d,
      EinsteinFull.External.Source.GMP.HasSourceMinorization
        (fun x => P (x, ω)) Δ δ R i) :
    IsMarkovKernel (oneIntervalSplitKernel Δ δ R i hδ₀.le hR P hminor) := by
  constructor
  intro a
  constructor
  have h := congrArg (fun μ : Measure (Path d) => μ Set.univ)
    (map_oneIntervalSplitKernel_fst Δ δ R i hδ₀ hδ₁ hR P hminor a)
  simpa only [Measure.map_apply measurable_fst MeasurableSet.univ,
    Set.preimage_univ, measure_univ] using h

/-- The first coin has the source Bernoulli probabilities. -/
theorem oneIntervalSplitKernel_coin {d : ℕ} (Δ : ℝ≥0) (δ R : ℝ) (i : Fin d)
    (hδ₀ : 0 < δ) (hδ₁ : δ < 1) (hR : 0 < R)
    (P : QuenchedPathLaws d) [IsMarkovKernel P]
    (hminor : ∀ ω : FieldPair d,
      EinsteinFull.External.Source.GMP.HasSourceMinorization
        (fun x => P (x, ω)) Δ δ R i) (a : Vec d × FieldPair d) (coin : Bool) :
    oneIntervalSplitKernel Δ δ R i hδ₀.le hR P hminor a {z | z.2 = coin} =
      ENNReal.ofReal (if coin then δ else 1 - δ) := by
  haveI := isProbabilityMeasure_killedBridgeMixture P a.2 Δ δ R i
    hδ₀ hR (hminor a.2) a.1
  haveI := isProbabilityMeasure_failedKilledBridgeLaw P a.2 Δ δ R i
    hδ₀ hδ₁ hR (hminor a.2) a.1
  have hm : MeasurableSet {z : Path d × Bool | z.2 = coin} :=
    measurable_snd (measurableSet_singleton coin)
  have ht : Measurable (fun γ : Path d => (γ, true)) :=
    measurable_id.prodMk measurable_const
  have hf : Measurable (fun γ : Path d => (γ, false)) :=
    measurable_id.prodMk measurable_const
  rw [oneIntervalSplitKernel_apply]
  simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul,
    Measure.map_apply ht hm, Measure.map_apply hf hm]
  cases coin <;> simp

/-- Restriction to a coin event selects exactly its weighted tagged branch. -/
theorem restrict_oneIntervalSplitKernel_coin {d : ℕ} (Δ : ℝ≥0)
    (δ R : ℝ) (i : Fin d) (hδ : 0 ≤ δ) (hR : 0 < R)
    (P : QuenchedPathLaws d) [IsFiniteKernel P]
    (hminor : ∀ ω : FieldPair d,
      EinsteinFull.External.Source.GMP.HasSourceMinorization
        (fun x => P (x, ω)) Δ δ R i) (a : Vec d × FieldPair d) (coin : Bool) :
    (oneIntervalSplitKernel Δ δ R i hδ hR P hminor a).restrict {z | z.2 = coin} =
      if coin then
        ENNReal.ofReal δ • (Renewal.killedBridgeMixture Δ R i P a.1 a.2).map
          (fun γ => (γ, true))
      else
        ENNReal.ofReal (1 - δ) • (failedKilledBridgeLaw Δ δ R i P a.1 a.2).map
          (fun γ => (γ, false)) := by
  have hm : MeasurableSet {z : Path d × Bool | z.2 = coin} :=
    measurable_snd (measurableSet_singleton coin)
  have ht : Measurable (fun γ : Path d => (γ, true)) :=
    measurable_id.prodMk measurable_const
  have hf : Measurable (fun γ : Path d => (γ, false)) :=
    measurable_id.prodMk measurable_const
  rw [oneIntervalSplitKernel_apply, Measure.restrict_add,
    Measure.restrict_smul, Measure.restrict_smul,
    Measure.restrict_map ht hm, Measure.restrict_map hf hm]
  cases coin <;> simp

/-- Conditioning on the first coin recovers the actual canonical branch,
including its normalization. The positive coin masses are explicit. -/
theorem map_cond_oneIntervalSplitKernel_coin {d : ℕ} (Δ : ℝ≥0)
    (δ R : ℝ) (i : Fin d) (hδ₀ : 0 < δ) (hδ₁ : δ < 1) (hR : 0 < R)
    (P : QuenchedPathLaws d) [IsMarkovKernel P]
    (hminor : ∀ ω : FieldPair d,
      EinsteinFull.External.Source.GMP.HasSourceMinorization
        (fun x => P (x, ω)) Δ δ R i) (a : Vec d × FieldPair d) (coin : Bool) :
    (cond (oneIntervalSplitKernel Δ δ R i hδ₀.le hR P hminor a)
      {z | z.2 = coin}).map Prod.fst =
      if coin then Renewal.killedBridgeMixture Δ R i P a.1 a.2
      else failedKilledBridgeLaw Δ δ R i P a.1 a.2 := by
  have ht : Measurable (fun γ : Path d => (γ, true)) :=
    measurable_id.prodMk measurable_const
  have hf : Measurable (fun γ : Path d => (γ, false)) :=
    measurable_id.prodMk measurable_const
  rw [ProbabilityTheory.cond, oneIntervalSplitKernel_coin Δ δ R i hδ₀ hδ₁ hR P hminor a coin,
    restrict_oneIntervalSplitKernel_coin]
  cases coin
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [Measure.map_smul _ measurable_fst.aemeasurable,
      Measure.map_smul _ measurable_fst.aemeasurable, Measure.map_map measurable_fst hf]
    change (ENNReal.ofReal (1 - δ))⁻¹ •
      (ENNReal.ofReal (1 - δ) • (failedKilledBridgeLaw Δ δ R i P a.1 a.2).map id) = _
    simp only [Measure.map_id, smul_smul,
      ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.mpr (sub_pos.mpr hδ₁)).ne'
        ENNReal.ofReal_ne_top, one_smul]
  · simp only [↓reduceIte]
    rw [Measure.map_smul _ measurable_fst.aemeasurable,
      Measure.map_smul _ measurable_fst.aemeasurable, Measure.map_map measurable_fst ht]
    change (ENNReal.ofReal δ)⁻¹ •
      (ENNReal.ofReal δ • (Renewal.killedBridgeMixture Δ R i P a.1 a.2).map id) = _
    simp only [Measure.map_id, smul_smul,
      ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.mpr hδ₀).ne'
        ENNReal.ofReal_ne_top, one_smul]

/-- On success the actual joint law stays in the source tube throughout the
closed first interval. This is a conditional-law assertion, not just support
of an independently supplied branch measure. -/
theorem ae_cond_oneIntervalSplitKernel_stays {d : ℕ} (Δ : ℝ≥0)
    (δ R : ℝ) (i : Fin d) (hδ₀ : 0 < δ) (hδ₁ : δ < 1) (hR : 0 < R)
    (P : QuenchedPathLaws d) [IsMarkovKernel P]
    (hminor : ∀ ω : FieldPair d,
      EinsteinFull.External.Source.GMP.HasSourceMinorization
        (fun x => P (x, ω)) Δ δ R i) (a : Vec d × FieldPair d) :
    ∀ᵐ z ∂cond (oneIntervalSplitKernel Δ δ R i hδ₀.le hR P hminor a)
      {z | z.2 = true}, ∀ t : ℝ≥0, t ≤ Δ → z.1 t ∈ couplingRegion i R a.1 := by
  have h := ae_killedBridgeMixture_stays_in_couplingRegion P a.2 Δ R i a.1
  have heq := map_cond_oneIntervalSplitKernel_coin Δ δ R i hδ₀ hδ₁ hR P hminor a true
  simp only [↓reduceIte] at heq
  rw [← heq] at h
  exact ae_of_ae_map measurable_fst.aemeasurable h

/-- The endpoint of the successful conditional joint law is exactly uniform
on the source endpoint ball. -/
theorem map_cond_oneIntervalSplitKernel_endpoint {d : ℕ} (Δ : ℝ≥0)
    (δ R : ℝ) (i : Fin d) (hδ₀ : 0 < δ) (hδ₁ : δ < 1) (hR : 0 < R)
    (P : QuenchedPathLaws d) [IsMarkovKernel P]
    (hminor : ∀ ω : FieldPair d,
      EinsteinFull.External.Source.GMP.HasSourceMinorization
        (fun x => P (x, ω)) Δ δ R i) (a : Vec d × FieldPair d) :
    (cond (oneIntervalSplitKernel Δ δ R i hδ₀.le hR P hminor a)
      {z | z.2 = true}).map (fun z => z.1 Δ) =
      cond (volume : Measure (Vec d)) (endpointBall i R a.1) := by
  have hm : Measurable (fun γ : Path d => γ Δ) := (continuous_eval_const Δ).measurable
  change (cond (oneIntervalSplitKernel Δ δ R i hδ₀.le hR P hminor a)
    {z | z.2 = true}).map ((fun γ : Path d => γ Δ) ∘ Prod.fst) = _
  rw [← Measure.map_map hm measurable_fst,
    map_cond_oneIntervalSplitKernel_coin Δ δ R i hδ₀ hδ₁ hR P hminor a true]
  exact map_killedBridgeMixture_endpoint_eq_uniform P a.2 Δ δ R i
    hδ₀ (hminor a.2) a.1

end EinsteinFull.Regeneration
