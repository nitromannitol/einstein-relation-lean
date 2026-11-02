import EinsteinFull.Regeneration.GMPSplitSourceTransfer
import EinsteinRelation.Regeneration.EndpointAverageFubini

/-! # Uniform endpoints at every deterministic split interval

The source's first-coin conditional path law, current-coin path restart and
fresh-coin independence imply the actual finite-history endpoint identity.
No joint-kernel existence, bridge formula or regeneration claim is assumed.
-/

open MeasureTheory
open scoped NNReal ENNReal

namespace EinsteinFull.Regeneration
open EinsteinRelation EinsteinRelation.Regeneration
open EinsteinFull.External.Source.GMP

/-- The literal successful conditional path law integrates an endpoint test
against the normalized Euclidean endpoint ball. -/
theorem source_split_conditional_endpoint_integral {d : ℕ}
    {P : Vec d → Measure (Path d)} {Δ : ℝ≥0} {δ R : ℝ} {i : Fin d}
    {K : Vec d → Measure (CoupledSample d)}
    (hK : IsSourceSplitCoupling P Δ δ R i K) (x : Vec d)
    (φ : Vec d → ℝ) (hφ : Measurable φ) :
    (∫ γ, φ (γ Δ) ∂conditionalPathLaw K x true) = endpointAverage i R x φ := by
  have hmap := (hK x).2.2.2.2.2.2
  calc
    (∫ γ, φ (γ Δ) ∂conditionalPathLaw K x true) =
        ∫ y, φ y ∂(conditionalPathLaw K x true).map (fun γ => γ Δ) :=
      (integral_map (measurable_pathPosition Δ).aemeasurable
        hφ.aestronglyMeasurable).symm
    _ = ∫ y, φ y ∂ProbabilityTheory.cond (volume : Measure (Vec d))
        (endpointBall i R x) := by rw [hmap]
    _ = endpointAverage i R x φ := by
      rw [ProbabilityTheory.cond, integral_smul_measure]
      simp only [ENNReal.toReal_inv, smul_eq_mul, endpointAverage, div_eq_mul_inv,
        mul_comm]

/-- Source path restart with the current coin, followed by its exact uniform
endpoint law and fresh-coin averaging, gives every deterministic interval's
literal successful endpoint identity against the entire finite past. -/
theorem source_split_uniform_successful_endpoint {d : ℕ}
    {P : Vec d → Measure (Path d)} {Δ : ℝ≥0} {δ R : ℝ} {i : Fin d}
    (K : CoupledQuenchedLaws d) (ω : FieldPair d)
    (hK : IsSourceSplitCoupling P Δ δ R i (fun x => K (x, ω)))
    (hδ : 0 ≤ δ) (hR : 0 < R) (x : Vec d) :
    UniformSuccessfulEndpointAt Δ δ R i K (x, ω) := by
  intro n H φ hH hbH hφ hbφ
  let χ : CoupledSample d → ℝ := fun z => if z.2 n = true then 1 else 0
  let X : CoupledSample d → Vec d := fun z => z.1 ((n : ℝ≥0) * Δ)
  have hX : @Measurable (CoupledSample d) (Vec d)
      (finiteHistorySigma Δ n) inferInstance X := by
    apply EinsteinRelation.Probability.measurable_of_finite_history_prefix Δ n X
      ((measurable_pathPosition _).comp measurable_fst)
    intro z z' hp _
    exact hp _ ⟨bot_le, le_rfl⟩
  have hχ : @Measurable (CoupledSample d) ℝ
      (currentCoinHistory Δ n) inferInstance χ := by
    have hc : @Measurable (CoupledSample d) Bool
        (currentCoinHistory Δ n) inferInstance (fun z => z.2 n) :=
      Measurable.of_comap_le le_sup_right
    exact measurable_const.ite
      (measurableSet_eq_fun hc measurable_const) measurable_const
  have hbHχ : BoundedRealTest (fun z => H z * χ z) := by
    obtain ⟨C, hC⟩ := hbH
    refine ⟨max C 0, fun z => ?_⟩
    by_cases hz : z.2 n = true
    · simpa only [χ, hz, ↓reduceIte, mul_one] using (hC z).trans (le_max_left C 0)
    · simpa only [χ, hz, Bool.false_eq_true, ↓reduceIte, mul_zero, abs_zero] using le_max_right C 0
  have hF : Measurable (fun γ : Path d => φ (γ Δ)) :=
    hφ.comp (measurable_pathPosition Δ)
  have hbF : BoundedRealTest (fun γ : Path d => φ (γ Δ)) := by
    obtain ⟨C, hC⟩ := hbφ
    exact ⟨C, fun γ => hC (γ Δ)⟩
  have hr := ((hK x).2.2.2.2.1 n (fun z => H z * χ z)
    (fun γ => φ (γ Δ)) ((hH.mono le_sup_left le_rfl).mul hχ) hbHχ hF hbF).2
  have heval (z : CoupledSample d) :
      (pathTimeShift z.1 ((n : ℝ≥0) * Δ)) Δ =
        z.1 (((n + 1 : ℕ) : ℝ≥0) * Δ) := by
    simp only [pathTimeShift, ContinuousMap.coe_mk, Nat.cast_add, Nat.cast_one,
      add_mul, one_mul]
  have hrhs (z : CoupledSample d) :
      H z * χ z *
          (∫ γ, φ (γ Δ) ∂conditionalPathLaw (fun y => K (y, ω)) (X z) (z.2 n)) =
        (H z * endpointAverage i R (X z) φ) * χ z := by
    by_cases hz : z.2 n = true
    · rw [hz, source_split_conditional_endpoint_integral hK (X z) φ hφ]
      simp only [χ, hz, ↓reduceIte, mul_one]
    · simp only [χ, hz, Bool.false_eq_true, ↓reduceIte, mul_zero, zero_mul]
  have hM : @Measurable (CoupledSample d) ℝ
      (finiteHistorySigma Δ n) inferInstance
      (fun z => H z * endpointAverage i R (X z) φ) := by
    letI : MeasurableSpace (CoupledSample d) := finiteHistorySigma Δ n
    exact hH.mul (measurable_endpointAverage i R X hX
      (fun q : CoupledSample d × Vec d => φ q.2) (hφ.comp measurable_snd))
  have hbM : BoundedRealTest (fun z => H z * endpointAverage i R (X z) φ) := by
    obtain ⟨C, hC⟩ := hbH
    have hb : BoundedRealTest (fun q : CoupledSample d × Vec d => φ q.2) := by
      obtain ⟨B, hB⟩ := hbφ
      exact ⟨B, fun q => hB q.2⟩
    obtain ⟨B, hB⟩ := boundedRealTest_endpointAverage i R hR X
      (fun q : CoupledSample d × Vec d => φ q.2) hb
    refine ⟨max C 0 * max B 0, fun z => ?_⟩
    rw [abs_mul]
    exact mul_le_mul ((hC z).trans (le_max_left C 0))
      ((hB z).trans (le_max_left B 0)) (abs_nonneg _)
      (le_max_right C 0)
  change (∫ z, H z * χ z * φ (z.1 (((n + 1 : ℕ) : ℝ≥0) * Δ)) ∂K (x, ω)) = _
  calc
    _ = ∫ z, H z * χ z * φ ((pathTimeShift z.1 ((n : ℝ≥0) * Δ)) Δ)
        ∂K (x, ω) := by simp only [heval]
    _ = ∫ z, (H z * endpointAverage i R (X z) φ) * χ z ∂K (x, ω) := by
      rw [hr]
      exact integral_congr_ae (Filter.Eventually.of_forall hrhs)
    _ = δ * ∫ z, H z * endpointAverage i R (X z) φ ∂K (x, ω) :=
      source_split_fresh_bits K ω hK hδ x n _ hM hbM


/-- Once a jointly measurable kernel is constructed internally with the source
property on one full environment event, it has the repository's exact origin
and product-a.e. probability, path, fresh-bit and successful endpoint laws.
This implication asserts no existence or locality of that joint kernel. -/
theorem source_split_joint_kernel_properties {d : ℕ}
    (Q : Measure (FieldPair d)) [SFinite Q] (P : QuenchedPathLaws d)
    {Δ : ℝ≥0} {δ R : ℝ} {i : Fin d}
    (K : CoupledQuenchedLaws d)
    (hK : ∀ᵐ ω ∂Q,
      IsSourceSplitCoupling (fun x => P (x, ω)) Δ δ R i (fun x => K (x, ω)))
    (hδ : 0 ≤ δ) (hR : 0 < R) :
    HasProbabilityLaws Q K ∧ HasPathMarginals Q K P ∧
      HasFreshBits Q Δ δ K ∧ HasUniformSuccessfulEndpoint Q Δ δ R i K := by
  have hp : ∀ᵐ xω ∂((volume : Measure (Vec d)).prod Q),
      IsSourceSplitCoupling (fun x => P (x, xω.2)) Δ δ R i
        (fun x => K (x, xω.2)) :=
    Measure.quasiMeasurePreserving_snd.ae hK
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · exact hK.mono (fun _ h => (h 0).1)
  · exact hp.mono (fun xω h => (h xω.1).1)
  · exact hK.mono (fun _ h => (h 0).2.1)
  · exact hp.mono (fun xω h => (h xω.1).2.1)
  · exact hK.mono (fun ω h => source_split_fresh_bits K ω h hδ 0)
  · exact hp.mono (fun xω h => source_split_fresh_bits K xω.2 h hδ xω.1)
  · exact hK.mono (fun ω h => source_split_uniform_successful_endpoint K ω h hδ hR 0)
  · exact hp.mono (fun xω h =>
      source_split_uniform_successful_endpoint K xω.2 h hδ hR xω.1)

end EinsteinFull.Regeneration
