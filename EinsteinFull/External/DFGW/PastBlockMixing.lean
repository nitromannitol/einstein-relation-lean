import EinsteinFull.External.DFGW.PastStateMixing

/-! # Mixing of past observables and future blocks

A future block whose conditional expectation factors through the initial state inherits
state-space mixing under time shifts.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- A centered future block with a state-measurable conditional expectation becomes
asymptotically orthogonal to any square-integrable past observable. -/
theorem tendsto_inner_past_shifted_block_zero
    (hP : Draft.IsDFGWTrajectoryProcess P μ T) (hμ : μ Set.univ ≠ ⊤)
    {t : ℝ≥0} (ht : 0 < t) (f Z : Lp ℝ 2 P)
    (hf : AEStronglyMeasurable[Draft.dfgwCoordSigma (Set.Iic 0)] f P)
    (g : Lp ℝ 2 μ) (hg : ∫ x, g x ∂μ = 0)
    (hZ : P[Z | Draft.dfgwCoordSigma (Set.Iic 0)] =ᵐ[P] fun η => g (η 0)) :
    let shiftMP (u : ℝ) : MeasurePreserving (Draft.dfgwShift (S := S) u) P P :=
      ⟨measurable_shift u, hP.stationary u⟩
    Tendsto (fun n : ℕ => inner ℝ f
      (Lp.compMeasurePreserving _ (shiftMP (n • t : ℝ≥0)) Z)) atTop (𝓝 0) := by
  let : IsProbabilityMeasure P := hP.probability
  let : IsProbabilityMeasure μ := hP.invariant_probability
  let hσ₀ : Draft.dfgwCoordSigma (S := S) (Set.Iic 0) ≤
      Draft.dfgwTrajectoryMeasurableSpace (S := S) := (Draft.dfgwPast (S := S)).le 0
  let shiftMP (u : ℝ) : MeasurePreserving (Draft.dfgwShift (S := S) u) P P :=
    ⟨measurable_shift u, hP.stationary u⟩
  let evalMP (u : ℝ) : MeasurePreserving (fun η : C(ℝ, S) => η u) P μ :=
    ⟨(continuous_eval_const u).measurable, hP.marginal u⟩
  let U (n : ℕ) : Lp ℝ 2 P := Lp.compMeasurePreserving _ (shiftMP (n • t : ℝ≥0)) Z
  let V (n : ℕ) : Lp ℝ 2 P := Lp.compMeasurePreserving _ (evalMP (n • t : ℝ≥0)) g
  have heq (n : ℕ) :
      (condExpL2 ℝ ℝ ((Draft.dfgwPast (S := S)).le (n • t)) (U n) : Lp ℝ 2 P) = V n := by
    let u : ℝ := (n • t : ℝ≥0)
    have hσ : Draft.dfgwCoordSigma (S := S) (Set.Iic u) ≤
        Draft.dfgwTrajectoryMeasurableSpace (S := S) := (Draft.dfgwPast (S := S)).le (n • t)
    have hcomp := EinsteinFull.condExp_map_comp (measurable_shift (S := S) u) hσ₀
      (show Integrable Z (P.map (Draft.dfgwShift u)) by
        rw [hP.stationary]; exact (Lp.memLp Z).integrable one_le_two)
    rw [hP.stationary, comap_shift_past u] at hcomp
    have hZ' := (shiftMP u).quasiMeasurePreserving.ae hZ
    have hcond : P[(Z : C(ℝ, S) → ℝ) ∘ Draft.dfgwShift u |
        Draft.dfgwCoordSigma (Set.Iic u)] =ᵐ[P] fun η => g (η u) := by
      filter_upwards [hcomp, hZ'] with η hc hz
      simpa only [Function.comp_apply, Draft.dfgwShift, ContinuousMap.coe_comp,
        ContinuousMap.coe_mk, zero_add] using hc.symm.trans hz
    have hmem := (Lp.memLp Z).comp_measurePreserving (shiftMP u)
    have hrep := Lp.coeFn_compMeasurePreserving Z (shiftMP u)
    have hU : hmem.toLp ((Z : C(ℝ, S) → ℝ) ∘ Draft.dfgwShift u) = U n := by
      apply Lp.ext
      exact (MemLp.coeFn_toLp hmem).trans hrep.symm
    have hc : (condExpL2 ℝ ℝ hσ (U n) : Lp ℝ 2 P) =ᵐ[P]
        P[(Z : C(ℝ, S) → ℝ) ∘ Draft.dfgwShift u |
          Draft.dfgwCoordSigma (Set.Iic u)] := by
      rw [← hU]
      exact hmem.condExpL2_ae_eq_condExp hσ
    have hv := Lp.coeFn_compMeasurePreserving g (evalMP u)
    apply Lp.ext
    exact hc.trans (hcond.trans hv.symm)
  have hinner (n : ℕ) : inner ℝ f (U n) = inner ℝ f (V n) := by
    have hsub : Draft.dfgwCoordSigma (S := S) (Set.Iic 0) ≤
        Draft.dfgwCoordSigma (Set.Iic ((n • t : ℝ≥0) : ℝ)) := by
      apply iSup₂_le
      intro u hu
      exact le_iSup₂_of_le (f := fun u (_ : u ∈ Set.Iic ((n • t : ℝ≥0) : ℝ)) =>
        MeasurableSpace.comap (fun η : C(ℝ, S) => η u) inferInstance) u
        (by change u ≤ ((n • t : ℝ≥0) : ℝ); have : u ≤ 0 := hu
            exact this.trans (NNReal.coe_nonneg _)) le_rfl
    calc
      inner ℝ f (U n) = inner ℝ (U n) f := real_inner_comm _ _
      _ = inner ℝ (condExpL2 ℝ ℝ ((Draft.dfgwPast (S := S)).le (n • t)) (U n) :
          Lp ℝ 2 P) f := (inner_condExpL2_eq_inner_fun _ (U n) f (hf.mono hsub)).symm
      _ = inner ℝ (V n) f := by rw [heq n]
      _ = inner ℝ f (V n) := real_inner_comm _ _
  have h := tendsto_inner_past_future_state_zero hP hμ 0 ht f hf g hg
  change Tendsto (fun n : ℕ => inner ℝ f (U n)) atTop (𝓝 0)
  have h' : Tendsto (fun n : ℕ => inner ℝ f (V n)) atTop (𝓝 0) := by
    simpa only [NNReal.coe_zero, add_zero] using h
  simpa only [hinner] using h'

end EinsteinFull.External.DFGW
