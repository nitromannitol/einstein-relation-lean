import EinsteinFull.External.DFGW.InvariantPast
import EinsteinFull.External.DFGW.ReflectionSigma

/-! # Future measurability of shift-invariant observables

Time reversal converts the past measurability of an invariant observable into future
measurability.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- An integrable observable invariant under all positive grid shifts is future measurable
up to a null set. -/
theorem aestronglyMeasurable_future_of_grid_invariant
    (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (hcoord : Draft.dfgwCoordSigma (S := S) Set.univ =
      Draft.dfgwTrajectoryMeasurableSpace (S := S))
    {t : ℝ≥0} (ht : 0 < t) (f : C(ℝ, S) → ℝ)
    (hf : Integrable f P) (hfm : StronglyMeasurable f)
    (hinv : ∀ n : ℕ, f ∘ Draft.dfgwShift (((n • t : ℝ≥0) : ℝ)) =ᵐ[P] f) :
    AEStronglyMeasurable[Draft.dfgwCoordSigma (Set.Ici 0)] f P := by
  let : IsProbabilityMeasure P := hP.probability
  let R := Draft.dfgwRefl (S := S) 0
  let hR : MeasurePreserving R P P := ⟨measurable_refl 0, hP.reversible 0⟩
  let F := f ∘ R
  have hFi : Integrable F P := hR.integrable_comp_of_integrable hf
  have hFm : StronglyMeasurable F := hfm.comp_measurable (measurable_refl 0)
  have hFinv (n : ℕ) : F ∘ Draft.dfgwShift (-((n • t : ℝ≥0) : ℝ)) =ᵐ[P] F := by
    have h := hR.quasiMeasurePreserving.ae (hinv n)
    filter_upwards [h] with η hη
    change f (R (Draft.dfgwShift (-((n • t : ℝ≥0) : ℝ)) η)) = f (R η)
    change f (Draft.dfgwRefl 0 (Draft.dfgwShift (-((n • t : ℝ≥0) : ℝ)) η)) =
      f (Draft.dfgwRefl 0 η)
    rw [refl_zero_shift]
    simpa only [Function.comp_apply, neg_neg] using hη
  obtain ⟨v, hv, hvEq⟩ := aestronglyMeasurable_past_of_grid_invariant
    hP hcoord ht F hFi hFm hFinv
  have hvfuture : StronglyMeasurable[Draft.dfgwCoordSigma (Set.Ici 0)] (v ∘ R) := by
    have h : StronglyMeasurable[MeasurableSpace.comap R (Draft.dfgwCoordSigma (Set.Iic 0))]
        (v ∘ R) := hv.comp_measurable (comap_measurable R)
    rwa [comap_refl_past] at h
  refine ⟨v ∘ R, hvfuture, ?_⟩
  have heq := hR.quasiMeasurePreserving.ae hvEq
  filter_upwards [heq] with η hη
  change f (Draft.dfgwRefl 0 (Draft.dfgwRefl 0 η)) = v (Draft.dfgwRefl 0 η) at hη
  change f η = v (Draft.dfgwRefl 0 η)
  rwa [refl_zero_involutive η] at hη

end EinsteinFull.External.DFGW
