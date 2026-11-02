import EinsteinRelation.Correctors.CommonSpatialDivergence
import EinsteinRelation.Calculus.Weak

/-!
# Spatial weak divergence of stationary square-integrable fields

Source: `paper/main.tex:693-698`. Local integrability and a common event for
all smooth tests give the literal samplewise weak-divergence predicate.
-/

open MeasureTheory

noncomputable section

namespace EinsteinRelation.Correctors.SpatialDivergence

open StationarySpatialRealization StationaryCurlRealization

/-- Fixed-test vanishing for a stationary L² field yields a full spatial
weak-divergence equation on one common full-measure event. -/
theorem ae_hasWeakDivergence_of_ae_fixedTest {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q] (hQ : IsStationary Q)
    (W : Lp (EuclideanSpace ℝ (Fin d)) 2 Q)
    (hfixed : ∀ ψ : SpatialTest d, ∀ᵐ ω ∂Q,
      (∫ x : Vec d, ∑ j : Fin d,
        coordinateDerivative j ψ x * (W (translate x ω)).ofLp j ∂volume) = 0) :
    ∀ᵐ ω ∂Q, HasWeakDivergence Set.univ
      (fun x : Vec d => (W (translate x ω)).ofLp) (fun _ => 0) := by
  filter_upwards [ae_spatialRealization_memLp_on_all_compacts hQ W,
    ae_allTests_of_ae_fixedTest Q hQ W hfixed] with ω hω htests
  refine ⟨fun j => ?_, locallyIntegrableOn_zero, ?_⟩
  · apply LocallyIntegrable.locallyIntegrableOn
    rw [locallyIntegrable_iff]
    intro K hK
    letI : IsFiniteMeasure (volume.restrict K) :=
      (isFiniteMeasure_restrict).2 hK.measure_ne_top
    have hc := (PiLp.proj (p := 2) (𝕜 := ℝ) (β := fun _ : Fin d => ℝ) j).comp_memLp'
      (hω K hK)
    exact hc.integrable (by norm_num)
  · intro ψ hψ
    let test : SpatialTest d := ⟨ψ, hψ.1, hψ.2.1, Set.subset_univ _⟩
    have ht := htests test
    change (∫ x : Vec d, ∑ j : Fin d,
      coordinateDerivative j ψ x * (W (translate x ω)).ofLp j ∂volume) = 0 at ht
    simp only [Measure.restrict_univ, zero_mul, integral_zero, neg_zero, dot, gradient]
    convert ht using 1
    apply integral_congr_ae
    filter_upwards [] with x
    apply Finset.sum_congr rfl
    intro j _
    exact mul_comm _ _

end EinsteinRelation.Correctors.SpatialDivergence

