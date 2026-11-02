import EinsteinRelation.Correctors.CommonScalarOrbitTests
import EinsteinRelation.Correctors.ScalarOrbitLocalL2
import EinsteinRelation.Calculus.WeakRepresentativeOperations

/-!
# Spatial weak gradients of horizontal H¹ observables

Source: `paper/main.tex:240-248,693-698`. The scalar orbit and its actual
horizontal gradient satisfy the weak equation simultaneously for every
spatial test, on one full-measure event.
-/

open MeasureTheory

namespace EinsteinRelation.Correctors

/-- The literal scalar orbit of a horizontal H¹ observable has its actual
Euclidean horizontal gradient as samplewise weak gradient. -/
theorem ae_horizontalH1_hasWeakGradient_orbit {d : ℕ} [Fact (2 ≤ d)]
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q] (hQ : IsStationary Q)
    (f : horizontalH1 Q hQ) :
    ∀ᵐ ω ∂Q, HasWeakGradient Set.univ
      (fun x => (f : Lp ℝ 2 Q) (translate x ω))
      (fun x => (horizontalEuclideanGradient Q hQ f (translate x ω)).ofLp) := by
  have hc (i : Fin d) : ∀ᵐ ω ∂Q, HasWeakPartialDerivative Set.univ i
      (fun x => (f : Lp ℝ 2 Q) (translate x ω))
      (fun x => horizontalH1Gradient Q hQ f i (translate x ω)) := by
    apply SpatialScalar.ae_hasWeakPartialDerivative_of_ae_fixedTest Q _ _ i
    · filter_upwards [ae_scalar_orbit_memLp_on_all_compacts Q hQ (f : Lp ℝ 2 Q),
        ae_scalar_orbit_memLp_on_all_compacts Q hQ (horizontalH1Gradient Q hQ f i)]
        with ω hf hg
      exact fun K hK => ⟨hf K hK, hg K hK⟩
    · exact ae_horizontalH1_orbit_weak_test Q hQ f i
  have hrep (i : Fin d) : ∀ᵐ ω ∂Q, ∀ᵐ x ∂(volume : Measure (Vec d)),
      (horizontalEuclideanGradient Q hQ f (translate x ω)).ofLp i =
        horizontalH1Gradient Q hQ f i (translate x ω) := by
    have h : ∀ᵐ x ∂(volume : Measure (Vec d)), ∀ᵐ ω ∂Q,
        (horizontalEuclideanGradient Q hQ f (translate x ω)).ofLp i =
          horizontalH1Gradient Q hQ f i (translate x ω) :=
      ae_of_all _ fun x => (measurePreserving_translate Q hQ x).quasiMeasurePreserving.ae
        (horizontalEuclideanGradient_coordinates Q hQ f i)
    apply (Measure.ae_ae_comm ?_).mp h
    exact measurableSet_eq_fun
      (((PiLp.proj (p := 2) (𝕜 := ℝ) (β := fun _ : Fin d => ℝ) i).continuous.measurable.comp
        (Lp.stronglyMeasurable (horizontalEuclideanGradient Q hQ f)).measurable).comp
          Probability.continuous_translate.measurable)
      ((Lp.stronglyMeasurable (horizontalH1Gradient Q hQ f i)).measurable.comp
        Probability.continuous_translate.measurable)
  filter_upwards [ae_all_iff.mpr hc, ae_all_iff.mpr hrep] with ω hcω hrω
  intro i
  apply (hcω i).congr_ae (ae_eq_refl _)
  rw [Measure.restrict_univ]
  filter_upwards [hrω i] with x hx
  exact hx.symm

end EinsteinRelation.Correctors
