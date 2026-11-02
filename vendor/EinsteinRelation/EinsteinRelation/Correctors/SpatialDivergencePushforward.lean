import EinsteinRelation.Correctors.CommonSpatialDivergenceGeneral
import EinsteinRelation.Calculus.SpatialPropertyPushforward

/-!
# Weak divergence under a measurable parameter map

Source: `paper/main.tex:693-702`. Fixed smooth-test integral events are
measurable. Local L² and countable density recover all tests after mapping.
-/
open MeasureTheory
namespace EinsteinRelation.Correctors
open StationaryCurlRealization

/-- Zero weak divergence transfers through measurable fixed-test events. -/
theorem ae_weakDivergence_zero_of_pullback {d : ℕ} {A B : Type*}
    [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure B) (π : B → A) (hπ : Measurable π)
    (F : A → Vec d → Vec d)
    (hF : Measurable (fun p : A × Vec d => F p.1 p.2))
    (hlocal : ∀ᵐ b ∂μ, ∀ K : Set (Vec d), IsCompact K →
      MemLp (F (π b)) 2 (volume.restrict K))
    (hweak : ∀ᵐ b ∂μ, HasWeakDivergence Set.univ (F (π b)) (fun _ => 0)) :
    ∀ᵐ a ∂Measure.map π μ, HasWeakDivergence Set.univ (F a) (fun _ => 0) := by
  have hloc := ae_local_square_integrable_of_pullback μ π hπ F hF hlocal
  have hfixed (ψ : SpatialTest d) : ∀ᵐ a ∂Measure.map π μ,
      (∫ x : Vec d, ∑ j : Fin d, coordinateDerivative j ψ x * F a x j ∂volume) = 0 := by
    have hm : Measurable (fun a => ∫ x : Vec d,
        ∑ j : Fin d, coordinateDerivative j ψ x * F a x j ∂volume) := by
      apply StronglyMeasurable.measurable
      apply StronglyMeasurable.integral_prod_right
      apply Measurable.stronglyMeasurable
      apply Finset.measurable_sum
      intro j _
      have hd : Continuous (coordinateDerivative j ψ) :=
        (ψ.contDiff.continuous_fderiv (by simp)).clm_apply continuous_const
      exact (hd.measurable.comp measurable_snd).mul ((measurable_pi_apply j).comp hF)
    apply (ae_map_iff hπ.aemeasurable (measurableSet_eq_fun hm measurable_const)).mpr
    filter_upwards [hweak] with b hb
    have he := hb.2.2 ψ ⟨ψ.contDiff, ψ.hasCompactSupport, Set.subset_univ _⟩
    simp only [Measure.restrict_univ, zero_mul, integral_zero, neg_zero, dot, gradient] at he
    convert he using 1
    apply integral_congr_ae
    exact ae_of_all _ fun x => Finset.sum_congr rfl fun j _ => mul_comm _ _
  have hall := SpatialDivergenceGeneral.ae_allTests_of_ae_fixedTest
    (Measure.map π μ) F hloc hfixed
  filter_upwards [hloc, hall] with a ha ht
  refine ⟨fun j => ?_, locallyIntegrableOn_zero, ?_⟩
  · rw [locallyIntegrableOn_univ, locallyIntegrable_iff]
    intro K hK
    letI : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.mpr hK.measure_ne_top
    exact ((ContinuousLinearMap.proj j : Vec d →L[ℝ] ℝ).comp_memLp'
      (ha K hK)).integrable (by norm_num)
  · intro φ hφ
    have he := ht ⟨φ, hφ.1, hφ.2.1, Set.subset_univ _⟩
    simp only [Measure.restrict_univ, zero_mul, integral_zero, neg_zero, dot, gradient]
    convert he using 1
    apply integral_congr_ae
    exact ae_of_all _ fun x => Finset.sum_congr rfl fun j _ => mul_comm _ _

end EinsteinRelation.Correctors
