import EinsteinFull.Calculus.U2GMPKernelReversibility
import EinsteinRelation.Diffusion.FellerKernelUniquenessSupport

open EinsteinRelation MeasureTheory ProbabilityTheory Filter
open EinsteinRelation.External.GantertSection7Support
open scoped NNReal ENNReal

namespace EinsteinFull

/-- Each given Lebesgue-null set is missed at almost every starting point. -/
theorem u2_gmpPhysicalC0KernelSemigroup_null_set_ae {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (hSmooth : IsSmoothFieldPair ω) (t : ℝ≥0)
    (N : Set (Vec d)) (hN : MeasurableSet N)
    (hzero : (volume : Measure (Vec d)) N = 0) :
    ∀ᵐ x ∂(volume : Measure (Vec d)),
      Blueprint.gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth t x N = 0 := by
  let μ := physicalReversibleMeasure ω hd lam
  let K := Blueprint.gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth t
  have hμzero : μ N = 0 := (withDensity_absolutelyContinuous _ _) hzero
  have hvol : (volume : Measure (Vec d)) ≪ μ :=
    withDensity_absolutelyContinuous'
      (physicalReversibleDensity_continuous ω hd lam).measurable.ennreal_ofReal.aemeasurable
      (ae_of_all _ fun x => (ENNReal.ofReal_pos.mpr
        (physicalReversibleDensity_pos ω hd lam x)).ne')
  have hi : (∫⁻ x, K x N ∂μ) = 0 := by
    rw [← Measure.bind_apply hN K.aemeasurable]
    change (K ∘ₘ μ) N = 0
    rw [u2_gmpPhysicalC0KernelSemigroup_invariant hd ω lam Λ hΛ hω hSmooth t]
    exact hμzero
  have hae := (lintegral_eq_zero_iff (Kernel.measurable_coe K hN)).mp hi
  exact hvol.ae_le hae

#print axioms u2_gmpPhysicalC0KernelSemigroup_null_set_ae

end EinsteinFull
