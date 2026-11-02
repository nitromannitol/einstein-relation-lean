import EinsteinFull.Calculus.SbxBUnitPointwiseHarnackR12

open EinsteinRelation MeasureTheory EinsteinFull.External.Source.GMP
open scoped ENNReal

namespace EinsteinFull.Calculus

/-- The local maximum estimate at every positive exponent, for a continuous
representative of a nonnegative weighted-caloric function. -/
theorem b_small_power_pointwise_local_max_r12 (d : ℕ) (hd : 2 ≤ d)
    (κ p : ℝ) (hκ : 0 < κ) (hp : 0 < p) :
    ∃ A : ℝ, 0 < A ∧ ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
      IsUniformlyElliptic κ ρ α →
      ∀ (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d),
      IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1) u G →
      (∀ᵐ z ∂volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1), 0 ≤ u z) →
      ContinuousOn u (Set.Ioo (-11/16 : ℝ) (-9/16) ×ˢ sourceBall 0 (1/4)) →
      ∀ z ∈ Set.Ioo (-11/16 : ℝ) (-9/16) ×ˢ sourceBall 0 (1/4),
      ENNReal.ofReal (u z) ≤ ENNReal.ofReal A * eLpNorm u (ENNReal.ofReal p)
        (volume.restrict (Set.Ioo (-3/4 : ℝ) (-1/2) ×ˢ sourceBall 0 (1/2))) := by
  obtain ⟨A, hA, hmax⟩ := b_unit_local_max_positive_power d hd κ p hκ hp
  refine ⟨A, hA, ?_⟩
  intro ρ α hell u G hcal _ hc z hz
  exact ((b_continuous_ess_bounds _ (isOpen_Ioo.prod (c17_isOpen_sourceBall _ _))
    u hc z hz).2).trans (hmax ρ α hell u G hcal)

#print axioms b_small_power_pointwise_local_max_r12

end EinsteinFull.Calculus
