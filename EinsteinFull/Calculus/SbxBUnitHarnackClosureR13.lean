import EinsteinFull.Calculus.SbxBSmallPowerLocalMaxR12
import EinsteinFull.Calculus.SbxBPointwiseHarnackScalingR12

open EinsteinRelation MeasureTheory EinsteinFull.External.Source.GMP
open scoped ENNReal

namespace EinsteinFull.Calculus

/-- The literal native weak Harnack estimate implies unit pointwise Harnack;
its exponent and constant are uniform over coefficients and solutions. -/
theorem b_unit_pointwise_harnack_of_native_weak_r13 (d : ℕ) (hd : 2 ≤ d)
    (κ : ℝ) (hκ : 0 < κ)
    (hweak : ∃ p C : ℝ, 0 < p ∧ 0 < C ∧
      ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d), IsUniformlyElliptic κ ρ α →
      ∀ (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d),
      IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1) u G →
      (∀ᵐ z ∂volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1), 0 ≤ u z) →
      eLpNorm u (ENNReal.ofReal p)
        (volume.restrict (Set.Ioo (-3/4 : ℝ) (-1/2) ×ˢ sourceBall 0 (1/2))) ≤
      ENNReal.ofReal C * essInf (fun z : ℝ × Vec d => ENNReal.ofReal (u z))
        (volume.restrict (Set.Ioo (1/2 : ℝ) (3/4) ×ˢ sourceBall 0 (1/2)))) :
    BUnitPointwiseHarnack d κ := by
  obtain ⟨p, C, hp, hC, hweak⟩ := hweak
  obtain ⟨A, hA, hmax⟩ := b_small_power_pointwise_local_max_r12 d hd κ p hκ hp
  refine ⟨A * C, mul_pos hA hC, ?_⟩
  intro ρ α hell u G hcal hearly hlate hu x hx y hy hy0
  have hy' := (b_continuous_ess_bounds _ (isOpen_Ioo.prod (c17_isOpen_sourceBall _ _))
    u hlate y hy).1
  have hbound : ENNReal.ofReal (u x) ≤ ENNReal.ofReal (A * C) * ENNReal.ofReal (u y) := by
    calc
      ENNReal.ofReal (u x) ≤ _ := hmax ρ α hell u G hcal hu hearly x hx
      _ ≤ ENNReal.ofReal A * (ENNReal.ofReal C * ENNReal.ofReal (u y)) :=
        mul_le_mul_right ((hweak ρ α hell u G hcal hu).trans (mul_le_mul_right hy' _)) _
      _ = _ := by rw [← mul_assoc, ← ENNReal.ofReal_mul hA.le]
  rw [← ENNReal.ofReal_mul (mul_pos hA hC).le] at hbound
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (mul_pos hA hC).le hy0)).mp hbound

#print axioms b_unit_pointwise_harnack_of_native_weak_r13

end EinsteinFull.Calculus
