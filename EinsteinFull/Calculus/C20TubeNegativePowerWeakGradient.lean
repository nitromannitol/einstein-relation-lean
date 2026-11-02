import EinsteinFull.Calculus.C13TubeWeakGradientChain
import EinsteinFull.Calculus.C13TubeNativeC2Energy
import EinsteinFull.Calculus.C20TubeNegativePowerExtension
import EinsteinFull.Calculus.C9TubeWeightedZeroPast
import EinsteinRelation.Correctors.SpatialWeakCongruence
import EinsteinRelation.Correctors.WeakGradientCentering
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

open EinsteinRelation MeasureTheory Filter EinsteinFull.External.Source.GMP
open PDE hiding Vec Mat
open scoped Topology

namespace EinsteinFull.Calculus

/-- A bounded smooth extension transfers the literal negative-power chain rule. -/
@[nolint unusedArguments]
theorem c20_native_weak_gradient_negative_power
    {d : ℕ} {U : Set (Vec d)} (hU : IsOpen U)
    {ε p : ℝ} (hε : 0 < ε) (hp : 0 < p)
    (F : ℝ → ℝ) (c M : ℝ) (hF : ContDiff ℝ 1 F) (hF0 : F 0 = 0)
    (hM : 0 ≤ M) (hdF : ∀ x, |deriv F x| ≤ M)
    (hval : ∀ x, ε ≤ x → F x = Real.rpow x (-p) - c)
    (hder : ∀ x, ε ≤ x → deriv F x = -p * Real.rpow x (-p-1))
    (u : Vec d → ℝ) (G : Vec d → Vec d)
    (hu : MemLp u 2 (volume.restrict U))
    (hG : MemLp (fun x => euclideanNorm (G x)) 2 (volume.restrict U))
    (hw : HasWeakGradient U u G)
    (hpos : ∀ᵐ x ∂volume.restrict U, ε ≤ u x) :
    MemLp (fun x => Real.rpow (u x) (-p) - c) 2 (volume.restrict U) ∧
    MemLp (fun x => euclideanNorm ((-p * Real.rpow (u x) (-p-1)) • G x)) 2 (volume.restrict U) ∧
    HasWeakGradient U (fun x => Real.rpow (u x) (-p) - c)
      (fun x => (-p * Real.rpow (u x) (-p-1)) • G x) := by
  have hc := c13_native_weak_gradient_bounded_C1_chain hU u G hu hG hw F hF hF0 M hM hdF
  have hv : (fun x => F (u x)) =ᵐ[volume.restrict U]
      (fun x => Real.rpow (u x) (-p) - c) := by
    filter_upwards [hpos] with x hx
    exact hval (u x) hx
  have hg : (fun x => deriv F (u x) • G x) =ᵐ[volume.restrict U]
      (fun x => (-p * Real.rpow (u x) (-p-1)) • G x) := by
    filter_upwards [hpos] with x hx
    rw [hder (u x) hx]
  exact ⟨(memLp_congr_ae hv).mp hc.1,
    (memLp_congr_ae (hg.mono fun _ h => congrArg euclideanNorm h)).mp hc.2.1,
    Correctors.hasWeakGradient_congr_ae hU hc.2.2 hv hg⟩

/-- The same chain rule applies to almost every spatial slice of a weighted caloric function. -/
@[nolint unusedArguments]
theorem c20_weighted_caloric_negative_power_gradient_slices
    {d : ℕ} {I : Set ℝ} {U : Set (Vec d)} [IsFiniteMeasure (volume.restrict U)]
    (hU : IsOpen U) {ε p : ℝ} (hε : 0 < ε) (hp : 0 < p)
    (F : ℝ → ℝ) (c M : ℝ) (hF : ContDiff ℝ 1 F) (hF0 : F 0 = 0)
    (hM : 0 ≤ M) (hdF : ∀ x, |deriv F x| ≤ M)
    (hval : ∀ x, ε ≤ x → F x = Real.rpow x (-p) - c)
    (hder : ∀ x, ε ≤ x → deriv F x = -p * Real.rpow x (-p-1))
    (ρ : Vec d → ℝ) (α : Vec d → Mat d)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hcal : IsWeightedCaloric ρ α I U u G)
    (hpos : ∀ᵐ z ∂volume.restrict (I ×ˢ U), ε ≤ u z) :
    ∀ᵐ t ∂volume.restrict I,
      MemLp (fun x => Real.rpow (u (t, x)) (-p) - c) 2 (volume.restrict U) ∧
      MemLp (fun x => euclideanNorm ((-p * Real.rpow (u (t, x)) (-p-1)) • G (t, x))) 2 (volume.restrict U) ∧
      HasWeakGradient U (fun x => Real.rpow (u (t, x)) (-p) - c)
        (fun x => (-p * Real.rpow (u (t, x)) (-p-1)) • G (t, x)) := by
  have hu : MemLp u 2 ((volume.restrict I).prod (volume.restrict U)) := by
    rw [Measure.prod_restrict]
    exact hcal.1
  have hG : MemLp (fun z => euclideanNorm (G z)) 2
      ((volume.restrict I).prod (volume.restrict U)) := by
    rw [Measure.prod_restrict]
    exact hcal.2.2.1
  have hpos' : ∀ᵐ z ∂(volume.restrict I).prod (volume.restrict U), ε ≤ u z := by
    rw [Measure.prod_restrict]
    exact hpos
  filter_upwards [c9_memLp_prod_right_ae _ _ _ hu,
    c9_memLp_prod_right_ae _ _ _ hG, hcal.2.2.2.1,
    Measure.ae_ae_of_ae_prod hpos'] with t hut hGt hwt hpt
  exact c20_native_weak_gradient_negative_power hU hε hp F c M hF hF0 hM hdF
    hval hder _ _ hut hGt hwt hpt

/-- Removing the normalization constant preserves the literal weak gradient. -/
theorem c20_native_weak_gradient_negative_power_literal
    {d : ℕ} {U : Set (Vec d)} (hU : IsOpen U)
    {ε p : ℝ} (hε : 0 < ε) (hp : 0 < p)
    (F : ℝ → ℝ) (c M : ℝ) (hF : ContDiff ℝ 1 F) (hF0 : F 0 = 0)
    (hM : 0 ≤ M) (hdF : ∀ x, |deriv F x| ≤ M)
    (hval : ∀ x, ε ≤ x → F x = Real.rpow x (-p) - c)
    (hder : ∀ x, ε ≤ x → deriv F x = -p * Real.rpow x (-p-1))
    (u : Vec d → ℝ) (G : Vec d → Vec d)
    (hu : MemLp u 2 (volume.restrict U))
    (hG : MemLp (fun x => euclideanNorm (G x)) 2 (volume.restrict U))
    (hw : HasWeakGradient U u G)
    (hpos : ∀ᵐ x ∂volume.restrict U, ε ≤ u x) :
    HasWeakGradient U (fun x => Real.rpow (u x) (-p))
      (fun x => (-p * Real.rpow (u x) (-p-1)) • G x) := by
  have h := (c20_native_weak_gradient_negative_power hU hε hp F c M hF hF0 hM hdF
    hval hder u G hu hG hw hpos).2.2
  have hc := Correctors.hasWeakGradient_sub_const U h (-c)
  simpa only [sub_neg_eq_add, sub_add_cancel] using hc

/-- Almost every weighted-caloric slice has the literal negative-power gradient. -/
theorem c20_weighted_caloric_negative_power_gradient_slices_literal
    {d : ℕ} {I : Set ℝ} {U : Set (Vec d)} [IsFiniteMeasure (volume.restrict U)]
    (hU : IsOpen U) {ε p : ℝ} (hε : 0 < ε) (hp : 0 < p)
    (F : ℝ → ℝ) (c M : ℝ) (hF : ContDiff ℝ 1 F) (hF0 : F 0 = 0)
    (hM : 0 ≤ M) (hdF : ∀ x, |deriv F x| ≤ M)
    (hval : ∀ x, ε ≤ x → F x = Real.rpow x (-p) - c)
    (hder : ∀ x, ε ≤ x → deriv F x = -p * Real.rpow x (-p-1))
    (ρ : Vec d → ℝ) (α : Vec d → Mat d)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hcal : IsWeightedCaloric ρ α I U u G)
    (hpos : ∀ᵐ z ∂volume.restrict (I ×ˢ U), ε ≤ u z) :
    ∀ᵐ t ∂volume.restrict I,
      HasWeakGradient U (fun x => Real.rpow (u (t, x)) (-p))
        (fun x => (-p * Real.rpow (u (t, x)) (-p-1)) • G (t, x)) := by
  filter_upwards [c20_weighted_caloric_negative_power_gradient_slices hU hε hp F c M
    hF hF0 hM hdF hval hder ρ α u G hcal hpos] with t ht
  have hc := Correctors.hasWeakGradient_sub_const U ht.2.2 (-c)
  simpa only [sub_neg_eq_add, sub_add_cancel] using hc

/-- The normalized negative power and its literal gradient are square integrable
on the full weighted-caloric cylinder. -/
theorem c20_weighted_caloric_negative_power_memLp
    {d : ℕ} {I : Set ℝ} {U : Set (Vec d)} {ε p : ℝ}
    (F : ℝ → ℝ) (c M : ℝ) (hF : ContDiff ℝ 1 F) (hF0 : F 0 = 0)
    (hM : 0 ≤ M) (hdF : ∀ x, |deriv F x| ≤ M)
    (hval : ∀ x, ε ≤ x → F x = Real.rpow x (-p) - c)
    (hder : ∀ x, ε ≤ x → deriv F x = -p * Real.rpow x (-p-1))
    (ρ : Vec d → ℝ) (α : Vec d → Mat d)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hcal : IsWeightedCaloric ρ α I U u G)
    (hpos : ∀ᵐ z ∂volume.restrict (I ×ˢ U), ε ≤ u z) :
    MemLp (fun z => Real.rpow (u z) (-p) - c) 2 (volume.restrict (I ×ˢ U)) ∧
    MemLp (fun z => euclideanNorm ((-p * Real.rpow (u z) (-p-1)) • G z))
      2 (volume.restrict (I ×ˢ U)) := by
  have hlip := PDE.lipschitzWith_of_abs_deriv_le hM
    (hF.differentiable (by norm_num)) hdF
  have hf : MemLp (fun z => F (u z)) 2 (volume.restrict (I ×ˢ U)) :=
    hlip.comp_memLp hF0 hcal.1
  have hv : (fun z => F (u z)) =ᵐ[volume.restrict (I ×ˢ U)]
      (fun z => Real.rpow (u z) (-p) - c) := by
    filter_upwards [hpos] with z hz
    exact hval (u z) hz
  refine ⟨(memLp_congr_ae hv).mp hf, ?_⟩
  have hc : Continuous (deriv F) := hF.continuous_deriv (by norm_num)
  have hcoef := hc.comp_aestronglyMeasurable hcal.1.aestronglyMeasurable
  have hnorm := hcoef.norm.mul hcal.2.2.1.aestronglyMeasurable
  have hg : MemLp (fun z => euclideanNorm (deriv F (u z) • G z))
      2 (volume.restrict (I ×ˢ U)) := by
    apply (hcal.2.2.1.const_mul M).mono' ?_
    · filter_upwards with z
      simp only [Real.norm_eq_abs, TimeChange.euclideanNorm_smul]
      have hG : 0 ≤ euclideanNorm (G z) := by
        rw [TimeChange.euclideanNorm_eq_norm_toLp]; positivity
      rw [abs_of_nonneg (mul_nonneg (abs_nonneg _) hG)]
      exact mul_le_mul_of_nonneg_right (hdF (u z)) hG
    · convert hnorm using 1 <;> ext z <;> simp [TimeChange.euclideanNorm_smul, Real.norm_eq_abs]
  have heq : (fun z => euclideanNorm (deriv F (u z) • G z))
      =ᵐ[volume.restrict (I ×ˢ U)]
      (fun z => euclideanNorm ((-p * Real.rpow (u z) (-p-1)) • G z)) := by
    filter_upwards [hpos] with z hz
    rw [hder (u z) hz]
  exact (memLp_congr_ae heq).mp hg

/-- A positive caloric function has the literal negative-power weak gradient. -/
theorem c20_weighted_caloric_negative_power_gradient_slices_unconditional
    {d : ℕ} {I : Set ℝ} {U : Set (Vec d)} [IsFiniteMeasure (volume.restrict U)]
    (hU : IsOpen U) {ε p : ℝ} (hε : 0 < ε) (hp : 0 < p)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hcal : IsWeightedCaloric ρ α I U u G)
    (hpos : ∀ᵐ z ∂volume.restrict (I ×ˢ U), ε ≤ u z) :
    ∀ᵐ t ∂volume.restrict I,
      HasWeakGradient U (fun x => Real.rpow (u (t, x)) (-p))
        (fun x => (-p * Real.rpow (u (t, x)) (-p-1)) • G (t, x)) := by
  obtain ⟨F, c, M, hF, hF0, hM, hb, hval, hder, _⟩ :=
    c20_negative_power_normalized_extension ε p hε hp
  exact c20_weighted_caloric_negative_power_gradient_slices_literal hU hε hp F c M
    (hF.of_le (by norm_num)) hF0 hM (fun x => (hb x).1) hval hder ρ α u G hcal hpos

/-- The normalized negative power and its gradient are square integrable
on the caloric cylinder, for a constant depending only on the scalar extension. -/
theorem c20_weighted_caloric_negative_power_memLp_unconditional
    {d : ℕ} {I : Set ℝ} {U : Set (Vec d)} {ε p : ℝ}
    (hε : 0 < ε) (hp : 0 < p)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hcal : IsWeightedCaloric ρ α I U u G)
    (hpos : ∀ᵐ z ∂volume.restrict (I ×ˢ U), ε ≤ u z) :
    ∃ c : ℝ,
      MemLp (fun z => Real.rpow (u z) (-p) - c) 2 (volume.restrict (I ×ˢ U)) ∧
      MemLp (fun z => euclideanNorm ((-p * Real.rpow (u z) (-p-1)) • G z))
        2 (volume.restrict (I ×ˢ U)) := by
  obtain ⟨F, c, M, hF, hF0, hM, hb, hval, hder, _⟩ :=
    c20_negative_power_normalized_extension ε p hε hp
  exact ⟨c, c20_weighted_caloric_negative_power_memLp F c M
    (hF.of_le (by norm_num)) hF0 hM (fun x => (hb x).1) hval hder ρ α u G hcal hpos⟩

/-- One normalization constant supplies both cylinder bounds and slice gradients. -/
theorem c20_weighted_caloric_negative_power_receipt
    {d : ℕ} {I : Set ℝ} {U : Set (Vec d)} [IsFiniteMeasure (volume.restrict U)]
    (hU : IsOpen U) {ε p : ℝ} (hε : 0 < ε) (hp : 0 < p)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hcal : IsWeightedCaloric ρ α I U u G)
    (hpos : ∀ᵐ z ∂volume.restrict (I ×ˢ U), ε ≤ u z) :
    ∃ c : ℝ,
      MemLp (fun z => Real.rpow (u z) (-p) - c) 2 (volume.restrict (I ×ˢ U)) ∧
      MemLp (fun z => euclideanNorm ((-p * Real.rpow (u z) (-p-1)) • G z))
        2 (volume.restrict (I ×ˢ U)) ∧
      ∀ᵐ t ∂volume.restrict I,
        MemLp (fun x => Real.rpow (u (t, x)) (-p) - c) 2 (volume.restrict U) ∧
        MemLp (fun x => euclideanNorm ((-p * Real.rpow (u (t, x)) (-p-1)) • G (t, x)))
          2 (volume.restrict U) ∧
        HasWeakGradient U (fun x => Real.rpow (u (t, x)) (-p))
          (fun x => (-p * Real.rpow (u (t, x)) (-p-1)) • G (t, x)) := by
  obtain ⟨F, c, M, hF, hF0, hM, hb, hval, hder, _⟩ :=
    c20_negative_power_normalized_extension ε p hε hp
  have hF1 : ContDiff ℝ 1 F := hF.of_le (by norm_num)
  have hdF : ∀ x, |deriv F x| ≤ M := fun x => (hb x).1
  have hc := c20_weighted_caloric_negative_power_memLp F c M hF1 hF0 hM hdF
    hval hder ρ α u G hcal hpos
  refine ⟨c, hc.1, hc.2, ?_⟩
  filter_upwards [c20_weighted_caloric_negative_power_gradient_slices hU hε hp F c M
    hF1 hF0 hM hdF hval hder ρ α u G hcal hpos] with t ht
  have h := Correctors.hasWeakGradient_sub_const U ht.2.2 (-c)
  exact ⟨ht.1, ht.2.1, by simpa only [sub_neg_eq_add, sub_add_cancel] using h⟩

/-- The actual smooth negative-power extension satisfies the C2 energy identity. -/
theorem c20_negative_power_continuous_energy
    {d : ℕ} {κ R a b ε p : ℝ} (hκ : 0 < κ) (hR : 0 < R) (hab : a < b)
    (hε : 0 < ε) (hp : 0 < p)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d) (hell : IsUniformlyElliptic κ ρ α)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hcal : IsWeightedCaloric ρ α (Set.Ioo a b) (sourceBall 0 R) u G)
    (χ : Vec d → ℝ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hχc : HasCompactSupport χ) (hχU : tsupport χ ⊆ sourceBall 0 R) :
    ∃ F : ℝ → ℝ, ∃ c : ℝ,
      (∀ x, ε ≤ x → F x = Real.rpow x (-p) - c) ∧
      (∀ x, ε ≤ x → deriv F x = -p * Real.rpow x (-p-1)) ∧
      (∀ x, ε ≤ x → deriv (deriv F) x = p*(p+1)*Real.rpow x (-p-2)) ∧
      ∃ E : ℝ → ℝ, ContinuousOn E (Set.Ioo a b) ∧
        (∀ᵐ t ∂volume.restrict (Set.Ioo a b),
          E t = ∫ x in sourceBall 0 R, ρ x * χ x ^ 2 * F (u (t,x))) ∧
        ∀ s ∈ Set.Ioo a b, ∀ t ∈ Set.Ioo a b,
          E t - E s = -(∫ r in s..t, ∫ x in sourceBall 0 R,
            χ x ^ 2 * deriv (deriv F) (u (r,x)) *
              dot ((α x).mulVec (G (r,x))) (G (r,x)) +
            2 * χ x * deriv F (u (r,x)) * dot ((α x).mulVec (G (r,x)))
              (fun j => fderiv ℝ χ x (unitVector j))) := by
  obtain ⟨F, c, M, hF, hF0, hM, hb, hval, hder, hder2⟩ :=
    c20_negative_power_normalized_extension ε p hε hp
  refine ⟨F, c, hval, hder, hder2, ?_⟩
  exact c13_actual_weighted_C2_continuous_energy hκ hR hab ρ α hell u G hcal
    F hF hF0 M hM (fun r => (hb r).2) χ hχ hχc hχU

end EinsteinFull.Calculus
