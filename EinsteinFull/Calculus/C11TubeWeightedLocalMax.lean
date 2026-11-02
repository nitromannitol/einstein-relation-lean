import EinsteinFull.Calculus.C17TubeTimeShiftedLocalMax
import EinsteinFull.Calculus.C18TubeCaloricTimeTranslation
import EinsteinFull.Calculus.C13TubeMoserEssentialBound
import EinsteinFull.Calculus.C17TubeMoserConstants
import EinsteinFull.Calculus.C20TubePositivePowerNormLimit
import EinsteinFull.External.Source.GMPDirichletKernel
import EllipticRegularity.Parabolic.LocalMax.PowerStepCore
import EllipticRegularity.Parabolic.LocalMax.PowerStep
import EllipticRegularity.Parabolic.LocalMax.EnergyLebesgueENN
import EllipticRegularity.Parabolic.LocalMax.EnergyTest
import EllipticRegularity.Parabolic.Chain.TimeChain
import EllipticRegularity.Parabolic.LocalMax.EnergyPointwise
import EinsteinFull.Calculus.ParabolicBridgeCoeff
import EinsteinFull.Calculus.C13TubeWeakGradientChain
import EinsteinFull.Calculus.C8TubeWeightedParabolicSobolev
import EinsteinFull.Calculus.C5TubeWeightedSquareBalance
import EinsteinFull.Calculus.C13TubeEnergyEndpoints
import EinsteinFull.Calculus.C20TubeWeightedNonlinearEnergyLimit
import EinsteinFull.Calculus.C20TubeRenormalizationConstantShift
import EinsteinRelation.Correctors.WeakGradientCentering
import EinsteinRelation.Regeneration.HalfSpaces
import Mathlib.MeasureTheory.Integral.Prod

open EinsteinRelation MeasureTheory EinsteinFull.External.Source.GMP
open scoped ENNReal Topology

namespace EinsteinFull.Calculus

/-- Spacetime L² data have L² spatial slices at almost every time. -/
theorem c11_memLp_spatial_slices {d : ℕ} {I : Set ℝ} {U : Set (Vec d)}
    {f : ℝ × Vec d → ℝ} (hf : MemLp f 2 (volume.restrict (I ×ˢ U))) :
    ∀ᵐ t ∂volume.restrict I, MemLp (fun x => f (t, x)) 2 (volume.restrict U) := by
  have hprod : MemLp f 2 ((volume.restrict I).prod (volume.restrict U)) := by
    rw [Measure.prod_restrict]
    exact hf
  have hm := hprod.aestronglyMeasurable.prodMk_left
  have hi := (hprod.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)).prod_right_ae
  filter_upwards [hm, hi] with t ht hti
  apply (integrable_norm_rpow_iff ht (by norm_num) (by norm_num)).mp
  simpa using hti

/-- The native weighted solution admits bounded C¹ spatial renormalization on
almost every time slice, with its actual weak gradient. -/
theorem c11_weighted_caloric_spatial_chain {d : ℕ}
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} {I : Set ℝ} {U : Set (Vec d)}
    (hU : IsOpen U) {u : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    (hu : IsWeightedCaloric ρ α I U u G) (F : ℝ → ℝ)
    (hF : ContDiff ℝ 1 F) (hF0 : F 0 = 0) (M : ℝ) (hM : 0 ≤ M)
    (hdF : ∀ r : ℝ, |deriv F r| ≤ M) :
    ∀ᵐ t ∂volume.restrict I,
      MemLp (fun x => F (u (t, x))) 2 (volume.restrict U) ∧
      MemLp (fun x => euclideanNorm (deriv F (u (t, x)) • G (t, x))) 2
        (volume.restrict U) ∧
      HasWeakGradient U (fun x => F (u (t, x)))
        (fun x => deriv F (u (t, x)) • G (t, x)) := by
  filter_upwards [c11_memLp_spatial_slices hu.1,
    c11_memLp_spatial_slices hu.2.2.1, hu.2.2.2.1] with t ht hG hw
  exact c13_native_weak_gradient_bounded_C1_chain hU _ _ ht hG hw F hF hF0 M hM hdF

/-- Bounded C¹ renormalization preserves the spacetime L² bounds of the
native weighted solution and its actual spatial chain-rule gradient. -/
theorem c11_weighted_caloric_spacetime_chain_memLp {d : ℕ}
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} {I : Set ℝ} {U : Set (Vec d)}
    {u : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    (hu : IsWeightedCaloric ρ α I U u G) (F : ℝ → ℝ)
    (hF : ContDiff ℝ 1 F) (hF0 : F 0 = 0) (M : ℝ) (hM : 0 ≤ M)
    (hdF : ∀ r : ℝ, |deriv F r| ≤ M) :
    MemLp (fun z => F (u z)) 2 (volume.restrict (I ×ˢ U)) ∧
    MemLp (fun z => euclideanNorm (deriv F (u z) • G z)) 2
      (volume.restrict (I ×ˢ U)) := by
  let μ := volume.restrict (I ×ˢ U)
  have hlip := PDE.lipschitzWith_of_abs_deriv_le hM (hF.differentiable (by simp)) hdF
  have hf : MemLp (fun z => F (u z)) 2 μ := by
    change MemLp (F ∘ u) 2 μ
    exact hlip.comp_memLp hF0 hu.1
  have hd : Continuous (deriv F) := hF.continuous_deriv_one
  have htop : MemLp (fun z => deriv F (u z)) ∞ μ := by
    apply memLp_top_of_bound (hd.comp_aestronglyMeasurable hu.1.aestronglyMeasurable) M
    exact Filter.Eventually.of_forall fun z => by simpa only [Real.norm_eq_abs] using hdF (u z)
  refine ⟨hf, ?_⟩
  have hm : MemLp (fun z => ‖deriv F (u z)‖ * euclideanNorm (G z)) 2 μ :=
    htop.norm.mul hu.2.2.1
  simpa only [Real.norm_eq_abs, TimeChange.euclideanNorm_smul] using hm

/-- On finite cylinders, bounded-derivative chains need not vanish at zero.
This includes the positive regularizations used in the Moser power family. -/
theorem c11_weighted_caloric_spacetime_chain_memLp_finite {d : ℕ}
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} {I : Set ℝ} {U : Set (Vec d)}
    {u : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    (hu : IsWeightedCaloric ρ α I U u G) (hfinite : volume (I ×ˢ U) < ∞)
    (F : ℝ → ℝ) (hF : ContDiff ℝ 1 F) (M : ℝ) (hM : 0 ≤ M)
    (hdF : ∀ r : ℝ, |deriv F r| ≤ M) :
    MemLp (fun z => F (u z)) 2 (volume.restrict (I ×ˢ U)) ∧
    MemLp (fun z => euclideanNorm (deriv F (u z) • G z)) 2
      (volume.restrict (I ×ˢ U)) := by
  let μ := volume.restrict (I ×ˢ U)
  haveI : IsFiniteMeasure μ := ⟨by simpa [μ] using hfinite⟩
  let H : ℝ → ℝ := fun r => F r - F 0
  have hH : ContDiff ℝ 1 H := hF.sub contDiff_const
  have hH0 : H 0 = 0 := sub_self _
  have hdH : ∀ r, deriv H r = deriv F r := by
    intro r
    simp only [H, deriv_sub_const]
  have hbound : ∀ r, |deriv H r| ≤ M := fun r => by rw [hdH]; exact hdF r
  obtain ⟨hv, hg⟩ := c11_weighted_caloric_spacetime_chain_memLp hu H hH hH0 M hM hbound
  refine ⟨?_, ?_⟩
  · have hc : MemLp (fun _ : ℝ × Vec d => F 0) 2 μ := memLp_const (F 0)
    have hv' := hv.add hc
    convert hv' using 1
    funext z
    simp only [Pi.add_apply, H, sub_add_cancel]
  · simpa only [hdH] using hg

/-- The uncentered regularized chain has its actual weak spatial gradient
on almost every slice of a finite cylinder. -/
theorem c11_weighted_caloric_spatial_chain_finite {d : ℕ}
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} {I : Set ℝ} {U : Set (Vec d)}
    (hU : IsOpen U) {u : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    (hu : IsWeightedCaloric ρ α I U u G) (hfinite : volume (I ×ˢ U) < ∞)
    (F : ℝ → ℝ) (hF : ContDiff ℝ 1 F) (M : ℝ) (hM : 0 ≤ M)
    (hdF : ∀ r : ℝ, |deriv F r| ≤ M) :
    ∀ᵐ t ∂volume.restrict I,
      MemLp (fun x => F (u (t, x))) 2 (volume.restrict U) ∧
      MemLp (fun x => euclideanNorm (deriv F (u (t, x)) • G (t, x))) 2
        (volume.restrict U) ∧
      HasWeakGradient U (fun x => F (u (t, x)))
        (fun x => deriv F (u (t, x)) • G (t, x)) := by
  let H : ℝ → ℝ := fun r => F r - F 0
  have hH : ContDiff ℝ 1 H := hF.sub contDiff_const
  have hH0 : H 0 = 0 := sub_self _
  have hdH : ∀ r, deriv H r = deriv F r := by
    intro r
    simp only [H, deriv_sub_const]
  have hbound : ∀ r, |deriv H r| ≤ M := fun r => by rw [hdH]; exact hdF r
  obtain ⟨hv, hg⟩ := c11_weighted_caloric_spacetime_chain_memLp_finite hu hfinite F hF M hM hdF
  filter_upwards [c11_memLp_spatial_slices hv, c11_memLp_spatial_slices hg,
    c11_weighted_caloric_spatial_chain hU hu H hH hH0 M hM hbound] with t ht hgt hw
  refine ⟨ht, hgt, ?_⟩
  have hw' := EinsteinRelation.Correctors.hasWeakGradient_sub_const U hw.2.2 (-F 0)
  simpa only [H, hdH, sub_neg_eq_add, sub_add_cancel] using hw'

/-- A time-dependent compact spatial cutoff of the renormalized weighted
solution has the expected weak gradient and square-integrable energy on almost
all spatial slices. -/
theorem c11_weighted_caloric_cutoff_spatial_chain {d : ℕ}
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} {I : Set ℝ} {U : Set (Vec d)}
    (hU : IsOpen U) {u : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    (hu : IsWeightedCaloric ρ α I U u G) (F : ℝ → ℝ)
    (hF : ContDiff ℝ 1 F) (hF0 : F 0 = 0) (M : ℝ) (hM : 0 ≤ M)
    (hdF : ∀ r : ℝ, |deriv F r| ≤ M) (η : ℝ → Vec d → ℝ)
    (hη : ∀ᵐ t ∂volume.restrict I, IsSpatialTest U (η t)) :
    ∀ᵐ t ∂volume.restrict I,
      HasWeakGradient U (fun x => η t x * F (u (t, x)))
        (fun x => η t x • (deriv F (u (t, x)) • G (t, x)) +
          F (u (t, x)) • (fun j => fderiv ℝ (η t) x (unitVector j))) ∧
      MemLp (fun x => η t x * F (u (t, x))) 2 (volume.restrict U) ∧
      MemLp (fun x => euclideanNorm
        (η t x • (deriv F (u (t, x)) • G (t, x)) +
          F (u (t, x)) • (fun j => fderiv ℝ (η t) x (unitVector j)))) 2
        (volume.restrict U) := by
  filter_upwards [c11_weighted_caloric_spatial_chain hU hu F hF hF0 M hM hdF, hη]
    with t ht htest
  exact EinsteinFull.c13_native_cutoff_weak_gradient hU _ _ ht.2.2 ht.1 ht.2.1 (η t) htest

/-- Compact spatial cutoffs preserve the uncentered chain and its actual
product-rule gradient on almost every slice of a finite cylinder. -/
theorem c11_weighted_caloric_cutoff_spatial_chain_finite {d : ℕ}
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} {I : Set ℝ} {U : Set (Vec d)}
    (hU : IsOpen U) {u : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    (hu : IsWeightedCaloric ρ α I U u G) (hfinite : volume (I ×ˢ U) < ∞)
    (F : ℝ → ℝ) (hF : ContDiff ℝ 1 F) (M : ℝ) (hM : 0 ≤ M)
    (hdF : ∀ r : ℝ, |deriv F r| ≤ M) (η : ℝ → Vec d → ℝ)
    (hη : ∀ᵐ t ∂volume.restrict I, IsSpatialTest U (η t)) :
    ∀ᵐ t ∂volume.restrict I,
      HasWeakGradient U (fun x => η t x * F (u (t, x)))
        (fun x => η t x • (deriv F (u (t, x)) • G (t, x)) +
          F (u (t, x)) • (fun j => fderiv ℝ (η t) x (unitVector j))) ∧
      MemLp (fun x => η t x * F (u (t, x))) 2 (volume.restrict U) ∧
      MemLp (fun x => euclideanNorm
        (η t x • (deriv F (u (t, x)) • G (t, x)) +
          F (u (t, x)) • (fun j => fderiv ℝ (η t) x (unitVector j)))) 2
        (volume.restrict U) := by
  filter_upwards [c11_weighted_caloric_spatial_chain_finite hU hu hfinite F hF M hM hdF, hη]
    with t ht htest
  exact EinsteinFull.c13_native_cutoff_weak_gradient hU _ _ ht.2.2 ht.1 ht.2.1 (η t) htest

/-- A fixed compact spatial cutoff of a bounded-derivative renormalization
has spacetime L² value and the actual product-rule gradient. -/
theorem c11_weighted_caloric_cutoff_chain_memLp {d : ℕ}
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} {I : Set ℝ} {U : Set (Vec d)}
    {u : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    (hu : IsWeightedCaloric ρ α I U u G) (F : ℝ → ℝ)
    (hF : ContDiff ℝ 1 F) (hF0 : F 0 = 0) (M : ℝ) (hM : 0 ≤ M)
    (hdF : ∀ r : ℝ, |deriv F r| ≤ M) (η : Vec d → ℝ)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hcη : HasCompactSupport η) :
    MemLp (fun z => η z.2 * F (u z)) 2 (volume.restrict (I ×ˢ U)) ∧
    MemLp (fun z => euclideanNorm
      (η z.2 • (deriv F (u z) • G z) +
        F (u z) • (fun j => fderiv ℝ η z.2 (unitVector j)))) 2
      (volume.restrict (I ×ˢ U)) := by
  let μ := volume.restrict (I ×ˢ U)
  obtain ⟨hv, hg⟩ := c11_weighted_caloric_spacetime_chain_memLp hu F hF hF0 M hM hdF
  have hηtop : MemLp (fun z : ℝ × Vec d => η z.2) ⊤ μ := by
    obtain ⟨B, hB, hb⟩ := PDE.Parabolic.LocalMax.exists_abs_le_of_continuous_of_eq_zero_off
      hη.continuous hcη (fun x hx => image_eq_zero_of_notMem_tsupport hx)
    apply memLp_top_of_bound ((hη.continuous.comp continuous_snd).aestronglyMeasurable) B
    exact ae_of_all _ fun z => by simpa only [Function.comp_apply, Real.norm_eq_abs] using hb z.2
  have hdtop (j : Fin d) : MemLp
      (fun z : ℝ × Vec d => fderiv ℝ η z.2 (unitVector j)) ⊤ μ := by
    have hdcont : Continuous (fun x => fderiv ℝ η x (unitVector j)) :=
      (hη.continuous_fderiv (by simp)).clm_apply continuous_const
    have hdc : HasCompactSupport (fun x => fderiv ℝ η x (unitVector j)) :=
      hcη.fderiv_apply (𝕜 := ℝ) (unitVector j)
    obtain ⟨B, hB, hb⟩ := PDE.Parabolic.LocalMax.exists_abs_le_of_continuous_of_eq_zero_off
      hdcont hdc (fun x hx => image_eq_zero_of_notMem_tsupport
        (f := fun y : Vec d => fderiv ℝ η y (unitVector j)) hx)
    apply memLp_top_of_bound ((hdcont.comp continuous_snd).aestronglyMeasurable) B
    exact ae_of_all _ fun z => by simpa only [Function.comp_apply, Real.norm_eq_abs] using hb z.2
  have hcoord (j : Fin d) : MemLp (fun z => deriv F (u z) * G z j) 2 μ := by
    have hm : AEStronglyMeasurable (fun z => deriv F (u z) * G z j) μ := by
      exact (hF.continuous_deriv_one.comp_aestronglyMeasurable hu.1.aestronglyMeasurable).mul
        ((continuous_apply j).comp_aestronglyMeasurable hu.2.1)
    apply hg.mono' hm
    exact ae_of_all _ fun z => by
      simpa only [Pi.smul_apply, smul_eq_mul, TimeChange.euclideanNorm_eq_norm_toLp] using
        (PiLp.norm_apply_le (WithLp.toLp 2 (deriv F (u z) • G z)) j)
  have hgrad : MemLp (fun z => (WithLp.toLp 2
      (η z.2 • (deriv F (u z) • G z) +
        F (u z) • (fun j => fderiv ℝ η z.2 (unitVector j))) :
        EuclideanSpace ℝ (Fin d))) 2 μ := by
    apply memLp_piLp_iff.mpr
    intro j
    have ha : MemLp (fun z => (deriv F (u z) * G z j) * η z.2) 2 μ :=
      (hcoord j).fun_mul hηtop
    have hb : MemLp (fun z => F (u z) * fderiv ℝ η z.2 (unitVector j)) 2 μ :=
      hv.fun_mul (hdtop j)
    convert ha.add hb using 1
    funext z
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  refine ⟨?_, ?_⟩
  · simpa only [mul_comm] using hv.fun_mul hηtop
  · simpa only [TimeChange.euclideanNorm_eq_norm_toLp] using hgrad.norm

/-- Finite cylinders allow an uncentered bounded-derivative chain. -/
theorem c11_weighted_caloric_cutoff_chain_memLp_finite {d : ℕ}
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} {I : Set ℝ} {U : Set (Vec d)}
    {u : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    (hu : IsWeightedCaloric ρ α I U u G) (hfinite : volume (I ×ˢ U) < ∞) (F : ℝ → ℝ)
    (hF : ContDiff ℝ 1 F) (M : ℝ) (hM : 0 ≤ M)
    (hdF : ∀ r : ℝ, |deriv F r| ≤ M) (η : Vec d → ℝ)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hcη : HasCompactSupport η) :
    MemLp (fun z => η z.2 * F (u z)) 2 (volume.restrict (I ×ˢ U)) ∧
    MemLp (fun z => euclideanNorm
      (η z.2 • (deriv F (u z) • G z) +
        F (u z) • (fun j => fderiv ℝ η z.2 (unitVector j)))) 2
      (volume.restrict (I ×ˢ U)) := by
  let μ := volume.restrict (I ×ˢ U)
  obtain ⟨hv, hg⟩ := c11_weighted_caloric_spacetime_chain_memLp_finite hu hfinite F hF M hM hdF
  have hηtop : MemLp (fun z : ℝ × Vec d => η z.2) ⊤ μ := by
    obtain ⟨B, hB, hb⟩ := PDE.Parabolic.LocalMax.exists_abs_le_of_continuous_of_eq_zero_off
      hη.continuous hcη (fun x hx => image_eq_zero_of_notMem_tsupport hx)
    apply memLp_top_of_bound ((hη.continuous.comp continuous_snd).aestronglyMeasurable) B
    exact ae_of_all _ fun z => by simpa only [Function.comp_apply, Real.norm_eq_abs] using hb z.2
  have hdtop (j : Fin d) : MemLp
      (fun z : ℝ × Vec d => fderiv ℝ η z.2 (unitVector j)) ⊤ μ := by
    have hdcont : Continuous (fun x => fderiv ℝ η x (unitVector j)) :=
      (hη.continuous_fderiv (by simp)).clm_apply continuous_const
    have hdc : HasCompactSupport (fun x => fderiv ℝ η x (unitVector j)) :=
      hcη.fderiv_apply (𝕜 := ℝ) (unitVector j)
    obtain ⟨B, hB, hb⟩ := PDE.Parabolic.LocalMax.exists_abs_le_of_continuous_of_eq_zero_off
      hdcont hdc (fun x hx => image_eq_zero_of_notMem_tsupport
        (f := fun y : Vec d => fderiv ℝ η y (unitVector j)) hx)
    apply memLp_top_of_bound ((hdcont.comp continuous_snd).aestronglyMeasurable) B
    exact ae_of_all _ fun z => by simpa only [Function.comp_apply, Real.norm_eq_abs] using hb z.2
  have hcoord (j : Fin d) : MemLp (fun z => deriv F (u z) * G z j) 2 μ := by
    have hm : AEStronglyMeasurable (fun z => deriv F (u z) * G z j) μ := by
      exact (hF.continuous_deriv_one.comp_aestronglyMeasurable hu.1.aestronglyMeasurable).mul
        ((continuous_apply j).comp_aestronglyMeasurable hu.2.1)
    apply hg.mono' hm
    exact ae_of_all _ fun z => by
      simpa only [Pi.smul_apply, smul_eq_mul, TimeChange.euclideanNorm_eq_norm_toLp] using
        (PiLp.norm_apply_le (WithLp.toLp 2 (deriv F (u z) • G z)) j)
  have hgrad : MemLp (fun z => (WithLp.toLp 2
      (η z.2 • (deriv F (u z) • G z) +
        F (u z) • (fun j => fderiv ℝ η z.2 (unitVector j))) :
        EuclideanSpace ℝ (Fin d))) 2 μ := by
    apply memLp_piLp_iff.mpr
    intro j
    have ha : MemLp (fun z => (deriv F (u z) * G z j) * η z.2) 2 μ :=
      (hcoord j).fun_mul hηtop
    have hb : MemLp (fun z => F (u z) * fderiv ℝ η z.2 (unitVector j)) 2 μ :=
      hv.fun_mul (hdtop j)
    convert ha.add hb using 1
    funext z
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  refine ⟨?_, ?_⟩
  · simpa only [mul_comm] using hv.fun_mul hηtop
  · simpa only [TimeChange.euclideanNorm_eq_norm_toLp] using hgrad.norm

/-- A smooth compact spacetime cutoff of an uncentered bounded-derivative
chain has square-integrable value and product-rule spatial gradient. -/
theorem c11_weighted_caloric_spacetime_cutoff_chain_memLp {d : ℕ}
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} {I : Set ℝ} {U : Set (Vec d)}
    {u : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    (hu : IsWeightedCaloric ρ α I U u G) (hfinite : volume (I ×ˢ U) < ∞)
    (F : ℝ → ℝ) (hF : ContDiff ℝ 1 F) (M : ℝ) (hM : 0 ≤ M)
    (hdF : ∀ r : ℝ, |deriv F r| ≤ M) (η : ℝ × Vec d → ℝ)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hcη : HasCompactSupport η) :
    MemLp (fun z => η z * F (u z)) 2 (volume.restrict (I ×ˢ U)) ∧
    MemLp (fun z => euclideanNorm
      (η z • (deriv F (u z) • G z) +
        F (u z) • (fun j => fderiv ℝ η z (0, unitVector j)))) 2
      (volume.restrict (I ×ˢ U)) := by
  let μ := volume.restrict (I ×ˢ U)
  obtain ⟨hv, hg⟩ := c11_weighted_caloric_spacetime_chain_memLp_finite hu hfinite F hF M hM hdF
  have hηtop : MemLp η ⊤ μ := by
    obtain ⟨B, hB, hb⟩ := PDE.Parabolic.LocalMax.exists_abs_le_of_continuous_of_eq_zero_off
      hη.continuous hcη (fun x hx => image_eq_zero_of_notMem_tsupport hx)
    apply memLp_top_of_bound hη.continuous.aestronglyMeasurable B
    exact ae_of_all _ fun z => by simpa only [Real.norm_eq_abs] using hb z
  have hdtop (j : Fin d) : MemLp
      (fun z : ℝ × Vec d => fderiv ℝ η z (0, unitVector j)) ⊤ μ := by
    have hdcont : Continuous (fun z => fderiv ℝ η z (0, unitVector j)) :=
      (hη.continuous_fderiv (by simp)).clm_apply continuous_const
    have hdc : HasCompactSupport (fun z => fderiv ℝ η z (0, unitVector j)) :=
      hcη.fderiv_apply (𝕜 := ℝ) (0, unitVector j)
    obtain ⟨B, hB, hb⟩ := PDE.Parabolic.LocalMax.exists_abs_le_of_continuous_of_eq_zero_off
      hdcont hdc (fun x hx => image_eq_zero_of_notMem_tsupport
        (f := fun y : ℝ × Vec d => fderiv ℝ η y (0, unitVector j)) hx)
    apply memLp_top_of_bound hdcont.aestronglyMeasurable B
    exact ae_of_all _ fun z => by simpa only [Real.norm_eq_abs] using hb z
  have hcoord (j : Fin d) : MemLp (fun z => deriv F (u z) * G z j) 2 μ := by
    have hm : AEStronglyMeasurable (fun z => deriv F (u z) * G z j) μ :=
      (hF.continuous_deriv_one.comp_aestronglyMeasurable hu.1.aestronglyMeasurable).mul
        ((continuous_apply j).comp_aestronglyMeasurable hu.2.1)
    apply hg.mono' hm
    exact ae_of_all _ fun z => by
      simpa only [Pi.smul_apply, smul_eq_mul, TimeChange.euclideanNorm_eq_norm_toLp] using
        (PiLp.norm_apply_le (WithLp.toLp 2 (deriv F (u z) • G z)) j)
  have hgrad : MemLp (fun z => (WithLp.toLp 2
      (η z • (deriv F (u z) • G z) +
        F (u z) • (fun j => fderiv ℝ η z (0, unitVector j))) :
        EuclideanSpace ℝ (Fin d))) 2 μ := by
    apply memLp_piLp_iff.mpr
    intro j
    have ha : MemLp (fun z => (deriv F (u z) * G z j) * η z) 2 μ :=
      (hcoord j).fun_mul hηtop
    have hb : MemLp (fun z => F (u z) * fderiv ℝ η z (0, unitVector j)) 2 μ :=
      hv.fun_mul (hdtop j)
    convert ha.add hb using 1
    funext z
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  refine ⟨?_, ?_⟩
  · simpa only [mul_comm] using hv.fun_mul hηtop
  · simpa only [TimeChange.euclideanNorm_eq_norm_toLp] using hgrad.norm

/-- Weighted parabolic Sobolev for a localized chain of the actual solution. -/
theorem c11_weighted_caloric_cutoff_chain_sobolev (d : ℕ) (hd : 2 ≤ d)
    (κ : ℝ) (hκ : 0 < κ) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
    IsUniformlyElliptic κ ρ α → ∀ (I : Set ℝ) (U : Set (Vec d)),
    MeasurableSet I → IsOpen U →
    ∀ (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d),
    IsWeightedCaloric ρ α I U u G →
    ∀ (F : ℝ → ℝ), ContDiff ℝ 1 F → F 0 = 0 → ∀ M : ℝ, 0 ≤ M →
    (∀ r, |deriv F r| ≤ M) →
    ∀ (η : Vec d → ℝ), ContDiff ℝ (⊤ : ℕ∞) η → HasCompactSupport η →
    IsSpatialTest U η → ∀ K : Set (Vec d), IsCompact K → K ⊆ U →
    (∀ x, x ∉ K → η x = 0) → ∀ S : ℝ≥0∞,
    (∀ᵐ t ∂volume.restrict I,
      (∫⁻ x in U, ENNReal.ofReal (ρ x) * ‖η x * F (u (t,x))‖ₑ ^ (2 : ℝ)) ≤ S) →
    (∫⁻ t in I, ∫⁻ x in U, ENNReal.ofReal (ρ x) *
      ‖η x * F (u (t,x))‖ₑ ^ (2 * ((d : ℝ)+2) / d)) ≤
    C * S ^ (2 / (d : ℝ)) *
      ∫⁻ t in I, ∫⁻ x in U, ENNReal.ofReal
        (dot ((α x).mulVec (η x • (deriv F (u (t,x)) • G (t,x)) +
          F (u (t,x)) • (fun j => fderiv ℝ η x (unitVector j))))
          (η x • (deriv F (u (t,x)) • G (t,x)) +
          F (u (t,x)) • (fun j => fderiv ℝ η x (unitVector j)))) := by
  obtain ⟨C, hC, hsob⟩ := c8_native_weighted_parabolic_sobolev d hd κ hκ
  refine ⟨C, hC, ?_⟩
  intro ρ α hcoeff I U hI hU u G hu F hF hF0 M hM hdF η hη hcη htest K hK hKU hzero S hS
  let v : ℝ × Vec d → ℝ := fun z => η z.2 * F (u z)
  let H : ℝ × Vec d → Vec d := fun z =>
    η z.2 • (deriv F (u z) • G z) +
      F (u z) • (fun j => fderiv ℝ η z.2 (unitVector j))
  obtain ⟨hv, hgrad⟩ := c11_weighted_caloric_cutoff_chain_memLp hu F hF hF0 M hM hdF η hη hcη
  have hηm : AEStronglyMeasurable (fun z : ℝ × Vec d => η z.2)
      (volume.restrict (I ×ˢ U)) := (hη.continuous.comp continuous_snd).aestronglyMeasurable
  have hdm : AEStronglyMeasurable (fun z : ℝ × Vec d => deriv F (u z))
      (volume.restrict (I ×ˢ U)) := hF.continuous_deriv_one.comp_aestronglyMeasurable hu.1.aestronglyMeasurable
  have hfm : AEStronglyMeasurable (fun z : ℝ × Vec d => F (u z))
      (volume.restrict (I ×ˢ U)) := hF.continuous.comp_aestronglyMeasurable hu.1.aestronglyMeasurable
  have hηd : Continuous (fun x => fun j => fderiv ℝ η x (unitVector j)) :=
    continuous_pi fun j => (hη.continuous_fderiv (by simp)).clm_apply continuous_const
  have hHm : AEStronglyMeasurable H (volume.restrict (I ×ˢ U)) :=
    (hηm.smul (hdm.smul hu.2.1)).add (hfm.smul (hηd.comp continuous_snd).aestronglyMeasurable)
  have hw : ∀ᵐ t ∂volume.restrict I, HasWeakGradient U (fun x => v (t,x)) (fun x => H (t,x)) := by
    filter_upwards [c11_weighted_caloric_cutoff_spatial_chain hU hu F hF hF0 M hM hdF
      (fun _ => η) (ae_of_all _ fun _ => htest)] with t ht
    exact ht.1
  exact hsob ρ α hcoeff I U hI hU v H hv hHm hgrad hw K hK hKU
    (ae_of_all _ fun t x hx hxK => by simp only [v, hzero x hxK, zero_mul]) S hS

/-- The same estimate includes uncentered chains on finite cylinders. -/
theorem c11_weighted_caloric_cutoff_chain_sobolev_finite (d : ℕ) (hd : 2 ≤ d)
    (κ : ℝ) (hκ : 0 < κ) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
    IsUniformlyElliptic κ ρ α → ∀ (I : Set ℝ) (U : Set (Vec d)),
    MeasurableSet I → IsOpen U → volume (I ×ˢ U) < ∞ →
    ∀ (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d),
    IsWeightedCaloric ρ α I U u G →
    ∀ (F : ℝ → ℝ), ContDiff ℝ 1 F → ∀ M : ℝ, 0 ≤ M →
    (∀ r, |deriv F r| ≤ M) →
    ∀ (η : Vec d → ℝ), ContDiff ℝ (⊤ : ℕ∞) η → HasCompactSupport η →
    IsSpatialTest U η → ∀ K : Set (Vec d), IsCompact K → K ⊆ U →
    (∀ x, x ∉ K → η x = 0) → ∀ S : ℝ≥0∞,
    (∀ᵐ t ∂volume.restrict I,
      (∫⁻ x in U, ENNReal.ofReal (ρ x) * ‖η x * F (u (t,x))‖ₑ ^ (2 : ℝ)) ≤ S) →
    (∫⁻ t in I, ∫⁻ x in U, ENNReal.ofReal (ρ x) *
      ‖η x * F (u (t,x))‖ₑ ^ (2 * ((d : ℝ)+2) / d)) ≤
    C * S ^ (2 / (d : ℝ)) *
      ∫⁻ t in I, ∫⁻ x in U, ENNReal.ofReal
        (dot ((α x).mulVec (η x • (deriv F (u (t,x)) • G (t,x)) +
          F (u (t,x)) • (fun j => fderiv ℝ η x (unitVector j))))
          (η x • (deriv F (u (t,x)) • G (t,x)) +
          F (u (t,x)) • (fun j => fderiv ℝ η x (unitVector j)))) := by
  obtain ⟨C, hC, hsob⟩ := c8_native_weighted_parabolic_sobolev d hd κ hκ
  refine ⟨C, hC, ?_⟩
  intro ρ α hcoeff I U hI hU hfinite u G hu F hF M hM hdF η hη hcη htest K hK hKU hzero S hS
  let v : ℝ × Vec d → ℝ := fun z => η z.2 * F (u z)
  let H : ℝ × Vec d → Vec d := fun z =>
    η z.2 • (deriv F (u z) • G z) +
      F (u z) • (fun j => fderiv ℝ η z.2 (unitVector j))
  obtain ⟨hv, hgrad⟩ := c11_weighted_caloric_cutoff_chain_memLp_finite hu hfinite F hF M hM hdF η hη hcη
  have hηm : AEStronglyMeasurable (fun z : ℝ × Vec d => η z.2)
      (volume.restrict (I ×ˢ U)) := (hη.continuous.comp continuous_snd).aestronglyMeasurable
  have hdm : AEStronglyMeasurable (fun z : ℝ × Vec d => deriv F (u z))
      (volume.restrict (I ×ˢ U)) := hF.continuous_deriv_one.comp_aestronglyMeasurable hu.1.aestronglyMeasurable
  have hfm : AEStronglyMeasurable (fun z : ℝ × Vec d => F (u z))
      (volume.restrict (I ×ˢ U)) := hF.continuous.comp_aestronglyMeasurable hu.1.aestronglyMeasurable
  have hηd : Continuous (fun x => fun j => fderiv ℝ η x (unitVector j)) :=
    continuous_pi fun j => (hη.continuous_fderiv (by simp)).clm_apply continuous_const
  have hHm : AEStronglyMeasurable H (volume.restrict (I ×ˢ U)) :=
    (hηm.smul (hdm.smul hu.2.1)).add (hfm.smul (hηd.comp continuous_snd).aestronglyMeasurable)
  have hw : ∀ᵐ t ∂volume.restrict I, HasWeakGradient U (fun x => v (t,x)) (fun x => H (t,x)) := by
    filter_upwards [c11_weighted_caloric_cutoff_spatial_chain_finite hU hu hfinite F hF M hM hdF
      (fun _ => η) (ae_of_all _ fun _ => htest)] with t ht
    exact ht.1
  exact hsob ρ α hcoeff I U hI hU v H hv hHm hgrad hw K hK hKU
    (ae_of_all _ fun t x hx hxK => by simp only [v, hzero x hxK, zero_mul]) S hS

/-- Native weighted Sobolev for an uncentered chain with a spacetime cutoff. -/
theorem c11_weighted_caloric_spacetime_cutoff_chain_sobolev (d : ℕ) (hd : 2 ≤ d)
    (κ : ℝ) (hκ : 0 < κ) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
    IsUniformlyElliptic κ ρ α → ∀ (I : Set ℝ) (U : Set (Vec d)),
    MeasurableSet I → IsOpen U → volume (I ×ˢ U) < ∞ →
    ∀ (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d),
    IsWeightedCaloric ρ α I U u G →
    ∀ (F : ℝ → ℝ), ContDiff ℝ 1 F → ∀ M : ℝ, 0 ≤ M →
    (∀ r, |deriv F r| ≤ M) →
    ∀ (η : ℝ × Vec d → ℝ), ContDiff ℝ (⊤ : ℕ∞) η → HasCompactSupport η →
    (∀ᵐ t ∂volume.restrict I, IsSpatialTest U (fun x => η (t,x))) → ∀ K : Set (Vec d), IsCompact K → K ⊆ U →
    (∀ t x, x ∉ K → η (t,x) = 0) → ∀ S : ℝ≥0∞,
    (∀ᵐ t ∂volume.restrict I,
      (∫⁻ x in U, ENNReal.ofReal (ρ x) * ‖η (t,x) * F (u (t,x))‖ₑ ^ (2 : ℝ)) ≤ S) →
    (∫⁻ t in I, ∫⁻ x in U, ENNReal.ofReal (ρ x) *
      ‖η (t,x) * F (u (t,x))‖ₑ ^ (2 * ((d : ℝ)+2) / d)) ≤
    C * S ^ (2 / (d : ℝ)) *
      ∫⁻ t in I, ∫⁻ x in U, ENNReal.ofReal
        (dot ((α x).mulVec (η (t,x) • (deriv F (u (t,x)) • G (t,x)) +
          F (u (t,x)) • (fun j => fderiv ℝ η (t,x) (0, unitVector j))))
          (η (t,x) • (deriv F (u (t,x)) • G (t,x)) +
          F (u (t,x)) • (fun j => fderiv ℝ η (t,x) (0, unitVector j)))) := by
  obtain ⟨C, hC, hsob⟩ := c8_native_weighted_parabolic_sobolev d hd κ hκ
  refine ⟨C, hC, ?_⟩
  intro ρ α hcoeff I U hI hU hfinite u G hu F hF M hM hdF η hη hcη htest K hK hKU hzero S hS
  let v : ℝ × Vec d → ℝ := fun z => η z * F (u z)
  let H : ℝ × Vec d → Vec d := fun z =>
    η z • (deriv F (u z) • G z) +
      F (u z) • (fun j => fderiv ℝ η z (0, unitVector j))
  obtain ⟨hv, hgrad⟩ := c11_weighted_caloric_spacetime_cutoff_chain_memLp hu hfinite F hF M hM hdF η hη hcη
  have hηm : AEStronglyMeasurable (fun z : ℝ × Vec d => η z)
      (volume.restrict (I ×ˢ U)) := hη.continuous.aestronglyMeasurable
  have hdm : AEStronglyMeasurable (fun z : ℝ × Vec d => deriv F (u z))
      (volume.restrict (I ×ˢ U)) := hF.continuous_deriv_one.comp_aestronglyMeasurable hu.1.aestronglyMeasurable
  have hfm : AEStronglyMeasurable (fun z : ℝ × Vec d => F (u z))
      (volume.restrict (I ×ˢ U)) := hF.continuous.comp_aestronglyMeasurable hu.1.aestronglyMeasurable
  have hηd : Continuous (fun z => fun j => fderiv ℝ η z (0, unitVector j)) :=
    continuous_pi fun j => (hη.continuous_fderiv (by simp)).clm_apply continuous_const
  have hHm : AEStronglyMeasurable H (volume.restrict (I ×ˢ U)) :=
    (hηm.smul (hdm.smul hu.2.1)).add (hfm.smul hηd.aestronglyMeasurable)
  have hw : ∀ᵐ t ∂volume.restrict I, HasWeakGradient U (fun x => v (t,x)) (fun x => H (t,x)) := by
    filter_upwards [c11_weighted_caloric_cutoff_spatial_chain_finite hU hu hfinite F hF M hM hdF
      (fun t x => η (t,x)) htest] with t ht
    have heq (x : Vec d) (j : Fin d) :
        fderiv ℝ (fun y => η (t,y)) x (unitVector j) =
          fderiv ℝ η (t,x) (0, unitVector j) := by
      have hf := (hη.differentiable (by simp) (t,x)).hasFDerivAt.comp x
        ((hasFDerivAt_const t x).prodMk (hasFDerivAt_id x))
      simpa [Function.comp_def] using congrArg (fun L : Vec d →L[ℝ] ℝ => L (unitVector j)) hf.fderiv
    simpa only [v, H, heq] using ht.1
  exact hsob ρ α hcoeff I U hI hU v H hv hHm hgrad hw K hK hKU
    (ae_of_all _ fun t x hx hxK => by simp only [v, hzero t x hxK, zero_mul]) S hS

/-- Each component of the actual coefficient flux is square integrable on the
native weighted solution cylinder. This supplies the integrability needed when
the weak equation is tested after time averaging. -/
theorem c11_weighted_caloric_flux_memLp {d : ℕ} {κ : ℝ} (hκ : 0 < κ)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (h : IsUniformlyElliptic κ ρ α)
    {I : Set ℝ} {U : Set (Vec d)} {u : ℝ × Vec d → ℝ}
    {G : ℝ × Vec d → Vec d} (hu : IsWeightedCaloric ρ α I U u G) :
    ∀ i : Fin d, MemLp (fun z => ((α z.2).mulVec (G z)) i) 2
      (volume.restrict (I ×ˢ U)) := by
  let μ := volume.restrict (I ×ˢ U)
  have hα : IsElliptic κ⁻¹ α := by
    intro x
    simpa only [inv_inv] using (h.2.2 x).2.2
  have hαtop (i j : Fin d) : MemLp (fun z : ℝ × Vec d => α z.2 i j) ∞ μ := by
    let : MeasurableSpace (Mat d) := EinsteinRelation.instMeasurableSpaceMat d
    let : BorelSpace (Mat d) := EinsteinRelation.instBorelSpaceMat d
    have hm : Measurable (fun z : ℝ × Vec d => α z.2 i j) :=
      ((continuous_id : Continuous (id : Mat d → Mat d)).matrix_elem i j).measurable.comp
        (h.2.1.comp measurable_snd)
    apply memLp_top_of_bound hm.aestronglyMeasurable κ⁻¹
    apply ae_of_all
    intro z
    have he := PiLp.norm_apply_le
      (WithLp.toLp 2 ((α z.2).mulVec (unitVector j)) : EuclideanSpace ℝ (Fin d)) i
    have hn := Correctors.isElliptic_mulVec_euclideanNorm_le (inv_pos.mpr hκ)
      hα z.2 (unitVector j)
    rw [TimeChange.euclideanNorm_eq_norm_toLp] at hn
    have hv : ((α z.2).mulVec (unitVector j)) i = α z.2 i j := by
      change dotProduct (fun k => α z.2 i k) (Pi.single j 1) = _
      rw [dotProduct_single, mul_one]
    have hw : euclideanNorm (unitVector j) = 1 := by
      simp [euclideanNorm, euclideanSq, dot, unitVector, Pi.single_apply, mul_ite]
    simpa only [PiLp.toLp_apply, hv, Real.norm_eq_abs, hw, mul_one] using he.trans hn
  have hG : MemLp G 2 μ := by
    apply hu.2.2.1.mono' hu.2.1
    exact Filter.Eventually.of_forall (fun z => by
      apply pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _) |>.mpr
      intro i
      exact EinsteinRelation.Regeneration.coordinate_abs_le_euclideanNorm (G z) i)
  have hg : ∀ i, MemLp (fun z => G z i) 2 μ := memLp_pi_iff.mp hG
  intro i
  simpa only [Matrix.mulVec, dotProduct, Pi.mul_apply] using
    memLp_finsetSum Finset.univ (fun j _ => (hαtop i j).mul (hg j))

/-- The nonlinear flux term in the renormalized weak equation is integrable
for the actual weighted solution whenever the chain derivative is bounded. -/
theorem c11_weighted_caloric_chain_flux_integrable {d : ℕ} {κ : ℝ} (hκ : 0 < κ)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (h : IsUniformlyElliptic κ ρ α)
    {I : Set ℝ} {U : Set (Vec d)} {u : ℝ × Vec d → ℝ}
    {G : ℝ × Vec d → Vec d} (hu : IsWeightedCaloric ρ α I U u G)
    (F : ℝ → ℝ) (hF : ContDiff ℝ 1 F) (M : ℝ)
    (hdF : ∀ r : ℝ, |deriv F r| ≤ M) :
    Integrable (fun z => dot ((α z.2).mulVec (G z))
      (deriv F (u z) • G z)) (volume.restrict (I ×ˢ U)) := by
  let μ := volume.restrict (I ×ˢ U)
  have hG : MemLp G 2 μ := by
    apply hu.2.2.1.mono' hu.2.1
    exact Filter.Eventually.of_forall (fun z => by
      apply pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _) |>.mpr
      intro i
      exact EinsteinRelation.Regeneration.coordinate_abs_le_euclideanNorm (G z) i)
  have hg : ∀ i, MemLp (fun z => G z i) 2 μ := memLp_pi_iff.mp hG
  have htop : MemLp (fun z => deriv F (u z)) ∞ μ := by
    apply memLp_top_of_bound
      (hF.continuous_deriv_one.comp_aestronglyMeasurable hu.1.aestronglyMeasurable) M
    exact Filter.Eventually.of_forall fun z => by simpa only [Real.norm_eq_abs] using hdF (u z)
  have hc (i : Fin d) : MemLp (fun z => deriv F (u z) * G z i) 2 μ :=
    htop.mul (hg i)
  have hflux := c11_weighted_caloric_flux_memLp hκ h hu
  change Integrable (fun z => ∑ i : Fin d,
    ((α z.2).mulVec (G z)) i * (deriv F (u z) * G z i)) μ
  exact integrable_finsetSum Finset.univ (fun i _ => (hflux i).integrable_mul (hc i))

/-- A lower bound on the clock density converts weighted nonnegative slice mass
into ordinary slice mass. This applies to the cutoff power in the energy estimate. -/
theorem c11_unweighted_slice_mass_le_weighted {d : ℕ} {κ : ℝ} (hκ : 0 < κ)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (hcoeff : IsUniformlyElliptic κ ρ α)
    (U : Set (Vec d)) (hU : MeasurableSet U) (f : Vec d → ℝ) (hf : ∀ x ∈ U, 0 ≤ f x) :
    ∫⁻ x in U, ENNReal.ofReal (f x) ≤
      ENNReal.ofReal κ⁻¹ * ∫⁻ x in U, ENNReal.ofReal (ρ x * f x) := by
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem hU] with x hx
  · rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hκ.le)]
    apply ENNReal.ofReal_le_ofReal
    have hρ := (hcoeff.2.2 x).1
    have hmul := mul_le_mul_of_nonneg_right hρ (hf x hx)
    have h := mul_le_mul_of_nonneg_left hmul (inv_nonneg.mpr hκ.le)
    simpa only [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hκ), one_mul] using h

/-- Almost-everywhere version of the clock-density comparison, suitable for
Sobolev time slices. -/
theorem c11_unweighted_slice_mass_le_weighted_ae {d : ℕ} {κ : ℝ} (hκ : 0 < κ)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (hcoeff : IsUniformlyElliptic κ ρ α)
    (U : Set (Vec d)) (f : Vec d → ℝ)
    (hf : ∀ᵐ x ∂volume.restrict U, 0 ≤ f x) :
    ∫⁻ x in U, ENNReal.ofReal (f x) ≤
      ENNReal.ofReal κ⁻¹ * ∫⁻ x in U, ENNReal.ofReal (ρ x * f x) := by
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono_ae
  filter_upwards [hf] with x hx
  rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hκ.le)]
  apply ENNReal.ofReal_le_ofReal
  have hρ := (hcoeff.2.2 x).1
  have hmul := mul_le_mul_of_nonneg_right hρ hx
  have h := mul_le_mul_of_nonneg_left hmul (inv_nonneg.mpr hκ.le)
  simpa only [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hκ), one_mul] using h

/-- Spatial Sobolev step with a clock-weighted slice bound. The gradient and
cutoff energy bounds remain the ordinary ones from the elliptic part. -/
theorem c11_weighted_cutoff_comp_energy_sobolev (d : ℕ) (hd : 0 < d)
    (κ : ℝ) (hκ : 0 < κ) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ {U : Set (PDE.Vec d)} {I J : Set ℝ},
      IsOpen U → volume U ≠ ⊤ → MeasurableSet J → J ⊆ I →
      ∀ (ρ : PDE.Vec d → ℝ) (α : PDE.Vec d → Mat d), IsUniformlyElliptic κ ρ α →
      ∀ (u : PDE.ParH1Function U I),
      (∀ᵐ z ∂(volume.restrict (U ×ˢ J)), 0 ≤ u.toFun z) →
      ∀ (F G : ℝ → ℝ), ContDiff ℝ 1 G → ∀ M : ℝ, 0 ≤ M →
      (∀ s, |deriv G s| ≤ M) → ∀ {K Lam : ℝ}, 1 ≤ K → 1 ≤ Lam →
      (∀ s, 0 ≤ s → 0 ≤ F s ∧ 0 ≤ deriv (deriv F) s ∧ G s ^ 2 ≤ K * F s ∧
        deriv G s ^ 2 ≤ K * deriv (deriv F) s) →
      ∀ η : PDE.Vec d × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) η → ∀ Kx : Set (PDE.Vec d),
      IsCompact Kx → Kx ⊆ U → (∀ x t, x ∉ Kx → η (x, t) = 0) → ∀ R : ℝ≥0∞,
      (∀ᵐ t ∂volume.restrict J,
        ∫⁻ x in U, ENNReal.ofReal (ρ x * (η (x,t)^2 * F (u.toFun (x,t)))) ≤ R) →
      ∫⁻ z in U ×ˢ J, ENNReal.ofReal
        (η z ^ 2 * deriv (deriv F) (u.toFun z) * PDE.vecNormSq (u.grad z)) ≤ 2 * R →
      ∫⁻ z in U ×ˢ J, ENNReal.ofReal
        (F (u.toFun z) * (2 * Lam * K * PDE.vecNormSq (PDE.parSpaceGrad η z))) ≤ R →
      ∫⁻ z in U ×ˢ J, ENNReal.ofReal |η z * G (u.toFun z)| ^ (2 * ((d : ℝ) + 2) / d) ≤
        C * (ENNReal.ofReal K * (max 1 (ENNReal.ofReal κ⁻¹) * R)) ^ (2 / (d : ℝ)) *
          (ENNReal.ofReal (5 * K) * (max 1 (ENNReal.ofReal κ⁻¹) * R)) := by
  obtain ⟨C, hC, hcore⟩ := PDE.Parabolic.LocalMax.cutoff_comp_energy_sobolev d hd
  refine ⟨C, hC, ?_⟩
  intro U I J hU hfin hJ hJI ρ α hcoeff u hpos F G hG M hM hGM K Lam hK hLam
    hstr η hη Kx hKx hKxU hηx R hmass hgrad hcut
  have hR : R ≤ max 1 (ENNReal.ofReal κ⁻¹) * R := by
    conv_lhs => rw [← one_mul R]
    gcongr
    exact le_max_left _ _
  have hposprod : ∀ᵐ z ∂((volume.restrict U).prod (volume.restrict J)), 0 ≤ u.toFun z := by
    rw [← PDE.Parabolic.Energy.volume_restrict_prod]; exact hpos
  have hslice : ∀ᵐ t ∂volume.restrict J,
      ∫⁻ x in U, ENNReal.ofReal (η (x,t)^2 * F (u.toFun (x,t))) ≤
        max 1 (ENNReal.ofReal κ⁻¹) * R := by
    filter_upwards [hmass, PDE.Parabolic.Energy.ae_ae_swap hposprod] with t ht hpt
    have hf : ∀ᵐ x ∂volume.restrict U, 0 ≤ η (x,t)^2 * F (u.toFun (x,t)) := by
      filter_upwards [hpt] with x hx
      exact mul_nonneg (sq_nonneg _) (hstr _ hx).1
    calc
      _ ≤ ENNReal.ofReal κ⁻¹ * ∫⁻ x in U,
          ENNReal.ofReal (ρ x * (η (x,t)^2 * F (u.toFun (x,t)))) :=
        c11_unweighted_slice_mass_le_weighted_ae hκ hcoeff U _ hf
      _ ≤ ENNReal.ofReal κ⁻¹ * R := by gcongr
      _ ≤ max 1 (ENNReal.ofReal κ⁻¹) * R :=
        by gcongr; exact le_max_right _ _
  exact hcore hU hfin hJ hJI u hpos F G hG M hM hGM hK hLam hstr η hη Kx hKx hKxU hηx
    (max 1 (ENNReal.ofReal κ⁻¹) * R) hslice
    (hgrad.trans (by gcongr)) (hcut.trans hR)

/-- Scalar reverse Hölder bookkeeping with the density factor from the
weighted Sobolev step. -/
theorem c11_weighted_power_step_arith {d : ℕ} (hd : 0 < d)
    {Cs : ℝ≥0∞} (hCs : Cs ≠ ⊤) {κ K Y : ℝ}
    (hK : 1 ≤ K) (I : ℝ≥0∞) :
    Cs * (ENNReal.ofReal K * (max 1 (ENNReal.ofReal κ⁻¹) *
      (ENNReal.ofReal Y * I))) ^ (2 / (d : ℝ)) *
      (ENNReal.ofReal (5 * K) * (max 1 (ENNReal.ofReal κ⁻¹) *
        (ENNReal.ofReal Y * I))) ≤
      ENNReal.ofReal (max 1 (5 * Cs.toReal) * (K * (max 1 κ⁻¹ * Y))) ^
        (((d : ℝ) + 2) / d) * I ^ (((d : ℝ) + 2) / d) := by
  have hm : 0 ≤ max 1 κ⁻¹ := (by positivity : (0 : ℝ) ≤ 1).trans (le_max_left _ _)
  have he : ENNReal.ofReal (max 1 κ⁻¹) = max 1 (ENNReal.ofReal κ⁻¹) := by
    by_cases h : κ⁻¹ ≤ 1
    · rw [max_eq_left h, max_eq_left]
      · simp
      · simpa using ENNReal.ofReal_le_ofReal h
    · have hh : 1 ≤ κ⁻¹ := le_of_not_ge h
      rw [max_eq_right hh, max_eq_right]
      simpa using ENNReal.ofReal_le_ofReal hh
  have hp := PDE.Parabolic.LocalMax.power_step_arith hd hCs hK I (Y := max 1 κ⁻¹ * Y)
  rw [ENNReal.ofReal_mul hm, he] at hp
  simpa only [mul_assoc] using hp

/-- Pass the truncated Moser powers to their full power using Fatou's lemma.
The estimate is stated on the native time-space carrier and for any measure. -/
theorem c11_truncated_power_lintegral_le {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {u : Ω → ℝ} (hu : AEMeasurable u μ)
    (hpos : ∀ᵐ z ∂μ, 0 ≤ u z) {p ε : ℝ} (hp : 0 ≤ p) (hε : 0 ≤ ε)
    (G : ℕ → ℝ → ℝ) (hG : ∀ n, Continuous (G n))
    (hpower : ∀ (n : ℕ) (s : ℝ), 0 ≤ s → s ≤ (n : ℝ) →
      G n s = (s + ε) ^ (p / 2))
    (B : ℝ≥0∞)
    (hbound : ∀ n, ∫⁻ z, ENNReal.ofReal |G n (u z)| ^
      (2 * ((d : ℝ) + 2) / d) ∂μ ≤ B) :
    ∫⁻ z, ENNReal.ofReal (u z + ε) ^ (p * (((d : ℝ) + 2) / d)) ∂μ ≤ B := by
  let q : ℝ := 2 * ((d : ℝ) + 2) / d
  have hlim : ∀ᵐ z ∂μ,
      Filter.liminf (fun n : ℕ => ENNReal.ofReal |G n (u z)| ^ q) Filter.atTop =
        ENNReal.ofReal (u z + ε) ^ (p * (((d : ℝ) + 2) / d)) := by
    filter_upwards [hpos] with z hz
    refine Filter.Tendsto.liminf_eq (tendsto_const_nhds.congr' ?_)
    obtain ⟨n₀, hn₀⟩ := exists_nat_ge (u z)
    filter_upwards [Filter.eventually_ge_atTop n₀] with n hn
    have hle : u z ≤ (n : ℝ) := hn₀.trans (by exact_mod_cast hn)
    rw [hpower n (u z) hz hle]
    exact (PDE.Parabolic.LocalMax.ofReal_half_pow_rpow (by linarith) hp).symm
  have hmeas : ∀ n : ℕ, AEMeasurable (fun z => ENNReal.ofReal |G n (u z)| ^ q) μ :=
    fun n => (ENNReal.measurable_ofReal.comp_aemeasurable
      (((hG n).measurable.comp_aemeasurable hu).abs)).pow_const q
  calc
    _ = ∫⁻ z, Filter.liminf (fun n : ℕ => ENNReal.ofReal |G n (u z)| ^ q)
        Filter.atTop ∂μ := (lintegral_congr_ae hlim).symm
    _ ≤ Filter.liminf (fun n : ℕ => ∫⁻ z, ENNReal.ofReal |G n (u z)| ^ q ∂μ)
        Filter.atTop := lintegral_liminf_le' hmeas
    _ ≤ B := Filter.liminf_le_of_frequently_le'
      (Filter.Eventually.frequently (Filter.Eventually.of_forall hbound))

/-- Localize the truncated-power limit to a cylinder on which the cutoff
is one, using estimates on a larger cylinder. -/
theorem c11_truncated_power_cutoff_lintegral_le {d : ℕ}
    {u η : ℝ × Vec d → ℝ} {S V : Set (ℝ × Vec d)}
    (hS : MeasurableSet S) (hSV : S ⊆ V)
    (hu : AEMeasurable u (volume.restrict S))
    (hpos : ∀ᵐ z ∂volume.restrict S, 0 ≤ u z)
    (hη : ∀ z ∈ S, η z = 1)
    {p ε : ℝ} (hp : 0 ≤ p) (hε : 0 ≤ ε)
    (G : ℕ → ℝ → ℝ) (hG : ∀ n, Continuous (G n))
    (hpower : ∀ (n : ℕ) (s : ℝ), 0 ≤ s → s ≤ (n : ℝ) →
      G n s = (s + ε) ^ (p / 2))
    (B : ℝ≥0∞)
    (hbound : ∀ n, ∫⁻ z in V, ENNReal.ofReal |η z * G n (u z)| ^
      (2 * ((d : ℝ) + 2) / d) ≤ B) :
    ∫⁻ z in S, ENNReal.ofReal (u z + ε) ^ (p * (((d : ℝ) + 2) / d)) ≤ B := by
  apply c11_truncated_power_lintegral_le (volume.restrict S) hu hpos hp hε G hG hpower B
  intro n
  calc
    (∫⁻ z in S, ENNReal.ofReal |G n (u z)| ^ (2 * ((d : ℝ) + 2) / d)) =
        ∫⁻ z in S, ENNReal.ofReal |η z * G n (u z)| ^ (2 * ((d : ℝ) + 2) / d) := by
      apply setLIntegral_congr_fun hS
      intro z hz
      dsimp only
      rw [hη z hz, one_mul]
    _ ≤ ∫⁻ z in V, ENNReal.ofReal |η z * G n (u z)| ^ (2 * ((d : ℝ) + 2) / d) :=
      lintegral_mono_set hSV
    _ ≤ B := hbound n

/-- A weighted cutoff bound controls the unweighted full power on the inner
cylinder, uniformly in the truncation parameter. -/
theorem c11_weighted_truncated_power_cutoff_lintegral_le {d : ℕ} {κ : ℝ}
    (hκ : 0 < κ) {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (hcoeff : IsUniformlyElliptic κ ρ α)
    {u η : ℝ × Vec d → ℝ} {S V : Set (ℝ × Vec d)}
    (hS : MeasurableSet S) (hSV : S ⊆ V)
    (hu : AEMeasurable u (volume.restrict S))
    (hpos : ∀ᵐ z ∂volume.restrict S, 0 ≤ u z)
    (hη : ∀ z ∈ S, η z = 1)
    {p ε : ℝ} (hp : 0 ≤ p) (hε : 0 ≤ ε)
    (G : ℕ → ℝ → ℝ) (hG : ∀ n, Continuous (G n))
    (hpower : ∀ (n : ℕ) (s : ℝ), 0 ≤ s → s ≤ (n : ℝ) →
      G n s = (s + ε) ^ (p / 2))
    (B : ℝ≥0∞)
    (hbound : ∀ n, ∫⁻ z in V, ENNReal.ofReal (ρ z.2) *
      ENNReal.ofReal |η z * G n (u z)| ^ (2 * ((d : ℝ) + 2) / d) ≤ B) :
    ∫⁻ z in S, ENNReal.ofReal (u z + ε) ^ (p * (((d : ℝ) + 2) / d)) ≤
      ENNReal.ofReal κ⁻¹ * B := by
  apply c11_truncated_power_cutoff_lintegral_le hS hSV hu hpos hη hp hε G hG hpower
  intro n
  calc
    (∫⁻ z in V, ENNReal.ofReal |η z * G n (u z)| ^ (2 * ((d : ℝ) + 2) / d)) ≤
        ENNReal.ofReal κ⁻¹ * ∫⁻ z in V, ENNReal.ofReal (ρ z.2) *
          ENNReal.ofReal |η z * G n (u z)| ^ (2 * ((d : ℝ) + 2) / d) :=
      (c8_density_lintegral_bounds (volume.restrict V) κ hκ (fun z => ρ z.2)
        (fun z => ⟨(hcoeff.2.2 z.2).1, (hcoeff.2.2 z.2).2.1⟩) _).2
    _ ≤ ENNReal.ofReal κ⁻¹ * B := by gcongr; exact hbound n

/-- Fubini puts the native weighted Sobolev integral in the form needed
for the cutoff power limit. -/
theorem c11_weighted_caloric_cutoff_lintegral_prod {d : ℕ} {κ : ℝ}
    {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (hcoeff : IsUniformlyElliptic κ ρ α)
    {I : Set ℝ} {U : Set (Vec d)} {u η : ℝ × Vec d → ℝ}
    {H : ℝ × Vec d → Vec d} (hu : IsWeightedCaloric ρ α I U u H)
    (hη : Continuous η) {F : ℝ → ℝ} (hF : Continuous F) (q : ℝ) :
    (∫⁻ z in I ×ˢ U, ENNReal.ofReal (ρ z.2) *
      ENNReal.ofReal |η z * F (u z)| ^ q) =
    ∫⁻ t in I, ∫⁻ x in U, ENNReal.ofReal (ρ x) * ‖η (t,x) * F (u (t,x))‖ₑ ^ q := by
  have hprod : volume.restrict (I ×ˢ U) =
      (volume.restrict I).prod (volume.restrict U) := by
    rw [Measure.volume_eq_prod, Measure.prod_restrict]
  have hm : AEMeasurable (fun z : ℝ × Vec d => ENNReal.ofReal (ρ z.2) *
      ‖η z * F (u z)‖ₑ ^ q) (volume.restrict (I ×ˢ U)) := by
    exact (ENNReal.measurable_ofReal.comp (hcoeff.1.comp measurable_snd)).aemeasurable.mul
      ((hη.aemeasurable.mul (hF.measurable.comp_aemeasurable hu.1.aemeasurable)).enorm.pow_const q)
  rw [hprod] at hm
  simp_rw [← Real.enorm_eq_ofReal_abs]
  rw [hprod, lintegral_prod _ hm]

/-- The native nested Sobolev bound controls the full power on the inner
cylinder after removing the truncation. -/
theorem c11_weighted_truncated_power_cutoff_nested_lintegral_le {d : ℕ} {κ : ℝ}
    (hκ : 0 < κ) {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (hcoeff : IsUniformlyElliptic κ ρ α)
    {I : Set ℝ} {U : Set (Vec d)} {u η : ℝ × Vec d → ℝ}
    {H : ℝ × Vec d → Vec d} (hu : IsWeightedCaloric ρ α I U u H)
    {S : Set (ℝ × Vec d)} (hS : MeasurableSet S) (hSV : S ⊆ I ×ˢ U)
    (hpos : ∀ᵐ z ∂volume.restrict S, 0 ≤ u z)
    (hη : Continuous η) (hηone : ∀ z ∈ S, η z = 1)
    {p ε : ℝ} (hp : 0 ≤ p) (hε : 0 ≤ ε)
    (G : ℕ → ℝ → ℝ) (hG : ∀ n, Continuous (G n))
    (hpower : ∀ (n : ℕ) (s : ℝ), 0 ≤ s → s ≤ (n : ℝ) →
      G n s = (s + ε) ^ (p / 2)) (B : ℝ≥0∞)
    (hbound : ∀ n, (∫⁻ t in I, ∫⁻ x in U, ENNReal.ofReal (ρ x) *
      ‖η (t,x) * G n (u (t,x))‖ₑ ^ (2 * ((d : ℝ) + 2) / d)) ≤ B) :
    ∫⁻ z in S, ENNReal.ofReal (u z + ε) ^ (p * (((d : ℝ) + 2) / d)) ≤
      ENNReal.ofReal κ⁻¹ * B := by
  apply c11_weighted_truncated_power_cutoff_lintegral_le hκ hcoeff hS hSV
    (hu.1.aemeasurable.mono_measure (Measure.restrict_mono hSV le_rfl)) hpos hηone hp hε G hG hpower B
  intro n
  rw [c11_weighted_caloric_cutoff_lintegral_prod hcoeff hu hη (hG n)]
  exact hbound n

/-- The canonical truncated power pair satisfies the pointwise inequalities
needed by the weighted ramp and cutoff energy estimates. -/
theorem c11_truncated_power_energy_structure {p ε : ℝ} (hp : 1 < p)
    (hε : 0 < ε) (n : ℕ) (s : ℝ) (hs : 0 ≤ s) :
    let F := PDE.Parabolic.LocalMax.powF p ε n
    let G := PDE.Parabolic.LocalMax.powG p ε n
    let K := 2 + p / (p - 1)
    0 ≤ F s ∧ 0 ≤ deriv (deriv F) s ∧
      deriv F s ^ 2 ≤ K * deriv (deriv F) s * F s ∧
      G s ^ 2 ≤ K * F s ∧ deriv G s ^ 2 ≤ K * deriv (deriv F) s ∧
      F s ≤ (s + ε) ^ p := by
  open PDE.Parabolic.LocalMax in
  have hN : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hp1 : 0 < p - 1 := by linarith
  have hK : (2 + p / (p - 1)) * (p - 1) = 3 * p - 2 := by field_simp; ring
  have hK2 : 2 ≤ 2 + p / (p - 1) := by
    have : 0 ≤ p / (p - 1) := div_nonneg (by linarith) hp1.le
    linarith
  have key : powF1 p ε n s ^ 2 ≤ (2 + p / (p - 1)) * powF2 p ε n s * powF p ε n s ∧
      powG p ε n s ^ 2 ≤ (2 + p / (p - 1)) * powF p ε n s ∧
      powG1 p ε n s ^ 2 ≤ (2 + p / (p - 1)) * powF2 p ε n s := by
    generalize 2 + p / (p - 1) = K at hK hK2 ⊢
    by_cases hc : p ≤ 2 ∨ s ≤ (n : ℝ)
    · have hw : 0 < s + ε := by linarith
      obtain ⟨h1, h2, h3, h4⟩ := rpow_split hw p
      have ha : 0 < (s + ε) ^ (p - 2) := Real.rpow_pos_of_pos hw _
      have hh := struct_ineqs_uncapped hp hK hK2 ha h4 hw
      rw [powF1_eq_of_le hε hs hc, powF2, powCap_eq_of_le hs hc,
        powF_eq_of_le hε hs hc, powG_eq_of_le hε hs hc, powG1,
        powCap_eq_of_le hs hc, h1, h2, h3]
      exact hh
    · push Not at hc
      obtain ⟨hp2, hsN⟩ := hc
      have hL : 0 < (n : ℝ) + ε := by linarith
      obtain ⟨h1, h2, h3, h4⟩ := rpow_split hL p
      have ha : 0 < ((n : ℝ) + ε) ^ (p - 2) := Real.rpow_pos_of_pos hL _
      have hh := struct_ineqs_capped hp2 hK hK2 ha h4 hL (sub_nonneg.2 hsN.le)
      have hcap : powCap p ε n s = n + ε := powCap_eq_cap hp2 hsN.le hN
      rw [powF1_eq_of_ge hp2 hε hN hsN.le, powF2, hcap,
        powF_eq_of_ge hp2 hε hN hsN.le, powG_eq_of_ge hp2 hε hN hsN.le,
        powG1, hcap, h1, h2, h3]
      convert hh using 3 <;> ring
  dsimp only
  rw [deriv_deriv_powF hε hN, deriv_powF hε hN, deriv_powG hε hN]
  exact ⟨powF_nonneg hp hε hN hs, powF2_nonneg hp hε hN s,
    key.1, key.2.1, key.2.2, powF_le hp hε hN hs⟩

/-- The structural inequality for the canonical power family controls the
weighted Sobolev slice mass by the corresponding renormalized energy. -/
theorem c11_weighted_truncated_power_slice_mass_le {d : ℕ}
    {ρ : Vec d → ℝ} {U : Set (Vec d)}
    (v η : Vec d → ℝ) (hpos : ∀ᵐ x ∂volume.restrict U, 0 ≤ v x)
    {p ε : ℝ} (hp : 1 < p) (hε : 0 < ε) (n : ℕ) :
    (∫⁻ x in U, ENNReal.ofReal (ρ x) *
      ‖η x * PDE.Parabolic.LocalMax.powG p ε n (v x)‖ₑ ^ (2 : ℝ)) ≤
    ENNReal.ofReal (2 + p / (p - 1)) *
      ∫⁻ x in U, ENNReal.ofReal (ρ x) *
        ENNReal.ofReal (η x ^ 2 * PDE.Parabolic.LocalMax.powF p ε n (v x)) := by
  have hK : 0 ≤ 2 + p / (p - 1) := by positivity
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono_ae
  filter_upwards [hpos] with x hx
  have hG : PDE.Parabolic.LocalMax.powG p ε n (v x) ^ 2 ≤
      (2 + p / (p - 1)) * PDE.Parabolic.LocalMax.powF p ε n (v x) := by
    have hp1 : 0 < p - 1 := by linarith
    have hKeq : (2 + p / (p - 1)) * (p - 1) = 3 * p - 2 := by field_simp; ring
    have hK2 : 2 ≤ 2 + p / (p - 1) := by
      have : 0 ≤ p / (p - 1) := div_nonneg (by linarith) hp1.le
      linarith
    by_cases hc : p ≤ 2 ∨ v x ≤ (n : ℝ)
    · have hw : 0 < v x + ε := by linarith
      obtain ⟨_, h2, h3, h4⟩ := PDE.Parabolic.LocalMax.rpow_split hw p
      have ha : 0 < (v x + ε) ^ (p - 2) := Real.rpow_pos_of_pos hw _
      have hh := (PDE.Parabolic.LocalMax.struct_ineqs_uncapped hp hKeq hK2 ha h4 hw).2.1
      rw [PDE.Parabolic.LocalMax.powF_eq_of_le hε hx hc,
        PDE.Parabolic.LocalMax.powG_eq_of_le hε hx hc, h2, h3]
      exact hh
    · push Not at hc
      obtain ⟨hp2, hsN⟩ := hc
      have hN : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
      have hL : 0 < (n : ℝ) + ε := by linarith
      obtain ⟨h1, h2, h3, h4⟩ := PDE.Parabolic.LocalMax.rpow_split hL p
      have ha : 0 < ((n : ℝ) + ε) ^ (p - 2) := Real.rpow_pos_of_pos hL _
      have hh := (PDE.Parabolic.LocalMax.struct_ineqs_capped hp2 hKeq hK2 ha h4 hL
        (sub_nonneg.2 hsN.le)).2.1
      rw [PDE.Parabolic.LocalMax.powF_eq_of_ge hp2 hε hN hsN.le,
        PDE.Parabolic.LocalMax.powG_eq_of_ge hp2 hε hN hsN.le, h1, h2, h3]
      convert hh using 1 <;> ring
  rw [Real.enorm_eq_ofReal_abs, ENNReal.rpow_two, ← ENNReal.ofReal_pow (abs_nonneg _)]
  have hpoint : (η x * PDE.Parabolic.LocalMax.powG p ε n (v x)) ^ 2 ≤
      (2 + p / (p - 1)) * (η x ^ 2 * PDE.Parabolic.LocalMax.powF p ε n (v x)) := by
    nlinarith [mul_le_mul_of_nonneg_left hG (sq_nonneg (η x))]
  calc
    ENNReal.ofReal (ρ x) * ENNReal.ofReal (|η x * PDE.Parabolic.LocalMax.powG p ε n (v x)| ^ 2) ≤
        ENNReal.ofReal (ρ x) * ENNReal.ofReal ((2 + p / (p - 1)) *
          (η x ^ 2 * PDE.Parabolic.LocalMax.powF p ε n (v x))) := by
      gcongr
      simpa only [sq_abs] using hpoint
    _ = _ := by rw [ENNReal.ofReal_mul hK]; ac_rfl

/-- Applying weighted Sobolev to the canonical truncated powers and passing to
its limit gives the power gain from uniform slice and gradient bounds. -/
theorem c11_weighted_caloric_cutoff_power_gain (d : ℕ) (hd : 2 ≤ d)
    (κ : ℝ) (hκ : 0 < κ) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
    IsUniformlyElliptic κ ρ α → ∀ (I : Set ℝ) (U : Set (Vec d)),
    MeasurableSet I → IsOpen U → volume (I ×ˢ U) < ∞ →
    ∀ (u : ℝ × Vec d → ℝ) (H : ℝ × Vec d → Vec d),
    IsWeightedCaloric ρ α I U u H →
    ∀ (η : ℝ × Vec d → ℝ), ContDiff ℝ (⊤ : ℕ∞) η → HasCompactSupport η →
    (∀ᵐ t ∂volume.restrict I, IsSpatialTest U (fun x => η (t,x))) →
    ∀ K : Set (Vec d), IsCompact K → K ⊆ U →
    (∀ t x, x ∉ K → η (t,x) = 0) →
    ∀ S : Set (ℝ × Vec d), MeasurableSet S → S ⊆ I ×ˢ U →
    (∀ᵐ z ∂volume.restrict S, 0 ≤ u z) → (∀ z ∈ S, η z = 1) →
    ∀ p ε : ℝ, 1 < p → 0 < ε → ∀ A E : ℝ≥0∞,
    (∀ n : ℕ, ∀ᵐ t ∂volume.restrict I,
      (∫⁻ x in U, ENNReal.ofReal (ρ x) *
        ‖η (t,x) * PDE.Parabolic.LocalMax.powG p ε n (u (t,x))‖ₑ ^ (2 : ℝ)) ≤ A) →
    (∀ n : ℕ, (∫⁻ t in I, ∫⁻ x in U, ENNReal.ofReal
      (dot ((α x).mulVec
        (η (t,x) • (deriv (PDE.Parabolic.LocalMax.powG p ε n) (u (t,x)) • H (t,x)) +
          PDE.Parabolic.LocalMax.powG p ε n (u (t,x)) •
            (fun j => fderiv ℝ η (t,x) (0, unitVector j))))
        (η (t,x) • (deriv (PDE.Parabolic.LocalMax.powG p ε n) (u (t,x)) • H (t,x)) +
          PDE.Parabolic.LocalMax.powG p ε n (u (t,x)) •
            (fun j => fderiv ℝ η (t,x) (0, unitVector j))))) ≤ E) →
    (∫⁻ z in S, ENNReal.ofReal (u z + ε) ^ (p * (((d : ℝ) + 2) / d))) ≤
      ENNReal.ofReal κ⁻¹ * (C * A ^ (2 / (d : ℝ)) * E) := by
  obtain ⟨C, hC, hsob⟩ := c11_weighted_caloric_spacetime_cutoff_chain_sobolev d hd κ hκ
  refine ⟨C, hC, ?_⟩
  intro ρ α hcoeff I U hI hU hfinite u H hu η hη hcη htest K hK hKU hzero S hS hSV hpos hηone p ε hp hε A E hmass henergy
  let G : ℕ → ℝ → ℝ := fun n => PDE.Parabolic.LocalMax.powG p ε n
  have hG (n : ℕ) : ContDiff ℝ 1 (G n) :=
    PDE.Parabolic.LocalMax.powG_contDiff hε (Nat.cast_nonneg n)
  apply c11_weighted_truncated_power_cutoff_nested_lintegral_le hκ hcoeff hu hS hSV hpos
    hη.continuous hηone (by linarith) hε.le G (fun n => (hG n).continuous)
    (fun n s hs hsn => PDE.Parabolic.LocalMax.powG_eq_of_le hε hs (Or.inr hsn))
  intro n
  obtain ⟨M, hM, hdM⟩ := PDE.Parabolic.LocalMax.exists_powG1_bound hp hε (Nat.cast_nonneg n)
  have h := hsob ρ α hcoeff I U hI hU hfinite u H hu (G n) (hG n) M hM hdM
    η hη hcη htest K hK hKU hzero A (hmass n)
  refine h.trans ?_
  gcongr
  exact henergy n

/-- Nonlinear time chain rule when the known derivative is that of the
weighted value `r * v`. The spatially varying density can be fixed at each
spatial point in an application; no derivative of the density is used. -/
theorem c11_weighted_time_chain_identity {s t r : ℝ} (hst : s ≤ t) (hr : r ≠ 0)
    {v D ψ : ℝ → ℝ} (hD : IntervalIntegrable D volume s t)
    (hv : ∀ τ ∈ Set.Icc s t, r * v τ = r * v s + ∫ σ in s..τ, D σ)
    (hψ : ContDiff ℝ 1 ψ) {F : ℝ → ℝ} (hF : ContDiff ℝ 1 F)
    (hFLip : ∃ C : NNReal, LipschitzWith C F) :
    r * (F (v t) * ψ t - F (v s) * ψ s) =
      ∫ τ in s..t, (r * F (v τ) * deriv ψ τ + deriv F (v τ) * ψ τ * D τ) := by
  have hv' : ∀ τ ∈ Set.Icc s t, v τ = v s + ∫ σ in s..τ, D σ / r := by
    intro τ hτ
    rw [intervalIntegral.integral_div]
    have h := hv τ hτ
    field_simp
    <;> nlinarith [h]
  have hchain := PDE.Parabolic.Chain.time_chain_identity hst (hD.div_const r) hv' hψ hF hFLip
  calc
    _ = r * ∫ τ in s..t, (F (v τ) * deriv ψ τ + deriv F (v τ) * ψ τ * (D τ / r)) :=
      congrArg (fun x => r * x) hchain
    _ = _ := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro τ hτ
      field_simp
      <;> ring

/-- Negating a weighted caloric function preserves its equation and gradient. -/
theorem c11_weighted_caloric_neg {d : ℕ} {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    {I : Set ℝ} {U : Set (Vec d)} {u : ℝ × Vec d → ℝ}
    {G : ℝ × Vec d → Vec d} (hu : IsWeightedCaloric ρ α I U u G) :
    IsWeightedCaloric ρ α I U (fun z => -u z) (fun z => -G z) := by
  refine ⟨hu.1.neg, hu.2.1.neg, ?_, ?_, ?_⟩
  · simpa [euclideanNorm, euclideanSq, dot] using hu.2.2.1
  · filter_upwards [hu.2.2.2.1] with t ht
    intro i
    obtain ⟨hf, hg, h⟩ := ht i
    refine ⟨hf.neg, hg.neg, ?_⟩
    intro φ hφ
    simpa only [Pi.neg_apply, neg_mul, integral_neg, neg_neg] using
      congrArg Neg.neg (h φ hφ)
  · intro ψ hψ hc hs
    have h := hu.2.2.2.2 ψ hψ hc hs
    have heq : (fun z : ℝ × Vec d =>
        -(ρ z.2 * -u z) * fderiv ℝ ψ z (1, 0) +
          dot ((α z.2).mulVec (-G z))
            (fun j => fderiv ℝ ψ z (0, unitVector j))) =
        (fun z : ℝ × Vec d => -(
          -(ρ z.2 * u z) * fderiv ℝ ψ z (1, 0) +
            dot ((α z.2).mulVec (G z))
              (fun j => fderiv ℝ ψ z (0, unitVector j)))) := by
      funext z
      simp [Matrix.mulVec_neg, dot, Finset.sum_neg_distrib, add_comm]
    rw [heq, integral_neg, h, neg_zero]

/-- The square of a compact spacetime cutoff multiplied by a time ramp is
an admissible smooth test, with its literal time and spatial derivatives. -/
theorem c11_weighted_ramp_test {d : ℕ} (η : ℝ × Vec d → ℝ)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (t₁ h : ℝ) :
    let ψ : ℝ × Vec d → ℝ := fun z => η z ^ 2 * PDE.Parabolic.LocalMax.timeRamp t₁ h z.1
    ContDiff ℝ (⊤ : ℕ∞) ψ ∧ HasCompactSupport ψ ∧ tsupport ψ ⊆ tsupport η ∧
    (∀ z, fderiv ℝ ψ z (1, 0) =
      2 * η z * fderiv ℝ η z (1, 0) * PDE.Parabolic.LocalMax.timeRamp t₁ h z.1 -
        η z ^ 2 * PDE.Parabolic.LocalMax.rampKernel t₁ h z.1) ∧
    (∀ z j, fderiv ℝ ψ z (0, unitVector j) =
      2 * η z * PDE.Parabolic.LocalMax.timeRamp t₁ h z.1 *
        fderiv ℝ η z (0, unitVector j)) := by
  let χ := PDE.Parabolic.LocalMax.timeRamp t₁ h
  let ψ : ℝ × Vec d → ℝ := fun z => η z ^ 2 * χ z.1
  have hχ := PDE.Parabolic.LocalMax.timeRamp_contDiff t₁ h
  have hηd : Differentiable ℝ η := hη.differentiable (by simp)
  have hχd : Differentiable ℝ χ := hχ.differentiable (by simp)
  have hp : (fun z => η z ^ 2) = fun z => η z * η z := by
    funext z
    rw [pow_two]
  have hd (z : ℝ × Vec d) := ((hηd z).hasFDerivAt.mul (hηd z).hasFDerivAt).mul
    ((hχd z.1).hasFDerivAt.comp z (hasFDerivAt_fst (𝕜 := ℝ)))
  have heq : ψ = fun z => (η z * η z) * χ z.1 := by
    funext z
    dsimp [ψ]
    rw [pow_two]
  have hs : tsupport ψ ⊆ tsupport η := by
    change tsupport (fun z => η z ^ 2 * χ z.1) ⊆ tsupport η
    exact tsupport_mul_subset_left.trans (by rw [hp]; exact tsupport_mul_subset_left)
  refine ⟨(hη.pow 2).mul (hχ.comp contDiff_fst), ?_, hs, ?_, ?_⟩
  · exact hηc.of_isClosed_subset (isClosed_tsupport ψ) hs
  · intro z
    change fderiv ℝ ψ z (1, 0) = _
    have hd' := hd z
    change HasFDerivAt (fun w => (η w * η w) * χ w.1) _ z at hd'
    rw [heq, hd'.fderiv]
    simp [χ, fderiv_apply_one_eq_deriv, PDE.Parabolic.LocalMax.deriv_timeRamp] <;> ring
  · intro z j
    change fderiv ℝ ψ z (0, unitVector j) = _
    have hd' := hd z
    change HasFDerivAt (fun w => (η w * η w) * χ w.1) _ z at hd'
    rw [heq, hd'.fderiv]
    simp [χ] <;> ring


/-- Pointwise ramp-energy bound with the density in the time term and the
ellipticity constant retained in the gradient term. -/
theorem c11_weighted_ramp_pointwise_lower
    {ρ κ F0 F1 F2 K L Q E N η τ χ χ' P : ℝ}
    (hρ : 0 ≤ ρ) (hF0 : 0 ≤ F0) (hF2 : 0 ≤ F2)
    (hK : 0 ≤ K) (hL : 0 ≤ L) (hQ : 0 ≤ Q)
    (hN : 0 ≤ N) (hχ : 0 ≤ χ) (hcoerc : κ * E ≤ Q)
    (hF : F1 ^ 2 ≤ K * F2 * F0) (hP : P ^ 2 ≤ L * Q * N) :
    ρ * F0 * η ^ 2 * (-χ') + κ / 2 * F2 * E * η ^ 2 * χ -
        χ * (F0 * (2 * ρ * |η| * |τ| + 2 * L * K * N)) ≤
      -(ρ * F0 * (2 * η * τ * χ + η ^ 2 * χ')) +
        F1 * (2 * η * χ * P) + F2 * Q * η ^ 2 * χ := by
  have hY := PDE.Parabolic.LocalMax.abs_young_le (η := η) hF0 hF2 hK hL hQ hN hχ hF hP
  have hY' := (abs_le.mp hY).1
  have hT : ρ * F0 * (2 * η * τ * χ) ≤
      χ * (F0 * (2 * ρ * |η| * |τ|)) := by
    have h : η * τ ≤ |η| * |τ| := by rw [← abs_mul]; exact le_abs_self _
    have hmul := mul_le_mul_of_nonneg_left h (show 0 ≤ ρ * F0 * χ by positivity)
    nlinarith
  have hA : κ / 2 * F2 * E * η ^ 2 * χ ≤
      1 / 2 * F2 * Q * η ^ 2 * χ := by
    have hmul := mul_le_mul_of_nonneg_left hcoerc
      (show 0 ≤ 1 / 2 * F2 * η ^ 2 * χ by positivity)
    nlinarith
  nlinarith

/-- The flux cross term is controlled by the actual symmetric coefficient's
quadratic form and its upper ellipticity bound. -/
theorem c11_weighted_flux_cross_bound {d : ℕ} {κ : ℝ} (hκ : 0 < κ)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (h : IsUniformlyElliptic κ ρ α)
    (x e p : Vec d) :
    dot ((α x).mulVec e) p ^ 2 ≤
      κ⁻¹ * dot e ((α x).mulVec e) * euclideanSq p := by
  have hk : κ ≤ κ⁻¹ := (h.2.2 x).1.trans (h.2.2 x).2.1
  have hkone : κ ≤ 1 := by
    have := mul_le_mul_of_nonneg_left hk hκ.le
    have hi : κ * κ⁻¹ = 1 := mul_inv_cancel₀ hκ.ne'
    nlinarith [sq_nonneg (κ - 1)]
  have hΛ : 1 ≤ κ⁻¹ := (one_le_inv₀ hκ).2 hkone
  have hS : EinsteinFull.S5Elliptic (α x) κ⁻¹ := by
    refine ⟨hΛ, ?_, ?_, ?_⟩
    · intro j k
      have hs := congrFun (congrFun (h.2.2 x).2.2.1 j) k
      simpa [Matrix.transpose_apply] using hs.symm
    · intro v
      simpa only [inv_inv, EinsteinFull.ParabolicBridge.s5Bil_eq_vecDot,
        PDE.vecNormSq, PDE.vecDot, PDE.matVecMul, Matrix.mulVec, dotProduct,
        euclideanSq, dot, pow_two] using (h.2.2 x).2.2.2 v |>.1
    · intro v
      simpa only [EinsteinFull.ParabolicBridge.s5Bil_eq_vecDot,
        PDE.vecNormSq, PDE.vecDot, PDE.matVecMul, Matrix.mulVec, dotProduct,
        euclideanSq, dot, pow_two] using (h.2.2 x).2.2.2 v |>.2
  have hcs := EinsteinFull.s5Bil_sq_le hS p e
  have hu := hS.upper p
  have hq := EinsteinFull.s5Bil_self_nonneg hS e
  have hh := mul_le_mul_of_nonneg_right hu hq
  have hp := hcs.trans hh
  have hcross : dot ((α x).mulVec e) p = EinsteinFull.s5Bil (α x) p e := by
    rw [EinsteinFull.ParabolicBridge.s5Bil_eq_vecDot, PDE.vecDot_comm]
    rfl
  rw [hcross]
  simp only [EinsteinFull.ParabolicBridge.s5Bil_eq_vecDot,
    PDE.vecNormSq, PDE.vecDot, PDE.matVecMul, Matrix.mulVec, dotProduct,
    euclideanSq, dot, pow_two] at hp ⊢
  convert hp using 1 <;> ring

/-- The pointwise weighted ramp estimate for the original coefficient field. -/
theorem c11_weighted_ramp_coefficient_lower {d : ℕ} {κ : ℝ} (hκ : 0 < κ)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (h : IsUniformlyElliptic κ ρ α)
    (x e p : Vec d) {F0 F1 F2 K η τ χ χ' : ℝ}
    (hF0 : 0 ≤ F0) (hF2 : 0 ≤ F2) (hK : 0 ≤ K) (hχ : 0 ≤ χ)
    (hF : F1 ^ 2 ≤ K * F2 * F0) :
    ρ x * F0 * η ^ 2 * (-χ') + κ / 2 * F2 * euclideanSq e * η ^ 2 * χ -
        χ * (F0 * (2 * ρ x * |η| * |τ| + 2 * κ⁻¹ * K * euclideanSq p)) ≤
      -(ρ x * F0 * (2 * η * τ * χ + η ^ 2 * χ')) +
        F1 * (2 * η * χ * dot ((α x).mulVec e) p) +
        F2 * dot e ((α x).mulVec e) * η ^ 2 * χ := by
  have he : 0 ≤ euclideanSq e := PDE.vecNormSq_nonneg e
  have hp : 0 ≤ euclideanSq p := PDE.vecNormSq_nonneg p
  have hc := (h.2.2 x).2.2.2 e |>.1
  have hq : 0 ≤ dot e ((α x).mulVec e) := (mul_nonneg hκ.le he).trans hc
  exact c11_weighted_ramp_pointwise_lower ((h.2.2 x).1.trans' hκ.le)
    hF0 hF2 hK (inv_nonneg.mpr hκ.le) hq hp hχ hc hF
    (c11_weighted_flux_cross_bound hκ h x e p)

/-- Integrate the two nonnegative parts of a ramp inequality against the
integrable renormalized weak integrand and its error term. -/
theorem c11_integrate_ramp_bound {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {A B W R : Ω → ℝ} (hW : Integrable W μ) (hR : Integrable R μ)
    (hzero : ∫ z, W z ∂μ = 0)
    (hA : ∀ᵐ z ∂μ, 0 ≤ A z) (hB : ∀ᵐ z ∂μ, 0 ≤ B z)
    (hR0 : ∀ᵐ z ∂μ, 0 ≤ R z)
    (hbound : ∀ᵐ z ∂μ, A z + B z - R z ≤ W z) :
    (∫⁻ z, ENNReal.ofReal (A z) ∂μ) ≤ ∫⁻ z, ENNReal.ofReal (R z) ∂μ ∧
    (∫⁻ z, ENNReal.ofReal (B z) ∂μ) ≤ ∫⁻ z, ENNReal.ofReal (R z) ∂μ := by
  have hsum := hW.add hR
  change Integrable (fun z => W z + R z) μ at hsum
  have hsum0 : ∀ᵐ z ∂μ, 0 ≤ W z + R z := by
    filter_upwards [hA, hB, hbound] with z ha hb hh
    linarith
  have hEq : ∫⁻ z, ENNReal.ofReal (W z + R z) ∂μ =
      ∫⁻ z, ENNReal.ofReal (R z) ∂μ := by
    rw [← ofReal_integral_eq_lintegral_ofReal hsum hsum0,
      integral_add hW hR, hzero, zero_add,
      ofReal_integral_eq_lintegral_ofReal hR hR0]
  constructor <;> rw [← hEq] <;> apply lintegral_mono_ae
  · filter_upwards [hA, hB, hbound] with z ha hb hh
    exact ENNReal.ofReal_le_ofReal (by linarith)
  · filter_upwards [hA, hB, hbound] with z ha hb hh
    exact ENNReal.ofReal_le_ofReal (by linarith)

/-- Integrated weighted ramp estimate, conditional on the renormalized weak
identity and integrability of its integrand and the cutoff error. -/
theorem c11_weighted_ramp_integrated {d : ℕ} {κ : ℝ} (hκ : 0 < κ)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (h : IsUniformlyElliptic κ ρ α)
    {μ : Measure (ℝ × Vec d)} (G P : ℝ × Vec d → Vec d)
    (F0 F1 F2 η τ χ χ' : ℝ × Vec d → ℝ) {K : ℝ} (hK : 0 ≤ K)
    (hF : ∀ᵐ z ∂μ, 0 ≤ F0 z ∧ 0 ≤ F2 z ∧ F1 z ^ 2 ≤ K * F2 z * F0 z)
    (hχ : ∀ᵐ z ∂μ, 0 ≤ χ z ∧ χ' z ≤ 0) :
    let W : ℝ × Vec d → ℝ := fun z =>
      -(ρ z.2 * F0 z * (2 * η z * τ z * χ z + η z ^ 2 * χ' z)) +
        F1 z * (2 * η z * χ z * dot ((α z.2).mulVec (G z)) (P z)) +
        F2 z * dot (G z) ((α z.2).mulVec (G z)) * η z ^ 2 * χ z
    let R : ℝ × Vec d → ℝ := fun z => χ z * (F0 z *
      (2 * ρ z.2 * |η z| * |τ z| + 2 * κ⁻¹ * K * euclideanSq (P z)))
    Integrable W μ → Integrable R μ → (∫ z, W z ∂μ) = 0 →
    (∫⁻ z, ENNReal.ofReal (ρ z.2 * F0 z * η z ^ 2 * (-χ' z)) ∂μ) ≤
        ∫⁻ z, ENNReal.ofReal (R z) ∂μ ∧
      (∫⁻ z, ENNReal.ofReal (κ / 2 * F2 z * euclideanSq (G z) * η z ^ 2 * χ z) ∂μ) ≤
        ∫⁻ z, ENNReal.ofReal (R z) ∂μ := by
  dsimp only
  intro hW hR hzero
  apply c11_integrate_ramp_bound hW hR hzero
  · filter_upwards [hF, hχ] with z hf hc
    have hρ : 0 ≤ ρ z.2 := hκ.le.trans (h.2.2 z.2).1
    have : 0 ≤ -χ' z := neg_nonneg.mpr hc.2
    have := hf.1
    positivity
  · filter_upwards [hF, hχ] with z hf hc
    have he : 0 ≤ euclideanSq (G z) := PDE.vecNormSq_nonneg _
    have := hf.2.1
    have := hc.1
    positivity
  · filter_upwards [hF, hχ] with z hf hc
    have hρ : 0 ≤ ρ z.2 := hκ.le.trans (h.2.2 z.2).1
    have hp : 0 ≤ euclideanSq (P z) := PDE.vecNormSq_nonneg _
    have hi : 0 ≤ κ⁻¹ := inv_nonneg.mpr hκ.le
    have := hf.1
    have := hc.1
    positivity
  · filter_upwards [hF, hχ] with z hf hc
    exact c11_weighted_ramp_coefficient_lower hκ h z.2 (G z) (P z)
      hf.1 hf.2.1 hK hc.1 hf.2.2

/-- A uniform bound on the cutoff derivatives controls the weighted ramp
error by the mass of the truncated power. -/
theorem c11_weighted_ramp_error_le_mass {d : ℕ} {μ : Measure (ℝ × Vec d)}
    (ρ : Vec d → ℝ) (F0 η τ χ : ℝ × Vec d → ℝ)
    (P : ℝ × Vec d → Vec d) (κ K B : ℝ) (hB : 0 ≤ B)
    (hF : ∀ᵐ z ∂μ, 0 ≤ F0 z) (hχ : ∀ᵐ z ∂μ, 0 ≤ χ z ∧ χ z ≤ 1)
    (hcut : ∀ᵐ z ∂μ, 0 ≤ 2 * ρ z.2 * |η z| * |τ z| +
        2 * κ⁻¹ * K * euclideanSq (P z) ∧
      2 * ρ z.2 * |η z| * |τ z| + 2 * κ⁻¹ * K * euclideanSq (P z) ≤ B) :
    (∫⁻ z, ENNReal.ofReal (χ z * (F0 z *
      (2 * ρ z.2 * |η z| * |τ z| + 2 * κ⁻¹ * K * euclideanSq (P z)))) ∂μ) ≤
      ENNReal.ofReal B * ∫⁻ z, ENNReal.ofReal (F0 z) ∂μ := by
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono_ae
  filter_upwards [hF, hχ, hcut] with z hf hc ht
  rw [← ENNReal.ofReal_mul hB]
  apply ENNReal.ofReal_le_ofReal
  have hp : 0 ≤ F0 z * (2 * ρ z.2 * |η z| * |τ z| +
      2 * κ⁻¹ * K * euclideanSq (P z)) := mul_nonneg hf ht.1
  have h1 : χ z * (F0 z * (2 * ρ z.2 * |η z| * |τ z| +
      2 * κ⁻¹ * K * euclideanSq (P z))) ≤
      F0 z * (2 * ρ z.2 * |η z| * |τ z| + 2 * κ⁻¹ * K * euclideanSq (P z)) := by
    nlinarith
  have h2 := mul_le_mul_of_nonneg_left ht.2 hf
  nlinarith

/-- One-sided ramp bounds yield weighted mass bounds on almost every time slice.
The cylinder uses the time-first product ordering of the native weak equation. -/
theorem c11_weighted_slice_le_of_ramp_bounds {d : ℕ} {U : Set (Vec d)}
    {s t : ℝ} {R : ℝ≥0∞} (ρ : Vec d → ℝ) (f : ℝ × Vec d → ℝ)
    (hρf : AEMeasurable (fun z : ℝ × Vec d => ENNReal.ofReal (ρ z.2 * f z))
      (volume.restrict (Set.Ioo s t ×ˢ U)))
    (hbound : ∀ t₁ ∈ Set.Ioo s t, ∀ h : ℝ, 0 < h →
      (∫⁻ z in Set.Ioo s t ×ˢ U,
        ENNReal.ofReal (PDE.Parabolic.LocalMax.rampKernel t₁ h z.1) *
          ENNReal.ofReal (ρ z.2 * f z)) ≤ R) :
    ∀ᵐ τ ∂volume.restrict (Set.Ioo s t),
      ∫⁻ x in U, ENNReal.ofReal (ρ x * f (τ, x)) ≤ R := by
  by_cases hR : R = ⊤
  · exact Filter.Eventually.of_forall fun _ => hR ▸ le_top
  have hprod : volume.restrict (Set.Ioo s t ×ˢ U) =
      (volume.restrict (Set.Ioo s t)).prod (volume.restrict U) := by
    rw [Measure.volume_eq_prod, Measure.prod_restrict]
  have hρf' := hρf
  rw [hprod] at hρf'
  apply PDE.Parabolic.LocalMax.ae_le_of_ramp_bounds hR hρf'.lintegral_prod_right'
  intro t₁ ht h hh
  have hm : AEMeasurable (fun z : ℝ × Vec d =>
      ENNReal.ofReal (PDE.Parabolic.LocalMax.rampKernel t₁ h z.1) *
        ENNReal.ofReal (ρ z.2 * f z))
      ((volume.restrict (Set.Ioo s t)).prod (volume.restrict U)) := by
    exact (ENNReal.measurable_ofReal.comp
      ((PDE.Parabolic.LocalMax.rampKernel_continuous t₁ h).measurable.comp measurable_fst)).aemeasurable.mul hρf'
  have hb := hbound t₁ ht h hh
  rw [hprod, lintegral_prod _ hm] at hb
  have heq : (∫⁻ τ in Set.Ioo s t,
      ENNReal.ofReal (PDE.Parabolic.LocalMax.rampKernel t₁ h τ) *
        ∫⁻ x in U, ENNReal.ofReal (ρ x * f (τ, x))) =
      ∫⁻ τ in Set.Ioo s t, ∫⁻ x in U,
        ENNReal.ofReal (PDE.Parabolic.LocalMax.rampKernel t₁ h τ) *
          ENNReal.ofReal (ρ x * f (τ, x)) := by
    apply lintegral_congr
    intro τ
    exact (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
  rw [heq]
  exact hb

/-- Ellipticity converts a weighted slice-energy bound to the ordinary
slice-energy bound used in the parabolic Sobolev estimate. -/
theorem c11_unweighted_slice_le_of_weighted {d : ℕ} {κ : ℝ} (hκ : 0 < κ)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (hc : IsUniformlyElliptic κ ρ α)
    {I : Set ℝ} {U : Set (Vec d)} (f : ℝ × Vec d → ℝ) (R : ℝ≥0∞)
    (hf : ∀ᵐ z ∂volume.restrict (I ×ˢ U), 0 ≤ f z)
    (hbound : ∀ᵐ t ∂volume.restrict I,
      ∫⁻ x in U, ENNReal.ofReal (ρ x * f (t, x)) ≤ R) :
    ∀ᵐ t ∂volume.restrict I,
      ∫⁻ x in U, ENNReal.ofReal (f (t, x)) ≤ ENNReal.ofReal κ⁻¹ * R := by
  have hf' : ∀ᵐ t ∂volume.restrict I, ∀ᵐ x ∂volume.restrict U, 0 ≤ f (t, x) := by
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict] at hf
    exact (Measure.ae_ae_of_ae_prod hf)
  filter_upwards [hf', hbound] with t ht hb
  calc
    ∫⁻ x in U, ENNReal.ofReal (f (t, x)) ≤
        ∫⁻ x in U, ENNReal.ofReal κ⁻¹ * ENNReal.ofReal (ρ x * f (t, x)) := by
      apply lintegral_mono_ae
      filter_upwards [ht] with x hx
      rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hκ.le)]
      apply ENNReal.ofReal_le_ofReal
      have hρ := (hc.2.2 x).1
      have hh : 1 ≤ κ⁻¹ * ρ x := by
        have := mul_le_mul_of_nonneg_left hρ (inv_nonneg.mpr hκ.le)
        simpa [inv_mul_cancel₀ hκ.ne'] using this
      nlinarith
    _ = ENNReal.ofReal κ⁻¹ * ∫⁻ x in U, ENNReal.ofReal (ρ x * f (t, x)) :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal κ⁻¹ * R := by gcongr

/-- The integrated renormalized identity for every smooth time ramp implies
an almost-everywhere weighted time-slice estimate. -/
theorem c11_weighted_slice_from_renormalized_ramps {d : ℕ} {κ : ℝ} (hκ : 0 < κ)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (hc : IsUniformlyElliptic κ ρ α)
    {U : Set (Vec d)} {s t : ℝ} (G P : ℝ × Vec d → Vec d)
    (F0 F1 F2 η τ : ℝ × Vec d → ℝ) {K B : ℝ} (hK : 0 ≤ K) (hB : 0 ≤ B)
    (hF : ∀ᵐ z ∂volume.restrict (Set.Ioo s t ×ˢ U),
      0 ≤ F0 z ∧ 0 ≤ F2 z ∧ F1 z ^ 2 ≤ K * F2 z * F0 z)
    (hcut : ∀ᵐ z ∂volume.restrict (Set.Ioo s t ×ˢ U),
      0 ≤ 2 * ρ z.2 * |η z| * |τ z| + 2 * κ⁻¹ * K * euclideanSq (P z) ∧
      2 * ρ z.2 * |η z| * |τ z| + 2 * κ⁻¹ * K * euclideanSq (P z) ≤ B)
    (hρf : AEMeasurable (fun z : ℝ × Vec d =>
      ENNReal.ofReal (ρ z.2 * (F0 z * η z ^ 2)))
      (volume.restrict (Set.Ioo s t ×ˢ U)))
    (hidentity : ∀ t₁ ∈ Set.Ioo s t, ∀ h : ℝ, 0 < h →
      let χ : ℝ × Vec d → ℝ := fun z => PDE.Parabolic.LocalMax.timeRamp t₁ h z.1
      let χ' : ℝ × Vec d → ℝ := fun z => -PDE.Parabolic.LocalMax.rampKernel t₁ h z.1
      let W : ℝ × Vec d → ℝ := fun z =>
        -(ρ z.2 * F0 z * (2 * η z * τ z * χ z + η z ^ 2 * χ' z)) +
          F1 z * (2 * η z * χ z * dot ((α z.2).mulVec (G z)) (P z)) +
          F2 z * dot (G z) ((α z.2).mulVec (G z)) * η z ^ 2 * χ z
      let E : ℝ × Vec d → ℝ := fun z => χ z * (F0 z *
        (2 * ρ z.2 * |η z| * |τ z| + 2 * κ⁻¹ * K * euclideanSq (P z)))
      Integrable W (volume.restrict (Set.Ioo s t ×ˢ U)) ∧
        Integrable E (volume.restrict (Set.Ioo s t ×ˢ U)) ∧
        (∫ z in Set.Ioo s t ×ˢ U, W z) = 0) :
    ∀ᵐ v ∂volume.restrict (Set.Ioo s t),
      ∫⁻ x in U, ENNReal.ofReal (ρ x * (F0 (v, x) * η (v, x) ^ 2)) ≤
        ENNReal.ofReal B * ∫⁻ z in Set.Ioo s t ×ˢ U, ENNReal.ofReal (F0 z) := by
  apply c11_weighted_slice_le_of_ramp_bounds ρ (fun z => F0 z * η z ^ 2) hρf
  intro t₁ ht h hh
  let χ : ℝ × Vec d → ℝ := fun z => PDE.Parabolic.LocalMax.timeRamp t₁ h z.1
  let χ' : ℝ × Vec d → ℝ := fun z => -PDE.Parabolic.LocalMax.rampKernel t₁ h z.1
  have hχ : ∀ᵐ z ∂volume.restrict (Set.Ioo s t ×ˢ U), 0 ≤ χ z ∧ χ' z ≤ 0 :=
    Filter.Eventually.of_forall fun z => ⟨PDE.Parabolic.LocalMax.timeRamp_nonneg _ _ _,
      neg_nonpos.mpr (PDE.Parabolic.LocalMax.rampKernel_nonneg hh _)⟩
  have hχ1 : ∀ᵐ z ∂volume.restrict (Set.Ioo s t ×ˢ U), 0 ≤ χ z ∧ χ z ≤ 1 :=
    Filter.Eventually.of_forall fun z => ⟨PDE.Parabolic.LocalMax.timeRamp_nonneg _ _ _,
      PDE.Parabolic.LocalMax.timeRamp_le_one _ _ _⟩
  obtain ⟨hW, hE, hz⟩ := hidentity t₁ ht h hh
  have hr := (c11_weighted_ramp_integrated hκ hc G P F0 F1 F2 η τ χ χ' hK hF hχ hW hE hz).1
  have he := c11_weighted_ramp_error_le_mass ρ F0 η τ χ P κ K B hB
    (hF.mono fun _ hz => hz.1) hχ1 hcut
  calc
    _ = ∫⁻ z in Set.Ioo s t ×ˢ U,
        ENNReal.ofReal (ρ z.2 * F0 z * η z ^ 2 * (-χ' z)) := by
          apply lintegral_congr
          intro z
          rw [← ENNReal.ofReal_mul (PDE.Parabolic.LocalMax.rampKernel_nonneg hh _)]
          congr 1
          dsimp [χ']
          ring
    _ ≤ _ := hr.trans he

/-- A uniform bound on the gradient energy with ramps approaching the top
of the cylinder gives the bound on the whole cylinder. -/
theorem c11_gradient_energy_le_of_ramp_bounds {d : ℕ} {U : Set (Vec d)}
    (hU : MeasurableSet U) {s t : ℝ} (A : ℝ × Vec d → ℝ) (R : ℝ≥0∞)
    (hbound : ∀ ε : ℝ, 0 < ε →
      (∫⁻ z in Set.Ioo s t ×ˢ U, ENNReal.ofReal
        (A z * PDE.Parabolic.LocalMax.timeRamp (t - ε) ε z.1)) ≤ R) :
    (∫⁻ z in Set.Ioo s t ×ˢ U, ENNReal.ofReal (A z)) ≤ R := by
  let ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hε : ∀ n, 0 < ε n := fun n => by dsimp [ε]; positivity
  let S : ℕ → Set (ℝ × Vec d) := fun n => Set.Ioo s (t - 2 * ε n) ×ˢ U
  have hmono : Monotone S := by
    intro n m hnm
    have hnm' : (n : ℝ) ≤ m := by exact_mod_cast hnm
    have hle : ε m ≤ ε n := by
      dsimp [ε]
      exact one_div_le_one_div_of_le (by positivity) (by linarith)
    exact Set.prod_mono (Set.Ioo_subset_Ioo_right (by linarith)) Set.Subset.rfl
  have hcover : Set.Ioo s t ×ˢ U ⊆ ⋃ n, S n := by
    rintro ⟨v, x⟩ ⟨⟨hvs, hvt⟩, hx⟩
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show 0 < (t - v) / 2 by linarith)
    exact Set.mem_iUnion.2 ⟨n, ⟨hvs, by dsimp [ε]; linarith⟩, hx⟩
  calc
    ∫⁻ z in Set.Ioo s t ×ˢ U, ENNReal.ofReal (A z) ≤
        ∫⁻ z in ⋃ n, S n, ENNReal.ofReal (A z) := lintegral_mono_set hcover
    _ = ⨆ n, ∫⁻ z in S n, ENNReal.ofReal (A z) :=
      setLIntegral_iUnion_of_directed _ hmono.directed_le
    _ ≤ R := by
      refine iSup_le fun n => ?_
      have hSm : MeasurableSet (S n) := measurableSet_Ioo.prod hU
      have hsub : S n ⊆ Set.Ioo s t ×ˢ U :=
        Set.prod_mono (Set.Ioo_subset_Ioo_right (by linarith [hε n])) Set.Subset.rfl
      have hone : ∀ z ∈ S n, PDE.Parabolic.LocalMax.timeRamp (t - ε n) (ε n) z.1 = 1 :=
        fun z hz => PDE.Parabolic.LocalMax.timeRamp_eq_one (hε n) (by linarith [hz.1.2])
      calc
        ∫⁻ z in S n, ENNReal.ofReal (A z) =
            ∫⁻ z in S n, ENNReal.ofReal
              (A z * PDE.Parabolic.LocalMax.timeRamp (t - ε n) (ε n) z.1) := by
          refine setLIntegral_congr_fun hSm fun z hz => ?_
          rw [hone z hz, mul_one]
        _ ≤ ∫⁻ z in Set.Ioo s t ×ˢ U, ENNReal.ofReal
            (A z * PDE.Parabolic.LocalMax.timeRamp (t - ε n) (ε n) z.1) :=
          lintegral_mono_set hsub
        _ ≤ R := hbound (ε n) (hε n)


/-- The renormalized ramp identities control the full-cylinder gradient energy. -/
theorem c11_weighted_gradient_from_renormalized_ramps {d : ℕ} {κ : ℝ} (hκ : 0 < κ)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (hc : IsUniformlyElliptic κ ρ α)
    {U : Set (Vec d)} (hU : MeasurableSet U) {s t : ℝ}
    (G P : ℝ × Vec d → Vec d) (F0 F1 F2 η τ : ℝ × Vec d → ℝ)
    {K B : ℝ} (hK : 0 ≤ K) (hB : 0 ≤ B)
    (hF : ∀ᵐ z ∂volume.restrict (Set.Ioo s t ×ˢ U),
      0 ≤ F0 z ∧ 0 ≤ F2 z ∧ F1 z ^ 2 ≤ K * F2 z * F0 z)
    (hcut : ∀ᵐ z ∂volume.restrict (Set.Ioo s t ×ˢ U),
      0 ≤ 2 * ρ z.2 * |η z| * |τ z| + 2 * κ⁻¹ * K * euclideanSq (P z) ∧
      2 * ρ z.2 * |η z| * |τ z| + 2 * κ⁻¹ * K * euclideanSq (P z) ≤ B)
    (hidentity : ∀ ε : ℝ, 0 < ε →
      let χ : ℝ × Vec d → ℝ := fun z => PDE.Parabolic.LocalMax.timeRamp (t - ε) ε z.1
      let χ' : ℝ × Vec d → ℝ := fun z => -PDE.Parabolic.LocalMax.rampKernel (t - ε) ε z.1
      let W : ℝ × Vec d → ℝ := fun z =>
        -(ρ z.2 * F0 z * (2 * η z * τ z * χ z + η z ^ 2 * χ' z)) +
          F1 z * (2 * η z * χ z * dot ((α z.2).mulVec (G z)) (P z)) +
          F2 z * dot (G z) ((α z.2).mulVec (G z)) * η z ^ 2 * χ z
      let E : ℝ × Vec d → ℝ := fun z => χ z * (F0 z *
        (2 * ρ z.2 * |η z| * |τ z| + 2 * κ⁻¹ * K * euclideanSq (P z)))
      Integrable W (volume.restrict (Set.Ioo s t ×ˢ U)) ∧
        Integrable E (volume.restrict (Set.Ioo s t ×ˢ U)) ∧
        (∫ z in Set.Ioo s t ×ˢ U, W z) = 0) :
    (∫⁻ z in Set.Ioo s t ×ˢ U,
      ENNReal.ofReal (κ / 2 * F2 z * euclideanSq (G z) * η z ^ 2)) ≤
      ENNReal.ofReal B * ∫⁻ z in Set.Ioo s t ×ˢ U, ENNReal.ofReal (F0 z) := by
  apply c11_gradient_energy_le_of_ramp_bounds hU
  intro ε hε
  let χ : ℝ × Vec d → ℝ := fun z => PDE.Parabolic.LocalMax.timeRamp (t - ε) ε z.1
  let χ' : ℝ × Vec d → ℝ := fun z => -PDE.Parabolic.LocalMax.rampKernel (t - ε) ε z.1
  have hχ : ∀ᵐ z ∂volume.restrict (Set.Ioo s t ×ˢ U), 0 ≤ χ z ∧ χ' z ≤ 0 :=
    Filter.Eventually.of_forall fun z => ⟨PDE.Parabolic.LocalMax.timeRamp_nonneg _ _ _,
      neg_nonpos.mpr (PDE.Parabolic.LocalMax.rampKernel_nonneg hε _)⟩
  have hχ1 : ∀ᵐ z ∂volume.restrict (Set.Ioo s t ×ˢ U), 0 ≤ χ z ∧ χ z ≤ 1 :=
    Filter.Eventually.of_forall fun z => ⟨PDE.Parabolic.LocalMax.timeRamp_nonneg _ _ _,
      PDE.Parabolic.LocalMax.timeRamp_le_one _ _ _⟩
  obtain ⟨hW, hE, hz⟩ := hidentity ε hε
  exact (c11_weighted_ramp_integrated hκ hc G P F0 F1 F2 η τ χ χ' hK hF hχ hW hE hz).2.trans
    (c11_weighted_ramp_error_le_mass ρ F0 η τ χ P κ K B hB
      (hF.mono fun _ hz => hz.1) hχ1 hcut)


/-- The coefficient energy of a cutoff chain is controlled by the
renormalized gradient and cutoff energies. -/
theorem c11_weighted_cutoff_chain_energy_pointwise {d : ℕ} {κ : ℝ} (hκ : 0 < κ)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (hc : IsUniformlyElliptic κ ρ α)
    (x G P : Vec d) (η g dg F F2 K : ℝ)
    (hg : g ^ 2 ≤ K * F) (hdg : dg ^ 2 ≤ K * F2) :
    dot ((α x).mulVec (η • (dg • G) + g • P))
        (η • (dg • G) + g • P) ≤
      2 * κ⁻¹ * K * (η ^ 2 * F2 * euclideanSq G + F * euclideanSq P) := by
  let V : Vec d := η • (dg • G) + g • P
  have hu := (hc.2.2 x).2.2.2 V |>.2
  have hdot : dot ((α x).mulVec V) V = dot V ((α x).mulVec V) := by
    exact PDE.vecDot_comm _ _
  rw [hdot]
  have htri : euclideanSq V ≤ 2 * euclideanSq (η • (dg • G)) +
      2 * euclideanSq (g • P) := by
    change PDE.vecNormSq (η • (dg • G) + g • P) ≤
      2 * PDE.vecNormSq (η • (dg • G)) + 2 * PDE.vecNormSq (g • P)
    simpa only [mul_add] using PDE.vecNormSq_add_le (η • (dg • G)) (g • P)
  have hfirst : euclideanSq (η • (dg • G)) ≤
      K * (η ^ 2 * F2 * euclideanSq G) := by
    change PDE.vecNormSq (η • (dg • G)) ≤ K * (η ^ 2 * F2 * PDE.vecNormSq G)
    rw [PDE.vecNormSq_smul, PDE.vecNormSq_smul]
    have h := mul_le_mul_of_nonneg_right hdg
      (mul_nonneg (sq_nonneg η) (PDE.vecNormSq_nonneg G))
    nlinarith
  have hsecond : euclideanSq (g • P) ≤ K * (F * euclideanSq P) := by
    change PDE.vecNormSq (g • P) ≤ K * (F * PDE.vecNormSq P)
    rw [PDE.vecNormSq_smul]
    have h := mul_le_mul_of_nonneg_right hg (PDE.vecNormSq_nonneg P)
    nlinarith
  have hi : 0 ≤ κ⁻¹ := inv_nonneg.mpr hκ.le
  have ht := mul_le_mul_of_nonneg_left htri hi
  have h1 := mul_le_mul_of_nonneg_left hfirst hi
  have h2 := mul_le_mul_of_nonneg_left hsecond hi
  nlinarith


/-- The coefficient energy of the actual truncated power cutoff is bounded by
its renormalized gradient energy and its cutoff error. -/
theorem c11_weighted_truncated_power_cutoff_energy_pointwise {d : ℕ} {κ : ℝ}
    (hκ : 0 < κ) {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (hc : IsUniformlyElliptic κ ρ α) {p ε : ℝ} (hp : 1 < p) (hε : 0 < ε)
    (n : ℕ) (s : ℝ) (hs : 0 ≤ s) (x G P : Vec d) (η : ℝ) :
    dot ((α x).mulVec
        (η • (deriv (PDE.Parabolic.LocalMax.powG p ε n) s • G) +
          PDE.Parabolic.LocalMax.powG p ε n s • P))
        (η • (deriv (PDE.Parabolic.LocalMax.powG p ε n) s • G) +
          PDE.Parabolic.LocalMax.powG p ε n s • P) ≤
      2 * κ⁻¹ * (2 + p / (p - 1)) *
        (η ^ 2 * deriv (deriv (PDE.Parabolic.LocalMax.powF p ε n)) s * euclideanSq G +
          PDE.Parabolic.LocalMax.powF p ε n s * euclideanSq P) := by
  have h := c11_truncated_power_energy_structure hp hε n s hs
  exact c11_weighted_cutoff_chain_energy_pointwise hκ hc x G P η
    (PDE.Parabolic.LocalMax.powG p ε n s)
    (deriv (PDE.Parabolic.LocalMax.powG p ε n) s)
    (PDE.Parabolic.LocalMax.powF p ε n s)
    (deriv (deriv (PDE.Parabolic.LocalMax.powF p ε n)) s)
    (2 + p / (p - 1)) h.2.2.2.1 h.2.2.2.2.1


/-- Integrating the truncated-power cutoff estimate gives a coefficient energy
bound in terms of the renormalized gradient and cutoff-error integrals. -/
theorem c11_weighted_truncated_power_cutoff_energy_integral {d : ℕ} {κ : ℝ}
    (hκ : 0 < κ) {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (hc : IsUniformlyElliptic κ ρ α) {I : Set ℝ} {U : Set (Vec d)}
    {u : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    (hu : IsWeightedCaloric ρ α I U u G)
    (hpos : ∀ᵐ z ∂volume.restrict (I ×ˢ U), 0 ≤ u z)
    (η : ℝ × Vec d → ℝ) (hη : Continuous η) (P : ℝ × Vec d → Vec d)
    {p ε : ℝ} (hp : 1 < p) (hε : 0 < ε) (n : ℕ) :
    (∫⁻ z in I ×ˢ U, ENNReal.ofReal
      (dot ((α z.2).mulVec
          (η z • (deriv (PDE.Parabolic.LocalMax.powG p ε n) (u z) • G z) +
            PDE.Parabolic.LocalMax.powG p ε n (u z) • P z))
          (η z • (deriv (PDE.Parabolic.LocalMax.powG p ε n) (u z) • G z) +
            PDE.Parabolic.LocalMax.powG p ε n (u z) • P z))) ≤
      ENNReal.ofReal (2 * κ⁻¹ * (2 + p / (p - 1))) *
        ((∫⁻ z in I ×ˢ U, ENNReal.ofReal
            (η z ^ 2 * deriv (deriv (PDE.Parabolic.LocalMax.powF p ε n)) (u z) *
              euclideanSq (G z))) +
          ∫⁻ z in I ×ˢ U, ENNReal.ofReal
            (PDE.Parabolic.LocalMax.powF p ε n (u z) * euclideanSq (P z))) := by
  let A : ℝ × Vec d → ℝ := fun z => η z ^ 2 *
    deriv (deriv (PDE.Parabolic.LocalMax.powF p ε n)) (u z) * euclideanSq (G z)
  let B : ℝ × Vec d → ℝ := fun z =>
    PDE.Parabolic.LocalMax.powF p ε n (u z) * euclideanSq (P z)
  have hA : AEMeasurable (fun z => ENNReal.ofReal (A z)) (volume.restrict (I ×ˢ U)) := by
    have hF : Continuous (deriv (deriv (PDE.Parabolic.LocalMax.powF p ε n))) := by
      rw [PDE.Parabolic.LocalMax.deriv_deriv_powF hε (Nat.cast_nonneg n)]
      exact PDE.Parabolic.LocalMax.powF2_continuous hε (Nat.cast_nonneg n)
    have hsq : Continuous (fun v : Vec d => euclideanSq v) := by
      unfold euclideanSq dot
      fun_prop
    exact ENNReal.measurable_ofReal.comp_aemeasurable
      (((hη.measurable.aemeasurable.pow_const 2).mul
        (hF.measurable.comp_aemeasurable hu.1.aestronglyMeasurable.aemeasurable)).mul
        (hsq.measurable.comp_aemeasurable hu.2.1.aemeasurable))
  have hC : 0 ≤ 2 * κ⁻¹ * (2 + p / (p - 1)) := by positivity
  calc
    _ ≤ ∫⁻ z in I ×ˢ U, ENNReal.ofReal (2 * κ⁻¹ * (2 + p / (p - 1))) *
        (ENNReal.ofReal (A z) + ENNReal.ofReal (B z)) := by
      apply lintegral_mono_ae
      filter_upwards [hpos] with z hz
      calc
        _ ≤ ENNReal.ofReal ((2 * κ⁻¹ * (2 + p / (p - 1))) * (A z + B z)) :=
          ENNReal.ofReal_le_ofReal
            (c11_weighted_truncated_power_cutoff_energy_pointwise hκ hc hp hε n (u z) hz
              z.2 (G z) (P z) (η z))
        _ = ENNReal.ofReal (2 * κ⁻¹ * (2 + p / (p - 1))) * ENNReal.ofReal (A z + B z) :=
          ENNReal.ofReal_mul hC
        _ ≤ _ := by gcongr; exact ENNReal.ofReal_add_le
    _ = _ := by rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_add_left' hA]


/-- The spatial cutoff error is controlled by the shifted power on the
support of the cutoff gradient. -/
theorem c11_truncated_power_cutoff_error_le {d : ℕ}
    {V S : Set (ℝ × Vec d)} (hS : MeasurableSet S) (hSV : S ⊆ V)
    (u : ℝ × Vec d → ℝ) (hpos : ∀ᵐ z ∂volume.restrict V, 0 ≤ u z)
    (P : ℝ × Vec d → Vec d) {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ z, euclideanSq (P z) ≤ B)
    (hsupp : ∀ z, z ∉ S → P z = 0)
    {p ε : ℝ} (hp : 1 < p) (hε : 0 < ε) (n : ℕ) :
    (∫⁻ z in V, ENNReal.ofReal
      (PDE.Parabolic.LocalMax.powF p ε n (u z) * euclideanSq (P z))) ≤
      ENNReal.ofReal B * ∫⁻ z in S, ENNReal.ofReal (u z + ε) ^ p := by
  calc
    _ ≤ ∫⁻ z in V, S.indicator
        (fun z => ENNReal.ofReal B * ENNReal.ofReal (u z + ε) ^ p) z := by
      apply lintegral_mono_ae
      filter_upwards [hpos] with z hz
      by_cases hzS : z ∈ S
      · rw [Set.indicator_of_mem hzS, ENNReal.ofReal_rpow_of_nonneg (by linarith) (by linarith),
          ← ENNReal.ofReal_mul hB]
        apply ENNReal.ofReal_le_ofReal
        have hF := c11_truncated_power_energy_structure hp hε n (u z) hz
        have hP : 0 ≤ euclideanSq (P z) := PDE.vecNormSq_nonneg (P z)
        have hr : 0 ≤ (u z + ε) ^ p := Real.rpow_nonneg (by linarith) _
        calc
          _ ≤ (u z + ε) ^ p * B := mul_le_mul hF.2.2.2.2.2 (hbound z) hP hr
          _ = _ := mul_comm _ _
      · rw [Set.indicator_of_notMem hzS, hsupp z hzS]
        simp [euclideanSq, dot]
    _ = ∫⁻ z in S, ENNReal.ofReal B * ENNReal.ofReal (u z + ε) ^ p := by
      rw [lintegral_indicator hS, Measure.restrict_restrict hS, Set.inter_eq_left.2 hSV]
    _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top


/-- The library cylinder cutoff and its derivatives in time-first coordinates. -/
theorem c11_time_first_cylinder_cutoff {d : ℕ} {r R T T' : ℝ}
    (hr : 0 ≤ r) (hrR : r < R) (hTT' : T < T')
    {B : ℝ} (hB : ∀ s, |deriv Real.smoothTransition s| ≤ B) :
    let η : ℝ × Vec d → ℝ := fun z =>
      PDE.Parabolic.LocalMax.cylCutoff r R T T' (z.2, z.1)
    ContDiff ℝ (⊤ : ℕ∞) η ∧
      (∀ z, 0 ≤ η z ∧ η z ≤ 1) ∧
      (∀ z, |fderiv ℝ η z (1, 0)| ≤ 2 * B / (T' - T)) ∧
      (∀ z, euclideanSq (fun j => fderiv ℝ η z (0, unitVector j)) ≤
        1024 / (R - r) ^ 2) := by
  let ξ : Vec d × ℝ → ℝ := PDE.Parabolic.LocalMax.cylCutoff r R T T'
  let η : ℝ × Vec d → ℝ := fun z => ξ (z.2, z.1)
  have hξ : ContDiff ℝ (⊤ : ℕ∞) ξ := PDE.Parabolic.LocalMax.cylCutoff_contDiff hr hrR T T'
  have hη : ContDiff ℝ (⊤ : ℕ∞) η := hξ.comp (contDiff_snd.prodMk contDiff_fst)
  have hswap (z : ℝ × Vec d) (v : ℝ × Vec d) :
      fderiv ℝ η z v = fderiv ℝ ξ (z.2, z.1) (v.2, v.1) := by
    have hs : HasFDerivAt (Prod.swap : ℝ × Vec d → Vec d × ℝ)
        ((ContinuousLinearMap.snd ℝ ℝ (Vec d)).prod
          (ContinuousLinearMap.fst ℝ ℝ (Vec d))) z :=
      hasFDerivAt_snd.prodMk hasFDerivAt_fst
    have h := ((hξ.differentiable (by simp)).differentiableAt.hasFDerivAt).comp z hs
    change fderiv ℝ (ξ ∘ Prod.swap) z v = _
    rw [h.fderiv]
    rfl
  refine ⟨hη, ?_, ?_, ?_⟩
  · intro z
    exact ⟨PDE.Parabolic.LocalMax.cylCutoff_nonneg r R T T' _,
      PDE.Parabolic.LocalMax.cylCutoff_le_one r R T T' _⟩
  · intro z
    rw [hswap]
    exact PDE.Parabolic.LocalMax.abs_parTimeDeriv_cylCutoff_le hB hr hrR hTT' _
  · intro z
    have heq : (fun j => fderiv ℝ η z (0, unitVector j)) =
        PDE.parSpaceGrad ξ (z.2, z.1) := by
      funext j
      rw [hswap]
      simp only [PDE.parSpaceGrad, PDE.basisVec, unitVector]
    rw [heq]
    exact PDE.Parabolic.LocalMax.vecNormSq_parSpaceGrad_cylCutoff_le hr hrR T T' _


/-- A smooth time cutoff that is one on a prescribed inner interval and
has compact support in the closed outer interval. -/
theorem c11_compact_time_cylinder_cutoff {T T' b h : ℝ}
    (hTT' : T < T') (hh : 0 < h) :
    let θ : ℝ → ℝ := fun t =>
      PDE.Parabolic.LocalMax.cylTimeRamp T ((T' - T) / 2) t *
        PDE.Parabolic.LocalMax.timeRamp b h t
    ContDiff ℝ (⊤ : ℕ∞) θ ∧ HasCompactSupport θ ∧
      tsupport θ ⊆ Set.Icc T b ∧
      (∀ t, 0 ≤ θ t ∧ θ t ≤ 1) ∧
      (∀ t, T' ≤ t → t ≤ b - h → θ t = 1) := by
  let θ : ℝ → ℝ := fun t =>
    PDE.Parabolic.LocalMax.cylTimeRamp T ((T' - T) / 2) t *
      PDE.Parabolic.LocalMax.timeRamp b h t
  have hδ : 0 < (T' - T) / 2 := by linarith
  have hleft (t : ℝ) (ht : t ≤ T) : θ t = 0 := by
    have hz : PDE.Parabolic.LocalMax.cylTimeRamp T ((T' - T) / 2) t = 0 := by
      apply Real.smoothTransition.zero_of_nonpos
      exact div_nonpos_of_nonpos_of_nonneg (by linarith) hδ.le
    simp [θ, hz]
  have hright (t : ℝ) (ht : b ≤ t) : θ t = 0 := by
    simp [θ, PDE.Parabolic.LocalMax.timeRamp_eq_zero hh ht]
  have hsupport : tsupport θ ⊆ Set.Icc T b := by
    apply closure_minimal _ isClosed_Icc
    intro t ht
    have ht0 : θ t ≠ 0 := ht
    exact ⟨le_of_not_gt (fun h => ht0 (hleft t h.le)),
      le_of_not_gt (fun h => ht0 (hright t h.le))⟩
  refine ⟨(PDE.Parabolic.LocalMax.cylTimeRamp_contDiff T _).mul
    (PDE.Parabolic.LocalMax.timeRamp_contDiff b h),
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport θ) hsupport, hsupport, ?_, ?_⟩
  · intro t
    have ha0 : 0 ≤ PDE.Parabolic.LocalMax.cylTimeRamp T ((T' - T) / 2) t :=
      Real.smoothTransition.nonneg _
    have ha1 : PDE.Parabolic.LocalMax.cylTimeRamp T ((T' - T) / 2) t ≤ 1 :=
      Real.smoothTransition.le_one _
    have hb0 := PDE.Parabolic.LocalMax.timeRamp_nonneg b h t
    have hb1 := PDE.Parabolic.LocalMax.timeRamp_le_one b h t
    exact ⟨mul_nonneg ha0 hb0, (mul_le_mul ha1 hb1 hb0 zero_le_one).trans_eq (one_mul 1)⟩
  · intro t ht ht'
    have ha : PDE.Parabolic.LocalMax.cylTimeRamp T ((T' - T) / 2) t = 1 := by
      apply Real.smoothTransition.one_of_one_le
      rw [le_div_iff₀ hδ]
      linarith
    simp [θ, ha, PDE.Parabolic.LocalMax.timeRamp_eq_one hh ht']


/-- A compact smooth time-first cutoff for nested parabolic cylinders. -/
theorem c11_compact_cylinder_cutoff {d : ℕ} {r R T T' b h : ℝ}
    (hr : 0 ≤ r) (hrR : r < R) (hTT' : T < T') (hh : 0 < h) :
    let θ : ℝ → ℝ := fun t =>
      PDE.Parabolic.LocalMax.cylTimeRamp T ((T' - T) / 2) t *
        PDE.Parabolic.LocalMax.timeRamp b h t
    let ξ : Vec d → ℝ := PDE.canonicalBallCutoff (0 : Vec d) r R
    let η : ℝ × Vec d → ℝ := fun z => θ z.1 * ξ z.2
    ContDiff ℝ (⊤ : ℕ∞) η ∧ HasCompactSupport η ∧
      tsupport η ⊆ Set.Icc T b ×ˢ tsupport ξ ∧
      tsupport ξ ⊆ PDE.euclideanBall (0 : Vec d) R ∧
      (∀ z, 0 ≤ η z ∧ η z ≤ 1) ∧
      (∀ z, T' ≤ z.1 → z.1 ≤ b - h → z.2 ∈ PDE.euclideanBall (0 : Vec d) r → η z = 1) := by
  let θ : ℝ → ℝ := fun t =>
    PDE.Parabolic.LocalMax.cylTimeRamp T ((T' - T) / 2) t *
      PDE.Parabolic.LocalMax.timeRamp b h t
  let ξ : Vec d → ℝ := PDE.canonicalBallCutoff (0 : Vec d) r R
  let η : ℝ × Vec d → ℝ := fun z => θ z.1 * ξ z.2
  obtain ⟨hθ, hθc, hθs, hθbounds, hθone⟩ := c11_compact_time_cylinder_cutoff hTT' hh
  have hξ : ContDiff ℝ (⊤ : ℕ∞) ξ := PDE.canonicalBallCutoff_smooth (0 : Vec d) hr hrR
  have hξc : HasCompactSupport ξ := PDE.canonicalBallCutoff_hasCompactSupport hr hrR
  have hsupport : tsupport η ⊆ tsupport θ ×ˢ tsupport ξ := by
    apply closure_minimal _ ((isClosed_tsupport θ).prod (isClosed_tsupport ξ))
    intro z hz
    have hθ0 : θ z.1 ≠ 0 := left_ne_zero_of_mul hz
    have hξ0 : ξ z.2 ≠ 0 := right_ne_zero_of_mul hz
    exact ⟨subset_tsupport θ hθ0, subset_tsupport ξ hξ0⟩
  refine ⟨(hθ.comp contDiff_fst).mul (hξ.comp contDiff_snd),
    (hθc.prod hξc).of_isClosed_subset (isClosed_tsupport η) hsupport,
    hsupport.trans (Set.prod_mono hθs Set.Subset.rfl),
    PDE.canonicalBallCutoff_tsupport_subset_outer hr hrR, ?_, ?_⟩
  · intro z
    have ht := hθbounds z.1
    have hx0 : 0 ≤ ξ z.2 := PDE.canonicalBallCutoff_nonneg _ _ _ _
    have hx1 : ξ z.2 ≤ 1 := PDE.canonicalBallCutoff_le_one _ _ _ _
    exact ⟨mul_nonneg ht.1 hx0, (mul_le_mul ht.2 hx1 hx0 zero_le_one).trans_eq (one_mul 1)⟩
  · intro z ht ht' hx
    simp [η, hθone z.1 ht ht', ξ, PDE.canonicalBallCutoff_eq_one_on_inner hr hrR hx]


/-- Derivative control for the compact cutoff, including the terminal ramp. -/
theorem c11_compact_cylinder_cutoff_derivatives {d : ℕ} {r R T T' b h : ℝ}
    (hr : 0 ≤ r) (hrR : r < R) (hTT' : T < T')
    {B : ℝ} (hB : ∀ s, |deriv Real.smoothTransition s| ≤ B) :
    let θ : ℝ → ℝ := fun t =>
      PDE.Parabolic.LocalMax.cylTimeRamp T ((T' - T) / 2) t *
        PDE.Parabolic.LocalMax.timeRamp b h t
    let ξ : Vec d → ℝ := PDE.canonicalBallCutoff (0 : Vec d) r R
    let η : ℝ × Vec d → ℝ := fun z => θ z.1 * ξ z.2
    (∀ z, |fderiv ℝ η z (1, 0)| ≤
      2 * B / (T' - T) + |PDE.Parabolic.LocalMax.rampKernel b h z.1|) ∧
    (∀ z, euclideanSq (fun j => fderiv ℝ η z (0, unitVector j)) ≤
      1024 / (R - r) ^ 2) := by
  let φ : ℝ × Vec d → ℝ := fun z =>
    PDE.Parabolic.LocalMax.cylCutoff r R T T' (z.2, z.1)
  let χ := PDE.Parabolic.LocalMax.timeRamp b h
  let η : ℝ × Vec d → ℝ := fun z => φ z * χ z.1
  obtain ⟨hφ, hφbounds, hφtime, hφspace⟩ :=
    c11_time_first_cylinder_cutoff (d := d) hr hrR hTT' hB
  have hχ := PDE.Parabolic.LocalMax.timeRamp_contDiff b h
  have hφd : Differentiable ℝ φ := hφ.differentiable (by simp)
  have hχd : Differentiable ℝ χ := hχ.differentiable (by simp)
  have hd (z : ℝ × Vec d) := (hφd z).hasFDerivAt.mul
    ((hχd z.1).hasFDerivAt.comp z (hasFDerivAt_fst (𝕜 := ℝ)))
  have hηeq : (fun z : ℝ × Vec d =>
      (PDE.Parabolic.LocalMax.cylTimeRamp T ((T' - T) / 2) z.1 *
        PDE.Parabolic.LocalMax.timeRamp b h z.1) *
          PDE.canonicalBallCutoff (0 : Vec d) r R z.2) = η := by
    funext z
    simp only [η, φ, χ, PDE.Parabolic.LocalMax.cylCutoff]
    ring
  change (∀ z, |fderiv ℝ _ z (1, 0)| ≤ _) ∧
    (∀ z, euclideanSq (fun j => fderiv ℝ _ z (0, unitVector j)) ≤ _)
  rw [hηeq]
  have htime (z : ℝ × Vec d) : fderiv ℝ η z (1, 0) =
      fderiv ℝ φ z (1, 0) * χ z.1 -
        φ z * PDE.Parabolic.LocalMax.rampKernel b h z.1 := by
    change fderiv ℝ (φ * χ ∘ Prod.fst) z (1, 0) = _
    rw [(hd z).fderiv]
    simp [χ, fderiv_apply_one_eq_deriv, PDE.Parabolic.LocalMax.deriv_timeRamp]
    ring
  have hspace (z : ℝ × Vec d) :
      (fun j => fderiv ℝ η z (0, unitVector j)) =
        χ z.1 • (fun j => fderiv ℝ φ z (0, unitVector j)) := by
    funext j
    change fderiv ℝ (φ * χ ∘ Prod.fst) z (0, unitVector j) = _
    rw [(hd z).fderiv]
    simp [χ, mul_comm]
  constructor
  · intro z
    rw [htime]
    have hχ0 : 0 ≤ χ z.1 := PDE.Parabolic.LocalMax.timeRamp_nonneg b h z.1
    have hχ1 : χ z.1 ≤ 1 := PDE.Parabolic.LocalMax.timeRamp_le_one b h z.1
    have hφ0 := (hφbounds z).1
    have hφ1 := (hφbounds z).2
    have ha : |fderiv ℝ φ z (1, 0) * χ z.1| ≤ 2 * B / (T' - T) := by
      rw [abs_mul, abs_of_nonneg hχ0]
      nlinarith [hφtime z, abs_nonneg (fderiv ℝ φ z (1, 0))]
    have hb : |φ z * PDE.Parabolic.LocalMax.rampKernel b h z.1| ≤
        |PDE.Parabolic.LocalMax.rampKernel b h z.1| := by
      rw [abs_mul, abs_of_nonneg hφ0]
      nlinarith [abs_nonneg (PDE.Parabolic.LocalMax.rampKernel b h z.1)]
    exact (abs_sub _ _).trans (add_le_add ha hb)
  · intro z
    rw [hspace]
    change PDE.vecNormSq _ ≤ _
    rw [PDE.vecNormSq_smul]
    have hχ0 : 0 ≤ χ z.1 := PDE.Parabolic.LocalMax.timeRamp_nonneg b h z.1
    have hχ1 : χ z.1 ≤ 1 := PDE.Parabolic.LocalMax.timeRamp_le_one b h z.1
    have hn := PDE.vecNormSq_nonneg (fun j => fderiv ℝ φ z (0, unitVector j))
    have hs : χ z.1 ^ 2 ≤ 1 := by nlinarith
    calc
      χ z.1 ^ 2 * PDE.vecNormSq (fun j => fderiv ℝ φ z (0, unitVector j)) ≤
          PDE.vecNormSq (fun j => fderiv ℝ φ z (0, unitVector j)) := by
            simpa using mul_le_mul_of_nonneg_right hs hn
      _ ≤ 1024 / (R - r) ^ 2 := hφspace z


/-- The renormalized weak identity evaluated at the actual smooth ramp test. -/
theorem c11_renormalized_ramp_identity {d : ℕ} {a b R : ℝ}
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} {u : ℝ × Vec d → ℝ}
    {G : ℝ × Vec d → Vec d} (F : ℝ → ℝ)
    (hchain : ∀ ψ : ℝ × Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ →
      HasCompactSupport ψ → tsupport ψ ⊆ Set.Ioo a b ×ˢ sourceBall 0 R →
      (∫ z in Set.Ioo a b ×ˢ sourceBall 0 R,
        -(ρ z.2 * F (u z)) * fderiv ℝ ψ z (1, 0) +
        deriv F (u z) * dot ((α z.2).mulVec (G z))
          (fun j => fderiv ℝ ψ z (0, unitVector j)) +
        deriv (deriv F) (u z) * dot ((α z.2).mulVec (G z)) (G z) * ψ z) = 0)
    (η : ℝ × Vec d → ℝ) (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hηc : HasCompactSupport η)
    (hηs : tsupport η ⊆ Set.Ioo a b ×ˢ sourceBall 0 R) (t₁ h : ℝ) :
    (∫ z in Set.Ioo a b ×ˢ sourceBall 0 R,
      -(ρ z.2 * F (u z) *
        (2 * η z * fderiv ℝ η z (1, 0) * PDE.Parabolic.LocalMax.timeRamp t₁ h z.1 +
          η z ^ 2 * (-PDE.Parabolic.LocalMax.rampKernel t₁ h z.1))) +
      deriv F (u z) * (2 * η z * PDE.Parabolic.LocalMax.timeRamp t₁ h z.1 *
        dot ((α z.2).mulVec (G z)) (fun j => fderiv ℝ η z (0, unitVector j))) +
      deriv (deriv F) (u z) * dot (G z) ((α z.2).mulVec (G z)) *
        η z ^ 2 * PDE.Parabolic.LocalMax.timeRamp t₁ h z.1) = 0 := by
  let ψ : ℝ × Vec d → ℝ := fun z => η z ^ 2 * PDE.Parabolic.LocalMax.timeRamp t₁ h z.1
  obtain ⟨hψ, hψc, hψs, hψt, hψx⟩ := c11_weighted_ramp_test η hη hηc t₁ h
  have hweak := hchain ψ hψ hψc (hψs.trans hηs)
  convert hweak using 1
  apply integral_congr_ae
  filter_upwards with z
  rw [hψt z]
  have hx : (fun j => fderiv ℝ ψ z (0, unitVector j)) =
      (2 * η z * PDE.Parabolic.LocalMax.timeRamp t₁ h z.1) •
        (fun j => fderiv ℝ η z (0, unitVector j)) := by
    funext j
    change fderiv ℝ ψ z (0, unitVector j) = _
    simpa only [Pi.smul_apply, smul_eq_mul] using hψx z j
  rw [hx]
  have hdot : dot ((α z.2).mulVec (G z)) (G z) =
      dot (G z) ((α z.2).mulVec (G z)) := by
    unfold dot
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hdot]
  simp only [dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  simp only [ψ]
  congr 1 <;> ring


/-- The quadratic flux term in the renormalized equation is integrable for
an actual weighted solution when the second chain derivative is bounded. -/
theorem c11_weighted_caloric_second_chain_flux_integrable {d : ℕ} {κ : ℝ}
    (hκ : 0 < κ) {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (h : IsUniformlyElliptic κ ρ α) {I : Set ℝ} {U : Set (Vec d)}
    {u : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    (hu : IsWeightedCaloric ρ α I U u G) (F : ℝ → ℝ)
    (hF : ContDiff ℝ 2 F) (M : ℝ)
    (hdF : ∀ r : ℝ, |deriv (deriv F) r| ≤ M) :
    Integrable (fun z => deriv (deriv F) (u z) *
      dot ((α z.2).mulVec (G z)) (G z)) (volume.restrict (I ×ˢ U)) := by
  let μ := volume.restrict (I ×ˢ U)
  have hG : MemLp G 2 μ := by
    apply hu.2.2.1.mono' hu.2.1
    exact Filter.Eventually.of_forall (fun z => by
      apply pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _) |>.mpr
      intro i
      exact EinsteinRelation.Regeneration.coordinate_abs_le_euclideanNorm (G z) i)
  have hg : ∀ i, MemLp (fun z => G z i) 2 μ := memLp_pi_iff.mp hG
  have hF' : ContDiff ℝ 1 (deriv F) :=
    PDE.Parabolic.Chain.contDiff_deriv_of_two hF
  have htop : MemLp (fun z => deriv (deriv F) (u z)) ∞ μ := by
    apply memLp_top_of_bound
      (hF'.continuous_deriv_one.comp_aestronglyMeasurable hu.1.aestronglyMeasurable) M
    exact Filter.Eventually.of_forall fun z => by simpa only [Real.norm_eq_abs] using hdF (u z)
  have hc (i : Fin d) : MemLp (fun z => deriv (deriv F) (u z) * G z i) 2 μ :=
    htop.mul (hg i)
  have hflux := c11_weighted_caloric_flux_memLp hκ h hu
  have hsum : Integrable (fun z => ∑ i : Fin d,
      ((α z.2).mulVec (G z)) i * (deriv (deriv F) (u z) * G z i)) μ :=
    integrable_finsetSum Finset.univ (fun i _ => (hflux i).integrable_mul (hc i))
  convert hsum using 1
  funext z
  simp only [dot, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring


/-- The mixed flux term is integrable for a compact smooth test when the
second derivative of the renormalization is bounded. -/
theorem c11_weighted_caloric_chain_test_flux_integrable {d : ℕ} {κ : ℝ}
    (hκ : 0 < κ) {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (h : IsUniformlyElliptic κ ρ α) {I : Set ℝ} {U : Set (Vec d)}
    {u : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    (hu : IsWeightedCaloric ρ α I U u G) (hfinite : volume (I ×ˢ U) < ∞)
    (F : ℝ → ℝ) (hF : ContDiff ℝ 2 F) (M : ℝ) (hM : 0 ≤ M)
    (hdF : ∀ r : ℝ, |deriv (deriv F) r| ≤ M)
    (ψ : ℝ × Vec d → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψc : HasCompactSupport ψ) :
    Integrable (fun z => deriv F (u z) * dot ((α z.2).mulVec (G z))
      (fun j => fderiv ℝ ψ z (0, unitVector j))) (volume.restrict (I ×ˢ U)) := by
  let μ := volume.restrict (I ×ˢ U)
  have hF' : ContDiff ℝ 1 (deriv F) := PDE.Parabolic.Chain.contDiff_deriv_of_two hF
  have hder : MemLp (fun z => deriv F (u z)) 2 μ :=
    (c11_weighted_caloric_spacetime_chain_memLp_finite hu hfinite (deriv F) hF' M hM hdF).1
  have hflux := c11_weighted_caloric_flux_memLp hκ h hu
  have hprod (j : Fin d) : Integrable (fun z =>
      (deriv F (u z) * ((α z.2).mulVec (G z)) j) *
        fderiv ℝ ψ z (0, unitVector j)) μ := by
    have hdcont : Continuous (fun z : ℝ × Vec d => fderiv ℝ ψ z (0, unitVector j)) :=
      (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
    have hdc : HasCompactSupport (fun z : ℝ × Vec d => fderiv ℝ ψ z (0, unitVector j)) :=
      hψc.fderiv_apply (𝕜 := ℝ) (0, unitVector j)
    obtain ⟨B, hB, hb⟩ := PDE.Parabolic.LocalMax.exists_abs_le_of_continuous_of_eq_zero_off
      hdcont hdc (fun z hz => image_eq_zero_of_notMem_tsupport
        (f := fun w : ℝ × Vec d => fderiv ℝ ψ w (0, unitVector j)) hz)
    exact (hder.integrable_mul (hflux j)).mul_bdd hdcont.aestronglyMeasurable
      (ae_of_all _ fun z => by simpa only [Real.norm_eq_abs] using hb z)
  have hsum := integrable_finsetSum Finset.univ (fun j _ => hprod j)
  convert hsum using 1
  funext z
  simp only [dot, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- The renormalized weighted mass is integrable on a finite cylinder. -/
theorem c11_weighted_caloric_renormalized_mass_integrable {d : ℕ} {κ : ℝ}
    (hκ : 0 < κ) {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (hell : IsUniformlyElliptic κ ρ α) {I : Set ℝ} {U : Set (Vec d)}
    {u : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    (hu : IsWeightedCaloric ρ α I U u G) (hfinite : volume (I ×ˢ U) < ∞)
    (F : ℝ → ℝ) (hF : ContDiff ℝ 2 F)
    (M : ℝ) (hM : 0 ≤ M) (hder : ∀ r, |deriv (deriv F) r| ≤ M) :
    Integrable (fun z => ρ z.2 * F (u z)) (volume.restrict (I ×ˢ U)) := by
  let μ := volume.restrict (I ×ˢ U)
  haveI : IsFiniteMeasure μ := ⟨by simpa [μ] using hfinite⟩
  have hρ : MemLp (fun z : ℝ × Vec d => ρ z.2) ∞ μ := by
    apply memLp_top_of_bound (hell.1.comp measurable_snd).aestronglyMeasurable κ⁻¹
    exact ae_of_all μ (fun z => by
      simpa only [Function.comp_apply, Real.norm_eq_abs,
        abs_of_nonneg (hκ.le.trans (hell.2.2 z.2).1)] using (hell.2.2 z.2).2.1)
  have hf : Integrable (fun z => F (u z)) μ :=
    c20_nonlinear_comp_integrable u hu.1 F hF M hM hder
  exact hf.mul_of_top_right hρ

/-- The spatial integral of the renormalized mass is time-integrable. -/
theorem c11_weighted_caloric_renormalized_mass_time_integrable {d : ℕ} {κ : ℝ}
    (hκ : 0 < κ) {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (hell : IsUniformlyElliptic κ ρ α) {I : Set ℝ} {U : Set (Vec d)}
    {u : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    (hu : IsWeightedCaloric ρ α I U u G) (hfinite : volume (I ×ˢ U) < ∞)
    (F : ℝ → ℝ) (hF : ContDiff ℝ 2 F)
    (M : ℝ) (hM : 0 ≤ M) (hder : ∀ r, |deriv (deriv F) r| ≤ M) :
    Integrable (fun t => ∫ x in U, ρ x * F (u (t, x))) (volume.restrict I) := by
  have h := c11_weighted_caloric_renormalized_mass_integrable hκ hell hu hfinite
    F hF M hM hder
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict] at h
  exact h.integral_prod_left

/-- The time-test term in the renormalized identity is integrable. -/
theorem c11_weighted_caloric_chain_time_test_integrable {d : ℕ} {κ : ℝ}
    (hκ : 0 < κ) {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (hell : IsUniformlyElliptic κ ρ α) {I : Set ℝ} {U : Set (Vec d)}
    {u : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    (hu : IsWeightedCaloric ρ α I U u G) (hfinite : volume (I ×ˢ U) < ∞)
    (F : ℝ → ℝ) (hF : ContDiff ℝ 2 F)
    (M : ℝ) (hM : 0 ≤ M) (hder : ∀ r, |deriv (deriv F) r| ≤ M)
    (ψ : ℝ × Vec d → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψc : HasCompactSupport ψ) :
    Integrable (fun z => (ρ z.2 * F (u z)) * fderiv ℝ ψ z (1, 0))
      (volume.restrict (I ×ˢ U)) := by
  have hd : Continuous (fun z : ℝ × Vec d => fderiv ℝ ψ z (1, 0)) :=
    (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hc : HasCompactSupport (fun z : ℝ × Vec d => fderiv ℝ ψ z (1, 0)) :=
    hψc.fderiv_apply (𝕜 := ℝ) (1, 0)
  obtain ⟨B, hB, hb⟩ := PDE.Parabolic.LocalMax.exists_abs_le_of_continuous_of_eq_zero_off
    hd hc (fun z hz => image_eq_zero_of_notMem_tsupport
      (f := fun w : ℝ × Vec d => fderiv ℝ ψ w (1, 0)) hz)
  exact (c11_weighted_caloric_renormalized_mass_integrable hκ hell hu hfinite
    F hF M hM hder).mul_bdd hd.aestronglyMeasurable
      (ae_of_all _ fun z => by simpa only [Real.norm_eq_abs] using hb z)

/-- The renormalization identity gives a continuous representative of the
actual weighted cutoff mass, with its signed flux balance. -/
theorem c11_weighted_cutoff_continuous_trace_of_renormalization
    {d : ℕ} {κ R a b : ℝ} (hκ : 0 < κ) (hR : 0 < R) (hab : a < b)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d) (hell : IsUniformlyElliptic κ ρ α)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hcal : IsWeightedCaloric ρ α (Set.Ioo a b) (sourceBall 0 R) u G)
    (hchain : ∀ (F : ℝ → ℝ), ContDiff ℝ 2 F → F 0 = 0 →
      ∀ M : ℝ, 0 ≤ M → (∀ r, |deriv (deriv F) r| ≤ M) →
      ∀ ψ : ℝ × Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Set.Ioo a b ×ˢ sourceBall 0 R →
      (∫ z in Set.Ioo a b ×ˢ sourceBall 0 R,
        -(ρ z.2 * F (u z)) * fderiv ℝ ψ z (1,0) +
        deriv F (u z) * dot ((α z.2).mulVec (G z))
          (fun j => fderiv ℝ ψ z (0,unitVector j)) +
        deriv (deriv F) (u z) * dot ((α z.2).mulVec (G z)) (G z) * ψ z) = 0)
    (χ : Vec d → ℝ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hχc : HasCompactSupport χ) (hχU : tsupport χ ⊆ sourceBall 0 R) :
    ∃ E : ℝ → ℝ, ContinuousOn E (Set.Ioo a b) ∧
      (∀ᵐ t ∂volume.restrict (Set.Ioo a b),
        E t = ∫ x in sourceBall 0 R, ρ x * χ x ^ 2 * u (t,x) ^ 2) ∧
      ∀ s ∈ Set.Ioo a b, ∀ t ∈ Set.Ioo a b,
        E t - E s = -2 * ∫ r in s..t,
          ∫ x in sourceBall 0 R,
            χ x ^ 2 * dot ((α x).mulVec (G (r,x))) (G (r,x)) +
            2 * χ x * u (r,x) * dot ((α x).mulVec (G (r,x)))
              (fun j => fderiv ℝ χ x (unitVector j)) := by
  apply c13_weighted_cutoff_energy_continuous_balance_of_distributional
    hκ hR hab ρ α hell u G hcal χ hχ hχc hχU
  intro η hη hηc hηI
  let θ : ℝ × Vec d → ℝ := fun z => η z.1 * χ z.2 ^ 2
  obtain ⟨hθ, hθc, hθs⟩ := c5_separated_square_cutoff η hη hηc hηI χ hχ hχc hχU
  let F : ℝ → ℝ := fun r => r ^ 2 / 2
  have hF : ContDiff ℝ 2 F := (contDiff_id.pow 2).div_const 2
  have hF' : deriv F = id := by
    funext r
    dsimp [F]
    simp [deriv_div_const]
  have hF'' : deriv (deriv F) = fun _ => 1 := by rw [hF']; simp
  have hw := hchain F hF (by simp [F]) 1 (by norm_num)
    (by intro r; rw [hF'']; norm_num) θ hθ hθc hθs
  have hmass := c13_weighted_cutoff_mass_integrable hκ ρ α hell
    (Set.Ioo a b) (sourceBall 0 R) u G hcal χ hχ hχc
  have hflux := c13_weighted_cutoff_energy_flux_integrable hκ ρ α hell
    (Set.Ioo a b) (sourceBall 0 R) u G hcal χ hχ hχc
  let μ := volume.restrict (Set.Ioo a b ×ˢ sourceBall (0 : Vec d) R)
  have hηtop : MemLp (fun z : ℝ × Vec d => η z.1) ∞ μ := by
    have ht := hη.continuous.memLp_top_of_hasCompactSupport hηc (Measure.map Prod.fst μ)
    exact ht.comp_of_map measurable_fst.aemeasurable
  have hdtop : MemLp (fun z : ℝ × Vec d => deriv η z.1) ∞ μ := by
    have ht := (hη.continuous_deriv (by simp)).memLp_top_of_hasCompactSupport
      hηc.deriv (Measure.map Prod.fst μ)
    exact ht.comp_of_map measurable_fst.aemeasurable
  have hA : Integrable (fun z : ℝ × Vec d =>
      deriv η z.1 * (ρ z.2 * χ z.2 ^ 2 * u z ^ 2)) μ := by
    convert hmass.mul_of_top_left hdtop using 1
    funext z
    simp only [Pi.mul_apply]
    ring
  have hB : Integrable (fun z : ℝ × Vec d => η z.1 *
      (χ z.2 ^ 2 * dot ((α z.2).mulVec (G z)) (G z) +
      2 * χ z.2 * u z * dot ((α z.2).mulVec (G z))
        (fun j => fderiv ℝ χ z.2 (unitVector j)))) μ := by
    convert hflux.mul_of_top_left hηtop using 1
    funext z
    simp only [Pi.mul_apply]
    ring
  have heq : (∫ z in Set.Ioo a b ×ˢ sourceBall 0 R,
      -((deriv η z.1 * (ρ z.2 * χ z.2 ^ 2 * u z ^ 2)) / 2) + η z.1 *
      (χ z.2 ^ 2 * dot ((α z.2).mulVec (G z)) (G z) +
      2 * χ z.2 * u z * dot ((α z.2).mulVec (G z))
        (fun j => fderiv ℝ χ z.2 (unitVector j)))) = 0 := by
    convert hw using 1
    apply integral_congr_ae
    filter_upwards with z
    rw [hF'', hF']
    simp only [id_eq, Pi.one_apply, one_mul, F, θ,
      c5_separated_square_cutoff_time_fderiv η (hη.differentiable (by simp)) χ
        (hχ.differentiable (by simp)),
      c5_separated_square_cutoff_fderiv η (hη.differentiable (by simp)) χ
        (hχ.differentiable (by simp))]
    have hdot : dot ((α z.2).mulVec (G z))
        (fun j => η z.1 * (2 * χ z.2 * fderiv ℝ χ z.2 (unitVector j))) =
        (2 * η z.1 * χ z.2) * dot ((α z.2).mulVec (G z))
          (fun j => fderiv ℝ χ z.2 (unitVector j)) := by
      simp only [dot, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    rw [hdot]
    ring
  have hn : Integrable (fun z : ℝ × Vec d =>
      -(deriv η z.1 * (ρ z.2 * χ z.2 ^ 2 * u z ^ 2) / 2)) μ := by
    convert (hA.div_const 2).neg using 1
  rw [integral_add hn hB, integral_neg, integral_div] at heq
  apply c5_weighted_square_time_slice_of_spacetime hκ ρ α hell
    (Set.Ioo a b) (sourceBall 0 R) u G hcal χ hχ hχc η hη hηc
  linarith

/-- The centered chain rule also yields the integrable ramp identity for an
uncentered nonlinearity, including the canonical truncated powers. -/
theorem c11_integrable_uncentered_renormalized_ramp {d : ℕ} {κ R a b : ℝ}
    (hκ : 0 < κ) (hR : 0 < R) (hab : a < b)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d) (hell : IsUniformlyElliptic κ ρ α)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hcal : IsWeightedCaloric ρ α (Set.Ioo a b) (sourceBall 0 R) u G)
    (F : ℝ → ℝ) (hF : ContDiff ℝ 2 F) (M : ℝ) (hM : 0 ≤ M)
    (hder : ∀ r, |deriv (deriv F) r| ≤ M)
    (η : ℝ × Vec d → ℝ) (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hηc : HasCompactSupport η)
    (hηs : tsupport η ⊆ Set.Ioo a b ×ˢ sourceBall 0 R) (t₁ h : ℝ) :
    let W : ℝ × Vec d → ℝ := fun z =>
      -(ρ z.2 * F (u z) *
        (2 * η z * fderiv ℝ η z (1, 0) * PDE.Parabolic.LocalMax.timeRamp t₁ h z.1 +
          η z ^ 2 * (-PDE.Parabolic.LocalMax.rampKernel t₁ h z.1))) +
      deriv F (u z) * (2 * η z * PDE.Parabolic.LocalMax.timeRamp t₁ h z.1 *
        dot ((α z.2).mulVec (G z)) (fun j => fderiv ℝ η z (0, unitVector j))) +
      deriv (deriv F) (u z) * dot (G z) ((α z.2).mulVec (G z)) *
        η z ^ 2 * PDE.Parabolic.LocalMax.timeRamp t₁ h z.1
    Integrable W (volume.restrict (Set.Ioo a b ×ˢ sourceBall 0 R)) ∧
      (∫ z in Set.Ioo a b ×ˢ sourceBall 0 R, W z) = 0 := by
  have hcenter : ContDiff ℝ 2 (fun r => F r - F 0) := hF.sub contDiff_const
  have hd := c20_deriv_sub_value_zero F
  have huncentered : ∀ ψ : ℝ × Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ →
      HasCompactSupport ψ → tsupport ψ ⊆ Set.Ioo a b ×ˢ sourceBall 0 R →
      (∫ z in Set.Ioo a b ×ˢ sourceBall 0 R,
        -(ρ z.2 * F (u z)) * fderiv ℝ ψ z (1,0) +
        deriv F (u z) * dot ((α z.2).mulVec (G z))
          (fun j => fderiv ℝ ψ z (0,unitVector j)) +
        deriv (deriv F) (u z) * dot ((α z.2).mulVec (G z)) (G z) * ψ z) = 0 := by
    intro ψ hψ hψc hψs
    apply c20_weighted_caloric_renormalization_of_centered hκ hR hab ρ α hell u G
      hcal F hF M hM hder ψ hψ hψc hψs
    exact c13_actual_weighted_caloric_renormalization hκ hR hab ρ α hell u G hcal
      (fun r => F r - F 0) hcenter (by simp) M hM
      (by simpa only [hd.2] using hder) ψ hψ hψc hψs
  constructor
  · let ψ : ℝ × Vec d → ℝ := fun z => η z ^ 2 * PDE.Parabolic.LocalMax.timeRamp t₁ h z.1
    obtain ⟨hψ, hψc, hψs, hψt, hψx⟩ := c11_weighted_ramp_test η hη hηc t₁ h
    have hi := c18_tested_nonlinear_pairing_integrable hκ hR hab ρ α hell 0 u G
      hcal.1 hcal.2.1 hcal.2.2.1 F hF M hM hder ψ hψ hψc (hψs.trans hηs)
    convert hi using 1
    funext z
    rw [hψt z]
    have hx : (fun j => fderiv ℝ ψ z (0, unitVector j)) =
        (2 * η z * PDE.Parabolic.LocalMax.timeRamp t₁ h z.1) •
          (fun j => fderiv ℝ η z (0, unitVector j)) := by
      funext j
      change fderiv ℝ ψ z (0, unitVector j) = _
      simpa only [Pi.smul_apply, smul_eq_mul] using hψx z j
    rw [hx]
    have hdot : dot ((α z.2).mulVec (G z)) (G z) =
        dot (G z) ((α z.2).mulVec (G z)) := PDE.vecDot_comm _ _
    rw [hdot]
    simp only [dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    simp only [ψ]
    congr 1 <;> ring
  · exact c11_renormalized_ramp_identity F huncentered η hη hηc hηs t₁ h

/-- The bounded cutoff error in the renormalized ramp identity is integrable. -/
theorem c11_integrable_renormalized_ramp_error {d : ℕ} {κ R a b : ℝ}
    (ρ : Vec d → ℝ) (α : Vec d → Mat d) (hell : IsUniformlyElliptic κ ρ α)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hcal : IsWeightedCaloric ρ α (Set.Ioo a b) (sourceBall 0 R) u G)
    (F : ℝ → ℝ) (hF : ContDiff ℝ 2 F) (M : ℝ) (hM : 0 ≤ M)
    (hder : ∀ r, |deriv (deriv F) r| ≤ M)
    (η : ℝ × Vec d → ℝ) (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (K B : ℝ) (t₁ h : ℝ)
    (hcut : ∀ᵐ z ∂volume.restrict (Set.Ioo a b ×ˢ sourceBall 0 R),
      0 ≤ 2 * ρ z.2 * |η z| * |fderiv ℝ η z (1, 0)| +
          2 * κ⁻¹ * K * euclideanSq (fun j => fderiv ℝ η z (0, unitVector j)) ∧
      2 * ρ z.2 * |η z| * |fderiv ℝ η z (1, 0)| +
          2 * κ⁻¹ * K * euclideanSq (fun j => fderiv ℝ η z (0, unitVector j)) ≤ B) :
    Integrable (fun z : ℝ × Vec d => PDE.Parabolic.LocalMax.timeRamp t₁ h z.1 *
      (F (u z) * (2 * ρ z.2 * |η z| * |fderiv ℝ η z (1, 0)| +
        2 * κ⁻¹ * K * euclideanSq (fun j => fderiv ℝ η z (0, unitVector j)))))
      (volume.restrict (Set.Ioo a b ×ˢ sourceBall 0 R)) := by
  let μ := volume.restrict (Set.Ioo a b ×ˢ sourceBall (0 : Vec d) R)
  let : IsFiniteMeasure μ := c18_intervalSourceCylinder_isFiniteMeasure a b R 0
  have hfi : Integrable (fun z => F (u z)) μ :=
    c20_nonlinear_comp_integrable u hcal.1 F hF M hM hder
  have ht : Continuous (fun z : ℝ × Vec d => fderiv ℝ η z (1, 0)) :=
    (hη.continuous_fderiv (by simp)).clm_apply continuous_const
  have hx (j : Fin d) : Continuous (fun z : ℝ × Vec d => fderiv ℝ η z (0, unitVector j)) :=
    (hη.continuous_fderiv (by simp)).clm_apply continuous_const
  have hρ : Measurable ρ := hell.1
  have hηm : Measurable η := hη.continuous.measurable
  have hm : Measurable (fun z : ℝ × Vec d =>
      2 * ρ z.2 * |η z| * |fderiv ℝ η z (1, 0)| +
        2 * κ⁻¹ * K * euclideanSq (fun j => fderiv ℝ η z (0, unitVector j))) := by
    unfold euclideanSq dot
    fun_prop
  have he := hfi.mul_bdd (c := B) hm.aestronglyMeasurable (by
    filter_upwards [hcut] with z hz
    simpa only [Real.norm_eq_abs, abs_of_nonneg hz.1] using hz.2)
  have hr := he.mul_bdd (c := 1)
    (((PDE.Parabolic.LocalMax.timeRamp_contDiff t₁ h).continuous.comp continuous_fst).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun z => by
      change ‖PDE.Parabolic.LocalMax.timeRamp t₁ h z.1‖ ≤ 1
      rw [Real.norm_eq_abs, abs_of_nonneg (PDE.Parabolic.LocalMax.timeRamp_nonneg _ _ _)]
      exact PDE.Parabolic.LocalMax.timeRamp_le_one t₁ h z.1)
  convert hr using 1 <;> ext z <;> dsimp only [Pi.mul_apply, Function.comp_apply] <;> ring

/-- Renormalization gives both the weighted time-slice and gradient bounds. -/
theorem c11_weighted_caloric_renormalized_energy_bounds {d : ℕ} {κ R a b : ℝ}
    (hκ : 0 < κ) (hR : 0 < R) (hab : a < b)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d) (hell : IsUniformlyElliptic κ ρ α)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hcal : IsWeightedCaloric ρ α (Set.Ioo a b) (sourceBall 0 R) u G)
    (F : ℝ → ℝ) (hF : ContDiff ℝ 2 F) (M : ℝ) (hM : 0 ≤ M)
    (hder : ∀ r, |deriv (deriv F) r| ≤ M)
    (η : ℝ × Vec d → ℝ) (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hηc : HasCompactSupport η)
    (hηs : tsupport η ⊆ Set.Ioo a b ×ˢ sourceBall 0 R)
    (K B : ℝ) (hK : 0 ≤ K) (hB : 0 ≤ B)
    (hconvex : ∀ᵐ z ∂volume.restrict (Set.Ioo a b ×ˢ sourceBall 0 R),
      0 ≤ F (u z) ∧ 0 ≤ deriv (deriv F) (u z) ∧
        deriv F (u z) ^ 2 ≤ K * deriv (deriv F) (u z) * F (u z))
    (hcut : ∀ᵐ z ∂volume.restrict (Set.Ioo a b ×ˢ sourceBall 0 R),
      0 ≤ 2 * ρ z.2 * |η z| * |fderiv ℝ η z (1, 0)| +
          2 * κ⁻¹ * K * euclideanSq (fun j => fderiv ℝ η z (0, unitVector j)) ∧
      2 * ρ z.2 * |η z| * |fderiv ℝ η z (1, 0)| +
          2 * κ⁻¹ * K * euclideanSq (fun j => fderiv ℝ η z (0, unitVector j)) ≤ B) :
    (∀ᵐ v ∂volume.restrict (Set.Ioo a b),
      ∫⁻ x in sourceBall 0 R, ENNReal.ofReal (ρ x * (F (u (v, x)) * η (v, x) ^ 2)) ≤
        ENNReal.ofReal B * ∫⁻ z in Set.Ioo a b ×ˢ sourceBall 0 R, ENNReal.ofReal (F (u z))) ∧
    (∫⁻ z in Set.Ioo a b ×ˢ sourceBall 0 R,
      ENNReal.ofReal (κ / 2 * deriv (deriv F) (u z) * euclideanSq (G z) * η z ^ 2)) ≤
      ENNReal.ofReal B * ∫⁻ z in Set.Ioo a b ×ˢ sourceBall 0 R, ENNReal.ofReal (F (u z)) := by
  let μ := volume.restrict (Set.Ioo a b ×ˢ sourceBall (0 : Vec d) R)
  have hmeas : AEMeasurable (fun z : ℝ × Vec d =>
      ENNReal.ofReal (ρ z.2 * (F (u z) * η z ^ 2))) μ := by
    have hu := hcal.1.aestronglyMeasurable
    have hf := hF.continuous.comp_aestronglyMeasurable hu
    exact (((hell.1.comp measurable_snd).aestronglyMeasurable.mul
      (hf.mul (hη.continuous.aestronglyMeasurable.pow 2))).aemeasurable.ennreal_ofReal)
  have hid (t₁ h : ℝ) :=
    c11_integrable_uncentered_renormalized_ramp hκ hR hab ρ α hell u G hcal
      F hF M hM hder η hη hηc hηs t₁ h
  have herr (t₁ h : ℝ) :=
    c11_integrable_renormalized_ramp_error ρ α hell u G hcal F hF M hM hder η hη K B t₁ h hcut
  constructor
  · apply c11_weighted_slice_from_renormalized_ramps hκ hell G
      (fun z j => fderiv ℝ η z (0, unitVector j))
      (fun z => F (u z)) (fun z => deriv F (u z))
      (fun z => deriv (deriv F) (u z)) η (fun z => fderiv ℝ η z (1, 0)) hK hB
      hconvex hcut hmeas
    intro t₁ ht h hh
    exact ⟨(hid t₁ h).1, herr t₁ h, (hid t₁ h).2⟩
  · apply c11_weighted_gradient_from_renormalized_ramps hκ hell
      (c20_sourceBall_measurable 0 R) G
      (fun z j => fderiv ℝ η z (0, unitVector j))
      (fun z => F (u z)) (fun z => deriv F (u z))
      (fun z => deriv (deriv F) (u z)) η (fun z => fderiv ℝ η z (1, 0)) hK hB
      hconvex hcut
    intro ε hε
    exact ⟨(hid (b - ε) ε).1, herr (b - ε) ε, (hid (b - ε) ε).2⟩

/-- A smooth compact cutoff has a coefficient-uniform bound for the ramp error. -/
theorem c11_compact_cutoff_ramp_error_bound {d : ℕ} {κ : ℝ} (hκ : 0 < κ)
    (η : ℝ × Vec d → ℝ) (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hηc : HasCompactSupport η) (K : ℝ) (hK : 0 ≤ K) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
      IsUniformlyElliptic κ ρ α → ∀ z : ℝ × Vec d,
      0 ≤ 2 * ρ z.2 * |η z| * |fderiv ℝ η z (1, 0)| +
          2 * κ⁻¹ * K * euclideanSq (fun j => fderiv ℝ η z (0, unitVector j)) ∧
      2 * ρ z.2 * |η z| * |fderiv ℝ η z (1, 0)| +
          2 * κ⁻¹ * K * euclideanSq (fun j => fderiv ℝ η z (0, unitVector j)) ≤ B := by
  obtain ⟨A, hA⟩ := hη.continuous.bounded_above_of_compact_support hηc
  have ht : Continuous (fun z : ℝ × Vec d => fderiv ℝ η z (1, 0)) :=
    (hη.continuous_fderiv (by simp)).clm_apply continuous_const
  obtain ⟨T, hT⟩ := ht.bounded_above_of_compact_support (hηc.fderiv_apply ℝ (1, 0))
  obtain ⟨_, ⟨D, hD, hd⟩, _⟩ := c18_compact_test_spatial_derivative_bounded η hη hηc
  refine ⟨2 * κ⁻¹ * max A 0 * max T 0 + 2 * κ⁻¹ * K * D ^ 2, by positivity, ?_⟩
  intro ρ α hell z
  have hρ0 : 0 ≤ ρ z.2 := hκ.le.trans (hell.2.2 z.2).1
  have hρ : ρ z.2 ≤ κ⁻¹ := (hell.2.2 z.2).2.1
  have hηb : |η z| ≤ max A 0 := by
    exact (by simpa only [Real.norm_eq_abs] using hA z : |η z| ≤ A).trans (le_max_left _ _)
  have htb : |fderiv ℝ η z (1, 0)| ≤ max T 0 := by
    exact (by simpa only [Real.norm_eq_abs] using hT z : |fderiv ℝ η z (1, 0)| ≤ T).trans (le_max_left _ _)
  have hsq : euclideanSq (fun j => fderiv ℝ η z (0, unitVector j)) ≤ D ^ 2 := by
    have hn := hd z
    have hn0 : 0 ≤ euclideanNorm (fun j => fderiv ℝ η z (0, unitVector j)) := Real.sqrt_nonneg _
    have he : euclideanNorm (fun j => fderiv ℝ η z (0, unitVector j)) ^ 2 =
        euclideanSq (fun j => fderiv ℝ η z (0, unitVector j)) :=
      Real.sq_sqrt (PDE.vecNormSq_nonneg _)
    nlinarith
  have he0 := PDE.vecNormSq_nonneg (fun j => fderiv ℝ η z (0, unitVector j))
  constructor
  · positivity
  · have hfirst : 2 * ρ z.2 * |η z| * |fderiv ℝ η z (1, 0)| ≤
        2 * κ⁻¹ * max A 0 * max T 0 := by gcongr
    have hsecond : 2 * κ⁻¹ * K * euclideanSq (fun j => fderiv ℝ η z (0, unitVector j)) ≤
        2 * κ⁻¹ * K * D ^ 2 := by gcongr
    linarith

/-- Uniform renormalized energy bounds for every truncated shifted power. -/
theorem c11_weighted_caloric_truncated_power_energy_bounds {d : ℕ} {κ R a b : ℝ}
    (hκ : 0 < κ) (hR : 0 < R) (hab : a < b)
    (η : ℝ × Vec d → ℝ) (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hηc : HasCompactSupport η)
    (hηs : tsupport η ⊆ Set.Ioo a b ×ˢ sourceBall 0 R)
    {p ε : ℝ} (hp : 1 < p) (hε : 0 < ε) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
    IsUniformlyElliptic κ ρ α →
    ∀ (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d),
    IsWeightedCaloric ρ α (Set.Ioo a b) (sourceBall 0 R) u G →
    (∀ᵐ z ∂volume.restrict (Set.Ioo a b ×ˢ sourceBall 0 R), 0 ≤ u z) →
    ∀ n : ℕ,
    (∀ᵐ v ∂volume.restrict (Set.Ioo a b),
      ∫⁻ x in sourceBall 0 R, ENNReal.ofReal
        (ρ x * (PDE.Parabolic.LocalMax.powF p ε n (u (v, x)) * η (v, x) ^ 2)) ≤
        ENNReal.ofReal B * ∫⁻ z in Set.Ioo a b ×ˢ sourceBall 0 R,
          ENNReal.ofReal (u z + ε) ^ p) ∧
    (∫⁻ z in Set.Ioo a b ×ˢ sourceBall 0 R, ENNReal.ofReal
      (κ / 2 * deriv (deriv (PDE.Parabolic.LocalMax.powF p ε n)) (u z) *
        euclideanSq (G z) * η z ^ 2)) ≤
      ENNReal.ofReal B * ∫⁻ z in Set.Ioo a b ×ˢ sourceBall 0 R,
        ENNReal.ofReal (u z + ε) ^ p := by
  have hK : 0 ≤ 2 + p / (p - 1) := by positivity
  obtain ⟨B, hB, hcut⟩ := c11_compact_cutoff_ramp_error_bound hκ η hη hηc _ hK
  refine ⟨B, hB, ?_⟩
  intro ρ α hell u G hcal hpos n
  obtain ⟨M, hM⟩ := PDE.Parabolic.LocalMax.exists_powF2_bound hp hε (Nat.cast_nonneg n)
  have hconvex : ∀ᵐ z ∂volume.restrict (Set.Ioo a b ×ˢ sourceBall 0 R),
      0 ≤ PDE.Parabolic.LocalMax.powF p ε n (u z) ∧
      0 ≤ deriv (deriv (PDE.Parabolic.LocalMax.powF p ε n)) (u z) ∧
      deriv (PDE.Parabolic.LocalMax.powF p ε n) (u z) ^ 2 ≤
        (2 + p / (p - 1)) * deriv (deriv (PDE.Parabolic.LocalMax.powF p ε n)) (u z) *
          PDE.Parabolic.LocalMax.powF p ε n (u z) := by
    filter_upwards [hpos] with z hz
    have hs := c11_truncated_power_energy_structure hp hε n (u z) hz
    exact ⟨hs.1, hs.2.1, hs.2.2.1⟩
  have hbound : (∫⁻ z in Set.Ioo a b ×ˢ sourceBall 0 R,
      ENNReal.ofReal (PDE.Parabolic.LocalMax.powF p ε n (u z))) ≤
      ∫⁻ z in Set.Ioo a b ×ˢ sourceBall 0 R, ENNReal.ofReal (u z + ε) ^ p := by
    apply lintegral_mono_ae
    filter_upwards [hpos] with z hz
    rw [ENNReal.ofReal_rpow_of_nonneg (by linarith) (by linarith)]
    exact ENNReal.ofReal_le_ofReal
      (c11_truncated_power_energy_structure hp hε n (u z) hz).2.2.2.2.2
  have he := c11_weighted_caloric_renormalized_energy_bounds hκ hR hab ρ α hell u G hcal
    (PDE.Parabolic.LocalMax.powF p ε n)
    (PDE.Parabolic.LocalMax.powF_contDiff hε (Nat.cast_nonneg n)) M M.coe_nonneg hM
    η hη hηc hηs _ B hK hB hconvex (Filter.Eventually.of_forall (hcut ρ α hell))
  have hmul : ENNReal.ofReal B *
      (∫⁻ z in Set.Ioo a b ×ˢ sourceBall 0 R,
        ENNReal.ofReal (PDE.Parabolic.LocalMax.powF p ε n (u z))) ≤
      ENNReal.ofReal B *
      (∫⁻ z in Set.Ioo a b ×ˢ sourceBall 0 R, ENNReal.ofReal (u z + ε) ^ p) := by
    gcongr
  exact ⟨he.1.mono (fun _ ht => ht.trans hmul), he.2.trans hmul⟩

/-- The truncated-power Sobolev slice masses have one coefficient-uniform bound. -/
theorem c11_weighted_caloric_truncated_power_slice_bounds {d : ℕ} {κ R a b : ℝ}
    (hκ : 0 < κ) (hR : 0 < R) (hab : a < b)
    (η : ℝ × Vec d → ℝ) (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hηc : HasCompactSupport η)
    (hηs : tsupport η ⊆ Set.Ioo a b ×ˢ sourceBall 0 R)
    {p ε : ℝ} (hp : 1 < p) (hε : 0 < ε) :
    ∃ B : ℝ≥0∞, B ≠ ⊤ ∧ ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
    IsUniformlyElliptic κ ρ α →
    ∀ (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d),
    IsWeightedCaloric ρ α (Set.Ioo a b) (sourceBall 0 R) u G →
    (∀ᵐ z ∂volume.restrict (Set.Ioo a b ×ˢ sourceBall 0 R), 0 ≤ u z) →
    ∀ n : ℕ, ∀ᵐ t ∂volume.restrict (Set.Ioo a b),
      (∫⁻ x in sourceBall 0 R, ENNReal.ofReal (ρ x) *
        ‖η (t,x) * PDE.Parabolic.LocalMax.powG p ε n (u (t,x))‖ₑ ^ (2 : ℝ)) ≤
      B * ∫⁻ z in Set.Ioo a b ×ˢ sourceBall 0 R, ENNReal.ofReal (u z + ε) ^ p := by
  obtain ⟨B, hB, henergy⟩ :=
    c11_weighted_caloric_truncated_power_energy_bounds hκ hR hab η hη hηc hηs hp hε
  refine ⟨ENNReal.ofReal (2 + p / (p - 1)) * ENNReal.ofReal B,
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top, ?_⟩
  intro ρ α hell u G hcal hpos n
  have hpairs : ∀ᵐ z ∂((volume.restrict (Set.Ioo a b)).prod
      (volume.restrict (sourceBall (0 : Vec d) R))), 0 ≤ u z := by
    rw [Measure.prod_restrict]
    exact hpos
  filter_upwards [Measure.ae_ae_of_ae_prod hpairs, (henergy ρ α hell u G hcal hpos n).1] with t ht he
  have hslice := c11_weighted_truncated_power_slice_mass_le (ρ := ρ)
    (fun x => u (t,x)) (fun x => η (t,x)) ht hp hε n
  have heq : (∫⁻ x in sourceBall 0 R, ENNReal.ofReal (ρ x) *
      ENNReal.ofReal (η (t,x) ^ 2 * PDE.Parabolic.LocalMax.powF p ε n (u (t,x)))) =
      ∫⁻ x in sourceBall 0 R, ENNReal.ofReal
        (ρ x * (PDE.Parabolic.LocalMax.powF p ε n (u (t,x)) * η (t,x) ^ 2)) := by
    apply lintegral_congr
    intro x
    rw [← ENNReal.ofReal_mul (hκ.le.trans (hell.2.2 x).1)]
    congr 1
    ring
  rw [heq] at hslice
  calc
    _ ≤ ENNReal.ofReal (2 + p / (p - 1)) *
        (∫⁻ x in sourceBall 0 R, ENNReal.ofReal
          (ρ x * (PDE.Parabolic.LocalMax.powF p ε n (u (t,x)) * η (t,x) ^ 2))) := hslice
    _ ≤ ENNReal.ofReal (2 + p / (p - 1)) * (ENNReal.ofReal B *
        ∫⁻ z in Set.Ioo a b ×ˢ sourceBall 0 R, ENNReal.ofReal (u z + ε) ^ p) := by gcongr
    _ = _ := by rw [mul_assoc]

/-- The unscaled truncated-power gradient energy is uniformly controlled by
the shifted power mass. -/
theorem c11_weighted_caloric_truncated_power_gradient_bounds {d : ℕ} {κ R a b : ℝ}
    (hκ : 0 < κ) (hR : 0 < R) (hab : a < b)
    (η : ℝ × Vec d → ℝ) (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hηc : HasCompactSupport η)
    (hηs : tsupport η ⊆ Set.Ioo a b ×ˢ sourceBall 0 R)
    {p ε : ℝ} (hp : 1 < p) (hε : 0 < ε) :
    ∃ B : ℝ≥0∞, B ≠ ⊤ ∧ ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
    IsUniformlyElliptic κ ρ α →
    ∀ (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d),
    IsWeightedCaloric ρ α (Set.Ioo a b) (sourceBall 0 R) u G →
    (∀ᵐ z ∂volume.restrict (Set.Ioo a b ×ˢ sourceBall 0 R), 0 ≤ u z) →
    ∀ n : ℕ,
      (∫⁻ z in Set.Ioo a b ×ˢ sourceBall 0 R, ENNReal.ofReal
        (η z ^ 2 * deriv (deriv (PDE.Parabolic.LocalMax.powF p ε n)) (u z) *
          euclideanSq (G z))) ≤
      B * ∫⁻ z in Set.Ioo a b ×ˢ sourceBall 0 R, ENNReal.ofReal (u z + ε) ^ p := by
  obtain ⟨B, hB, henergy⟩ :=
    c11_weighted_caloric_truncated_power_energy_bounds hκ hR hab η hη hηc hηs hp hε
  refine ⟨ENNReal.ofReal (2 / κ) * ENNReal.ofReal B,
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top, ?_⟩
  intro ρ α hell u G hcal hpos n
  have he := (henergy ρ α hell u G hcal hpos n).2
  have hfactor : 0 ≤ 2 / κ := by positivity
  have hpoint (z : ℝ × Vec d) :
      η z ^ 2 * deriv (deriv (PDE.Parabolic.LocalMax.powF p ε n)) (u z) * euclideanSq (G z) =
      (2 / κ) * (κ / 2 * deriv (deriv (PDE.Parabolic.LocalMax.powF p ε n)) (u z) *
        euclideanSq (G z) * η z ^ 2) := by
    field_simp
    <;> ring
  calc
    _ = ENNReal.ofReal (2 / κ) *
        (∫⁻ z in Set.Ioo a b ×ˢ sourceBall 0 R, ENNReal.ofReal
          (κ / 2 * deriv (deriv (PDE.Parabolic.LocalMax.powF p ε n)) (u z) *
            euclideanSq (G z) * η z ^ 2)) := by
      simp_rw [hpoint, ENNReal.ofReal_mul hfactor]
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ENNReal.ofReal (2 / κ) * (ENNReal.ofReal B *
        ∫⁻ z in Set.Ioo a b ×ˢ sourceBall 0 R, ENNReal.ofReal (u z + ε) ^ p) := by gcongr
    _ = _ := by rw [mul_assoc]

/-- A compact cutoff gives uniform coefficient-energy bounds for the
truncated powers, in terms of their shifted power mass. -/
theorem c11_weighted_caloric_truncated_power_cutoff_energy_bounds
    {d : ℕ} {κ R a b : ℝ} (hκ : 0 < κ) (hR : 0 < R) (hab : a < b)
    (η : ℝ × Vec d → ℝ) (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hηc : HasCompactSupport η)
    (hηs : tsupport η ⊆ Set.Ioo a b ×ˢ sourceBall 0 R)
    {p ε : ℝ} (hp : 1 < p) (hε : 0 < ε) :
    ∃ B : ℝ≥0∞, B ≠ ⊤ ∧ ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
    IsUniformlyElliptic κ ρ α →
    ∀ (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d),
    IsWeightedCaloric ρ α (Set.Ioo a b) (sourceBall 0 R) u G →
    (∀ᵐ z ∂volume.restrict (Set.Ioo a b ×ˢ sourceBall 0 R), 0 ≤ u z) →
    ∀ n : ℕ,
      (∫⁻ z in Set.Ioo a b ×ˢ sourceBall 0 R, ENNReal.ofReal
        (dot ((α z.2).mulVec
          (η z • (deriv (PDE.Parabolic.LocalMax.powG p ε n) (u z) • G z) +
            PDE.Parabolic.LocalMax.powG p ε n (u z) •
              (fun j => fderiv ℝ η z (0, unitVector j))))
          (η z • (deriv (PDE.Parabolic.LocalMax.powG p ε n) (u z) • G z) +
            PDE.Parabolic.LocalMax.powG p ε n (u z) •
              (fun j => fderiv ℝ η z (0, unitVector j))))) ≤
      B * ∫⁻ z in Set.Ioo a b ×ˢ sourceBall 0 R, ENNReal.ofReal (u z + ε) ^ p := by
  obtain ⟨A, hA, hgrad⟩ :=
    c11_weighted_caloric_truncated_power_gradient_bounds hκ hR hab η hη hηc hηs hp hε
  obtain ⟨_, ⟨D, hD, hd⟩, _⟩ := c18_compact_test_spatial_derivative_bounded η hη hηc
  have hsq (z : ℝ × Vec d) :
      euclideanSq (fun j => fderiv ℝ η z (0, unitVector j)) ≤ D ^ 2 := by
    have hn := hd z
    have hn0 : 0 ≤ euclideanNorm (fun j => fderiv ℝ η z (0, unitVector j)) := Real.sqrt_nonneg _
    have he : euclideanNorm (fun j => fderiv ℝ η z (0, unitVector j)) ^ 2 =
        euclideanSq (fun j => fderiv ℝ η z (0, unitVector j)) :=
      Real.sq_sqrt (PDE.vecNormSq_nonneg _)
    nlinarith
  let C : ℝ≥0∞ := ENNReal.ofReal (2 * κ⁻¹ * (2 + p / (p - 1)))
  refine ⟨C * (A + ENNReal.ofReal (D ^ 2)),
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.add_ne_top.mpr ⟨hA, ENNReal.ofReal_ne_top⟩), ?_⟩
  intro ρ α hell u G hcal hpos n
  have herr : (∫⁻ z in Set.Ioo a b ×ˢ sourceBall 0 R, ENNReal.ofReal
      (PDE.Parabolic.LocalMax.powF p ε n (u z) *
        euclideanSq (fun j => fderiv ℝ η z (0, unitVector j)))) ≤
      ENNReal.ofReal (D ^ 2) *
        ∫⁻ z in Set.Ioo a b ×ˢ sourceBall 0 R, ENNReal.ofReal (u z + ε) ^ p := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply lintegral_mono_ae
    filter_upwards [hpos] with z hz
    rw [ENNReal.ofReal_rpow_of_nonneg (by linarith) (by linarith),
      ← ENNReal.ofReal_mul (sq_nonneg D)]
    apply ENNReal.ofReal_le_ofReal
    have hf := c11_truncated_power_energy_structure hp hε n (u z) hz
    have hr : 0 ≤ (u z + ε) ^ p := Real.rpow_nonneg (by linarith) _
    have hs := PDE.vecNormSq_nonneg (fun j => fderiv ℝ η z (0, unitVector j))
    calc
      _ ≤ (u z + ε) ^ p * D ^ 2 := mul_le_mul hf.2.2.2.2.2 (hsq z) hs hr
      _ = _ := by ring
  have hc := c11_weighted_truncated_power_cutoff_energy_integral hκ hell hcal hpos
    η hη.continuous (fun z j => fderiv ℝ η z (0, unitVector j)) hp hε n
  calc
    _ ≤ C * ((∫⁻ z in Set.Ioo a b ×ˢ sourceBall 0 R, ENNReal.ofReal
          (η z ^ 2 * deriv (deriv (PDE.Parabolic.LocalMax.powF p ε n)) (u z) * euclideanSq (G z))) +
        ∫⁻ z in Set.Ioo a b ×ˢ sourceBall 0 R, ENNReal.ofReal
          (PDE.Parabolic.LocalMax.powF p ε n (u z) *
            euclideanSq (fun j => fderiv ℝ η z (0, unitVector j)))) := hc
    _ ≤ C * (A * (∫⁻ z in Set.Ioo a b ×ˢ sourceBall 0 R, ENNReal.ofReal (u z + ε) ^ p) +
        ENNReal.ofReal (D ^ 2) * (∫⁻ z in Set.Ioo a b ×ˢ sourceBall 0 R,
          ENNReal.ofReal (u z + ε) ^ p)) := by
      gcongr
      exact hgrad ρ α hell u G hcal hpos n
    _ = _ := by rw [← add_mul, mul_assoc]

/-- Fubini for the actual measurable coefficient energy. -/
theorem c11_weighted_coefficient_energy_lintegral_prod {d : ℕ} {κ : ℝ}
    {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (hell : IsUniformlyElliptic κ ρ α) {I : Set ℝ} {U : Set (Vec d)}
    (V : ℝ × Vec d → Vec d)
    (hV : AEStronglyMeasurable V (volume.restrict (I ×ˢ U))) :
    (∫⁻ z in I ×ˢ U, ENNReal.ofReal (dot ((α z.2).mulVec (V z)) (V z))) =
      ∫⁻ t in I, ∫⁻ x in U, ENNReal.ofReal (dot ((α x).mulVec (V (t,x))) (V (t,x))) := by
  let μ := volume.restrict (I ×ˢ U)
  have hm : AEStronglyMeasurable (fun z => dot ((α z.2).mulVec (V z)) (V z)) μ := by
    change AEStronglyMeasurable (fun z => ∑ i : Fin d, (∑ j : Fin d,
      α z.2 i j * V z j) * V z i) μ
    have hm' : AEStronglyMeasurable (∑ i : Fin d, fun z => (∑ j : Fin d,
        α z.2 i j * V z j) * V z i) μ := by
      apply Finset.aestronglyMeasurable_sum
      intro i hi
      apply AEStronglyMeasurable.mul _ ((continuous_apply i).comp_aestronglyMeasurable hV)
      have hjm : AEStronglyMeasurable (∑ j : Fin d, fun z => α z.2 i j * V z j) μ := by
        apply Finset.aestronglyMeasurable_sum
        intro j hj
        apply AEStronglyMeasurable.mul _ ((continuous_apply j).comp_aestronglyMeasurable hV)
        let : MeasurableSpace (Mat d) := EinsteinRelation.instMeasurableSpaceMat d
        let : BorelSpace (Mat d) := EinsteinRelation.instBorelSpaceMat d
        exact ((((continuous_id : Continuous (id : Mat d → Mat d)).matrix_elem i j).measurable.comp
          hell.2.1).comp measurable_snd).aestronglyMeasurable
      convert hjm using 1
      ext z
      simp only [Finset.sum_apply]
    convert hm' using 1
    ext z
    simp only [Finset.sum_apply]
  have hprod : volume.restrict (I ×ˢ U) =
      (volume.restrict I).prod (volume.restrict U) := by
    rw [Measure.volume_eq_prod, Measure.prod_restrict]
  have hm' := hm.aemeasurable.ennreal_ofReal
  change AEMeasurable (fun z => ENNReal.ofReal (dot ((α z.2).mulVec (V z)) (V z)))
    (volume.restrict (I ×ˢ U)) at hm'
  rw [hprod] at hm' ⊢
  exact lintegral_prod _ hm'

/-- The actual weighted caloric energy estimates imply the cutoff power gain. -/
theorem c11_weighted_caloric_power_gain_of_energy (d : ℕ) (hd : 2 ≤ d)
    {κ R a b : ℝ} (hκ : 0 < κ) (hR : 0 < R) (hab : a < b)
    (hfinite : volume (Set.Ioo a b ×ˢ sourceBall (0 : Vec d) R) < ∞)
    (η : ℝ × Vec d → ℝ) (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hηc : HasCompactSupport η)
    (hηs : tsupport η ⊆ Set.Ioo a b ×ˢ sourceBall 0 R)
    (htest : ∀ᵐ t ∂volume.restrict (Set.Ioo a b),
      IsSpatialTest (sourceBall 0 R) (fun x => η (t,x)))
    (K : Set (Vec d)) (hK : IsCompact K) (hKU : K ⊆ sourceBall 0 R)
    (hzero : ∀ t x, x ∉ K → η (t,x) = 0)
    (S : Set (ℝ × Vec d)) (hS : MeasurableSet S)
    (hSV : S ⊆ Set.Ioo a b ×ˢ sourceBall 0 R)
    (hηone : ∀ z ∈ S, η z = 1)
    {p ε : ℝ} (hp : 1 < p) (hε : 0 < ε) :
    ∃ C A E : ℝ≥0∞, C ≠ ⊤ ∧ A ≠ ⊤ ∧ E ≠ ⊤ ∧
    ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d), IsUniformlyElliptic κ ρ α →
    ∀ (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d),
    IsWeightedCaloric ρ α (Set.Ioo a b) (sourceBall 0 R) u G →
    (∀ᵐ z ∂volume.restrict (Set.Ioo a b ×ˢ sourceBall 0 R), 0 ≤ u z) →
    (∫⁻ z in S, ENNReal.ofReal (u z + ε) ^ (p * (((d : ℝ) + 2) / d))) ≤
      ENNReal.ofReal κ⁻¹ * (C *
        (A * (∫⁻ z in Set.Ioo a b ×ˢ sourceBall 0 R, ENNReal.ofReal (u z + ε) ^ p)) ^
          (2 / (d : ℝ)) *
        (E * (∫⁻ z in Set.Ioo a b ×ˢ sourceBall 0 R, ENNReal.ofReal (u z + ε) ^ p))) := by
  obtain ⟨C, hC, hgain⟩ := c11_weighted_caloric_cutoff_power_gain d hd κ hκ
  obtain ⟨A, hA, hslice⟩ :=
    c11_weighted_caloric_truncated_power_slice_bounds hκ hR hab η hη hηc hηs hp hε
  obtain ⟨E, hE, henergy⟩ :=
    c11_weighted_caloric_truncated_power_cutoff_energy_bounds hκ hR hab η hη hηc hηs hp hε
  refine ⟨C, A, E, hC, hA, hE, ?_⟩
  intro ρ α hell u G hcal hpos
  let μ := volume.restrict (Set.Ioo a b ×ˢ sourceBall (0 : Vec d) R)
  have hOpen : IsOpen (sourceBall (0 : Vec d) R) := by
    have hsum : Continuous (fun v : Vec d => ∑ j, v j * v j) :=
      continuous_finset_sum Finset.univ fun j _ => (continuous_apply j).mul (continuous_apply j)
    have hn : Continuous (fun v : Vec d => euclideanNorm v) := by
      unfold euclideanNorm euclideanSq dot
      exact Real.continuous_sqrt.comp hsum
    exact isOpen_lt (hn.comp (continuous_id.sub continuous_const)) continuous_const
  apply hgain ρ α hell (Set.Ioo a b) (sourceBall 0 R) measurableSet_Ioo
    hOpen hfinite u G hcal η hη hηc htest K hK hKU hzero
    S hS hSV (ae_restrict_of_ae_restrict_of_subset hSV hpos) hηone p ε hp hε
    (A * ∫⁻ z in Set.Ioo a b ×ˢ sourceBall 0 R, ENNReal.ofReal (u z + ε) ^ p)
    (E * ∫⁻ z in Set.Ioo a b ×ˢ sourceBall 0 R, ENNReal.ofReal (u z + ε) ^ p)
    (fun n => hslice ρ α hell u G hcal hpos n)
  intro n
  let F := PDE.Parabolic.LocalMax.powG p ε n
  let V : ℝ × Vec d → Vec d := fun z =>
    η z • (deriv F (u z) • G z) + F (u z) •
      (fun j => fderiv ℝ η z (0, unitVector j))
  have hF : ContDiff ℝ 1 F := PDE.Parabolic.LocalMax.powG_contDiff hε (Nat.cast_nonneg n)
  have hηd : Continuous (fun z => fun j => fderiv ℝ η z (0, unitVector j)) :=
    continuous_pi fun j => (hη.continuous_fderiv (by simp)).clm_apply continuous_const
  have hV : AEStronglyMeasurable V μ :=
    (hη.continuous.aestronglyMeasurable.smul
      ((hF.continuous_deriv_one.comp_aestronglyMeasurable hcal.1.aestronglyMeasurable).smul hcal.2.1)).add
      ((hF.continuous.comp_aestronglyMeasurable hcal.1.aestronglyMeasurable).smul hηd.aestronglyMeasurable)
  have hfub := c11_weighted_coefficient_energy_lintegral_prod hell V hV
  rw [← hfub]
  exact henergy ρ α hell u G hcal hpos n

/-- Explicit ramp-error bound from uniform cutoff and derivative bounds. -/
theorem c11_cutoff_ramp_error_le_of_bounds {d : ℕ} {κ : ℝ} (hκ : 0 < κ)
    (η : ℝ × Vec d → ℝ) (K A T D : ℝ)
    (hK : 0 ≤ K) (hA : 0 ≤ A)
    (hη : ∀ z, |η z| ≤ A)
    (ht : ∀ z, |fderiv ℝ η z (1, 0)| ≤ T)
    (hd : ∀ z, euclideanSq (fun j => fderiv ℝ η z (0, unitVector j)) ≤ D ^ 2)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d) (hell : IsUniformlyElliptic κ ρ α)
    (z : ℝ × Vec d) :
    0 ≤ 2 * ρ z.2 * |η z| * |fderiv ℝ η z (1, 0)| +
      2 * κ⁻¹ * K * euclideanSq (fun j => fderiv ℝ η z (0, unitVector j)) ∧
    2 * ρ z.2 * |η z| * |fderiv ℝ η z (1, 0)| +
      2 * κ⁻¹ * K * euclideanSq (fun j => fderiv ℝ η z (0, unitVector j)) ≤
      2 * κ⁻¹ * A * T + 2 * κ⁻¹ * K * D ^ 2 := by
  have hρ0 : 0 ≤ ρ z.2 := hκ.le.trans (hell.2.2 z.2).1
  have hρ : ρ z.2 ≤ κ⁻¹ := (hell.2.2 z.2).2.1
  have he0 := PDE.vecNormSq_nonneg (fun j => fderiv ℝ η z (0, unitVector j))
  constructor
  · positivity
  · have hfirst : 2 * ρ z.2 * |η z| * |fderiv ℝ η z (1, 0)| ≤
        2 * κ⁻¹ * A * T := by
      gcongr <;> first | exact hρ | exact hη z | exact ht z
    have hsecond : 2 * κ⁻¹ * K * euclideanSq (fun j => fderiv ℝ η z (0, unitVector j)) ≤
        2 * κ⁻¹ * K * D ^ 2 := by gcongr; exact hd z
    linarith

/-- Quantitative truncated-power energy in terms of cutoff derivative bounds. -/
theorem c11_weighted_caloric_truncated_power_energy_bounds_explicit {d : ℕ} {κ R a b : ℝ}
    (hκ : 0 < κ) (hR : 0 < R) (hab : a < b)
    (η : ℝ × Vec d → ℝ) (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hηc : HasCompactSupport η)
    (hηs : tsupport η ⊆ Set.Ioo a b ×ˢ sourceBall 0 R)
    (A T D : ℝ) (hA : 0 ≤ A) (hT : 0 ≤ T)
    (hηbound : ∀ z, |η z| ≤ A)
    (htbound : ∀ z, |fderiv ℝ η z (1, 0)| ≤ T)
    (hdbound : ∀ z, euclideanSq (fun j => fderiv ℝ η z (0, unitVector j)) ≤ D ^ 2)
    {p ε : ℝ} (hp : 1 < p) (hε : 0 < ε) :
    let B := 2 * κ⁻¹ * A * T + 2 * κ⁻¹ * (2 + p / (p - 1)) * D ^ 2
    ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
    IsUniformlyElliptic κ ρ α →
    ∀ (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d),
    IsWeightedCaloric ρ α (Set.Ioo a b) (sourceBall 0 R) u G →
    (∀ᵐ z ∂volume.restrict (Set.Ioo a b ×ˢ sourceBall 0 R), 0 ≤ u z) →
    ∀ n : ℕ,
    (∀ᵐ v ∂volume.restrict (Set.Ioo a b),
      ∫⁻ x in sourceBall 0 R, ENNReal.ofReal
        (ρ x * (PDE.Parabolic.LocalMax.powF p ε n (u (v, x)) * η (v, x) ^ 2)) ≤
        ENNReal.ofReal B * ∫⁻ z in Set.Ioo a b ×ˢ sourceBall 0 R,
          ENNReal.ofReal (u z + ε) ^ p) ∧
    (∫⁻ z in Set.Ioo a b ×ˢ sourceBall 0 R, ENNReal.ofReal
      (κ / 2 * deriv (deriv (PDE.Parabolic.LocalMax.powF p ε n)) (u z) *
        euclideanSq (G z) * η z ^ 2)) ≤
      ENNReal.ofReal B * ∫⁻ z in Set.Ioo a b ×ˢ sourceBall 0 R,
        ENNReal.ofReal (u z + ε) ^ p := by
  have hK : 0 ≤ 2 + p / (p - 1) := by positivity
  dsimp only
  let B := 2 * κ⁻¹ * A * T + 2 * κ⁻¹ * (2 + p / (p - 1)) * D ^ 2
  have hB : 0 ≤ B := by dsimp [B]; positivity
  intro ρ α hell u G hcal hpos n
  have hcut := c11_cutoff_ramp_error_le_of_bounds hκ η (2 + p / (p - 1)) A T D
    hK hA hηbound htbound hdbound ρ α hell
  obtain ⟨M, hM⟩ := PDE.Parabolic.LocalMax.exists_powF2_bound hp hε (Nat.cast_nonneg n)
  have hconvex : ∀ᵐ z ∂volume.restrict (Set.Ioo a b ×ˢ sourceBall 0 R),
      0 ≤ PDE.Parabolic.LocalMax.powF p ε n (u z) ∧
      0 ≤ deriv (deriv (PDE.Parabolic.LocalMax.powF p ε n)) (u z) ∧
      deriv (PDE.Parabolic.LocalMax.powF p ε n) (u z) ^ 2 ≤
        (2 + p / (p - 1)) * deriv (deriv (PDE.Parabolic.LocalMax.powF p ε n)) (u z) *
          PDE.Parabolic.LocalMax.powF p ε n (u z) := by
    filter_upwards [hpos] with z hz
    have hs := c11_truncated_power_energy_structure hp hε n (u z) hz
    exact ⟨hs.1, hs.2.1, hs.2.2.1⟩
  have hbound : (∫⁻ z in Set.Ioo a b ×ˢ sourceBall 0 R,
      ENNReal.ofReal (PDE.Parabolic.LocalMax.powF p ε n (u z))) ≤
      ∫⁻ z in Set.Ioo a b ×ˢ sourceBall 0 R, ENNReal.ofReal (u z + ε) ^ p := by
    apply lintegral_mono_ae
    filter_upwards [hpos] with z hz
    rw [ENNReal.ofReal_rpow_of_nonneg (by linarith) (by linarith)]
    exact ENNReal.ofReal_le_ofReal
      (c11_truncated_power_energy_structure hp hε n (u z) hz).2.2.2.2.2
  have he := c11_weighted_caloric_renormalized_energy_bounds hκ hR hab ρ α hell u G hcal
    (PDE.Parabolic.LocalMax.powF p ε n)
    (PDE.Parabolic.LocalMax.powF_contDiff hε (Nat.cast_nonneg n)) M M.coe_nonneg hM
    η hη hηc hηs _ B hK hB hconvex (Filter.Eventually.of_forall hcut)
  have hmul : ENNReal.ofReal B *
      (∫⁻ z in Set.Ioo a b ×ˢ sourceBall 0 R,
        ENNReal.ofReal (PDE.Parabolic.LocalMax.powF p ε n (u z))) ≤
      ENNReal.ofReal B *
      (∫⁻ z in Set.Ioo a b ×ˢ sourceBall 0 R, ENNReal.ofReal (u z + ε) ^ p) := by
    gcongr
  exact ⟨he.1.mono (fun _ ht => ht.trans hmul), he.2.trans hmul⟩

/-- Quantitative slice bound with explicit cutoff dependence. -/
theorem c11_weighted_caloric_truncated_power_slice_bounds_explicit {d : ℕ} {κ R a b : ℝ}
    (hκ : 0 < κ) (hR : 0 < R) (hab : a < b)
    (η : ℝ × Vec d → ℝ) (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hηc : HasCompactSupport η)
    (hηs : tsupport η ⊆ Set.Ioo a b ×ˢ sourceBall 0 R)
    (A T D : ℝ) (hA : 0 ≤ A) (hT : 0 ≤ T)
    (hηbound : ∀ z, |η z| ≤ A)
    (htbound : ∀ z, |fderiv ℝ η z (1, 0)| ≤ T)
    (hdbound : ∀ z, euclideanSq (fun j => fderiv ℝ η z (0, unitVector j)) ≤ D ^ 2)
    {p ε : ℝ} (hp : 1 < p) (hε : 0 < ε) :
    let B := 2 * κ⁻¹ * A * T + 2 * κ⁻¹ * (2 + p / (p - 1)) * D ^ 2
    ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
    IsUniformlyElliptic κ ρ α →
    ∀ (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d),
    IsWeightedCaloric ρ α (Set.Ioo a b) (sourceBall 0 R) u G →
    (∀ᵐ z ∂volume.restrict (Set.Ioo a b ×ˢ sourceBall 0 R), 0 ≤ u z) →
    ∀ n : ℕ, ∀ᵐ t ∂volume.restrict (Set.Ioo a b),
      (∫⁻ x in sourceBall 0 R, ENNReal.ofReal (ρ x) *
        ‖η (t,x) * PDE.Parabolic.LocalMax.powG p ε n (u (t,x))‖ₑ ^ (2 : ℝ)) ≤
      (ENNReal.ofReal (2 + p / (p - 1)) * ENNReal.ofReal B) *
        ∫⁻ z in Set.Ioo a b ×ˢ sourceBall 0 R, ENNReal.ofReal (u z + ε) ^ p := by
  dsimp only
  let B := 2 * κ⁻¹ * A * T + 2 * κ⁻¹ * (2 + p / (p - 1)) * D ^ 2
  have henergy := c11_weighted_caloric_truncated_power_energy_bounds_explicit
    hκ hR hab η hη hηc hηs A T D hA hT hηbound htbound hdbound hp hε
  intro ρ α hell u G hcal hpos n
  have hpairs : ∀ᵐ z ∂((volume.restrict (Set.Ioo a b)).prod
      (volume.restrict (sourceBall (0 : Vec d) R))), 0 ≤ u z := by
    rw [Measure.prod_restrict]
    exact hpos
  filter_upwards [Measure.ae_ae_of_ae_prod hpairs, (henergy ρ α hell u G hcal hpos n).1] with t ht he
  have hslice := c11_weighted_truncated_power_slice_mass_le (ρ := ρ)
    (fun x => u (t,x)) (fun x => η (t,x)) ht hp hε n
  have heq : (∫⁻ x in sourceBall 0 R, ENNReal.ofReal (ρ x) *
      ENNReal.ofReal (η (t,x) ^ 2 * PDE.Parabolic.LocalMax.powF p ε n (u (t,x)))) =
      ∫⁻ x in sourceBall 0 R, ENNReal.ofReal
        (ρ x * (PDE.Parabolic.LocalMax.powF p ε n (u (t,x)) * η (t,x) ^ 2)) := by
    apply lintegral_congr
    intro x
    rw [← ENNReal.ofReal_mul (hκ.le.trans (hell.2.2 x).1)]
    congr 1
    ring
  rw [heq] at hslice
  calc
    _ ≤ ENNReal.ofReal (2 + p / (p - 1)) *
        (∫⁻ x in sourceBall 0 R, ENNReal.ofReal
          (ρ x * (PDE.Parabolic.LocalMax.powF p ε n (u (t,x)) * η (t,x) ^ 2))) := hslice
    _ ≤ ENNReal.ofReal (2 + p / (p - 1)) * (ENNReal.ofReal B *
        ∫⁻ z in Set.Ioo a b ×ˢ sourceBall 0 R, ENNReal.ofReal (u z + ε) ^ p) := by gcongr
    _ = _ := by rw [mul_assoc]

/-- Quantitative gradient bound with explicit cutoff dependence. -/
theorem c11_weighted_caloric_truncated_power_gradient_bounds_explicit {d : ℕ} {κ R a b : ℝ}
    (hκ : 0 < κ) (hR : 0 < R) (hab : a < b)
    (η : ℝ × Vec d → ℝ) (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hηc : HasCompactSupport η)
    (hηs : tsupport η ⊆ Set.Ioo a b ×ˢ sourceBall 0 R)
    (A T D : ℝ) (hA : 0 ≤ A) (hT : 0 ≤ T)
    (hηbound : ∀ z, |η z| ≤ A)
    (htbound : ∀ z, |fderiv ℝ η z (1, 0)| ≤ T)
    (hdbound : ∀ z, euclideanSq (fun j => fderiv ℝ η z (0, unitVector j)) ≤ D ^ 2)
    {p ε : ℝ} (hp : 1 < p) (hε : 0 < ε) :
    let B := 2 * κ⁻¹ * A * T + 2 * κ⁻¹ * (2 + p / (p - 1)) * D ^ 2
    ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
    IsUniformlyElliptic κ ρ α →
    ∀ (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d),
    IsWeightedCaloric ρ α (Set.Ioo a b) (sourceBall 0 R) u G →
    (∀ᵐ z ∂volume.restrict (Set.Ioo a b ×ˢ sourceBall 0 R), 0 ≤ u z) →
    ∀ n : ℕ,
      (∫⁻ z in Set.Ioo a b ×ˢ sourceBall 0 R, ENNReal.ofReal
        (η z ^ 2 * deriv (deriv (PDE.Parabolic.LocalMax.powF p ε n)) (u z) *
          euclideanSq (G z))) ≤
      (ENNReal.ofReal (2 / κ) * ENNReal.ofReal B) *
        ∫⁻ z in Set.Ioo a b ×ˢ sourceBall 0 R, ENNReal.ofReal (u z + ε) ^ p := by
  dsimp only
  let B := 2 * κ⁻¹ * A * T + 2 * κ⁻¹ * (2 + p / (p - 1)) * D ^ 2
  have henergy := c11_weighted_caloric_truncated_power_energy_bounds_explicit
    hκ hR hab η hη hηc hηs A T D hA hT hηbound htbound hdbound hp hε
  intro ρ α hell u G hcal hpos n
  have he := (henergy ρ α hell u G hcal hpos n).2
  have hfactor : 0 ≤ 2 / κ := by positivity
  have hpoint (z : ℝ × Vec d) :
      η z ^ 2 * deriv (deriv (PDE.Parabolic.LocalMax.powF p ε n)) (u z) * euclideanSq (G z) =
      (2 / κ) * (κ / 2 * deriv (deriv (PDE.Parabolic.LocalMax.powF p ε n)) (u z) *
        euclideanSq (G z) * η z ^ 2) := by
    field_simp
  calc
    _ = ENNReal.ofReal (2 / κ) *
        (∫⁻ z in Set.Ioo a b ×ˢ sourceBall 0 R, ENNReal.ofReal
          (κ / 2 * deriv (deriv (PDE.Parabolic.LocalMax.powF p ε n)) (u z) *
            euclideanSq (G z) * η z ^ 2)) := by
      simp_rw [hpoint, ENNReal.ofReal_mul hfactor]
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ENNReal.ofReal (2 / κ) * (ENNReal.ofReal B *
        ∫⁻ z in Set.Ioo a b ×ˢ sourceBall 0 R, ENNReal.ofReal (u z + ε) ^ p) := by gcongr
    _ = _ := by rw [mul_assoc]

/-- Quantitative cutoff coefficient energy with explicit derivative bounds. -/
theorem c11_weighted_caloric_truncated_power_cutoff_energy_bounds_explicit
    {d : ℕ} {κ R a b : ℝ} (hκ : 0 < κ) (hR : 0 < R) (hab : a < b)
    (η : ℝ × Vec d → ℝ) (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hηc : HasCompactSupport η)
    (hηs : tsupport η ⊆ Set.Ioo a b ×ˢ sourceBall 0 R)
    (A T D : ℝ) (hA : 0 ≤ A) (hT : 0 ≤ T)
    (hηbound : ∀ z, |η z| ≤ A)
    (htbound : ∀ z, |fderiv ℝ η z (1, 0)| ≤ T)
    (hdbound : ∀ z, euclideanSq (fun j => fderiv ℝ η z (0, unitVector j)) ≤ D ^ 2)
    {p ε : ℝ} (hp : 1 < p) (hε : 0 < ε) :
    let B := 2 * κ⁻¹ * A * T + 2 * κ⁻¹ * (2 + p / (p - 1)) * D ^ 2
    let C := ENNReal.ofReal (2 * κ⁻¹ * (2 + p / (p - 1)))
    let E := ENNReal.ofReal (2 / κ) * ENNReal.ofReal B
    ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
    IsUniformlyElliptic κ ρ α →
    ∀ (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d),
    IsWeightedCaloric ρ α (Set.Ioo a b) (sourceBall 0 R) u G →
    (∀ᵐ z ∂volume.restrict (Set.Ioo a b ×ˢ sourceBall 0 R), 0 ≤ u z) →
    ∀ n : ℕ,
      (∫⁻ z in Set.Ioo a b ×ˢ sourceBall 0 R, ENNReal.ofReal
        (dot ((α z.2).mulVec
          (η z • (deriv (PDE.Parabolic.LocalMax.powG p ε n) (u z) • G z) +
            PDE.Parabolic.LocalMax.powG p ε n (u z) •
              (fun j => fderiv ℝ η z (0, unitVector j))))
          (η z • (deriv (PDE.Parabolic.LocalMax.powG p ε n) (u z) • G z) +
            PDE.Parabolic.LocalMax.powG p ε n (u z) •
              (fun j => fderiv ℝ η z (0, unitVector j))))) ≤
      C * (E + ENNReal.ofReal (D ^ 2)) *
        ∫⁻ z in Set.Ioo a b ×ˢ sourceBall 0 R, ENNReal.ofReal (u z + ε) ^ p := by
  dsimp only
  let B := 2 * κ⁻¹ * A * T + 2 * κ⁻¹ * (2 + p / (p - 1)) * D ^ 2
  let E : ℝ≥0∞ := ENNReal.ofReal (2 / κ) * ENNReal.ofReal B
  let C : ℝ≥0∞ := ENNReal.ofReal (2 * κ⁻¹ * (2 + p / (p - 1)))
  have hgrad := c11_weighted_caloric_truncated_power_gradient_bounds_explicit
    hκ hR hab η hη hηc hηs A T D hA hT hηbound htbound hdbound hp hε
  have hsq := hdbound
  intro ρ α hell u G hcal hpos n
  have herr : (∫⁻ z in Set.Ioo a b ×ˢ sourceBall 0 R, ENNReal.ofReal
      (PDE.Parabolic.LocalMax.powF p ε n (u z) *
        euclideanSq (fun j => fderiv ℝ η z (0, unitVector j)))) ≤
      ENNReal.ofReal (D ^ 2) *
        ∫⁻ z in Set.Ioo a b ×ˢ sourceBall 0 R, ENNReal.ofReal (u z + ε) ^ p := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply lintegral_mono_ae
    filter_upwards [hpos] with z hz
    rw [ENNReal.ofReal_rpow_of_nonneg (by linarith) (by linarith),
      ← ENNReal.ofReal_mul (sq_nonneg D)]
    apply ENNReal.ofReal_le_ofReal
    have hf := c11_truncated_power_energy_structure hp hε n (u z) hz
    have hr : 0 ≤ (u z + ε) ^ p := Real.rpow_nonneg (by linarith) _
    have hs := PDE.vecNormSq_nonneg (fun j => fderiv ℝ η z (0, unitVector j))
    calc
      _ ≤ (u z + ε) ^ p * D ^ 2 := mul_le_mul hf.2.2.2.2.2 (hsq z) hs hr
      _ = _ := by ring
  have hc := c11_weighted_truncated_power_cutoff_energy_integral hκ hell hcal hpos
    η hη.continuous (fun z j => fderiv ℝ η z (0, unitVector j)) hp hε n
  calc
    _ ≤ C * ((∫⁻ z in Set.Ioo a b ×ˢ sourceBall 0 R, ENNReal.ofReal
          (η z ^ 2 * deriv (deriv (PDE.Parabolic.LocalMax.powF p ε n)) (u z) * euclideanSq (G z))) +
        ∫⁻ z in Set.Ioo a b ×ˢ sourceBall 0 R, ENNReal.ofReal
          (PDE.Parabolic.LocalMax.powF p ε n (u z) *
            euclideanSq (fun j => fderiv ℝ η z (0, unitVector j)))) := hc
    _ ≤ C * (E * (∫⁻ z in Set.Ioo a b ×ˢ sourceBall 0 R, ENNReal.ofReal (u z + ε) ^ p) +
        ENNReal.ofReal (D ^ 2) * (∫⁻ z in Set.Ioo a b ×ˢ sourceBall 0 R,
          ENNReal.ofReal (u z + ε) ^ p)) := by
      gcongr
      exact hgrad ρ α hell u G hcal hpos n
    _ = _ := by rw [← add_mul, mul_assoc]

/-- The cutoff power gain with explicit energy constants. -/
theorem c11_weighted_caloric_power_gain_of_energy_explicit (d : ℕ) (hd : 2 ≤ d)
    {κ R a b : ℝ} (hκ : 0 < κ) (hR : 0 < R) (hab : a < b)
    (hfinite : volume (Set.Ioo a b ×ˢ sourceBall (0 : Vec d) R) < ∞)
    (η : ℝ × Vec d → ℝ) (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hηc : HasCompactSupport η)
    (hηs : tsupport η ⊆ Set.Ioo a b ×ˢ sourceBall 0 R)
    (A₀ T₀ D₀ : ℝ) (hA₀ : 0 ≤ A₀) (hT₀ : 0 ≤ T₀)
    (hηbound : ∀ z, |η z| ≤ A₀)
    (htbound : ∀ z, |fderiv ℝ η z (1, 0)| ≤ T₀)
    (hdbound : ∀ z, euclideanSq (fun j => fderiv ℝ η z (0, unitVector j)) ≤ D₀ ^ 2)
    (htest : ∀ᵐ t ∂volume.restrict (Set.Ioo a b),
      IsSpatialTest (sourceBall 0 R) (fun x => η (t,x)))
    (K : Set (Vec d)) (hK : IsCompact K) (hKU : K ⊆ sourceBall 0 R)
    (hzero : ∀ t x, x ∉ K → η (t,x) = 0)
    (S : Set (ℝ × Vec d)) (hS : MeasurableSet S)
    (hSV : S ⊆ Set.Ioo a b ×ˢ sourceBall 0 R)
    (hηone : ∀ z ∈ S, η z = 1)
    {p ε : ℝ} (hp : 1 < p) (hε : 0 < ε) :
    let B := 2 * κ⁻¹ * A₀ * T₀ + 2 * κ⁻¹ * (2 + p / (p - 1)) * D₀ ^ 2
    let A := ENNReal.ofReal (2 + p / (p - 1)) * ENNReal.ofReal B
    let E := ENNReal.ofReal (2 * κ⁻¹ * (2 + p / (p - 1))) *
      (ENNReal.ofReal (2 / κ) * ENNReal.ofReal B + ENNReal.ofReal (D₀ ^ 2))
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
    ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d), IsUniformlyElliptic κ ρ α →
    ∀ (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d),
    IsWeightedCaloric ρ α (Set.Ioo a b) (sourceBall 0 R) u G →
    (∀ᵐ z ∂volume.restrict (Set.Ioo a b ×ˢ sourceBall 0 R), 0 ≤ u z) →
    (∫⁻ z in S, ENNReal.ofReal (u z + ε) ^ (p * (((d : ℝ) + 2) / d))) ≤
      ENNReal.ofReal κ⁻¹ * (C *
        (A * (∫⁻ z in Set.Ioo a b ×ˢ sourceBall 0 R, ENNReal.ofReal (u z + ε) ^ p)) ^
          (2 / (d : ℝ)) *
        (E * (∫⁻ z in Set.Ioo a b ×ˢ sourceBall 0 R, ENNReal.ofReal (u z + ε) ^ p))) := by
  dsimp only
  let B := 2 * κ⁻¹ * A₀ * T₀ + 2 * κ⁻¹ * (2 + p / (p - 1)) * D₀ ^ 2
  let A : ℝ≥0∞ := ENNReal.ofReal (2 + p / (p - 1)) * ENNReal.ofReal B
  let E : ℝ≥0∞ := ENNReal.ofReal (2 * κ⁻¹ * (2 + p / (p - 1))) *
    (ENNReal.ofReal (2 / κ) * ENNReal.ofReal B + ENNReal.ofReal (D₀ ^ 2))
  obtain ⟨C, hC, hgain⟩ := c11_weighted_caloric_cutoff_power_gain d hd κ hκ
  have hslice := c11_weighted_caloric_truncated_power_slice_bounds_explicit
    hκ hR hab η hη hηc hηs A₀ T₀ D₀ hA₀ hT₀ hηbound htbound hdbound hp hε
  have henergy := c11_weighted_caloric_truncated_power_cutoff_energy_bounds_explicit
    hκ hR hab η hη hηc hηs A₀ T₀ D₀ hA₀ hT₀ hηbound htbound hdbound hp hε
  refine ⟨C, hC, ?_⟩
  intro ρ α hell u G hcal hpos
  let μ := volume.restrict (Set.Ioo a b ×ˢ sourceBall (0 : Vec d) R)
  have hOpen : IsOpen (sourceBall (0 : Vec d) R) := by
    have hsum : Continuous (fun v : Vec d => ∑ j, v j * v j) :=
      continuous_finset_sum Finset.univ fun j _ => (continuous_apply j).mul (continuous_apply j)
    have hn : Continuous (fun v : Vec d => euclideanNorm v) := by
      unfold euclideanNorm euclideanSq dot
      exact Real.continuous_sqrt.comp hsum
    exact isOpen_lt (hn.comp (continuous_id.sub continuous_const)) continuous_const
  apply hgain ρ α hell (Set.Ioo a b) (sourceBall 0 R) measurableSet_Ioo
    hOpen hfinite u G hcal η hη hηc htest K hK hKU hzero
    S hS hSV (ae_restrict_of_ae_restrict_of_subset hSV hpos) hηone p ε hp hε
    (A * ∫⁻ z in Set.Ioo a b ×ˢ sourceBall 0 R, ENNReal.ofReal (u z + ε) ^ p)
    (E * ∫⁻ z in Set.Ioo a b ×ˢ sourceBall 0 R, ENNReal.ofReal (u z + ε) ^ p)
    (fun n => hslice ρ α hell u G hcal hpos n)
  intro n
  let F := PDE.Parabolic.LocalMax.powG p ε n
  let V : ℝ × Vec d → Vec d := fun z =>
    η z • (deriv F (u z) • G z) + F (u z) •
      (fun j => fderiv ℝ η z (0, unitVector j))
  have hF : ContDiff ℝ 1 F := PDE.Parabolic.LocalMax.powG_contDiff hε (Nat.cast_nonneg n)
  have hηd : Continuous (fun z => fun j => fderiv ℝ η z (0, unitVector j)) :=
    continuous_pi fun j => (hη.continuous_fderiv (by simp)).clm_apply continuous_const
  have hV : AEStronglyMeasurable V μ :=
    (hη.continuous.aestronglyMeasurable.smul
      ((hF.continuous_deriv_one.comp_aestronglyMeasurable hcal.1.aestronglyMeasurable).smul hcal.2.1)).add
      ((hF.continuous.comp_aestronglyMeasurable hcal.1.aestronglyMeasurable).smul hηd.aestronglyMeasurable)
  have hfub := c11_weighted_coefficient_energy_lintegral_prod hell V hV
  rw [← hfub]
  exact henergy ρ α hell u G hcal hpos n


/-- Ramp error when the time cutoff is controlled through its product with the cutoff. -/
theorem c11_cutoff_ramp_error_le_of_product_bound {d : ℕ} {κ : ℝ} (hκ : 0 < κ)
    (η : ℝ × Vec d → ℝ) (K T D : ℝ)
    (hK : 0 ≤ K) (_hT : 0 ≤ T)
    (ht : ∀ z, |η z * fderiv ℝ η z (1, 0)| ≤ T)
    (hd : ∀ z, euclideanSq (fun j => fderiv ℝ η z (0, unitVector j)) ≤ D ^ 2)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d) (hell : IsUniformlyElliptic κ ρ α)
    (z : ℝ × Vec d) :
    0 ≤ 2 * ρ z.2 * |η z| * |fderiv ℝ η z (1, 0)| +
      2 * κ⁻¹ * K * euclideanSq (fun j => fderiv ℝ η z (0, unitVector j)) ∧
    2 * ρ z.2 * |η z| * |fderiv ℝ η z (1, 0)| +
      2 * κ⁻¹ * K * euclideanSq (fun j => fderiv ℝ η z (0, unitVector j)) ≤
      2 * κ⁻¹ * T + 2 * κ⁻¹ * K * D ^ 2 := by
  have hρ0 : 0 ≤ ρ z.2 := hκ.le.trans (hell.2.2 z.2).1
  have hρ : ρ z.2 ≤ κ⁻¹ := (hell.2.2 z.2).2.1
  have he0 := PDE.vecNormSq_nonneg (fun j => fderiv ℝ η z (0, unitVector j))
  have ht' : |η z| * |fderiv ℝ η z (1, 0)| ≤ T := by simpa [abs_mul] using ht z
  constructor
  · positivity
  · have hfirst : 2 * ρ z.2 * (|η z| * |fderiv ℝ η z (1, 0)|) ≤ 2 * κ⁻¹ * T := by
      gcongr
    have hsecond : 2 * κ⁻¹ * K * euclideanSq (fun j => fderiv ℝ η z (0, unitVector j)) ≤
        2 * κ⁻¹ * K * D ^ 2 := by gcongr; exact hd z
    nlinarith

/-- Quantitative energy using the cutoff product time-derivative bound. -/
theorem c11_weighted_caloric_truncated_power_energy_bounds_product {d : ℕ} {κ R a b : ℝ}
    (hκ : 0 < κ) (hR : 0 < R) (hab : a < b)
    (η : ℝ × Vec d → ℝ) (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hηc : HasCompactSupport η)
    (hηs : tsupport η ⊆ Set.Ioo a b ×ˢ sourceBall 0 R)
    (T D : ℝ) (hT : 0 ≤ T)
    (htbound : ∀ z, |η z * fderiv ℝ η z (1, 0)| ≤ T)
    (hdbound : ∀ z, euclideanSq (fun j => fderiv ℝ η z (0, unitVector j)) ≤ D ^ 2)
    {p ε : ℝ} (hp : 1 < p) (hε : 0 < ε) :
    let B := 2 * κ⁻¹ * T + 2 * κ⁻¹ * (2 + p / (p - 1)) * D ^ 2
    ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
    IsUniformlyElliptic κ ρ α →
    ∀ (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d),
    IsWeightedCaloric ρ α (Set.Ioo a b) (sourceBall 0 R) u G →
    (∀ᵐ z ∂volume.restrict (Set.Ioo a b ×ˢ sourceBall 0 R), 0 ≤ u z) →
    ∀ n : ℕ,
    (∀ᵐ v ∂volume.restrict (Set.Ioo a b),
      ∫⁻ x in sourceBall 0 R, ENNReal.ofReal
        (ρ x * (PDE.Parabolic.LocalMax.powF p ε n (u (v, x)) * η (v, x) ^ 2)) ≤
        ENNReal.ofReal B * ∫⁻ z in Set.Ioo a b ×ˢ sourceBall 0 R,
          ENNReal.ofReal (u z + ε) ^ p) ∧
    (∫⁻ z in Set.Ioo a b ×ˢ sourceBall 0 R, ENNReal.ofReal
      (κ / 2 * deriv (deriv (PDE.Parabolic.LocalMax.powF p ε n)) (u z) *
        euclideanSq (G z) * η z ^ 2)) ≤
      ENNReal.ofReal B * ∫⁻ z in Set.Ioo a b ×ˢ sourceBall 0 R,
        ENNReal.ofReal (u z + ε) ^ p := by
  have hK : 0 ≤ 2 + p / (p - 1) := by positivity
  dsimp only
  let B := 2 * κ⁻¹ * T + 2 * κ⁻¹ * (2 + p / (p - 1)) * D ^ 2
  have hB : 0 ≤ B := by dsimp [B]; positivity
  intro ρ α hell u G hcal hpos n
  have hcut := c11_cutoff_ramp_error_le_of_product_bound hκ η (2 + p / (p - 1)) T D
    hK hT htbound hdbound ρ α hell
  obtain ⟨M, hM⟩ := PDE.Parabolic.LocalMax.exists_powF2_bound hp hε (Nat.cast_nonneg n)
  have hconvex : ∀ᵐ z ∂volume.restrict (Set.Ioo a b ×ˢ sourceBall 0 R),
      0 ≤ PDE.Parabolic.LocalMax.powF p ε n (u z) ∧
      0 ≤ deriv (deriv (PDE.Parabolic.LocalMax.powF p ε n)) (u z) ∧
      deriv (PDE.Parabolic.LocalMax.powF p ε n) (u z) ^ 2 ≤
        (2 + p / (p - 1)) * deriv (deriv (PDE.Parabolic.LocalMax.powF p ε n)) (u z) *
          PDE.Parabolic.LocalMax.powF p ε n (u z) := by
    filter_upwards [hpos] with z hz
    have hs := c11_truncated_power_energy_structure hp hε n (u z) hz
    exact ⟨hs.1, hs.2.1, hs.2.2.1⟩
  have hbound : (∫⁻ z in Set.Ioo a b ×ˢ sourceBall 0 R,
      ENNReal.ofReal (PDE.Parabolic.LocalMax.powF p ε n (u z))) ≤
      ∫⁻ z in Set.Ioo a b ×ˢ sourceBall 0 R, ENNReal.ofReal (u z + ε) ^ p := by
    apply lintegral_mono_ae
    filter_upwards [hpos] with z hz
    rw [ENNReal.ofReal_rpow_of_nonneg (by linarith) (by linarith)]
    exact ENNReal.ofReal_le_ofReal
      (c11_truncated_power_energy_structure hp hε n (u z) hz).2.2.2.2.2
  have he := c11_weighted_caloric_renormalized_energy_bounds hκ hR hab ρ α hell u G hcal
    (PDE.Parabolic.LocalMax.powF p ε n)
    (PDE.Parabolic.LocalMax.powF_contDiff hε (Nat.cast_nonneg n)) M M.coe_nonneg hM
    η hη hηc hηs _ B hK hB hconvex (Filter.Eventually.of_forall hcut)
  have hmul : ENNReal.ofReal B *
      (∫⁻ z in Set.Ioo a b ×ˢ sourceBall 0 R,
        ENNReal.ofReal (PDE.Parabolic.LocalMax.powF p ε n (u z))) ≤
      ENNReal.ofReal B *
      (∫⁻ z in Set.Ioo a b ×ˢ sourceBall 0 R, ENNReal.ofReal (u z + ε) ^ p) := by
    gcongr
  exact ⟨he.1.mono (fun _ ht => ht.trans hmul), he.2.trans hmul⟩


theorem c11_weighted_caloric_truncated_power_slice_bounds_product {d : ℕ} {κ R a b : ℝ}
    (hκ : 0 < κ) (hR : 0 < R) (hab : a < b)
    (η : ℝ × Vec d → ℝ) (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hηc : HasCompactSupport η)
    (hηs : tsupport η ⊆ Set.Ioo a b ×ˢ sourceBall 0 R)
    (T D : ℝ) (hT : 0 ≤ T)
    (htbound : ∀ z, |η z * fderiv ℝ η z (1, 0)| ≤ T)
    (hdbound : ∀ z, euclideanSq (fun j => fderiv ℝ η z (0, unitVector j)) ≤ D ^ 2)
    {p ε : ℝ} (hp : 1 < p) (hε : 0 < ε) :
    let B := 2 * κ⁻¹ * T + 2 * κ⁻¹ * (2 + p / (p - 1)) * D ^ 2
    ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
    IsUniformlyElliptic κ ρ α →
    ∀ (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d),
    IsWeightedCaloric ρ α (Set.Ioo a b) (sourceBall 0 R) u G →
    (∀ᵐ z ∂volume.restrict (Set.Ioo a b ×ˢ sourceBall 0 R), 0 ≤ u z) →
    ∀ n : ℕ, ∀ᵐ t ∂volume.restrict (Set.Ioo a b),
      (∫⁻ x in sourceBall 0 R, ENNReal.ofReal (ρ x) *
        ‖η (t,x) * PDE.Parabolic.LocalMax.powG p ε n (u (t,x))‖ₑ ^ (2 : ℝ)) ≤
      (ENNReal.ofReal (2 + p / (p - 1)) * ENNReal.ofReal B) *
        ∫⁻ z in Set.Ioo a b ×ˢ sourceBall 0 R, ENNReal.ofReal (u z + ε) ^ p := by
  dsimp only
  let B := 2 * κ⁻¹ * T + 2 * κ⁻¹ * (2 + p / (p - 1)) * D ^ 2
  have henergy := c11_weighted_caloric_truncated_power_energy_bounds_product
    hκ hR hab η hη hηc hηs T D hT htbound hdbound hp hε
  intro ρ α hell u G hcal hpos n
  have hpairs : ∀ᵐ z ∂((volume.restrict (Set.Ioo a b)).prod
      (volume.restrict (sourceBall (0 : Vec d) R))), 0 ≤ u z := by
    rw [Measure.prod_restrict]
    exact hpos
  filter_upwards [Measure.ae_ae_of_ae_prod hpairs, (henergy ρ α hell u G hcal hpos n).1] with t ht he
  have hslice := c11_weighted_truncated_power_slice_mass_le (ρ := ρ)
    (fun x => u (t,x)) (fun x => η (t,x)) ht hp hε n
  have heq : (∫⁻ x in sourceBall 0 R, ENNReal.ofReal (ρ x) *
      ENNReal.ofReal (η (t,x) ^ 2 * PDE.Parabolic.LocalMax.powF p ε n (u (t,x)))) =
      ∫⁻ x in sourceBall 0 R, ENNReal.ofReal
        (ρ x * (PDE.Parabolic.LocalMax.powF p ε n (u (t,x)) * η (t,x) ^ 2)) := by
    apply lintegral_congr
    intro x
    rw [← ENNReal.ofReal_mul (hκ.le.trans (hell.2.2 x).1)]
    congr 1
    ring
  rw [heq] at hslice
  calc
    _ ≤ ENNReal.ofReal (2 + p / (p - 1)) *
        (∫⁻ x in sourceBall 0 R, ENNReal.ofReal
          (ρ x * (PDE.Parabolic.LocalMax.powF p ε n (u (t,x)) * η (t,x) ^ 2))) := hslice
    _ ≤ ENNReal.ofReal (2 + p / (p - 1)) * (ENNReal.ofReal B *
        ∫⁻ z in Set.Ioo a b ×ˢ sourceBall 0 R, ENNReal.ofReal (u z + ε) ^ p) := by gcongr
    _ = _ := by rw [mul_assoc]


theorem c11_weighted_caloric_truncated_power_gradient_bounds_product {d : ℕ} {κ R a b : ℝ}
    (hκ : 0 < κ) (hR : 0 < R) (hab : a < b)
    (η : ℝ × Vec d → ℝ) (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hηc : HasCompactSupport η)
    (hηs : tsupport η ⊆ Set.Ioo a b ×ˢ sourceBall 0 R)
    (T D : ℝ) (hT : 0 ≤ T)
    (htbound : ∀ z, |η z * fderiv ℝ η z (1, 0)| ≤ T)
    (hdbound : ∀ z, euclideanSq (fun j => fderiv ℝ η z (0, unitVector j)) ≤ D ^ 2)
    {p ε : ℝ} (hp : 1 < p) (hε : 0 < ε) :
    let B := 2 * κ⁻¹ * T + 2 * κ⁻¹ * (2 + p / (p - 1)) * D ^ 2
    ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
    IsUniformlyElliptic κ ρ α →
    ∀ (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d),
    IsWeightedCaloric ρ α (Set.Ioo a b) (sourceBall 0 R) u G →
    (∀ᵐ z ∂volume.restrict (Set.Ioo a b ×ˢ sourceBall 0 R), 0 ≤ u z) →
    ∀ n : ℕ,
      (∫⁻ z in Set.Ioo a b ×ˢ sourceBall 0 R, ENNReal.ofReal
        (η z ^ 2 * deriv (deriv (PDE.Parabolic.LocalMax.powF p ε n)) (u z) *
          euclideanSq (G z))) ≤
      (ENNReal.ofReal (2 / κ) * ENNReal.ofReal B) *
        ∫⁻ z in Set.Ioo a b ×ˢ sourceBall 0 R, ENNReal.ofReal (u z + ε) ^ p := by
  dsimp only
  let B := 2 * κ⁻¹ * T + 2 * κ⁻¹ * (2 + p / (p - 1)) * D ^ 2
  have henergy := c11_weighted_caloric_truncated_power_energy_bounds_product
    hκ hR hab η hη hηc hηs T D hT htbound hdbound hp hε
  intro ρ α hell u G hcal hpos n
  have he := (henergy ρ α hell u G hcal hpos n).2
  have hfactor : 0 ≤ 2 / κ := by positivity
  have hpoint (z : ℝ × Vec d) :
      η z ^ 2 * deriv (deriv (PDE.Parabolic.LocalMax.powF p ε n)) (u z) * euclideanSq (G z) =
      (2 / κ) * (κ / 2 * deriv (deriv (PDE.Parabolic.LocalMax.powF p ε n)) (u z) *
        euclideanSq (G z) * η z ^ 2) := by
    field_simp
  calc
    _ = ENNReal.ofReal (2 / κ) *
        (∫⁻ z in Set.Ioo a b ×ˢ sourceBall 0 R, ENNReal.ofReal
          (κ / 2 * deriv (deriv (PDE.Parabolic.LocalMax.powF p ε n)) (u z) *
            euclideanSq (G z) * η z ^ 2)) := by
      simp_rw [hpoint, ENNReal.ofReal_mul hfactor]
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ENNReal.ofReal (2 / κ) * (ENNReal.ofReal B *
        ∫⁻ z in Set.Ioo a b ×ˢ sourceBall 0 R, ENNReal.ofReal (u z + ε) ^ p) := by gcongr
    _ = _ := by rw [mul_assoc]


theorem c11_weighted_caloric_truncated_power_cutoff_energy_bounds_product
    {d : ℕ} {κ R a b : ℝ} (hκ : 0 < κ) (hR : 0 < R) (hab : a < b)
    (η : ℝ × Vec d → ℝ) (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hηc : HasCompactSupport η)
    (hηs : tsupport η ⊆ Set.Ioo a b ×ˢ sourceBall 0 R)
    (T D : ℝ) (hT : 0 ≤ T)
    (htbound : ∀ z, |η z * fderiv ℝ η z (1, 0)| ≤ T)
    (hdbound : ∀ z, euclideanSq (fun j => fderiv ℝ η z (0, unitVector j)) ≤ D ^ 2)
    {p ε : ℝ} (hp : 1 < p) (hε : 0 < ε) :
    let B := 2 * κ⁻¹ * T + 2 * κ⁻¹ * (2 + p / (p - 1)) * D ^ 2
    let C := ENNReal.ofReal (2 * κ⁻¹ * (2 + p / (p - 1)))
    let E := ENNReal.ofReal (2 / κ) * ENNReal.ofReal B
    ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
    IsUniformlyElliptic κ ρ α →
    ∀ (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d),
    IsWeightedCaloric ρ α (Set.Ioo a b) (sourceBall 0 R) u G →
    (∀ᵐ z ∂volume.restrict (Set.Ioo a b ×ˢ sourceBall 0 R), 0 ≤ u z) →
    ∀ n : ℕ,
      (∫⁻ z in Set.Ioo a b ×ˢ sourceBall 0 R, ENNReal.ofReal
        (dot ((α z.2).mulVec
          (η z • (deriv (PDE.Parabolic.LocalMax.powG p ε n) (u z) • G z) +
            PDE.Parabolic.LocalMax.powG p ε n (u z) •
              (fun j => fderiv ℝ η z (0, unitVector j))))
          (η z • (deriv (PDE.Parabolic.LocalMax.powG p ε n) (u z) • G z) +
            PDE.Parabolic.LocalMax.powG p ε n (u z) •
              (fun j => fderiv ℝ η z (0, unitVector j))))) ≤
      C * (E + ENNReal.ofReal (D ^ 2)) *
        ∫⁻ z in Set.Ioo a b ×ˢ sourceBall 0 R, ENNReal.ofReal (u z + ε) ^ p := by
  dsimp only
  let B := 2 * κ⁻¹ * T + 2 * κ⁻¹ * (2 + p / (p - 1)) * D ^ 2
  let E : ℝ≥0∞ := ENNReal.ofReal (2 / κ) * ENNReal.ofReal B
  let C : ℝ≥0∞ := ENNReal.ofReal (2 * κ⁻¹ * (2 + p / (p - 1)))
  have hgrad := c11_weighted_caloric_truncated_power_gradient_bounds_product
    hκ hR hab η hη hηc hηs T D hT htbound hdbound hp hε
  have hsq := hdbound
  intro ρ α hell u G hcal hpos n
  have herr : (∫⁻ z in Set.Ioo a b ×ˢ sourceBall 0 R, ENNReal.ofReal
      (PDE.Parabolic.LocalMax.powF p ε n (u z) *
        euclideanSq (fun j => fderiv ℝ η z (0, unitVector j)))) ≤
      ENNReal.ofReal (D ^ 2) *
        ∫⁻ z in Set.Ioo a b ×ˢ sourceBall 0 R, ENNReal.ofReal (u z + ε) ^ p := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply lintegral_mono_ae
    filter_upwards [hpos] with z hz
    rw [ENNReal.ofReal_rpow_of_nonneg (by linarith) (by linarith),
      ← ENNReal.ofReal_mul (sq_nonneg D)]
    apply ENNReal.ofReal_le_ofReal
    have hf := c11_truncated_power_energy_structure hp hε n (u z) hz
    have hr : 0 ≤ (u z + ε) ^ p := Real.rpow_nonneg (by linarith) _
    have hs := PDE.vecNormSq_nonneg (fun j => fderiv ℝ η z (0, unitVector j))
    calc
      _ ≤ (u z + ε) ^ p * D ^ 2 := mul_le_mul hf.2.2.2.2.2 (hsq z) hs hr
      _ = _ := by ring
  have hc := c11_weighted_truncated_power_cutoff_energy_integral hκ hell hcal hpos
    η hη.continuous (fun z j => fderiv ℝ η z (0, unitVector j)) hp hε n
  calc
    _ ≤ C * ((∫⁻ z in Set.Ioo a b ×ˢ sourceBall 0 R, ENNReal.ofReal
          (η z ^ 2 * deriv (deriv (PDE.Parabolic.LocalMax.powF p ε n)) (u z) * euclideanSq (G z))) +
        ∫⁻ z in Set.Ioo a b ×ˢ sourceBall 0 R, ENNReal.ofReal
          (PDE.Parabolic.LocalMax.powF p ε n (u z) *
            euclideanSq (fun j => fderiv ℝ η z (0, unitVector j)))) := hc
    _ ≤ C * (E * (∫⁻ z in Set.Ioo a b ×ˢ sourceBall 0 R, ENNReal.ofReal (u z + ε) ^ p) +
        ENNReal.ofReal (D ^ 2) * (∫⁻ z in Set.Ioo a b ×ˢ sourceBall 0 R,
          ENNReal.ofReal (u z + ε) ^ p)) := by
      gcongr
      exact hgrad ρ α hell u G hcal hpos n
    _ = _ := by rw [← add_mul, mul_assoc]


theorem c11_weighted_caloric_power_gain_of_energy_product (d : ℕ) (hd : 2 ≤ d)
    {κ R a b : ℝ} (hκ : 0 < κ) (hR : 0 < R) (hab : a < b)
    (hfinite : volume (Set.Ioo a b ×ˢ sourceBall (0 : Vec d) R) < ∞)
    (η : ℝ × Vec d → ℝ) (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hηc : HasCompactSupport η)
    (hηs : tsupport η ⊆ Set.Ioo a b ×ˢ sourceBall 0 R)
    (T₀ D₀ : ℝ) (hT₀ : 0 ≤ T₀)
    (htbound : ∀ z, |η z * fderiv ℝ η z (1, 0)| ≤ T₀)
    (hdbound : ∀ z, euclideanSq (fun j => fderiv ℝ η z (0, unitVector j)) ≤ D₀ ^ 2)
    (htest : ∀ᵐ t ∂volume.restrict (Set.Ioo a b),
      IsSpatialTest (sourceBall 0 R) (fun x => η (t,x)))
    (K : Set (Vec d)) (hK : IsCompact K) (hKU : K ⊆ sourceBall 0 R)
    (hzero : ∀ t x, x ∉ K → η (t,x) = 0)
    (S : Set (ℝ × Vec d)) (hS : MeasurableSet S)
    (hSV : S ⊆ Set.Ioo a b ×ˢ sourceBall 0 R)
    (hηone : ∀ z ∈ S, η z = 1)
    {p ε : ℝ} (hp : 1 < p) (hε : 0 < ε) :
    let B := 2 * κ⁻¹ * T₀ + 2 * κ⁻¹ * (2 + p / (p - 1)) * D₀ ^ 2
    let A := ENNReal.ofReal (2 + p / (p - 1)) * ENNReal.ofReal B
    let E := ENNReal.ofReal (2 * κ⁻¹ * (2 + p / (p - 1))) *
      (ENNReal.ofReal (2 / κ) * ENNReal.ofReal B + ENNReal.ofReal (D₀ ^ 2))
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
    ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d), IsUniformlyElliptic κ ρ α →
    ∀ (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d),
    IsWeightedCaloric ρ α (Set.Ioo a b) (sourceBall 0 R) u G →
    (∀ᵐ z ∂volume.restrict (Set.Ioo a b ×ˢ sourceBall 0 R), 0 ≤ u z) →
    (∫⁻ z in S, ENNReal.ofReal (u z + ε) ^ (p * (((d : ℝ) + 2) / d))) ≤
      ENNReal.ofReal κ⁻¹ * (C *
        (A * (∫⁻ z in Set.Ioo a b ×ˢ sourceBall 0 R, ENNReal.ofReal (u z + ε) ^ p)) ^
          (2 / (d : ℝ)) *
        (E * (∫⁻ z in Set.Ioo a b ×ˢ sourceBall 0 R, ENNReal.ofReal (u z + ε) ^ p))) := by
  dsimp only
  let B := 2 * κ⁻¹ * T₀ + 2 * κ⁻¹ * (2 + p / (p - 1)) * D₀ ^ 2
  let A : ℝ≥0∞ := ENNReal.ofReal (2 + p / (p - 1)) * ENNReal.ofReal B
  let E : ℝ≥0∞ := ENNReal.ofReal (2 * κ⁻¹ * (2 + p / (p - 1))) *
    (ENNReal.ofReal (2 / κ) * ENNReal.ofReal B + ENNReal.ofReal (D₀ ^ 2))
  obtain ⟨C, hC, hgain⟩ := c11_weighted_caloric_cutoff_power_gain d hd κ hκ
  have hslice := c11_weighted_caloric_truncated_power_slice_bounds_product
    hκ hR hab η hη hηc hηs T₀ D₀ hT₀ htbound hdbound hp hε
  have henergy := c11_weighted_caloric_truncated_power_cutoff_energy_bounds_product
    hκ hR hab η hη hηc hηs T₀ D₀ hT₀ htbound hdbound hp hε
  refine ⟨C, hC, ?_⟩
  intro ρ α hell u G hcal hpos
  let μ := volume.restrict (Set.Ioo a b ×ˢ sourceBall (0 : Vec d) R)
  have hOpen : IsOpen (sourceBall (0 : Vec d) R) := by
    have hsum : Continuous (fun v : Vec d => ∑ j, v j * v j) :=
      continuous_finset_sum Finset.univ fun j _ => (continuous_apply j).mul (continuous_apply j)
    have hn : Continuous (fun v : Vec d => euclideanNorm v) := by
      unfold euclideanNorm euclideanSq dot
      exact Real.continuous_sqrt.comp hsum
    exact isOpen_lt (hn.comp (continuous_id.sub continuous_const)) continuous_const
  apply hgain ρ α hell (Set.Ioo a b) (sourceBall 0 R) measurableSet_Ioo
    hOpen hfinite u G hcal η hη hηc htest K hK hKU hzero
    S hS hSV (ae_restrict_of_ae_restrict_of_subset hSV hpos) hηone p ε hp hε
    (A * ∫⁻ z in Set.Ioo a b ×ˢ sourceBall 0 R, ENNReal.ofReal (u z + ε) ^ p)
    (E * ∫⁻ z in Set.Ioo a b ×ˢ sourceBall 0 R, ENNReal.ofReal (u z + ε) ^ p)
    (fun n => hslice ρ α hell u G hcal hpos n)
  intro n
  let F := PDE.Parabolic.LocalMax.powG p ε n
  let V : ℝ × Vec d → Vec d := fun z =>
    η z • (deriv F (u z) • G z) + F (u z) •
      (fun j => fderiv ℝ η z (0, unitVector j))
  have hF : ContDiff ℝ 1 F := PDE.Parabolic.LocalMax.powG_contDiff hε (Nat.cast_nonneg n)
  have hηd : Continuous (fun z => fun j => fderiv ℝ η z (0, unitVector j)) :=
    continuous_pi fun j => (hη.continuous_fderiv (by simp)).clm_apply continuous_const
  have hV : AEStronglyMeasurable V μ :=
    (hη.continuous.aestronglyMeasurable.smul
      ((hF.continuous_deriv_one.comp_aestronglyMeasurable hcal.1.aestronglyMeasurable).smul hcal.2.1)).add
      ((hF.continuous.comp_aestronglyMeasurable hcal.1.aestronglyMeasurable).smul hηd.aestronglyMeasurable)
  have hfub := c11_weighted_coefficient_energy_lintegral_prod hell V hV
  rw [← hfub]
  exact henergy ρ α hell u G hcal hpos n



/-- The truncated-power coefficient is uniform over the Moser exponent range. -/
theorem c11_moser_power_coefficient_le (d : ℕ) (hd : 0 < d) {p : ℝ}
    (hp : ((d : ℝ) + 1) / d ≤ p) :
    2 + p / (p - 1) ≤ (d : ℝ) + 3 := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hp1 : 1 < p := by
    have : 1 < ((d : ℝ) + 1) / d := by rw [lt_div_iff₀ hd0]; linarith
    linarith
  have hpd : (d : ℝ) * (p - 1) ≥ 1 := by
    have := (div_le_iff₀ hd0).mp hp
    nlinarith
  have hdiv : p / (p - 1) ≤ (d : ℝ) + 1 := by
    apply (div_le_iff₀ (by linarith : 0 < p - 1)).2
    nlinarith
  linarith

/-- The explicit cutoff-energy coefficient has a uniform Moser exponent bound. -/
theorem c11_moser_energy_coefficient_le (d : ℕ) (hd : 0 < d)
    {κ p T D : ℝ} (hκ : 0 < κ) (_hT : 0 ≤ T)
    (hp : ((d : ℝ) + 1) / d ≤ p) :
    2 * κ⁻¹ * T + 2 * κ⁻¹ * (2 + p / (p - 1)) * D ^ 2 ≤
      2 * κ⁻¹ * T + 2 * κ⁻¹ * ((d : ℝ) + 3) * D ^ 2 := by
  have hc := c11_moser_power_coefficient_le d hd hp
  gcongr

/-- Explicit gap bounds for the compact nested-cylinder cutoff. -/
theorem c11_compact_cylinder_cutoff_gap_bounds :
    ∃ Q : ℝ, 0 ≤ Q ∧ ∀ {d : ℕ} {r R T T' b h : ℝ}
    (_hr : 0 ≤ r) (_hrR : r < R) (_hTT' : T < T') (_hh : 0 < h)
    {B : ℝ} (_hB : ∀ s, |deriv Real.smoothTransition s| ≤ B),
      let θ : ℝ → ℝ := fun t =>
        PDE.Parabolic.LocalMax.cylTimeRamp T ((T' - T) / 2) t *
          PDE.Parabolic.LocalMax.timeRamp b h t
      let ξ : Vec d → ℝ := PDE.canonicalBallCutoff (0 : Vec d) r R
      let η : ℝ × Vec d → ℝ := fun z => θ z.1 * ξ z.2
      (∀ z, |fderiv ℝ η z (1, 0)| ≤ 2 * B / (T' - T) + Q / h) ∧
      (∀ z, euclideanSq (fun j => fderiv ℝ η z (0, unitVector j)) ≤
        (32 / (R - r)) ^ 2) := by
  obtain ⟨Q, hQ, hQbound⟩ := PDE.Parabolic.LocalMax.exists_rampDeriv_le
  refine ⟨Q, hQ, ?_⟩
  intro d r R T T' b h hr hrR hTT' hh B hB
  dsimp only
  obtain ⟨ht, hx⟩ := c11_compact_cylinder_cutoff_derivatives (d := d) hr hrR hTT' hB
  constructor
  · intro z
    have hkernel : |PDE.Parabolic.LocalMax.rampKernel b h z.1| ≤ Q / h := by
      rw [abs_of_nonneg (PDE.Parabolic.LocalMax.rampKernel_nonneg hh _)]
      unfold PDE.Parabolic.LocalMax.rampKernel
      have hq := hQbound ((z.1 - (b - h)) / h)
      calc
        _ ≤ h⁻¹ * Q := mul_le_mul_of_nonneg_left hq (inv_nonneg.mpr hh.le)
        _ = _ := by ring
    exact (ht z).trans (add_le_add (le_refl _) hkernel)
  · intro z
    have hx' := hx z
    have heq : 1024 / (R - r) ^ 2 = (32 / (R - r)) ^ 2 := by
      rw [div_pow]
      norm_num
    exact hx'.trans_eq heq

/-- A single Sobolev gain constant works for every cutoff and power. -/
theorem c11_weighted_caloric_power_gain_of_energy_product_uniform (d : ℕ) (hd : 2 ≤ d)
    (κ : ℝ) (hκ : 0 < κ) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ {R a b : ℝ} (_hR : 0 < R) (_hab : a < b)
    (_hfinite : volume (Set.Ioo a b ×ˢ sourceBall (0 : Vec d) R) < ∞)
    (η : ℝ × Vec d → ℝ) (_hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (_hηc : HasCompactSupport η)
    (_hηs : tsupport η ⊆ Set.Ioo a b ×ˢ sourceBall 0 R)
    (T₀ D₀ : ℝ) (_hT₀ : 0 ≤ T₀)
    (_htbound : ∀ z, |η z * fderiv ℝ η z (1, 0)| ≤ T₀)
    (_hdbound : ∀ z, euclideanSq (fun j => fderiv ℝ η z (0, unitVector j)) ≤ D₀ ^ 2)
    (_htest : ∀ᵐ t ∂volume.restrict (Set.Ioo a b),
      IsSpatialTest (sourceBall 0 R) (fun x => η (t,x)))
    (K : Set (Vec d)) (_hK : IsCompact K) (_hKU : K ⊆ sourceBall 0 R)
    (_hzero : ∀ t x, x ∉ K → η (t,x) = 0)
    (S : Set (ℝ × Vec d)) (_hS : MeasurableSet S)
    (_hSV : S ⊆ Set.Ioo a b ×ˢ sourceBall 0 R)
    (_hηone : ∀ z ∈ S, η z = 1)
    {p ε : ℝ} (_hp : 1 < p) (_hε : 0 < ε),
    let B := 2 * κ⁻¹ * T₀ + 2 * κ⁻¹ * (2 + p / (p - 1)) * D₀ ^ 2
    let A := ENNReal.ofReal (2 + p / (p - 1)) * ENNReal.ofReal B
    let E := ENNReal.ofReal (2 * κ⁻¹ * (2 + p / (p - 1))) *
      (ENNReal.ofReal (2 / κ) * ENNReal.ofReal B + ENNReal.ofReal (D₀ ^ 2))
    ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d), IsUniformlyElliptic κ ρ α →
    ∀ (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d),
    IsWeightedCaloric ρ α (Set.Ioo a b) (sourceBall 0 R) u G →
    (∀ᵐ z ∂volume.restrict (Set.Ioo a b ×ˢ sourceBall 0 R), 0 ≤ u z) →
    (∫⁻ z in S, ENNReal.ofReal (u z + ε) ^ (p * (((d : ℝ) + 2) / d))) ≤
      ENNReal.ofReal κ⁻¹ * (C *
        (A * (∫⁻ z in Set.Ioo a b ×ˢ sourceBall 0 R, ENNReal.ofReal (u z + ε) ^ p)) ^
          (2 / (d : ℝ)) *
        (E * (∫⁻ z in Set.Ioo a b ×ˢ sourceBall 0 R, ENNReal.ofReal (u z + ε) ^ p))) := by
  obtain ⟨C, hC, hgain⟩ := c11_weighted_caloric_cutoff_power_gain d hd κ hκ
  refine ⟨C, hC, ?_⟩
  intro R a b hR hab hfinite η hη hηc hηs T₀ D₀ hT₀ htbound hdbound
    htest K hK hKU hzero S hS hSV hηone p ε hp hε
  dsimp only
  let B := 2 * κ⁻¹ * T₀ + 2 * κ⁻¹ * (2 + p / (p - 1)) * D₀ ^ 2
  let A : ℝ≥0∞ := ENNReal.ofReal (2 + p / (p - 1)) * ENNReal.ofReal B
  let E : ℝ≥0∞ := ENNReal.ofReal (2 * κ⁻¹ * (2 + p / (p - 1))) *
    (ENNReal.ofReal (2 / κ) * ENNReal.ofReal B + ENNReal.ofReal (D₀ ^ 2))
  have hslice := c11_weighted_caloric_truncated_power_slice_bounds_product
    hκ hR hab η hη hηc hηs T₀ D₀ hT₀ htbound hdbound hp hε
  have henergy := c11_weighted_caloric_truncated_power_cutoff_energy_bounds_product
    hκ hR hab η hη hηc hηs T₀ D₀ hT₀ htbound hdbound hp hε
  intro ρ α hell u G hcal hpos
  let μ := volume.restrict (Set.Ioo a b ×ˢ sourceBall (0 : Vec d) R)
  have hOpen : IsOpen (sourceBall (0 : Vec d) R) := by
    have hsum : Continuous (fun v : Vec d => ∑ j, v j * v j) :=
      continuous_finsetSum Finset.univ fun j _ => (continuous_apply j).mul (continuous_apply j)
    have hn : Continuous (fun v : Vec d => euclideanNorm v) := by
      unfold euclideanNorm euclideanSq dot
      exact Real.continuous_sqrt.comp hsum
    exact isOpen_lt (hn.comp (continuous_id.sub continuous_const)) continuous_const
  apply hgain ρ α hell (Set.Ioo a b) (sourceBall 0 R) measurableSet_Ioo
    hOpen hfinite u G hcal η hη hηc htest K hK hKU hzero
    S hS hSV (ae_restrict_of_ae_restrict_of_subset hSV hpos) hηone p ε hp hε
    (A * ∫⁻ z in Set.Ioo a b ×ˢ sourceBall 0 R, ENNReal.ofReal (u z + ε) ^ p)
    (E * ∫⁻ z in Set.Ioo a b ×ˢ sourceBall 0 R, ENNReal.ofReal (u z + ε) ^ p)
    (fun n => hslice ρ α hell u G hcal hpos n)
  intro n
  let F := PDE.Parabolic.LocalMax.powG p ε n
  let V : ℝ × Vec d → Vec d := fun z =>
    η z • (deriv F (u z) • G z) + F (u z) •
      (fun j => fderiv ℝ η z (0, unitVector j))
  have hF : ContDiff ℝ 1 F := PDE.Parabolic.LocalMax.powG_contDiff hε (Nat.cast_nonneg n)
  have hηd : Continuous (fun z => fun j => fderiv ℝ η z (0, unitVector j)) :=
    continuous_pi fun j => (hη.continuous_fderiv (by simp)).clm_apply continuous_const
  have hV : AEStronglyMeasurable V μ :=
    (hη.continuous.aestronglyMeasurable.smul
      ((hF.continuous_deriv_one.comp_aestronglyMeasurable hcal.1.aestronglyMeasurable).smul hcal.2.1)).add
      ((hF.continuous.comp_aestronglyMeasurable hcal.1.aestronglyMeasurable).smul hηd.aestronglyMeasurable)
  have hfub := c11_weighted_coefficient_energy_lintegral_prod hell V hV
  rw [← hfub]
  exact henergy ρ α hell u G hcal hpos n




/-- Each spatial slice of the nested cutoff is a compact test on the outer ball. -/
theorem c11_compact_cylinder_cutoff_spatial_test {d : ℕ} {r R T T' b h : ℝ}
    (hr : 0 ≤ r) (hrR : r < R) (t : ℝ) :
    let θ : ℝ → ℝ := fun s =>
      PDE.Parabolic.LocalMax.cylTimeRamp T ((T' - T) / 2) s *
        PDE.Parabolic.LocalMax.timeRamp b h s
    let ξ : Vec d → ℝ := PDE.canonicalBallCutoff (0 : Vec d) r R
    IsSpatialTest (sourceBall 0 R) (fun x => θ t * ξ x) := by
  dsimp only
  have hball : sourceBall (0 : Vec d) R = PDE.euclideanBall 0 R := by
    ext x
    rw [PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt (lt_of_le_of_lt hr hrR)]
    rfl
  refine ⟨contDiff_const.mul (PDE.canonicalBallCutoff_smooth 0 hr hrR),
    (PDE.canonicalBallCutoff_hasCompactSupport hr hrR).mul_left, ?_⟩
  rw [hball]
  exact tsupport_mul_subset_right.trans (PDE.canonicalBallCutoff_tsupport_subset_outer hr hrR)


/-- One compact spatial set supports every slice of a nested cutoff. -/
theorem c11_compact_cylinder_cutoff_spatial_support {d : ℕ} {r R T T' b h : ℝ}
    (hr : 0 ≤ r) (hrR : r < R) :
    let θ : ℝ → ℝ := fun s =>
      PDE.Parabolic.LocalMax.cylTimeRamp T ((T' - T) / 2) s *
        PDE.Parabolic.LocalMax.timeRamp b h s
    let ξ : Vec d → ℝ := PDE.canonicalBallCutoff (0 : Vec d) r R
    IsCompact (tsupport ξ) ∧ tsupport ξ ⊆ sourceBall 0 R ∧
      ∀ t x, x ∉ tsupport ξ → θ t * ξ x = 0 := by
  dsimp only
  have hball : sourceBall (0 : Vec d) R = PDE.euclideanBall 0 R := by
    ext x
    rw [PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt (lt_of_le_of_lt hr hrR)]
    rfl
  refine ⟨PDE.canonicalBallCutoff_hasCompactSupport hr hrR, ?_, ?_⟩
  · rw [hball]
    exact PDE.canonicalBallCutoff_tsupport_subset_outer hr hrR
  · intro t x hx
    have hz : PDE.canonicalBallCutoff (0 : Vec d) r R x = 0 := by
      by_contra hn
      exact hx (subset_tsupport _ hn)
    simp [hz]

/-- Weighted caloricity restricts to any smaller spatial domain. -/
theorem c11_weighted_caloric_spatial_mono {d : ℕ} {ρ : PDE.Vec d → ℝ}
    {α : PDE.Vec d → EinsteinRelation.Mat d} {I : Set ℝ}
    {U V : Set (PDE.Vec d)} (hI : MeasurableSet I) (hU : MeasurableSet U)
    (hVU : V ⊆ U) {u : ℝ × PDE.Vec d → ℝ} {G : ℝ × PDE.Vec d → PDE.Vec d}
    (hu : IsWeightedCaloric ρ α I U u G) : IsWeightedCaloric ρ α I V u G := by
  have hsub : I ×ˢ V ⊆ I ×ˢ U := Set.prod_mono Set.Subset.rfl hVU
  have hmeasure := Measure.restrict_mono_set (volume : Measure (ℝ × PDE.Vec d)) hsub
  refine ⟨hu.1.mono_measure hmeasure, hu.2.1.mono_measure hmeasure,
    hu.2.2.1.mono_measure hmeasure, ?_, ?_⟩
  · filter_upwards [hu.2.2.2.1] with t ht
    exact EinsteinRelation.Correctors.hasWeakGradient_mono hVU ht
  · intro ψ hψ hc hs
    have hs' : tsupport ψ ⊆ interior I ×ˢ U := hs.trans (Set.prod_mono Set.Subset.rfl hVU)
    have hz (z : ℝ × PDE.Vec d) (hz : z ∈ (I ×ˢ U) \ (I ×ˢ V)) :
        fderiv ℝ ψ z = 0 := by
      apply fderiv_of_notMem_tsupport ℝ
      intro hz'
      have hh := hs hz'
      exact hz.2 ⟨interior_subset hh.1, hh.2⟩
    have heq : (∫ z in I ×ˢ U, -(ρ z.2 * u z) * fderiv ℝ ψ z (1, 0) +
        dot ((α z.2).mulVec (G z)) (fun j => fderiv ℝ ψ z (0, unitVector j))) =
      ∫ z in I ×ˢ V, -(ρ z.2 * u z) * fderiv ℝ ψ z (1, 0) +
        dot ((α z.2).mulVec (G z)) (fun j => fderiv ℝ ψ z (0, unitVector j)) := by
      apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (hI.prod hU) hsub
      intro z hz'
      simp [hz z hz', dot]
    rw [← heq]
    exact hu.2.2.2.2 ψ hψ hc hs'

/-- Weighted caloricity restricts to nested spacetime cylinders. -/
theorem c11_weighted_caloric_cylinder_mono {d : ℕ} {ρ : Vec d → ℝ}
    {α : Vec d → Mat d} {I J : Set ℝ} {U V : Set (Vec d)}
    (hI : MeasurableSet I) (hJ : MeasurableSet J) (hU : MeasurableSet U)
    (hJI : J ⊆ I) (hVU : V ⊆ U)
    {u : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    (hu : IsWeightedCaloric ρ α I U u G) : IsWeightedCaloric ρ α J V u G := by
  exact c11_weighted_caloric_spatial_mono hJ hU hVU
    (c5_weighted_caloric_time_mono hI hU hJI hu)

/-- The compact nested cutoff meets the gain theorem's domain and support conditions. -/
theorem c11_nested_cutoff_ready {d : ℕ} {r R a T T' b B h : ℝ}
    (hr : 0 < r) (hrR : r < R) (haT : a < T) (hTT' : T < T')
    (hbB : b < B) (hh : 0 < h) :
    let θ : ℝ → ℝ := fun t =>
      PDE.Parabolic.LocalMax.cylTimeRamp T ((T' - T) / 2) t *
        PDE.Parabolic.LocalMax.timeRamp b h t
    let ξ : Vec d → ℝ := PDE.canonicalBallCutoff (0 : Vec d) r R
    let η : ℝ × Vec d → ℝ := fun z => θ z.1 * ξ z.2
    ContDiff ℝ (⊤ : ℕ∞) η ∧ HasCompactSupport η ∧
    tsupport η ⊆ Set.Ioo a B ×ˢ sourceBall 0 R ∧
    (∀ t, IsSpatialTest (sourceBall 0 R) (fun x => η (t, x))) ∧
    IsCompact (tsupport ξ) ∧ tsupport ξ ⊆ sourceBall 0 R ∧
    (∀ t x, x ∉ tsupport ξ → η (t, x) = 0) ∧
    (∀ z ∈ Set.Ioo T' (b - h) ×ˢ sourceBall (0 : Vec d) r, η z = 1) := by
  dsimp only
  obtain ⟨hs, hc, hsupport, hξ, _hbounds, hone⟩ :=
    c11_compact_cylinder_cutoff (d := d) hr.le hrR hTT' hh
  obtain ⟨hK, hKU, hzero⟩ :=
    c11_compact_cylinder_cutoff_spatial_support (d := d) (T := T) (T' := T')
      (b := b) (h := h) hr.le hrR
  have hballR : sourceBall (0 : Vec d) R = PDE.euclideanBall 0 R := by
    ext x
    rw [PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt (lt_trans hr hrR)]
    rfl
  have hballr : sourceBall (0 : Vec d) r = PDE.euclideanBall 0 r := by
    ext x
    rw [PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt hr]
    rfl
  refine ⟨hs, hc, ?_, ?_, hK, hKU, hzero, ?_⟩
  · apply hsupport.trans
    apply Set.prod_mono
    · intro t ht
      exact ⟨lt_of_lt_of_le haT ht.1, lt_of_le_of_lt ht.2 hbB⟩
    · rw [hballR]
      exact hξ
  · intro t
    exact c11_compact_cylinder_cutoff_spatial_test (T := T) (T' := T')
      (b := b) (h := h) hr.le hrR t
  · intro z hz
    apply hone z hz.1.1.le hz.1.2.le
    simpa only [hballr] using hz.2

/-- Uniform energy coefficient when both cutoff errors share a bound. -/
theorem c11_moser_energy_coefficient_common_bound (d : ℕ) (hd : 0 < d)
    {κ p T D L : ℝ} (hκ : 0 < κ) (hT : 0 ≤ T)
    (hp : ((d : ℝ) + 1) / d ≤ p) (hTL : T ≤ L) (hDL : D ^ 2 ≤ L) :
    2 * κ⁻¹ * T + 2 * κ⁻¹ * (2 + p / (p - 1)) * D ^ 2 ≤
      (2 * κ⁻¹ * ((d : ℝ) + 4)) * L := by
  calc
    _ ≤ 2 * κ⁻¹ * T + 2 * κ⁻¹ * ((d : ℝ) + 3) * D ^ 2 :=
      c11_moser_energy_coefficient_le d hd hκ hT hp
    _ ≤ 2 * κ⁻¹ * L + 2 * κ⁻¹ * ((d : ℝ) + 3) * L := by
      gcongr
    _ = _ := by ring

/-- The gradient-side coefficient grows linearly with the common cutoff bound. -/
theorem c11_moser_gradient_coefficient_common_bound (d : ℕ) (hd : 0 < d)
    {κ p T D L : ℝ} (hκ : 0 < κ) (hT : 0 ≤ T)
    (hp : ((d : ℝ) + 1) / d ≤ p) (hTL : T ≤ L) (hDL : D ^ 2 ≤ L) :
    2 * κ⁻¹ * (2 + p / (p - 1)) *
      ((2 / κ) * (2 * κ⁻¹ * T + 2 * κ⁻¹ * (2 + p / (p - 1)) * D ^ 2) + D ^ 2) ≤
    (2 * κ⁻¹ * ((d : ℝ) + 3) * ((2 / κ) * (2 * κ⁻¹ * ((d : ℝ) + 4)) + 1)) * L := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hp1 : 1 < p := by
    have : 1 < ((d : ℝ) + 1) / d := by rw [lt_div_iff₀ hd0]; linarith
    linarith
  have hc := c11_moser_power_coefficient_le d hd hp
  have hB := c11_moser_energy_coefficient_common_bound d hd hκ hT hp hTL hDL
  have hL : 0 ≤ L := (sq_nonneg D).trans hDL
  have hc0 : 0 ≤ 2 + p / (p - 1) := by positivity
  have hB0 : 0 ≤ 2 * κ⁻¹ * T + 2 * κ⁻¹ * (2 + p / (p - 1)) * D ^ 2 := by positivity
  calc
    _ ≤ 2 * κ⁻¹ * ((d : ℝ) + 3) *
       ((2 / κ) * ((2 * κ⁻¹ * ((d : ℝ) + 4)) * L) + L) := by
      gcongr
    _ = _ := by ring


/-- Exact spatial and temporal gaps for the dyadic Moser cylinders. -/
theorem c11_moser_dyadic_gaps (n : ℕ) :
    let z : ℝ := (2 : ℝ) ^ n
    let z' : ℝ := (2 : ℝ) ^ (n + 1)
    0 < z ∧
    ((1 / 2 + 1 / (2 * z)) - (1 / 2 + 1 / (2 * z'))) = 1 / (4 * z) ∧
    ((-(1 / 4) - 3 / (4 * z')) - (-(1 / 4) - 3 / (4 * z))) = 3 / (8 * z) ∧
    ((1 / 4 + 3 / (4 * z)) - (1 / 4 + 3 / (4 * z'))) = 3 / (8 * z) := by
  dsimp only
  have hn : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  refine ⟨hn, ?_, ?_, ?_⟩ <;> rw [pow_succ] <;> field_simp [ne_of_gt hn] <;> ring


/-- Positivity and the derivative-energy inequality for the negative quadratic branch. -/
theorem c11_negative_power_quadratic (p t : ℝ) (hp : 2 ≤ p) :
    0 ≤ 1 - p * t + p * (p - 1) / 2 * t ^ 2 ∧
    (p - p * (p - 1) * t) ^ 2 ≤
      2 * (p * (p - 1)) * (1 - p * t + p * (p - 1) / 2 * t ^ 2) ∧
    (1 - p * t / 2) ^ 2 ≤ 2 * (1 - p * t + p * (p - 1) / 2 * t ^ 2) := by
  have hp0 : 0 ≤ p := by linarith
  have hp2 : 0 ≤ p - 2 := by linarith
  have hp1 : 0 < 2 * (p - 1) := by linarith
  have hs : 0 ≤ p * (((p - 1) * t - 1) ^ 2) + (p - 2) :=
    add_nonneg (mul_nonneg hp0 (sq_nonneg _)) hp2
  have heq : 2 * (p - 1) * (1 - p * t + p * (p - 1) / 2 * t ^ 2) =
      p * (((p - 1) * t - 1) ^ 2) + (p - 2) := by ring
  refine ⟨?_, ?_, ?_⟩
  · by_contra hn
    have hneg : 1 - p * t + p * (p - 1) / 2 * t ^ 2 < 0 := lt_of_not_ge hn
    have := mul_neg_of_pos_of_neg hp1 hneg
    linarith [heq]
  · nlinarith [mul_nonneg hp0 hp2]
  · nlinarith [mul_nonneg (mul_nonneg hp0 hp2) (sq_nonneg t)]

/-- The dyadic cylinder gaps give a common geometric bound for both cutoff errors. -/
theorem c11_moser_dyadic_cutoff_bounds (B Q : ℝ) (hB : 0 ≤ B) (hQ : 0 ≤ Q)
    (n : ℕ) :
    let z : ℝ := (2 : ℝ) ^ n
    2 * B / (3 / (16 * z)) + Q / (3 / (16 * z)) ≤
      ((32 * B + 16 * Q) / 3 + 16384) * (4 : ℝ) ^ n ∧
    (32 / (1 / (4 * z))) ^ 2 ≤
      ((32 * B + 16 * Q) / 3 + 16384) * (4 : ℝ) ^ n := by
  dsimp only
  have hz : 1 ≤ (2 : ℝ) ^ n := one_le_pow₀ (by norm_num)
  have hzpos : 0 < (2 : ℝ) ^ n := lt_of_lt_of_le zero_lt_one hz
  have hpow : (4 : ℝ) ^ n = ((2 : ℝ) ^ n) ^ 2 := by
    calc
      (4 : ℝ) ^ n = ((2 : ℝ) ^ 2) ^ n := by norm_num
      _ = ((2 : ℝ) ^ n) ^ 2 := by rw [← pow_mul, ← pow_mul, Nat.mul_comm 2 n]
  rw [hpow]
  constructor
  · have hbase : 0 ≤ (32 * B + 16 * Q) / 3 := by positivity
    have hlinear : (2 : ℝ) ^ n ≤ ((2 : ℝ) ^ n) ^ 2 := by nlinarith
    have hmul := mul_le_mul_of_nonneg_left hlinear hbase
    field_simp
    nlinarith [sq_nonneg ((2 : ℝ) ^ n)]
  · field_simp
    have hbase : 0 ≤ (32 * B + 16 * Q) / 3 := by positivity
    nlinarith [mul_nonneg hbase (sq_nonneg ((2 : ℝ) ^ n))]

/-- The Moser exponents stay in the uniform coefficient range and increase geometrically. -/
theorem c11_moser_exponents_lower_bound {d : ℕ} (hd : 2 ≤ d) (n : ℕ) :
    let q : ℝ := ((d : ℝ) + 2) / d
    1 < q ∧ ((d : ℝ) + 1) / d ≤ 2 * q ^ n := by
  dsimp only
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
  have hq : 1 < ((d : ℝ) + 2) / d := by
    rw [lt_div_iff₀ hd0]
    linarith
  have hpow : 1 ≤ (((d : ℝ) + 2) / d) ^ n := one_le_pow₀ hq.le
  refine ⟨hq, ?_⟩
  have hbase : ((d : ℝ) + 1) / d ≤ 2 := by
    rw [div_le_iff₀ hd0]
    linarith
  linarith


/-- A geometric recurrence for finite norms gives a uniform essential bound. -/
@[nolint unusedArguments]
theorem c11_moser_iteration_essential_bound
    {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    (u : X → ℝ) (hu : AEStronglyMeasurable u μ)
    (A b c p : ℝ) (hA : 1 ≤ A) (hb : 1 < b) (hc : 1 < c) (hp : 0 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ Y : ℕ → ℝ, (∀ n, 0 ≤ Y n) →
      (∀ n, Y (n + 1) ≤ Real.rpow (A * Real.rpow b (n : ℝ))
        (1 / (p * Real.rpow c (n : ℝ))) * Y n) →
      (∀ n, eLpNorm u (ENNReal.ofReal (p * c ^ n)) μ ≤ ENNReal.ofReal (Y n)) →
      eLpNorm u ⊤ μ ≤ ENNReal.ofReal (C * Y 0) := by
  obtain ⟨C, hC, hiter⟩ := c17_moser_geometric_iteration_bound A b c p hA hb hc hp
  refine ⟨C, hC, ?_⟩
  intro Y hY hstep hnorm
  apply c13_moser_powers_essential_bound μ u hu p c (C * Y 0) hp hc
    (mul_nonneg hC.le (hY 0))
  intro n
  exact (hnorm n).trans (ENNReal.ofReal_le_ofReal (hiter Y hY hstep n))

/-- Dyadic cylinders meet the strict cutoff support conditions. -/
theorem c11_moser_dyadic_cylinder_geometry (n : ℕ) :
    let z : ℝ := (2 : ℝ) ^ n
    let R : ℝ := 1 / 2 + 1 / (2 * z)
    let r : ℝ := 1 / 2 + 1 / (4 * z)
    let a : ℝ := -(1 / 4) - 3 / (4 * z)
    let a' : ℝ := -(1 / 4) - 3 / (8 * z)
    let b : ℝ := 1 / 4 + 3 / (4 * z)
    let b' : ℝ := 1 / 4 + 3 / (8 * z)
    let T : ℝ := (a + a') / 2
    let B : ℝ := (b + b') / 2
    let h : ℝ := (b - b') / 2
    0 < r ∧ r < R ∧ a < T ∧ T < a' ∧ B < b ∧ 0 < h ∧ B - h = b' := by
  dsimp only
  have hz : 0 < (2 : ℝ) ^ n := by positivity
  have hz0 : (2 : ℝ) ^ n ≠ 0 := ne_of_gt hz
  have hi : 0 < ((2 : ℝ) ^ n)⁻¹ := inv_pos.mpr hz
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [div_eq_mul_inv, mul_inv_rev] <;> norm_num <;> nlinarith

/-- The explicit dyadic cutoff is admissible for the nested gain estimate. -/
theorem c11_moser_dyadic_cutoff_ready (d n : ℕ) :
    let z : ℝ := (2 : ℝ) ^ n
    let R : ℝ := 1 / 2 + 1 / (2 * z)
    let r : ℝ := 1 / 2 + 1 / (4 * z)
    let a : ℝ := -(1 / 4) - 3 / (4 * z)
    let a' : ℝ := -(1 / 4) - 3 / (8 * z)
    let b : ℝ := 1 / 4 + 3 / (4 * z)
    let b' : ℝ := 1 / 4 + 3 / (8 * z)
    let T : ℝ := (a + a') / 2
    let B : ℝ := (b + b') / 2
    let h : ℝ := (b - b') / 2
    let θ : ℝ → ℝ := fun t =>
      PDE.Parabolic.LocalMax.cylTimeRamp T ((a' - T) / 2) t *
        PDE.Parabolic.LocalMax.timeRamp B h t
    let ξ : Vec d → ℝ := PDE.canonicalBallCutoff (0 : Vec d) r R
    let η : ℝ × Vec d → ℝ := fun z => θ z.1 * ξ z.2
    ContDiff ℝ (⊤ : ℕ∞) η ∧ HasCompactSupport η ∧
    tsupport η ⊆ Set.Ioo a b ×ˢ sourceBall 0 R ∧
    (∀ t, IsSpatialTest (sourceBall 0 R) (fun x => η (t, x))) ∧
    IsCompact (tsupport ξ) ∧ tsupport ξ ⊆ sourceBall 0 R ∧
    (∀ t x, x ∉ tsupport ξ → η (t, x) = 0) ∧
    (∀ x ∈ Set.Ioo a' b' ×ˢ sourceBall (0 : Vec d) r, η x = 1) := by
  dsimp only
  obtain ⟨hr, hrR, haT, hTa, hBb, hh, hBh⟩ := c11_moser_dyadic_cylinder_geometry n
  have h := c11_nested_cutoff_ready (d := d) hr hrR haT hTa hBb hh
  rw [hBh] at h
  exact h

/-- The dyadic cutoffs have a common geometric bound on their time and spatial errors. -/
theorem c11_moser_dyadic_cutoff_derivative_bounds :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ (d n : ℕ),
    let z : ℝ := (2 : ℝ) ^ n
    let R : ℝ := 1 / 2 + 1 / (2 * z)
    let r : ℝ := 1 / 2 + 1 / (4 * z)
    let a : ℝ := -(1 / 4) - 3 / (4 * z)
    let a' : ℝ := -(1 / 4) - 3 / (8 * z)
    let b : ℝ := 1 / 4 + 3 / (4 * z)
    let b' : ℝ := 1 / 4 + 3 / (8 * z)
    let T : ℝ := (a + a') / 2
    let B : ℝ := (b + b') / 2
    let h : ℝ := (b - b') / 2
    let θ : ℝ → ℝ := fun t =>
      PDE.Parabolic.LocalMax.cylTimeRamp T ((a' - T) / 2) t *
        PDE.Parabolic.LocalMax.timeRamp B h t
    let ξ : Vec d → ℝ := PDE.canonicalBallCutoff (0 : Vec d) r R
    let η : ℝ × Vec d → ℝ := fun z => θ z.1 * ξ z.2
    (∀ x, |η x * fderiv ℝ η x (1, 0)| ≤ L * (4 : ℝ) ^ n) ∧
    (∀ x, euclideanSq (fun j => fderiv ℝ η x (0, unitVector j)) ≤
       (32 / (R - r)) ^ 2) ∧ (32 / (R - r)) ^ 2 ≤ L * (4 : ℝ) ^ n := by
  obtain ⟨K, hK0, hK⟩ := PDE.Parabolic.LocalMax.exists_abs_deriv_smoothTransition_le
  obtain ⟨Q, hQ0, hQ⟩ := c11_compact_cylinder_cutoff_gap_bounds
  let L : ℝ := (32 * K + 16 * Q) / 3 + 16384
  have hL : 0 ≤ L := by dsimp [L]; positivity
  refine ⟨L, hL, ?_⟩
  intro d n
  dsimp only
  let z : ℝ := (2 : ℝ) ^ n
  let R : ℝ := 1 / 2 + 1 / (2 * z)
  let r : ℝ := 1 / 2 + 1 / (4 * z)
  let a : ℝ := -(1 / 4) - 3 / (4 * z)
  let a' : ℝ := -(1 / 4) - 3 / (8 * z)
  let b : ℝ := 1 / 4 + 3 / (4 * z)
  let b' : ℝ := 1 / 4 + 3 / (8 * z)
  let T : ℝ := (a + a') / 2
  let B : ℝ := (b + b') / 2
  let h : ℝ := (b - b') / 2
  let θ : ℝ → ℝ := fun t => PDE.Parabolic.LocalMax.cylTimeRamp T ((a' - T) / 2) t *
    PDE.Parabolic.LocalMax.timeRamp B h t
  let ξ : Vec d → ℝ := PDE.canonicalBallCutoff (0 : Vec d) r R
  let η : ℝ × Vec d → ℝ := fun x => θ x.1 * ξ x.2
  change (∀ x, |η x * fderiv ℝ η x (1, 0)| ≤ L * (4 : ℝ) ^ n) ∧
    (∀ x, euclideanSq (fun j => fderiv ℝ η x (0, unitVector j)) ≤ (32 / (R - r)) ^ 2) ∧
      (32 / (R - r)) ^ 2 ≤ L * (4 : ℝ) ^ n
  have hgeo := c11_moser_dyadic_cylinder_geometry n
  change 0 < r ∧ r < R ∧ a < T ∧ T < a' ∧ B < b ∧ 0 < h ∧ B - h = b' at hgeo
  obtain ⟨hr, hrR, haT, hTa, hBb, hh, hBh⟩ := hgeo
  have hd := hQ (d := d) (r := r) (R := R) (T := T) (T' := a') (b := B) (h := h)
    hr.le hrR hTa hh hK
  change (∀ x, |fderiv ℝ η x (1, 0)| ≤ 2 * K / (a' - T) + Q / h) ∧
    (∀ x, euclideanSq (fun j => fderiv ℝ η x (0, unitVector j)) ≤ (32 / (R - r)) ^ 2) at hd
  have hη := (c11_compact_cylinder_cutoff (d := d) (b := B) hr.le hrR hTa hh).2.2.2.2.1
  change ∀ x, 0 ≤ η x ∧ η x ≤ 1 at hη
  have hg := c11_moser_dyadic_cutoff_bounds K Q hK0 hQ0 n
  change 2 * K / (3 / (16 * z)) + Q / (3 / (16 * z)) ≤ L * (4 : ℝ) ^ n ∧
    (32 / (1 / (4 * z))) ^ 2 ≤ L * (4 : ℝ) ^ n at hg
  have hz : z ≠ 0 := by dsimp [z]; positivity
  have htgap : a' - T = 3 / (16 * z) := by dsimp [a', T, a]; field_simp; ring
  have hhgap : h = 3 / (16 * z) := by dsimp [h, b, b']; field_simp; ring
  have hxgap : R - r = 1 / (4 * z) := by dsimp [R, r]; field_simp; ring
  rw [htgap, hhgap] at hd
  refine ⟨?_, hd.2, ?_⟩
  · intro x
    rw [abs_mul, abs_of_nonneg (hη x).1]
    calc
      _ ≤ |fderiv ℝ η x (1, 0)| := by
        nlinarith [mul_nonneg (sub_nonneg.mpr (hη x).2)
          (abs_nonneg (fderiv ℝ η x (1, 0)))]
      _ ≤ _ := hd.1 x
      _ ≤ _ := hg.1
  · rw [hxgap]
    exact hg.2

/-- Every dyadic cylinder lies between the unit and terminal cylinders. -/
theorem c11_moser_dyadic_cylinder_containment (d n : ℕ) :
    let z : ℝ := (2 : ℝ) ^ n
    let R : ℝ := 1 / 2 + 1 / (2 * z)
    let a : ℝ := -(1 / 4) - 3 / (4 * z)
    let b : ℝ := 1 / 4 + 3 / (4 * z)
    (Set.Ioo (-(1 / 4) : ℝ) (1 / 4) ×ˢ sourceBall (0 : Vec d) (1 / 2)) ⊆
      Set.Ioo a b ×ˢ sourceBall (0 : Vec d) R ∧
    (Set.Ioo a b ×ˢ sourceBall (0 : Vec d) R) ⊆
      Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall (0 : Vec d) 1 := by
  dsimp only
  have hz : 1 ≤ (2 : ℝ) ^ n := one_le_pow₀ (by norm_num)
  have hzpos : 0 < (2 : ℝ) ^ n := lt_of_lt_of_le zero_lt_one hz
  have hi : 0 < ((2 : ℝ) ^ n)⁻¹ := inv_pos.mpr hzpos
  have hi1 : ((2 : ℝ) ^ n)⁻¹ ≤ 1 := (inv_le_one₀ hzpos).2 hz
  have ha : (-1 : ℝ) ≤ -(1 / 4) - 3 / (4 * (2 : ℝ) ^ n) ∧
      -(1 / 4) - 3 / (4 * (2 : ℝ) ^ n) ≤ -(1 / 4) := by
    constructor <;> simp only [div_eq_mul_inv, mul_inv_rev] <;> norm_num <;> nlinarith
  have hb : (1 / 4 : ℝ) ≤ 1 / 4 + 3 / (4 * (2 : ℝ) ^ n) ∧
      1 / 4 + 3 / (4 * (2 : ℝ) ^ n) ≤ 1 := by
    constructor <;> simp only [div_eq_mul_inv, mul_inv_rev] <;> norm_num <;> nlinarith
  have hR : (1 / 2 : ℝ) ≤ 1 / 2 + 1 / (2 * (2 : ℝ) ^ n) ∧
      1 / 2 + 1 / (2 * (2 : ℝ) ^ n) ≤ 1 := by
    constructor <;> simp only [div_eq_mul_inv, mul_inv_rev] <;> norm_num <;> nlinarith
  constructor
  · intro x hx
    refine ⟨⟨lt_of_le_of_lt ha.2 hx.1.1, lt_of_lt_of_le hx.1.2 hb.1⟩, ?_⟩
    exact lt_of_lt_of_le hx.2 hR.1
  · intro x hx
    refine ⟨⟨lt_of_le_of_lt ha.1 hx.1.1, lt_of_lt_of_le hx.1.2 hb.2⟩, ?_⟩
    exact lt_of_lt_of_le hx.2 hR.2

/-- The uniform power gain applies to every pair of dyadic cylinders. -/
theorem c11_moser_dyadic_power_gain (d : ℕ) (hd : 2 ≤ d) (κ : ℝ) (hκ : 0 < κ) :
    ∃ (C : ℝ≥0∞) (L : ℝ), C ≠ ⊤ ∧ 0 ≤ L ∧ ∀ n : ℕ,
    let z : ℝ := (2 : ℝ) ^ n
    let R : ℝ := 1 / 2 + 1 / (2 * z)
    let r : ℝ := 1 / 2 + 1 / (4 * z)
    let a : ℝ := -(1 / 4) - 3 / (4 * z)
    let a' : ℝ := -(1 / 4) - 3 / (8 * z)
    let b : ℝ := 1 / 4 + 3 / (4 * z)
    let b' : ℝ := 1 / 4 + 3 / (8 * z)
    let D : ℝ := 32 / (R - r)
    let T : ℝ := L * (4 : ℝ) ^ n
    ∀ {p ε : ℝ}, 1 < p → 0 < ε →
    let B := 2 * κ⁻¹ * T + 2 * κ⁻¹ * (2 + p / (p - 1)) * D ^ 2
    let A := ENNReal.ofReal (2 + p / (p - 1)) * ENNReal.ofReal B
    let E := ENNReal.ofReal (2 * κ⁻¹ * (2 + p / (p - 1))) *
      (ENNReal.ofReal (2 / κ) * ENNReal.ofReal B + ENNReal.ofReal (D ^ 2))
    ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d), IsUniformlyElliptic κ ρ α →
    ∀ (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d),
    IsWeightedCaloric ρ α (Set.Ioo a b) (sourceBall 0 R) u G →
    (∀ᵐ x ∂volume.restrict (Set.Ioo a b ×ˢ sourceBall 0 R), 0 ≤ u x) →
    (∫⁻ x in Set.Ioo a' b' ×ˢ sourceBall (0 : Vec d) r,
      ENNReal.ofReal (u x + ε) ^ (p * (((d : ℝ) + 2) / d))) ≤
      ENNReal.ofReal κ⁻¹ * (C *
        (A * (∫⁻ x in Set.Ioo a b ×ˢ sourceBall 0 R, ENNReal.ofReal (u x + ε) ^ p)) ^
          (2 / (d : ℝ)) *
        (E * (∫⁻ x in Set.Ioo a b ×ˢ sourceBall 0 R, ENNReal.ofReal (u x + ε) ^ p))) := by
  obtain ⟨C, hC, hgain⟩ := c11_weighted_caloric_power_gain_of_energy_product_uniform d hd κ hκ
  obtain ⟨L, hL, hder⟩ := c11_moser_dyadic_cutoff_derivative_bounds
  refine ⟨C, L, hC, hL, ?_⟩
  intro n
  dsimp only
  let z : ℝ := (2 : ℝ) ^ n
  let R : ℝ := 1 / 2 + 1 / (2 * z)
  let r : ℝ := 1 / 2 + 1 / (4 * z)
  let a : ℝ := -(1 / 4) - 3 / (4 * z)
  let a' : ℝ := -(1 / 4) - 3 / (8 * z)
  let b : ℝ := 1 / 4 + 3 / (4 * z)
  let b' : ℝ := 1 / 4 + 3 / (8 * z)
  let T : ℝ := (a + a') / 2
  let B : ℝ := (b + b') / 2
  let h : ℝ := (b - b') / 2
  let θ : ℝ → ℝ := fun t => PDE.Parabolic.LocalMax.cylTimeRamp T ((a' - T) / 2) t *
    PDE.Parabolic.LocalMax.timeRamp B h t
  let ξ : Vec d → ℝ := PDE.canonicalBallCutoff (0 : Vec d) r R
  let η : ℝ × Vec d → ℝ := fun x => θ x.1 * ξ x.2
  have hgeo := c11_moser_dyadic_cylinder_geometry n
  change 0 < r ∧ r < R ∧ a < T ∧ T < a' ∧ B < b ∧ 0 < h ∧ B - h = b' at hgeo
  obtain ⟨hr, hrR, haT, hTa, hBb, hh, hBh⟩ := hgeo
  have hready := c11_moser_dyadic_cutoff_ready d n
  change ContDiff ℝ (⊤ : ℕ∞) η ∧ HasCompactSupport η ∧
    tsupport η ⊆ Set.Ioo a b ×ˢ sourceBall 0 R ∧
    (∀ t, IsSpatialTest (sourceBall 0 R) (fun x => η (t, x))) ∧
    IsCompact (tsupport ξ) ∧ tsupport ξ ⊆ sourceBall 0 R ∧
    (∀ t x, x ∉ tsupport ξ → η (t, x) = 0) ∧
    (∀ x ∈ Set.Ioo a' b' ×ˢ sourceBall (0 : Vec d) r, η x = 1) at hready
  obtain ⟨hη, hηc, hηs, htest, hK, hKU, hzero, hone⟩ := hready
  have hbounds := hder d n
  change (∀ x, |η x * fderiv ℝ η x (1, 0)| ≤ L * (4 : ℝ) ^ n) ∧
    (∀ x, euclideanSq (fun j => fderiv ℝ η x (0, unitVector j)) ≤ (32 / (R - r)) ^ 2) ∧
      (32 / (R - r)) ^ 2 ≤ L * (4 : ℝ) ^ n at hbounds
  have hOpen : IsOpen (sourceBall (0 : Vec d) r) := by
    have hsum : Continuous (fun v : Vec d => ∑ j, v j * v j) :=
      continuous_finsetSum Finset.univ fun j _ => (continuous_apply j).mul (continuous_apply j)
    have hn : Continuous (fun v : Vec d => euclideanNorm v) := by
      unfold euclideanNorm euclideanSq dot
      exact Real.continuous_sqrt.comp hsum
    exact isOpen_lt (hn.comp (continuous_id.sub continuous_const)) continuous_const
  have hS : MeasurableSet (Set.Ioo a' b' ×ˢ sourceBall (0 : Vec d) r) :=
    measurableSet_Ioo.prod hOpen.measurableSet
  have hsub : Set.Ioo a' b' ×ˢ sourceBall (0 : Vec d) r ⊆
      Set.Ioo a b ×ˢ sourceBall 0 R := by
    intro x hx
    apply hηs
    apply subset_tsupport η
    change η x ≠ 0
    rw [hone x hx]
    norm_num
  have hab : a < b := by
    have hz : 0 < (2 : ℝ) ^ n := by positivity
    have hi : 0 < ((2 : ℝ) ^ n)⁻¹ := inv_pos.mpr hz
    dsimp [a, b, z]
    simp only [div_eq_mul_inv, mul_inv_rev]
    norm_num
    nlinarith
  haveI := c20_sourceCylinder_isFiniteMeasure a b R (0 : Vec d)
  have hfinite : volume (Set.Ioo a b ×ˢ sourceBall (0 : Vec d) R) < ∞ := by
    simpa using (measure_lt_top (volume.restrict (Set.Ioo a b ×ˢ sourceBall (0 : Vec d) R)) Set.univ)
  intro p ε hp hε
  exact hgain (lt_trans hr hrR) hab hfinite η hη hηc hηs
    (L * (4 : ℝ) ^ n) (32 / (R - r)) (by positivity) hbounds.1 hbounds.2.1
    (Filter.Eventually.of_forall htest) (tsupport ξ) hK hKU hzero
    _ hS hsub hone hp hε

/-- The slice-side coefficient also grows linearly with the common cutoff bound. -/
theorem c11_moser_slice_coefficient_common_bound (d : ℕ) (hd : 0 < d)
    {κ p T D L : ℝ} (hκ : 0 < κ) (hT : 0 ≤ T)
    (hp : ((d : ℝ) + 1) / d ≤ p) (hTL : T ≤ L) (hDL : D ^ 2 ≤ L) :
    (2 + p / (p - 1)) *
      (2 * κ⁻¹ * T + 2 * κ⁻¹ * (2 + p / (p - 1)) * D ^ 2) ≤
    (((d : ℝ) + 3) * (2 * κ⁻¹ * ((d : ℝ) + 4))) * L := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hp1 : 1 < p := by
    have : 1 < ((d : ℝ) + 1) / d := by rw [lt_div_iff₀ hd0]; linarith
    linarith
  have hc := c11_moser_power_coefficient_le d hd hp
  have hB := c11_moser_energy_coefficient_common_bound d hd hκ hT hp hTL hDL
  have hL : 0 ≤ L := (sq_nonneg D).trans hDL
  have hc0 : 0 ≤ 2 + p / (p - 1) := by positivity
  have hB0 : 0 ≤ 2 * κ⁻¹ * T + 2 * κ⁻¹ * (2 + p / (p - 1)) * D ^ 2 := by positivity
  calc
    _ ≤ ((d : ℝ) + 3) * ((2 * κ⁻¹ * ((d : ℝ) + 4)) * L) := by gcongr
    _ = _ := by ring

/-- Both ENNReal gain coefficients admit linear bounds in the common cutoff error. -/
theorem c11_moser_ennreal_coefficient_common_bounds (d : ℕ) (hd : 0 < d)
    {κ p T D L : ℝ} (hκ : 0 < κ) (hT : 0 ≤ T)
    (hp : ((d : ℝ) + 1) / d ≤ p) (hTL : T ≤ L) (hDL : D ^ 2 ≤ L) :
    let B := 2 * κ⁻¹ * T + 2 * κ⁻¹ * (2 + p / (p - 1)) * D ^ 2
    ENNReal.ofReal (2 + p / (p - 1)) * ENNReal.ofReal B ≤
      ENNReal.ofReal ((((d : ℝ) + 3) * (2 * κ⁻¹ * ((d : ℝ) + 4))) * L) ∧
    ENNReal.ofReal (2 * κ⁻¹ * (2 + p / (p - 1))) *
      (ENNReal.ofReal (2 / κ) * ENNReal.ofReal B + ENNReal.ofReal (D ^ 2)) ≤
      ENNReal.ofReal ((2 * κ⁻¹ * ((d : ℝ) + 3) *
        ((2 / κ) * (2 * κ⁻¹ * ((d : ℝ) + 4)) + 1)) * L) := by
  dsimp only
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hp1 : 1 < p := by
    have : 1 < ((d : ℝ) + 1) / d := by rw [lt_div_iff₀ hd0]; linarith
    linarith
  have hc0 : 0 ≤ 2 + p / (p - 1) := by positivity
  have hB0 : 0 ≤ 2 * κ⁻¹ * T + 2 * κ⁻¹ * (2 + p / (p - 1)) * D ^ 2 := by positivity
  constructor
  · rw [← ENNReal.ofReal_mul hc0]
    exact ENNReal.ofReal_le_ofReal
      (c11_moser_slice_coefficient_common_bound d hd hκ hT hp hTL hDL)
  · rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 2 / κ),
      ← ENNReal.ofReal_add (by positivity : 0 ≤ (2 / κ) *
        (2 * κ⁻¹ * T + 2 * κ⁻¹ * (2 + p / (p - 1)) * D ^ 2)) (sq_nonneg D),
      ← ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * κ⁻¹ * (2 + p / (p - 1)))]
    exact ENNReal.ofReal_le_ofReal
      (c11_moser_gradient_coefficient_common_bound d hd hκ hT hp hTL hDL)

/-- The inner cylinder of each cutoff is the next dyadic cylinder. -/
theorem c11_moser_dyadic_cylinder_succ (d n : ℕ) :
    let z : ℝ := (2 : ℝ) ^ n
    let z' : ℝ := (2 : ℝ) ^ (n + 1)
    (Set.Ioo (-(1 / 4) - 3 / (8 * z) : ℝ) (1 / 4 + 3 / (8 * z)) ×ˢ
      sourceBall (0 : Vec d) (1 / 2 + 1 / (4 * z))) =
    (Set.Ioo (-(1 / 4) - 3 / (4 * z') : ℝ) (1 / 4 + 3 / (4 * z')) ×ˢ
      sourceBall (0 : Vec d) (1 / 2 + 1 / (2 * z'))) := by
  dsimp only
  rw [pow_succ]
  have hz : (2 : ℝ) ^ n ≠ 0 := by positivity
  congr 2 <;> field_simp <;> ring

/-- A geometric recurrence for finite cylinder norms gives an essential bound on
an inner cylinder, provided its finite-exponent norms are dominated by the
corresponding cylinder norms. -/
@[nolint unusedArguments]
theorem c11_moser_essential_bound_of_norm_recurrence
    {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    (ν : ℕ → Measure X) (u : X → ℝ) (hu : AEStronglyMeasurable u μ)
    (A b c p : ℝ) (hA : 1 ≤ A) (hb : 1 < b) (hc : 1 < c) (hp : 0 < p)
    (hfinite : ∀ n, eLpNorm u (ENNReal.ofReal (p * c ^ n)) (ν n) ≠ ⊤)
    (hinner : ∀ n, eLpNorm u (ENNReal.ofReal (p * c ^ n)) μ ≤
      eLpNorm u (ENNReal.ofReal (p * c ^ n)) (ν n))
    (hstep : ∀ n,
      (eLpNorm u (ENNReal.ofReal (p * c ^ (n + 1))) (ν (n + 1))).toReal ≤
        Real.rpow (A * Real.rpow b (n : ℝ))
          (1 / (p * Real.rpow c (n : ℝ))) *
        (eLpNorm u (ENNReal.ofReal (p * c ^ n)) (ν n)).toReal) :
    ∃ C : ℝ, 0 < C ∧ eLpNorm u ⊤ μ ≤
      ENNReal.ofReal C * eLpNorm u (ENNReal.ofReal p) (ν 0) := by
  obtain ⟨C, hC, hbound⟩ := c17_moser_geometric_iteration_bound A b c p hA hb hc hp
  refine ⟨C, hC, ?_⟩
  let Y : ℕ → ℝ := fun n => (eLpNorm u (ENNReal.ofReal (p * c ^ n)) (ν n)).toReal
  have hY : ∀ n, 0 ≤ Y n := fun n => ENNReal.toReal_nonneg
  have hiter : ∀ n, eLpNorm u (ENNReal.ofReal (p * c ^ n)) μ ≤
      ENNReal.ofReal (C * Y 0) := by
    intro n
    calc
      _ ≤ eLpNorm u (ENNReal.ofReal (p * c ^ n)) (ν n) := hinner n
      _ = ENNReal.ofReal (Y n) := (ENNReal.ofReal_toReal (hfinite n)).symm
      _ ≤ ENNReal.ofReal (C * Y 0) := ENNReal.ofReal_le_ofReal (hbound Y hY hstep n)
  have h := c13_moser_powers_essential_bound μ u hu p c (C * Y 0) hp hc
    (mul_nonneg hC.le (hY 0)) hiter
  calc
    eLpNorm u ⊤ μ ≤ ENNReal.ofReal (C * Y 0) := h
    _ = ENNReal.ofReal C * eLpNorm u (ENNReal.ofReal p) (ν 0) := by
      rw [ENNReal.ofReal_mul hC.le]
      have hzero : eLpNorm u (ENNReal.ofReal p) (ν 0) ≠ ⊤ := by
        simpa only [pow_zero, mul_one] using hfinite 0
      simp only [Y, pow_zero, mul_one, ENNReal.ofReal_toReal hzero]


/-- The Moser exponents, starting at two, stay above the coefficient threshold. -/
theorem c11_moser_geometric_exponent_threshold (d n : ℕ) (hd : 2 ≤ d) :
    ((d : ℝ) + 1) / d ≤ 2 * (((d : ℝ) + 2) / d) ^ n := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (by omega : 1 ≤ d)
  have hc : (1 : ℝ) ≤ ((d : ℝ) + 2) / d := by
    rw [le_div_iff₀ hd0]
    linarith
  have hn : (1 : ℝ) ≤ (((d : ℝ) + 2) / d) ^ n := one_le_pow₀ hc
  have ht : ((d : ℝ) + 1) / d ≤ 2 := by
    rw [div_le_iff₀ hd0]
    linarith
  nlinarith

/-- On the dyadic cylinders, both gain coefficients grow at most like four
to the cylinder index, uniformly over the Moser exponents. -/
theorem c11_moser_dyadic_coefficient_bounds (d : ℕ) (hd : 2 ≤ d)
    (κ L : ℝ) (hκ : 0 < κ) (hL : 0 ≤ L) (n : ℕ)
    (hD : (32 / ((1 / 2 + 1 / (2 * (2 : ℝ) ^ n)) -
      (1 / 2 + 1 / (4 * (2 : ℝ) ^ n)))) ^ 2 ≤ L * (4 : ℝ) ^ n) :
    let p : ℝ := 2 * (((d : ℝ) + 2) / d) ^ n
    let D : ℝ := 32 / ((1 / 2 + 1 / (2 * (2 : ℝ) ^ n)) -
      (1 / 2 + 1 / (4 * (2 : ℝ) ^ n)))
    let T : ℝ := L * (4 : ℝ) ^ n
    let B := 2 * κ⁻¹ * T + 2 * κ⁻¹ * (2 + p / (p - 1)) * D ^ 2
    ENNReal.ofReal (2 + p / (p - 1)) * ENNReal.ofReal B ≤
      ENNReal.ofReal ((((d : ℝ) + 3) * (2 * κ⁻¹ * ((d : ℝ) + 4))) * T) ∧
    ENNReal.ofReal (2 * κ⁻¹ * (2 + p / (p - 1))) *
      (ENNReal.ofReal (2 / κ) * ENNReal.ofReal B + ENNReal.ofReal (D ^ 2)) ≤
      ENNReal.ofReal ((2 * κ⁻¹ * ((d : ℝ) + 3) *
        ((2 / κ) * (2 * κ⁻¹ * ((d : ℝ) + 4)) + 1)) * T) := by
  dsimp only
  exact c11_moser_ennreal_coefficient_common_bounds d (by omega) hκ
    (mul_nonneg hL (by positivity)) (c11_moser_geometric_exponent_threshold d n hd)
    le_rfl hD


/-- The exponent ratio in the dyadic iteration is strictly larger than one,
and multiplication by it advances the exponent by one step. -/
theorem c11_moser_geometric_exponent_step (d n : ℕ) (hd : 0 < d) :
    1 < (((d : ℝ) + 2) / d) ∧
      (2 * (((d : ℝ) + 2) / d) ^ n) * (((d : ℝ) + 2) / d) =
        2 * (((d : ℝ) + 2) / d) ^ (n + 1) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  constructor
  · rw [lt_div_iff₀ hd0]
    linarith
  · rw [pow_succ]
    ring

/-- A uniform estimate for positive constant regularizations passes to the
unregularized nonnegative function. -/
theorem c11_moser_remove_positive_regularization
    {X : Type*} [MeasurableSpace X] (μ ν : Measure X) [IsFiniteMeasure ν]
    (u : X → ℝ) (huμ : AEStronglyMeasurable u μ)
    (huμ0 : ∀ᵐ x ∂μ, 0 ≤ u x) (huν0 : ∀ᵐ x ∂ν, 0 ≤ u x)
    (p C : ℝ) (hp : 0 < p) (huν : MemLp u (ENNReal.ofReal p) ν)
    (hregularized : ∀ ε : ℝ, 0 < ε →
      eLpNorm (fun x => u x + ε) ⊤ μ ≤
        ENNReal.ofReal C * eLpNorm (fun x => u x + ε) (ENNReal.ofReal p) ν) :
    eLpNorm u ⊤ μ ≤ ENNReal.ofReal C * eLpNorm u (ENNReal.ofReal p) ν := by
  let ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hε (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  have hε0 : Filter.Tendsto ε Filter.atTop (𝓝 0) := by
    simpa [ε] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have ht := c20_regularized_positive_eLpNorm_tendsto ν u huν0 p hp huν ε
    (fun n => (hε n).le) hε0
  have ht' : Filter.Tendsto (fun n => ENNReal.ofReal C *
      eLpNorm (fun x => u x + ε n) (ENNReal.ofReal p) ν) Filter.atTop
      (𝓝 (ENNReal.ofReal C * eLpNorm u (ENNReal.ofReal p) ν)) :=
    (ENNReal.continuous_const_mul ENNReal.ofReal_ne_top).tendsto _ |>.comp ht
  apply ge_of_tendsto ht'
  apply Filter.Eventually.of_forall
  intro n
  have hmono : eLpNorm u ⊤ μ ≤ eLpNorm (fun x => u x + ε n) ⊤ μ := by
    apply eLpNorm_mono_ae_real huμ
    filter_upwards [huμ0] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg hx]
    exact le_add_of_nonneg_right (hε n).le
  exact hmono.trans (hregularized (ε n) (hε n))

/-- Taking the correct root of a power-gain estimate isolates the input
moment at exponent `1 / p` and the gain coefficient at exponent
`1 / (p * (1 + s))`. -/
theorem c11_moser_power_gain_root (p s : ℝ) (hp : 0 < p) (hs : 0 ≤ s)
    (I J K A E : ℝ≥0∞)
    (hgain : J ≤ K * (A * I) ^ s * (E * I)) :
    J ^ (1 / (p * (1 + s))) ≤
      (K * A ^ s * E) ^ (1 / (p * (1 + s))) * I ^ (1 / p) := by
  have hs1 : 0 < 1 + s := by linarith
  have hr : 0 ≤ 1 / (p * (1 + s)) := by positivity
  have he : (s + 1) * (1 / (p * (1 + s))) = 1 / p := by
    field_simp
    <;> ring
  have hfactor : K * (A * I) ^ s * (E * I) =
      (K * A ^ s * E) * I ^ (s + 1) := by
    rw [ENNReal.mul_rpow_of_nonneg _ _ hs,
      ENNReal.rpow_add_of_nonneg _ _ hs (by norm_num), ENNReal.rpow_one]
    ac_rfl
  calc
    J ^ (1 / (p * (1 + s))) ≤
        (K * (A * I) ^ s * (E * I)) ^ (1 / (p * (1 + s))) :=
      ENNReal.rpow_le_rpow hgain hr
    _ = (K * A ^ s * E) ^ (1 / (p * (1 + s))) * I ^ (1 / p) := by
      rw [hfactor, ENNReal.mul_rpow_of_nonneg _ _ hr, ← ENNReal.rpow_mul, he]

/-- A moment gain yields the corresponding finite-exponent norm step. -/
theorem c11_moser_norm_step_of_moment_gain
    {X : Type*} [MeasurableSpace X] (μ ν : Measure X) (v : X → ℝ)
    (hvμ : AEStronglyMeasurable v μ) (hvν : AEStronglyMeasurable v ν)
    (p s : ℝ) (hp : 0 < p) (hs : 0 ≤ s) (K A E : ℝ≥0∞)
    (hgain : (∫⁻ x, ‖v x‖ₑ ^ (p * (1 + s)) ∂ν) ≤
      K * (A * (∫⁻ x, ‖v x‖ₑ ^ p ∂μ)) ^ s *
        (E * (∫⁻ x, ‖v x‖ₑ ^ p ∂μ))) :
    eLpNorm v (ENNReal.ofReal (p * (1 + s))) ν ≤
      (K * A ^ s * E) ^ (1 / (p * (1 + s))) *
        eLpNorm v (ENNReal.ofReal p) μ := by
  have hq : 0 < p * (1 + s) := by positivity
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
    (ENNReal.ofReal_pos.mpr hq).ne' ENNReal.ofReal_ne_top hvν,
    eLpNorm_eq_lintegral_rpow_enorm_toReal
    (ENNReal.ofReal_pos.mpr hp).ne' ENNReal.ofReal_ne_top hvμ,
    ENNReal.toReal_ofReal hq.le, ENNReal.toReal_ofReal hp.le]
  exact c11_moser_power_gain_root p s hp hs _ _ K A E hgain

/-- For nonnegative functions the positive moments appearing in the caloric
power gain are precisely the moments used by the norm step. -/
theorem c11_moser_norm_step_of_nonnegative_moment_gain
    {X : Type*} [MeasurableSpace X] (μ ν : Measure X) (v : X → ℝ)
    (hvμ : AEStronglyMeasurable v μ) (hvν : AEStronglyMeasurable v ν)
    (hvμ0 : ∀ᵐ x ∂μ, 0 ≤ v x) (hvν0 : ∀ᵐ x ∂ν, 0 ≤ v x)
    (p s : ℝ) (hp : 0 < p) (hs : 0 ≤ s) (K A E : ℝ≥0∞)
    (hgain : (∫⁻ x, ENNReal.ofReal (v x) ^ (p * (1 + s)) ∂ν) ≤
      K * (A * (∫⁻ x, ENNReal.ofReal (v x) ^ p ∂μ)) ^ s *
        (E * (∫⁻ x, ENNReal.ofReal (v x) ^ p ∂μ))) :
    eLpNorm v (ENNReal.ofReal (p * (1 + s))) ν ≤
      (K * A ^ s * E) ^ (1 / (p * (1 + s))) *
        eLpNorm v (ENNReal.ofReal p) μ := by
  apply c11_moser_norm_step_of_moment_gain μ ν v hvμ hvν p s hp hs K A E
  have hμ : (∫⁻ x, ‖v x‖ₑ ^ p ∂μ) =
      ∫⁻ x, ENNReal.ofReal (v x) ^ p ∂μ := by
    apply lintegral_congr_ae
    filter_upwards [hvμ0] with x hx
    rw [Real.enorm_eq_ofReal hx]
  have hν : (∫⁻ x, ‖v x‖ₑ ^ (p * (1 + s)) ∂ν) =
      ∫⁻ x, ENNReal.ofReal (v x) ^ (p * (1 + s)) ∂ν := by
    apply lintegral_congr_ae
    filter_upwards [hvν0] with x hx
    rw [Real.enorm_eq_ofReal hx]
  simpa only [hμ, hν] using hgain


/-- A signed dyadic norm recurrence on the actual cylinders yields a uniform
unit-scale essential bound. The recurrence and its finiteness remain explicit. -/
theorem c11_signed_unit_local_max_of_norm_recurrence
    (d : ℕ) (hd : 2 ≤ d) (A b : ℝ) (hA : 1 ≤ A) (hb : 1 < b) :
    let c : ℝ := ((d : ℝ) + 2) / d
    let μ := volume.restrict (Set.Ioo (-(1 / 4) : ℝ) (1 / 4) ×ˢ
      sourceBall (0 : Vec d) (1 / 2))
    let ν : ℕ → Measure (ℝ × Vec d) := fun n =>
      volume.restrict (Set.Ioo (-(1 / 4) - 3 / (4 * (2 : ℝ) ^ n))
        (1 / 4 + 3 / (4 * (2 : ℝ) ^ n)) ×ˢ
        sourceBall (0 : Vec d) (1 / 2 + 1 / (2 * (2 : ℝ) ^ n)))
    ∃ C : ℝ, 0 < C ∧ ∀ u : ℝ × Vec d → ℝ,
      AEStronglyMeasurable u μ →
      (∀ n, eLpNorm u (ENNReal.ofReal (2 * c ^ n)) (ν n) ≠ ⊤) →
      (∀ n, (eLpNorm u (ENNReal.ofReal (2 * c ^ (n + 1))) (ν (n + 1))).toReal ≤
        Real.rpow (A * Real.rpow b (n : ℝ)) (1 / (2 * Real.rpow c (n : ℝ))) *
          (eLpNorm u (ENNReal.ofReal (2 * c ^ n)) (ν n)).toReal) →
      eLpNorm u ⊤ μ ≤ ENNReal.ofReal C * eLpNorm u 2 (ν 0) := by
  dsimp only
  let c : ℝ := ((d : ℝ) + 2) / d
  let μ := volume.restrict (Set.Ioo (-(1 / 4) : ℝ) (1 / 4) ×ˢ
    sourceBall (0 : Vec d) (1 / 2))
  let ν : ℕ → Measure (ℝ × Vec d) := fun n =>
    volume.restrict (Set.Ioo (-(1 / 4) - 3 / (4 * (2 : ℝ) ^ n))
      (1 / 4 + 3 / (4 * (2 : ℝ) ^ n)) ×ˢ
      sourceBall (0 : Vec d) (1 / 2 + 1 / (2 * (2 : ℝ) ^ n)))
  change ∃ C : ℝ, 0 < C ∧ ∀ u : ℝ × Vec d → ℝ,
    AEStronglyMeasurable u μ →
    (∀ n, eLpNorm u (ENNReal.ofReal (2 * c ^ n)) (ν n) ≠ ⊤) →
    (∀ n, (eLpNorm u (ENNReal.ofReal (2 * c ^ (n + 1))) (ν (n + 1))).toReal ≤
      Real.rpow (A * Real.rpow b (n : ℝ)) (1 / (2 * Real.rpow c (n : ℝ))) *
        (eLpNorm u (ENNReal.ofReal (2 * c ^ n)) (ν n)).toReal) →
    eLpNorm u ⊤ μ ≤ ENNReal.ofReal C * eLpNorm u 2 (ν 0)
  have hc : 1 < c := (c11_moser_geometric_exponent_step d 0 (by omega)).1
  obtain ⟨C, hC, hbound⟩ := c17_moser_geometric_iteration_bound A b c 2 hA hb hc (by norm_num)
  refine ⟨C, hC, ?_⟩
  intro u hu hfinite hstep
  have : IsFiniteMeasure μ := c20_sourceCylinder_isFiniteMeasure _ _ _ _
  let Y : ℕ → ℝ := fun n => (eLpNorm u (ENNReal.ofReal (2 * c ^ n)) (ν n)).toReal
  have hY : ∀ n, 0 ≤ Y n := fun _ => ENNReal.toReal_nonneg
  have hiter : ∀ n, eLpNorm u (ENNReal.ofReal (2 * c ^ n)) μ ≤
      ENNReal.ofReal (C * Y 0) := by
    intro n
    have hsub := (c11_moser_dyadic_cylinder_containment d n).1
    have hmeasure : μ ≤ ν n := Measure.restrict_mono_set volume hsub
    calc
      _ ≤ eLpNorm u (ENNReal.ofReal (2 * c ^ n)) (ν n) := eLpNorm_mono_measure u hmeasure
      _ = ENNReal.ofReal (Y n) := (ENNReal.ofReal_toReal (hfinite n)).symm
      _ ≤ ENNReal.ofReal (C * Y 0) := ENNReal.ofReal_le_ofReal (hbound Y hY hstep n)
  have h := c13_moser_powers_essential_bound μ u hu 2 c (C * Y 0) (by norm_num) hc
    (mul_nonneg hC.le (hY 0)) hiter
  calc
    eLpNorm u ⊤ μ ≤ ENNReal.ofReal (C * Y 0) := h
    _ = ENNReal.ofReal C * eLpNorm u 2 (ν 0) := by
      rw [ENNReal.ofReal_mul hC.le]
      have hzero : eLpNorm u 2 (ν 0) ≠ ⊤ := by simpa using hfinite 0
      simpa [Y] using congrArg (fun x => ENNReal.ofReal C * x)
        (ENNReal.ofReal_toReal hzero)


/-- A signed moment gain with a finite real coefficient gives the finite
real-valued norm step required by the dyadic iteration. -/
theorem c11_signed_real_norm_step_of_moment_gain
    {X : Type*} [MeasurableSpace X] (μ ν : Measure X) (v : X → ℝ)
    (hvμ : AEStronglyMeasurable v μ) (hvν : AEStronglyMeasurable v ν)
    (p s R : ℝ) (hp : 0 < p) (hs : 0 ≤ s) (hR : 0 ≤ R)
    (K A E : ℝ≥0∞)
    (hfinite : eLpNorm v (ENNReal.ofReal p) μ ≠ ⊤)
    (hcoefficient : (K * A ^ s * E) ^ (1 / (p * (1 + s))) ≤ ENNReal.ofReal R)
    (hgain : (∫⁻ x, ‖v x‖ₑ ^ (p * (1 + s)) ∂ν) ≤
      K * (A * (∫⁻ x, ‖v x‖ₑ ^ p ∂μ)) ^ s *
        (E * (∫⁻ x, ‖v x‖ₑ ^ p ∂μ))) :
    eLpNorm v (ENNReal.ofReal (p * (1 + s))) ν ≠ ⊤ ∧
      (eLpNorm v (ENNReal.ofReal (p * (1 + s))) ν).toReal ≤
        R * (eLpNorm v (ENNReal.ofReal p) μ).toReal := by
  have hstep := c11_moser_norm_step_of_moment_gain μ ν v hvμ hvν p s hp hs K A E hgain
  have hcoefficient' : (K * A ^ s * E) ^ (1 / (p * (1 + s))) *
      eLpNorm v (ENNReal.ofReal p) μ ≤ ENNReal.ofReal R *
      eLpNorm v (ENNReal.ofReal p) μ := by
    simpa only [mul_comm] using (mul_le_mul_right hcoefficient (eLpNorm v (ENNReal.ofReal p) μ))
  have hbound : eLpNorm v (ENNReal.ofReal (p * (1 + s))) ν ≤
      ENNReal.ofReal R * eLpNorm v (ENNReal.ofReal p) μ :=
    hstep.trans hcoefficient'
  have htop : ENNReal.ofReal R * eLpNorm v (ENNReal.ofReal p) μ ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfinite
  refine ⟨ne_top_of_le_ne_top htop hbound, ?_⟩
  have hreal := ENNReal.toReal_mono htop hbound
  simpa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hR] using hreal


/-- A signed moment gain on every pair of dyadic cylinders gives the uniform
unit-scale local maximum estimate, once its coefficient and moments are finite. -/
theorem c11_signed_unit_local_max_of_moment_gain
    (d : ℕ) (hd : 2 ≤ d) (A b : ℝ) (hA : 1 ≤ A) (hb : 1 < b) :
    let c : ℝ := ((d : ℝ) + 2) / d
    let s : ℝ := 2 / d
    let μ := volume.restrict (Set.Ioo (-(1 / 4) : ℝ) (1 / 4) ×ˢ
      sourceBall (0 : Vec d) (1 / 2))
    let ν : ℕ → Measure (ℝ × Vec d) := fun n =>
      volume.restrict (Set.Ioo (-(1 / 4) - 3 / (4 * (2 : ℝ) ^ n))
        (1 / 4 + 3 / (4 * (2 : ℝ) ^ n)) ×ˢ
        sourceBall (0 : Vec d) (1 / 2 + 1 / (2 * (2 : ℝ) ^ n)))
    ∃ C : ℝ, 0 < C ∧ ∀ (u : ℝ × Vec d → ℝ) (K B E : ℕ → ℝ≥0∞),
      AEStronglyMeasurable u μ →
      (∀ n, AEStronglyMeasurable u (ν n)) →
      (∀ n, eLpNorm u (ENNReal.ofReal (2 * c ^ n)) (ν n) ≠ ⊤) →
      (∀ n, (K n * B n ^ s * E n) ^ (1 / ((2 * c ^ n) * (1 + s))) ≤
        ENNReal.ofReal (Real.rpow (A * Real.rpow b (n : ℝ))
          (1 / (2 * Real.rpow c (n : ℝ))))) →
      (∀ n, (∫⁻ x, ‖u x‖ₑ ^ ((2 * c ^ n) * (1 + s)) ∂(ν (n + 1))) ≤
        K n * (B n * (∫⁻ x, ‖u x‖ₑ ^ (2 * c ^ n) ∂(ν n))) ^ s *
          (E n * (∫⁻ x, ‖u x‖ₑ ^ (2 * c ^ n) ∂(ν n)))) →
      eLpNorm u ⊤ μ ≤ ENNReal.ofReal C * eLpNorm u 2 (ν 0) := by
  dsimp only
  let c : ℝ := ((d : ℝ) + 2) / d
  let s : ℝ := 2 / d
  let μ := volume.restrict (Set.Ioo (-(1 / 4) : ℝ) (1 / 4) ×ˢ
    sourceBall (0 : Vec d) (1 / 2))
  let ν : ℕ → Measure (ℝ × Vec d) := fun n =>
    volume.restrict (Set.Ioo (-(1 / 4) - 3 / (4 * (2 : ℝ) ^ n))
      (1 / 4 + 3 / (4 * (2 : ℝ) ^ n)) ×ˢ
      sourceBall (0 : Vec d) (1 / 2 + 1 / (2 * (2 : ℝ) ^ n)))
  obtain ⟨C, hC, hbound⟩ := c11_signed_unit_local_max_of_norm_recurrence d hd A b hA hb
  refine ⟨C, hC, ?_⟩
  intro u K B E hu hmeas hfinite hcoef hgain
  apply hbound u hu hfinite
  intro n
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hc : 1 < c := (c11_moser_geometric_exponent_step d n (by omega)).1
  have hs : 0 ≤ s := by dsimp [s]; positivity
  have hcs : 1 + s = c := by
    dsimp [s, c]
    field_simp
  have hp : 0 < 2 * c ^ n := by positivity
  have hA0 : 0 ≤ A := le_trans (by norm_num) hA
  have hb0 : 0 ≤ b := le_of_lt (lt_trans zero_lt_one hb)
  have hR : 0 ≤ Real.rpow (A * Real.rpow b (n : ℝ))
      (1 / (2 * Real.rpow c (n : ℝ))) :=
    Real.rpow_nonneg (mul_nonneg hA0 (Real.rpow_nonneg hb0 _)) _
  have hstep := c11_signed_real_norm_step_of_moment_gain (ν n) (ν (n + 1)) u
    (hmeas n) (hmeas (n + 1)) (2 * c ^ n) s _ hp hs hR
    (K n) (B n) (E n) (hfinite n) (hcoef n) (hgain n)
  have hexp : (2 * c ^ n) * (1 + s) = 2 * c ^ (n + 1) := by
    rw [hcs, pow_succ]
    ring
  simpa only [hexp] using hstep.2

/-- A moment gain propagates finite norms from the initial exponent. -/
theorem c11_signed_moment_gain_finite_iterates
    {X : Type*} [MeasurableSpace X] (ν : ℕ → Measure X) (v : X → ℝ)
    (p : ℕ → ℝ) (s : ℝ) (K B E : ℕ → ℝ≥0∞) (R : ℕ → ℝ)
    (hmeas : ∀ n, AEStronglyMeasurable v (ν n))
    (hp : ∀ n, 0 < p n) (hs : 0 ≤ s) (hR : ∀ n, 0 ≤ R n)
    (hexp : ∀ n, p n * (1 + s) = p (n + 1))
    (hzero : eLpNorm v (ENNReal.ofReal (p 0)) (ν 0) ≠ ⊤)
    (hcoef : ∀ n, (K n * B n ^ s * E n) ^ (1 / (p n * (1 + s))) ≤
      ENNReal.ofReal (R n))
    (hgain : ∀ n, (∫⁻ x, ‖v x‖ₑ ^ (p n * (1 + s)) ∂(ν (n + 1))) ≤
      K n * (B n * (∫⁻ x, ‖v x‖ₑ ^ p n ∂(ν n))) ^ s *
        (E n * (∫⁻ x, ‖v x‖ₑ ^ p n ∂(ν n)))) :
    ∀ n, eLpNorm v (ENNReal.ofReal (p n)) (ν n) ≠ ⊤ := by
  intro n
  induction n with
  | zero => exact hzero
  | succ n ih =>
      have hstep := c11_signed_real_norm_step_of_moment_gain (ν n) (ν (n + 1)) v
        (hmeas n) (hmeas (n + 1)) (p n) s (R n) (hp n) hs (hR n)
        (K n) (B n) (E n) ih (hcoef n) (hgain n)
      simpa only [hexp n] using hstep.1

/-- Initial L2 finiteness suffices to run the conditional signed iteration. -/
theorem c11_signed_unit_local_max_of_initial_finite_moment_gain
    (d : ℕ) (hd : 2 ≤ d) (A b : ℝ) (hA : 1 ≤ A) (hb : 1 < b) :
    let c : ℝ := ((d : ℝ) + 2) / d
    let s : ℝ := 2 / d
    let μ := volume.restrict (Set.Ioo (-(1 / 4) : ℝ) (1 / 4) ×ˢ
      sourceBall (0 : Vec d) (1 / 2))
    let ν : ℕ → Measure (ℝ × Vec d) := fun n =>
      volume.restrict (Set.Ioo (-(1 / 4) - 3 / (4 * (2 : ℝ) ^ n))
        (1 / 4 + 3 / (4 * (2 : ℝ) ^ n)) ×ˢ
        sourceBall (0 : Vec d) (1 / 2 + 1 / (2 * (2 : ℝ) ^ n)))
    ∃ C : ℝ, 0 < C ∧ ∀ (u : ℝ × Vec d → ℝ) (K B E : ℕ → ℝ≥0∞),
      AEStronglyMeasurable u μ →
      (∀ n, AEStronglyMeasurable u (ν n)) →
      eLpNorm u 2 (ν 0) ≠ ⊤ →
      (∀ n, (K n * B n ^ s * E n) ^ (1 / ((2 * c ^ n) * (1 + s))) ≤
        ENNReal.ofReal (Real.rpow (A * Real.rpow b (n : ℝ))
          (1 / (2 * Real.rpow c (n : ℝ))))) →
      (∀ n, (∫⁻ x, ‖u x‖ₑ ^ ((2 * c ^ n) * (1 + s)) ∂(ν (n + 1))) ≤
        K n * (B n * (∫⁻ x, ‖u x‖ₑ ^ (2 * c ^ n) ∂(ν n))) ^ s *
          (E n * (∫⁻ x, ‖u x‖ₑ ^ (2 * c ^ n) ∂(ν n)))) →
      eLpNorm u ⊤ μ ≤ ENNReal.ofReal C * eLpNorm u 2 (ν 0) := by
  dsimp only
  let c : ℝ := ((d : ℝ) + 2) / d
  let s : ℝ := 2 / d
  let ν : ℕ → Measure (ℝ × Vec d) := fun n =>
    volume.restrict (Set.Ioo (-(1 / 4) - 3 / (4 * (2 : ℝ) ^ n))
      (1 / 4 + 3 / (4 * (2 : ℝ) ^ n)) ×ˢ
      sourceBall (0 : Vec d) (1 / 2 + 1 / (2 * (2 : ℝ) ^ n)))
  obtain ⟨C, hC, hbound⟩ := c11_signed_unit_local_max_of_moment_gain d hd A b hA hb
  refine ⟨C, hC, ?_⟩
  intro u K B E hu hmeas hzero hcoef hgain
  apply hbound u K B E hu hmeas ?_ hcoef hgain
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hc : 1 < c := (c11_moser_geometric_exponent_step d 0 (by omega)).1
  have hs : 0 ≤ s := by dsimp [s]; positivity
  have hcs : 1 + s = c := by
    dsimp [s, c]
    field_simp
  have hp : ∀ n : ℕ, 0 < 2 * c ^ n := by intro n; positivity
  have hA0 : 0 ≤ A := le_trans (by norm_num) hA
  have hb0 : 0 ≤ b := le_of_lt (lt_trans zero_lt_one hb)
  have hR : ∀ n : ℕ, 0 ≤ Real.rpow (A * Real.rpow b (n : ℝ))
      (1 / (2 * Real.rpow c (n : ℝ))) := by
    intro n
    exact Real.rpow_nonneg (mul_nonneg hA0 (Real.rpow_nonneg hb0 _)) _
  have hexp : ∀ n : ℕ, (2 * c ^ n) * (1 + s) = 2 * c ^ (n + 1) := by
    intro n
    rw [hcs, pow_succ]
    ring
  apply c11_signed_moment_gain_finite_iterates ν u (fun n => 2 * c ^ n) s K B E
    (fun n => Real.rpow (A * Real.rpow b (n : ℝ)) (1 / (2 * Real.rpow c (n : ℝ))))
    hmeas hp hs hR hexp ?_ hcoef hgain
  simpa [ν] using hzero


/-- Conditional native weighted-caloric local maximum estimate. The explicit
missing input is the signed dyadic moment gain with uniform coefficients. -/
theorem c11_native_unit_L2_local_max_of_signed_moment_gain
    (d : ℕ) (hd : 2 ≤ d) (κ : ℝ)
    (hgain :
      let c : ℝ := ((d : ℝ) + 2) / d
      let s : ℝ := 2 / d
      let ν : ℕ → Measure (ℝ × Vec d) := fun n =>
        volume.restrict (Set.Ioo (-(1 / 4) - 3 / (4 * (2 : ℝ) ^ n))
          (1 / 4 + 3 / (4 * (2 : ℝ) ^ n)) ×ˢ
          sourceBall (0 : Vec d) (1 / 2 + 1 / (2 * (2 : ℝ) ^ n)))
      ∃ A b : ℝ, 1 ≤ A ∧ 1 < b ∧
        ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
          IsUniformlyElliptic κ ρ α →
          ∀ (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d),
          IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1) u G →
          ∃ K B E : ℕ → ℝ≥0∞,
            (∀ n, (K n * B n ^ s * E n) ^ (1 / ((2 * c ^ n) * (1 + s))) ≤
              ENNReal.ofReal (Real.rpow (A * Real.rpow b (n : ℝ))
                (1 / (2 * Real.rpow c (n : ℝ))))) ∧
            (∀ n, (∫⁻ x, ‖u x‖ₑ ^ ((2 * c ^ n) * (1 + s)) ∂(ν (n + 1))) ≤
              K n * (B n * (∫⁻ x, ‖u x‖ₑ ^ (2 * c ^ n) ∂(ν n))) ^ s *
                (E n * (∫⁻ x, ‖u x‖ₑ ^ (2 * c ^ n) ∂(ν n))))) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
      IsUniformlyElliptic κ ρ α →
      ∀ (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d),
      IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1) u G →
      eLpNorm u ⊤ (volume.restrict (Set.Ioo (-(1/4:ℝ)) (1/4) ×ˢ sourceBall 0 (1/2))) ≤
        ENNReal.ofReal C * eLpNorm u 2
          (volume.restrict (Set.Ioo (-1:ℝ) 1 ×ˢ sourceBall 0 1)) := by
  obtain ⟨A, b, hA, hb, hgain⟩ := hgain
  obtain ⟨C, hC, hiter⟩ := c11_signed_unit_local_max_of_initial_finite_moment_gain d hd A b hA hb
  refine ⟨C, hC, ?_⟩
  intro ρ α hell u G hcal
  obtain ⟨K, B, E, hcoef, hmoment⟩ := hgain ρ α hell u G hcal
  have hmeas (n : ℕ) : AEStronglyMeasurable u
      (volume.restrict (Set.Ioo (-(1 / 4) - 3 / (4 * (2 : ℝ) ^ n))
        (1 / 4 + 3 / (4 * (2 : ℝ) ^ n)) ×ˢ
        sourceBall (0 : Vec d) (1 / 2 + 1 / (2 * (2 : ℝ) ^ n)))) :=
    hcal.1.aestronglyMeasurable.mono_measure
      (Measure.restrict_mono_set volume (c11_moser_dyadic_cylinder_containment d n).2)
  have hinner := (c11_moser_dyadic_cylinder_containment d 0).1.trans
    (c11_moser_dyadic_cylinder_containment d 0).2
  have hterminal := hcal.1.aestronglyMeasurable.mono_measure
    (Measure.restrict_mono_set volume hinner)
  have hzero : eLpNorm u 2
      (volume.restrict (Set.Ioo (-(1 / 4) - 3 / (4 * (2 : ℝ) ^ 0))
        (1 / 4 + 3 / (4 * (2 : ℝ) ^ 0)) ×ˢ
        sourceBall (0 : Vec d) (1 / 2 + 1 / (2 * (2 : ℝ) ^ 0)))) ≠ ⊤ :=
    (hcal.1.mono_measure
      (Measure.restrict_mono_set volume (c11_moser_dyadic_cylinder_containment d 0).2)).eLpNorm_ne_top
  have h := hiter u K B E hterminal hmeas hzero hcoef hmoment
  convert h using 1 <;> norm_num


/-- Conditional local maximum estimate for the actual Dirichlet kernel on a
unit cylinder centered at a strictly positive time. -/
theorem c11_native_dirichlet_kernel_unit_local_max_of_signed_moment_gain
    (d : ℕ) (hd : 2 ≤ d) (κ : ℝ)
    (hgain :
      let c : ℝ := ((d : ℝ) + 2) / d
      let s : ℝ := 2 / d
      let ν : ℕ → Measure (ℝ × Vec d) := fun n =>
        volume.restrict (Set.Ioo (-(1 / 4) - 3 / (4 * (2 : ℝ) ^ n))
          (1 / 4 + 3 / (4 * (2 : ℝ) ^ n)) ×ˢ
          sourceBall (0 : Vec d) (1 / 2 + 1 / (2 * (2 : ℝ) ^ n)))
      ∃ A b : ℝ, 1 ≤ A ∧ 1 < b ∧
        ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
          IsUniformlyElliptic κ ρ α →
          ∀ (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d),
          IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1) u G →
          ∃ K B E : ℕ → ℝ≥0∞,
            (∀ n, (K n * B n ^ s * E n) ^ (1 / ((2 * c ^ n) * (1 + s))) ≤
              ENNReal.ofReal (Real.rpow (A * Real.rpow b (n : ℝ))
                (1 / (2 * Real.rpow c (n : ℝ))))) ∧
            (∀ n, (∫⁻ x, ‖u x‖ₑ ^ ((2 * c ^ n) * (1 + s)) ∂(ν (n + 1))) ≤
              K n * (B n * (∫⁻ x, ‖u x‖ₑ ^ (2 * c ^ n) ∂(ν n))) ^ s *
                (E n * (∫⁻ x, ‖u x‖ₑ ^ (2 * c ^ n) ∂(ν n))))) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
      IsUniformlyElliptic κ ρ α →
      ∀ (K : ℝ → Vec d → Vec d → ℝ) (G : ℝ → Vec d → Vec d → Vec d),
      IsDirichletFundamentalSolution ρ α 1 K G →
      ∀ y ∈ sourceBall (0 : Vec d) 1, ∀ t₀ : ℝ, 1 < t₀ →
        eLpNorm (fun z : ℝ × Vec d => K (t₀ + z.1) z.2 y) ⊤
          (volume.restrict (Set.Ioo (-(1/4:ℝ)) (1/4) ×ˢ sourceBall 0 (1/2))) ≤
        ENNReal.ofReal C * eLpNorm (fun z : ℝ × Vec d => K (t₀ + z.1) z.2 y) 2
          (volume.restrict (Set.Ioo (-1:ℝ) 1 ×ˢ sourceBall 0 1)) := by
  obtain ⟨C, hC, hlocal⟩ := c11_native_unit_L2_local_max_of_signed_moment_gain d hd κ hgain
  refine ⟨C, hC, ?_⟩
  intro ρ α hell K G hK y hy t₀ ht₀
  have ha : 0 < t₀ + (-1 : ℝ) := by linarith
  have hab : t₀ + (-1 : ℝ) < t₀ + 1 := by linarith
  have hcal := ((hK y hy).2.2.2.1 (t₀ + (-1)) (t₀ + 1) ha hab).1
  have hc := c18_weighted_caloric_time_translate ρ α (-1) 1 t₀
    (sourceBall 0 1) (fun z => K z.1 z.2 y) (fun z => G z.1 z.2 y) hcal
  exact hlocal ρ α hell _ _ hc


/-- The signed gain yields the square-integral form used by the scaled
weighted-caloric local maximum theorem. -/
theorem c11_native_unit_essSup_local_max_of_signed_moment_gain
    (d : ℕ) (hd : 2 ≤ d) (κ : ℝ)
    (hgain :
      let c : ℝ := ((d : ℝ) + 2) / d
      let s : ℝ := 2 / d
      let ν : ℕ → Measure (ℝ × Vec d) := fun n =>
        volume.restrict (Set.Ioo (-(1 / 4) - 3 / (4 * (2 : ℝ) ^ n))
          (1 / 4 + 3 / (4 * (2 : ℝ) ^ n)) ×ˢ
          sourceBall (0 : Vec d) (1 / 2 + 1 / (2 * (2 : ℝ) ^ n)))
      ∃ A b : ℝ, 1 ≤ A ∧ 1 < b ∧
        ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
          IsUniformlyElliptic κ ρ α →
          ∀ (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d),
          IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1) u G →
          ∃ K B E : ℕ → ℝ≥0∞,
            (∀ n, (K n * B n ^ s * E n) ^ (1 / ((2 * c ^ n) * (1 + s))) ≤
              ENNReal.ofReal (Real.rpow (A * Real.rpow b (n : ℝ))
                (1 / (2 * Real.rpow c (n : ℝ))))) ∧
            (∀ n, (∫⁻ x, ‖u x‖ₑ ^ ((2 * c ^ n) * (1 + s)) ∂(ν (n + 1))) ≤
              K n * (B n * (∫⁻ x, ‖u x‖ₑ ^ (2 * c ^ n) ∂(ν n))) ^ s *
                (E n * (∫⁻ x, ‖u x‖ₑ ^ (2 * c ^ n) ∂(ν n))))) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
      IsUniformlyElliptic κ ρ α →
      ∀ (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d),
      IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1) u G →
      essSup (fun z => ENNReal.ofReal |u z|)
        (volume.restrict (Set.Ioo (-(1/4:ℝ)) (1/4) ×ˢ sourceBall 0 (1/2))) ≤
      ENNReal.ofReal (C * Real.sqrt
        (∫ z in Set.Ioo (-1:ℝ) 1 ×ˢ sourceBall 0 1, |u z| ^ 2)) := by
  obtain ⟨C, hC, hbound⟩ := c11_native_unit_L2_local_max_of_signed_moment_gain d hd κ hgain
  refine ⟨C, hC, ?_⟩
  intro ρ α hell u G hcal
  have h := hbound ρ α hell u G hcal
  have hreal : (eLpNorm u 2
      (volume.restrict (Set.Ioo (-1:ℝ) 1 ×ˢ sourceBall 0 1))).toReal =
      Real.sqrt (∫ z in Set.Ioo (-1:ℝ) 1 ×ˢ sourceBall 0 1, |u z| ^ 2) := by
    rw [hcal.1.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top,
      ENNReal.toReal_ofReal (by positivity), Real.sqrt_eq_rpow]
    congr 1
    · exact integral_congr_ae (Filter.Eventually.of_forall fun x => by
        simp only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs])
    · simp
  have hn : eLpNorm u 2 (volume.restrict (Set.Ioo (-1:ℝ) 1 ×ˢ sourceBall 0 1)) =
      ENNReal.ofReal (Real.sqrt (∫ z in Set.Ioo (-1:ℝ) 1 ×ˢ sourceBall 0 1, |u z| ^ 2)) := by
    rw [← hreal, ENNReal.ofReal_toReal hcal.1.eLpNorm_ne_top]
  have hsup : essSup (fun z => ENNReal.ofReal |u z|)
      (volume.restrict (Set.Ioo (-(1/4:ℝ)) (1/4) ×ˢ sourceBall 0 (1/2))) ≤
      eLpNorm u ⊤ (volume.restrict (Set.Ioo (-(1/4:ℝ)) (1/4) ×ˢ sourceBall 0 (1/2))) := by
    simpa only [eLpNormEssSup_eq_essSup_enorm, Real.enorm_eq_ofReal_abs] using
      (eLpNormEssSup_le_eLpNorm_top (f := u)
        (μ := volume.restrict (Set.Ioo (-(1/4:ℝ)) (1/4) ×ˢ sourceBall 0 (1/2))))
  calc
    _ ≤ ENNReal.ofReal C * eLpNorm u 2
        (volume.restrict (Set.Ioo (-1:ℝ) 1 ×ˢ sourceBall 0 1)) := hsup.trans h
    _ = _ := by rw [hn, ← ENNReal.ofReal_mul hC.le]

/-- The signed gain gives the local maximum bound on any parabolic cylinder. -/
theorem c11_native_scaled_essSup_local_max_of_signed_moment_gain
    (d : ℕ) (hd : 2 ≤ d) (κ : ℝ) (hκ : 0 < κ)
    (hgain :
      let c : ℝ := ((d : ℝ) + 2) / d
      let s : ℝ := 2 / d
      let ν : ℕ → Measure (ℝ × Vec d) := fun n =>
        volume.restrict (Set.Ioo (-(1 / 4) - 3 / (4 * (2 : ℝ) ^ n))
          (1 / 4 + 3 / (4 * (2 : ℝ) ^ n)) ×ˢ
          sourceBall (0 : Vec d) (1 / 2 + 1 / (2 * (2 : ℝ) ^ n)))
      ∃ A b : ℝ, 1 ≤ A ∧ 1 < b ∧
        ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
          IsUniformlyElliptic κ ρ α →
          ∀ (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d),
          IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1) u G →
          ∃ K B E : ℕ → ℝ≥0∞,
            (∀ n, (K n * B n ^ s * E n) ^ (1 / ((2 * c ^ n) * (1 + s))) ≤
              ENNReal.ofReal (Real.rpow (A * Real.rpow b (n : ℝ))
                (1 / (2 * Real.rpow c (n : ℝ))))) ∧
            (∀ n, (∫⁻ x, ‖u x‖ₑ ^ ((2 * c ^ n) * (1 + s)) ∂(ν (n + 1))) ≤
              K n * (B n * (∫⁻ x, ‖u x‖ₑ ^ (2 * c ^ n) ∂(ν n))) ^ s *
                (E n * (∫⁻ x, ‖u x‖ₑ ^ (2 * c ^ n) ∂(ν n))))) :
    ∃ C : ℝ, 0 < C ∧ ∀ (t₀ : ℝ) (y : Vec d) (r : ℝ), 0 < r →
      ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
      IsUniformlyElliptic κ ρ α →
      ∀ (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d),
      IsWeightedCaloric ρ α (Set.Ioo (t₀ - r^2) (t₀ + r^2)) (sourceBall y r) u G →
      essSup (fun z => ENNReal.ofReal |u z|)
        (volume.restrict (Set.Ioo (t₀ - r^2 / 4) (t₀ + r^2 / 4) ×ˢ sourceBall y (r / 2))) ≤
      ENNReal.ofReal (C * Real.sqrt
        ((r ^ (d + 2))⁻¹ * ∫ z in Set.Ioo (t₀ - r^2) (t₀ + r^2) ×ˢ sourceBall y r, |u z| ^ 2)) := by
  obtain ⟨C, hC, hunit⟩ := c11_native_unit_essSup_local_max_of_signed_moment_gain d hd κ hgain
  refine ⟨C, hC, ?_⟩
  intro t₀ y r hr ρ α hell u G hcal
  exact c17_time_shifted_scaled_local_max_of_unit_bound d hd κ C hκ hC
    (by simpa only [neg_div] using hunit) t₀ y r hr ρ α hell u G hcal

/-- The scaled signed-gain estimate applies to the actual Dirichlet kernel
on cylinders contained in its spatial domain and positive-time region. -/
theorem c11_native_dirichlet_kernel_scaled_local_max_of_signed_moment_gain
    (d : ℕ) (hd : 2 ≤ d) (κ : ℝ) (hκ : 0 < κ)
    (hgain :
      let c : ℝ := ((d : ℝ) + 2) / d
      let s : ℝ := 2 / d
      let ν : ℕ → Measure (ℝ × Vec d) := fun n =>
        volume.restrict (Set.Ioo (-(1 / 4) - 3 / (4 * (2 : ℝ) ^ n))
          (1 / 4 + 3 / (4 * (2 : ℝ) ^ n)) ×ˢ
          sourceBall (0 : Vec d) (1 / 2 + 1 / (2 * (2 : ℝ) ^ n)))
      ∃ A b : ℝ, 1 ≤ A ∧ 1 < b ∧
        ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
          IsUniformlyElliptic κ ρ α →
          ∀ (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d),
          IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1) u G →
          ∃ K B E : ℕ → ℝ≥0∞,
            (∀ n, (K n * B n ^ s * E n) ^ (1 / ((2 * c ^ n) * (1 + s))) ≤
              ENNReal.ofReal (Real.rpow (A * Real.rpow b (n : ℝ))
                (1 / (2 * Real.rpow c (n : ℝ))))) ∧
            (∀ n, (∫⁻ x, ‖u x‖ₑ ^ ((2 * c ^ n) * (1 + s)) ∂(ν (n + 1))) ≤
              K n * (B n * (∫⁻ x, ‖u x‖ₑ ^ (2 * c ^ n) ∂(ν n))) ^ s *
                (E n * (∫⁻ x, ‖u x‖ₑ ^ (2 * c ^ n) ∂(ν n))))) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
      IsUniformlyElliptic κ ρ α →
      ∀ (K : ℝ → Vec d → Vec d → ℝ) (G : ℝ → Vec d → Vec d → Vec d),
      IsDirichletFundamentalSolution ρ α 1 K G →
      ∀ pole ∈ sourceBall (0 : Vec d) 1, ∀ (t₀ : ℝ) (y : Vec d) (r : ℝ),
      0 < r → 0 < t₀ - r ^ 2 → sourceBall y r ⊆ sourceBall (0 : Vec d) 1 →
      essSup (fun z : ℝ × Vec d => ENNReal.ofReal |K z.1 z.2 pole|)
        (volume.restrict (Set.Ioo (t₀ - r^2 / 4) (t₀ + r^2 / 4) ×ˢ sourceBall y (r / 2))) ≤
      ENNReal.ofReal (C * Real.sqrt
        ((r ^ (d + 2))⁻¹ * ∫ z in Set.Ioo (t₀ - r^2) (t₀ + r^2) ×ˢ sourceBall y r,
          |K z.1 z.2 pole| ^ 2)) := by
  obtain ⟨C, hC, hlocal⟩ :=
    c11_native_scaled_essSup_local_max_of_signed_moment_gain d hd κ hκ hgain
  refine ⟨C, hC, ?_⟩
  intro ρ α hell K G hK pole hpole t₀ y r hr ht hsub
  have hab : t₀ - r^2 < t₀ + r^2 := by nlinarith [sq_pos_of_pos hr]
  have hcal := ((hK pole hpole).2.2.2.1 (t₀ - r^2) (t₀ + r^2) ht hab).1
  have hcal' := c11_weighted_caloric_spatial_mono measurableSet_Ioo
    (c17_isOpen_sourceBall (0 : Vec d) 1).measurableSet hsub hcal
  exact hlocal t₀ y r hr ρ α hell _ _ hcal'

end EinsteinFull.Calculus
