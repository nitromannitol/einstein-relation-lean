import EinsteinRelation.Calculus.Weak
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-! # Smooth compact tests for the heat-kernel weak pairing

Source: AKM (9.2), p. 347; `paper/main.tex:777–782,840`.
Convolution commutes with the actual weak spatial derivative.
-/

open MeasureTheory
open scoped Convolution Topology
namespace EinsteinRelation.Correctors

/-- A smooth compact convolution is an admissible whole-space test. -/
theorem akm_convolution_isSpatialTest {d : ℕ} {f ρ : Vec d → ℝ}
    (hf : Integrable f volume) (hfc : HasCompactSupport f)
    (hρ : ContDiff ℝ (⊤ : ℕ∞) ρ) (hρc : HasCompactSupport ρ) :
    IsSpatialTest Set.univ (fun x => ∫ y, f y * ρ (x-y) ∂volume) := by
  let L := ContinuousLinearMap.mul ℝ ℝ
  exact ⟨hρc.contDiff_convolution_right (L := L) hf.locallyIntegrable hρ,
    hfc.convolution (L := L) (μ := volume) hρc, Set.subset_univ _⟩

/-- Differentiation of a smooth convolution retains the given weak gradient. -/
theorem akm_coordinateDerivative_convolution {d : ℕ} {f : Vec d → ℝ}
    {Df : Vec d → Vec d} (hf : Integrable f volume)
    (hweak : HasWeakGradient Set.univ f Df)
    {ρ : Vec d → ℝ} (hρ : ContDiff ℝ (⊤ : ℕ∞) ρ)
    (hρc : HasCompactSupport ρ) (x : Vec d) (j : Fin d) :
    coordinateDerivative j (fun z => ∫ y, f y * ρ (z-y) ∂volume) x =
      ∫ y, Df y j * ρ (x-y) ∂volume := by
  let L := ContinuousLinearMap.mul ℝ ℝ
  have hρ1 : ContDiff ℝ 1 ρ := hρ.of_le (by norm_cast)
  have hd := hρc.hasFDerivAt_convolution_right (L := L) hf.locallyIntegrable hρ1 x
  have hdiff : coordinateDerivative j (fun z => ∫ y, f y * ρ (z-y) ∂volume) x =
      ∫ y, f y * fderiv ℝ ρ (x-y) (unitVector j) ∂volume := by
    change fderiv ℝ (convolution f ρ L volume) x (unitVector j) = _
    rw [hd.fderiv]
    exact convolution_precompR_apply (L := L) hf.locallyIntegrable (hρc.fderiv ℝ)
      (contDiff_infty_iff_fderiv.mp hρ).2.continuous x (unitVector j)
  rw [hdiff]
  let ψ : Vec d → ℝ := fun y => ρ (x-y)
  have hψ : ContDiff ℝ (⊤ : ℕ∞) ψ := hρ.comp (contDiff_const.sub contDiff_id)
  have hψc : HasCompactSupport ψ := hρc.comp_homeomorph (Homeomorph.subLeft x)
  have hder (y : Vec d) : coordinateDerivative j ψ y =
      -fderiv ℝ ρ (x-y) (unitVector j) := by
    have hs := (hasFDerivAt_const (𝕜 := ℝ) x y).sub (hasFDerivAt_id y)
    have hh := (hρ.differentiable (by norm_cast) (x-y)).hasFDerivAt.comp y hs
    change HasFDerivAt ψ _ y at hh
    unfold coordinateDerivative
    rw [hh.fderiv]
    simp
  have hh := (hweak j).2.2 ψ ⟨hψ, hψc, Set.subset_univ _⟩
  simp only [Measure.restrict_univ] at hh
  simp_rw [hder, mul_neg] at hh
  rw [integral_neg] at hh
  exact neg_injective hh

/-- A normalized family shrinking to the origin, used only in the
internal weak-pairing approximation. -/
noncomputable def akmTraceBump (d n : ℕ) : ContDiffBump (0 : Vec d) where
  rIn := 1 / ((n : ℝ) + 1) / 2
  rOut := 1 / ((n : ℝ) + 1)
  rIn_pos := by positivity
  rIn_lt_rOut := by
    have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    linarith

end EinsteinRelation.Correctors
