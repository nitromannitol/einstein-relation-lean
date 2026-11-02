import EinsteinRelation.Correctors.HorizontalMollifierBounds
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Topology.Algebra.ConstMulAction

/-! # The literal scaled mollifier orbit is a horizontal core

Source `paper/main.tex:545–566`: the horizontal smoothing `S_ε F(ω) = ∫ κ_ε(x) F(T_x ω) dx` with
`κ_ε(x) = ε^{-d} κ(x/ε)`. The literal scaled-orbit scalar `∫ κ(x) F(T_{εx} ω) dx` is the same
smoothing of the dilated kernel `κ_ε`. The spatial change of variables `y = ε • x` (Haar scaling by
the linear map `ε`, with Jacobian `ε^d` since `ε > 0`) gives the identity. Then
`isHorizontalTest_horizontalMollify` applies to `κ_ε`, which is smooth with compact support when
`ε ≠ 0`. No continuity of `F` in the environment is used, and `ε = 0` is excluded by hypothesis.
-/

open MeasureTheory

namespace EinsteinRelation.Correctors

/-- The dilated kernel `κ_ε(y) = ε^{-d} κ(y/ε)` of `paper/main.tex:548–566`, with `y/ε` written
as `ε⁻¹ • y`. Private to this file: the frozen statement does not mention it. -/
private noncomputable def scaledKernel {d : ℕ} (ε : ℝ) (y : Vec d) : ℝ :=
  (ε ^ d)⁻¹ * mollifier d (ε⁻¹ • y)

/-- The dilated kernel is `C^∞`: a constant times the smooth mollifier composed with a linear map. -/
private theorem contDiff_scaledKernel {d : ℕ} (ε : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (scaledKernel (d := d) ε) := by
  have hlin : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec d => ε⁻¹ • y) := contDiff_const_smul ε⁻¹
  unfold scaledKernel
  exact (contDiff_const (c := (ε ^ d)⁻¹)).mul ((contDiff_mollifier d).comp hlin)

/-- The dilated kernel has compact support whenever `ε ≠ 0`. -/
private theorem hasCompactSupport_scaledKernel {d : ℕ} {ε : ℝ} (hε : ε ≠ 0) :
    HasCompactSupport (scaledKernel (d := d) ε) := by
  have hc : HasCompactSupport (fun y : Vec d => mollifier d (ε⁻¹ • y)) :=
    (hasCompactSupport_mollifier d).comp_smul (inv_ne_zero hε)
  unfold scaledKernel
  exact hc.mul_left (f := fun _ : Vec d => (ε ^ d)⁻¹)

/-- Change of variables `y = ε • x` identifies the literal scaled-orbit integral with the horizontal
smoothing of the dilated kernel. The Haar scaling constant is `|(ε ^ d)⁻¹|`, which is `(ε ^ d)⁻¹`
for `ε > 0`; it cancels the prefactor `(ε ^ d)⁻¹` of the kernel at `ε • x`. -/
private theorem integral_scaledMollifier_eq_horizontalMollify {d : ℕ} (F : FieldPair d → ℝ)
    {ε : ℝ} (hε : 0 < ε) (ω : FieldPair d) :
    (∫ x : Vec d, mollifier d x * F (translate (ε • x) ω)) =
      horizontalMollify (scaledKernel (d := d) ε) F ω := by
  have hε0 : ε ≠ 0 := hε.ne'
  have hpos : 0 < (ε ^ d)⁻¹ := inv_pos.mpr (pow_pos hε d)
  have hfr : Module.finrank ℝ (Vec d) = d := Module.finrank_fin_fun ℝ
  have hkernel : ∀ x : Vec d, scaledKernel (d := d) ε (ε • x) = (ε ^ d)⁻¹ * mollifier d x := by
    intro x
    unfold scaledKernel
    rw [smul_smul, inv_mul_cancel₀ hε0, one_smul]
  have hJ : (∫ x : Vec d, scaledKernel (d := d) ε (ε • x) * F (translate (ε • x) ω)) =
      (ε ^ d)⁻¹ * ∫ x : Vec d, mollifier d x * F (translate (ε • x) ω) := by
    rw [← integral_const_mul]
    congr 1
    funext x
    rw [hkernel x, mul_assoc]
  have hscale : (∫ x : Vec d, scaledKernel (d := d) ε (ε • x) * F (translate (ε • x) ω)) =
      |(ε ^ d)⁻¹| • ∫ y : Vec d, scaledKernel (d := d) ε y * F (translate y ω) := by
    have h := Measure.integral_comp_smul (volume : Measure (Vec d))
      (fun y : Vec d => scaledKernel (d := d) ε y * F (translate y ω)) ε
    rw [hfr] at h
    exact h
  rw [hJ, abs_of_pos hpos, smul_eq_mul] at hscale
  unfold horizontalMollify
  exact mul_left_cancel₀ hpos.ne' hscale

/-- The literal scaled-orbit scalar integral is a horizontal core for every `ε > 0`: it equals the
horizontal smoothing of the dilated kernel `κ_ε`, which is smooth with compact support. Source
`paper/main.tex:545–566`. No continuity of `F` is assumed. -/
theorem isHorizontalTest_scaled_mollifier : ∀ {d : ℕ} {F : FieldPair d → ℝ},
    Measurable F → (∃ M : ℝ, ∀ ω, |F ω| ≤ M) → ∀ ε : ℝ, 0 < ε →
    IsHorizontalTest (fun ω => ∫ x : Vec d, mollifier d x * F (translate (ε • x) ω)) := by
  intro d F hF hb ε hε
  have key := isHorizontalTest_horizontalMollify (d := d) (scaledKernel (d := d) ε)
    (contDiff_scaledKernel (d := d) ε) (hasCompactSupport_scaledKernel (d := d) hε.ne') F hF hb
  have heq : (fun ω : FieldPair d => ∫ x : Vec d, mollifier d x * F (translate (ε • x) ω)) =
      horizontalMollify (scaledKernel (d := d) ε) F :=
    funext fun ω => integral_scaledMollifier_eq_horizontalMollify F hε ω
  rw [← heq] at key
  exact key

end EinsteinRelation.Correctors
