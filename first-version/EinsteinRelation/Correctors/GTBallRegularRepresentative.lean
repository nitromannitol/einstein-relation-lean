import EinsteinRelation.Correctors.GTRegularCoefficientSupport
import EinsteinRelation.Correctors.AffineWeakSolution
import EinsteinRelation.Calculus.WeakRepresentativeOperations

/-! Source: `paper/main.tex:694-704,735-737`. Interior regularity
produces continuous representatives of the scalar corrector on every
positive Euclidean ball, with the actual coefficient and weak gradient. -/

open MeasureTheory

namespace EinsteinRelation.Correctors
open External.AKM External.GilbargTrudinger

private theorem le_mul_sqrt_of_le {t D : ℝ} (ht : 0 ≤ t) (hD : t ≤ D) :
    t ≤ (D + 1) * Real.sqrt t := by
  have hs := Real.sq_sqrt ht
  have hpos := mul_nonneg (Real.sqrt_nonneg t) (sq_nonneg (Real.sqrt t - 1))
  have h : t ≤ (t + 1) * Real.sqrt t := by nlinarith only [hs, hpos]
  exact h.trans (mul_le_mul_of_nonneg_right (by linarith only [hD]) (Real.sqrt_nonneg t))

/-- Bounded Lipschitz coefficients have a bounded half-Hölder norm on
every Euclidean ball. The radius dependence is explicit. -/
theorem holderBound_half_ball_of_isElliptic_lipschitz {d : ℕ}
    {a : Vec d → Mat d} {B A R : ℝ} (hB : 0 < B) (hA : 0 ≤ A)
    (hR : 0 < R) (ha : IsElliptic B a) (hlip : IsOperatorLipschitz A a)
    (i j : Fin d) :
    HolderBound (ball 0 (2 * R)) (1 / 2) (fun x => a x i j)
      (B + A * (4 * R + 1)) := by
  refine ⟨B, A * (4 * R + 1), hB.le, by positivity, le_rfl,
    fun x _ => IsElliptic.entry_abs_le hB ha x i j, ?_⟩
  intro x hx y hy
  have hn : euclideanNorm (-y) = euclideanNorm y := by
    rw [TimeChange.euclideanNorm_eq_norm_toLp, TimeChange.euclideanNorm_eq_norm_toLp]
    exact norm_neg _
  have ht : euclideanNorm (x - y) ≤ 4 * R := by
    have h := TimeChange.euclideanNorm_add_le x (-y)
    rw [hn] at h
    change euclideanNorm (x - 0) < 2 * R at hx
    change euclideanNorm (y - 0) < 2 * R at hy
    simp only [sub_zero] at hx hy
    change euclideanNorm (x - y) ≤ euclideanNorm x + euclideanNorm y at h
    linarith only [h, hx, hy]
  have hs : euclideanNorm (x - y) ≤
      (4 * R + 1) * euclideanNorm (x - y) ^ (1 / (2 : ℝ)) := by
    rw [← Real.sqrt_eq_rpow]
    exact le_mul_sqrt_of_le (Real.sqrt_nonneg _) ht
  calc
    |a x i j - a y i j| ≤ A * euclideanNorm (x - y) := hlip.entry_bound i j x y
    _ ≤ A * ((4 * R + 1) * euclideanNorm (x - y) ^ (1 / (2 : ℝ))) :=
      mul_le_mul_of_nonneg_left hs hA
    _ = _ := by ring

/-- The full local affine representative retains the regular gradient from
GT, so its physical flux can also be used as a Hölder Poisson source. -/
theorem exists_c1Alpha_affine_corrector_ball_of_gt
    (h836 : InteriorRegularRepresentative)
    {d : ℕ} (hd : 2 ≤ d) (a : Vec d → Mat d) (B A R : ℝ)
    (hB : 0 < B) (hA : 0 ≤ A) (hR : 0 < R)
    (ha : IsElliptic B a) (hlip : IsOperatorLipschitz A a)
    (i : Fin d) (u : Vec d → ℝ) (g : Vec d → Vec d)
    (hu : MemLp u 2 (volume.restrict (ball 0 (2 * R))))
    (hg : MemLp g 2 (volume.restrict (ball 0 (2 * R))))
    (hw : HasWeakGradient (ball 0 (2 * R)) u g)
    (hdiv : HasWeakDivergence (ball 0 (2 * R))
      (fun x => (a x).mulVec (unitVector i + g x)) (fun _ => 0)) :
    ∃ (v : Vec d → ℝ) (h : Vec d → Vec d),
      C1Alpha (ball 0 R) (1 / 2) v h ∧
      v =ᵐ[volume.restrict (ball 0 R)] (fun x => x i + u x) ∧
      h =ᵐ[volume.restrict (ball 0 R)] (fun x => unitVector i + g x) := by
  exact h836 d hd B⁻¹ (B + A * (4 * R + 1)) (1 / 2) R
    (inv_pos.mpr hB) (by positivity) (by norm_num) (by norm_num) hR a
    (fun x _ ξ => ((ha x).2 ξ).1)
    (holderBound_half_ball_of_isElliptic_lipschitz hB hA hR ha hlip)
    (fun x => x i + u x) (fun x => unitVector i + g x)
    (affine_weakSolution_of_weakPotential (2 * R) (by positivity)
      i a u g hu hg hw hdiv)

/-- The homogeneous GT input provides a continuous version of a scalar
corrector on an arbitrary ball. Its a.e. equality preserves its gauge. -/
theorem exists_continuousOn_scalar_corrector_ball_of_gt
    (h836 : InteriorRegularRepresentative)
    {d : ℕ} (hd : 2 ≤ d) (a : Vec d → Mat d) (B A R : ℝ)
    (hB : 0 < B) (hA : 0 ≤ A) (hR : 0 < R)
    (ha : IsElliptic B a) (hlip : IsOperatorLipschitz A a)
    (i : Fin d) (u : Vec d → ℝ) (g : Vec d → Vec d)
    (hu : MemLp u 2 (volume.restrict (ball 0 (2 * R))))
    (hg : MemLp g 2 (volume.restrict (ball 0 (2 * R))))
    (hw : HasWeakGradient (ball 0 (2 * R)) u g)
    (hdiv : HasWeakDivergence (ball 0 (2 * R))
      (fun x => (a x).mulVec (unitVector i + g x)) (fun _ => 0)) :
    ∃ v : Vec d → ℝ, ContinuousOn v (ball 0 R) ∧
      u =ᵐ[volume.restrict (ball 0 R)] v := by
  have hK : 0 < B + A * (4 * R + 1) := by positivity
  obtain ⟨v, h, hv, heq, _⟩ := h836 d hd B⁻¹ _ (1 / 2) R
    (inv_pos.mpr hB) hK (by norm_num) (by norm_num) hR a
    (fun x _ ξ => ((ha x).2 ξ).1)
    (holderBound_half_ball_of_isElliptic_lipschitz hB hA hR ha hlip)
    (fun x => x i + u x) (fun x => unitVector i + g x)
    (affine_weakSolution_of_weakPotential (2 * R) (by positivity)
      i a u g hu hg hw hdiv)
  refine ⟨fun x => v x - x i, ?_, ?_⟩
  · have hc : ContinuousOn v (ball 0 R) :=
      fun x hx => (hv.1 x hx).continuousAt.continuousWithinAt
    exact hc.sub (continuous_apply i).continuousOn
  · filter_upwards [heq] with x hx
    linarith only [hx]

end EinsteinRelation.Correctors
