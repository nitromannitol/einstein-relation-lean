import Homogenization.Sobolev.W1p.BasicLemmas

/-!
# Linear functions

The linear function `x ↦ e · x` is smooth, and its partial derivatives are the coordinates of
`e`.
-/

namespace EinsteinFull.Homogenization

open _root_.Homogenization

variable {d : ℕ}

theorem contDiff_vecDot_left (e : Vec d) : ContDiff ℝ 1 (fun x : Vec d => vecDot e x) := by
  unfold vecDot
  exact ContDiff.sum fun i _ => contDiff_const.mul (contDiff_apply ℝ ℝ i)

theorem fderiv_vecDot_left_apply (e : Vec d) (x : Vec d) (i : Fin d) :
    fderiv ℝ (fun y : Vec d => vecDot e y) x (basisVec i) = e i := by
  have hlin : (fun y : Vec d => vecDot e y) =
      fun y => (∑ j : Fin d, e j • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) j)
        y := by
    funext y
    simp [vecDot, smul_eq_mul]
  rw [hlin, ContinuousLinearMap.fderiv]
  simp [basisVec, Pi.single_apply, smul_eq_mul]

end EinsteinFull.Homogenization
