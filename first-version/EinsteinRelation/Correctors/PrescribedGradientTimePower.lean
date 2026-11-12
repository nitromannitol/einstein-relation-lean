import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace EinsteinRelation.Correctors

/-- Conversion from the diffusive radius to the prescribed time.
Source: `paper/main.tex:798–806`. -/
theorem prescribed_decay_radius_to_time {C r : ℝ} (hr : 0 < r) (a : ℝ) :
    C/r * (r^2)^a = (C * (3 : ℝ)^(1/2-a)) *
      (3*r^2)^(a-1/2) := by
  have hpow : (3 : ℝ)^(1/2-a) * 3^(a-1/2) = 1 := by
    rw [← Real.rpow_add (by norm_num), show (1/2-a)+(a-1/2) = 0 by ring,
      Real.rpow_zero]
  calc
    C/r * (r^2)^a = C * (r^2)^(a-1/2) := by
      rw [Real.rpow_sub (sq_pos_of_pos hr), ← Real.sqrt_eq_rpow, Real.sqrt_sq hr.le]
      ring
    _ = C * ((3 : ℝ)^(1/2-a)*3^(a-1/2)) * (r^2)^(a-1/2) := by rw [hpow,mul_one]
    _ = _ := by rw [Real.mul_rpow (by norm_num) (sq_nonneg r)]; ring

end EinsteinRelation.Correctors
