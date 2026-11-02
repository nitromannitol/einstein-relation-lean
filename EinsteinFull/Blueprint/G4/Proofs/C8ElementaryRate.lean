import EinsteinFull.Blueprint.G4.node_t_u2E_main_u23_elementary_u2D_rate

namespace EinsteinFull.Blueprint

/-- The logarithmic critical scale is bounded by a first-order rate, uniformly
in the dimension. This is the scalar estimate in `paper/main.tex:1431–1433`. -/
theorem elementaryRate_log_bound {d : ℕ} (hd : 2 ≤ d) {s : ℝ}
    (hs : 0 < s) (hs1 : s ≤ 1) :
    s ^ d * (1 + Real.log (1 / s)) ≤ 2 * s := by
  have hlog : 0 ≤ Real.log (1 / s) :=
    Real.log_nonneg ((le_div_iff₀ hs).2 (by simpa using hs1))
  have hlog_upper := Real.log_le_sub_one_of_pos (one_div_pos.mpr hs)
  have hmul : s * Real.log (1 / s) ≤ 1 := by
    have h := mul_le_mul_of_nonneg_left hlog_upper hs.le
    have hid : s * (1 / s - 1) = 1 - s := by field_simp [hs.ne']
    rw [hid] at h
    linarith
  calc
    s ^ d * (1 + Real.log (1 / s)) ≤
        s ^ 2 * (1 + Real.log (1 / s)) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hs.le hs1 hd) (by linarith)
    _ = s * (s + s * Real.log (1 / s)) := by ring
    _ ≤ s * (1 + 1) := mul_le_mul_of_nonneg_left (add_le_add hs1 hmul) hs.le
    _ = 2 * s := by ring

/-- The explicit expansion modulus is at most one on its stated domain. -/
theorem elementaryRate_modulus_le_one {s : ℝ} (hs : 0 < s)
    (hsmall : s ≤ Real.exp (-1)) : expansionModulus s hs hsmall ≤ 1 := by
  unfold expansionModulus
  exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (Real.sqrt_nonneg _))

/-- The critical kernel contributes at most twice the force magnitude. -/
theorem elementaryRate_critical_bound {d : ℕ} (hd : 2 ≤ d) {lam : ℝ}
    (hlam : lam ≠ 0) (hsmall : |lam| ≤ 1) :
    |criticalKernelTerm d lam hlam| ≤ 2 * |lam| := by
  have hpos := abs_pos.mpr hlam
  have hlog : 0 ≤ Real.log (1 / |lam|) :=
    Real.log_nonneg ((le_div_iff₀ hpos).2 (by simpa using hsmall))
  have hbound := elementaryRate_log_bound hd hpos hsmall
  unfold criticalKernelTerm
  split_ifs
  · rw [abs_mul, abs_pow, abs_of_nonneg hlog]
    nlinarith [pow_nonneg (abs_nonneg lam) d]
  · rw [abs_of_nonneg (pow_nonneg (abs_nonneg lam) d)]
    nlinarith [mul_nonneg (pow_nonneg (abs_nonneg lam) d) hlog]

end EinsteinFull.Blueprint
