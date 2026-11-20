import EinsteinFull.External.DFGW.TrajectoryEmpiricalAverage

/-! # Deterministic scaling of convergence in measure

Convergence in measure to a constant is preserved by multiplication by a convergent
deterministic scalar sequence.
-/

open MeasureTheory Filter
open scoped ENNReal Topology

namespace EinsteinFull.External.DFGW

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]

/-- Multiplying by convergent deterministic scalars preserves convergence in measure to a
constant. -/
theorem tendstoInMeasure_mul_const_sequence (X : ℕ → Ω → ℝ) (a : ℝ) (c : ℕ → ℝ) (b : ℝ)
    (hX : TendstoInMeasure P X atTop (fun _ => a)) (hc : Tendsto c atTop (𝓝 b)) :
    TendstoInMeasure P (fun n ω => c n * X n ω) atTop (fun _ => b * a) := by
  apply tendstoInMeasure_iff_measureReal_norm.2
  intro ε hε
  let K : ℝ := |b| + 1
  have hK : 0 < K := by dsimp [K]; positivity
  let δ : ℝ := ε / (2 * K)
  have hδ : 0 < δ := div_pos hε (by positivity)
  have hsmall := (tendstoInMeasure_iff_measureReal_norm.1 hX) δ hδ
  have hbound : ∀ᶠ n in atTop, |c n| ≤ K := by
    have h := (Metric.tendsto_nhds.mp hc) 1 (by norm_num)
    filter_upwards [h] with n hn
    rw [Real.dist_eq] at hn
    dsimp [K]
    have ht := abs_add_le (c n - b) b
    have heq : c n - b + b = c n := by ring
    rw [heq] at ht
    linarith
  have herror : ∀ᶠ n in atTop, |(c n - b) * a| < ε / 2 := by
    have ht : Tendsto (fun n => (c n - b) * a) atTop (𝓝 0) := by
      simpa using (hc.sub (tendsto_const_nhds : Tendsto (fun _ : ℕ => b) atTop (𝓝 b))).mul_const a
    have h := (Metric.tendsto_nhds.mp ht) (ε / 2) (by positivity)
    filter_upwards [h] with n hn
    simpa only [Real.dist_eq, sub_zero] using hn
  apply squeeze_zero' (Filter.Eventually.of_forall fun _ => measureReal_nonneg) _ hsmall
  filter_upwards [hbound, herror] with n hn he
  apply measureReal_mono _ (measure_ne_top P _)
  intro ω hω
  simp only [Set.mem_ofPred_eq, Real.norm_eq_abs] at hω ⊢
  by_contra hnot
  have hx : |X n ω - a| < δ := lt_of_not_ge hnot
  have hid : c n * X n ω - b * a = c n * (X n ω - a) + (c n - b) * a := by ring
  have habs := abs_add_le (c n * (X n ω - a)) ((c n - b) * a)
  rw [← hid, abs_mul] at habs
  have hmul : |c n| * |X n ω - a| < ε / 2 := by
    have := mul_le_mul_of_nonneg_right hn (abs_nonneg (X n ω - a))
    have := mul_lt_mul_of_pos_left hx hK
    dsimp [δ] at this
    have hk : K * (ε / (2 * K)) = ε / 2 := by field_simp
    linarith
  linarith

end EinsteinFull.External.DFGW
