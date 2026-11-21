import EinsteinFull.External.DFGW.DiffusiveModulus

/-! # Moduli of continuity at all small diffusive scales

The modulus of continuity proved along the scales `(n + 1) ^ (-1 / 2)` on `[0, 1]` transfers to
every small scale `ε` and every horizon `T ≥ 1`: on `[0, T]`, the path rescaled by `ε` is, up to a
factor at most `√(T + 2)` and a time change contracting distances, the path rescaled by
`(m + 1) ^ (-1 / 2)` on `[0, 1]`, with `m = ⌈ε⁻² T⌉`.
-/

open MeasureTheory ProbabilityTheory Filter EinsteinRelation
open scoped NNReal ENNReal Topology

namespace EinsteinFull.External.DFGW

/-- The diffusive time factor of the scale `(m + 1) ^ (-1 / 2)` is `m + 1`. -/
theorem toNNReal_inv_inv_sqrt_succ_sq (m : ℕ) :
    (((Real.sqrt (m + 1))⁻¹)⁻¹ ^ 2).toNNReal = ((m + 1 : ℕ) : ℝ≥0) := by
  apply NNReal.eq
  rw [Real.coe_toNNReal _ (sq_nonneg _), inv_inv, Real.sq_sqrt (by positivity)]
  push_cast
  ring

variable {S : Type} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {d : ℕ} {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}
variable {X : ℝ → ℝ → C(ℝ, S) → Vec d} {Y : C(ℝ, S) → Path d}

/-- **Modulus of continuity at small scales.** For every projection, horizon `T ≥ 1` and
`ρ, κ > 0` there are `δ > 0` and `ε₁ ∈ (0, 1]` such that for every `ε ∈ (0, ε₁]` the probability
that the projected rescaled path oscillates by more than `ρ` at scale `δ` on `[0, T]` is at most
`κ`. -/
theorem exists_scale_measureReal_oscillation_le
    (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (hcoord : Draft.dfgwCoordSigma (S := S) Set.univ =
      Draft.dfgwTrajectoryMeasurableSpace (S := S))
    (hX : Draft.IsDFGWTrajectoryFamily P X Y) (φ : S → Vec d) (hφ : MemLp φ 2 μ)
    (hlim : Tendsto (fun δ : ℝ =>
      ∫ η, ‖δ⁻¹ • (P[X 0 δ | Draft.dfgwCoordSigma (Set.Iic 0)]) η - φ (η 0)‖ ∂P)
      (𝓝[>] 0) (𝓝 0))
    (hL2 : ∀ t, MemLp (compensated X φ t) 2 P)
    (hM : Martingale (compensated X φ) Draft.dfgwPast P)
    {D : Mat d} {W : Measure (Path d)} (hW : IsBrownianLaw D W)
    (hsec : ∀ (e : Vec d) (t : ℝ≥0), Tendsto
      (fun ε : ℝ => ∫ η, dot e (ε • Y η ((ε⁻¹ ^ 2).toNNReal * t)) ^ 2 ∂P)
      (𝓝[>] 0) (𝓝 (dot e (D.mulVec e) * t)))
    (hfdd : ∀ (m : ℕ) (t : Fin m → ℝ≥0),
      letI : IsProbabilityMeasure P := hP.probability
      letI : IsProbabilityMeasure W := hW.1
      TendstoInDistribution (fun (ε : ℝ) η j => ε • Y η ((ε⁻¹ ^ 2).toNNReal * t j))
        (𝓝[>] 0) (fun γ : Path d => fun j => γ (t j)) (fun _ => P) W)
    (e : Vec d) {L ρ κ : ℝ} (hL : 1 ≤ L) (hρ : 0 < ρ) (hκ : 0 < κ) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ ε₁ : ℝ, 0 < ε₁ ∧ ε₁ ≤ 1 ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₁ →
      P.real {η | ∃ s t : ℝ≥0, (s : ℝ) ≤ L ∧ (t : ℝ) ≤ L ∧ |(s : ℝ) - t| ≤ δ ∧
        ρ < |dot e (rescalePath ε (Y η) s) - dot e (rescalePath ε (Y η) t)|} ≤ κ := by
  let : IsProbabilityMeasure P := hP.probability
  have hL2' : 0 < Real.sqrt (L + 2) := Real.sqrt_pos.2 (by linarith)
  obtain ⟨a, ha⟩ := exists_level_measureReal_oscillation_le hP hcoord hX φ hφ hlim hL2 hM hW
    hsec hfdd e (ρ := ρ / Real.sqrt (L + 2)) (κ := κ) (by positivity) hκ
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 ha
  have hLpos : 0 < L := by linarith
  let ε₁ : ℝ := min 1 (Real.sqrt (L / (n₀ + 1)))
  have hε₁ : 0 < ε₁ := lt_min one_pos (Real.sqrt_pos.2 (by positivity))
  refine ⟨(2 ^ a : ℝ)⁻¹, by positivity, ε₁, hε₁, min_le_left _ _, fun ε hε hεε₁ => ?_⟩
  have hε1 : ε ≤ 1 := hεε₁.trans (min_le_left _ _)
  set c : ℝ := ε⁻¹ ^ 2 with hc
  have hcpos : 0 < c := by positivity
  have hcε : ε ^ 2 * c = 1 := by
    rw [hc, inv_pow, mul_inv_cancel₀ (by positivity)]
  let m : ℕ := ⌈c * L⌉₊
  have hm1 : c * L ≤ m := Nat.le_ceil _
  have hm2 : (m : ℝ) < c * L + 1 := Nat.ceil_lt_add_one (by positivity)
  have hn₀m : n₀ ≤ m := by
    have hε2 : ε ^ 2 ≤ L / (n₀ + 1) := by
      have h := hεε₁.trans (min_le_right _ _)
      have h2 := pow_le_pow_left₀ hε.le h 2
      rwa [Real.sq_sqrt (by positivity)] at h2
    have hn : (n₀ : ℝ) + 1 ≤ c * L := by
      rw [le_div_iff₀ (by positivity)] at hε2
      have h3 : ((n₀ : ℝ) + 1) * (ε ^ 2 * c) ≤ L * c := by
        have := mul_le_mul_of_nonneg_right hε2 hcpos.le
        linarith
      rw [hcε, mul_one] at h3
      linarith
    have : (n₀ : ℝ) ≤ m := by linarith
    exact_mod_cast this
  refine (measureReal_mono ?_).trans (hn₀ m hn₀m)
  rintro η ⟨s, t, hs, ht, hst, hbig⟩
  let N1 : ℝ≥0 := ((m + 1 : ℕ) : ℝ≥0)
  have hN1 : (N1 : ℝ) = m + 1 := by simp [N1]
  have hN1ne : N1 ≠ 0 := by
    intro h0
    have : (N1 : ℝ) = 0 := by rw [h0]; rfl
    rw [hN1] at this
    linarith
  have hu (v : ℝ≥0) : ((c.toNNReal * v / N1 : ℝ≥0) : ℝ) = c * v / (m + 1) := by
    rw [NNReal.coe_div, NNReal.coe_mul, Real.coe_toNNReal _ hcpos.le, hN1]
  have htime (v : ℝ≥0) :
      (((Real.sqrt (m + 1))⁻¹)⁻¹ ^ 2).toNNReal * (c.toNNReal * v / N1) = c.toNNReal * v := by
    rw [toNNReal_inv_inv_sqrt_succ_sq]
    exact mul_div_cancel₀ _ hN1ne
  have hdot (v : Vec d) (b : ℝ) : dot e (b • v) = b * dot e v := by
    simp only [dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hzε (v : ℝ≥0) : dot e (rescalePath ε (Y η) v) = ε * dot e (Y η (c.toNNReal * v)) := by
    change dot e (ε • Y η ((ε⁻¹ ^ 2).toNNReal * v)) = _
    rw [hdot]
  have hzm (v : ℝ≥0) : dot e (rescalePath (Real.sqrt (m + 1))⁻¹ (Y η) (c.toNNReal * v / N1)) =
      (Real.sqrt (m + 1))⁻¹ * dot e (Y η (c.toNNReal * v)) := by
    change dot e ((Real.sqrt (m + 1))⁻¹ •
      Y η ((((Real.sqrt (m + 1))⁻¹)⁻¹ ^ 2).toNNReal * (c.toNNReal * v / N1))) = _
    rw [htime, hdot]
  have hmpos : (0 : ℝ) < m + 1 := by positivity
  have hle1 (v : ℝ≥0) (hv : (v : ℝ) ≤ L) : c.toNNReal * v / N1 ≤ 1 := by
    rw [← NNReal.coe_le_coe, hu, NNReal.coe_one, div_le_one hmpos]
    have := mul_le_mul_of_nonneg_left hv hcpos.le
    linarith
  refine ⟨c.toNNReal * s / N1, c.toNNReal * t / N1, hle1 s hs, hle1 t ht, ?_, ?_⟩
  · rw [hu, hu, ← sub_div, ← mul_sub, abs_div, abs_mul, abs_of_pos hcpos, abs_of_pos hmpos,
      div_le_iff₀ hmpos]
    have h1 : c * |(s : ℝ) - t| ≤ c * (2 ^ a : ℝ)⁻¹ := mul_le_mul_of_nonneg_left hst hcpos.le
    have h2 : c ≤ m + 1 := by nlinarith
    have h3 : c * (2 ^ a : ℝ)⁻¹ ≤ (2 ^ a : ℝ)⁻¹ * (m + 1) := by
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_left h2 (by positivity)
    linarith
  · rw [hzm, hzm, ← mul_sub, abs_mul, abs_of_pos (inv_pos.2 (Real.sqrt_pos.2 hmpos))]
    rw [hzε, hzε, ← mul_sub, abs_mul, abs_of_pos hε] at hbig
    set A : ℝ := |dot e (Y η (c.toNNReal * s)) - dot e (Y η (c.toNNReal * t))|
    have hq : 0 < Real.sqrt ((m : ℝ) + 1) := Real.sqrt_pos.2 hmpos
    have hkey : ε * Real.sqrt ((m : ℝ) + 1) ≤ Real.sqrt (L + 2) := by
      rw [show ε = Real.sqrt (ε ^ 2) from (Real.sqrt_sq hε.le).symm,
        ← Real.sqrt_mul (sq_nonneg _)]
      apply Real.sqrt_le_sqrt
      have h4 : ε ^ 2 * ((m : ℝ) + 1) ≤ ε ^ 2 * (c * L + 2) :=
        mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg _)
      have h5 : ε ^ 2 * (c * L + 2) = L + 2 * ε ^ 2 := by
        rw [mul_add, ← mul_assoc, hcε, one_mul]
        ring
      have h6 : ε ^ 2 ≤ 1 := by nlinarith
      linarith
    have hA : 0 ≤ A := abs_nonneg _
    have hstep : ρ * Real.sqrt ((m : ℝ) + 1) < Real.sqrt (L + 2) * A := by
      calc
        ρ * Real.sqrt ((m : ℝ) + 1) < ε * A * Real.sqrt ((m : ℝ) + 1) :=
          mul_lt_mul_of_pos_right hbig hq
        _ = (ε * Real.sqrt ((m : ℝ) + 1)) * A := by ring
        _ ≤ Real.sqrt (L + 2) * A := mul_le_mul_of_nonneg_right hkey hA
    rw [div_lt_iff₀ hL2', inv_mul_eq_div, div_mul_eq_mul_div, lt_div_iff₀ hq]
    linarith

end EinsteinFull.External.DFGW
