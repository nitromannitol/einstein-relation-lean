import EinsteinFull.External.DFGW.UniformMartingaleApproximation
import EinsteinFull.External.DFGW.ScaledBlockMoments
import EinsteinFull.External.DFGW.DyadicBlockModulus
import EinsteinFull.External.DFGW.IncrementL2

/-! # Moduli of continuity of the diffusively rescaled increments

At the scales `(n + 1) ^ (-1 / 2)`, every projection of the rescaled continuous increment path has,
with probability close to one uniformly in large `n`, a small oscillation at a fixed dyadic scale
on `[0, 1]`. The oscillation over dyadic blocks splits into a block oscillation of the
approximating stationary-increment martingale and the uniformly negligible remainder of the
martingale approximation; continuity of the paths passes from dyadic points to all times.
-/

open MeasureTheory ProbabilityTheory Filter EinsteinRelation
open scoped NNReal ENNReal Topology

namespace EinsteinFull.External.DFGW

/-- Scaling commutes with the block and dyadic structure of times. -/
theorem mul_nsmul_add_dyadicGridTime (c δ : ℝ≥0) (j r k : ℕ) :
    c * (j • δ + dyadicGridTime δ r k) = j • (c * δ) + dyadicGridTime (c * δ) r k := by
  apply NNReal.eq
  simp only [NNReal.coe_mul, NNReal.coe_add, nsmul_eq_mul, coe_dyadicGridTime,
    NNReal.coe_natCast]
  ring

/-- A dyadic point of a block of `[0, n + 1]` is a dyadic point of `[0, n + 1]`. -/
theorem nsmul_blockStep_add_dyadicGridTime (n a j r k : ℕ) :
    j • blockStep n a + dyadicGridTime (blockStep n a) r k =
      dyadicGridTime ((n + 1 : ℕ) : ℝ≥0) (a + r) (j * 2 ^ r + k) := by
  apply NNReal.eq
  simp only [NNReal.coe_add, nsmul_eq_mul, NNReal.coe_mul, NNReal.coe_natCast,
    coe_dyadicGridTime, coe_blockStep]
  push_cast
  rw [pow_add]
  field_simp

/-- The left endpoint of a block of `[0, n + 1]` is a dyadic point of `[0, n + 1]`. -/
theorem nsmul_blockStep (n a j : ℕ) :
    j • blockStep n a = dyadicGridTime ((n + 1 : ℕ) : ℝ≥0) a j := by
  apply NNReal.eq
  simp only [nsmul_eq_mul, NNReal.coe_mul, NNReal.coe_natCast, coe_dyadicGridTime,
    coe_blockStep]
  push_cast
  ring

variable {S : Type} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {d : ℕ} {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}
variable {X : ℝ → ℝ → C(ℝ, S) → Vec d} {Y : C(ℝ, S) → Path d}

/-- **Modulus of continuity at the scales `(n + 1) ^ (-1 / 2)`.** For every projection and all
`ρ, κ > 0` there is a dyadic scale `2 ^ (-a)` such that, for all large `n`, the probability that
the projected rescaled path oscillates by more than `ρ` at scale `2 ^ (-a)` on `[0, 1]` is at most
`κ`. -/
theorem exists_level_measureReal_oscillation_le
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
    (e : Vec d) {ρ κ : ℝ} (hρ : 0 < ρ) (hκ : 0 < κ) :
    ∃ a : ℕ, ∀ᶠ n : ℕ in atTop, P.real {η | ∃ s t : ℝ≥0, s ≤ 1 ∧ t ≤ 1 ∧
      |(s : ℝ) - t| ≤ (2 ^ a : ℝ)⁻¹ ∧
      ρ < |dot e (rescalePath (Real.sqrt (n + 1))⁻¹ (Y η) s) -
        dot e (rescalePath (Real.sqrt (n + 1))⁻¹ (Y η) t)|} ≤ κ := by
  let : IsProbabilityMeasure P := hP.probability
  obtain ⟨m, hm, hm2, hstat, hremX, hunif⟩ :=
    exists_projected_martingale_approximation_uniform hP hcoord hX φ hφ hlim hL2 hM e
  let y : ℝ≥0 → C(ℝ, S) → ℝ := fun t η => dot e (Y η t)
  have hyX (t : ℝ≥0) : y t =ᵐ[P] fun η => dot e (X 0 t η) := by
    filter_upwards [hX.version] with η hη
    simp only [y, hη t]
  have hy2 (t : ℝ≥0) : MemLp (y t) 2 P :=
    (memLp_congr_ae (hyX t)).2 (increment_dot_memLp hP φ hφ t (hL2 t) e)
  have hremY : Tendsto (fun t : ℝ≥0 => (t : ℝ)⁻¹ * ∫ η, (y t η - m t η) ^ 2 ∂P) atTop
      (𝓝 0) := by
    apply hremX.congr'
    filter_upwards with t
    congr 1
    apply integral_congr_ae
    filter_upwards [hyX t] with η hη
    rw [hη]
  -- the Gaussian comparison law
  have hσ : 0 ≤ dot e (D.mulVec e) := hW.2.2.1 e
  let ν : Measure ℝ := gaussianReal 0 (dot e (D.mulVec e)).toNNReal
  have hν : Integrable (fun x : ℝ => x ^ 2) ν := (memLp_id_gaussianReal 2).integrable_sq
  have hνs : ∫ x, x ^ 2 ∂ν = dot e (D.mulVec e) := by
    have h := variance_of_integral_eq_zero (μ := ν) (X := id) aemeasurable_id
      (integral_id_gaussianReal (μ := 0) (v := (dot e (D.mulVec e)).toNNReal))
    rw [variance_id_gaussianReal, Real.coe_toNNReal _ hσ] at h
    simpa using h.symm
  have hmean (a : ℕ) := tendsto_integral_dot_blockStep_sq Y e (hsec e) a
  have hmin (a : ℕ) (Λ : ℝ) := tendsto_integral_min_dot_blockStep_sq Y hW hfdd e a Λ
  obtain ⟨a, ha⟩ := exists_level_measureReal_martingale_blocks_le hP m hm hm2 hstat y hy2 ν
    hν (dot e (D.mulVec e)) hνs hmean hmin hremY (c := ρ / 6) (κ := κ / 2) (by positivity)
    (by positivity)
  have hR := hunif (ρ / 12) (by positivity)
  refine ⟨a, ?_⟩
  filter_upwards [ha, hR.eventually (gt_mem_nhds (show (0 : ℝ) < κ / 2 by positivity))] with
    n hn1 hn2
  -- the oscillation event lies in the union of a martingale block event and a remainder event
  set ε : ℝ := (Real.sqrt (n + 1))⁻¹ with hε
  have hsqrt : 0 < Real.sqrt ((n : ℝ) + 1) := Real.sqrt_pos.2 (by positivity)
  let h : ℝ≥0 := blockStep n a
  let Mset : Set C(ℝ, S) := {η | ∃ j < 2 ^ a, ∃ r k, k ≤ 2 ^ r ∧
    ρ / 6 * Real.sqrt (n + 1) ≤ |m (j • h + dyadicGridTime h r k) η - m (j • h) η|}
  let Rset : Set C(ℝ, S) := {η | ∃ r k, k ≤ 2 ^ r ∧ ρ / 12 * Real.sqrt (n + 1) ≤
    |dot e (Y η (dyadicGridTime ((n + 1 : ℕ) : ℝ≥0) r k)) -
      m (dyadicGridTime ((n + 1 : ℕ) : ℝ≥0) r k) η|}
  have hsub : {η | ∃ s t : ℝ≥0, s ≤ 1 ∧ t ≤ 1 ∧ |(s : ℝ) - t| ≤ (2 ^ a : ℝ)⁻¹ ∧
      ρ < |dot e (rescalePath ε (Y η) s) - dot e (rescalePath ε (Y η) t)|} ⊆
      Mset ∪ Rset := by
    rintro η ⟨s, t, hs, ht, hst, hbig⟩
    by_contra hnot
    simp only [Set.mem_union, not_or] at hnot
    obtain ⟨hnM, hnR⟩ := hnot
    let z : ℝ≥0 → ℝ := fun u => dot e (rescalePath ε (Y η) u)
    have hz : Continuous z := by
      have hdotc : Continuous fun v : Vec d => dot e v := by
        unfold dot
        exact continuous_finsetSum _ fun i _ => continuous_const.mul (continuous_apply i)
      exact hdotc.comp (rescalePath ε (Y η)).continuous
    have hdot (v : Vec d) (c : ℝ) : dot e (c • v) = c * dot e v := by
      simp only [dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    have hscale : ((ε⁻¹ ^ 2).toNNReal * ((2 : ℝ≥0) ^ a)⁻¹) = h :=
      scale_mul_dyadic_eq_blockStep n a
    have hblocks : ∀ j < 2 ^ a, ∀ r k : ℕ, k ≤ 2 ^ r →
        |z (j • ((2 : ℝ≥0) ^ a)⁻¹ + dyadicGridTime ((2 : ℝ≥0) ^ a)⁻¹ r k) -
          z (j • ((2 : ℝ≥0) ^ a)⁻¹)| ≤ ρ / 3 := by
      intro j hj r k hk
      have hzA : z (j • ((2 : ℝ≥0) ^ a)⁻¹ + dyadicGridTime ((2 : ℝ≥0) ^ a)⁻¹ r k) =
          ε * y (j • h + dyadicGridTime h r k) η := by
        change dot e (ε • Y η ((ε⁻¹ ^ 2).toNNReal *
          (j • ((2 : ℝ≥0) ^ a)⁻¹ + dyadicGridTime ((2 : ℝ≥0) ^ a)⁻¹ r k))) = _
        rw [mul_nsmul_add_dyadicGridTime, hscale, hdot]
      have hzB : z (j • ((2 : ℝ≥0) ^ a)⁻¹) = ε * y (j • h) η := by
        change dot e (ε • Y η ((ε⁻¹ ^ 2).toNNReal * (j • ((2 : ℝ≥0) ^ a)⁻¹))) = _
        rw [show (ε⁻¹ ^ 2).toNNReal * (j • ((2 : ℝ≥0) ^ a)⁻¹) = j • h by
          rw [← hscale, nsmul_eq_mul, nsmul_eq_mul]
          ring, hdot]
      rw [hzA, hzB, ← mul_sub, abs_mul, abs_of_pos (inv_pos.2 hsqrt)]
      -- the martingale part
      have hmA : |m (j • h + dyadicGridTime h r k) η - m (j • h) η| <
          ρ / 6 * Real.sqrt (n + 1) := by
        apply lt_of_not_ge
        intro hge
        exact hnM ⟨j, hj, r, k, hk, hge⟩
      have hkA : j * 2 ^ r + k ≤ 2 ^ (a + r) := by
        rw [pow_add]
        have : j + 1 ≤ 2 ^ a := hj
        nlinarith [Nat.one_le_two_pow (n := r)]
      have hrA : |y (j • h + dyadicGridTime h r k) η - m (j • h + dyadicGridTime h r k) η| <
          ρ / 12 * Real.sqrt (n + 1) := by
        apply lt_of_not_ge
        intro hge
        apply hnR
        refine ⟨a + r, j * 2 ^ r + k, hkA, ?_⟩
        rw [← nsmul_blockStep_add_dyadicGridTime]
        exact hge
      have hrB : |y (j • h) η - m (j • h) η| < ρ / 12 * Real.sqrt (n + 1) := by
        apply lt_of_not_ge
        intro hge
        apply hnR
        refine ⟨a, j, hj.le, ?_⟩
        rw [← nsmul_blockStep]
        exact hge
      have htri : |y (j • h + dyadicGridTime h r k) η - y (j • h) η| ≤
          |m (j • h + dyadicGridTime h r k) η - m (j • h) η| +
            |y (j • h + dyadicGridTime h r k) η - m (j • h + dyadicGridTime h r k) η| +
            |y (j • h) η - m (j • h) η| := by
        have e1 : y (j • h + dyadicGridTime h r k) η - y (j • h) η =
            (m (j • h + dyadicGridTime h r k) η - m (j • h) η) +
              (y (j • h + dyadicGridTime h r k) η - m (j • h + dyadicGridTime h r k) η) -
              (y (j • h) η - m (j • h) η) := by ring
        rw [e1]
        calc
          _ ≤ |(m (j • h + dyadicGridTime h r k) η - m (j • h) η) +
              (y (j • h + dyadicGridTime h r k) η - m (j • h + dyadicGridTime h r k) η)| +
              |y (j • h) η - m (j • h) η| := abs_sub _ _
          _ ≤ _ := by gcongr; exact abs_add_le _ _
      rw [inv_mul_le_iff₀ hsqrt]
      have : ρ / 3 * Real.sqrt (n + 1) = ρ / 6 * Real.sqrt (n + 1) +
          ρ / 12 * Real.sqrt (n + 1) + ρ / 12 * Real.sqrt (n + 1) := by ring
      nlinarith
    have hosc := abs_sub_le_of_dyadic_blocks hz a hblocks hs ht hst
    change ρ < |z s - z t| at hbig
    linarith
  calc
    _ ≤ P.real (Mset ∪ Rset) := measureReal_mono hsub
    _ ≤ P.real Mset + P.real Rset := measureReal_union_le _ _
    _ ≤ κ / 2 + κ / 2 := add_le_add hn1 hn2.le
    _ = κ := by ring

end EinsteinFull.External.DFGW
