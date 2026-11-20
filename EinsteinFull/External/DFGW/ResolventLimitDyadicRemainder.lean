import EinsteinFull.External.DFGW.ResolventDyadicTail
import EinsteinFull.External.DFGW.ResolventPartialIntegralTail
import EinsteinFull.External.DFGW.ResolventDecomposition
import EinsteinFull.External.DFGW.ResolventLimitMartingale
import EinsteinFull.External.DFGW.MartingaleTailMaximal

/-! # Uniform remainder of the Kipnis–Varadhan martingale approximation

The integrated observable minus the limit of the resolvent Dynkin martingales is uniformly
negligible at diffusive scale over all dyadic times of a long interval (source (2.68)). The
remainder splits into the resolvent boundary term, the integrated resolvent term, and the
difference between a resolvent Dynkin martingale and the limit martingale; the last is controlled
by Doob's inequality and the energy convergence of the resolvents.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace EinsteinFull.External.DFGW

variable {S : Type} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- The resolvent Dynkin increments approach their limit uniformly in energy: the squared
distance at time `t` is at most `t` times a quantity tending to zero. -/
theorem exists_norm_dynkinIncrementLp_sub_limit_sq_le
    (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (hcoord : Draft.dfgwCoordSigma (S := S) Set.univ =
      Draft.dfgwTrajectoryMeasurableSpace (S := S))
    (f : Lp ℝ 2 μ)
    (hint : IntegrableOn (fun t : ℝ => inner ℝ f (transitionOperator hP t.toNNReal f))
      (Set.Ioi 0)) (Z : ℝ≥0 → Lp ℝ 2 P)
    (hZ : ∀ t, Tendsto (fun n : ℕ => dynkinIncrementLp hP
      (transitionResolventDomain hP (reciprocalShift n) f) t) atTop (𝓝 (Z t)))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ t : ℝ≥0,
      ‖dynkinIncrementLp hP (transitionResolventDomain hP (reciprocalShift n) f) t - Z t‖ ^ 2 ≤
        (t : ℝ) * (2 * ε) := by
  obtain ⟨N, hN⟩ := resolvent_energy_cauchy hP f hint ε hε
  refine ⟨N, fun n hn t => ?_⟩
  have hlim : Tendsto (fun m : ℕ =>
      ‖dynkinIncrementLp hP (transitionResolventDomain hP (reciprocalShift n) f) t -
        dynkinIncrementLp hP (transitionResolventDomain hP (reciprocalShift m) f) t‖ ^ 2)
      atTop (𝓝 (‖dynkinIncrementLp hP
        (transitionResolventDomain hP (reciprocalShift n) f) t - Z t‖ ^ 2)) :=
    ((tendsto_const_nhds.sub (hZ t)).norm).pow 2
  apply le_of_tendsto hlim
  filter_upwards [eventually_ge_atTop N] with m hm
  rw [norm_dynkinIncrementLp_sub_sq hP hcoord]
  have hE := hN n hn m hm
  dsimp only at hE
  gcongr

/-- Almost surely, the integrated observable minus a resolvent Dynkin increment is the negative
resolvent boundary increment plus the normalized integrated resolvent. -/
theorem ae_time_integral_sub_dynkin_eq (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (f : Lp ℝ 2 μ) (a : MarkovProcess.Semigroup.PositiveShift) (t : ℝ≥0) :
    ∀ᵐ η ∂P, (∫ u in (0 : ℝ)..t, f (η u)) -
        (dynkinProcess hP (transitionResolventDomain hP a f) t η -
          dynkinProcess hP (transitionResolventDomain hP a f) 0 η) =
      -(transitionResolvent hP a f (η t) - transitionResolvent hP a f (η 0)) +
        (a : ℝ) * ∫ u in (0 : ℝ)..t, transitionResolvent hP a f (η u) := by
  let v := transitionResolvent hP a f
  let F := transitionResolventDomain hP a f
  have hL := timeIntegralLp_sub_resolvent_martingale hP f a t
  have hL' : ⇑(timeIntegralLp hP f t - dynkinIncrementLp hP F t) =ᵐ[P]
      ⇑(-(stateEvaluationLp hP v t - stateEvaluationLp hP v 0) +
        (a : ℝ) • timeIntegralLp hP v t) := by
    rw [hL]
  have hf : timeIntegralLp hP f t =ᵐ[P] fun η => ∫ u in (0 : ℝ)..t, f (η u) :=
    MemLp.coeFn_toLp ((time_integral_memLp_and_sq_le hP f (Lp.memLp f) t.coe_nonneg).1)
  have hv : timeIntegralLp hP v t =ᵐ[P] fun η => ∫ u in (0 : ℝ)..t, v (η u) :=
    MemLp.coeFn_toLp ((time_integral_memLp_and_sq_le hP v (Lp.memLp v) t.coe_nonneg).1)
  have hD : dynkinIncrementLp hP F t =ᵐ[P]
      fun η => dynkinProcess hP F t η - dynkinProcess hP F 0 η :=
    MemLp.coeFn_toLp ((dynkinProcess_memLp hP F t).sub (dynkinProcess_memLp hP F 0))
  have hev (s : ℝ≥0) : stateEvaluationLp hP v s =ᵐ[P] fun η => v (η s) :=
    Lp.coeFn_compMeasurePreserving v _
  filter_upwards [hL', hf, hv, hD, hev t, hev 0,
    Lp.coeFn_sub (timeIntegralLp hP f t) (dynkinIncrementLp hP F t),
    Lp.coeFn_add (-(stateEvaluationLp hP v t - stateEvaluationLp hP v 0))
      ((a : ℝ) • timeIntegralLp hP v t),
    Lp.coeFn_neg (stateEvaluationLp hP v t - stateEvaluationLp hP v 0),
    Lp.coeFn_sub (stateEvaluationLp hP v t) (stateEvaluationLp hP v 0),
    Lp.coeFn_smul (a : ℝ) (timeIntegralLp hP v t)] with η h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  simp only [Pi.sub_apply, Pi.add_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul,
    NNReal.coe_zero] at h1 h4 h5 h6 h7 h8 h9 h10 h11
  rw [h7, h8, h9, h10, h11, h2, h3, h4, h5, h6] at h1
  change _ = -(v (η t) - v (η 0)) + _ * ∫ u in (0 : ℝ)..t, v (η u)
  simpa only [NNReal.coe_zero] using h1

/-- The integrated observable minus the limit of the resolvent martingales is uniformly
negligible on long dyadic grids at diffusive scale. -/
theorem tendsto_measureReal_max_resolvent_limit_remainder_dyadic
    (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (hcoord : Draft.dfgwCoordSigma (S := S) Set.univ =
      Draft.dfgwTrajectoryMeasurableSpace (S := S))
    (f : Lp ℝ 2 μ)
    (hint : IntegrableOn (fun t : ℝ => inner ℝ f (transitionOperator hP t.toNNReal f))
      (Set.Ioi 0)) (Z : ℝ≥0 → Lp ℝ 2 P) (M : ℝ≥0 → C(ℝ, S) → ℝ)
    (hZ : ∀ t, Tendsto (fun n : ℕ => dynkinIncrementLp hP
      (transitionResolventDomain hP (reciprocalShift n) f) t) atTop (𝓝 (Z t)))
    (hrep : ∀ t, M t =ᵐ[P] Z t) (hM : Martingale M Draft.dfgwPast P) {θ : ℝ} (hθ : 0 < θ) :
    Tendsto (fun n : ℕ => P.real {η | ∃ r k, k ≤ 2 ^ r ∧ θ * Real.sqrt (n + 1) ≤
      |(∫ u in (0 : ℝ)..(dyadicGridTime ((n + 1 : ℕ) : ℝ≥0) r k : ℝ), f (η u)) -
        M (dyadicGridTime ((n + 1 : ℕ) : ℝ≥0) r k) η|}) atTop (𝓝 0) := by
  let : IsProbabilityMeasure P := hP.probability
  set θ' : ℝ := θ / 4 with hθ'
  have hθ'pos : 0 < θ' := by positivity
  let g : ℕ → ℕ → ℕ → ℝ≥0 := fun n r k => dyadicGridTime ((n + 1 : ℕ) : ℝ≥0) r k
  let v : ℕ → Lp ℝ 2 μ := fun n => transitionResolvent hP (reciprocalShift n) f
  let u : ℕ → (transitionSemigroup hP).generatorDomain := fun n =>
    transitionResolventDomain hP (reciprocalShift n) f
  let Δ : ℕ → ℝ≥0 → C(ℝ, S) → ℝ := fun n =>
    dynkinProcess hP (u n) - (fun _ => dynkinProcess hP (u n) 0) - M
  let E : ℕ → Set C(ℝ, S) := fun n => {η | ∃ r k, k ≤ 2 ^ r ∧ θ * Real.sqrt (n + 1) ≤
    |(∫ w in (0 : ℝ)..(g n r k : ℝ), f (η w)) - M (g n r k) η|}
  let A1 : ℕ → Set C(ℝ, S) := fun n => {η | ∃ r k, k ≤ 2 ^ r ∧
    θ' * Real.sqrt (n + 1) ≤ |transitionResolvent hP (reciprocalShift n) f
      (η (dyadicGridTime ((n + 1 : ℕ) : ℝ≥0) r k))|}
  let A2 : ℕ → Set C(ℝ, S) := fun n => {η | ∃ r k, k ≤ 2 ^ r ∧ θ' ≤
    |(Real.sqrt (n + 1))⁻¹ * (reciprocalShift n : ℝ) *
      ∫ w in (0 : ℝ)..(dyadicGridTime ((n + 1 : ℕ) : ℝ≥0) r k : ℝ),
        transitionResolvent hP (reciprocalShift n) f (η w)|}
  let A3 : ℕ → Set C(ℝ, S) := fun n => {η | ∃ r k, k ≤ 2 ^ r ∧
    θ' * Real.sqrt (n + 1) ≤ |Δ n (dyadicGridTime ((n + 1 : ℕ) : ℝ≥0) r k) η|}
  -- the three error terms tend to zero
  have h1 : Tendsto (fun n => P.real (A1 n)) atTop (𝓝 0) :=
    tendsto_measureReal_max_reciprocal_resolvent_dyadic hP hcoord f hint θ' hθ'pos
  have h2 : Tendsto (fun n => P.real (A2 n)) atTop (𝓝 0) :=
    tendsto_measureReal_max_integrated_resolvent_dyadic hP f hint hθ'pos
  have hΔmart (n : ℕ) : Martingale (Δ n) Draft.dfgwPast P := by
    have hD := martingale_dynkinProcess hP hcoord (u n)
    have h0 : StronglyMeasurable[Draft.dfgwPast (S := S) ⊥] (dynkinProcess hP (u n) 0) :=
      stronglyAdapted_dynkinProcess hP hcoord (u n) ⊥
    have hconst : Martingale (fun _ : ℝ≥0 => dynkinProcess hP (u n) 0) Draft.dfgwPast P :=
      martingale_const_fun _ _ h0 ((dynkinProcess_memLp hP (u n) 0).integrable one_le_two)
    exact (hD.sub hconst).sub hM
  have hΔrep (n : ℕ) (t : ℝ≥0) : Δ n t =ᵐ[P]
      ⇑(dynkinIncrementLp hP (u n) t - Z t) := by
    have hD : dynkinIncrementLp hP (u n) t =ᵐ[P]
        fun η => dynkinProcess hP (u n) t η - dynkinProcess hP (u n) 0 η :=
      MemLp.coeFn_toLp ((dynkinProcess_memLp hP (u n) t).sub (dynkinProcess_memLp hP (u n) 0))
    filter_upwards [hD, hrep t, Lp.coeFn_sub (dynkinIncrementLp hP (u n) t) (Z t)] with η ha hb hc
    simp only [Pi.sub_apply] at hc
    rw [hc, ha, ← hb]
    rfl
  have hΔ2 (n : ℕ) (t : ℝ≥0) : MemLp (Δ n t) 2 P :=
    (memLp_congr_ae (hΔrep n t)).2 (Lp.memLp _)
  have hΔnorm (n : ℕ) (t : ℝ≥0) : (∫ η, (Δ n t η) ^ 2 ∂P) =
      ‖dynkinIncrementLp hP (u n) t - Z t‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hΔrep n t] with η hη
    rw [hη]
    simp only [RCLike.inner_apply, starRingEnd_apply, star_trivial, pow_two]
  have h3bound (n : ℕ) : P.real (A3 n) ≤ 4 / θ' ^ 2 *
      (‖dynkinIncrementLp hP (u n) ((n + 1 : ℕ) : ℝ≥0) - Z ((n + 1 : ℕ) : ℝ≥0)‖ ^ 2 /
        ((n : ℝ) + 1)) := by
    have hsqrt : 0 < Real.sqrt ((n : ℝ) + 1) := Real.sqrt_pos.2 (by positivity)
    have ha : 0 < θ' * Real.sqrt ((n : ℝ) + 1) := mul_pos hθ'pos hsqrt
    have hdoob := measureReal_dyadic_martingale_max_le_tail (Δ n) (hΔmart n)
      ((n + 1 : ℕ) : ℝ≥0) (hΔ2 n _) ha
    have hset : (∫ η in {η | θ' * Real.sqrt ((n : ℝ) + 1) / 2 ≤
        |Δ n ((n + 1 : ℕ) : ℝ≥0) η|}, (Δ n ((n + 1 : ℕ) : ℝ≥0) η) ^ 2 ∂P) ≤
        ∫ η, (Δ n ((n + 1 : ℕ) : ℝ≥0) η) ^ 2 ∂P :=
      setIntegral_le_integral (hΔ2 n _).integrable_sq (ae_of_all _ fun η => sq_nonneg _)
    rw [hΔnorm] at hset
    have hsq : (θ' * Real.sqrt ((n : ℝ) + 1)) ^ 2 = θ' ^ 2 * ((n : ℝ) + 1) := by
      rw [mul_pow, Real.sq_sqrt (by positivity)]
    have hcoef : 0 ≤ 4 / (θ' * Real.sqrt ((n : ℝ) + 1)) ^ 2 := by positivity
    calc
      P.real (A3 n) ≤ _ := hdoob
      _ ≤ 4 / (θ' * Real.sqrt ((n : ℝ) + 1)) ^ 2 *
          ‖dynkinIncrementLp hP (u n) ((n + 1 : ℕ) : ℝ≥0) - Z ((n + 1 : ℕ) : ℝ≥0)‖ ^ 2 :=
        mul_le_mul_of_nonneg_left hset hcoef
      _ = _ := by
        rw [hsq]
        have hn : ((n : ℝ) + 1) ≠ 0 := by positivity
        field_simp
  have h3lim : Tendsto (fun n : ℕ =>
      ‖dynkinIncrementLp hP (u n) ((n + 1 : ℕ) : ℝ≥0) - Z ((n + 1 : ℕ) : ℝ≥0)‖ ^ 2 /
        ((n : ℝ) + 1)) atTop (𝓝 0) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N, hN⟩ := exists_norm_dynkinIncrementLp_sub_limit_sq_le hP hcoord f hint Z hZ
      (ε := ε / 4) (by positivity)
    refine ⟨N, fun n hn => ?_⟩
    have hb := hN n hn ((n + 1 : ℕ) : ℝ≥0)
    have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hnn : 0 ≤ ‖dynkinIncrementLp hP (u n) ((n + 1 : ℕ) : ℝ≥0) -
        Z ((n + 1 : ℕ) : ℝ≥0)‖ ^ 2 / ((n : ℝ) + 1) := by positivity
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hnn, div_lt_iff₀ hpos]
    have hcast : (((n + 1 : ℕ) : ℝ≥0) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
    rw [hcast] at hb
    nlinarith
  have h3 : Tendsto (fun n => P.real (A3 n)) atTop (𝓝 0) := by
    have hupper : Tendsto (fun n : ℕ => 4 / θ' ^ 2 *
        (‖dynkinIncrementLp hP (u n) ((n + 1 : ℕ) : ℝ≥0) - Z ((n + 1 : ℕ) : ℝ≥0)‖ ^ 2 /
          ((n : ℝ) + 1))) atTop (𝓝 0) := by
      simpa only [mul_zero] using h3lim.const_mul (4 / θ' ^ 2)
    exact squeeze_zero (fun n => measureReal_nonneg) h3bound hupper
  -- the event is contained in the union of the three error events
  have hsub (n : ℕ) : E n ≤ᵐ[P] (A1 n ∪ A2 n ∪ A3 n : Set C(ℝ, S)) := by
    have hall : ∀ᵐ η ∂P, ∀ r k : ℕ,
        (∫ w in (0 : ℝ)..(g n r k : ℝ), f (η w)) -
          (dynkinProcess hP (u n) (g n r k) η - dynkinProcess hP (u n) 0 η) =
        -(v n (η (g n r k)) - v n (η 0)) +
          (reciprocalShift n : ℝ) * ∫ w in (0 : ℝ)..(g n r k : ℝ), v n (η w) := by
      rw [ae_all_iff]
      intro r
      rw [ae_all_iff]
      intro k
      simpa only [NNReal.coe_zero] using
        ae_time_integral_sub_dynkin_eq hP f (reciprocalShift n) (g n r k)
    filter_upwards [hall] with η hη hE
    obtain ⟨r, k, hk, hbig⟩ := hE
    by_contra hnot
    simp only [Set.mem_union, not_or] at hnot
    obtain ⟨⟨hn1, hn2⟩, hn3⟩ := hnot
    have hsqrt : 0 < Real.sqrt ((n : ℝ) + 1) := Real.sqrt_pos.2 (by positivity)
    have hb1 : |v n (η (g n r k))| < θ' * Real.sqrt (n + 1) := by
      apply lt_of_not_ge
      intro h
      exact hn1 ⟨r, k, hk, h⟩
    have hb0 : |v n (η 0)| < θ' * Real.sqrt (n + 1) := by
      apply lt_of_not_ge
      intro h
      apply hn1
      refine ⟨0, 0, Nat.zero_le _, ?_⟩
      have hz : (dyadicGridTime ((n + 1 : ℕ) : ℝ≥0) 0 0 : ℝ) = 0 := by
        simp [dyadicGridTime]
      rw [hz]
      exact h
    have hb2 : |(reciprocalShift n : ℝ) * ∫ w in (0 : ℝ)..(g n r k : ℝ), v n (η w)| <
        θ' * Real.sqrt (n + 1) := by
      apply lt_of_not_ge
      intro h
      apply hn2
      refine ⟨r, k, hk, ?_⟩
      rw [mul_assoc, abs_mul, abs_of_pos (inv_pos.2 hsqrt)]
      rw [le_inv_mul_iff₀ hsqrt]
      rw [mul_comm]
      exact h
    have hb3 : |Δ n (g n r k) η| < θ' * Real.sqrt (n + 1) := by
      apply lt_of_not_ge
      intro h
      exact hn3 ⟨r, k, hk, h⟩
    have hdecomp : (∫ w in (0 : ℝ)..(g n r k : ℝ), f (η w)) - M (g n r k) η =
        -(v n (η (g n r k)) - v n (η 0)) +
          (reciprocalShift n : ℝ) * (∫ w in (0 : ℝ)..(g n r k : ℝ), v n (η w)) +
          Δ n (g n r k) η := by
      have h := hη r k
      change _ = _ + _ + (dynkinProcess hP (u n) (g n r k) η - dynkinProcess hP (u n) 0 η -
        M (g n r k) η)
      linarith
    have htri : |(∫ w in (0 : ℝ)..(g n r k : ℝ), f (η w)) - M (g n r k) η| ≤
        |v n (η (g n r k))| + |v n (η 0)| +
          |(reciprocalShift n : ℝ) * ∫ w in (0 : ℝ)..(g n r k : ℝ), v n (η w)| +
          |Δ n (g n r k) η| := by
      rw [hdecomp]
      calc
        _ ≤ |-(v n (η (g n r k)) - v n (η 0))| +
            |(reciprocalShift n : ℝ) * (∫ w in (0 : ℝ)..(g n r k : ℝ), v n (η w))| +
            |Δ n (g n r k) η| := abs_add_three _ _ _
        _ ≤ _ := by
          rw [abs_neg]
          linarith [abs_sub (v n (η (g n r k))) (v n (η 0))]
    have hθsplit : θ * Real.sqrt (n + 1) = 4 * (θ' * Real.sqrt (n + 1)) := by
      rw [hθ']
      ring
    linarith
  have hbound (n : ℕ) : P.real (E n) ≤ P.real (A1 n) + P.real (A2 n) + P.real (A3 n) := by
    calc
      P.real (E n) ≤ P.real (A1 n ∪ A2 n ∪ A3 n) :=
        ENNReal.toReal_mono (measure_ne_top P _) (measure_mono_ae (hsub n))
      _ ≤ P.real (A1 n ∪ A2 n) + P.real (A3 n) := measureReal_union_le _ _
      _ ≤ P.real (A1 n) + P.real (A2 n) + P.real (A3 n) := by
        gcongr
        exact measureReal_union_le _ _
  have hsum : Tendsto (fun n => P.real (A1 n) + P.real (A2 n) + P.real (A3 n)) atTop
      (𝓝 0) := by
    simpa only [add_zero] using (h1.add h2).add h3
  exact squeeze_zero (fun n => measureReal_nonneg) hbound hsum

end EinsteinFull.External.DFGW
