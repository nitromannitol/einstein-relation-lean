import Mathlib

open MeasureTheory Filter Topology

namespace EinsteinFull.Calculus.K4

/-- Telescoping reconstruction: a finite block sum is controlled by its coarsest conditional
sum and the annular increments, once every block is the limit of its conditional versions. -/
theorem annular_reconstruction_core {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {p : ℝ} (hp : 1 ≤ p) (X : ι → Ω → ℂ) (CE : ℕ → ι → Ω → ℂ) (Λ : Finset ι)
    (hX : ∀ z, MemLp (X z) (ENNReal.ofReal p) μ)
    (hCE : ∀ n z, MemLp (CE n z) (ENNReal.ofReal p) μ)
    (a : ℝ) (b : ℕ → ℝ)
    (h0 : (eLpNorm (∑ z ∈ Λ, CE 0 z) (ENNReal.ofReal p) μ).toReal ≤ a)
    (hA : ∀ n, (eLpNorm (∑ z ∈ Λ, (CE (n + 1) z - CE n z)) (ENNReal.ofReal p) μ).toReal ≤ b n)
    (hb : Summable b)
    (hrem : ∀ z ∈ Λ,
      Tendsto (fun n => (eLpNorm (X z - CE n z) (ENNReal.ofReal p) μ).toReal) atTop (𝓝 0)) :
    MemLp (∑ z ∈ Λ, X z) (ENNReal.ofReal p) μ ∧
      (eLpNorm (∑ z ∈ Λ, X z) (ENNReal.ofReal p) μ).toReal ≤ a + ∑' n, b n := by
  have hq : (1 : ENNReal) ≤ ENNReal.ofReal p := by
    simpa using ENNReal.ofReal_le_ofReal hp
  refine ⟨memLp_finsetSum' _ (fun z _ => hX z), ?_⟩
  have hbn : ∀ n, 0 ≤ b n := fun n => le_trans ENNReal.toReal_nonneg (hA n)
  have hD : ∀ n, MemLp (∑ z ∈ Λ, (CE (n + 1) z - CE n z)) (ENNReal.ofReal p) μ := fun n =>
    memLp_finsetSum' _ (fun z _ => (hCE (n + 1) z).sub (hCE n z))
  have hR : ∀ n, MemLp (∑ z ∈ Λ, (X z - CE n z)) (ENNReal.ofReal p) μ := fun n =>
    memLp_finsetSum' _ (fun z _ => (hX z).sub (hCE n z))
  have h00 : MemLp (∑ z ∈ Λ, CE 0 z) (ENNReal.ofReal p) μ :=
    memLp_finsetSum' _ (fun z _ => hCE 0 z)
  have key : ∀ N : ℕ, (eLpNorm (∑ z ∈ Λ, X z) (ENNReal.ofReal p) μ).toReal ≤
      a + ∑ n ∈ Finset.range N, b n +
        ∑ z ∈ Λ, (eLpNorm (X z - CE N z) (ENNReal.ofReal p) μ).toReal := by
    intro N
    have hid : (∑ z ∈ Λ, X z) = (∑ z ∈ Λ, CE 0 z) +
        ∑ n ∈ Finset.range N, (∑ z ∈ Λ, (CE (n + 1) z - CE n z)) +
          ∑ z ∈ Λ, (X z - CE N z) := by
      have h1 : ∀ z, CE N z = CE 0 z + ∑ n ∈ Finset.range N, (CE (n + 1) z - CE n z) := by
        intro z
        rw [Finset.sum_range_sub (fun n => CE n z)]
        abel
      funext ω
      simp only [Pi.add_apply, Finset.sum_apply, Pi.sub_apply]
      rw [Finset.sum_comm (s := Finset.range N) (t := Λ)]
      have : ∀ z ∈ Λ, X z ω = CE 0 z ω +
          ∑ n ∈ Finset.range N, (CE (n + 1) z ω - CE n z ω) + (X z ω - CE N z ω) := by
        intro z _
        have := congrFun (h1 z) ω
        simp only [Pi.add_apply, Finset.sum_apply, Pi.sub_apply] at this
        rw [this]; ring
      rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, Finset.sum_add_distrib]
    have hsum : MemLp (∑ n ∈ Finset.range N, (∑ z ∈ Λ, (CE (n + 1) z - CE n z)))
        (ENNReal.ofReal p) μ := memLp_finsetSum' _ (fun n _ => hD n)
    have e1 := eLpNorm_add_le (μ := μ) (f := (∑ z ∈ Λ, CE 0 z) +
        ∑ n ∈ Finset.range N, (∑ z ∈ Λ, (CE (n + 1) z - CE n z)))
        (g := ∑ z ∈ Λ, (X z - CE N z)) hq
    have e2 := eLpNorm_add_le (μ := μ) (f := ∑ z ∈ Λ, CE 0 z)
        (g := ∑ n ∈ Finset.range N, (∑ z ∈ Λ, (CE (n + 1) z - CE n z))) hq
    have e3 := eLpNorm_sum_le (μ := μ) (p := ENNReal.ofReal p)
        (f := fun n => ∑ z ∈ Λ, (CE (n + 1) z - CE n z)) (s := Finset.range N) hq
    have e4 := eLpNorm_sum_le (μ := μ) (p := ENNReal.ofReal p)
        (f := fun z => X z - CE N z) (s := Λ) hq
    rw [hid]
    have hfin : ∀ n, eLpNorm (∑ z ∈ Λ, (CE (n + 1) z - CE n z)) (ENNReal.ofReal p) μ ≠ ⊤ :=
      fun n => (hD n).eLpNorm_ne_top
    have hfin2 : ∀ z ∈ Λ, eLpNorm (X z - CE N z) (ENNReal.ofReal p) μ ≠ ⊤ :=
      fun z _ => ((hX z).sub (hCE N z)).eLpNorm_ne_top
    have t1 : (eLpNorm ((∑ z ∈ Λ, CE 0 z) + ∑ n ∈ Finset.range N,
        (∑ z ∈ Λ, (CE (n + 1) z - CE n z)) + ∑ z ∈ Λ, (X z - CE N z))
          (ENNReal.ofReal p) μ).toReal ≤
        (eLpNorm (∑ z ∈ Λ, CE 0 z) (ENNReal.ofReal p) μ).toReal +
        (∑ n ∈ Finset.range N,
          eLpNorm (∑ z ∈ Λ, (CE (n + 1) z - CE n z)) (ENNReal.ofReal p) μ).toReal +
        (∑ z ∈ Λ, eLpNorm (X z - CE N z) (ENNReal.ofReal p) μ).toReal := by
      have hne1 : eLpNorm (∑ z ∈ Λ, CE 0 z) (ENNReal.ofReal p) μ ≠ ⊤ := h00.eLpNorm_ne_top
      have hne2 : (∑ n ∈ Finset.range N,
          eLpNorm (∑ z ∈ Λ, (CE (n + 1) z - CE n z)) (ENNReal.ofReal p) μ) ≠ ⊤ :=
        ENNReal.sum_ne_top.2 (fun n _ => hfin n)
      have hne3 : (∑ z ∈ Λ, eLpNorm (X z - CE N z) (ENNReal.ofReal p) μ) ≠ ⊤ :=
        ENNReal.sum_ne_top.2 hfin2
      rw [← ENNReal.toReal_add hne1 hne2, ← ENNReal.toReal_add (ENNReal.add_ne_top.2 ⟨hne1, hne2⟩) hne3]
      refine ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2 ⟨hne1, hne2⟩, hne3⟩) ?_
      exact e1.trans (add_le_add (e2.trans (add_le_add_right e3 _)) e4)
    have t2 : (∑ n ∈ Finset.range N,
          eLpNorm (∑ z ∈ Λ, (CE (n + 1) z - CE n z)) (ENNReal.ofReal p) μ).toReal =
        ∑ n ∈ Finset.range N,
          (eLpNorm (∑ z ∈ Λ, (CE (n + 1) z - CE n z)) (ENNReal.ofReal p) μ).toReal :=
      ENNReal.toReal_sum (fun n _ => hfin n)
    have t3 : (∑ z ∈ Λ, eLpNorm (X z - CE N z) (ENNReal.ofReal p) μ).toReal =
        ∑ z ∈ Λ, (eLpNorm (X z - CE N z) (ENNReal.ofReal p) μ).toReal :=
      ENNReal.toReal_sum hfin2
    rw [t2, t3] at t1
    have : ∑ n ∈ Finset.range N,
          (eLpNorm (∑ z ∈ Λ, (CE (n + 1) z - CE n z)) (ENNReal.ofReal p) μ).toReal ≤
        ∑ n ∈ Finset.range N, b n := Finset.sum_le_sum (fun n _ => hA n)
    linarith
  have hlim : Tendsto (fun N : ℕ => a + ∑ n ∈ Finset.range N, b n +
      ∑ z ∈ Λ, (eLpNorm (X z - CE N z) (ENNReal.ofReal p) μ).toReal) atTop
      (𝓝 (a + ∑' n, b n + ∑ z ∈ Λ, (0 : ℝ))) := by
    refine Tendsto.add (Tendsto.const_add a hb.hasSum.tendsto_sum_nat) ?_
    exact tendsto_finsetSum _ hrem
  simp only [Finset.sum_const_zero, add_zero] at hlim
  exact ge_of_tendsto' hlim key

theorem eventually_poly_exp_le {C a β γ : ℝ} (hC : 0 < C) (hβ : 0 < β) (hβγ : β < γ) :
    ∃ T : ℝ, 1 ≤ T ∧ ∀ t : ℝ, T ≤ t →
      (2 + t) ^ C * t ^ a * Real.exp (C * t ^ β) ≤ Real.exp (t ^ γ / C) := by
  have hγ : 0 < γ := hβ.trans hβγ
  set K : ℝ := 2 * C + |a| with hK
  have hKpos : 0 < K := by positivity
  have h1 : ∀ᶠ t : ℝ in atTop, K * Real.log t ≤ t ^ γ / (2 * C) := by
    have := (isLittleO_log_rpow_atTop hγ).bound (c := 1 / (2 * C * K)) (by positivity)
    filter_upwards [this, eventually_ge_atTop (1 : ℝ)] with t ht ht1
    have ht0 : 0 < t := by linarith
    rw [Real.norm_of_nonneg (Real.log_nonneg ht1), Real.norm_of_nonneg (by positivity)] at ht
    calc K * Real.log t ≤ K * (1 / (2 * C * K) * t ^ γ) := by gcongr
      _ = t ^ γ / (2 * C) := by field_simp
  have h2 : ∀ᶠ t : ℝ in atTop, C * t ^ β ≤ t ^ γ / (2 * C) := by
    have := (tendsto_rpow_atTop (sub_pos.2 hβγ)).eventually_ge_atTop (2 * C ^ 2)
    filter_upwards [this, eventually_gt_atTop (0 : ℝ)] with t ht ht0
    have hsplit : t ^ γ = t ^ β * t ^ (γ - β) := by
      rw [← Real.rpow_add ht0]; ring_nf
    rw [hsplit, le_div_iff₀ (by positivity)]
    have : 0 < t ^ β := by positivity
    nlinarith [mul_le_mul_of_nonneg_left ht this.le]
  obtain ⟨T, hT⟩ := (h1.and (h2.and (eventually_ge_atTop (3 : ℝ)))).exists_forall_of_atTop
  refine ⟨max T 3, le_trans (by norm_num) (le_max_right _ _), fun t ht => ?_⟩
  obtain ⟨hk1, hk2, hk3⟩ := hT t (le_trans (le_max_left _ _) ht)
  have ht0 : 0 < t := by linarith
  have ht1 : 1 ≤ t := by linarith
  have hlog0 : 0 ≤ Real.log t := Real.log_nonneg ht1
  have hl2 : Real.log (2 + t) ≤ 2 * Real.log t := by
    rw [← Real.log_rpow ht0 2]
    refine Real.log_le_log (by linarith) ?_
    rw [Real.rpow_two]
    nlinarith
  rw [Real.rpow_def_of_pos (by linarith : 0 < 2 + t), Real.rpow_def_of_pos ht0,
    ← Real.exp_add, ← Real.exp_add, Real.exp_le_exp]
  have hal : a * Real.log t ≤ |a| * Real.log t := by gcongr; exact le_abs_self a
  have : Real.log (2 + t) * C ≤ 2 * Real.log t * C := by gcongr
  have e : t ^ γ / C = t ^ γ / (2 * C) + t ^ γ / (2 * C) := by field_simp; ring
  rw [e]
  have hKl : K * Real.log t = 2 * C * Real.log t + |a| * Real.log t := by rw [hK]; ring
  nlinarith

theorem summable_two_rpow_mul_exp_neg_four_pow (d : ℕ) {c : ℝ} (hc : 0 < c) :
    Summable (fun n : ℕ => (2 : ℝ) ^ ((n : ℝ) * (d : ℝ) / 2) * Real.exp (-4 ^ n * c)) := by
  have hpos : ∀ n : ℕ, 0 < (2 : ℝ) ^ ((n : ℝ) * (d : ℝ) / 2) * Real.exp (-4 ^ n * c) :=
    fun n => by positivity
  refine summable_of_ratio_test_tendsto_lt_one (l := 0) one_pos
    (Eventually.of_forall fun n => (hpos n).ne') ?_
  have hratio : ∀ n : ℕ,
      ‖(2 : ℝ) ^ (((n + 1 : ℕ) : ℝ) * (d : ℝ) / 2) * Real.exp (-4 ^ (n + 1) * c)‖ /
        ‖(2 : ℝ) ^ ((n : ℝ) * (d : ℝ) / 2) * Real.exp (-4 ^ n * c)‖ =
      (2 : ℝ) ^ ((d : ℝ) / 2) * Real.exp (-(3 * c) * 4 ^ n) := by
    intro n
    rw [Real.norm_of_nonneg (hpos _).le, Real.norm_of_nonneg (hpos n).le, div_eq_iff (hpos n).ne']
    have h1 : (2 : ℝ) ^ (((n + 1 : ℕ) : ℝ) * (d : ℝ) / 2) =
        (2 : ℝ) ^ ((n : ℝ) * (d : ℝ) / 2) * (2 : ℝ) ^ ((d : ℝ) / 2) := by
      rw [← Real.rpow_add (by norm_num)]; congr 1; push_cast; ring
    have h2 : Real.exp (-4 ^ (n + 1) * c) =
        Real.exp (-4 ^ n * c) * Real.exp (-(3 * c) * 4 ^ n) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [h1, h2]; ring
  simp_rw [hratio]
  have : Tendsto (fun n : ℕ => (2 : ℝ) ^ ((d : ℝ) / 2) * Real.exp (-(3 * c) * 4 ^ n)) atTop
      (𝓝 ((2 : ℝ) ^ ((d : ℝ) / 2) * 0)) := by
    refine Tendsto.const_mul _ ?_
    refine Real.tendsto_exp_atBot.comp ?_
    refine Filter.Tendsto.neg_mul_atTop (by linarith) tendsto_const_nhds ?_
    exact tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  simpa using this

end EinsteinFull.Calculus.K4
