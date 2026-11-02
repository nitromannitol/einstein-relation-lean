import EinsteinFull.Calculus.ParabolicLibraryBridgeOscIter

/-!
# Hölder decay of the oscillation on parabolic cylinders of continuous radius
-/

open scoped ENNReal

noncomputable section
namespace EinsteinFull.ParabolicBridge

open MeasureTheory Set Filter PDE

/-- Real-variable fact: `(1 - η)^n ≤ C θ^α` when `(1/2)^(n+1) < θ ≤ (1/2)^n`. -/
theorem pow_decay_le {δ : ℝ} (hδ0 : 1 / 2 ≤ δ) (hδ1 : δ < 1) :
    ∃ α C : ℝ, 0 < α ∧ α ≤ 1 ∧ 1 ≤ C ∧ ∀ θ : ℝ, 0 < θ → θ ≤ 1 →
      ∃ n : ℕ, θ ≤ (1 / 2 : ℝ) ^ n ∧ δ ^ n ≤ C * θ ^ α := by
  have hδpos : 0 < δ := by linarith
  have hlogδ : Real.log δ < 0 := Real.log_neg hδpos hδ1
  have hlog2 : Real.log (1 / 2 : ℝ) < 0 := Real.log_neg (by norm_num) (by norm_num)
  set α : ℝ := Real.log δ / Real.log (1 / 2) with hα
  have hα0 : 0 < α := div_pos_of_neg_of_neg hlogδ hlog2
  have hα1 : α ≤ 1 := by
    rw [hα, div_le_one_of_neg hlog2]
    exact Real.log_le_log (by norm_num) hδ0
  have hδα : (1 / 2 : ℝ) ^ α = δ := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 1 / 2), hα, mul_div_cancel₀ _ hlog2.ne]
    exact Real.exp_log hδpos
  refine ⟨α, (2 : ℝ) ^ α, hα0, hα1, Real.one_le_rpow (by norm_num) hα0.le, ?_⟩
  intro θ hθ hθ1
  obtain ⟨n, hn1, hn2⟩ := exists_nat_pow_near_of_lt_one hθ hθ1 (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)
  refine ⟨n, hn2, ?_⟩
  have h1 : δ ^ n = ((1 / 2 : ℝ) ^ n) ^ α := by
    rw [← hδα, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
      ← Real.rpow_mul (by norm_num), mul_comm]
  have h2 : ((1 / 2 : ℝ) ^ n) ^ α = (2 : ℝ) ^ α * ((1 / 2 : ℝ) ^ (n + 1)) ^ α := by
    rw [← Real.mul_rpow (by norm_num) (by positivity)]
    congr 1
    rw [pow_succ]
    ring
  rw [h1, h2]
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (by positivity) hn1.le hα0.le) (by positivity)

/-- Hölder-type decay of the oscillation on `B(c, θρ) × (T₀ - (θρ)², T₀]`. -/
theorem osc_holder (d : ℕ) (hd : 0 < d) (Lam : ℝ) (hLam : 1 ≤ Lam) :
    ∃ α C : ℝ, 0 < α ∧ α ≤ 1 ∧ 1 ≤ C ∧ ∀ (a : ParCoeffField d) (c : Vec d) (T₀ ρ : ℝ), 0 < ρ →
      ∀ {I' : Set ℝ}, MeasurableSet I' → Ioc (T₀ - ρ ^ 2) T₀ ⊆ I' →
      IsParabolicCoeff 1 Lam a (euclideanBall c ρ) I' →
      ∀ u : ParH1Function (euclideanBall c ρ) I',
      IsParabolicWeakSolution a (euclideanBall c ρ) I' u →
      ∀ m M : ℝ, m ≤ M →
      (∀ᵐ z ∂(volume.restrict (euclideanBall c ρ ×ˢ Ioc (T₀ - ρ ^ 2) T₀)),
        m ≤ u.toFun z ∧ u.toFun z ≤ M) →
      ∀ θ : ℝ, 0 < θ → θ ≤ 1 →
      ∃ m' M' : ℝ,
        (∀ᵐ z ∂(volume.restrict
          (euclideanBall c (θ * ρ) ×ˢ Ioc (T₀ - (θ * ρ) ^ 2) T₀)),
          m' ≤ u.toFun z ∧ u.toFun z ≤ M') ∧ M' - m' ≤ C * θ ^ α * (M - m) := by
  obtain ⟨η, hη, hη2, hiter⟩ := osc_decay_iter d hd Lam hLam
  obtain ⟨α, C, hα0, hα1, hC1, hdec⟩ := pow_decay_le (δ := 1 - η) (by linarith) (by linarith)
  refine ⟨α, C, hα0, hα1, hC1, ?_⟩
  intro a c T₀ ρ hρ I' hI'meas hI' ha u hu m M hmM hbd θ hθ hθ1
  obtain ⟨n, hn1, hn2⟩ := hdec θ hθ hθ1
  obtain ⟨m', M', hae, g1, g2, g3, g4⟩ := hiter a c T₀ ρ hρ hI'meas hI' ha u hu m M hmM hbd n
  refine ⟨m', M', ?_, ?_⟩
  · refine ae_restrict_of_ae_restrict_of_subset ?_ hae
    have hr : θ * ρ ≤ ρ / 2 ^ n := by
      have h2n : (1 / 2 : ℝ) ^ n = 1 / 2 ^ n := by rw [one_div, inv_pow, one_div]
      calc θ * ρ ≤ (1 / 2 : ℝ) ^ n * ρ := mul_le_mul_of_nonneg_right hn1 hρ.le
        _ = ρ / 2 ^ n := by rw [h2n]; ring
    refine prod_mono (euclideanBall_mono (by positivity) hr) (Ioc_subset_Ioc_left ?_)
    have : (θ * ρ) ^ 2 ≤ (ρ / 2 ^ n) ^ 2 := pow_le_pow_left₀ (by positivity) hr 2
    linarith
  · have hω : 0 ≤ M - m := by linarith
    calc M' - m' ≤ (1 - η) ^ n * (M - m) := g4
      _ ≤ (C * θ ^ α) * (M - m) := mul_le_mul_of_nonneg_right hn2 hω

end EinsteinFull.ParabolicBridge
