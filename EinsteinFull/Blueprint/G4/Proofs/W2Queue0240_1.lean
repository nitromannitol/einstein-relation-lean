import EinsteinFull.Blueprint.G4.node_p_u3A_integration_u23_compact_u2D_extension
import EinsteinFull.Blueprint.G4.node_finite_u2D_time_u2D_analyticity
import EinsteinFull.Blueprint.G4.node_p_u3A_integration_u23_uniform_u2D_profile_u2D_bounds

open MeasureTheory Filter
open scoped Topology NNReal BigOperators

namespace EinsteinFull.Blueprint
open EinsteinRelation

private lemma compact_profile_bound {u₀ u₂ γ B : ℝ} (hB : 0 ≤ B)
    (hγ : 0 ≤ γ) (hγB : γ ≤ B) (hu : |u₀| + |u₂| ≤ B)
    {w : ℂ} (hw : ‖w‖ ≤ 2) :
    ‖complexGaussianProfile u₀ u₂ γ w‖ ≤ 5 * B * Real.exp (4 * B) := by
  have hw2 : ‖w‖ ^ 2 ≤ 4 := by nlinarith [norm_nonneg w]
  have hu₀ : |u₀| ≤ B := le_trans (le_add_of_nonneg_right (abs_nonneg _)) hu
  have hu₂ : |u₂| ≤ B := le_trans (le_add_of_nonneg_left (abs_nonneg _)) hu
  have hpoly : ‖(u₀ : ℂ) + (u₂ : ℂ) * w ^ 2‖ ≤ 5 * B := by
    calc
      _ ≤ ‖(u₀ : ℂ)‖ + ‖(u₂ : ℂ) * w ^ 2‖ := norm_add_le _ _
      _ = |u₀| + |u₂| * ‖w‖ ^ 2 := by
        rw [norm_mul, norm_pow, Complex.norm_real, Complex.norm_real,
          Real.norm_eq_abs, Real.norm_eq_abs]
      _ ≤ B + B * 4 := add_le_add hu₀ (mul_le_mul hu₂ hw2 (sq_nonneg _) hB)
      _ = 5 * B := by ring
  have hexp : ‖Complex.exp (-(γ : ℂ) * w ^ 2)‖ ≤ Real.exp (4 * B) := by
    apply (Complex.norm_exp_le_exp_norm _).trans
    apply Real.exp_le_exp.mpr
    simp only [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hγ,
      norm_pow]
    nlinarith [mul_le_mul hγB hw2 (sq_nonneg ‖w‖) hB]
  exact (norm_mul_le _ _).trans (mul_le_mul hpoly hexp (norm_nonneg _) (by positivity))

private lemma extend_profile_estimate (d : ℕ) {α₀ Cp B Ck : ℝ}
    (hα₀ : 0 < α₀) (hCp : 0 < Cp) (hB : 0 < B)  :
    ∃ α C : ℝ, 0 < α ∧ α ≤ 1 / 4 ∧ 0 < C ∧
    ∀ (u₀ u₂ γ : ℝ) (K : ℝ → ℂ → ℂ),
      0 ≤ γ → γ ≤ B → |u₀| + |u₂| ≤ B →
      (∀ t : ℝ, 1 ≤ t → t ≤ 4 → ∀ z : ℂ, ‖z‖ * Real.sqrt t ≤ 2 → ‖K t z‖ ≤ Ck) →
      (∀ t : ℝ, 4 ≤ t → ∀ z : ℂ, ‖z‖ * Real.sqrt t ≤ 2 →
        ‖kernelProfileRemainder d u₀ u₂ γ K t z‖ ≤
          Cp * t ^ (-1 - (d : ℝ) / 2 - α₀) *
            Real.exp (Cp * (1 + ‖z‖ * Real.sqrt t) ^ 2)) →
      ∀ t : ℝ, 1 ≤ t → ∀ z : ℂ, ‖z‖ * Real.sqrt t ≤ 2 →
        ‖kernelProfileRemainder d u₀ u₂ γ K t z‖ ≤
          C * t ^ (-1 - (d : ℝ) / 2 - α) *
            Real.exp (C * (1 + ‖z‖ * Real.sqrt t) ^ 2) := by
  let α := min α₀ (1 / 4)
  let q := -1 - (d : ℝ) / 2 - α
  let M := Ck + 5 * B * Real.exp (4 * B)
  let C := max Cp (M / 4 ^ q) + 1
  have hα : 0 < α := lt_min hα₀ (by norm_num)
  have hq : q ≤ 0 := by dsimp [q]; linarith [Nat.cast_nonneg (α := ℝ) d]
  have hpow : 0 < (4 : ℝ) ^ q := Real.rpow_pos_of_pos (by norm_num) _
  have hCpC : Cp ≤ C := by dsimp [C]; linarith [le_max_left Cp (M / 4 ^ q)]
  have hMC : M ≤ C * 4 ^ q := by
    have : M / 4 ^ q ≤ C := by dsimp [C]; linarith [le_max_right Cp (M / 4 ^ q)]
    exact (div_le_iff₀ hpow).mp this
  have hC : 0 < C := lt_of_lt_of_le hCp hCpC
  refine ⟨α, C, hα, min_le_right _ _, hC, ?_⟩
  intro u₀ u₂ γ K hγ hγB hu hsmall hlarge t ht z hz
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have he : 1 ≤ Real.exp (C * (1 + ‖z‖ * Real.sqrt t) ^ 2) :=
    Real.one_le_exp (mul_nonneg hC.le (sq_nonneg _))
  by_cases ht4 : 4 ≤ t
  · apply (hlarge t ht4 z hz).trans
    apply mul_le_mul
    · exact mul_le_mul hCpC
        (Real.rpow_le_rpow_of_exponent_le ht (by dsimp [α]; linarith [min_le_left α₀ (1 / 4 : ℝ)]))
        (Real.rpow_nonneg ht0.le _) hC.le
    · exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hCpC (sq_nonneg _))
    · exact (Real.exp_pos _).le
    · positivity
  · have ht4' : t ≤ 4 := (lt_of_not_ge ht4).le
    have hGauss := compact_profile_bound hB.le hγ hγB hu
      (show ‖z * (Real.sqrt t : ℂ)‖ ≤ 2 by
        simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (Real.sqrt_nonneg t)] using hz)
    have hscale : t ^ (-1 - (d : ℝ) / 2) ≤ 1 := by
      exact Real.rpow_le_one_of_one_le_of_nonpos ht (by linarith [Nat.cast_nonneg (α := ℝ) d])
    have hrem : ‖kernelProfileRemainder d u₀ u₂ γ K t z‖ ≤ M := by
      unfold kernelProfileRemainder
      rw [if_pos ht]
      calc
        _ ≤ ‖K t z‖ + ‖((t ^ (-1 - (d : ℝ) / 2) : ℝ) : ℂ) *
            complexGaussianProfile u₀ u₂ γ (z * (Real.sqrt t : ℂ))‖ := norm_sub_le _ _
        _ ≤ Ck + 5 * B * Real.exp (4 * B) := by
          apply add_le_add (hsmall t ht ht4' z hz)
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (Real.rpow_nonneg ht0.le _)]
          exact (mul_le_mul hscale hGauss (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
    apply hrem.trans
    calc
      M ≤ C * 4 ^ q := hMC
      _ ≤ C * t ^ q := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos ht0 ht4' hq) hC.le
      _ ≤ C * t ^ q * Real.exp (C * (1 + ‖z‖ * Real.sqrt t) ^ 2) :=
        le_mul_of_one_le_right (by positivity) he

/-- Extend the actual correlation-profile bounds to time one, with structural constants. -/
theorem node_p_u3A_integration_u23_compact_u2D_extension_of_deps
    (hprofile : node_p_u3A_profileStmt)
    (hanalytic : node_finite_u2D_time_u2D_analyticityStmt)
    (huniform : node_p_u3A_integration_u23_uniform_u2D_profile_u2D_boundsStmt) :
    node_p_u3A_integration_u23_compact_u2D_extensionStmt := by
  intro d hd D
  obtain ⟨α₀, Cp, hα₀, hCp, hprofile, _⟩ := hprofile d hd D
  obtain ⟨Ck, _hCk, hanalytic⟩ := hanalytic d hd D 4 2 (by norm_num) (by norm_num)
  obtain ⟨c, B, hc, hB, huniform⟩ := huniform d hd D
  obtain ⟨α, C, hα, hα4, hC, hextend⟩ := extend_profile_estimate d hα₀ hCp hB
  refine ⟨α, C, hα, hα4, hC, ?_⟩
  intro Q hQ β a μ Z covariance hβ ha hμ hZ hcov P hP
  let first : Fin d := ⟨0, by omega⟩
  let A := homogenizedCoefficient Q
  let p₀ : ℝ := (2 * Real.pi) ^ (-(d : ℝ) / 2) / Real.sqrt A.det
  let γ : ℝ := A first first / 2
  let u₀ : Option (Fin d) → ℝ := fun κ => match κ with
    | none => 0
    | some i => p₀ / 4 * ∑ j, ∑ k,
        (A⁻¹) j k * covariance (.inl (j, first)) (.inl (k, i))
  let u₂ : Option (Fin d) → ℝ := fun κ => match κ with
    | none => p₀ / 2 * covariance (.inl (first, first)) (.inr ())
    | some i => p₀ / 4 * covariance (.inl (first, first)) (.inl (first, i))
  let K : Option (Fin d) → ℝ → ℂ → ℂ := fun κ t z => match κ with
    | none => clockCorrelation Q first z (P z) β μ t.toNNReal
    | some i => velocityCorrelation Q first i z (P z) β a t.toNNReal
  change ∀ κ t, 1 ≤ t → ∀ z, ‖z‖ * Real.sqrt t ≤ 2 →
    ‖kernelProfileRemainder d (u₀ κ) (u₂ κ) γ (K κ) t z‖ ≤
      C * t ^ (-1 - (d : ℝ) / 2 - α) * Real.exp (C * (1 + ‖z‖ * Real.sqrt t) ^ 2)
  have hb := huniform Q hQ Z covariance hZ hcov
  change c ≤ γ ∧ γ ≤ B ∧ ∀ κ, |u₀ κ| + |u₂ κ| ≤ B ∧
    ∀ z, (match κ with
      | none => clockGaussianProfile hd Q covariance z
      | some i => velocityGaussianProfile hd Q covariance i z) =
        complexGaussianProfile (u₀ κ) (u₂ κ) γ z at hb
  obtain ⟨hcγ, hγB, hu⟩ := hb
  have hk := (hanalytic Q hQ β a μ hβ ha hμ P hP).2.2
  have hp := (hprofile Q hQ β a μ Z covariance hβ ha hμ hZ hcov).2.2
  intro κ
  apply hextend (u₀ κ) (u₂ κ) γ (K κ) (le_trans hc.le hcγ) hγB (hu κ).1
  · intro t ht ht4 z hz
    have ht0 : 0 ≤ t := le_trans zero_le_one ht
    have hz2 : ‖z‖ ≤ 2 := by
      have hs : 1 ≤ Real.sqrt t := (Real.one_le_sqrt).mpr ht
      nlinarith [norm_nonneg z]
    have hk' := hk t.toNNReal z (by simpa only [Real.coe_toNNReal t ht0] using ht4) hz2
    cases κ with
    | none => exact (le_add_of_nonneg_left (norm_nonneg _)).trans (hk' first)
    | some i => exact (le_add_of_nonneg_right (norm_nonneg _)).trans (hk' i)
  · intro t ht z hz
    have ht0 : 0 ≤ t := by linarith
    have ht1 : 1 ≤ t := by linarith
    have hp' := hp t.toNNReal (by simpa only [Real.coe_toNNReal t ht0] using ht) z
      (by simpa only [Real.coe_toNNReal t ht0] using hz) (P z) (hP z)
    have hnormal := (hu κ).2 (z * (Real.sqrt t : ℂ))
    cases κ with
    | none =>
      have h := (le_add_of_nonneg_left (norm_nonneg _)).trans (hp' first)
      simpa only [kernelProfileRemainder, if_pos ht1, K,
        Real.coe_toNNReal t ht0, hnormal] using h
    | some i =>
      have h := (le_add_of_nonneg_right (norm_nonneg _)).trans (hp' i)
      simpa only [kernelProfileRemainder, if_pos ht1, K,
        Real.coe_toNNReal t ht0, hnormal] using h

end EinsteinFull.Blueprint
