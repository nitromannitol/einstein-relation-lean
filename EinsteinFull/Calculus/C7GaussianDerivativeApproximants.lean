import EinsteinFull.Calculus.C7UnitInitializationSupport
import EinsteinFull.Blueprint.G3.Proofs.W1SplitTailClosure

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation

/-- Gaussian local approximants give the spatial decay of the first two derivatives. -/
theorem gaussian_derivative_of_local_approximants
    : ∀ (d : ℕ) (D : StructuralData d) (R B L b p : ℝ),
      0 ≤ R → 0 ≤ B → 0 ≤ L → 0 < b → 2 ≤ p →
      ∃ C : ℝ, 0 ≤ C ∧
      ∀ (hd : 2 ≤ d) (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
        (H : Lp ℂ 2 (reducedLaw Q)) (K : ℕ → Lp ℂ 2 (reducedLaw Q)),
        (∀ n, ∀ᵐ ω ∂reducedLaw Q, ‖K n ω‖ ≤ B) →
        (∀ n : ℕ, IsComplexLocalObservation Q (R+n) (K n)) →
        (∀ n, (∫ ω, K n ω ∂reducedLaw Q) = 0) →
        (∀ n, ‖H-K n‖ ≤ L * Real.exp (-b * (n : ℝ)^2)) →
      ∀ (k : ℕ), 1 ≤ k → k ≤ 2 → ∀ (j : Fin k → Fin d) (s : ℝ) (hs : 0 < s),
        MemLp (gaussianDerivativeAverage hd Q s hs k j H : FieldPair d → ℂ)
          (ENNReal.ofReal p) (reducedLaw Q) ∧
        (eLpNorm (gaussianDerivativeAverage hd Q s hs k j H : FieldPair d → ℂ)
          (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤
            C * s ^ (-((k : ℝ) / 2 + (d : ℝ) / 4)) := by
  intro d D R B L b p hR hB hL hb hp
  have : Fact (1 ≤ ENNReal.ofReal p) := ⟨by
    exact_mod_cast ENNReal.ofReal_le_ofReal (show (1 : ℝ) ≤ p by linarith)⟩
  obtain ⟨C₀, hC₀, havg⟩ :=
    UnitInitialization.exists_gaussian_average_of_gaussian_norm_approximants
      d D.ellipticity D.dependenceRange R B L b p hR hB hL hb hp
  obtain ⟨C₁, hC₁, hbound₁⟩ := SplitTail.exists_unit_derivative_integral_bound
    d D.ellipticity D.one_le_ellipticity 1
  obtain ⟨C₂, hC₂, hbound₂⟩ := SplitTail.exists_unit_derivative_integral_bound
    d D.ellipticity D.one_le_ellipticity 2
  let E := C₁ * (2 : ℝ) ^ ((1 : ℝ) / 2 + (d : ℝ) / 4) +
    C₂ * (2 : ℝ) ^ ((2 : ℝ) / 2 + (d : ℝ) / 4)
  refine ⟨C₀ * E, mul_nonneg hC₀ (by dsimp [E]; positivity), ?_⟩
  intro hd Q H K hKB hlocal hmean herr k hk₁ hk₂ j s hs
  obtain ⟨A, hA, hAweight, hAbound⟩ : ∃ A : ℝ, 0 ≤ A ∧
      A * (2 : ℝ) ^ ((k : ℝ) / 2 + (d : ℝ) / 4) ≤ E ∧
      (∫ x : Vec d, ‖iteratedFDeriv ℝ k
        (homogenizedGaussianKernel Q ⟨0, by omega⟩ 1 zero_lt_one 0) x
          (fun z => unitVector (j z))‖) ≤ A := by
    interval_cases k
    · refine ⟨C₁, hC₁.le, ?_, hbound₁ _ Q _ j⟩
      dsimp only [E]
      norm_num only [Nat.cast_one]
      exact le_add_of_nonneg_right (by positivity)
    · refine ⟨C₂, hC₂.le, ?_, hbound₂ _ Q _ j⟩
      dsimp only [E]
      norm_num only [Nat.cast_ofNat]
      exact le_add_of_nonneg_left (by positivity)
  have hg := havg hd Q (Localization.finiteRange_map_reduce Q.measure Q.finiteRange)
    H K hKB hlocal hmean herr (s / 2) (half_pos hs)
  let ψ := unforcedGaussianDerivativeSchwartz Q ⟨0, by omega⟩
    (s / 2) (half_pos hs) k j
  have hop := bootstrap_point_kernel_Lp Q p hp (fun x => ψ (-x))
    (ψ.continuous.comp continuous_neg) ψ.integrable.comp_neg
    (gaussianAverage hd Q (s / 2) (half_pos hs) H) hg.1
  have heq : (∫ x : Vec d, ψ (-x) •
      complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x
        (gaussianAverage hd Q (s / 2) (half_pos hs) H)) =
      gaussianDerivativeAverage hd Q s hs k j H := by
    rw [SplitTail.gaussianDerivativeAverage_half_split hd Q s hs k j H]
    simp only [ψ, unforcedGaussianDerivativeSchwartz_apply, gaussianDerivativeAverage]
  dsimp only at hop
  rw [heq] at hop
  refine ⟨hop.1, hop.2.trans ?_⟩
  have hkern : (∫ x : Vec d, ‖ψ (-x)‖) ≤ A * (s / 2) ^ (-(k : ℝ) / 2) := by
    rw [show (∫ x : Vec d, ‖ψ (-x)‖) = ∫ x : Vec d, ‖ψ x‖ from
      integral_neg_eq_self (fun x : Vec d => ‖ψ x‖) volume]
    simp only [ψ, unforcedGaussianDerivativeSchwartz_apply]
    rw [SplitTail.gaussianDerivativeKernel_integral_scale]
    exact (mul_le_mul_of_nonneg_left hAbound (Real.rpow_nonneg (half_pos hs).le _)).trans_eq
      (mul_comm _ _)
  calc
    _ ≤ (A * (s / 2) ^ (-(k : ℝ) / 2)) *
        (C₀ * (s / 2) ^ (-(d : ℝ) / 4)) :=
      mul_le_mul hkern hg.2 ENNReal.toReal_nonneg (by positivity)
    _ = C₀ * (A * (2 : ℝ) ^ ((k : ℝ) / 2 + (d : ℝ) / 4)) *
        s ^ (-((k : ℝ) / 2 + (d : ℝ) / 4)) := by
      rw [Real.div_rpow hs.le (by norm_num), Real.div_rpow hs.le (by norm_num)]
      simp only [neg_div]
      rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
        Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
      simp only [div_inv_eq_mul]
      rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      have he : -((k : ℝ) / 2 + (d : ℝ) / 4) = -((k : ℝ) / 2) + -((d : ℝ) / 4) := by ring
      rw [he, Real.rpow_add hs]
      ring
    _ ≤ (C₀ * E) * s ^ (-((k : ℝ) / 2 + (d : ℝ) / 4)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hAweight hC₀)
        (Real.rpow_nonneg hs.le _)

end EinsteinFull.Blueprint
