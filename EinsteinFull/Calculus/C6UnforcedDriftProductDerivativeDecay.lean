import EinsteinFull.Calculus.C6UnforcedDriftProductApproximants
import EinsteinFull.Calculus.C7GaussianDerivativeApproximants
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation
/-- The centered unforced drift product has uniform Gaussian derivative decay. -/
theorem unforced_drift_product_derivative_decay
    : ∀ (hlocal : node_e_u3A_forced_u2D_localityStmt)
        (hends : node_stationary_u2D_analytic_u2D_semigroup_u23_endpointsStmt)
        (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) (T p : ℝ), 0 ≤ T → 2 ≤ p →
      ∃ C : ℝ, 1 ≤ C ∧
      ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q)
        (β : Fin d → Lp ℂ 2 (reducedLaw Q))
        (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
        IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
        IsReducedClockObservation Q μ →
      ∀ (P Pdag : ℂ → ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)),
        (∀ ζ, IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ (P ζ)) →
        (∀ ζ, IsComplexTransposeSemigroup Q (P ζ) (Pdag ζ)) →
      ∀ (t : ℝ≥0), (t : ℝ) ≤ T → ∀ (m l : Fin d),
        ∃ H : Lp ℂ 2 (reducedLaw Q),
          ((H : FieldPair d → ℂ) =ᵐ[reducedLaw Q] fun ω =>
            β l ω * P 0 t (β m) ω - ∫ η, β l η * P 0 t (β m) η ∂reducedLaw Q) ∧
          ∀ (k : ℕ), 1 ≤ k → k ≤ 2 →
          ∀ (dirs : Fin k → Fin d) (s : ℝ) (hs : 0 < s),
            MemLp (gaussianDerivativeAverage hd Q s hs k dirs H : FieldPair d → ℂ)
              (ENNReal.ofReal p) (reducedLaw Q) ∧
            (eLpNorm (gaussianDerivativeAverage hd Q s hs k dirs H : FieldPair d → ℂ)
              (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤
                C * s ^ (-((k : ℝ)/2+(d : ℝ)/4)) := by
  intro hlocal hends d hd D T p hT hp
  obtain ⟨B, R, L, c, hB, hR, hL, hc, happ⟩ :=
    unforced_drift_product_local_approximants hlocal hends d hd D T hT
  obtain ⟨C, hC, hdecay⟩ := gaussian_derivative_of_local_approximants
    d D R B L c p (by linarith) (by linarith) hL.le hc hp
  refine ⟨max 1 C, le_max_left _ _, ?_⟩
  intro Q hQ β a μ hβ ha hμ P Pdag hP hPdag t ht m l
  obtain ⟨H, hH, _, happrox⟩ := happ Q hQ β a μ hβ ha hμ P Pdag hP hPdag t ht m l
  have hRn (n : ℕ) : R ≤ R + (n : ℝ) := le_add_of_nonneg_right (Nat.cast_nonneg n)
  choose K hKlocal hKmean hKbound hKerr using fun n : ℕ => happrox (R+n) (hRn n)
  have herr (n : ℕ) : ‖H - K n‖ ≤ L * Real.exp (-c * (n : ℝ)^2) := by
    refine (hKerr n).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hL.le)
    have hsq : (n : ℝ)^2 ≤ (R + (n : ℝ))^2 := by
      nlinarith [show (0 : ℝ) ≤ (n : ℝ) from Nat.cast_nonneg n]
    exact mul_le_mul_of_nonpos_left hsq (neg_nonpos.mpr hc.le)
  refine ⟨H, hH, ?_⟩
  intro k hk₁ hk₂ dirs s hs
  obtain ⟨hmem, hnorm⟩ := hdecay hd Q H K hKbound hKlocal hKmean herr k hk₁ hk₂ dirs s hs
  exact ⟨hmem, hnorm.trans (mul_le_mul_of_nonneg_right (le_max_right 1 C)
    (Real.rpow_nonneg hs.le _))⟩

end EinsteinFull.Blueprint
