import EinsteinFull.Calculus.C7UnforcedCoefficientProductApproximants
import EinsteinFull.Calculus.C7GaussianDerivativeApproximants
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation
/-- Centered zero-force coefficient products have first and second derivative decay. -/
theorem unforced_coefficient_product_derivative_decay
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
      ∀ (t : ℝ≥0), (t : ℝ) ≤ T → ∀ (m j l : Fin d) (k : ℕ), 1 ≤ k → k ≤ 2 →
      ∀ (dirs : Fin k → Fin d) (s : ℝ) (hs : 0 < s),
        let H := centeredComplexLp Q (complexCoefficientMul Q j l (P 0 t (β m)))
        MemLp (gaussianDerivativeAverage hd Q s hs k dirs H : FieldPair d → ℂ)
          (ENNReal.ofReal p) (reducedLaw Q) ∧
        (eLpNorm (gaussianDerivativeAverage hd Q s hs k dirs H : FieldPair d → ℂ)
          (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤
            C * s ^ (-((k : ℝ)/2+(d : ℝ)/4)) := by
  intro hlocal hends d hd D T p hT hp
  obtain ⟨B, R, L, c, hB, hR, hL, hc, happ⟩ :=
    unforced_coefficient_product_local_approximants hlocal hends d hd D T hT
  obtain ⟨C, hC, hdecay⟩ := gaussian_derivative_of_local_approximants
    d D R B L c p (zero_le_one.trans hR) (zero_le_one.trans hB) hL.le hc hp
  refine ⟨max 1 C, le_max_left _ _, ?_⟩
  intro Q hQ β a μ hβ ha hμ P Pdag hP hPdag t ht m j l k hk₁ hk₂ dirs s hs
  let H := centeredComplexLp Q (complexCoefficientMul Q j l (P 0 t (β m)))
  have happrox := (happ Q hQ β a μ hβ ha hμ P Pdag hP hPdag t ht m j l).2
  have hradius (n : ℕ) : R ≤ R + (n : ℝ) := le_add_of_nonneg_right (Nat.cast_nonneg n)
  choose K hKlocal hKmean hKbound hKerror using fun n : ℕ => happrox (R + n) (hradius n)
  have herr (n : ℕ) : ‖H - K n‖ ≤ L * Real.exp (-c * (n : ℝ)^2) := by
    apply (hKerror n).trans
    apply mul_le_mul_of_nonneg_left _ hL.le
    apply Real.exp_le_exp.mpr
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hRn : (n : ℝ)^2 ≤ (R + n)^2 := by
      nlinarith [zero_le_one.trans hR]
    exact mul_le_mul_of_nonpos_left hRn (neg_nonpos.mpr hc.le)
  obtain ⟨hmem, hnorm⟩ := hdecay hd Q H K hKbound hKlocal hKmean herr
    k hk₁ hk₂ dirs s hs
  refine ⟨hmem, hnorm.trans ?_⟩
  exact mul_le_mul_of_nonneg_right (le_max_right 1 C) (Real.rpow_nonneg hs.le _)

end EinsteinFull.Blueprint
