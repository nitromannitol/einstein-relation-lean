import EinsteinFull.Calculus.C7UnitInitializationSupport
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation EinsteinFull.UnitInitialization
/-- Gaussian averaging of the bounded-time endpoint force difference retains
the force factor and the full spatial decay for every finite exponent. -/
theorem bounded_time_gaussian_force_difference
    (hlocal : node_e_u3A_forced_u2D_localityStmt)
    (hends : node_stationary_u2D_analytic_u2D_semigroup_u23_endpointsStmt)
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) (T p : ℝ) (hT : 0 ≤ T)
    (hp : 2 ≤ p) :
    ∃ C : ℝ, 1 ≤ C ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ → ∀ ζ : ℂ,
    ∀ P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P →
      IsComplexTransposeSemigroup Q P Pdag → ∀ ν : EndpointIndex d,
      ‖ζ‖ ≤ 2 → ∀ t : ℝ≥0, (t : ℝ) ≤ T →
    ∀ (s : ℝ) (hs : 0 < s),
      let U₀ := indexedEndpoint hd Q ν 0 (forcedComplexEvolution Q ⟨0, by omega⟩ 0)
        (fun u => complexL2Transpose (reducedLaw Q)
          (forcedComplexEvolution Q ⟨0, by omega⟩ 0 u)) β a μ t
      let F := gaussianAverage hd Q s hs (indexedEndpoint hd Q ν ζ P Pdag β a μ t - U₀)
      MemLp (F : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q) ∧
      (eLpNorm (F : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤
        C * ‖ζ‖ * s ^ (-(d : ℝ)/4) := by
  classical
  let : Fact (1 ≤ ENNReal.ofReal p) := ⟨by
    exact_mod_cast ENNReal.ofReal_le_ofReal (show (1 : ℝ) ≤ p by linarith)⟩
  obtain ⟨C, hC, hbound⟩ :=
    exists_all_time_gaussian_force_quotient hlocal hends d hd D T p hT hp
  refine ⟨max 1 C, le_max_left _ _, ?_⟩
  intro Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν hζ t ht s hs
  dsimp only
  by_cases hz : ζ = 0
  · subst ζ
    have he : P = forcedComplexEvolution Q ⟨0, by omega⟩ 0 :=
      hP.eq_forcedComplexEvolution
    have het : Pdag = fun u => complexL2Transpose (reducedLaw Q)
        (forcedComplexEvolution Q ⟨0, by omega⟩ 0 u) := by
      rw [hPdag.eq_complexL2Transpose, he]
    rw [he, het, sub_self]
    have hg : gaussianAverage hd Q s hs 0 = 0 := by
      change homogeneousAverageCLM Q ⟨0, by omega⟩ s hs 0 0 = 0
      exact map_zero _
    rw [hg]
    constructor
    · exact (MemLp.zero : MemLp (0 : FieldPair d → ℂ)
        (ENNReal.ofReal p) (reducedLaw Q)).ae_eq (Lp.coeFn_zero ℂ 2 (reducedLaw Q)).symm
    · simp only [eLpNorm_congr_ae (Lp.coeFn_zero ℂ 2 (reducedLaw Q)),
        eLpNorm_zero, ENNReal.toReal_zero, norm_zero, mul_zero, zero_mul, le_refl]
  · obtain ⟨E, E₀, H, he, he₀, hfactor, _, hb⟩ :=
      hbound Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν hζ hz t ht
    have hE : E = indexedEndpoint hd Q ν ζ P Pdag β a μ t := Lp.ext he
    have hE₀ : E₀ = indexedEndpoint hd Q ν 0
        (forcedComplexEvolution Q ⟨0, by omega⟩ 0)
        (fun u => complexL2Transpose (reducedLaw Q)
          (forcedComplexEvolution Q ⟨0, by omega⟩ 0 u)) β a μ t := Lp.ext he₀
    rw [← hE, ← hE₀, hfactor]
    have hg : gaussianAverage hd Q s hs (ζ • H) =
        ζ • gaussianAverage hd Q s hs H := by
      change homogeneousAverageCLM Q ⟨0, by omega⟩ s hs 0 (ζ • H) =
        ζ • homogeneousAverageCLM Q ⟨0, by omega⟩ s hs 0 H
      exact map_smul _ _ _
    rw [hg]
    obtain ⟨hm, hn⟩ := hb s hs
    have hae := Lp.coeFn_smul ζ (gaussianAverage hd Q s hs H)
    constructor
    · exact (hm.const_smul ζ).ae_eq hae.symm
    · rw [eLpNorm_congr_ae hae, eLpNorm_const_smul, ENNReal.toReal_mul,
        ← ofReal_norm, ENNReal.toReal_ofReal (norm_nonneg _)]
      calc
        ‖ζ‖ * (eLpNorm (gaussianAverage hd Q s hs H : FieldPair d → ℂ)
            (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤
            ‖ζ‖ * (C * s ^ (-(d : ℝ) / 4)) :=
          mul_le_mul_of_nonneg_left hn (norm_nonneg _)
        _ ≤ max 1 C * ‖ζ‖ * s ^ (-(d : ℝ) / 4) := by
          have hc := mul_le_mul_of_nonneg_right (le_max_right 1 C)
            (mul_nonneg (norm_nonneg ζ) (Real.rpow_nonneg hs.le (-(d : ℝ) / 4)))
          simpa only [mul_assoc, mul_comm, mul_left_comm] using hc
end EinsteinFull.Blueprint
