import EinsteinFull.Calculus.C14DyadicGainProducer

open MeasureTheory
open scoped NNReal ENNReal Topology
namespace EinsteinFull.Blueprint
open EinsteinRelation EinsteinFull

theorem c3_dyadic_actual_L2_flux_gain (hlocal : node_l_u3A_forced_u2D_localStmt) (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) : ∃ ε growth₀ t₀ : ℝ, ∃ Cder : ℕ → ℝ, ∃ L : ℕ → ℕ, 0 < ε ∧ 0 < growth₀ ∧ 1 ≤ t₀ ∧ (∀ k, 0 < Cder k) ∧ ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
        (hQ : HasSmoothBounds D Q)
        (β : Fin d → Lp ℂ 2 (reducedLaw Q))
        (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
        IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
        IsReducedClockObservation Q μ → ∀ ζ : ℂ,
      ∀ P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
        IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P →
        IsComplexTransposeSemigroup Q P Pdag → ∀ ν : EndpointIndex d,
      ∃ G J : ℝ≥0 → Fin d → Lp ℂ 2 (reducedLaw Q),
        (∀ t : ℝ≥0, 0 < (t : ℝ) →
          IsEndpointWeakFlux hd Q ν ζ a (indexedEndpoint hd Q ν ζ P Pdag β a μ t)
            (G t) (J t)) ∧
        ∀ (t : ℝ≥0), t₀ ≤ (t : ℝ) →
        ‖ζ‖ * Real.sqrt (t : ℝ) ≤ 1 →
        ∀ growth K : ℝ, growth₀ ≤ growth → 1 ≤ K →
        MemLp (indexedEndpoint hd Q ν ζ P Pdag β a μ (t / 8) : FieldPair d → ℂ)
          2 (reducedLaw Q) →
        (eLpNorm (indexedEndpoint hd Q ν ζ P Pdag β a μ (t / 8) : FieldPair d → ℂ)
          2 (reducedLaw Q)).toReal ≤
          K * Real.exp (growth * ‖ζ‖ ^ 2 * (t : ℝ) / 8) *
            (((t : ℝ) / 8) ^ (-(1 / 2 + (d : ℝ) / 4)) +
              ‖ζ‖ * ((t : ℝ) / 8) ^ (-(d : ℝ) / 4)) →
        ∀ (s : ℝ), 1 ≤ s → ∀ hs : 0 < s,
        ∀ (k : ℕ) (dirs : Fin k → Fin d),
          (∀ j : Fin d, MemLp
            (gaussianDerivativeAverage hd Q s hs k dirs (centeredComplexLp Q (J t j)) :
              FieldPair d → ℂ) 2 (reducedLaw Q)) ∧
          Real.sqrt (∑ j : Fin d, ((eLpNorm
            (gaussianDerivativeAverage hd Q s hs k dirs (centeredComplexLp Q (J t j)) :
              FieldPair d → ℂ) 2 (reducedLaw Q)).toReal) ^ 2) ≤
            Cder k * K * Real.exp (growth * ‖ζ‖ ^ 2 * (t : ℝ) / 2) *
              (t : ℝ) ^ (-1 - ε) * s ^ (-(d : ℝ) / 4 - (k : ℝ) / 2) *
                (1 + (t : ℝ) / s) ^ L k := by
  obtain ⟨κ, η, η₀, ε, Clat, L, hκ, hκlt, hη, hη₀, hε, hεpos, hη₀pos, hClat, hexp, hsum, hp⟩ :=
    c14_dyadic_flux_gain hlocal d hd D
  obtain ⟨growth₀, t₀, Cder, hgrowth, ht₀, hCder, hactual, htest⟩ := hp 2 (by norm_num)
  refine ⟨ε, growth₀, t₀, Cder, L, hεpos, hgrowth, ht₀, hCder, ?_⟩
  intro Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν
  obtain ⟨G, J, hflux, hgain⟩ := hactual Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν
  refine ⟨G, J, hflux, ?_⟩
  intro t ht hforce growth K hg hK hmem hbound s hs hspos k dirs
  have htone : (1 : ℝ) ≤ t := le_trans ht₀ ht
  have hwide : ‖ζ‖ * Real.sqrt (t : ℝ) ≤ (t : ℝ) ^ η₀ :=
    le_trans hforce (Real.one_le_rpow htone (le_of_lt hη₀pos))
  simpa only [ENNReal.ofReal_ofNat] using
    hgain t ht hwide growth K hg hK (by simpa using hmem) (by simpa using hbound) s hs hspos k dirs

end EinsteinFull.Blueprint
