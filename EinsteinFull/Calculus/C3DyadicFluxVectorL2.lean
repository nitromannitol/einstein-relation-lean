import EinsteinFull.Calculus.C3BootstrapAverageSupport

open EinsteinRelation EinsteinFull MeasureTheory
open scoped NNReal ENNReal Topology

namespace EinsteinFull.Blueprint

/-- The actual propagated flux satisfies its uniform bound in L². -/
theorem c3_dyadic_flux_vector_L2_bound {d : ℕ} (hd : 2 ≤ d) {Λ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ r₀) (ν : EndpointIndex d) (ζ : ℂ)
    (J : ℝ≥0 → Fin d → Lp ℂ 2 (reducedLaw Q))
    (s : ℝ) (hs : 0 < s) (t r b ε growth K : ℝ) (L : ℕ → ℕ)
    (Cder : ℕ → ℝ) (ht : 0 < t) (hr : t / 2 ≤ r) (hrt : r ≤ t)
    (hb : 0 < b) (hbs : b * t ≤ s) (hε : 0 ≤ ε) (hK : 0 ≤ K)
    (hCder : ∀ k, 0 ≤ Cder k) (hgrowth : 0 ≤ growth)
    (hrate : sourceReducedBound Λ ≤ growth)
    (hflux : ∀ k : ℕ, ∀ dirs : Fin k → Fin d,
      (∀ j, MemLp
        (gaussianDerivativeAverage hd Q s hs k dirs (centeredComplexLp Q (J r.toNNReal j)) :
          FieldPair d → ℂ) 2 (reducedLaw Q)) ∧
      Real.sqrt (∑ j, ((eLpNorm
        (gaussianDerivativeAverage hd Q s hs k dirs (centeredComplexLp Q (J r.toNNReal j)) :
          FieldPair d → ℂ) 2 (reducedLaw Q)).toReal) ^ 2) ≤
        Cder k * K * Real.exp (growth * ‖ζ‖ ^ 2 * r / 2) *
          r ^ (-1 - ε) * s ^ (-(d : ℝ) / 4 - (k : ℝ) / 2) * (1 + r / s) ^ L k) :
    ‖c3BootstrapFluxVector hd Q ν ζ J s hs t r‖ ≤
      Real.exp (growth * ‖ζ‖ ^ 2 * t) * (t / 2) ^ (-1 - ε) * K *
        ((d : ℝ) / 2 * Cder 1 * (1 + b⁻¹) ^ L 1 * s ^ (-(d : ℝ) / 4 - 1 / 2) +
          ‖ζ‖ * Cder 0 * (1 + b⁻¹) ^ L 0 * s ^ (-(d : ℝ) / 4)) := by
  have h := c3BootstrapFluxVector_uniform_bound hd Q ν ζ J s hs t r b ε growth K 2 L Cder
    (by norm_num) ht hr hrt hb hbs hε hK hCder hgrowth hrate (by simpa using hflux)
  simpa only [ENNReal.ofReal_ofNat, Lp.norm_def] using h.2

end EinsteinFull.Blueprint
