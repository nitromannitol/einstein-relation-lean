import EinsteinFull.Blueprint.G2.node_e_u3A_flux_u2D_block
import EinsteinFull.Blueprint.Foundation.node_e_u3A_forced_u2D_locality
import EinsteinFull.Blueprint.G2.node_l_u3A_forced_u2D_flux_u23_parameters
import EinsteinFull.Calculus.ComplexGeneratorUniquenessSupport
import EinsteinFull.Calculus.ComplexLpSupport
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real

open MeasureTheory
open scoped NNReal ENNReal

namespace EinsteinFull.Blueprint
open EinsteinRelation

/-- The gradient relation and literal flux formula determine the weak flux. -/
theorem carverS_endpoint_weak_flux_unique {d : ℕ} (hd : 2 ≤ d) {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (ν : EndpointIndex d) (ζ : ℂ)
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q))
    (U : Lp ℂ 2 (reducedLaw Q)) (G J H K : Fin d → Lp ℂ 2 (reducedLaw Q))
    (h : IsEndpointWeakFlux hd Q ν ζ a U G J)
    (h' : IsEndpointWeakFlux hd Q ν ζ a U H K) : G = H ∧ J = K := by
  have hGH := h.1.unique h'.1
  subst H
  refine ⟨rfl, funext fun j => Lp.ext ?_⟩
  exact (h.2 j).trans (h'.2 j).symm

/-- Centering preserves finite-p membership under the actual probability law. -/
theorem carverS_memLp_centered {d : ℕ} {Λ r : ℝ} (Q : EnvironmentLaw d Λ r)
    (f : Lp ℂ 2 (reducedLaw Q)) {p : ℝ≥0∞}
    (hf : MemLp (f : FieldPair d → ℂ) p (reducedLaw Q)) :
    MemLp (centeredComplexLp Q f : FieldPair d → ℂ) p (reducedLaw Q) := by
  let := reducedLaw_probability Q
  exact MemLp.ae_eq (coeFn_centeredComplexLp Q f).symm
    (hf.sub (memLp_const (∫ ω, f ω ∂reducedLaw Q)))

/-- Conditional expectation contracts the finite seminorm after centering. -/
theorem carverS_centered_condExp_contraction {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (f : Lp ℂ 2 (reducedLaw Q))
    {p : ℝ≥0∞} (hp : 1 ≤ p)
    (hf : MemLp (f : FieldPair d → ℂ) p (reducedLaw Q))
    (m : MeasurableSpace (FieldPair d)) :
    MemLp (centeredComplexLp Q f : FieldPair d → ℂ) p (reducedLaw Q) ∧
    MemLp ((reducedLaw Q)[(centeredComplexLp Q f : FieldPair d → ℂ) | m])
      p (reducedLaw Q) ∧
    (eLpNorm ((reducedLaw Q)[(centeredComplexLp Q f : FieldPair d → ℂ) | m])
      p (reducedLaw Q)).toReal ≤
      (eLpNorm (centeredComplexLp Q f : FieldPair d → ℂ) p (reducedLaw Q)).toReal := by
  have hc := carverS_memLp_centered Q f hf
  refine ⟨hc, hc.condExp hp, ?_⟩
  exact ENNReal.toReal_mono hc.eLpNorm_lt_top.ne
    (eLpNorm_condExp_le_eLpNorm _ hp)

/-- Finite-p conditional contraction for the actual centered endpoint blocks,
with the structural constants and weak-flux witnesses of the block estimate. -/
theorem carverS_conditional_block_contraction : EinsteinFull.Blueprint.node_e_u3A_flux_u2D_blockStmt →
    EinsteinFull.Blueprint.node_e_u3A_forced_u2D_localityStmt →
    EinsteinFull.Blueprint.node_l_u3A_forced_u2D_flux_u23_parametersStmt →
  ∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d),
    ∃ κ η η₀ Cenv : ℝ, ∃ Lblock : ℕ → ℕ,
      0 < κ ∧ κ < 1 / 2 ∧ 1 ≤ Cenv ∧
      η = κ / (16 * ((d : ℝ) + 2)) ∧ η₀ = η / 4 ∧
    ∀ p : ℝ, 2 ≤ p → ∃ growth₀ t₀ Cloc : ℝ, ∃ Cder : ℕ → ℝ,
      0 < growth₀ ∧ 1 ≤ t₀ ∧ 1 ≤ Cloc ∧ (∀ k, 1 ≤ Cder k) ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
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
        ‖ζ‖ * Real.sqrt (t : ℝ) ≤ (t : ℝ) ^ η₀ →
        ∀ growth K : ℝ, growth₀ ≤ growth → 1 ≤ K →
        MemLp (indexedEndpoint hd Q ν ζ P Pdag β a μ (t / 8) : FieldPair d → ℂ)
          (ENNReal.ofReal p) (reducedLaw Q) →
        (eLpNorm (indexedEndpoint hd Q ν ζ P Pdag β a μ (t / 8) : FieldPair d → ℂ)
          (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤
          K * Real.exp (growth * ‖ζ‖ ^ 2 * (t : ℝ) / 8) *
            (((t : ℝ) / 8) ^ (-(1 / 2 + (d : ℝ) / 4)) +
              ‖ζ‖ * ((t : ℝ) / 8) ^ (-(d : ℝ) / 4)) →

        ∀ (s : ℝ), 1 ≤ s → ∀ hs : 0 < s,
        ∀ (k : ℕ) (dirs : Fin k → Fin d),
          let r := (t : ℝ) ^ (1 / 2 + η)
          let R := 2 * Real.sqrt (d : ℝ) + 2
          let kernel := fun y : Vec d =>
            iteratedFDeriv ℝ k (homogenizedGaussianKernel Q ⟨0, by omega⟩ s hs 0)
              y (fun j => unitVector (dirs j))
          let W := fun (x z : Vec d) => sSup
            ((fun y : Vec d => s ^ (-(d : ℝ) / 2) *
              Real.exp (-euclideanNorm (x - y) ^ 2 / (Cenv * s))) ''
                {y : Vec d | euclideanNorm (y - z) ≤ R * r})
          ∀ χ : Vec d → ℝ,
            ContDiff ℝ (⊤ : ℕ∞) χ → HasCompactSupport χ →
            Function.support χ ⊆ {y : Vec d | euclideanNorm y ≤ R * r} →
            (∀ y, |χ y| ≤ 1) →
            (∀ y, Real.sqrt (∑ j : Fin d,
              (fderiv ℝ χ y (unitVector j)) ^ 2) ≤ R / r) →
          let B := fun (x z : Vec d) (j : Fin d) =>
            ∫ y : Vec d, (χ (y - z) * kernel (x - y)) •
              complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) y (J t j)
          (∀ y : Vec d, (∑' z : Fin d → ℤ,
            χ (y - fun j => r * (z j : ℝ))) = 1) →
          ∀ (x : Vec d) (j : Fin d),
            let center := fun (z : Fin d → ℤ) (j : Fin d) => r * (z j : ℝ)
            let X := fun (z : Fin d → ℤ) =>
              (centeredComplexLp Q (B x (center z) j) : FieldPair d → ℂ)
            let CE := fun (n : ℕ) (z : Fin d → ℤ) =>
              (reducedLaw Q)[X z | localSigma
                {y : Vec d | euclideanNorm (y - center z) < R * 2 ^ (n + 1) * r}]
            let A := fun (n : ℕ) (z : Fin d → ℤ) => CE (n + 1) z - CE n z
            let N := fun f : FieldPair d → ℂ =>
              (eLpNorm f (ENNReal.ofReal p) (reducedLaw Q)).toReal
            (∀ z : Fin d → ℤ,
              MemLp (X z) (ENNReal.ofReal p) (reducedLaw Q) ∧
              MemLp (CE 0 z) (ENNReal.ofReal p) (reducedLaw Q) ∧
              N (CE 0 z) ≤ N (X z)) := by
  intro hblock _hlocal _hparams d hd D
  obtain ⟨κ, η, η₀, Cenv, Lblock, hκ, hκ', hCenv, hη, hη₀, hb⟩ := hblock d hd D
  refine ⟨κ, η, η₀, Cenv, Lblock, hκ, hκ', hCenv, hη, hη₀, ?_⟩
  intro p hp
  obtain ⟨growth₀, t₀, Cder, hgrowth, ht₀, hCder, hb⟩ := hb p hp
  refine ⟨growth₀, t₀, 1, Cder, hgrowth, ht₀, le_rfl, hCder, ?_⟩
  intro Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν
  obtain ⟨G, J, hflux, hb⟩ := hb Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν
  refine ⟨G, J, hflux, ?_⟩
  intro t ht hζ growth K hg hK hmem hnorm s hs hs' k dirs
  dsimp only
  intro χ hχ hχc hχs hχb hχg _hpartition x j z
  have hB := (hb t ht hζ growth K hg hK hmem hnorm s hs hs' k dirs
    χ hχ hχc hχs hχb hχg x (fun j => (t : ℝ) ^ (1 / 2 + η) * (z j : ℝ)) j).1
  have hp' : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (le_trans (by norm_num) hp)
  exact carverS_centered_condExp_contraction Q _ hp' hB _

end EinsteinFull.Blueprint
