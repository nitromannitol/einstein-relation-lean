import EinsteinFull.Blueprint.G2.node_l_u3A_forced_u2D_flux_u23_independent_u2D_blocks
import EinsteinFull.Calculus.C28FluxGaussianEnvelopePositivity

noncomputable section
open MeasureTheory
open scoped NNReal ENNReal
namespace EinsteinFull.Blueprint
open EinsteinRelation EinsteinFull

theorem c19_v2_actual_single_block_bounds
    (hV2 : node_l_u3A_forced_u2D_flux_u23_independent_u2D_blocksStmtV2) :
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
            ∀ z : Fin d → ℤ,
            MemLp (X z) (ENNReal.ofReal p) (reducedLaw Q) ∧
            N (X z) ≤
              Cder k * K * Real.exp (growth * ‖ζ‖ ^ 2 * (t : ℝ) / 2) *
                (t : ℝ) ^ (-1 - (1 / 2 + (d : ℝ) / 4)) *
                r ^ ((d : ℝ) + 1 - κ) * s ^ (-(k : ℝ) / 2) *
                (1 + (t : ℝ) / s) ^ Lblock k * W x (center z) +
              Cder k * (2 + (t : ℝ)) ^ Cloc *
                Real.exp (Cloc * ‖ζ‖ ^ 2 * (t : ℝ) - (t : ℝ) ^ (2 * η) / Cloc) *
                r ^ d * s ^ (-(k : ℝ) / 2) * W x (center z) ∧
            ∀ n : ℕ,
              MemLp (X z - CE n z) (ENNReal.ofReal p) (reducedLaw Q) ∧
              N (X z - CE n z) ≤
                Cder k * (2 + (t : ℝ)) ^ Cloc *
                  Real.exp (Cloc * ‖ζ‖ ^ 2 * (t : ℝ) -
                    4 ^ n * (t : ℝ) ^ (2 * η) / Cloc) *
                  r ^ d * s ^ (-(k : ℝ) / 2) * W x (center z) := by
  intro d hd D
  obtain ⟨κ, η, η₀, Cenv, Lblock, hκ, hκ', hCenv, hη, hη₀, hv⟩ := hV2 d hd D
  refine ⟨κ, η, η₀, Cenv, Lblock, hκ, hκ', hCenv, hη, hη₀, ?_⟩
  intro p hp
  obtain ⟨growth₀, t₀, Cloc, Cder, hg, ht₀, hCloc, hCder, hv⟩ := hv p hp
  refine ⟨growth₀, t₀, Cloc, Cder, hg, ht₀, hCloc, hCder, ?_⟩
  intro Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν
  obtain ⟨G, J, hflux, hv⟩ := hv Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν
  refine ⟨G, J, hflux, ?_⟩
  intro t ht hforce growth K hgrowth hK hm hb s hs hs' k dirs
  dsimp only
  intro χ hχ hcompact hsupp hχbound hder
  intro hpartition x j
  have hv := hv t ht hforce growth K hgrowth hK hm hb s hs hs' k dirs χ hχ hcompact hsupp hχbound hder hpartition x j
  intro z
  have hW : 0 ≤ (sSup ((fun y : Vec d => s ^ (-(d : ℝ) / 2) *
      Real.exp (-euclideanNorm (x-y)^2 / (Cenv*s))) ''
      {y : Vec d | euclideanNorm (y - (fun j => (t : ℝ) ^ (1 / 2 + η) * (z j : ℝ))) ≤
        (2 * Real.sqrt (d : ℝ) + 2) * (t : ℝ) ^ (1 / 2 + η)})) := by
    apply le_of_lt
    apply c28_actual_gaussian_spatial_envelope_positive s Cenv hs' x _
    positivity
  have hsingle := hv.2.2.2.2.2 ({z} : Finset (Fin d → ℤ))
  simp only [Finset.sum_singleton, Real.sqrt_sq hW] at hsingle
  refine ⟨hv.1 z |>.1, ?_, fun n => hv.2.2.1 n z⟩
  have herr : 0 ≤ Cder k * (2 + (t : ℝ)) ^ Cloc *
      Real.exp (Cloc * ‖ζ‖ ^ 2 * (t : ℝ) - (t : ℝ) ^ (2 * η) / Cloc) *
      ((t : ℝ) ^ (1 / 2 + η)) ^ d * s ^ (-(k : ℝ) / 2) *
      (sSup ((fun y : Vec d => s ^ (-(d : ℝ) / 2) *
        Real.exp (-euclideanNorm (x-y)^2 / (Cenv*s))) ''
        {y : Vec d | euclideanNorm (y - (fun j => (t : ℝ) ^ (1 / 2 + η) * (z j : ℝ))) ≤
          (2 * Real.sqrt (d : ℝ) + 2) * (t : ℝ) ^ (1 / 2 + η)})) := by
    have : 0 ≤ Cder k := le_trans (by norm_num) (hCder k)
    positivity
  exact le_trans hsingle.2 (le_add_of_nonneg_right herr)

end EinsteinFull.Blueprint
