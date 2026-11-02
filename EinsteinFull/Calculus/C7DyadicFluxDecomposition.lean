import EinsteinFull.Calculus.C10DyadicLargeWindowProjection
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation
theorem dyadic_flux_decomposition {d : ℕ} (hd : 2 ≤ d) {Λ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ r₀) (ζ : ℂ)
    (P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (β : Fin d → Lp ℂ 2 (reducedLaw Q))
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q))
    (ha : IsReducedCoefficientObservation Q a)
    (G F : ℝ≥0 → FluxIndex d → Fin d → Lp ℂ 2 (reducedLaw Q))
    (hF : IsFiniteTimeFlux hd Q ζ P Pdag β a μ G F)
    (s u : ℝ≥0) (hsu : s ≤ u) (ν : FluxIndex d) :
    ∃ Y B : Fin d → Lp ℂ 2 (reducedLaw Q),
      (∀ j, (Y j : FieldPair d → ℂ) =ᵐ[reducedLaw Q]
        fun ω => ∑ k : Fin d, a j k ω *
          (∫ r in Set.Icc (s : ℝ) (u : ℝ), G r.toNNReal ν k) ω) ∧
      (∀ j, (B j : FieldPair d → ℂ) =ᵐ[reducedLaw Q]
        fun ω => ν.elim (fun _ => 0) (fun _ =>
          -2 * ζ * a j ⟨0, by omega⟩ ω *
            (∫ r in Set.Icc (s : ℝ) (u : ℝ),
              transposeEndpoint Q ⟨0, by omega⟩ Pdag β r.toNNReal) ω)) ∧
      (∀ j, F u ν j - F s ν j = Y j + B j) ∧
      (∀ j, Y j = ∑ k : Fin d, complexCoefficientMul Q j k
        (∫ r in Set.Icc (s : ℝ) (u : ℝ), G r.toNNReal ν k)) ∧
      (∀ j, B j = ν.elim (fun _ => 0) (fun _ => (-2 * ζ) •
        complexCoefficientMul Q j ⟨0, by omega⟩
          (∫ r in Set.Icc (s : ℝ) (u : ℝ),
            transposeEndpoint Q ⟨0, by omega⟩ Pdag β r.toNNReal))) := by
  classical
  let H (k : Fin d) := ∫ r in Set.Icc (s : ℝ) (u : ℝ), G r.toNNReal ν k
  let T := ∫ r in Set.Icc (s : ℝ) (u : ℝ),
    transposeEndpoint Q ⟨0, by omega⟩ Pdag β r.toNNReal
  let Y (j : Fin d) := ∑ k : Fin d, complexCoefficientMul Q j k (H k)
  let B (j : Fin d) : Lp ℂ 2 (reducedLaw Q) :=
    ν.elim (fun _ => 0) (fun _ => (-2 * ζ) •
      complexCoefficientMul Q j ⟨0, by omega⟩ T)
  refine ⟨Y, B, ?_, ?_, ?_, fun _ => rfl, fun _ => rfl⟩
  · intro j
    filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ
      (fun k => complexCoefficientMul Q j k (H k)),
      ae_all_iff.mpr (fun k => complexCoefficientMul_coe Q j k (H k)),
      ae_all_iff.mpr (ha j)] with ω hsum hmul haω
    change (∑ k, complexCoefficientMul Q j k (H k)) ω = _
    rw [hsum]
    apply Finset.sum_congr rfl
    intro k _
    rw [hmul k, ← haω k]
  · intro j
    cases ν with
    | inl i => exact Lp.coeFn_zero ℂ 2 (reducedLaw Q)
    | inr b =>
      filter_upwards [Lp.coeFn_smul (-2 * ζ)
        (complexCoefficientMul Q j ⟨0, by omega⟩ T),
        complexCoefficientMul_coe Q j ⟨0, by omega⟩ T,
        ha j ⟨0, by omega⟩] with ω hsmul hmul haω
      change (((-2 * ζ) • complexCoefficientMul Q j ⟨0, by omega⟩ T)
        : Lp ℂ 2 (reducedLaw Q)) ω = _
      rw [hsmul]
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [hmul, ← haω]
      simp only [Sum.elim_inr]
      ring
  · exact largeWindow_flux_split hd Q ζ P Pdag β a μ ha G F hF s u hsu ν
end EinsteinFull.Blueprint
