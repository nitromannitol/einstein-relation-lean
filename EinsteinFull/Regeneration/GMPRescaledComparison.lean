import EinsteinFull.Regeneration.GMPRescaledEllipticity

/-!
# Slab comparison for the rescaled source coefficient

The source ellipticity and continuity hypotheses supply the coefficient
conditions in the slab comparison uniformly over environments and rescalings.
-/

open MeasureTheory Set PDE EinsteinRelation
open scoped ENNReal

namespace EinsteinFull.Regeneration

/-- The rescaled source equation has the uniform slab comparison. -/
theorem exists_gmp_rescaled_slab_width (n : ℕ) (Λ : ℝ) (hΛ : 1 ≤ Λ) :
    ∃ L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L → ∀ (U : Set (PDE.Vec (n + 1)))
      (hU : PDE.IsOpenBoundedConvexDomain U) (u : PDE.H1Function U) (i : Fin (n + 1)),
      coordinateSlabBox n i 2 L ⊆ U →
      ∀ {x₀ : PDE.Vec (n + 1)} {r : ℝ}, 0 < r → Metric.closedBall x₀ r ⊆ U →
      Continuous u.toFun → (∀ x, 0 ≤ u x) → (∀ x, u x ≤ 1) →
      (∀ᵐ z ∂(volume.restrict
        (Icc (fun _ : Fin n => -Real.exp (2 * L / (n + 1)))
          (fun _ => Real.exp (2 * L / (n + 1))))),
        u (centralSlabPoint n i (-L, z)) = 0) →
      (∀ᵐ z ∂(volume.restrict
        (Icc (fun _ : Fin n => -Real.exp (2 * L / (n + 1)))
          (fun _ => Real.exp (2 * L / (n + 1))))),
        u (centralSlabPoint n i (L, z)) = 1) →
      ∀ (ω : FieldPair (n + 1)), IsRegular Λ ω → ∀ (y : PDE.Vec (n + 1)) (μ : ℝ),
      PDE.IsWeakDivergenceFormL2SolutionOn
        (fun x => Real.exp (2 * x i) • gmpRescaledCoefficient ω y μ x)
        (openForceSlab U i L)
        (u.restrict (isOpen_openForceSlab hU.isOpen i L) inter_subset_left) 0 0 →
      (2 / 3 : ℝ) ≤ u 0 := by
  have hΛpos : 0 < Λ := lt_of_lt_of_le zero_lt_one hΛ
  have hLam : Λ⁻¹ ≤ Λ := (inv_le_one_of_one_le₀ hΛ).trans hΛ
  obtain ⟨L₀, hL₀⟩ := exists_slab_width_of_open_equation n 2 Λ⁻¹ Λ
    (by norm_num) (inv_pos.mpr hΛpos) hLam
  refine ⟨L₀, ?_⟩
  intro L hL U hU u i hsource x₀ r hr hball hcont hzero hone hleft hright ω hω y μ hsol
  obtain ⟨lam', Λ', hEll⟩ := gmpRescaledCoefficient_weighted_elliptic hΛ ω hω y μ i hU
  have hmeas : ∀ j k, AEMeasurable (fun x => gmpRescaledCoefficient ω y μ x j k)
      (volume.restrict U) := by
    intro j k
    exact ((continuous_apply k).comp ((continuous_apply j).comp
      (continuous_gmpRescaledCoefficient ω y μ))).measurable.aemeasurable
  have hA : ∀ᵐ x ∂(PDE.volumeOn U), PDE.IsEllipticMatrix Λ⁻¹ Λ (gmpRescaledCoefficient ω y μ x) :=
    Filter.Eventually.of_forall (gmpRescaledCoefficient_elliptic hΛ ω hω y μ)
  have hsym : ∀ᵐ x ∂(PDE.volumeOn U), (gmpRescaledCoefficient ω y μ x).IsSymm :=
    Filter.Eventually.of_forall (gmpRescaledCoefficient_symm ω hω y μ)
  exact hL₀ L hL U hU u i hsource hr hball hcont hzero hone hleft hright
    (gmpRescaledCoefficient ω y μ) lam' Λ' hsol hEll hmeas hA hsym

end EinsteinFull.Regeneration
