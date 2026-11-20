import EinsteinFull.Regeneration.EllipticHarnackViaParabolic

/-!
# Stationary parabolic coefficients

Spatial measurability and ellipticity lift to the stationary space-time field.
-/

open MeasureTheory Set
open scoped ENNReal

namespace EinsteinFull.Regeneration

/-- Spatial coefficient bounds lift to a stationary parabolic coefficient. -/
theorem isParabolicCoeff_stationary {d : ℕ} (U : Set (PDE.Vec d)) (I : Set ℝ)
    [IsFiniteMeasure (volume.restrict I : Measure ℝ)] (a : PDE.CoeffField d)
    (lam Λ : ℝ) (hmeas : ∀ i j, AEMeasurable (fun x => a x i j) (volume.restrict U))
    (hell : ∀ᵐ x ∂(volume.restrict U), PDE.IsEllipticMatrix lam Λ (a x)) :
    PDE.IsParabolicCoeff lam Λ (fun z => a z.1) U I := by
  constructor
  · intro i j
    rw [PDE.Parabolic.Energy.volume_restrict_prod]
    exact (hmeas i j).comp_fst
  · rw [PDE.Parabolic.Energy.volume_restrict_prod]
    exact (MeasureTheory.Measure.quasiMeasurePreserving_fst
      (μ := volume.restrict U) (ν := volume.restrict I)).ae hell

/-- Continuous nonnegative elliptic solutions satisfy Harnack under spatial coefficient bounds. -/
theorem elliptic_pointwise_harnack_of_spatial_coeff (d : ℕ) (hd : 0 < d)
    (Λ : ℝ) (hΛ : 1 ≤ Λ) :
    ∃ H : ℝ, 2 ≤ H ∧ ∀ (a : PDE.CoeffField d) (θ : ℝ), 0 < θ →
      ∀ z z' : PDE.Vec d, PDE.euclideanSqDist z z' ≤ θ / 4 →
      let U := PDE.euclideanBall ((1 / 2 : ℝ) • (z + z')) (Real.sqrt (2 * θ))
      (∀ i j, AEMeasurable (fun x => a x i j) (volume.restrict U)) →
      (∀ᵐ x ∂(volume.restrict U), PDE.IsEllipticMatrix 1 Λ (a x)) →
      ∀ u : PDE.H1Function U, PDE.IsWeakDivergenceFormL2SolutionOn a U u 0 0 →
      Continuous u.toFun → (∀ x, 0 ≤ u.toFun x) → u z ≤ H * u z' := by
  obtain ⟨H, hH, hcomp⟩ := elliptic_pointwise_harnack_of_parabolic_coeff d hd Λ hΛ
  refine ⟨H, hH, ?_⟩
  intro a θ hθ z z' hdist
  dsimp only
  intro hmeas hell u hsol hcont hnonneg
  let U := PDE.euclideanBall ((1 / 2 : ℝ) • (z + z')) (Real.sqrt (2 * θ))
  let I := Ioc ((0 : ℝ) - 3 * θ / 2) ((0 : ℝ) + 5 * θ / 4)
  let : IsFiniteMeasure (volume.restrict I : Measure ℝ) := by dsimp [I]; infer_instance
  have hcoeff : PDE.IsParabolicCoeff 1 Λ (fun p => a p.1) U I :=
    isParabolicCoeff_stationary U I a 1 Λ hmeas hell
  exact hcomp a 0 θ hθ z z' hdist hcoeff u hsol hcont hnonneg

end EinsteinFull.Regeneration
