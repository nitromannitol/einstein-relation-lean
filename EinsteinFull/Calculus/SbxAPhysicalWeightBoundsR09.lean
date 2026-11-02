import EinsteinFull.Calculus.SbxS4KilledSpectralR01
import EinsteinRelation.Regeneration.Coupling

/-! Bounds for the physical reversible density in a coupling region. -/

open EinsteinRelation EinsteinRelation.Regeneration
open EinsteinRelation.External.GantertSection7Support

namespace EinsteinFull.Calculus

/-- Normalization at an arbitrary center preserves a uniform density bound whenever
    the force times the Euclidean displacement is bounded. -/
theorem a_physical_density_normalized_bounds {d : ℕ} (hd : 2 ≤ d)
    (Λ : ℝ) (ω : FieldPair d) (hω : IsRegular Λ ω)
    (lam M : ℝ) (c z : Vec d)
    (hgeom : |lam| * euclideanNorm (z - c) ≤ M) :
    Real.exp (-2 * M - 2 * Λ) ≤ s4PhysicalRho hd ω lam z / physicalForceWeight hd lam c ∧
      s4PhysicalRho hd ω lam z / physicalForceWeight hd lam c ≤ Real.exp (2 * M + 2 * Λ) := by
  have hv := abs_le.mp (hω.2.1 z)
  have hc := coordinate_abs_le_euclideanNorm (z - c) (firstCoordinateIndex hd)
  have ha : |lam * ((z - c) (firstCoordinateIndex hd))| ≤ M := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left hc (abs_nonneg lam)).trans hgeom
  have ha' := abs_le.mp ha
  have heq : s4PhysicalRho hd ω lam z / physicalForceWeight hd lam c =
      Real.exp (2 * (lam * ((z - c) (firstCoordinateIndex hd))) - 2 * ω.2 z) := by
    rw [s4PhysicalRho, physicalReversibleDensity_eq_source_formula, physicalForceWeight,
      ← Real.exp_sub]
    congr 1
    simp only [Pi.sub_apply]
    ring
  rw [heq]
  constructor <;> apply Real.exp_le_exp.mpr <;> linarith

/-- The bounds are uniform in all regular environments and signed forces with
    the prescribed product of force magnitude and coupling scale. -/
theorem a_coupling_physical_density_normalized_bounds {d : ℕ} (hd : 2 ≤ d)
    (Λ l : ℝ) (i : Fin d) :
    ∀ (R lam : ℝ), 0 < R → l = |lam| * R →
    ∀ (ω : FieldPair d), IsRegular Λ ω → ∀ (x z : Vec d),
    z ∈ couplingRegion i R x →
    Real.exp (-2 * (6 * l) - 2 * Λ) ≤
      s4PhysicalRho hd ω lam z / physicalForceWeight hd lam (x + (5 * R) • unitVector i) ∧
    s4PhysicalRho hd ω lam z / physicalForceWeight hd lam (x + (5 * R) • unitVector i) ≤
      Real.exp (2 * (6 * l) + 2 * Λ) := by
  intro R lam hR hl ω hω x z hz
  apply a_physical_density_normalized_bounds hd Λ ω hω lam (6 * l)
  change euclideanNorm (z - (x + (5 * R) • unitVector i)) < 6 * R at hz
  calc
    |lam| * euclideanNorm (z - (x + (5 * R) • unitVector i)) ≤ |lam| * (6 * R) :=
      mul_le_mul_of_nonneg_left hz.le (abs_nonneg lam)
    _ = 6 * l := by rw [hl]; ring

/-- The scalar-normalized physical coefficient inherits the elliptic quadratic
    form bounds of the actual field on the same displacement scale. -/
theorem a_physical_alpha_normalized_bounds {d : ℕ} (hd : 2 ≤ d)
    (Λ : ℝ) (hΛ : 1 ≤ Λ) (ω : FieldPair d) (hω : IsRegular Λ ω)
    (lam M : ℝ) (c z ξ : Vec d)
    (hgeom : |lam| * euclideanNorm (z - c) ≤ M) :
    ((1 / 2 : ℝ) * Real.exp (-2 * M - 2 * Λ) * Λ⁻¹) * euclideanSq ξ ≤
      dot ξ (((physicalForceWeight hd lam c)⁻¹ • s4PhysicalAlpha hd ω lam z).mulVec ξ) ∧
    dot ξ (((physicalForceWeight hd lam c)⁻¹ • s4PhysicalAlpha hd ω lam z).mulVec ξ) ≤
      ((1 / 2 : ℝ) * Real.exp (2 * M + 2 * Λ) * Λ) * euclideanSq ξ := by
  have hρ := a_physical_density_normalized_bounds hd Λ ω hω lam M c z hgeom
  have hsq : 0 ≤ euclideanSq ξ := by
    unfold euclideanSq dot
    exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
  have he := (hω.1 z).2 ξ
  have hΛ0 : 0 ≤ Λ := by linarith
  have hlow : 0 ≤ Λ⁻¹ * euclideanSq ξ := mul_nonneg (inv_nonneg.mpr hΛ0) hsq
  have hnorm : 0 ≤ s4PhysicalRho hd ω lam z / physicalForceWeight hd lam c :=
    (Real.exp_pos _).le.trans hρ.1
  have hdot : dot ξ (((physicalForceWeight hd lam c)⁻¹ • s4PhysicalAlpha hd ω lam z).mulVec ξ) =
      ((1 / 2 : ℝ) * (s4PhysicalRho hd ω lam z / physicalForceWeight hd lam c)) *
        dot ξ ((ω.1 z).mulVec ξ) := by
    simp only [s4PhysicalAlpha, smul_smul, Matrix.smul_mulVec, dot, Pi.smul_apply,
      smul_eq_mul, Finset.mul_sum, div_eq_mul_inv]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hdot]
  constructor
  · have h1 := mul_le_mul_of_nonneg_right hρ.1 hlow
    have h2 := mul_le_mul_of_nonneg_left he.1 hnorm
    nlinarith only [h1, h2]
  · have h1 := mul_le_mul_of_nonneg_left he.2 hnorm
    have h2 := mul_le_mul_of_nonneg_right hρ.2 (mul_nonneg hΛ0 hsq)
    nlinarith only [h1, h2]

#print axioms a_physical_alpha_normalized_bounds
#print axioms a_physical_density_normalized_bounds
#print axioms a_coupling_physical_density_normalized_bounds

end EinsteinFull.Calculus
