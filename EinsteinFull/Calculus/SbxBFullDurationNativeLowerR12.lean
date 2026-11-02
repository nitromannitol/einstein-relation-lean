import EinsteinFull.Calculus.SbxBCappedNativeLowerR03

open EinsteinRelation MeasureTheory EinsteinFull.External.Source.GMP
open PDE hiding Vec Mat
open EinsteinFull.Blueprint.TubeProbability

namespace EinsteinFull.Calculus

/-- Prescribed-start native half-survival and pointwise comparison yield
both orientations of the kernel bound for arbitrary positive total time. -/
theorem b_full_duration_native_lower
    (d : ℕ) (hd : 2 ≤ d) (κ δ H S T : ℝ)
    (hκ : 0 < κ) (hδ : 0 < δ) (hH : 0 < H) (hS : 0 < S) (hT : 0 < T) :
    ∃ c : ℝ, 0 < c ∧ ∀ (R lam : ℝ),
    0 < R → 0 < lam → S = lam * R →
    ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d), IsUniformlyElliptic κ ρ α →
    ∀ (K : ℝ → Vec d → Vec d → ℝ) (G : ℝ → Vec d → Vec d → Vec d),
    IsSpectralDirichletFundamentalSolution ρ α R K G →
    (∀ (x : Vec d) (r u : ℝ), 0 < r → sourceBall x (2*r) ⊆ sourceBall 0 R →
      0 < u → u ≤ δ*r^2 → (1/2 : ℝ) ≤ ∫ y in sourceBall 0 R, K u x y) →
    (∀ (x y : Vec d) (r u : ℝ), 0 < r → sourceBall x (2*r) ⊆ sourceBall 0 R →
      y ∈ sourceBall 0 R → 0 < u → u ≤ δ*r^2 → euclideanSq (x-y) ≤ u →
      K (2*u) x x / ρ x ≤ H * (K (4*u) x y / ρ y)) →
    ∀ x ∈ sourceBall 0 (S/2), ∀ y ∈ sourceBall 0 (S/2),
      c ≤ (lam⁻¹)^d * K (T / lam^2) (lam⁻¹ • x) (lam⁻¹ • y) /
          ρ (lam⁻¹ • y) ∧
      c ≤ (lam⁻¹)^d * K (T / lam^2) (lam⁻¹ • y) (lam⁻¹ • x) /
          ρ (lam⁻¹ • x) := by
  obtain ⟨c, hc, hbound⟩ :=
    b_native_capped_fixed_time_lower d hd κ δ H S T hκ hδ hH hS hT
  refine ⟨c, hc, ?_⟩
  intro R lam hR hlam hSR ρ α hell K G hK hmass hcompare x hx y hy
  exact ⟨hbound R lam hR hlam hSR ρ α hell K G hK hmass hcompare x hx y hy,
    hbound R lam hR hlam hSR ρ α hell K G hK hmass hcompare y hy x hx⟩

/-- A prescribed-start half-survival estimate, written using the actual endpoint
Lebesgue density, and the native pointwise comparison imply a full-duration
lower bound. Both endpoint and source orientations use the same constant. -/
theorem b_full_duration_native_lower_of_endpoint_density
    (d : ℕ) (hd : 2 ≤ d) (κ δ H S T : ℝ)
    (hκ : 0 < κ) (hδ : 0 < δ) (hH : 0 < H) (hS : 0 < S) (hT : 0 < T) :
    ∃ c : ℝ, 0 < c ∧ ∀ (R lam : ℝ),
    0 < R → 0 < lam → S = lam * R →
    ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d), IsUniformlyElliptic κ ρ α →
    ∀ (K : ℝ → Vec d → Vec d → ℝ) (G : ℝ → Vec d → Vec d → Vec d),
    IsSpectralDirichletFundamentalSolution ρ α R K G →
    (∀ (x : Vec d) (r u : ℝ), 0 < r → sourceBall x (2*r) ⊆ sourceBall 0 R →
      0 < u → u ≤ δ*r^2 → (1/2 : ℝ) ≤
        ∫ y in sourceBall 0 R, (ρ y / ρ x) * K u y x) →
    (∀ (x y : Vec d) (r u : ℝ), 0 < r → sourceBall x (2*r) ⊆ sourceBall 0 R →
      y ∈ sourceBall 0 R → 0 < u → u ≤ δ*r^2 → euclideanSq (x-y) ≤ u →
      K (2*u) x x / ρ x ≤ H * (K (4*u) x y / ρ y)) →
    ∀ x ∈ sourceBall 0 (S/2), ∀ y ∈ sourceBall 0 (S/2),
      c ≤ (lam⁻¹)^d * K (T / lam^2) (lam⁻¹ • x) (lam⁻¹ • y) /
          ρ (lam⁻¹ • y) ∧
      c ≤ (lam⁻¹)^d * K (T / lam^2) (lam⁻¹ • y) (lam⁻¹ • x) /
          ρ (lam⁻¹ • x) := by
  obtain ⟨c, hc, hbound⟩ :=
    b_native_capped_fixed_time_lower d hd κ δ H S T hκ hδ hH hS hT
  refine ⟨c, hc, ?_⟩
  intro R lam hR hlam hSR ρ α hell K G hK hsurvival hcompare
  have hmass : ∀ (x : Vec d) (r u : ℝ), 0 < r →
      sourceBall x (2*r) ⊆ sourceBall 0 R → 0 < u → u ≤ δ*r^2 →
      (1/2 : ℝ) ≤ ∫ y in sourceBall 0 R, K u x y := by
    intro x r u hr hinside hu hcap
    have hx : x ∈ sourceBall 0 R := hinside (by
      change euclideanNorm (x - x) < 2 * r
      simp only [sub_self]
      have hz : euclideanNorm (0 : Vec d) = 0 := by simp [euclideanNorm, euclideanSq, dot]
      rw [hz]
      linarith)
    have heq : (∫ y in sourceBall 0 R, (ρ y / ρ x) * K u y x) =
        ∫ y in sourceBall 0 R, K u x y := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem (dirichletBall (d := d) R).isOpen.measurableSet] with y hy
      have hsym := b_native_spectral_normalized_transpose hκ hell hK hu hx hy
      have hρy : ρ y ≠ 0 := ne_of_gt (hκ.trans_le (hell.2.2 y).1)
      calc
        (ρ y / ρ x) * K u y x = ρ y * (K u y x / ρ x) := by ring
        _ = ρ y * (K u x y / ρ y) := by rw [hsym]
        _ = K u x y := by field_simp
    rw [← heq]
    exact hsurvival x r u hr hinside hu hcap
  intro x hx y hy
  exact ⟨hbound R lam hR hlam hSR ρ α hell K G hK hmass hcompare x hx y hy,
    hbound R lam hR hlam hSR ρ α hell K G hK hmass hcompare y hy x hx⟩

#print axioms b_full_duration_native_lower
#print axioms b_full_duration_native_lower_of_endpoint_density

end EinsteinFull.Calculus
