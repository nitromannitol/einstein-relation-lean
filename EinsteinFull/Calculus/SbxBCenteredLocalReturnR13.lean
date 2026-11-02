import EinsteinFull.Calculus.SbxBCenteredSurvivalR12
import EinsteinFull.Calculus.SbxBPhysicalClippedCoefficientsR13

open MeasureTheory
open EinsteinRelation EinsteinRelation.SpatialDirichlet
open EinsteinRelation.External.GantertSection7Support
open EinsteinFull.Blueprint.TubeProbability EinsteinFull.External.Source.GMP

namespace EinsteinFull

/-- The remaining native spectral existence statement, independent of the
physical environment and radius. -/
@[nolint defsWithUnderscore]
def b_centered_global_spectral_existence : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ (κ : ℝ), 0 < κ →
    ∀ (R : ℝ), 0 < R → ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
      IsUniformlyElliptic κ ρ α →
      ∃ (K : ℝ → Vec d → Vec d → ℝ) (G : ℝ → Vec d → Vec d → Vec d),
        IsSpectralDirichletFundamentalSolution ρ α R K G

/-- The remaining prescribed-start native half-survival statement. -/
@[nolint defsWithUnderscore]
def b_centered_global_half_survival : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ (κ : ℝ), 0 < κ →
    ∃ δ : ℝ, 0 < δ ∧ ∀ (R : ℝ), 0 < R →
      ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d), IsUniformlyElliptic κ ρ α →
      ∀ (K : ℝ → Vec d → Vec d → ℝ) (G : ℝ → Vec d → Vec d → Vec d),
        IsSpectralDirichletFundamentalSolution ρ α R K G →
      ∀ (x : Vec d) (r u : ℝ), 0 < r →
        sourceBall x (2*r) ⊆ sourceBall 0 R → 0 < u → u ≤ δ*r^2 →
        (1/2 : ℝ) ≤ ∫ y in sourceBall 0 R, K u x y

/-- The remaining native pointwise comparison, for the prescribed points. -/
@[nolint defsWithUnderscore]
def b_centered_global_native_comparison : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ (κ : ℝ), 0 < κ →
    ∃ δ H : ℝ, 0 < δ ∧ 0 < H ∧ ∀ (R : ℝ), 0 < R →
      ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d), IsUniformlyElliptic κ ρ α →
      ∀ (K : ℝ → Vec d → Vec d → ℝ) (G : ℝ → Vec d → Vec d → Vec d),
        IsSpectralDirichletFundamentalSolution ρ α R K G →
      ∀ (x y : Vec d) (r u : ℝ), 0 < r →
        sourceBall x (2*r) ⊆ sourceBall 0 R → y ∈ sourceBall 0 R →
        0 < u → u ≤ δ*r^2 → euclideanSq (x-y) ≤ u →
        K (2*u) x x / ρ x ≤ H * (K (4*u) x y / ρ y)

/-- Spectral existence for continuous densities; the clipped physical density
has this regularity even though the ellipticity predicate alone does not. -/
@[nolint defsWithUnderscore]
def b_centered_continuous_spectral_existence : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ (κ : ℝ), 0 < κ →
    ∀ (R : ℝ), 0 < R → ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
      IsUniformlyElliptic κ ρ α → Continuous ρ →
      ∃ (K : ℝ → Vec d → Vec d → ℝ) (G : ℝ → Vec d → Vec d → Vec d),
        IsSpectralDirichletFundamentalSolution ρ α R K G

/-- The centered return uses spectral existence only for continuous densities. -/
theorem b_centered_local_return_of_continuous_native_primitives
    (hspectral : b_centered_continuous_spectral_existence)
    (hsurvival : b_centered_global_half_survival)
    (hcomparison : b_centered_global_native_comparison) :
    b_centered_local_return_input := by
  apply b_centered_local_return_input_of_native_inputs
  intro d hd L l hl
  let M := max 1 (sourceReducedBound L)
  have hLpos : 0 < sourceReducedBound L := by
    unfold sourceReducedBound
    apply mul_pos (Real.exp_pos _)
    nlinarith [sq_nonneg (L + 1/6)]
  have hLM : sourceReducedBound L ≤ M := le_max_right _ _
  let κ := bPhysicalClippedKappa M (l/2)
  have hκ : 0 < κ := b_physical_clipped_kappa_pos (le_max_left _ _)
  obtain ⟨δ₁, hδ₁, hmass⟩ := hsurvival d hd κ hκ
  obtain ⟨δ₂, H, hδ₂, hH, hcomp⟩ := hcomparison d hd κ hκ
  refine ⟨κ, min δ₁ δ₂, H, hκ, lt_min hδ₁ hδ₂, hH, ?_, ?_, ?_⟩
  · intro ω hω μ hμ hμ1
    have hωM : IsRegular M ω := by
      rcases hω with ⟨hell, hpot, hlip, hpotlip⟩
      refine ⟨?_, fun x => (hpot x).trans hLM, ?_, ?_⟩
      · intro x
        refine ⟨(hell x).1, fun v => ⟨?_, ?_⟩⟩
        · exact (mul_le_mul_of_nonneg_right (inv_anti₀ hLpos hLM)
            (euclideanSq_nonneg_coords v)).trans ((hell x).2 v).1
        · exact ((hell x).2 v).2.trans (mul_le_mul_of_nonneg_right hLM
            (euclideanSq_nonneg_coords v))
      · intro x y v
        exact (hlip x y v).trans (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hLM (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _))
      · intro x y
        exact (hpotlip x y).trans (mul_le_mul_of_nonneg_right hLM (Real.sqrt_nonneg _))
    let ρ := bPhysicalClippedRho hd ω (l/2) μ
    let α := bPhysicalClippedAlpha hd ω (l/2) μ
    have hell : IsUniformlyElliptic κ ρ α :=
      b_physical_clipped_elliptic (le_max_left _ _) (by positivity) hd ω hωM μ
    have hρ : Continuous ρ := b_physical_clipped_rho_continuous hd ω (l/2) μ
    obtain ⟨K, G, hK⟩ := hspectral d hd κ hκ ((l/2)/μ) (by positivity) ρ α hell hρ
    exact ⟨ρ, α, K, G, hell,
      fun x hx => b_physical_clipped_eq_on_ball hμ hd ω x hx, hK⟩
  · intro ω μ hμ hμ1 ρ α K G hell hcoeff hK x r u hr hball hu hut
    exact hmass ((l/2)/μ) (by positivity) ρ α hell K G hK x r u hr hball hu
      (hut.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) (sq_nonneg r)))
  · intro ω μ hμ hμ1 ρ α K G hell hcoeff hK x y r u hr hball hy hu hut hxy
    exact hcomp ((l/2)/μ) (by positivity) ρ α hell K G hK x y r u hr hball hy hu
      (hut.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) (sq_nonneg r))) hxy


/-- Uniform clipped physical coefficients and the three displayed global native
primitives give the original centered local-return input for every radius. -/
theorem b_centered_local_return_of_global_native_primitives
    (hspectral : b_centered_global_spectral_existence)
    (hsurvival : b_centered_global_half_survival)
    (hcomparison : b_centered_global_native_comparison) :
    b_centered_local_return_input := by
  apply b_centered_local_return_input_of_native_inputs
  intro d hd L l hl
  let M := max 1 (sourceReducedBound L)
  have hLpos : 0 < sourceReducedBound L := by
    unfold sourceReducedBound
    apply mul_pos (Real.exp_pos _)
    nlinarith [sq_nonneg (L + 1/6)]
  have hLM : sourceReducedBound L ≤ M := le_max_right _ _
  obtain ⟨κ, hκ, hext⟩ := b_physical_clipped_extension hd M (l/2)
    (le_max_left _ _) (by positivity)
  obtain ⟨δ₁, hδ₁, hmass⟩ := hsurvival d hd κ hκ
  obtain ⟨δ₂, H, hδ₂, hH, hcomp⟩ := hcomparison d hd κ hκ
  refine ⟨κ, min δ₁ δ₂, H, hκ, lt_min hδ₁ hδ₂, hH, ?_, ?_, ?_⟩
  · intro ω hω μ hμ hμ1
    have hωM : IsRegular M ω := by
      rcases hω with ⟨hell, hpot, hlip, hpotlip⟩
      refine ⟨?_, fun x => (hpot x).trans hLM, ?_, ?_⟩
      · intro x
        refine ⟨(hell x).1, fun v => ⟨?_, ?_⟩⟩
        · exact (mul_le_mul_of_nonneg_right (inv_anti₀ hLpos hLM)
            (euclideanSq_nonneg_coords v)).trans ((hell x).2 v).1
        · exact ((hell x).2 v).2.trans (mul_le_mul_of_nonneg_right hLM
            (euclideanSq_nonneg_coords v))
      · intro x y v
        exact (hlip x y v).trans (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hLM (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _))
      · intro x y
        exact (hpotlip x y).trans (mul_le_mul_of_nonneg_right hLM (Real.sqrt_nonneg _))
    obtain ⟨ρ, α, hell, hcoeff⟩ := hext ω hωM μ hμ hμ1
    obtain ⟨K, G, hK⟩ := hspectral d hd κ hκ ((l/2)/μ) (by positivity) ρ α hell
    exact ⟨ρ, α, K, G, hell, hcoeff, hK⟩
  · intro ω μ hμ hμ1 ρ α K G hell hcoeff hK x r u hr hball hu hut
    exact hmass ((l/2)/μ) (by positivity) ρ α hell K G hK x r u hr hball hu
      (hut.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) (sq_nonneg r)))
  · intro ω μ hμ hμ1 ρ α K G hell hcoeff hK x y r u hr hball hy hu hut hxy
    exact hcomp ((l/2)/μ) (by positivity) ρ α hell K G hK x y r u hr hball hy hu
      (hut.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) (sq_nonneg r))) hxy

#print axioms b_centered_local_return_of_continuous_native_primitives
#print axioms b_centered_local_return_of_global_native_primitives
end EinsteinFull
