import EinsteinFull.Calculus.C18TubeUniformDiagonalScale

open EinsteinRelation MeasureTheory EinsteinFull.External.Source.GMP
open PDE hiding Vec Mat
open EinsteinFull.Blueprint.TubeProbability
open EinsteinFull.Blueprint.SbxS3UniformCrossHeat

noncomputable section
namespace EinsteinFull.Calculus

/-- Uniform near-diagonal control of the actual normalized spectral kernel,
from interior survival and a supplied pointwise row comparison. -/
theorem c18_native_uniform_near_diagonal_of_mass_comparison
    (d : ℕ) (hd : 2 ≤ d) (κ δ H : ℝ) (hκ : 0 < κ) (hδ : 0 < δ) (hH : 0 < H) :
    ∃ c η : ℝ, 0 < c ∧ 0 < η ∧ ∀ R : ℝ, 0 < R →
    ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d), IsUniformlyElliptic κ ρ α →
    ∀ (K : ℝ → Vec d → Vec d → ℝ) (G : ℝ → Vec d → Vec d → Vec d),
    IsSpectralDirichletFundamentalSolution ρ α R K G →
    (∀ (x : Vec d) (r t : ℝ), 0 < r → sourceBall x (2*r) ⊆ sourceBall 0 R →
      0 < t → t ≤ δ*r^2 → (1/2 : ℝ) ≤ ∫ y in sourceBall 0 R, K t x y) →
    (∀ (x y : Vec d) (r t : ℝ), 0 < r → sourceBall x (2*r) ⊆ sourceBall 0 R →
      y ∈ sourceBall 0 R → 0 < t → t ≤ δ*r^2 → euclideanSq (x-y) ≤ t →
      K (2*t) x x / ρ x ≤ H * (K (4*t) x y / ρ y)) →
    ∀ (x y : Vec d) (r t : ℝ), 0 < r → sourceBall x (2*r) ⊆ sourceBall 0 R →
    y ∈ sourceBall 0 R → 0 < t → t ≤ η*r^2 → euclideanSq (x-y) ≤ t →
    c * Real.rpow (4*t) (-(d : ℝ)/2) ≤ K (4*t) x y / ρ y := by
  obtain ⟨a, ε, ha, hε, hdiag⟩ := c18_native_uniform_diagonal_of_mass_moment d hd κ δ hκ hδ
  refine ⟨a / H, min ε δ, div_pos ha hH, lt_min hε hδ, ?_⟩
  intro R hR ρ α hell K G hK hmass hcompare x y r t hr hinside hy ht htime hdist
  have htε : t ≤ ε*r^2 := htime.trans
    (mul_le_mul_of_nonneg_right (min_le_left _ _) (sq_nonneg r))
  have htδ : t ≤ δ*r^2 := htime.trans
    (mul_le_mul_of_nonneg_right (min_le_right _ _) (sq_nonneg r))
  have hpower : Real.rpow (4*t) (-(d : ℝ)/2) ≤ Real.rpow t (-(d : ℝ)/2) :=
    Real.rpow_le_rpow_of_nonpos ht (by linarith)
      (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg d)) (by norm_num))
  have hbound := (mul_le_mul_of_nonneg_left hpower ha.le).trans
    ((hdiag R hR ρ α hell K G hK hmass x r t hr hinside ht htε).trans
      (hcompare x y r t hr hinside hy ht htδ hdist))
  have hdiv : (a * Real.rpow (4*t) (-(d : ℝ)/2)) / H ≤ K (4*t) x y / ρ y :=
    (div_le_iff₀ hH).2 (by simpa only [mul_comm] using hbound)
  simpa only [div_mul_eq_mul_div] using hdiv

/-- The same actual-kernel estimate at time `s`, in the time variable used by
near-diagonal chaining. The spatial condition retains its factor `1/4`. -/
theorem c18_native_uniform_near_diagonal_rescaled_of_mass_comparison
    (d : ℕ) (hd : 2 ≤ d) (κ δ H : ℝ) (hκ : 0 < κ) (hδ : 0 < δ) (hH : 0 < H) :
    ∃ c η : ℝ, 0 < c ∧ 0 < η ∧ ∀ R : ℝ, 0 < R →
    ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d), IsUniformlyElliptic κ ρ α →
    ∀ (K : ℝ → Vec d → Vec d → ℝ) (G : ℝ → Vec d → Vec d → Vec d),
    IsSpectralDirichletFundamentalSolution ρ α R K G →
    (∀ (x : Vec d) (r t : ℝ), 0 < r → sourceBall x (2*r) ⊆ sourceBall 0 R →
      0 < t → t ≤ δ*r^2 → (1/2 : ℝ) ≤ ∫ y in sourceBall 0 R, K t x y) →
    (∀ (x y : Vec d) (r t : ℝ), 0 < r → sourceBall x (2*r) ⊆ sourceBall 0 R →
      y ∈ sourceBall 0 R → 0 < t → t ≤ δ*r^2 → euclideanSq (x-y) ≤ t →
      K (2*t) x x / ρ x ≤ H * (K (4*t) x y / ρ y)) →
    ∀ (x y : Vec d) (r s : ℝ), 0 < r → sourceBall x (2*r) ⊆ sourceBall 0 R →
    y ∈ sourceBall 0 R → 0 < s → s ≤ η*r^2 → euclideanSq (x-y) ≤ s/4 →
    c * Real.rpow s (-(d : ℝ)/2) ≤ K s x y / ρ y := by
  obtain ⟨c, η, hc, hη, hnear⟩ :=
    c18_native_uniform_near_diagonal_of_mass_comparison d hd κ δ H hκ hδ hH
  refine ⟨c, 4*η, hc, by positivity, ?_⟩
  intro R hR ρ α hell K G hK hmass hcompare x y r s hr hinside hy hs htime hdist
  have htime' : s/4 ≤ η*r^2 := by nlinarith
  have hresult := hnear R hR ρ α hell K G hK hmass hcompare x y r (s/4)
    hr hinside hy (by positivity) htime' hdist
  simpa only [mul_div_cancel₀ _ (by norm_num : (4 : ℝ) ≠ 0)] using hresult

/-- The rescaled near-diagonal estimate at the fixed local radius `R/8`.
The survival and row-comparison inputs remain explicit for the same kernel. -/
theorem c18_native_uniform_near_diagonal_radius_eighth_of_mass_comparison
    (d : ℕ) (hd : 2 ≤ d) (κ δ H : ℝ) (hκ : 0 < κ) (hδ : 0 < δ) (hH : 0 < H) :
    ∃ c η : ℝ, 0 < c ∧ 0 < η ∧ ∀ R : ℝ, 0 < R →
    ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d), IsUniformlyElliptic κ ρ α →
    ∀ (K : ℝ → Vec d → Vec d → ℝ) (G : ℝ → Vec d → Vec d → Vec d),
    IsSpectralDirichletFundamentalSolution ρ α R K G →
    (∀ (x : Vec d) (r t : ℝ), 0 < r → sourceBall x (2*r) ⊆ sourceBall 0 R →
      0 < t → t ≤ δ*r^2 → (1/2 : ℝ) ≤ ∫ y in sourceBall 0 R, K t x y) →
    (∀ (x y : Vec d) (r t : ℝ), 0 < r → sourceBall x (2*r) ⊆ sourceBall 0 R →
      y ∈ sourceBall 0 R → 0 < t → t ≤ δ*r^2 → euclideanSq (x-y) ≤ t →
      K (2*t) x x / ρ x ≤ H * (K (4*t) x y / ρ y)) →
    ∀ (x y : Vec d) (s : ℝ), sourceBall x (2*(R/8)) ⊆ sourceBall 0 R →
    y ∈ sourceBall 0 R → 0 < s → s ≤ η*(R/8)^2 → euclideanSq (x-y) ≤ s/4 →
    c * Real.rpow s (-(d : ℝ)/2) ≤ K s x y / ρ y := by
  obtain ⟨c, η, hc, hη, hnear⟩ :=
    c18_native_uniform_near_diagonal_rescaled_of_mass_comparison d hd κ δ H hκ hδ hH
  refine ⟨c, η, hc, hη, ?_⟩
  intro R hR ρ α hell K G hK hmass hcompare x y s hinside hy hs htime hdist
  exact hnear R hR ρ α hell K G hK hmass hcompare x y (R/8) s
    (by positivity) hinside hy hs htime hdist

end EinsteinFull.Calculus
