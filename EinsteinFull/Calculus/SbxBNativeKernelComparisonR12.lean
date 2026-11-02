import EinsteinFull.Calculus.C9TubeNativeHarnackComparison

open EinsteinRelation MeasureTheory EinsteinFull.External.Source.GMP
open PDE hiding Vec Mat
open scoped Topology

namespace EinsteinFull.Calculus

/-- Pointwise parabolic Harnack on two separated subcylinders, with the
constant fixed before the coefficients, cylinder, and solution. -/
def BScaledCylinderPointwiseHarnack (d : ℕ) (κ : ℝ) : Prop :=
  ∃ H : ℝ, 0 < H ∧ ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
    IsUniformlyElliptic κ ρ α → ∀ (t₀ r : ℝ) (x : Vec d), 0 < r →
    ∀ (v : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d),
    IsWeightedCaloric ρ α (Set.Ioo (t₀-r^2) (t₀+r^2)) (sourceBall x r) v G →
    ContinuousOn v (Set.Ioo (t₀-r^2) (t₀+r^2) ×ˢ sourceBall x r) →
    (∀ p ∈ Set.Ioo (t₀-r^2) (t₀+r^2) ×ˢ sourceBall x r, 0 ≤ v p) →
    ∀ p ∈ Set.Ioo (t₀-3*r^2/4) (t₀-r^2/4) ×ˢ sourceBall x (3*r/4),
    ∀ q ∈ Set.Ioo (t₀+r^2/4) (t₀+3*r^2/4) ×ˢ sourceBall x (3*r/4),
      v p ≤ H * v q

/-- The native spectral kernel satisfies the exact comparison required by the
capped fixed-time lower bound, conditional on pointwise cylinder Harnack. -/
theorem b_native_kernel_comparison_of_scaled_harnack
    (d : ℕ) (κ : ℝ) (hκ : 0 < κ) (hh : BScaledCylinderPointwiseHarnack d κ) :
    ∃ δ H : ℝ, 0 < δ ∧ 0 < H ∧ ∀ (R : ℝ), 0 < R →
    ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d), IsUniformlyElliptic κ ρ α →
    ∀ (K : ℝ → Vec d → Vec d → ℝ) (G : ℝ → Vec d → Vec d → Vec d),
    IsSpectralDirichletFundamentalSolution ρ α R K G →
    ∀ (x y : Vec d) (r u : ℝ), 0 < r → sourceBall x (2*r) ⊆ sourceBall 0 R →
      y ∈ sourceBall 0 R → 0 < u → u ≤ δ*r^2 → euclideanSq (x-y) ≤ u →
      K (2*u) x x / ρ x ≤ H * (K (4*u) x y / ρ y) := by
  obtain ⟨H, hH, hh⟩ := hh
  refine ⟨1, H, by norm_num, hH, ?_⟩
  intro R hR ρ α hell K G hK x y r u hr hball hy hu hcap hdist
  let a : ℝ := Real.sqrt (2*u)
  have ha : 0 < a := Real.sqrt_pos.2 (by positivity)
  have ha2 : a^2 = 2*u := Real.sq_sqrt (by positivity)
  have har : a ≤ 2*r := by nlinarith [sq_nonneg (a + 2*r)]
  have hlocal : sourceBall x a ⊆ sourceBall (0 : Vec d) R := by
    intro z hz
    apply hball
    change euclideanNorm (z-x) < 2*r
    change euclideanNorm (z-x) < a at hz
    linarith
  have hx : x ∈ sourceBall (0 : Vec d) R := hlocal (by
    change euclideanNorm (x-x) < a
    simpa [euclideanNorm, euclideanSq, dot] using ha)
  let v : ℝ × Vec d → ℝ := fun p => K p.1 p.2 x
  let F : ℝ × Vec d → Vec d := fun p => G p.1 p.2 x
  have hc : IsWeightedCaloric ρ α (Set.Ioo (3*u-a^2) (3*u+a^2))
      (sourceBall x a) v F := by
    apply c9_weighted_caloric_spatial_mono measurableSet_Ioo
      (c17_isOpen_sourceBall (0 : Vec d) R).measurableSet hlocal
    exact (hK.1 x hx).2.2.2.1 _ _ (by rw [ha2]; linarith) (by rw [ha2]; linarith) |>.1
  have hcont : ContinuousOn v (Set.Ioo (3*u-a^2) (3*u+a^2) ×ˢ sourceBall x a) := by
    apply (hK.1 x hx).1.mono
    intro p hp
    refine ⟨?_, subset_closure (hlocal hp.2)⟩
    change 0 < p.1
    rw [ha2] at hp
    linarith [hp.1.1]
  have hnonneg : ∀ p ∈ Set.Ioo (3*u-a^2) (3*u+a^2) ×ˢ sourceBall x a, 0 ≤ v p := by
    intro p hp
    apply (hK.1 x hx).2.1 p.1 _ p.2 (hlocal hp.2)
    rw [ha2] at hp
    linarith [hp.1.1]
  have hp : (2*u,x) ∈ Set.Ioo (3*u-3*a^2/4) (3*u-a^2/4) ×ˢ sourceBall x (3*a/4) := by
    constructor
    · rw [ha2]; constructor <;> linarith
    · change euclideanNorm (x-x) < 3*a/4
      simpa [euclideanNorm, euclideanSq, dot] using (show 0 < 3*a/4 by positivity)
  have hdist' : euclideanNorm (y-x)^2 ≤ u := by
    rw [show y-x = -(x-y) by abel, Entropy.euclideanNorm_neg', ← TimeChange.euclideanSq_eq_sq_euclideanNorm]
    exact hdist
  have hnorm : 0 ≤ euclideanNorm (y-x) := by unfold euclideanNorm; positivity
  have hq : (4*u,y) ∈ Set.Ioo (3*u+a^2/4) (3*u+3*a^2/4) ×ˢ sourceBall x (3*a/4) := by
    constructor
    · rw [ha2]; constructor <;> linarith
    · change euclideanNorm (y-x) < 3*a/4
      nlinarith [sq_nonneg (euclideanNorm (y-x) + 3*a/4)]
  have h := hh ρ α hell (3*u) a x ha v F hc hcont hnonneg (2*u,x) hp (4*u,y) hq
  have hρx : 0 < ρ x := hκ.trans_le (hell.2.2 x).1
  have hρy : 0 < ρ y := hκ.trans_le (hell.2.2 y).1
  have hsym := hK.weighted_symmetry (show 0 < 4*u by positivity) hx hy
  dsimp only [v] at h
  have heq : K (4*u) y x / ρ x = K (4*u) x y / ρ y := by
    apply (div_eq_div_iff (ne_of_gt hρx) (ne_of_gt hρy)).2
    nlinarith [hsym]
  have hdiv := div_le_div_of_nonneg_right h hρx.le
  rw [mul_div_assoc, heq] at hdiv
  exact hdiv

#print axioms b_native_kernel_comparison_of_scaled_harnack

end EinsteinFull.Calculus
