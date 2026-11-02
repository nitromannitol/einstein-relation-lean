import EinsteinFull.Calculus.C11TubeWeightedLocalMax
import EllipticRegularity.Parabolic.LocalMax.Cutoff

open EinsteinRelation MeasureTheory Filter EinsteinFull.External.Source.GMP
open PDE hiding Vec Mat
open scoped Topology

namespace EinsteinFull.Calculus

private theorem sourceBall_eq_pde_ball {d : ℕ} (a : Vec d) {R : ℝ} (hR : 0 < R) :
    sourceBall a R = PDE.euclideanBall a R := by
  ext x
  rw [PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt hR]
  rfl

/-- Smooth nested source-ball cutoffs with a uniform Euclidean gradient bound. -/
theorem c5_source_ball_cutoffs (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ r R : ℝ, 0 ≤ r → r < R →
    ∃ χ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ ∧ HasCompactSupport χ ∧
    tsupport χ ⊆ sourceBall 0 R ∧ (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) ∧
    (∀ x ∈ sourceBall (0 : Vec d) r, χ x = 1) ∧
    (∀ x, euclideanSq (fun j => fderiv ℝ χ x (unitVector j)) ≤ C/(R-r)^2) := by
  refine ⟨1024, by norm_num, ?_⟩
  intro r R hr hrR
  let χ := PDE.canonicalBallCutoff (0 : Vec d) r R
  refine ⟨χ, PDE.canonicalBallCutoff_smooth 0 hr hrR,
    PDE.canonicalBallCutoff_hasCompactSupport hr hrR, ?_, ?_, ?_, ?_⟩
  · rw [sourceBall_eq_pde_ball 0 (lt_of_le_of_lt hr hrR)]
    exact PDE.canonicalBallCutoff_tsupport_subset_outer hr hrR
  · intro x
    exact ⟨PDE.canonicalBallCutoff_nonneg 0 r R x, PDE.canonicalBallCutoff_le_one 0 r R x⟩
  · intro x hx
    by_cases hr0 : r = 0
    · subst r
      have hx' : euclideanNorm (x - (0 : Vec d)) < 0 := hx
      exact False.elim ((not_lt_of_ge (Real.sqrt_nonneg _)) hx')
    · have hrp : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
      rw [sourceBall_eq_pde_ball 0 hrp] at hx
      exact PDE.canonicalBallCutoff_eq_one_on_inner hr hrR hx
  · intro x
    have hb := PDE.canonicalBallCutoff_gradient_bound (x₀ := (0 : Vec d)) hr hrR x
    have hs := pow_le_pow_left₀ (PDE.vecEuclideanNorm_nonneg _) hb 2
    rw [PDE.vecEuclideanNorm_sq] at hs
    rw [div_pow] at hs
    norm_num only at hs
    simpa only [PDE.vecNormSq, PDE.vecDot, euclideanSq, dot,
      PDE.classicalGradient_apply, PDE.basisVec, unitVector] using hs

/-- A time-first product of the canonical spatial cutoff and the smooth time ramp. -/
theorem c5_source_cylinder_cutoffs (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ r R T T' : ℝ, 0 ≤ r → r < R → T < T' →
    ∃ η : ℝ × Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) η ∧
      (∀ z, 0 ≤ η z ∧ η z ≤ 1) ∧
      (∃ K : Set (Vec d), IsCompact K ∧ K ⊆ sourceBall 0 R ∧
        ∀ t x, x ∉ K → η (t,x) = 0) ∧
      (∀ t x, t ≤ T + (T' - T) / 2 → η (t,x) = 0) ∧
      (∀ t x, T' ≤ t → x ∈ sourceBall (0 : Vec d) r → η (t,x) = 1) ∧
      (∀ z, |fderiv ℝ η z (1, 0)| ≤ C / (T' - T)) ∧
      (∀ z, euclideanSq (fun j => fderiv ℝ η z (0, unitVector j)) ≤ C / (R-r)^2) := by
  obtain ⟨B, hB0, hB⟩ := PDE.Parabolic.LocalMax.exists_abs_deriv_smoothTransition_le
  refine ⟨1025 + 2 * B, by positivity, ?_⟩
  intro r R T T' hr hrR hTT'
  let η : ℝ × Vec d → ℝ := fun z =>
    PDE.Parabolic.LocalMax.cylCutoff r R T T' (z.2, z.1)
  have h := c11_time_first_cylinder_cutoff (d := d) hr hrR hTT' hB
  refine ⟨η, h.1, h.2.1, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨tsupport (PDE.canonicalBallCutoff (0 : Vec d) r R),
      PDE.canonicalBallCutoff_hasCompactSupport hr hrR, ?_, ?_⟩
    · rw [sourceBall_eq_pde_ball 0 (lt_of_le_of_lt hr hrR)]
      exact PDE.canonicalBallCutoff_tsupport_subset_outer hr hrR
    · intro t x hx
      exact PDE.Parabolic.LocalMax.cylCutoff_eq_zero_of_notMem hx t
  · intro t x ht
    exact PDE.Parabolic.LocalMax.cylCutoff_eq_zero_of_le hTT' x ht
  · intro t x ht hx
    by_cases hr0 : r = 0
    · subst r
      have hx' : euclideanNorm (x - (0 : Vec d)) < 0 := hx
      exact False.elim ((not_lt_of_ge (Real.sqrt_nonneg _)) hx')
    · have hrp : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
      rw [sourceBall_eq_pde_ball 0 hrp] at hx
      exact PDE.Parabolic.LocalMax.cylCutoff_eq_one hr hrR hTT' hx ht
  · intro z
    exact (h.2.2.1 z).trans (div_le_div_of_nonneg_right (by linarith) (by linarith))
  · intro z
    exact (h.2.2.2 z).trans (div_le_div_of_nonneg_right (by linarith) (sq_nonneg _))

end EinsteinFull.Calculus
