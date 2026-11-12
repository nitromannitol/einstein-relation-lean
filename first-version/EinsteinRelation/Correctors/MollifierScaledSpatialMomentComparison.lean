import EinsteinRelation.Correctors.MollifierSpatialMomentComparison

/-! # Scaled spatial domination for normalized source estimates

Source: `paper/main.tex:913–925,942–947`. The same source normalization
controls moments and integrability on any fixed enlargement of its support.
-/

open MeasureTheory
open scoped ENNReal
namespace EinsteinRelation.Correctors
open External.AKM

/-- The reflected mollifier measure is dominated by a dimension and fixed scale
multiple of the normalized Euclidean ball measure.
Source: `paper/main.tex:715–722,942–947`. -/
theorem exists_mollifierCenterMeasure_le_scaled_ball_average (d : ℕ) (κ : ℝ) (hκ : 1 ≤ κ) :
    ∃ D : ℝ, 0 < D ∧ ∀ R : ℝ, 0 < R →
      mollifierCenterMeasure d R ≤
        ENNReal.ofReal D • ((volume (ball (0 : Vec d) (κ * R)))⁻¹ •
          volume.restrict (ball (0 : Vec d) (κ * R))) := by
  have hκ0 : 0 < κ := zero_lt_one.trans_le hκ
  obtain ⟨M, hM⟩ := (hasCompactSupport_mollifier d).exists_bound_of_continuous
    (contDiff_mollifier d).continuous
  let A : ℝ := |M| + 1
  have hA : 0 < A := by dsimp only [A]; positivity
  have hAb (x : Vec d) : mollifier d x ≤ A :=
    (le_abs_self _).trans ((hM x).trans (by
      dsimp only [A]; linarith [le_abs_self M]))
  let V := volume.real (ball (0 : Vec d) 1)
  have hV : 0 < V := paired_ball_volume_pos_finite (d := d) zero_lt_one
  refine ⟨A * κ ^ d * V, by positivity, ?_⟩
  intro R hR
  have hball : MeasurableSet (ball (0 : Vec d) (κ * R)) :=
    (paired_isOpen_ball _ _).measurableSet
  have hvol := ENNReal.toReal_pos_iff.mp
    (paired_ball_volume_pos_finite (d := d) (show 0 < κ * R by positivity))
  have hcoef : ENNReal.ofReal (A * κ ^ d * V) *
      (volume (ball (0 : Vec d) (κ * R)))⁻¹ = ENNReal.ofReal ((R ^ d)⁻¹ * A) := by
    have hinv : (volume (ball (0 : Vec d) (κ * R)))⁻¹ =
        ENNReal.ofReal ((volume.real (ball (0 : Vec d) (κ * R)))⁻¹) := by
      rw [ENNReal.ofReal_inv_of_pos
        (paired_ball_volume_pos_finite (d := d) (show 0 < κ * R by positivity))]
      rw [Measure.real, ENNReal.ofReal_toReal hvol.2.ne]
    rw [hinv, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [paired_ball_volume_real (by positivity : 0 < κ * R), mul_pow]
    dsimp only [V]
    field_simp [hκ0.ne', hR.ne', (show volume.real (ball (0 : Vec d) 1) ≠ 0 from hV.ne')]
  rw [smul_smul, hcoef]
  have hbound : (fun y : Vec d =>
      ENNReal.ofReal (Calculus.unitMassScaledMollifier d R (-y))) ≤
      (ball (0 : Vec d) (κ * R)).indicator
        (fun _ => ENNReal.ofReal ((R ^ d)⁻¹ * A)) := by
    intro y
    by_cases hy : y ∈ ball (0 : Vec d) (κ * R)
    · rw [Set.indicator_of_mem hy]
      exact ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_left (hAb _) (inv_nonneg.mpr (pow_nonneg hR.le _)))
    · rw [Set.indicator_of_notMem hy]
      have hz : Calculus.unitMassScaledMollifier d R (-y) = 0 := by
        by_contra hn
        have hh := Entropy.euclideanNorm_lt_of_unitMassScaledMollifier_ne_zero hR hn
        have hy' : euclideanNorm y < κ * R := by
          rw [Entropy.euclideanNorm_neg'] at hh
          exact hh.trans_le (le_mul_of_one_le_left hR.le hκ)
        exact hy (by simpa only [ball, Set.mem_setOf_eq, sub_zero] using hy')
      simp only [hz, ENNReal.ofReal_zero, le_refl]
  exact (withDensity_mono (ae_of_all _ hbound)).trans_eq
    (by rw [withDensity_indicator hball, withDensity_const])


end EinsteinRelation.Correctors
