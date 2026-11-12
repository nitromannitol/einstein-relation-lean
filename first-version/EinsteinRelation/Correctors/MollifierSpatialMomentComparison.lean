import EinsteinRelation.Correctors.ConditionalSpatialMollifierMoment
import EinsteinRelation.Correctors.PairedPDEBallNormalization

/-! # Comparing mollifier moments with centered ball moments

Source: `paper/main.tex:715–722,942–947`. The comparison constant depends
only on the dimension and the fixed mollifier, uniformly in the radius.
-/

open MeasureTheory
open scoped ENNReal

namespace EinsteinRelation.Correctors
open External.AKM

/-- The reflected mollifier measure is dominated by a dimension-only
multiple of the normalized Euclidean ball measure.
Source: `paper/main.tex:715–722,942–947`. -/
theorem exists_mollifierCenterMeasure_le_ball_average (d : ℕ) :
    ∃ D : ℝ, 0 < D ∧ ∀ R : ℝ, 0 < R →
      mollifierCenterMeasure d R ≤
        ENNReal.ofReal D • ((volume (ball (0 : Vec d) (2 * R)))⁻¹ •
          volume.restrict (ball (0 : Vec d) (2 * R))) := by
  obtain ⟨M, hM⟩ := (hasCompactSupport_mollifier d).exists_bound_of_continuous
    (contDiff_mollifier d).continuous
  let A : ℝ := |M| + 1
  have hA : 0 < A := by dsimp only [A]; positivity
  have hAb (x : Vec d) : mollifier d x ≤ A :=
    (le_abs_self _).trans ((hM x).trans (by
      dsimp only [A]; linarith [le_abs_self M]))
  let V := volume.real (ball (0 : Vec d) 1)
  have hV : 0 < V := paired_ball_volume_pos_finite (d := d) zero_lt_one
  refine ⟨A * 2 ^ d * V, by positivity, ?_⟩
  intro R hR
  have hball : MeasurableSet (ball (0 : Vec d) (2 * R)) :=
    (paired_isOpen_ball _ _).measurableSet
  have hvol := ENNReal.toReal_pos_iff.mp
    (paired_ball_volume_pos_finite (d := d) (show 0 < 2 * R by positivity))
  have hcoef : ENNReal.ofReal (A * 2 ^ d * V) *
      (volume (ball (0 : Vec d) (2 * R)))⁻¹ = ENNReal.ofReal ((R ^ d)⁻¹ * A) := by
    have hinv : (volume (ball (0 : Vec d) (2 * R)))⁻¹ =
        ENNReal.ofReal ((volume.real (ball (0 : Vec d) (2 * R)))⁻¹) := by
      rw [ENNReal.ofReal_inv_of_pos
        (paired_ball_volume_pos_finite (d := d) (show 0 < 2 * R by positivity))]
      rw [Measure.real, ENNReal.ofReal_toReal hvol.2.ne]
    rw [hinv, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [paired_ball_volume_real (by positivity : 0 < 2 * R), mul_pow]
    dsimp only [V]
    field_simp [hR.ne', (show volume.real (ball (0 : Vec d) 1) ≠ 0 from hV.ne')]
  rw [smul_smul, hcoef]
  have hbound : (fun y : Vec d =>
      ENNReal.ofReal (Calculus.unitMassScaledMollifier d R (-y))) ≤
      (ball (0 : Vec d) (2 * R)).indicator
        (fun _ => ENNReal.ofReal ((R ^ d)⁻¹ * A)) := by
    intro y
    by_cases hy : y ∈ ball (0 : Vec d) (2 * R)
    · rw [Set.indicator_of_mem hy]
      exact ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_left (hAb _) (inv_nonneg.mpr (pow_nonneg hR.le _)))
    · rw [Set.indicator_of_notMem hy]
      have hz : Calculus.unitMassScaledMollifier d R (-y) = 0 := by
        by_contra hn
        have hh := Entropy.euclideanNorm_lt_of_unitMassScaledMollifier_ne_zero hR hn
        have hy' : euclideanNorm y < 2 * R := by
          rw [Entropy.euclideanNorm_neg'] at hh
          linarith only [hh, hR]
        exact hy (by simpa only [ball, Set.mem_setOf_eq, sub_zero] using hy')
      simp only [hz, ENNReal.ofReal_zero, le_refl]
  exact (withDensity_mono (ae_of_all _ hbound)).trans_eq
    (by rw [withDensity_indicator hball, withDensity_const])

/-- A mollifier-weighted moment of the reflected source is controlled by
the source's ordinary ball average, with one constant for every radius.
Source: `paper/main.tex:715–722,942–947`. -/
theorem exists_lintegral_mollifierCenterMeasure_le_ball_average (d : ℕ) :
    ∃ D : ℝ, 0 < D ∧ ∀ R : ℝ, 0 < R → ∀ F : Vec d → ℝ≥0∞,
      (∫⁻ y, F (-y) ∂mollifierCenterMeasure d R) ≤
        ENNReal.ofReal D * (⨍⁻ x in ball (0 : Vec d) (2 * R), F x ∂volume) := by
  obtain ⟨D, hD, hbound⟩ := exists_mollifierCenterMeasure_le_ball_average d
  refine ⟨D, hD, ?_⟩
  intro R hR F
  let B := ball (0 : Vec d) (2 * R)
  have hpre : (fun x : Vec d => -x) ⁻¹' B = B := by
    ext x
    simp only [B, ball, Set.mem_preimage, Set.mem_setOf_eq, sub_zero,
      Entropy.euclideanNorm_neg']
  have hneg : MeasurePreserving (fun x : Vec d => -x)
      (volume.restrict B) (volume.restrict B) := by
    have h := (Measure.measurePreserving_neg (volume : Measure (Vec d))).restrict_preimage_emb
      (MeasurableEquiv.neg (Vec d)).measurableEmbedding B
    simpa only [hpre] using h
  have h := lintegral_mono' (hbound R hR) (le_refl (fun y : Vec d => F (-y)))
  simp only [lintegral_smul_measure, smul_eq_mul] at h
  have heq := hneg.lintegral_comp_emb (MeasurableEquiv.neg (Vec d)).measurableEmbedding F
  change (∫⁻ y in B, F (-y) ∂volume) = ∫⁻ y in B, F y ∂volume at heq
  rw [show (∫⁻ y in ball (0 : Vec d) (2 * R), F (-y) ∂volume) =
      ∫⁻ y in ball (0 : Vec d) (2 * R), F y ∂volume from heq] at h
  simpa only [laverage_eq, Measure.restrict_apply_univ, div_eq_mul_inv, mul_comm] using h

end EinsteinRelation.Correctors
