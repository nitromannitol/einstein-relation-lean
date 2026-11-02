import EinsteinFull.Calculus.SbxBNegativeNestedGainAdapterR11
import EinsteinFull.Calculus.SbxBBackwardGainScalingR12
import EinsteinFull.Calculus.C8TubeWeightedWeakHarnack

open EinsteinRelation EinsteinFull.External.Source.GMP MeasureTheory Filter
open scoped ENNReal

namespace EinsteinFull.Calculus

/-- The scaled backward gain applies to the shifted, positive regularization on
any backward piece whose translation lies in the original caloric cylinder. -/
theorem b_translated_backward_gain_raw (d : ℕ) (hd : 2 ≤ d)
    (κ : ℝ) (hκ : 0 < κ) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
    IsUniformlyElliptic κ ρ α →
    ∀ (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d),
    IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1) u G →
    (∀ᵐ z ∂volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1), 0 ≤ u z) →
    ∀ (ε p : ℝ), 0 < ε → 0 < p → ∀ (x : ℝ × Vec d) (r : ℝ), 0 < r →
    (∀ z ∈ sbxBBackPiece x r,
      (z.1 + 3 / 4, z.2) ∈ Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall (0 : Vec d) 1) →
    eLpNorm (fun z => 1 / max ε (u (z.1 + 3 / 4, z.2) + ε))
      (ENNReal.ofReal ((((d : ℝ) + 2) / d) * p))
      (volume.restrict (sbxBBackHalfPiece x r)) ≤
    ((C * ENNReal.ofReal ((1+p)^2)) ^ (1/p) * ENNReal.ofReal (Real.rpow r (-(2/p)))) *
      eLpNorm (fun z => 1 / max ε (u (z.1 + 3 / 4, z.2) + ε))
        (ENNReal.ofReal p) (volume.restrict (sbxBBackPiece x r)) := by
  obtain ⟨C, hC, hgain⟩ := b_backward_negative_power_gain_scaled d hd κ hκ
  refine ⟨C, hC, ?_⟩
  intro ρ α hell u G hcal hu ε p hε hp x r hr hS
  let t := min 0 (x.1 + r ^ 2 / 8)
  have hcenter : x.2 ∈ sourceBall x.2 r := by
    change euclideanNorm (x.2 - x.2) < r
    simpa [euclideanNorm, euclideanSq, dot] using hr
  have htime : Set.Ioo (t-r^2) t ⊆ Set.Ioo (-1 - 3/4 : ℝ) (1 - 3/4) := by
    intro s hs
    have h := hS (s, x.2) (show (s, x.2) ∈ sbxBBackPiece x r from
      ⟨⟨hs.1, le_of_lt hs.2⟩, hcenter⟩)
    constructor <;> linarith [h.1.1, h.1.2]
  have hspace : sourceBall x.2 r ⊆ sourceBall (0 : Vec d) 1 := by
    intro y hy
    have hrsq : 0 < r^2 := sq_pos_of_pos hr
    have h := hS (t-r^2/2, y) (show (t-r^2/2, y) ∈ sbxBBackPiece x r from
      ⟨⟨by dsimp [t]; linarith, by dsimp [t]; linarith⟩, hy⟩)
    exact h.2
  obtain ⟨hshift, hpos⟩ := c8_weighted_caloric_positive_shift hκ hell hcal hu hε
  have htcal := c13_weighted_caloric_time_translation (3/4) (-1) 1
    (sourceBall 0 1) ρ α (fun z => u z + ε) G hshift
  have hlocal := c11_weighted_caloric_cylinder_mono measurableSet_Ioo measurableSet_Ioo
    (c17_isOpen_sourceBall (0 : Vec d) 1).measurableSet htime hspace htcal
  have hm := c13_time_translation_measurePreserving (d := d) (3/4) (-1) 1 (sourceBall 0 1)
  have hpos' := hm.quasiMeasurePreserving.ae hpos
  have hpos'' := ae_restrict_of_ae_restrict_of_subset (Set.prod_mono htime hspace) hpos'
  have hh := hgain t x.2 r hr ρ α hell _ _ hlocal ε p hε hp hpos''
  have hclip : (fun z : ℝ × Vec d => 1 / max ε (u (z.1 + 3/4,z.2) + ε)) =ᵐ[
      volume.restrict (Set.Ioo (t-r^2) t ×ˢ sourceBall x.2 r)]
      (fun z => (u (z.1 + 3/4,z.2) + ε)⁻¹) := by
    filter_upwards [hpos''] with z hz
    rw [max_eq_right hz, one_div]
  have hsub : Set.Ioo (t-r^2/4) t ×ˢ sourceBall x.2 (r/2) ⊆
      Set.Ioo (t-r^2) t ×ˢ sourceBall x.2 r := by
    intro z hz
    refine ⟨⟨?_, hz.1.2⟩, ?_⟩
    · nlinarith [hz.1.1, sq_nonneg r]
    · change euclideanNorm (z.2-x.2) < r
      have hs := hz.2
      change euclideanNorm (z.2-x.2) < r/2 at hs
      linarith
  have hcliphalf := hclip.filter_mono (ae_mono (Measure.restrict_mono_set volume hsub))
  rw [← eLpNorm_congr_ae hcliphalf, ← eLpNorm_congr_ae hclip] at hh
  simpa only [sbxBBackPiece, sbxBBackHalfPiece, ← sbxB_backward_restrict_Ioo_eq_Ioc,
    mul_comm p (((d : ℝ)+2)/d)] using hh

/-- The scaled constant is chosen before the exponent and the radius. -/
theorem b_backward_scaled_constant_absorb (C : ℝ≥0∞) (hC : C ≠ ⊤) :
    ∃ A : ℝ, 0 < A ∧ ∀ p r : ℝ, 0 < p → 0 < r →
      (C * ENNReal.ofReal ((1+p)^2)) ^ (1/p) * ENNReal.ofReal (r ^ (-(2/p) : ℝ)) ≤
      ENNReal.ofReal ((A * (1+p) ^ (2 : ℝ) * r ^ (-2 : ℝ)) ^ (1/p)) := by
  let A := max 1 C.toReal
  have hA : 0 < A := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  refine ⟨A, hA, ?_⟩
  intro p r hp hr
  have hC' : C ≤ ENNReal.ofReal A := by
    rw [← ENNReal.ofReal_toReal hC]
    exact ENNReal.ofReal_le_ofReal (le_max_right _ _)
  have hbase : 0 < A * (1+p)^2 := by positivity
  have hroot : r ^ (-(2/p) : ℝ) = (r ^ (-2 : ℝ)) ^ (1/p) := by
    rw [← Real.rpow_mul hr.le]
    congr 1
    ring
  calc
    _ ≤ (ENNReal.ofReal A * ENNReal.ofReal ((1+p)^2)) ^ (1/p) *
        ENNReal.ofReal (r ^ (-(2/p) : ℝ)) := by
      gcongr
    _ = ENNReal.ofReal ((A * (1+p) ^ (2 : ℝ) * r ^ (-2 : ℝ)) ^ (1/p)) := by
      rw [← ENNReal.ofReal_mul hA.le, ENNReal.ofReal_rpow_of_pos hbase, hroot,
        ← ENNReal.ofReal_mul (Real.rpow_nonneg hbase.le _),
        ← Real.mul_rpow hbase.le (Real.rpow_nonneg hr.le _)]
      rw [Real.rpow_two]

/-- The translated backward local gain with a structural real constant. -/
theorem b_translated_backward_local_gain (d : ℕ) (hd : 2 ≤ d)
    (κ : ℝ) (hκ : 0 < κ) :
    ∃ C : ℝ, 0 < C ∧ sbxBTranslatedBackwardLocalGain d κ C := by
  obtain ⟨C, hC, hraw⟩ := b_translated_backward_gain_raw d hd κ hκ
  obtain ⟨A, hA, habsorb⟩ := b_backward_scaled_constant_absorb C hC
  refine ⟨A, hA, ?_⟩
  intro ρ α hell u G hcal hu ε p hε hp x r hr hS
  exact (hraw ρ α hell u G hcal hu ε p hε hp x r hr hS).trans
    (mul_le_mul_left (habsorb p r hp hr) _)

#print axioms b_translated_backward_local_gain
#print axioms b_translated_backward_gain_raw

end EinsteinFull.Calculus
