import EinsteinFull.Calculus.C5TubePositiveConcentricGain

open EinsteinRelation MeasureTheory Filter EinsteinFull.External.Source.GMP
open scoped Topology ENNReal

namespace EinsteinFull.Calculus

/-- The literal real slice estimate implies the extended-nonnegative slice
mass clause used by the positive-power gain. -/
theorem b_positive_slice_lintegral {d : ℕ} {κ ε p D : ℝ}
    (hκ : 0 < κ) (hε : 0 < ε) (hp : 0 < p) (hp1 : p < 1) (hD : 0 ≤ D)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d) (hell : IsUniformlyElliptic κ ρ α)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hcal : IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1) u G)
    (hu : ∀ᵐ z ∂volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1), 0 ≤ u z)
    (η : ℝ × Vec d → ℝ) (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (T : Set (ℝ × Vec d))
    (hT : T ⊆ Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1)
    (htrace : ∀ᵐ t ∂volume.restrict (Set.Ioo (-1 : ℝ) 1),
      (∫ x in sourceBall (0 : Vec d) 1,
        ρ x * (η (t,x) * Real.rpow (u (t,x) + ε) (p / 2)) ^ 2) ≤
      D * ∫ z in T, Real.rpow (u z + ε) p) :
    ∀ᵐ t ∂volume.restrict (Set.Ioo (-1 : ℝ) 1),
      (∫⁻ x in sourceBall (0 : Vec d) 1,
        ENNReal.ofReal (ρ x) * ‖η (t,x) * Real.rpow (u (t,x) + ε) (p / 2)‖ₑ ^ (2 : ℝ)) ≤
      ENNReal.ofReal D * ∫⁻ z in T, ENNReal.ofReal (u z + ε) ^ p := by
  let I : Set ℝ := Set.Ioo (-1) 1
  let U : Set (Vec d) := sourceBall 0 1
  let μ : Measure (ℝ × Vec d) := volume.restrict (I ×ˢ U)
  let w : ℝ × Vec d → ℝ := fun z => u z + ε
  obtain ⟨hshift, hpos⟩ := c8_weighted_caloric_positive_shift hκ hell hcal hu hε
  have hpow : Integrable (fun z => Real.rpow (w z) p) μ :=
    c13_positive_power_integrable hε hp hp1 ρ α w G hshift hpos
  have hweighted : Integrable (fun z => ρ z.2 * Real.rpow (w z) p) μ :=
    c13_weighted_positive_power_integrable hκ hε hp hp1 ρ α hell w G hshift hpos
  have hηtop : MemLp η ∞ μ := hη.continuous.memLp_top_of_hasCompactSupport hηc μ
  have hmass : Integrable (fun z => (ρ z.2 * Real.rpow (w z) p) * (η z * η z)) μ := by
    convert hweighted.mul_of_top_right (hηtop.mul hηtop) using 1 <;>
      ext z <;> simp only [Pi.mul_apply] <;> ring
  have hmass' : Integrable (fun z => ρ z.2 * (η z * Real.rpow (w z) (p / 2)) ^ 2) μ := by
    apply hmass.congr
    filter_upwards [hpos] with z hz
    have hw : 0 ≤ w z := le_trans hε.le hz
    have he : Real.rpow (w z) (p / 2) ^ 2 = Real.rpow (w z) p := by
      convert (Real.rpow_mul_natCast hw (p / 2) 2).symm using 1 <;>
        congr 1 <;> ring
    rw [mul_pow, he]
    ring
  have hmassprod := hmass'
  rw [show μ = (volume.restrict I).prod (volume.restrict U) by
    dsimp [μ]; rw [Measure.volume_eq_prod, Measure.prod_restrict]] at hmassprod
  have hTpos : ∀ᵐ z ∂volume.restrict T, 0 ≤ w z :=
    (ae_restrict_of_ae_restrict_of_subset hT hpos).mono fun _ hz => le_trans hε.le hz
  have hTpow : Integrable (fun z => Real.rpow (w z) p) (volume.restrict T) :=
    hpow.mono_measure (Measure.restrict_mono_set volume hT)
  have hTrhs : (∫⁻ z in T, ENNReal.ofReal (w z) ^ p) =
      ENNReal.ofReal (∫ z in T, Real.rpow (w z) p) := by
    rw [ofReal_integral_eq_lintegral_ofReal hTpow
      (hTpos.mono fun _ hz => Real.rpow_nonneg hz p)]
    apply lintegral_congr_ae
    filter_upwards [hTpos] with z hz
    exact ENNReal.ofReal_rpow_of_nonneg hz hp.le
  filter_upwards [hmassprod.prod_right_ae, htrace] with t hint ht
  have hlhs : (∫⁻ x in U, ENNReal.ofReal (ρ x) *
      ‖η (t,x) * Real.rpow (w (t,x)) (p / 2)‖ₑ ^ (2 : ℝ)) =
      ENNReal.ofReal (∫ x in U, ρ x * (η (t,x) * Real.rpow (w (t,x)) (p / 2)) ^ 2) := by
    rw [ofReal_integral_eq_lintegral_ofReal hint
      (ae_of_all _ fun x => mul_nonneg (hκ.le.trans (hell.2.2 x).1) (sq_nonneg _))]
    apply lintegral_congr
    intro x
    rw [ENNReal.rpow_two, Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _),
      ← ENNReal.ofReal_mul (hκ.le.trans (hell.2.2 x).1)]
    simp only [sq_abs]
  rw [hlhs, hTrhs, ← ENNReal.ofReal_mul hD]
  exact ENNReal.ofReal_le_ofReal ht


end EinsteinFull.Calculus
