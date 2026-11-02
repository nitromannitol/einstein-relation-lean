import EinsteinFull.Calculus.SbxBBackwardLocalGainClosureR13

open EinsteinRelation MeasureTheory EinsteinFull.External.Source.GMP
open scoped ENNReal

namespace EinsteinFull.Calculus

/-- A local inverse gain remains valid when its structural constant is enlarged. -/
theorem sbxB_translated_backward_local_gain_mono
    (d : ℕ) (κ C D : ℝ) (hC : 0 ≤ C) (hCD : C ≤ D)
    (hgain : sbxBTranslatedBackwardLocalGain d κ C) :
    sbxBTranslatedBackwardLocalGain d κ D := by
  intro ρ α hell u G hcal hu ε p hε hp x r hr hsubset
  have h := hgain ρ α hell u G hcal hu ε p hε hp x r hr hsubset
  have hbase : C * (1 + p) ^ (2 : ℝ) * r ^ (-2 : ℝ) ≤
      D * (1 + p) ^ (2 : ℝ) * r ^ (-2 : ℝ) := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hCD (Real.rpow_nonneg (by linarith) _))
      (Real.rpow_nonneg hr.le _)
  have hnonneg : 0 ≤ C * (1 + p) ^ (2 : ℝ) * r ^ (-2 : ℝ) := by positivity
  have hcoeff := ENNReal.ofReal_le_ofReal
    (Real.rpow_le_rpow hnonneg hbase (by positivity : 0 ≤ 1 / p))
  exact h.trans (mul_le_mul_left hcoeff _)

/-- Conditional assembly from the literal translated backward estimate. The
backward estimate is a separate pending producer; this theorem does not prove it. -/
theorem sbxB_both_negative_gains_of_literal_backward_estimate
    (d : ℕ) (hd : 2 ≤ d) (κ : ℝ)
    (hback : ∃ C : ℝ, 0 ≤ C ∧
      ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d), IsUniformlyElliptic κ ρ α →
    ∀ (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d),
    IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1) u G →
    (∀ᵐ z ∂volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1), 0 ≤ u z) →
    ∀ (ε p : ℝ), 0 < ε → 0 < p → ∀ (x : ℝ × Vec d) (r : ℝ), 0 < r →
    (∀ z ∈ sbxBBackPiece x r,
      (z.1 + 3 / 4, z.2) ∈ Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall (0 : Vec d) 1) →
    eLpNorm (fun z => 1 / max ε (u (z.1 + 3 / 4, z.2) + ε))
        (ENNReal.ofReal ((((d : ℝ) + 2) / d) * p))
        (volume.restrict (sbxBBackHalfPiece x r)) ≤
      ENNReal.ofReal ((C * (1 + p) ^ (2 : ℝ) * r ^ (-2 : ℝ)) ^ (1 / p)) *
        eLpNorm (fun z => 1 / max ε (u (z.1 + 3 / 4, z.2) + ε))
          (ENNReal.ofReal p) (volume.restrict (sbxBBackPiece x r))) :
    ∃ A₂ β₂ m₂ A₃ β₃ m₃ : ℝ, 1 ≤ A₂ ∧ 0 ≤ β₂ ∧ 0 < m₂ ∧
      1 ≤ A₃ ∧ 0 ≤ β₃ ∧ 0 < m₃ ∧
      (∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
      IsUniformlyElliptic κ ρ α → ∀ (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d),
      IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1) u G →
      (∀ᵐ z ∂volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1), 0 ≤ u z) →
      ∀ ε : ℝ, 0 < ε →
      (∀ σ' σ : ℝ, 1 / 2 ≤ σ' → σ' < σ → σ ≤ 1 → ∀ p : ℝ, 0 < p →
      eLpNorm (fun z => 1 / max ε (u (z.2 + 3 / 4, z.1) + ε)) (ENNReal.ofReal ((((d : ℝ) + 2) / d) * p))
        ((PDE.Parabolic.WeakHarnack.cylMeasure (PDE.Parabolic.WeakHarnack.negCyl d 1)).restrict
          (PDE.Parabolic.WeakHarnack.negCyl d σ')) ≤
      ENNReal.ofReal ((A₂ * (1 + p) ^ β₂ * (σ - σ') ^ (-m₂)) ^ (1 / p)) *
      eLpNorm (fun z => 1 / max ε (u (z.2 + 3 / 4, z.1) + ε)) (ENNReal.ofReal p)
        ((PDE.Parabolic.WeakHarnack.cylMeasure (PDE.Parabolic.WeakHarnack.negCyl d 1)).restrict
          (PDE.Parabolic.WeakHarnack.negCyl d σ)))) ∧
      (∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
      IsUniformlyElliptic κ ρ α → ∀ (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d),
      IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1) u G →
      (∀ᵐ z ∂volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1), 0 ≤ u z) →
      ∀ ε : ℝ, 0 < ε →
      (∀ σ' σ : ℝ, 1 / 2 ≤ σ' → σ' < σ → σ ≤ 1 → ∀ p : ℝ, 0 < p →
      eLpNorm (fun z => 1 / max ε (u (z.2 + 3 / 4, z.1) + ε)) (ENNReal.ofReal ((((d : ℝ) + 2) / d) * p))
        ((PDE.Parabolic.WeakHarnack.cylMeasure (PDE.Parabolic.WeakHarnack.negCylInner d 1)).restrict
          (PDE.Parabolic.WeakHarnack.negCylInner d σ')) ≤
      ENNReal.ofReal ((A₃ * (1 + p) ^ β₃ * (σ - σ') ^ (-m₃)) ^ (1 / p)) *
      eLpNorm (fun z => 1 / max ε (u (z.2 + 3 / 4, z.1) + ε)) (ENNReal.ofReal p)
        ((PDE.Parabolic.WeakHarnack.cylMeasure (PDE.Parabolic.WeakHarnack.negCylInner d 1)).restrict
          (PDE.Parabolic.WeakHarnack.negCylInner d σ)))) := by
  obtain ⟨C, hC, hlocal⟩ := hback
  have hlocal' : sbxBTranslatedBackwardLocalGain d κ (max 1 C) :=
    sbxB_translated_backward_local_gain_mono d κ C (max 1 C) hC
      (le_max_right 1 C) hlocal
  exact sbxB_both_shifted_negative_normalized_gains_of_local d hd κ (max 1 C)
    (le_max_left 1 C) hlocal'

/-- Both normalized negative-cylinder gains for every positive exponent. -/
theorem sbxB_both_shifted_negative_normalized_gains
    (d : ℕ) (hd : 2 ≤ d) (κ : ℝ) (hκ : 0 < κ) :
    ∃ A₂ β₂ m₂ A₃ β₃ m₃ : ℝ, 1 ≤ A₂ ∧ 0 ≤ β₂ ∧ 0 < m₂ ∧
      1 ≤ A₃ ∧ 0 ≤ β₃ ∧ 0 < m₃ ∧
      (∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
      IsUniformlyElliptic κ ρ α → ∀ (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d),
      IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1) u G →
      (∀ᵐ z ∂volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1), 0 ≤ u z) →
      ∀ ε : ℝ, 0 < ε →
      (∀ σ' σ : ℝ, 1 / 2 ≤ σ' → σ' < σ → σ ≤ 1 → ∀ p : ℝ, 0 < p →
      eLpNorm (fun z => 1 / max ε (u (z.2 + 3 / 4, z.1) + ε)) (ENNReal.ofReal ((((d : ℝ) + 2) / d) * p))
        ((PDE.Parabolic.WeakHarnack.cylMeasure (PDE.Parabolic.WeakHarnack.negCyl d 1)).restrict
          (PDE.Parabolic.WeakHarnack.negCyl d σ')) ≤
      ENNReal.ofReal ((A₂ * (1 + p) ^ β₂ * (σ - σ') ^ (-m₂)) ^ (1 / p)) *
      eLpNorm (fun z => 1 / max ε (u (z.2 + 3 / 4, z.1) + ε)) (ENNReal.ofReal p)
        ((PDE.Parabolic.WeakHarnack.cylMeasure (PDE.Parabolic.WeakHarnack.negCyl d 1)).restrict
          (PDE.Parabolic.WeakHarnack.negCyl d σ)))) ∧
      (∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
      IsUniformlyElliptic κ ρ α → ∀ (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d),
      IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1) u G →
      (∀ᵐ z ∂volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1), 0 ≤ u z) →
      ∀ ε : ℝ, 0 < ε →
      (∀ σ' σ : ℝ, 1 / 2 ≤ σ' → σ' < σ → σ ≤ 1 → ∀ p : ℝ, 0 < p →
      eLpNorm (fun z => 1 / max ε (u (z.2 + 3 / 4, z.1) + ε)) (ENNReal.ofReal ((((d : ℝ) + 2) / d) * p))
        ((PDE.Parabolic.WeakHarnack.cylMeasure (PDE.Parabolic.WeakHarnack.negCylInner d 1)).restrict
          (PDE.Parabolic.WeakHarnack.negCylInner d σ')) ≤
      ENNReal.ofReal ((A₃ * (1 + p) ^ β₃ * (σ - σ') ^ (-m₃)) ^ (1 / p)) *
      eLpNorm (fun z => 1 / max ε (u (z.2 + 3 / 4, z.1) + ε)) (ENNReal.ofReal p)
        ((PDE.Parabolic.WeakHarnack.cylMeasure (PDE.Parabolic.WeakHarnack.negCylInner d 1)).restrict
          (PDE.Parabolic.WeakHarnack.negCylInner d σ)))) := by
  obtain ⟨C, hC, hlocal⟩ := b_translated_backward_local_gain d hd κ hκ
  exact sbxB_both_negative_gains_of_literal_backward_estimate d hd κ ⟨C, hC.le, hlocal⟩

#print axioms sbxB_both_shifted_negative_normalized_gains

#print axioms sbxB_both_negative_gains_of_literal_backward_estimate

#print axioms sbxB_translated_backward_local_gain_mono

end EinsteinFull.Calculus
