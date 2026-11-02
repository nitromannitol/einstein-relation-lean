import EinsteinFull.Calculus.C5TubePositiveConcentricGain

open EinsteinRelation MeasureTheory Filter EinsteinFull.External.Source.GMP
open scoped Topology ENNReal

namespace EinsteinFull.Calculus

/-- The time-first positive cylinder used in the concentric iteration. -/
def sbxBPositiveCylinder (d : ℕ) (σ : ℝ) : Set (ℝ × Vec d) :=
  Set.Ioo (-3 / 4 - (σ - 1 / 2) / 4) (-1 / 2 + (σ - 1 / 2) / 4) ×ˢ
    sourceBall 0 (1 / 2 + (σ - 1 / 2) / 2)

/-- The canonical compact cutoff used for two nested positive cylinders. -/
noncomputable def sbxBPositiveCutoff (d : ℕ) (σ' σ : ℝ) : ℝ × Vec d → ℝ :=
  let r : ℝ := 1 / 2 + (σ' - 1 / 2) / 2
  let R : ℝ := 1 / 2 + (σ - 1 / 2) / 2
  let a : ℝ := -3 / 4 - (σ - 1 / 2) / 4
  let a' : ℝ := -3 / 4 - (σ' - 1 / 2) / 4
  let b : ℝ := -1 / 2 + (σ - 1 / 2) / 4
  let δ : ℝ := (σ - σ') / 8
  fun z => (PDE.Parabolic.LocalMax.cylTimeRamp (a + δ) ((a' - (a + δ)) / 2) z.1 *
    PDE.Parabolic.LocalMax.timeRamp (b - δ) δ z.1) *
      PDE.canonicalBallCutoff (0 : Vec d) r R z.2

/-- The canonical cutoff has precisely the admissibility needed by the
positive-power Sobolev estimate. -/
theorem sbxB_positive_cutoff_admissible (d : ℕ) (σ' σ : ℝ)
    (hσ' : 1 / 2 ≤ σ') (hσ : σ' < σ) (hσ1 : σ ≤ 1) :
    ContDiff ℝ (⊤ : ℕ∞) (sbxBPositiveCutoff d σ' σ) ∧
    HasCompactSupport (sbxBPositiveCutoff d σ' σ) ∧
    tsupport (sbxBPositiveCutoff d σ' σ) ⊆
      Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall (0 : Vec d) 1 ∧
    (∀ z ∈ sbxBPositiveCylinder d σ', sbxBPositiveCutoff d σ' σ z = 1) := by
  let r : ℝ := 1 / 2 + (σ' - 1 / 2) / 2
  let R : ℝ := 1 / 2 + (σ - 1 / 2) / 2
  let a : ℝ := -3 / 4 - (σ - 1 / 2) / 4
  let a' : ℝ := -3 / 4 - (σ' - 1 / 2) / 4
  let b : ℝ := -1 / 2 + (σ - 1 / 2) / 4
  let δ : ℝ := (σ - σ') / 8
  have hr : 0 < r ∧ r < R ∧ R < 1 := c5_positive_concentric_radius_bounds σ' σ hσ' hσ hσ1
  have ht := c5_positive_concentric_time_gaps σ' σ hσ' hσ hσ1
  dsimp only at ht
  have hc := c11_compact_cylinder_cutoff (d := d) (r := r) (R := R)
    (T := a + δ) (T' := a') (b := b - δ) (h := δ) hr.1.le hr.2.1 ht.2.2.1 ht.1
  change ContDiff ℝ (⊤ : ℕ∞) _ ∧ HasCompactSupport _ ∧ _ ∧ _
  refine ⟨hc.1, hc.2.1, ?_, ?_⟩
  · intro z hz
    have h := hc.2.2.1 hz
    have hx := hc.2.2.2.1 h.2
    rw [← c8_sourceBall_eq_euclideanBall (0 : Vec d) (lt_trans hr.1 hr.2.1)] at hx
    refine ⟨⟨lt_of_lt_of_le ht.2.1 h.1.1, lt_of_le_of_lt h.1.2 ht.2.2.2.2⟩, ?_⟩
    change euclideanNorm (z.2 - 0) < 1
    change euclideanNorm (z.2 - 0) < R at hx
    exact lt_trans hx hr.2.2
  · intro z hz
    apply hc.2.2.2.2.2 z (le_of_lt hz.1.1) (le_trans (le_of_lt hz.1.2) ht.2.2.2.1)
    rw [← c8_sourceBall_eq_euclideanBall (0 : Vec d) hr.1]
    exact hz.2

/-- A positive iteration cylinder is contained in the original unit cylinder. -/
theorem sbxB_positive_cylinder_subset (d : ℕ) (σ : ℝ)
    (_hσ : 1 / 2 ≤ σ) (hσ1 : σ ≤ 1) :
    sbxBPositiveCylinder d σ ⊆ Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall (0 : Vec d) 1 := by
  intro z hz
  rcases hz with ⟨ht, hx⟩
  refine ⟨⟨by linarith [ht.1], by linarith [ht.2]⟩, ?_⟩
  change euclideanNorm (z.2 - 0) < 1
  change euclideanNorm (z.2 - 0) < 1 / 2 + (σ - 1 / 2) / 2 at hx
  linarith

/-- The Sobolev and energy constants combine under the input-exponent root. -/
theorem sbxB_positive_gain_coefficient (C D : ℝ≥0∞) (p χ : ℝ)
    (hp : 0 < p) :
    C ^ ((p * χ)⁻¹) * D ^ p⁻¹ = (C ^ χ⁻¹ * D) ^ p⁻¹ := by
  rw [ENNReal.mul_rpow_of_nonneg _ _ (inv_nonneg.mpr hp.le), ← ENNReal.rpow_mul]
  rw [mul_inv_rev]

/-- A finite Sobolev constant can be absorbed into a real structural
constant in the form needed by the normalized iteration. -/
theorem sbxB_positive_gain_coefficient_bound (C : ℝ≥0∞) (hC : C ≠ ⊤)
    (A g m p χ : ℝ) (hA : 0 < A) (hg : 0 < g) (hp : 0 < p) (hχ : 1 ≤ χ) :
    C ^ ((p * χ)⁻¹) * (ENNReal.ofReal (A * g ^ (-m))) ^ p⁻¹ ≤
      ENNReal.ofReal (((max 1 C.toReal * A) * g ^ (-m)) ^ (1 / p)) := by
  let B : ℝ := max 1 C.toReal
  have hB : 1 ≤ B := le_max_left _ _
  have hBp : 0 < B := lt_of_lt_of_le zero_lt_one hB
  have hC' : C ≤ ENNReal.ofReal B := by
    rw [← ENNReal.ofReal_toReal hC]
    exact ENNReal.ofReal_le_ofReal (le_max_right _ _)
  have hχp : 0 < χ := lt_of_lt_of_le zero_lt_one hχ
  have hχinv : χ⁻¹ ≤ 1 := (inv_le_one₀ hχp).2 hχ
  have hroot : C ^ χ⁻¹ ≤ ENNReal.ofReal B := by
    calc
      C ^ χ⁻¹ ≤ (ENNReal.ofReal B) ^ χ⁻¹ :=
        ENNReal.rpow_le_rpow hC' (inv_nonneg.mpr hχp.le)
      _ ≤ (ENNReal.ofReal B) ^ (1 : ℝ) :=
        ENNReal.rpow_le_rpow_of_exponent_le (by simpa using ENNReal.ofReal_le_ofReal hB) hχinv
      _ = ENNReal.ofReal B := ENNReal.rpow_one _
  rw [sbxB_positive_gain_coefficient C _ p χ hp]
  calc
    _ ≤ (ENNReal.ofReal B * ENNReal.ofReal (A * g ^ (-m))) ^ p⁻¹ :=
      ENNReal.rpow_le_rpow (mul_le_mul_left hroot _) (inv_nonneg.mpr hp.le)
    _ = ENNReal.ofReal (((B * A) * g ^ (-m)) ^ (1 / p)) := by
      rw [← ENNReal.ofReal_mul hBp.le, ← ENNReal.ofReal_rpow_of_pos]
      · congr 2 <;> ring
      · positivity

/-- Sobolev yields the unnormalized positive gain from the literal slice-mass,
coefficient-energy, and energy-measurability inputs for the canonical cutoff. -/
theorem sbxB_positive_nested_gain (d : ℕ) (hd : 2 ≤ d) (κ : ℝ) (hκ : 0 < κ) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ (A : ℝ), 1 ≤ A → ∀ (m : ℝ),
    ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
    IsUniformlyElliptic κ ρ α →
    ∀ (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d),
    IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1) u G →
    (∀ᵐ z ∂volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1), 0 ≤ u z) →
    ∀ ε : ℝ, 0 < ε → ∀ σ' σ : ℝ, 1 / 2 ≤ σ' → σ' < σ → σ ≤ 1 →
    ∀ p : ℝ, 0 < p → p ≤ (d : ℝ) / (2 * ((d : ℝ) + 2)) →
    let D : ℝ≥0∞ := ENNReal.ofReal (A * (σ - σ') ^ (-m))
    let η := sbxBPositiveCutoff d σ' σ
    let w : ℝ × Vec d → ℝ := fun z => u z + ε
    let v : ℝ × Vec d → ℝ := fun z => η z * (w z) ^ (p / 2)
    let J : ℝ × Vec d → Vec d := fun z =>
      η z • ((p / 2 * (w z) ^ (p / 2 - 1)) • G z) +
        (w z) ^ (p / 2) • (fun j => fderiv ℝ η z (0, unitVector j))
    (∀ᵐ t ∂volume.restrict (Set.Ioo (-1 : ℝ) 1),
      (∫⁻ x in sourceBall (0 : Vec d) 1, ENNReal.ofReal (ρ x) * ‖v (t,x)‖ₑ ^ (2 : ℝ)) ≤
        D * ∫⁻ z in sbxBPositiveCylinder d σ, ENNReal.ofReal (w z) ^ p) →
    AEMeasurable (fun z => ENNReal.ofReal (dot ((α z.2).mulVec (J z)) (J z)))
      (volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1)) →
    (∫⁻ z in Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall (0 : Vec d) 1,
      ENNReal.ofReal (dot ((α z.2).mulVec (J z)) (J z))) ≤
        D * ∫⁻ z in sbxBPositiveCylinder d σ, ENNReal.ofReal (w z) ^ p →
    eLpNorm w (ENNReal.ofReal (p * (((d : ℝ) + 2) / d)))
      (volume.restrict (sbxBPositiveCylinder d σ')) ≤
      ENNReal.ofReal (((B * A) * (σ - σ') ^ (-m)) ^ (1 / p)) *
        eLpNorm w (ENNReal.ofReal p) (volume.restrict (sbxBPositiveCylinder d σ)) := by
  obtain ⟨C, hC, hgain⟩ := c5_shifted_cutoff_norm_gain d hd κ hκ
  refine ⟨max 1 C.toReal, le_max_left _ _, ?_⟩
  intro A hA m ρ α hell u G hcal hu ε hε σ' σ hσ' hσσ hσ p hp hpmax D η w v J hmass hmeas henergy
  have hcut := sbxB_positive_cutoff_admissible d σ' σ hσ' hσσ hσ
  let K := Prod.snd '' tsupport η
  have hK : IsCompact K := hcut.2.1.isCompact.image continuous_snd
  have hKU : K ⊆ sourceBall (0 : Vec d) 1 := by
    rintro x ⟨z, hz, rfl⟩
    exact (hcut.2.2.1 hz).2
  have hzero : ∀ t x, x ∉ K → η (t,x) = 0 := by
    intro t x hx
    apply image_eq_zero_of_notMem_tsupport
    intro hz
    exact hx ⟨(t,x), hz, rfl⟩
  have hp1 : p < 1 := lt_trans (c5_positive_gain_exponent_lt_half d hd p hpmax) (by norm_num)
  have hSm : MeasurableSet (sbxBPositiveCylinder d σ') :=
    measurableSet_Ioo.prod (c17_isOpen_sourceBall _ _).measurableSet
  have h := hgain ρ α hell u G hcal hu ε hε η hcut.1 hcut.2.1 K hK hKU hzero
    (sbxBPositiveCylinder d σ') (sbxBPositiveCylinder d σ) hSm
    (sbxB_positive_cylinder_subset d σ' hσ' (le_trans hσσ.le hσ))
    (sbxB_positive_cylinder_subset d σ (le_trans hσ' hσσ.le) hσ)
    hcut.2.2.2 p hp hp1 D hmass hmeas henergy
  have hdpos : 0 < (d : ℝ) := by exact_mod_cast (show 0 < d by omega)
  have hχ : 1 ≤ (((d : ℝ) + 2) / d) := by
    apply (one_le_div hdpos).2
    linarith
  have hcoeff := sbxB_positive_gain_coefficient_bound C hC A (σ - σ') m p
    (((d : ℝ) + 2) / d) (lt_of_lt_of_le zero_lt_one hA) (sub_pos.mpr hσσ) hp hχ
  exact h.trans (mul_le_mul_left hcoeff _)

end EinsteinFull.Calculus

