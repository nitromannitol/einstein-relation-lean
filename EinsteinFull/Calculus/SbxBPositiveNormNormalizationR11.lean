import EinsteinFull.Calculus.C17TubeInverseGainRadiusAlgebra
import EinsteinFull.Calculus.C8TubeWeightedParabolicPoincare
import EllipticRegularity.Parabolic.WeakHarnack.MeasuresCylinders

open EinsteinRelation MeasureTheory Filter EinsteinFull.External.Source.GMP
open scoped Topology ENNReal

namespace EinsteinFull.Calculus


/-- The volume correction is bounded by a structural constant. -/
theorem sbxB_volume_rpow_bound (v χ p : ℝ) (hv : 0 < v)
    (hχ : 1 < χ) (hp : 0 < p) :
    v ^ (1 / p - 1 / (χ * p)) ≤ (max 1 v) ^ (1 / p) := by
  have he : 0 ≤ 1 / p - 1 / (χ * p) := by
    have hχp : 0 < χ * p := by positivity
    have hh : 1 / (χ * p) ≤ 1 / p := by
      apply one_div_le_one_div_of_le hp
      nlinarith
    linarith
  by_cases hv1 : v ≤ 1
  · rw [max_eq_left hv1, Real.one_rpow]
    exact Real.rpow_le_one hv.le hv1 he
  · have hv1 : 1 ≤ v := le_of_not_ge hv1
    rw [max_eq_right hv1]
    apply Real.rpow_le_rpow_of_exponent_le hv1
    have : 0 ≤ 1 / (χ * p) := by positivity
    linarith

/-- The two normalized exponents absorb into one enlarged gain constant. -/
theorem sbxB_volume_gain_bound (v χ p a : ℝ) (hv : 0 < v)
    (hχ : 1 < χ) (hp : 0 < p) (ha : 0 ≤ a) :
    v⁻¹ ^ (1 / (χ * p)) * a ^ (1 / p) ≤
      (a * max 1 v) ^ (1 / p) * v⁻¹ ^ (1 / p) := by
  have hb := mul_le_mul_of_nonneg_left (sbxB_volume_rpow_bound v χ p hv hχ hp)
    (Real.rpow_nonneg ha (1 / p))
  rw [← Real.mul_rpow ha (le_trans zero_le_one (le_max_left 1 v))] at hb
  have hvp : 0 < v ^ (1 / p) := Real.rpow_pos_of_pos hv _
  have hvq : 0 < v ^ (1 / (χ * p)) := Real.rpow_pos_of_pos hv _
  rw [Real.inv_rpow hv.le, Real.inv_rpow hv.le]
  rw [Real.rpow_sub hv] at hb
  apply le_of_mul_le_mul_right _ hvp
  have heq : (v ^ (1 / (χ * p)))⁻¹ * a ^ (1 / p) * v ^ (1 / p) =
      a ^ (1 / p) * (v ^ (1 / p) / v ^ (1 / (χ * p))) := by ring
  rw [heq]
  have hc : (a * max 1 v) ^ (1 / p) * (v ^ (1 / p))⁻¹ * v ^ (1 / p) =
      (a * max 1 v) ^ (1 / p) := by field_simp
  rw [hc]
  exact hb

/-- The volume correction in the extended-nonnegative form used by `eLpNorm`. -/
theorem sbxB_volume_gain_bound_ennreal (v χ p a : ℝ) (hv : 0 < v)
    (hχ : 1 < χ) (hp : 0 < p) (ha : 0 ≤ a) :
    ENNReal.ofReal v⁻¹ ^ (1 / ENNReal.ofReal (χ * p)).toReal *
      ENNReal.ofReal (a ^ (1 / p)) ≤
    ENNReal.ofReal ((a * max 1 v) ^ (1 / p)) *
      ENNReal.ofReal v⁻¹ ^ (1 / ENNReal.ofReal p).toReal := by
  have hχp : 0 < χ * p := by positivity
  simp only [ENNReal.toReal_div, ENNReal.toReal_one,
    ENNReal.toReal_ofReal hp.le, ENNReal.toReal_ofReal hχp.le]
  rw [ENNReal.ofReal_rpow_of_pos (inv_pos.mpr hv),
    ENNReal.ofReal_rpow_of_pos (inv_pos.mpr hv),
    ← ENNReal.ofReal_mul (Real.rpow_nonneg (inv_nonneg.mpr hv.le) _),
    ← ENNReal.ofReal_mul (Real.rpow_nonneg (mul_nonneg ha
      (le_trans zero_le_one (le_max_left 1 v))) _)]
  exact ENNReal.ofReal_le_ofReal (sbxB_volume_gain_bound v χ p a hv hχ hp ha)

/-- A raw nested norm inequality persists after multiplying both measures by
    the same inverse volume, with a structural enlargement of the coefficient. -/
theorem sbxB_normalize_nested_gain {α : Type*} [MeasurableSpace α]
    (μ ν : Measure α) (f : α → ℝ) (v χ p a : ℝ)
    (hv : 0 < v) (hχ : 1 < χ) (hp : 0 < p) (ha : 0 ≤ a)
    (hraw : eLpNorm f (ENNReal.ofReal (χ * p)) μ ≤
      ENNReal.ofReal (a ^ (1 / p)) * eLpNorm f (ENNReal.ofReal p) ν) :
    eLpNorm f (ENNReal.ofReal (χ * p)) (ENNReal.ofReal v⁻¹ • μ) ≤
      ENNReal.ofReal ((a * max 1 v) ^ (1 / p)) *
      eLpNorm f (ENNReal.ofReal p) (ENNReal.ofReal v⁻¹ • ν) := by
  have hχp : 0 < χ * p := by positivity
  rw [eLpNorm_smul_measure_of_ne_zero_of_ne_top
      (ENNReal.ofReal_ne_zero_iff.mpr hχp) ENNReal.ofReal_ne_top,
    eLpNorm_smul_measure_of_ne_zero_of_ne_top
      (ENNReal.ofReal_ne_zero_iff.mpr hp) ENNReal.ofReal_ne_top]
  simp only [smul_eq_mul]
  calc
    _ ≤ ENNReal.ofReal v⁻¹ ^ (1 / ENNReal.ofReal (χ * p)).toReal *
        (ENNReal.ofReal (a ^ (1 / p)) * eLpNorm f (ENNReal.ofReal p) ν) :=
          mul_le_mul_right hraw _
    _ = (ENNReal.ofReal v⁻¹ ^ (1 / ENNReal.ofReal (χ * p)).toReal *
        ENNReal.ofReal (a ^ (1 / p))) * eLpNorm f (ENNReal.ofReal p) ν := by rw [mul_assoc]
    _ ≤ (ENNReal.ofReal ((a * max 1 v) ^ (1 / p)) *
        ENNReal.ofReal v⁻¹ ^ (1 / ENNReal.ofReal p).toReal) *
        eLpNorm f (ENNReal.ofReal p) ν :=
          mul_le_mul_left (sbxB_volume_gain_bound_ennreal v χ p a hv hχ hp ha) _
    _ = _ := by rw [mul_assoc]


/-- The normalized positive-cylinder measure, after swapping time and space. -/
theorem sbxB_positive_normalized_norm (d : ℕ) (σ : ℝ)
    (hσ : 1 / 2 ≤ σ) (hσ1 : σ ≤ 1) (p : ℝ≥0∞)
    (f : ℝ × Vec d → ℝ) :
    eLpNorm (fun z : Vec d × ℝ => f (z.2, z.1)) p
      ((PDE.Parabolic.WeakHarnack.cylMeasure (PDE.Parabolic.WeakHarnack.posCyl d 1)).restrict
        (PDE.Parabolic.WeakHarnack.posCyl d σ)) =
    eLpNorm f p ((volume (PDE.Parabolic.WeakHarnack.posCyl d 1))⁻¹ •
      volume.restrict (Set.Ioo (-3 / 4 - (σ - 1 / 2) / 4)
        (-1 / 2 + (σ - 1 / 2) / 4) ×ˢ
        sourceBall 0 (1 / 2 + (σ - 1 / 2) / 2))) := by
  have hm : Measure.map (Prod.swap : ℝ × Vec d → Vec d × ℝ)
      (volume.restrict (Set.Ioo (-3 / 4 - (σ - 1 / 2) / 4)
        (-1 / 2 + (σ - 1 / 2) / 4) ×ˢ
        sourceBall 0 (1 / 2 + (σ - 1 / 2) / 2))) =
      volume.restrict (PDE.Parabolic.WeakHarnack.posCyl d σ) := by
    rw [PDE.Parabolic.WeakHarnack.posCyl,
      c8_sourceBall_eq_euclideanBall 0 (by linarith)]
    simp only [Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.prod_swap]
  have hf : MeasurableEmbedding (Prod.swap : ℝ × Vec d → Vec d × ℝ) :=
    MeasurableEquiv.prodComm.measurableEmbedding
  rw [PDE.Parabolic.WeakHarnack.cylMeasure_restrict
      (PDE.Parabolic.WeakHarnack.measurableSet_posCyl _)
      (PDE.Parabolic.WeakHarnack.posCyl_mono hσ hσ1),
    ← hm, ← Measure.map_smul _ hf.measurable.aemeasurable,
    hf.eLpNorm_map_measure]
  rfl

/-- A literal time-first positive gain gives the normalized C8 positive gain.
    The enlarged constant is fixed before the coefficients and caloric field. -/
theorem sbxB_positive_nested_gain_normalize (d : ℕ) (κ χ A m q : ℝ)
    (hχ : 1 < χ) (hA : 1 ≤ A) (_hm : 0 < m) (_hq : 0 < q)
    (hraw : ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
      IsUniformlyElliptic κ ρ α → ∀ (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d),
      IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1) u G →
      (∀ᵐ z ∂volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1), 0 ≤ u z) →
      ∀ ε : ℝ, 0 < ε → ∀ σ' σ : ℝ, 1 / 2 ≤ σ' → σ' < σ → σ ≤ 1 →
      ∀ p : ℝ, 0 < p → p ≤ q →
      eLpNorm (fun z => u z + ε) (ENNReal.ofReal (χ * p))
        (volume.restrict (Set.Ioo (-3 / 4 - (σ' - 1 / 2) / 4)
          (-1 / 2 + (σ' - 1 / 2) / 4) ×ˢ
          sourceBall 0 (1 / 2 + (σ' - 1 / 2) / 2))) ≤
      ENNReal.ofReal ((A * (σ - σ') ^ (-m)) ^ (1 / p)) *
      eLpNorm (fun z => u z + ε) (ENNReal.ofReal p)
        (volume.restrict (Set.Ioo (-3 / 4 - (σ - 1 / 2) / 4)
          (-1 / 2 + (σ - 1 / 2) / 4) ×ˢ
          sourceBall 0 (1 / 2 + (σ - 1 / 2) / 2)))) :
    ∃ A' : ℝ, 1 ≤ A' ∧ ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
      IsUniformlyElliptic κ ρ α → ∀ (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d),
      IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1) u G →
      (∀ᵐ z ∂volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1), 0 ≤ u z) →
      ∀ ε : ℝ, 0 < ε → ∀ σ' σ : ℝ, 1 / 2 ≤ σ' → σ' < σ → σ ≤ 1 →
      ∀ p : ℝ, 0 < p → p ≤ q →
      eLpNorm (fun z : Vec d × ℝ => u (z.2, z.1) + ε) (ENNReal.ofReal (χ * p))
        ((PDE.Parabolic.WeakHarnack.cylMeasure (PDE.Parabolic.WeakHarnack.posCyl d 1)).restrict
          (PDE.Parabolic.WeakHarnack.posCyl d σ')) ≤
      ENNReal.ofReal ((A' * (σ - σ') ^ (-m)) ^ (1 / p)) *
      eLpNorm (fun z : Vec d × ℝ => u (z.2, z.1) + ε) (ENNReal.ofReal p)
        ((PDE.Parabolic.WeakHarnack.cylMeasure (PDE.Parabolic.WeakHarnack.posCyl d 1)).restrict
          (PDE.Parabolic.WeakHarnack.posCyl d σ)) := by
  let V : ℝ≥0∞ := volume (PDE.Parabolic.WeakHarnack.posCyl d 1)
  have hV0 : V ≠ 0 := (PDE.Parabolic.WeakHarnack.volume_posCyl_pos (d := d) (σ := 1) (by norm_num)).ne'
  have hVt : V ≠ ⊤ := PDE.Parabolic.WeakHarnack.volume_posCyl_ne_top (d := d) (σ := 1) (by norm_num)
  have hV : 0 < V.toReal := ENNReal.toReal_pos hV0 hVt
  have hVi : ENNReal.ofReal V.toReal⁻¹ = V⁻¹ := by
    rw [ENNReal.ofReal_inv_of_pos hV, ENNReal.ofReal_toReal hVt]
  refine ⟨A * max 1 V.toReal, ?_, ?_⟩
  · exact one_le_mul_of_one_le_of_one_le hA (le_max_left _ _)
  intro ρ α hell u G hcal hu ε hε σ' σ hσ' hσσ hσ p hp hpq
  have hσlower : 1 / 2 ≤ σ := le_trans hσ' hσσ.le
  rw [sbxB_positive_normalized_norm d σ' hσ' (le_trans hσσ.le hσ)
      (ENNReal.ofReal (χ * p)) (fun z => u z + ε),
    sbxB_positive_normalized_norm d σ hσlower hσ
      (ENNReal.ofReal p) (fun z => u z + ε)]
  have ha : 0 ≤ A * (σ - σ') ^ (-m) :=
    mul_nonneg (le_trans zero_le_one hA) (Real.rpow_nonneg (by linarith) _)
  have hh := sbxB_normalize_nested_gain _ _ (fun z => u z + ε) V.toReal χ p
    (A * (σ - σ') ^ (-m)) hV hχ hp ha
    (hraw ρ α hell u G hcal hu ε hε σ' σ hσ' hσσ hσ p hp hpq)
  rw [hVi] at hh
  simpa only [mul_comm, mul_left_comm, mul_assoc] using hh


end EinsteinFull.Calculus
