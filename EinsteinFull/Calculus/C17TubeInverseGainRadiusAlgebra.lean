import EinsteinFull.Calculus.C17TubeScaledLocalMax

open EinsteinRelation MeasureTheory EinsteinFull.External.Source.GMP
open scoped ENNReal

namespace EinsteinFull.Calculus

/-- The radius-loss factor in the inverse-power gain is positive. -/
@[nolint unusedArguments]
theorem c17_inverse_gain_radius_factor (p r R : ℝ)
    (hp : 0 < p) (hrR : r < R) :
    0 < Real.rpow (R-r) (-(2/p)) := by
  exact Real.rpow_pos_of_pos (sub_pos.mpr hrR) _

/-- The physical radius loss splits into the scale and unit-cylinder losses. -/
theorem c17_inverse_gain_radius_factor_rescale (p r R : ℝ)
    (hR : 0 < R) (hrR : r < R) :
    Real.rpow (R-r) (-(2/p)) =
      Real.rpow R (-(2/p)) * Real.rpow (1-r/R) (-(2/p)) := by
  have hunit : 0 < 1-r/R := by
    have h : r / R < 1 := (div_lt_one hR).2 hrR
    linarith
  have heq : R-r = R * (1-r/R) := by field_simp [ne_of_gt hR]
  rw [heq]
  change (R * (1-r/R)) ^ (-(2/p) : ℝ) =
    R ^ (-(2/p) : ℝ) * (1-r/R) ^ (-(2/p) : ℝ)
  exact Real.mul_rpow hR.le hunit.le

/-- The parabolic Jacobian contributes the expected inverse-power norm scale. -/
theorem c17_parabolic_jacobian_rpow (d : ℕ) (p R : ℝ) (hR : 0 < R) :
    Real.rpow ((R ^ (d+2))⁻¹) (1/p) =
      Real.rpow R (-((d+2 : ℕ) : ℝ) / p) := by
  change ((R ^ (d+2))⁻¹) ^ (1/p : ℝ) = R ^ (-((d+2 : ℕ) : ℝ) / p : ℝ)
  rw [Real.inv_rpow (pow_nonneg hR.le _), ← Real.rpow_natCast,
    ← Real.rpow_mul hR.le, ← Real.rpow_neg hR.le]
  congr 1
  ring

/-- The Jacobian exponent difference for the parabolic Sobolev gain. -/
theorem c17_parabolic_gain_exponent (d p : ℝ) (hd : 0 < d) (hp : 0 < p) :
    (d + 2) * (1 / p - 1 / (p * ((d + 2) / d))) = 2 / p := by
  have hd2 : d + 2 ≠ 0 := by linarith
  field_simp [ne_of_gt hd, ne_of_gt hp, hd2]
  ring

/-- The ratio of Jacobian factors gives the physical inverse-gain scale. -/
theorem c17_parabolic_gain_jacobian_ratio (d : ℕ) (p R : ℝ)
    (hd : 0 < (d : ℝ)) (hp : 0 < p) (hR : 0 < R) :
    (Real.rpow ((R ^ (d+2))⁻¹) (1 / (p * (((d : ℝ)+2)/d))))⁻¹ *
      Real.rpow ((R ^ (d+2))⁻¹) (1/p) = Real.rpow R (-(2/p)) := by
  rw [c17_parabolic_jacobian_rpow d _ R hR,
    c17_parabolic_jacobian_rpow d p R hR]
  change (R ^ (-((d+2 : ℕ) : ℝ) / (p * (((d : ℝ)+2)/d))) : ℝ)⁻¹ *
    R ^ (-((d+2 : ℕ) : ℝ) / p : ℝ) = R ^ (-(2/p) : ℝ)
  rw [← Real.rpow_neg hR.le, ← Real.rpow_add hR]
  congr 1
  push_cast
  have hd2 : (d : ℝ) + 2 ≠ 0 := by linarith
  field_simp [ne_of_gt hd, ne_of_gt hp, hd2]
  ring

/-- The parabolic gain Jacobian ratio, expressed in extended nonnegative reals. -/
theorem c17_parabolic_gain_ennreal_ratio (d : ℕ) (p R : ℝ)
    (hd : 0 < (d : ℝ)) (hp : 0 < p) (hR : 0 < R) :
    (ENNReal.ofReal ((R ^ (d+2))⁻¹) ^
      (1 / ENNReal.ofReal (p * (((d : ℝ)+2)/d))).toReal)⁻¹ *
      ENNReal.ofReal ((R ^ (d+2))⁻¹) ^ (1 / ENNReal.ofReal p).toReal =
      ENNReal.ofReal (Real.rpow R (-(2/p))) := by
  have hj : 0 < (R ^ (d+2))⁻¹ := by positivity
  have hq : 0 < p * (((d : ℝ)+2)/d) := by positivity
  simp only [ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofReal hp.le,
    ENNReal.toReal_ofReal hq.le]
  rw [ENNReal.ofReal_rpow_of_pos hj, ENNReal.ofReal_rpow_of_pos hj,
    ← ENNReal.ofReal_inv_of_pos (Real.rpow_pos_of_pos hj _),
    ← ENNReal.ofReal_mul (inv_nonneg.mpr (Real.rpow_nonneg hj.le _))]
  exact congrArg ENNReal.ofReal (c17_parabolic_gain_jacobian_ratio d p R hd hp hR)

/-- The temporal and spatial Jacobians combine into the parabolic Jacobian. -/
theorem c17_parabolic_jacobian_combine (d : ℕ) (R : ℝ) (hR : 0 < R) :
    ENNReal.ofReal |(R^2)⁻¹| *
      ENNReal.ofReal (|R ^ Module.finrank ℝ (Vec d)|⁻¹) =
      ENNReal.ofReal ((R ^ (d+2))⁻¹) := by
  rw [Module.finrank_fin_fun, abs_of_pos (inv_pos.mpr (pow_pos hR 2)),
    abs_of_pos (pow_pos hR d), ← ENNReal.ofReal_mul (by positivity),
    ← mul_inv, ← pow_add, Nat.add_comm 2 d]

/-- The inverse-power norm on the smaller cylinder under parabolic scaling. -/
theorem c17_small_cylinder_eLpNorm_rescale {d : ℕ} (y : Vec d) {R : ℝ}
    (hR : 0 < R) (p : ℝ≥0∞) (f : ℝ × Vec d → ℝ) :
    eLpNorm (f ∘ fun z : ℝ × Vec d => (R^2*z.1, y+R • z.2)) p
      (volume.restrict (Set.Ioo (-1/4:ℝ) (1/4) ×ˢ sourceBall (0 : Vec d) (1/2))) =
    (ENNReal.ofReal |(R^2)⁻¹| * ENNReal.ofReal (|R ^ Module.finrank ℝ (Vec d)|⁻¹)) ^
        (1 / p).toReal *
      eLpNorm f p (volume.restrict
        (Set.Ioo (-(R^2)/4) (R^2/4) ×ˢ sourceBall y (R/2))) := by
  have hemb : MeasurableEmbedding (fun z : ℝ × Vec d => (R^2*z.1, y+R • z.2)) := by
    exact ((Homeomorph.smulOfNeZero (R^2) (ne_of_gt (sq_pos_of_pos hR))).prodCongr
      ((Homeomorph.smulOfNeZero R hR.ne').trans (Homeomorph.addLeft y))).measurableEmbedding
  have hn : ENNReal.ofReal |(R^2)⁻¹| *
      ENNReal.ofReal (|R ^ Module.finrank ℝ (Vec d)|⁻¹) ≠ 0 := by
    apply mul_ne_zero <;> apply ENNReal.ofReal_ne_zero_iff.mpr <;> positivity
  have hm := hemb.eLpNorm_map_measure (g := f) (p := p)
    (μ := volume.restrict (Set.Ioo (-1/4:ℝ) (1/4) ×ˢ sourceBall (0 : Vec d) (1/2)))
  rw [c17_parabolic_small_cylinder_map y hR, eLpNorm_smul_measure_of_ne_zero hn] at hm
  simpa only [smul_eq_mul] using hm.symm

/-- Parabolic scaling of an Lp norm on any measurable physical region. -/
theorem c17_parabolic_eLpNorm_preimage {d : ℕ} (y : Vec d) {R : ℝ}
    (hR : 0 < R) (S : Set (ℝ × Vec d)) (hS : MeasurableSet S)
    (p : ℝ≥0∞) (f : ℝ × Vec d → ℝ) :
    let F : ℝ × Vec d → ℝ × Vec d := fun z => (R^2*z.1, y+R • z.2)
    let J : ℝ≥0∞ := ENNReal.ofReal |(R^2)⁻¹| *
      ENNReal.ofReal (|R ^ Module.finrank ℝ (Vec d)|⁻¹)
    eLpNorm (f ∘ F) p (volume.restrict (F ⁻¹' S)) =
      J ^ (1 / p).toReal * eLpNorm f p (volume.restrict S) := by
  dsimp only
  let F : ℝ × Vec d → ℝ × Vec d := fun z => (R^2*z.1, y+R • z.2)
  have hemb : MeasurableEmbedding F := by
    exact ((Homeomorph.smulOfNeZero (R^2) (ne_of_gt (sq_pos_of_pos hR))).prodCongr
      ((Homeomorph.smulOfNeZero R hR.ne').trans (Homeomorph.addLeft y))).measurableEmbedding
  have hm : Measure.map F volume =
      (ENNReal.ofReal |(R^2)⁻¹| * ENNReal.ofReal (|R ^ Module.finrank ℝ (Vec d)|⁻¹)) •
        (volume : Measure (ℝ × Vec d)) := by
    change Measure.map (Prod.map (fun t : ℝ => R^2*t) (fun x : Vec d => y+R • x)) volume = _
    rw [Measure.volume_eq_prod ℝ (Vec d), ← Measure.map_prod_map _ _
      (measurable_const_mul _) (c17_spatial_affine_embedding y hR).measurable,
      show (fun t : ℝ => R^2*t) = (fun t : ℝ => 0 + R^2*t) by ext; simp,
      c20_map_volume_affine_time 0 (R^2) (ne_of_gt (sq_pos_of_pos hR)),
      c17_spatial_affine_map_volume y hR, Measure.prod_smul_left, Measure.prod_smul_right,
      ← smul_smul, ← Measure.volume_eq_prod]
  have hn : ENNReal.ofReal |(R^2)⁻¹| *
      ENNReal.ofReal (|R ^ Module.finrank ℝ (Vec d)|⁻¹) ≠ 0 := by
    apply mul_ne_zero <;> apply ENNReal.ofReal_ne_zero_iff.mpr <;> positivity
  have hmap : Measure.map F (volume.restrict (F ⁻¹' S)) =
      (ENNReal.ofReal |(R^2)⁻¹| * ENNReal.ofReal (|R ^ Module.finrank ℝ (Vec d)|⁻¹)) •
        (volume.restrict S) := by
    rw [← Measure.restrict_map hemb.measurable hS, hm, Measure.restrict_smul]
  have hnorm := hemb.eLpNorm_map_measure (g := f) (p := p)
    (μ := volume.restrict (F ⁻¹' S))
  rw [hmap, eLpNorm_smul_measure_of_ne_zero hn] at hnorm
  simpa only [smul_eq_mul] using hnorm.symm

/-- A concentric parabolic cylinder pulls back to its unit-scale counterpart. -/
theorem c17_concentric_cylinder_preimage {d : ℕ} (y : Vec d) {R : ℝ}
    (hR : 0 < R) (r : ℝ) :
    (fun z : ℝ × Vec d => (R^2*z.1, y+R • z.2)) ⁻¹'
      (Set.Ioo (-(r^2)) (r^2) ×ˢ sourceBall y r) =
    Set.Ioo (-((r/R)^2)) ((r/R)^2) ×ˢ sourceBall (0 : Vec d) (r/R) := by
  ext ⟨t, x⟩
  simp only [Set.mem_preimage, Set.mem_prod, Set.mem_Ioo, sourceBall,
    Set.mem_ofPred_eq, add_sub_cancel_left, sub_zero,
    TimeChange.euclideanNorm_smul, abs_of_pos hR]
  have hR2 : 0 < R^2 := sq_pos_of_pos hR
  have ht₁ : -(r^2) < R^2*t ↔ -((r/R)^2) < t := by
    rw [div_pow, ← neg_div, div_lt_iff₀ hR2]
    constructor <;> intro h <;> nlinarith
  have ht₂ : R^2*t < r^2 ↔ t < (r/R)^2 := by
    rw [div_pow, lt_div_iff₀ hR2]
    constructor <;> intro h <;> nlinarith
  have hx : R * euclideanNorm x < r ↔ euclideanNorm x < r/R := by
    rw [lt_div_iff₀ hR]
    exact mul_comm R (euclideanNorm x) ▸ Iff.rfl
  exact and_congr (and_congr ht₁ ht₂) hx

/-- A supplied unit-scale inverse-norm gain transfers to physical regions with
    the exact ratio of parabolic Jacobian factors. -/
theorem c17_inverse_gain_transfer_of_unit {d : ℕ} (y : Vec d) {R : ℝ}
    (hR : 0 < R) (S T : Set (ℝ × Vec d)) (hS : MeasurableSet S)
    (hT : MeasurableSet T) (p q K : ℝ≥0∞) (u : ℝ × Vec d → ℝ) :
    let F : ℝ × Vec d → ℝ × Vec d := fun z => (R^2*z.1, y+R • z.2)
    let J : ℝ≥0∞ := ENNReal.ofReal |(R^2)⁻¹| *
      ENNReal.ofReal (|R ^ Module.finrank ℝ (Vec d)|⁻¹)
    eLpNorm ((fun z => (u z)⁻¹) ∘ F) q (volume.restrict (F ⁻¹' S)) ≤
      K * eLpNorm ((fun z => (u z)⁻¹) ∘ F) p (volume.restrict (F ⁻¹' T)) →
    eLpNorm (fun z => (u z)⁻¹) q (volume.restrict S) ≤
      ((J ^ (1/q).toReal)⁻¹ * (K * J ^ (1/p).toReal)) *
        eLpNorm (fun z => (u z)⁻¹) p (volume.restrict T) := by
  dsimp only
  intro hunit
  let J : ℝ≥0∞ := ENNReal.ofReal |(R^2)⁻¹| *
    ENNReal.ofReal (|R ^ Module.finrank ℝ (Vec d)|⁻¹)
  have hJ0 : J ≠ 0 := by
    dsimp [J]
    apply mul_ne_zero <;> apply ENNReal.ofReal_ne_zero_iff.mpr <;> positivity
  have hJtop : J ≠ ⊤ := by
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  have hq0 : J ^ (1/q).toReal ≠ 0 := (ENNReal.rpow_pos (pos_iff_ne_zero.mpr hJ0) hJtop).ne'
  have hqtop : J ^ (1/q).toReal ≠ ⊤ := ENNReal.rpow_ne_top_of_ne_zero hJ0 hJtop
  rw [c17_parabolic_eLpNorm_preimage y hR S hS,
    c17_parabolic_eLpNorm_preimage y hR T hT] at hunit
  change J ^ (1/q).toReal * eLpNorm (fun z => (u z)⁻¹) q (volume.restrict S) ≤
    K * (J ^ (1/p).toReal * eLpNorm (fun z => (u z)⁻¹) p (volume.restrict T)) at hunit
  have h := mul_le_mul' (le_refl ((J ^ (1/q).toReal)⁻¹)) hunit
  rw [← mul_assoc, ENNReal.inv_mul_cancel hq0 hqtop, one_mul] at h
  simpa only [mul_assoc] using h

/-- A full supplied unit-cylinder gain yields the corresponding concentric
    physical-cylinder gain, with the exact change-of-variables coefficient. -/
theorem c17_inverse_gain_concentric_of_unit {d : ℕ} (y : Vec d) {r R : ℝ}
    (hR : 0 < R) (p q K : ℝ≥0∞) (u : ℝ × Vec d → ℝ) :
    let F : ℝ × Vec d → ℝ × Vec d := fun z => (R^2*z.1, y+R • z.2)
    let J : ℝ≥0∞ := ENNReal.ofReal |(R^2)⁻¹| *
      ENNReal.ofReal (|R ^ Module.finrank ℝ (Vec d)|⁻¹)
    eLpNorm ((fun z => (u z)⁻¹) ∘ F) q (volume.restrict
      (Set.Ioo (-((r/R)^2)) ((r/R)^2) ×ˢ sourceBall (0 : Vec d) (r/R))) ≤
      K * eLpNorm ((fun z => (u z)⁻¹) ∘ F) p (volume.restrict
        (Set.Ioo (-1) 1 ×ˢ sourceBall (0 : Vec d) 1)) →
    eLpNorm (fun z => (u z)⁻¹) q (volume.restrict
      (Set.Ioo (-(r^2)) (r^2) ×ˢ sourceBall y r)) ≤
      ((J ^ (1/q).toReal)⁻¹ * (K * J ^ (1/p).toReal)) *
        eLpNorm (fun z => (u z)⁻¹) p (volume.restrict
          (Set.Ioo (-(R^2)) (R^2) ×ˢ sourceBall y R)) := by
  dsimp only
  intro hunit
  have h := c17_inverse_gain_transfer_of_unit y hR
    (Set.Ioo (-(r^2)) (r^2) ×ˢ sourceBall y r)
    (Set.Ioo (-(R^2)) (R^2) ×ˢ sourceBall y R)
    (measurableSet_Ioo.prod (c17_isOpen_sourceBall y r).measurableSet)
    (measurableSet_Ioo.prod (c17_isOpen_sourceBall y R).measurableSet) p q K u
  apply h
  rw [c17_concentric_cylinder_preimage y hR r,
    c17_concentric_cylinder_preimage y hR R]
  simpa [div_self hR.ne'] using hunit

/-- The full unit gain implies the physical inverse gain with radius loss
    `(R-r)^(-2/p)`. -/
theorem c17_inverse_gain_concentric_radius {d : ℕ} (y : Vec d) {r R p C : ℝ}
    (hd : 0 < (d : ℝ)) (hp : 0 < p) (hR : 0 < R) (hrR : r < R)
    (hC : 0 ≤ C) (u : ℝ × Vec d → ℝ) :
    let F : ℝ × Vec d → ℝ × Vec d := fun z => (R^2*z.1, y+R • z.2)
    let q : ℝ := p * (((d : ℝ)+2)/d)
    eLpNorm ((fun z => (u z)⁻¹) ∘ F) (ENNReal.ofReal q) (volume.restrict
      (Set.Ioo (-((r/R)^2)) ((r/R)^2) ×ˢ sourceBall (0 : Vec d) (r/R))) ≤
      (ENNReal.ofReal C * ENNReal.ofReal (Real.rpow (1-r/R) (-(2/p)))) *
        eLpNorm ((fun z => (u z)⁻¹) ∘ F) (ENNReal.ofReal p) (volume.restrict
          (Set.Ioo (-1) 1 ×ˢ sourceBall (0 : Vec d) 1)) →
    eLpNorm (fun z => (u z)⁻¹) (ENNReal.ofReal q) (volume.restrict
      (Set.Ioo (-(r^2)) (r^2) ×ˢ sourceBall y r)) ≤
      ENNReal.ofReal (C * Real.rpow (R-r) (-(2/p))) *
        eLpNorm (fun z => (u z)⁻¹) (ENNReal.ofReal p) (volume.restrict
          (Set.Ioo (-(R^2)) (R^2) ×ˢ sourceBall y R)) := by
  dsimp only
  intro hunit
  have h := c17_inverse_gain_concentric_of_unit y hR (ENNReal.ofReal p)
    (ENNReal.ofReal (p * (((d : ℝ)+2)/d)))
    (ENNReal.ofReal C * ENNReal.ofReal (Real.rpow (1-r/R) (-(2/p)))) u hunit
  rw [c17_parabolic_jacobian_combine d R hR] at h
  have hcoef :
      (ENNReal.ofReal ((R ^ (d+2))⁻¹) ^
          (1 / ENNReal.ofReal (p * (((d : ℝ)+2)/d))).toReal)⁻¹ *
        ((ENNReal.ofReal C * ENNReal.ofReal (Real.rpow (1-r/R) (-(2/p)))) *
          ENNReal.ofReal ((R ^ (d+2))⁻¹) ^ (1 / ENNReal.ofReal p).toReal) =
      ENNReal.ofReal (C * Real.rpow (R-r) (-(2/p))) := by
    calc
      _ = ((ENNReal.ofReal ((R ^ (d+2))⁻¹) ^
            (1 / ENNReal.ofReal (p * (((d : ℝ)+2)/d))).toReal)⁻¹ *
          ENNReal.ofReal ((R ^ (d+2))⁻¹) ^ (1 / ENNReal.ofReal p).toReal) *
          (ENNReal.ofReal C * ENNReal.ofReal (Real.rpow (1-r/R) (-(2/p)))) := by ac_rfl
      _ = ENNReal.ofReal (Real.rpow R (-(2/p))) *
          (ENNReal.ofReal C * ENNReal.ofReal (Real.rpow (1-r/R) (-(2/p)))) := by
            rw [c17_parabolic_gain_ennreal_ratio d p R hd hp hR]
      _ = ENNReal.ofReal C * (ENNReal.ofReal (Real.rpow R (-(2/p))) *
          ENNReal.ofReal (Real.rpow (1-r/R) (-(2/p)))) := by ac_rfl
      _ = ENNReal.ofReal (C * Real.rpow (R-r) (-(2/p))) := by
        change ENNReal.ofReal C * (ENNReal.ofReal (R ^ (-(2/p) : ℝ)) *
          ENNReal.ofReal ((1-r/R) ^ (-(2/p) : ℝ))) = _
        rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hR.le _)]
        change ENNReal.ofReal C * ENNReal.ofReal
          (Real.rpow R (-(2/p)) * Real.rpow (1-r/R) (-(2/p))) = _
        rw [← c17_inverse_gain_radius_factor_rescale p r R hR hrR,
          ← ENNReal.ofReal_mul hC]
  rw [hcoef] at h
  exact h

end EinsteinFull.Calculus
