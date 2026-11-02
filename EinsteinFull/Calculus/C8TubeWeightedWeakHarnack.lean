import EinsteinFull.Calculus.C13TubeSmallPowerSobolev
import EinsteinFull.Calculus.C13TubeActualSmallPowerSobolev
import EinsteinFull.Calculus.C13TubeSmallPowerTimeBalance
import EinsteinFull.Calculus.C8TubeWeightedParabolicPoincare
import EinsteinFull.Calculus.C8TubeWeakHarnackEpsilon
import EinsteinFull.Calculus.C9TubeHarnackEpsilonRemoval
import EinsteinFull.Calculus.C11TubeWeightedZeroPastRepresentative
import EinsteinFull.Calculus.C16TubeWeightedLogEnergy
import EllipticRegularity.Parabolic.WeakHarnack.AssemblyNeg
import EllipticRegularity.Parabolic.WeakHarnack.MeasuresConvert

open EinsteinRelation MeasureTheory Filter EinsteinFull.External.Source.GMP
open scoped Topology ENNReal

namespace EinsteinFull.Calculus

/-- Positive shifts retain the actual weighted equation and gradient. -/
@[nolint unusedArguments]
theorem c8_weighted_caloric_positive_shift {d : ℕ} {κ : ℝ} (hκ : 0 < κ)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (hell : IsUniformlyElliptic κ ρ α)
    {u : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    (hu : IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1) u G)
    (hu0 : ∀ᵐ z ∂volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1), 0 ≤ u z)
    {ε : ℝ} (hε : 0 < ε) :
    IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1) (fun z => u z + ε) G ∧
    (∀ᵐ z ∂volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1), ε ≤ u z + ε) := by
  let I := Set.Ioo (-1 : ℝ) 1
  let U := sourceBall (0 : Vec d) 1
  haveI : IsFiniteMeasure (volume.restrict I) := isFiniteMeasure_restrict.mpr (by simp [I])
  haveI : IsFiniteMeasure (volume.restrict U) := isFiniteMeasure_restrict.mpr (by
    dsimp [U]; rw [c8_sourceBall_eq_euclideanBall 0 (by norm_num)]
    exact PDE.volume_euclideanBall_ne_top 0 (by norm_num))
  have hprod : volume.restrict (I ×ˢ U) = (volume.restrict I).prod (volume.restrict U) := by
    rw [Measure.volume_eq_prod, Measure.prod_restrict]
  haveI : IsFiniteMeasure (volume.restrict (I ×ˢ U)) := by rw [hprod]; infer_instance
  have hfinite : volume (I ×ˢ U) ≠ ⊤ := by
    simpa only [Measure.restrict_apply_univ] using
      (measure_ne_top (volume.restrict (I ×ˢ U)) Set.univ)
  constructor
  · simpa only [sub_neg_eq_add] using c11_weighted_caloric_sub_const hκ hell hfinite hu (-ε)
  · filter_upwards [hu0] with z hz
    linarith

/-- The logarithmic test's squared cutoff has uniformly positive density mass. -/
theorem c8_squared_cutoff_density_mass {d : ℕ} {κ : ℝ} (hκ : 0 < κ)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (hell : IsUniformlyElliptic κ ρ α) :
    κ * (volume (PDE.euclideanBall (0 : Vec d) (3 / 4))).toReal ≤
      ∫ x in sourceBall (0 : Vec d) 1,
        ρ x * PDE.Parabolic.WeakHarnack.radialCutoff d x ^ 2 := by
  let B := sourceBall (0 : Vec d) 1
  let A := PDE.euclideanBall (0 : Vec d) (3 / 4)
  let χ := PDE.Parabolic.WeakHarnack.radialCutoff d
  have hAB : A ⊆ B := by
    dsimp [A, B]
    rw [c8_sourceBall_eq_euclideanBall 0 (by norm_num)]
    exact PDE.euclideanBall_mono (by norm_num) (by norm_num)
  haveI : IsFiniteMeasure (volume.restrict B) := by
    apply isFiniteMeasure_restrict.mpr
    dsimp [B]
    rw [c8_sourceBall_eq_euclideanBall 0 (by norm_num)]
    exact PDE.volume_euclideanBall_ne_top 0 (by norm_num)
  have hpoint (x : Vec d) : 0 ≤ ρ x * χ x ^ 2 ∧ ρ x * χ x ^ 2 ≤ κ⁻¹ := by
    have hρ := hell.2.2 x
    have hχ := (c8_radial_cutoff_properties d).2.2.2.1 x
    have hχ2 : χ x ^ 2 ≤ 1 := by nlinarith
    constructor
    · exact mul_nonneg (hκ.le.trans hρ.1) (sq_nonneg _)
    · calc
        ρ x * χ x ^ 2 ≤ ρ x * 1 := mul_le_mul_of_nonneg_left hχ2 (hκ.le.trans hρ.1)
        _ ≤ κ⁻¹ := by simpa using hρ.2.1
  have hi : IntegrableOn (fun x => ρ x * χ x ^ 2) B := by
    apply (integrable_const κ⁻¹).mono'
      ((hell.1.mul ((c8_radial_cutoff_properties d).1.continuous.measurable.pow_const 2)).aestronglyMeasurable)
    filter_upwards [] with x
    change |ρ x * χ x ^ 2| ≤ κ⁻¹
    rw [abs_of_nonneg (hpoint x).1]
    exact (hpoint x).2
  haveI : IsFiniteMeasure (volume.restrict A) := by
    apply isFiniteMeasure_restrict.mpr
    exact PDE.volume_euclideanBall_ne_top 0 (by norm_num)
  have hsmall : κ * (volume A).toReal ≤ ∫ x in A, ρ x * χ x ^ 2 := by
    have hm : (∫ _x in A, κ) ≤ ∫ x in A, ρ x * χ x ^ 2 := by
      apply setIntegral_mono_on (integrable_const κ) (hi.mono_set hAB)
        (PDE.isOpen_euclideanBall 0 (3 / 4)).measurableSet
      intro x hx
      have hχ : χ x = 1 := (c8_radial_cutoff_properties d).2.2.2.2.1 x hx
      simpa [hχ] using (hell.2.2 x).1
    simpa [setIntegral_const, smul_eq_mul, Measure.real, mul_comm] using hm
  calc
    κ * (volume A).toReal ≤ ∫ x in A, ρ x * χ x ^ 2 := hsmall
    _ ≤ ∫ x in B, ρ x * χ x ^ 2 :=
      setIntegral_mono_set hi (ae_of_all _ fun x => (hpoint x).1)
        (ae_of_all _ fun x hx => hAB hx)

/-- The density-weighted squared cutoff therefore has positive total mass. -/
theorem c8_squared_cutoff_density_mass_pos {d : ℕ} {κ : ℝ} (hκ : 0 < κ)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (hell : IsUniformlyElliptic κ ρ α) :
    0 < ∫ x in sourceBall (0 : Vec d) 1,
      ρ x * PDE.Parabolic.WeakHarnack.radialCutoff d x ^ 2 :=
  lt_of_lt_of_le (mul_pos hκ (PDE.volume_euclideanBall_toReal_pos 0 (by norm_num)))
    (c8_squared_cutoff_density_mass hκ hell)

/-- Total mass of the density-weighted logarithmic cutoff. -/
noncomputable def c8LogCutoffMass {d : ℕ} (ρ : Vec d → ℝ) : ℝ≥0∞ :=
  ∫⁻ x in sourceBall (0 : Vec d) 1,
    ENNReal.ofReal (ρ x * PDE.Parabolic.WeakHarnack.radialCutoff d x ^ 2)

/-- The normalized density-weighted cutoff measure used for logarithmic tails. -/
noncomputable def c8LogCutoffMeasure {d : ℕ} (ρ : Vec d → ℝ) : Measure (Vec d) :=
  (c8LogCutoffMass ρ)⁻¹ • (volume.restrict (sourceBall 0 1)).withDensity
    (fun x => ENNReal.ofReal (ρ x * PDE.Parabolic.WeakHarnack.radialCutoff d x ^ 2))

/-- The logarithmic cutoff mass is the extended-real image of its real integral. -/
theorem c8_log_cutoff_mass_eq {d : ℕ} {κ : ℝ} (hκ : 0 < κ)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (hell : IsUniformlyElliptic κ ρ α) :
    c8LogCutoffMass ρ = ENNReal.ofReal
      (∫ x in sourceBall (0 : Vec d) 1,
        ρ x * PDE.Parabolic.WeakHarnack.radialCutoff d x ^ 2) := by
  let B := sourceBall (0 : Vec d) 1
  let χ := PDE.Parabolic.WeakHarnack.radialCutoff d
  haveI : IsFiniteMeasure (volume.restrict B) := by
    apply isFiniteMeasure_restrict.mpr
    dsimp [B]
    rw [c8_sourceBall_eq_euclideanBall 0 (by norm_num)]
    exact PDE.volume_euclideanBall_ne_top 0 (by norm_num)
  have hp (x : Vec d) : 0 ≤ ρ x * χ x ^ 2 ∧ ρ x * χ x ^ 2 ≤ κ⁻¹ := by
    have hρ := hell.2.2 x
    have hχ := (c8_radial_cutoff_properties d).2.2.2.1 x
    have hχ2 : χ x ^ 2 ≤ 1 := by nlinarith
    exact ⟨mul_nonneg (hκ.le.trans hρ.1) (sq_nonneg _),
      (mul_le_mul_of_nonneg_left hχ2 (hκ.le.trans hρ.1)).trans (by simpa using hρ.2.1)⟩
  have hi : IntegrableOn (fun x => ρ x * χ x ^ 2) B := by
    apply (integrable_const κ⁻¹).mono'
      ((hell.1.mul ((c8_radial_cutoff_properties d).1.continuous.measurable.pow_const 2)).aestronglyMeasurable)
    exact ae_of_all _ (fun x => by
      change |ρ x * χ x ^ 2| ≤ κ⁻¹
      rw [abs_of_nonneg (hp x).1]
      exact (hp x).2)
  exact (ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun x => (hp x).1)).symm

/-- Uniform ellipticity makes the normalized logarithmic cutoff a probability measure. -/
theorem c8_log_cutoff_isProbabilityMeasure {d : ℕ} {κ : ℝ} (hκ : 0 < κ)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (hell : IsUniformlyElliptic κ ρ α) :
    IsProbabilityMeasure (c8LogCutoffMeasure ρ) := by
  have hmass : c8LogCutoffMass ρ ≠ 0 := by
    rw [c8_log_cutoff_mass_eq hκ hell]
    exact (ENNReal.ofReal_pos.mpr (c8_squared_cutoff_density_mass_pos hκ hell)).ne'
  have htop : c8LogCutoffMass ρ ≠ ⊤ := by
    rw [c8_log_cutoff_mass_eq hκ hell]
    exact ENNReal.ofReal_ne_top
  constructor
  rw [c8LogCutoffMeasure, Measure.smul_apply, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ]
  exact ENNReal.inv_mul_cancel hmass htop |>.trans rfl

/-- Integration against the logarithmic cutoff measure is the normalized weighted integral. -/
theorem c8_integral_log_cutoff_measure {d : ℕ} {κ : ℝ} (hκ : 0 < κ)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (hell : IsUniformlyElliptic κ ρ α)
    (f : Vec d → ℝ) :
    ∫ x, f x ∂(c8LogCutoffMeasure ρ) =
      (∫ x in sourceBall (0 : Vec d) 1,
        ρ x * PDE.Parabolic.WeakHarnack.radialCutoff d x ^ 2)⁻¹ *
      ∫ x in sourceBall (0 : Vec d) 1,
        (ρ x * PDE.Parabolic.WeakHarnack.radialCutoff d x ^ 2) * f x := by
  have hm : Measurable fun x => ENNReal.ofReal
      (ρ x * PDE.Parabolic.WeakHarnack.radialCutoff d x ^ 2) :=
    ENNReal.measurable_ofReal.comp
      (hell.1.mul ((c8_radial_cutoff_properties d).1.continuous.measurable.pow_const 2))
  have h := integral_withDensity_eq_integral_toReal_smul (μ := volume.restrict
    (sourceBall (0 : Vec d) 1)) hm
    (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top) f
  unfold c8LogCutoffMeasure
  rw [integral_smul_measure (G := ℝ), h, c8_log_cutoff_mass_eq hκ hell,
    ENNReal.toReal_inv, ENNReal.toReal_ofReal (c8_squared_cutoff_density_mass_pos hκ hell).le,
    smul_eq_mul]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [smul_eq_mul]
  rw [ENNReal.toReal_ofReal (mul_nonneg (hκ.le.trans (hell.2.2 x).1) (sq_nonneg _))]

/-- Uniform ellipticity bounds the logarithmic measure by restricted volume. -/
theorem c8_log_cutoff_measure_le {d : ℕ} {κ : ℝ} (hκ : 0 < κ)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (hell : IsUniformlyElliptic κ ρ α) :
    c8LogCutoffMeasure ρ ≤
      ((c8LogCutoffMass ρ)⁻¹ * ENNReal.ofReal κ⁻¹) •
        volume.restrict (sourceBall 0 1) := by
  have hle : (volume.restrict (sourceBall (0 : Vec d) 1)).withDensity
      (fun x => ENNReal.ofReal
        (ρ x * PDE.Parabolic.WeakHarnack.radialCutoff d x ^ 2)) ≤
      ENNReal.ofReal κ⁻¹ • volume.restrict (sourceBall 0 1) := by
    refine Measure.le_iff.2 fun s hs => ?_
    rw [withDensity_apply _ hs]
    refine (lintegral_mono (g := fun _ => ENNReal.ofReal κ⁻¹) fun x => ?_).trans_eq ?_
    · have hρ := hell.2.2 x
      have hχ := (c8_radial_cutoff_properties d).2.2.2.1 x
      have hχ2 : PDE.Parabolic.WeakHarnack.radialCutoff d x ^ 2 ≤ 1 := by nlinarith
      apply ENNReal.ofReal_le_ofReal
      calc
        ρ x * PDE.Parabolic.WeakHarnack.radialCutoff d x ^ 2 ≤ ρ x * 1 :=
          mul_le_mul_of_nonneg_left hχ2 (hκ.le.trans hρ.1)
        _ ≤ κ⁻¹ := by simpa using hρ.2.1
    · rw [lintegral_const, Measure.smul_apply, smul_eq_mul, Measure.restrict_apply_univ]
  unfold c8LogCutoffMeasure
  intro s
  simp only [Measure.smul_apply, smul_eq_mul]
  calc
    _ ≤ (c8LogCutoffMass ρ)⁻¹ *
        ((ENNReal.ofReal κ⁻¹ • volume.restrict (sourceBall 0 1)) s) :=
      mul_le_mul' le_rfl (hle s)
    _ = _ := by simp only [Measure.smul_apply, smul_eq_mul, mul_assoc]

/-- Spatial L² functions remain L² for the logarithmic cutoff measure. -/
theorem c8_memLp_log_cutoff_measure {d : ℕ} {κ : ℝ} (hκ : 0 < κ)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (hell : IsUniformlyElliptic κ ρ α)
    {f : Vec d → ℝ} (hf : MemLp f 2 (volume.restrict (sourceBall 0 1))) :
    MemLp f 2 (c8LogCutoffMeasure ρ) := by
  apply hf.of_measure_le_smul ?_ (c8_log_cutoff_measure_le hκ hell)
  rw [c8_log_cutoff_mass_eq hκ hell]
  exact (ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr
    (ENNReal.ofReal_pos.mpr (c8_squared_cutoff_density_mass_pos hκ hell)).ne')
    ENNReal.ofReal_ne_top)

/-- The actual density-weighted mean minimizes the cutoff variance. -/
theorem c8_log_cutoff_variance_le {d : ℕ} {κ : ℝ} (hκ : 0 < κ)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (hell : IsUniformlyElliptic κ ρ α)
    {f : Vec d → ℝ} (hf : MemLp f 2 (volume.restrict (sourceBall 0 1))) (a : ℝ) :
    (∫ x, (f x - ∫ y, f y ∂(c8LogCutoffMeasure ρ)) ^ 2 ∂(c8LogCutoffMeasure ρ)) ≤
      ∫ x, (f x - a) ^ 2 ∂(c8LogCutoffMeasure ρ) := by
  letI : IsProbabilityMeasure (c8LogCutoffMeasure ρ) :=
    c8_log_cutoff_isProbabilityMeasure hκ hell
  have h := c8_integral_sq_sub_mean_le (c8LogCutoffMeasure ρ) (by simp)
    (c8_memLp_log_cutoff_measure hκ hell hf) a
  simpa using h

/-- Ellipticity compares the actual cutoff variance to the unweighted cutoff energy. -/
theorem c8_log_cutoff_variance_comparison {d : ℕ} {κ : ℝ} (hκ : 0 < κ)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (hell : IsUniformlyElliptic κ ρ α)
    {f : Vec d → ℝ} (hf : MemLp f 2 (volume.restrict (sourceBall 0 1))) (a : ℝ) :
    (∫ x, (f x - ∫ y, f y ∂(c8LogCutoffMeasure ρ)) ^ 2 ∂(c8LogCutoffMeasure ρ)) ≤
      (∫ x in sourceBall (0 : Vec d) 1,
        ρ x * PDE.Parabolic.WeakHarnack.radialCutoff d x ^ 2)⁻¹ * κ⁻¹ *
      ∫ x in sourceBall (0 : Vec d) 1,
        PDE.Parabolic.WeakHarnack.radialCutoff d x ^ 2 * (f x - a) ^ 2 := by
  let B := sourceBall (0 : Vec d) 1
  let χ := PDE.Parabolic.WeakHarnack.radialCutoff d
  haveI : IsFiniteMeasure (volume.restrict B) := isFiniteMeasure_restrict.mpr (by
    dsimp [B]; rw [c8_sourceBall_eq_euclideanBall 0 (by norm_num)]
    exact PDE.volume_euclideanBall_ne_top 0 (by norm_num))
  have hsq : Integrable (fun x => (f x - a) ^ 2) (volume.restrict B) :=
    (hf.sub (memLp_const a)).integrable_sq
  have hχ (x : Vec d) : 0 ≤ χ x ^ 2 ∧ χ x ^ 2 ≤ 1 := by
    have h := (c8_radial_cutoff_properties d).2.2.2.1 x
    constructor <;> nlinarith [sq_nonneg (χ x)]
  have hcut : Integrable (fun x => χ x ^ 2 * (f x - a) ^ 2) (volume.restrict B) := by
    apply hsq.mono' (((c8_radial_cutoff_properties d).1.continuous.measurable.pow_const 2).aestronglyMeasurable.mul hsq.aestronglyMeasurable)
    exact ae_of_all _ fun x => by
      change |χ x ^ 2 * (f x - a) ^ 2| ≤ (f x - a) ^ 2
      rw [abs_of_nonneg (mul_nonneg (hχ x).1 (sq_nonneg _))]
      nlinarith [mul_le_mul_of_nonneg_right (hχ x).2 (sq_nonneg (f x - a))]
  have hweight : Integrable (fun x => (ρ x * χ x ^ 2) * (f x - a) ^ 2)
      (volume.restrict B) := by
    apply (hcut.const_mul κ⁻¹).mono'
      ((hell.1.mul ((c8_radial_cutoff_properties d).1.continuous.measurable.pow_const 2)).aestronglyMeasurable.mul hsq.aestronglyMeasurable)
    exact ae_of_all _ fun x => by
      have hρ := hell.2.2 x
      have hnonneg : 0 ≤ (ρ x * χ x ^ 2) * (f x - a) ^ 2 :=
        mul_nonneg (mul_nonneg (hκ.le.trans hρ.1) (hχ x).1) (sq_nonneg _)
      change |(ρ x * χ x ^ 2) * (f x - a) ^ 2| ≤ κ⁻¹ * (χ x ^ 2 * (f x - a) ^ 2)
      rw [abs_of_nonneg hnonneg]
      nlinarith [mul_le_mul_of_nonneg_right hρ.2.1
        (mul_nonneg (hχ x).1 (sq_nonneg (f x - a)))]
  have hcomp : (∫ x in B, (ρ x * χ x ^ 2) * (f x - a) ^ 2) ≤
      κ⁻¹ * ∫ x in B, χ x ^ 2 * (f x - a) ^ 2 := by
    rw [← integral_const_mul]
    apply integral_mono_ae hweight (hcut.const_mul κ⁻¹)
    exact ae_of_all _ fun x => by
      have hρ := (hell.2.2 x).2.1
      nlinarith [mul_le_mul_of_nonneg_right hρ
        (mul_nonneg (hχ x).1 (sq_nonneg (f x - a)))]
  calc
    _ ≤ ∫ x, (f x - a) ^ 2 ∂(c8LogCutoffMeasure ρ) :=
      c8_log_cutoff_variance_le hκ hell hf a
    _ = (∫ x in B, ρ x * χ x ^ 2)⁻¹ *
        ∫ x in B, (ρ x * χ x ^ 2) * (f x - a) ^ 2 :=
      c8_integral_log_cutoff_measure hκ hell _
    _ ≤ (∫ x in B, ρ x * χ x ^ 2)⁻¹ *
        (κ⁻¹ * ∫ x in B, χ x ^ 2 * (f x - a) ^ 2) :=
      mul_le_mul_of_nonneg_left hcomp (inv_nonneg.mpr (c8_squared_cutoff_density_mass_pos hκ hell).le)
    _ = _ := by ring

/-- The native density-weighted logarithmic variance is controlled by cutoff gradient energy. -/
theorem c8_log_cutoff_poincare {d : ℕ} {κ : ℝ} (hκ : 0 < κ)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (hell : IsUniformlyElliptic κ ρ α)
    (u : PDE.H1Function (sourceBall (0 : Vec d) 1)) :
    (∫ x, (u x - ∫ y, u y ∂(c8LogCutoffMeasure ρ)) ^ 2 ∂(c8LogCutoffMeasure ρ)) ≤
      ((∫ x in sourceBall (0 : Vec d) 1,
        ρ x * PDE.Parabolic.WeakHarnack.radialCutoff d x ^ 2)⁻¹ * κ⁻¹ *
          PDE.Parabolic.WeakHarnack.weightedPoincareConst d) *
      ∫ x in sourceBall (0 : Vec d) 1,
        PDE.vecNormSq (u.grad x) * PDE.Parabolic.WeakHarnack.radialCutoff d x ^ 2 := by
  let B := sourceBall (0 : Vec d) 1
  let χ := PDE.Parabolic.WeakHarnack.radialCutoff d
  let a := (∫ y in B, u y * χ y ^ 2) / ∫ y in B, χ y ^ 2
  have hb : PDE.euclideanBall (0 : Vec d) 1 = B := by
    dsimp [B]; exact (c8_sourceBall_eq_euclideanBall 0 (by norm_num)).symm
  have hP := PDE.Parabolic.WeakHarnack.weightedPoincare_radialCutoff
    (by rw [hb]) u
  rw [hb] at hP
  change (∫ x in B, (u x - a) ^ 2 * χ x ^ 2) ≤
    PDE.Parabolic.WeakHarnack.weightedPoincareConst d *
      ∫ x in B, PDE.vecNormSq (u.grad x) * χ x ^ 2 at hP
  have hcomp := c8_log_cutoff_variance_comparison hκ hell u.memL2 a
  have hnonneg : 0 ≤ (∫ x in B, ρ x * χ x ^ 2)⁻¹ * κ⁻¹ :=
    mul_nonneg (inv_nonneg.mpr (c8_squared_cutoff_density_mass_pos hκ hell).le)
      (inv_nonneg.mpr hκ.le)
  have hp' := mul_le_mul_of_nonneg_left hP hnonneg
  have hswap : (∫ x in B, χ x ^ 2 * (u x - a) ^ 2) =
      ∫ x in B, (u x - a) ^ 2 * χ x ^ 2 := by
    apply integral_congr_ae
    exact ae_of_all _ fun x => mul_comm _ _
  rw [hswap] at hcomp
  exact hcomp.trans (by simpa only [mul_assoc] using hp')

/-- The logarithmic cutoff Poincaré constant is uniform over elliptic coefficients. -/
theorem c8_log_cutoff_poincare_uniform (d : ℕ) {κ : ℝ} (hκ : 0 < κ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
      IsUniformlyElliptic κ ρ α → ∀ u : PDE.H1Function (sourceBall 0 1),
      (∫ x, (u x - ∫ y, u y ∂(c8LogCutoffMeasure ρ)) ^ 2 ∂(c8LogCutoffMeasure ρ)) ≤
        C * ∫ x in sourceBall (0 : Vec d) 1,
          PDE.vecNormSq (u.grad x) * PDE.Parabolic.WeakHarnack.radialCutoff d x ^ 2 := by
  let V := (volume (PDE.euclideanBall (0 : Vec d) (3 / 4))).toReal
  have hV : 0 < V := PDE.volume_euclideanBall_toReal_pos 0 (by norm_num)
  have hP := PDE.Parabolic.WeakHarnack.weightedPoincareConst_pos d
  refine ⟨(κ * V)⁻¹ * κ⁻¹ * PDE.Parabolic.WeakHarnack.weightedPoincareConst d,
    by positivity, ?_⟩
  intro ρ α hell u
  have hmass := c8_squared_cutoff_density_mass hκ hell
  have hmasspos := c8_squared_cutoff_density_mass_pos hκ hell
  have hinv : (∫ x in sourceBall (0 : Vec d) 1,
      ρ x * PDE.Parabolic.WeakHarnack.radialCutoff d x ^ 2)⁻¹ ≤ (κ * V)⁻¹ :=
    (inv_le_inv₀ hmasspos (mul_pos hκ hV)).2 hmass
  have hE : 0 ≤ ∫ x in sourceBall (0 : Vec d) 1,
      PDE.vecNormSq (u.grad x) * PDE.Parabolic.WeakHarnack.radialCutoff d x ^ 2 :=
    integral_nonneg fun x => mul_nonneg (PDE.vecNormSq_nonneg _) (sq_nonneg _)
  have hcoeff := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hinv (inv_nonneg.mpr hκ.le)) hP.le
  exact (c8_log_cutoff_poincare hκ hell u).trans
    (mul_le_mul_of_nonneg_right hcoeff hE)

/-- Inner-ball volume is controlled by the density-weighted logarithmic measure. -/
theorem c8_volume_inter_le_log_cutoff {d : ℕ} {κ : ℝ} (hκ : 0 < κ)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (hell : IsUniformlyElliptic κ ρ α)
    {A : Set (Vec d)} (hA : MeasurableSet A) :
    volume (A ∩ PDE.euclideanBall (0 : Vec d) (3 / 4)) ≤
      (ENNReal.ofReal κ)⁻¹ * c8LogCutoffMass ρ * c8LogCutoffMeasure ρ A := by
  let B := sourceBall (0 : Vec d) 1
  let S := PDE.euclideanBall (0 : Vec d) (3 / 4)
  have hS : MeasurableSet S := PDE.measurableSet_euclideanBall _ _
  have hSB : S ⊆ B := by
    dsimp [S, B]
    rw [c8_sourceBall_eq_euclideanBall 0 (by norm_num)]
    exact PDE.euclideanBall_mono (by norm_num) (by norm_num)
  have hmass : c8LogCutoffMass ρ ≠ 0 := by
    rw [c8_log_cutoff_mass_eq hκ hell]
    exact (ENNReal.ofReal_pos.mpr (c8_squared_cutoff_density_mass_pos hκ hell)).ne'
  have htop : c8LogCutoffMass ρ ≠ ⊤ := by
    rw [c8_log_cutoff_mass_eq hκ hell]
    exact ENNReal.ofReal_ne_top
  have hk : ENNReal.ofReal κ ≠ 0 := (ENNReal.ofReal_pos.mpr hκ).ne'
  have hkTop : ENNReal.ofReal κ ≠ ⊤ := ENNReal.ofReal_ne_top
  have hbound : ENNReal.ofReal κ * volume (A ∩ S) ≤
      c8LogCutoffMass ρ * c8LogCutoffMeasure ρ A := by
    rw [c8LogCutoffMeasure, Measure.smul_apply, withDensity_apply _ hA, smul_eq_mul,
      ← mul_assoc, ENNReal.mul_inv_cancel hmass htop, one_mul]
    calc
      _ = ENNReal.ofReal κ * (volume.restrict B) (A ∩ S) := by
        rw [Measure.restrict_apply (hA.inter hS), Set.inter_eq_left.mpr
          (Set.inter_subset_right.trans hSB)]
      _ = ∫⁻ _x in A ∩ S, ENNReal.ofReal κ ∂(volume.restrict B) := by
        rw [lintegral_const]
        simp only [Measure.restrict_apply_univ]
      _ ≤ ∫⁻ x in A ∩ S, ENNReal.ofReal
          (ρ x * PDE.Parabolic.WeakHarnack.radialCutoff d x ^ 2) ∂(volume.restrict B) := by
        apply setLIntegral_mono' (hA.inter hS)
        intro x hx
        apply ENNReal.ofReal_le_ofReal
        have hχ := (c8_radial_cutoff_properties d).2.2.2.2.1 x hx.2
        simpa [hχ] using (hell.2.2 x).1
      _ ≤ _ := lintegral_mono_set Set.inter_subset_left
  calc
    _ = (ENNReal.ofReal κ)⁻¹ * (ENNReal.ofReal κ * volume (A ∩ S)) := by
      rw [← mul_assoc, ENNReal.inv_mul_cancel hk hkTop, one_mul]
    _ ≤ (ENNReal.ofReal κ)⁻¹ * (c8LogCutoffMass ρ * c8LogCutoffMeasure ρ A) :=
      mul_le_mul' le_rfl hbound
    _ = _ := by rw [mul_assoc]

/-- The logarithmic cutoff mass has a coefficient-independent upper bound. -/
theorem c8_log_cutoff_mass_le {d : ℕ} {κ : ℝ} (hκ : 0 < κ)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (hell : IsUniformlyElliptic κ ρ α) :
    c8LogCutoffMass ρ ≤ ENNReal.ofReal κ⁻¹ * volume (sourceBall (0 : Vec d) 1) := by
  unfold c8LogCutoffMass
  calc
    _ ≤ ∫⁻ _x in sourceBall (0 : Vec d) 1, ENNReal.ofReal κ⁻¹ := by
      apply lintegral_mono
      intro x
      have hρ := hell.2.2 x
      have hχ := (c8_radial_cutoff_properties d).2.2.2.1 x
      have hχ2 : PDE.Parabolic.WeakHarnack.radialCutoff d x ^ 2 ≤ 1 := by nlinarith
      apply ENNReal.ofReal_le_ofReal
      calc
        ρ x * PDE.Parabolic.WeakHarnack.radialCutoff d x ^ 2 ≤ ρ x * 1 :=
          mul_le_mul_of_nonneg_left hχ2 (hκ.le.trans hρ.1)
        _ ≤ κ⁻¹ := by simpa using hρ.2.1
    _ = _ := by rw [lintegral_const, Measure.restrict_apply_univ]

/-- Volume transfer with a constant depending only on dimension and ellipticity. -/
theorem c8_volume_inter_le_log_cutoff_uniform {d : ℕ} {κ : ℝ} (hκ : 0 < κ)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (hell : IsUniformlyElliptic κ ρ α)
    {A : Set (Vec d)} (hA : MeasurableSet A) :
    volume (A ∩ PDE.euclideanBall (0 : Vec d) (3 / 4)) ≤
      ((ENNReal.ofReal κ)⁻¹ * (ENNReal.ofReal κ⁻¹ *
        volume (sourceBall (0 : Vec d) 1))) * c8LogCutoffMeasure ρ A := by
  exact (c8_volume_inter_le_log_cutoff hκ hell hA).trans
    (mul_le_mul' (mul_le_mul' le_rfl (c8_log_cutoff_mass_le hκ hell)) le_rfl)

/-- The uniform spatial comparison transfers to measurable space-time slabs. -/
theorem c8_volume_slab_le_log_cutoff {d : ℕ} {κ : ℝ} (hκ : 0 < κ)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (hell : IsUniformlyElliptic κ ρ α)
    {E : Set (Vec d × ℝ)} (hE : MeasurableSet E) {I : Set ℝ} (hI : MeasurableSet I) :
    volume ((PDE.euclideanBall (0 : Vec d) (3 / 4) ×ˢ I) ∩ E) ≤
      ((ENNReal.ofReal κ)⁻¹ * (ENNReal.ofReal κ⁻¹ *
        volume (sourceBall (0 : Vec d) 1))) *
      ∫⁻ t in I, c8LogCutoffMeasure ρ {x | (x, t) ∈ E} := by
  have hM : (ENNReal.ofReal κ)⁻¹ * (ENNReal.ofReal κ⁻¹ *
      volume (sourceBall (0 : Vec d) 1)) ≠ ⊤ := by
    apply ENNReal.mul_ne_top
    · exact ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr hκ).ne'
    · apply ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      rw [c8_sourceBall_eq_euclideanBall 0 (by norm_num)]
      exact PDE.volume_euclideanBall_ne_top 0 (by norm_num)
  exact PDE.Parabolic.WeakHarnack.volume_slab_inter_le hM
    (c8LogCutoffMeasure ρ) (fun _ hA => c8_volume_inter_le_log_cutoff_uniform hκ hell hA)
    hE hI

/-- Cylinder L² control gives logarithmic-measure L² control on almost every time slice. -/
theorem c8_ae_slice_memLp_log_cutoff {d : ℕ} {κ : ℝ} (hκ : 0 < κ)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (hell : IsUniformlyElliptic κ ρ α)
    {I : Set ℝ} (f : ℝ × Vec d → ℝ)
    (hf : MemLp f 2 (volume.restrict (I ×ˢ sourceBall 0 1))) :
    ∀ᵐ t ∂volume.restrict I, MemLp (fun x => f (t, x)) 2 (c8LogCutoffMeasure ρ) := by
  have hB : MeasurableSet (sourceBall (0 : Vec d) 1) := by
    rw [c8_sourceBall_eq_euclideanBall 0 (by norm_num)]
    exact PDE.measurableSet_euclideanBall 0 1
  filter_upwards [c8_native_ae_slice_memLp hB f hf] with t ht
  exact c8_memLp_log_cutoff_measure hκ hell ht


/-- A scalar logarithmic tail estimate transfers to ordinary space-time volume. -/
theorem c8_log_tail_volume {d : ℕ} {κ : ℝ} (hκ : 0 < κ)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (hell : IsUniformlyElliptic κ ρ α)
    (w : Vec d → ℝ → ℝ) (hw : Measurable (fun z : Vec d × ℝ => w z.1 z.2))
    {T₁ T₂ t₀ c K : ℝ} (N : Set ℝ)
    (hT₁ : T₁ < t₀) (hT₂ : t₀ < T₂) (hc : 0 < c) (hK : 0 ≤ K)
    (hN : volume N = 0)
    (hL2 : ∀ t ∈ Set.Icc T₁ T₂, t ∉ N → MemLp (fun x => w x t) 2 (c8LogCutoffMeasure ρ))
    (hV : IntervalIntegrable (fun t => ∫ x, (w x t - ∫ y, w y t ∂c8LogCutoffMeasure ρ) ^ 2 ∂c8LogCutoffMeasure ρ) volume T₁ T₂)
    (hdiff : ∀ t₁ ∈ Set.Icc T₁ T₂, ∀ t₂ ∈ Set.Icc T₁ T₂, t₁ ∉ N → t₂ ∉ N → t₁ < t₂ →
      ∫ τ in t₁..t₂, (c * ∫ x, (w x τ - ∫ y, w y τ ∂c8LogCutoffMeasure ρ) ^ 2 ∂c8LogCutoffMeasure ρ - K) ≤
        (∫ x, w x t₂ ∂c8LogCutoffMeasure ρ) - ∫ x, w x t₁ ∂c8LogCutoffMeasure ρ)
    (ht₀ : t₀ ∉ N) {ℓ : ℝ} (hℓ : 0 < ℓ) :
    volume ((PDE.euclideanBall (0 : Vec d) (3 / 4) ×ˢ Set.Ioc T₁ t₀) ∩
      {z | (∫ y, w y t₀ ∂c8LogCutoffMeasure ρ) + ℓ < w z.1 z.2}) +
    volume ((PDE.euclideanBall (0 : Vec d) (3 / 4) ×ˢ Set.Ioc t₀ T₂) ∩
      {z | w z.1 z.2 < (∫ y, w y t₀ ∂c8LogCutoffMeasure ρ) - ℓ}) ≤
      ((ENNReal.ofReal κ)⁻¹ * (ENNReal.ofReal κ⁻¹ * volume (sourceBall (0 : Vec d) 1))) *
        ENNReal.ofReal ((4 / c + 4 * K * (T₂ - T₁) ^ 2) / ℓ) := by
  letI : IsProbabilityMeasure (c8LogCutoffMeasure ρ) := c8_log_cutoff_isProbabilityMeasure hκ hell
  have hleft := c8_volume_slab_le_log_cutoff hκ hell
    (E := {z : Vec d × ℝ | (∫ y, w y t₀ ∂c8LogCutoffMeasure ρ) + ℓ < w z.1 z.2})
    (I := Set.Ioc T₁ t₀) (measurableSet_lt measurable_const hw) measurableSet_Ioc
  have hright := c8_volume_slab_le_log_cutoff hκ hell
    (E := {z : Vec d × ℝ | w z.1 z.2 < (∫ y, w y t₀ ∂c8LogCutoffMeasure ρ) - ℓ})
    (I := Set.Ioc t₀ T₂) (measurableSet_lt hw measurable_const) measurableSet_Ioc
  have htail := PDE.Parabolic.WeakHarnack.logTail_integrated (c8LogCutoffMeasure ρ) w N
    hT₁ hT₂ hc hK hN hL2 hV hdiff ht₀ hℓ
  calc
    _ ≤ _ := add_le_add hleft hright
    _ = _ := by
      rw [mul_add]
      rfl
    _ ≤ _ := mul_le_mul' le_rfl htail


/-- A cutoff Poincaré bound converts a time-integrated energy inequality
into the variance inequality used by the logarithmic tail theorem. -/
theorem c8_log_variance_time_bound {a C K t₁ t₂ : ℝ} (ha : 0 < a) (hC : 0 < C)
    (ht : t₁ ≤ t₂) (V E : ℝ → ℝ) (m : ℝ → ℝ)
    (hV : IntervalIntegrable V volume t₁ t₂)
    (hE : IntervalIntegrable E volume t₁ t₂)
    (hP : ∀ᵐ t ∂volume.restrict (Set.Icc t₁ t₂), V t ≤ C * E t)
    (henergy : ∫ t in t₁..t₂, (a * E t - K) ≤ m t₂ - m t₁) :
    ∫ t in t₁..t₂, ((a / C) * V t - K) ≤ m t₂ - m t₁ := by
  have hvi : IntervalIntegrable (fun t => (a / C) * V t - K) volume t₁ t₂ :=
    (hV.const_mul (a / C)).sub intervalIntegrable_const
  have hei : IntervalIntegrable (fun t => a * E t - K) volume t₁ t₂ :=
    (hE.const_mul a).sub intervalIntegrable_const
  apply (intervalIntegral.integral_mono_ae_restrict ht hvi hei ?_).trans henergy
  filter_upwards [hP] with t hpt
  have hm := mul_le_mul_of_nonneg_left hpt (div_nonneg ha.le hC.le)
  have heq : (a / C) * (C * E t) = a * E t := by field_simp
  rw [heq] at hm
  linarith


/-- The actual logarithmic slices satisfy the uniform cutoff Poincaré bound,
with their literal quotient gradient. -/
theorem c8_ae_log_cutoff_poincare (d : ℕ) {κ : ℝ} (hκ : 0 < κ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
      IsUniformlyElliptic κ ρ α → ∀ (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
      {ε : ℝ}, 0 < ε →
      IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1) u G →
      (∀ᵐ z ∂volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1), ε ≤ u z) →
      ∀ᵐ t ∂volume.restrict (Set.Ioo (-1 : ℝ) 1),
        (∫ x, (Real.log (u (t,x)) - ∫ y, Real.log (u (t,y)) ∂c8LogCutoffMeasure ρ) ^ 2 ∂c8LogCutoffMeasure ρ) ≤
          C * ∫ x in sourceBall (0 : Vec d) 1,
            PDE.vecNormSq ((u (t,x))⁻¹ • G (t,x)) * PDE.Parabolic.WeakHarnack.radialCutoff d x ^ 2 := by
  obtain ⟨C, hC, hP⟩ := c8_log_cutoff_poincare_uniform d hκ
  refine ⟨C, hC, ?_⟩
  intro ρ α hell u G ε hε hcal hpositive
  let U := sourceBall (0 : Vec d) 1
  have hU : IsOpen U := by
    dsimp [U]
    rw [c8_sourceBall_eq_euclideanBall 0 (by norm_num)]
    exact PDE.isOpen_euclideanBall 0 1
  haveI : IsFiniteMeasure (volume.restrict U) := isFiniteMeasure_restrict.mpr (by
    dsimp [U]
    rw [c8_sourceBall_eq_euclideanBall 0 (by norm_num)]
    exact PDE.volume_euclideanBall_ne_top 0 (by norm_num))
  have hm := c16_weighted_caloric_log_memLp hε ρ α u G hcal hpositive
  have hw := c16_weighted_caloric_log_gradient_slices hU hε ρ α u G hcal hpositive
  filter_upwards [c8_native_ae_slice_memLp hU.measurableSet _ hm.1,
    c8_native_ae_slice_memLp hU.measurableSet _ hm.2, hw] with t ht hg hw
  have hl : MemLp (fun x => Real.log (u (t,x))) 2 (volume.restrict U) := by
    have heq : ((fun x => Real.log (u (t,x)) - c16LogExtension ε 0) +
        (fun _ => c16LogExtension ε 0)) = (fun x => Real.log (u (t,x))) := by
      funext x
      simp only [Pi.add_apply, sub_add_cancel]
    rw [← heq]
    exact ht.add (memLp_const (c16LogExtension ε 0))
  let v : PDE.H1Function U := {
    toFun := fun x => Real.log (u (t,x))
    grad := fun x => (u (t,x))⁻¹ • G (t,x)
    memL2 := hl
    gradMemL2 := by
      intro i
      apply hg.mono' (hw i).2.1.aestronglyMeasurable
      exact ae_of_all _ fun x => by
        simpa only [TimeChange.euclideanNorm_eq_norm_toLp] using
          (PiLp.norm_apply_le (WithLp.toLp 2 ((u (t,x))⁻¹ • G (t,x))) i)
    hasWeakGradient := by
      intro i φ hφ hc hs
      simpa only [coordinateDerivative, PDE.basisVec, unitVector] using
        (hw i).2.2 φ ⟨hφ, hc, hs⟩ }
  exact hP ρ α hell v


/-- Positive weighted-caloric logarithms have square-integrable slices for the
normalized cutoff measure. -/
theorem c8_ae_log_memLp_cutoff {d : ℕ} {κ : ℝ} (hκ : 0 < κ)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (hell : IsUniformlyElliptic κ ρ α)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d) {ε : ℝ} (hε : 0 < ε)
    (hcal : IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1) u G)
    (hpositive : ∀ᵐ z ∂volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1), ε ≤ u z) :
    ∀ᵐ t ∂volume.restrict (Set.Ioo (-1 : ℝ) 1),
      MemLp (fun x => Real.log (u (t,x))) 2 (c8LogCutoffMeasure ρ) := by
  letI : IsProbabilityMeasure (c8LogCutoffMeasure ρ) :=
    c8_log_cutoff_isProbabilityMeasure hκ hell
  have hm := (c16_weighted_caloric_log_memLp hε ρ α u G hcal hpositive).1
  filter_upwards [c8_ae_slice_memLp_log_cutoff hκ hell _ hm] with t ht
  have heq : ((fun x => Real.log (u (t,x)) - c16LogExtension ε 0) +
      (fun _ => c16LogExtension ε 0)) = (fun x => Real.log (u (t,x))) := by
    funext x
    simp only [Pi.add_apply, sub_add_cancel]
  rw [← heq]
  exact ht.add (memLp_const (c16LogExtension ε 0))


/-- The dissipation in the cutoff Poincaré estimate is integrable on the
full time cylinder and on each interior time interval. -/
theorem c8_log_cutoff_dissipation_integrable {d : ℕ} {ε : ℝ} (hε : 0 < ε)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hcal : IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1) u G)
    (hpositive : ∀ᵐ z ∂volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1), ε ≤ u z) :
    let E : ℝ → ℝ := fun t => ∫ x in sourceBall (0 : Vec d) 1,
      PDE.vecNormSq ((u (t,x))⁻¹ • G (t,x)) *
        PDE.Parabolic.WeakHarnack.radialCutoff d x ^ 2
    Integrable E (volume.restrict (Set.Ioo (-1 : ℝ) 1)) ∧
      ∀ {s t : ℝ}, s ∈ Set.Ioo (-1 : ℝ) 1 → t ∈ Set.Ioo (-1 : ℝ) 1 →
        s ≤ t → IntervalIntegrable E volume s t := by
  dsimp only
  obtain ⟨hχ, hχc, _⟩ := c8_radial_cutoff_properties d
  have hi := (c16_weighted_caloric_log_dissipation_integrable hε ρ α u G hcal hpositive
    (PDE.Parabolic.WeakHarnack.radialCutoff d) hχ hχc).2
  have hE : Integrable (fun t => ∫ x in sourceBall (0 : Vec d) 1,
      PDE.vecNormSq ((u (t,x))⁻¹ • G (t,x)) *
        PDE.Parabolic.WeakHarnack.radialCutoff d x ^ 2)
      (volume.restrict (Set.Ioo (-1 : ℝ) 1)) := by
    convert hi using 1 <;> ext t x <;> simp only [mul_comm] <;> rfl
  refine ⟨hE, ?_⟩
  intro s t hs ht hst
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hst).2
  apply IntegrableOn.mono_set hE
  intro x hx
  exact ⟨lt_trans hs.1 hx.1, lt_of_le_of_lt hx.2 ht.2⟩


/-- Square-integrable space-time functions have an integrable time-dependent
variance under a probability measure. -/
@[nolint unusedArguments]
theorem c8_integrable_slice_variance {X : Type*} [MeasurableSpace X]
    (μ : Measure ℝ) [SFinite μ] (ν : Measure X) [IsProbabilityMeasure ν]
    (f : ℝ × X → ℝ) (hf : MemLp f 2 (μ.prod ν))
    (hslice : ∀ᵐ t ∂μ, MemLp (fun x => f (t,x)) 2 ν) :
    Integrable (fun t => ∫ x, (f (t,x) - ∫ y, f (t,y) ∂ν) ^ 2 ∂ν) μ := by
  have hm : AEStronglyMeasurable (fun t => ∫ x, f (t,x) ∂ν) μ :=
    hf.aestronglyMeasurable.integral_prod_right'
  have hv : AEStronglyMeasurable (fun t => ∫ x,
      (f (t,x) - ∫ y, f (t,y) ∂ν) ^ 2 ∂ν) μ := by
    have hsub := hf.aestronglyMeasurable.sub (hm.comp_fst)
    simpa only [pow_two, Pi.mul_apply, Pi.sub_apply] using (hsub.mul hsub).integral_prod_right'
  have hb := hf.integrable_sq.integral_prod_left
  apply hb.mono_nonneg hv (ae_of_all μ fun t => integral_nonneg fun x => sq_nonneg _)
  filter_upwards [hslice] with t ht
  have h := c8_integral_sq_sub_mean_le ν (by simp) ht 0
  simpa using h


/-- The actual positive logarithm has integrable cutoff variance in time. -/
theorem c8_log_cutoff_variance_integrable {d : ℕ} {κ : ℝ} (hκ : 0 < κ)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (hell : IsUniformlyElliptic κ ρ α)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d) {ε : ℝ} (hε : 0 < ε)
    (hcal : IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1) u G)
    (hpositive : ∀ᵐ z ∂volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1), ε ≤ u z) :
    Integrable (fun t => ∫ x, (Real.log (u (t,x)) -
      ∫ y, Real.log (u (t,y)) ∂c8LogCutoffMeasure ρ) ^ 2 ∂c8LogCutoffMeasure ρ)
        (volume.restrict (Set.Ioo (-1 : ℝ) 1)) := by
  let I := Set.Ioo (-1 : ℝ) 1
  let B := sourceBall (0 : Vec d) 1
  let ν := c8LogCutoffMeasure ρ
  let c := (c8LogCutoffMass ρ)⁻¹ * ENNReal.ofReal κ⁻¹
  letI : IsProbabilityMeasure ν := c8_log_cutoff_isProbabilityMeasure hκ hell
  letI : IsFiniteMeasure (volume.restrict I) := isFiniteMeasure_restrict.mpr (by
    dsimp [I]
    simp)
  have hc : c ≠ ⊤ := by
    dsimp [c]
    rw [c8_log_cutoff_mass_eq hκ hell]
    exact ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr
      (ENNReal.ofReal_pos.mpr (c8_squared_cutoff_density_mass_pos hκ hell)).ne')
      ENNReal.ofReal_ne_top
  have hle : (volume.restrict I).prod ν ≤ c • ((volume.restrict I).prod (volume.restrict B)) := by
    calc
      _ ≤ (volume.restrict I).prod (c • volume.restrict B) :=
        Measure.prod_mono le_rfl (c8_log_cutoff_measure_le hκ hell)
      _ = _ := Measure.prod_smul_right c
  have hm := (c16_weighted_caloric_log_memLp hε ρ α u G hcal hpositive).1
  have hp : MemLp (fun z => Real.log (u z) - c16LogExtension ε 0) 2
      ((volume.restrict I).prod (volume.restrict B)) := by
    rw [Measure.prod_restrict]
    exact hm
  have hn := hp.of_measure_le_smul hc hle
  have hl : MemLp (fun z => Real.log (u z)) 2 ((volume.restrict I).prod ν) := by
    have heq : ((fun z => Real.log (u z) - c16LogExtension ε 0) +
        (fun _ => c16LogExtension ε 0)) = (fun z => Real.log (u z)) := by
      funext z
      simp only [Pi.add_apply, sub_add_cancel]
    rw [← heq]
    exact hn.add (memLp_const (c16LogExtension ε 0))
  exact c8_integrable_slice_variance (volume.restrict I) ν _ hl
    (c8_ae_log_memLp_cutoff hκ hell u G hε hcal hpositive)


/-- Normalize a weighted logarithmic energy inequality by the positive
cutoff mass. The endpoint identities need only hold at the selected times. -/
theorem c8_normalize_log_energy {a M K s t : ℝ} (hM : 0 < M)
    (D E m : ℝ → ℝ) (hD : IntervalIntegrable D volume s t)
    (hs : E s = M * m s) (ht : E t = M * m t)
    (henergy : a * (∫ q in s..t, D q) ≤ E t - E s + K * (t - s)) :
    ∫ q in s..t, ((a / M) * D q - K / M) ≤ m t - m s := by
  have heq : (∫ q in s..t, ((a / M) * D q - K / M)) =
      (a * (∫ q in s..t, D q) - K * (t - s)) / M := by
    rw [intervalIntegral.integral_sub (hD.const_mul (a / M)) intervalIntegrable_const,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const]
    simp only [smul_eq_mul]
    ring
  rw [heq]
  apply (div_le_iff₀ hM).2
  rw [hs, ht] at henergy
  nlinarith


/-- A cutoff Poincaré inequality and an unnormalized energy inequality
imply the normalized variance inequality on an interior time interval. -/
theorem c8_log_variance_time_bound_of_energy {a M C K s t : ℝ}
    (ha : 0 < a) (hM : 0 < M) (hC : 0 < C) (hst : s ≤ t)
    (V D E m : ℝ → ℝ) (hV : IntervalIntegrable V volume s t)
    (hD : IntervalIntegrable D volume s t)
    (hP : ∀ᵐ q ∂volume.restrict (Set.Icc s t), V q ≤ C * D q)
    (hs : E s = M * m s) (ht : E t = M * m t)
    (henergy : a * (∫ q in s..t, D q) ≤ E t - E s + K * (t - s)) :
    ∫ q in s..t, (((a / M) / C) * V q - K / M) ≤ m t - m s := by
  apply c8_log_variance_time_bound (div_pos ha hM) hC hst V D m hV hD hP
  exact c8_normalize_log_energy hM D E m hD hs ht henergy


/-- The actual logarithmic variance satisfies the scalar time inequality
on intervals whose endpoints realize the weighted logarithmic energy. -/
theorem c8_actual_log_variance_time_bound (d : ℕ) {κ : ℝ} (hκ : 0 < κ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
      IsUniformlyElliptic κ ρ α → ∀ (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
      {ε : ℝ}, 0 < ε →
      IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1) u G →
      (∀ᵐ z ∂volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1), ε ≤ u z) →
      ∀ (E : ℝ → ℝ) (K : ℝ) {s t : ℝ}, s ∈ Set.Ioo (-1 : ℝ) 1 →
      t ∈ Set.Ioo (-1 : ℝ) 1 → s ≤ t →
      E s = (∫ x in sourceBall (0 : Vec d) 1,
        ρ x * PDE.Parabolic.WeakHarnack.radialCutoff d x ^ 2 * Real.log (u (s,x))) →
      E t = (∫ x in sourceBall (0 : Vec d) 1,
        ρ x * PDE.Parabolic.WeakHarnack.radialCutoff d x ^ 2 * Real.log (u (t,x))) →
      (κ / 2) * (∫ q in s..t, ∫ x in sourceBall (0 : Vec d) 1,
        PDE.vecNormSq ((u (q,x))⁻¹ • G (q,x)) *
          PDE.Parabolic.WeakHarnack.radialCutoff d x ^ 2) ≤
        E t - E s + K * (t - s) →
      let M := ∫ x in sourceBall (0 : Vec d) 1,
        ρ x * PDE.Parabolic.WeakHarnack.radialCutoff d x ^ 2
      ∫ q in s..t, (((κ / 2 / M) / C) *
        (∫ x, (Real.log (u (q,x)) -
          ∫ y, Real.log (u (q,y)) ∂c8LogCutoffMeasure ρ) ^ 2 ∂c8LogCutoffMeasure ρ) - K / M) ≤
        (∫ x, Real.log (u (t,x)) ∂c8LogCutoffMeasure ρ) -
          ∫ x, Real.log (u (s,x)) ∂c8LogCutoffMeasure ρ := by
  obtain ⟨C, hC, hP⟩ := c8_ae_log_cutoff_poincare d hκ
  refine ⟨C, hC, ?_⟩
  intro ρ α hell u G ε hε hcal hpositive E K s t hs ht hst hEs hEt henergy
  let M := ∫ x in sourceBall (0 : Vec d) 1,
    ρ x * PDE.Parabolic.WeakHarnack.radialCutoff d x ^ 2
  let m : ℝ → ℝ := fun q => ∫ x, Real.log (u (q,x)) ∂c8LogCutoffMeasure ρ
  let V : ℝ → ℝ := fun q => ∫ x, (Real.log (u (q,x)) - m q) ^ 2 ∂c8LogCutoffMeasure ρ
  let D : ℝ → ℝ := fun q => ∫ x in sourceBall (0 : Vec d) 1,
    PDE.vecNormSq ((u (q,x))⁻¹ • G (q,x)) * PDE.Parabolic.WeakHarnack.radialCutoff d x ^ 2
  have hM : 0 < M := c8_squared_cutoff_density_mass_pos hκ hell
  have hsub : Set.Icc s t ⊆ Set.Ioo (-1 : ℝ) 1 := by
    intro q hq
    exact ⟨lt_of_lt_of_le hs.1 hq.1, lt_of_le_of_lt hq.2 ht.2⟩
  have hioc : Set.Ioc s t ⊆ Set.Ioo (-1 : ℝ) 1 := fun q hq =>
    ⟨lt_trans hs.1 hq.1, lt_of_le_of_lt hq.2 ht.2⟩
  have hv : IntervalIntegrable V volume s t := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hst).2
    exact IntegrableOn.mono_set (c8_log_cutoff_variance_integrable hκ hell u G hε hcal hpositive) hioc
  have hd : IntervalIntegrable D volume s t :=
    (c8_log_cutoff_dissipation_integrable hε ρ α u G hcal hpositive).2 hs ht hst
  have hp : ∀ᵐ q ∂volume.restrict (Set.Icc s t), V q ≤ C * D q :=
    ae_restrict_of_ae_restrict_of_subset hsub (hP ρ α hell u G hε hcal hpositive)
  have hms : E s = M * m s := by
    have hh := c8_integral_log_cutoff_measure hκ hell (fun x => Real.log (u (s,x)))
    rw [← hEs] at hh
    change m s = M⁻¹ * E s at hh
    rw [hh]
    field_simp [ne_of_gt hM]
  have hmt : E t = M * m t := by
    have hh := c8_integral_log_cutoff_measure hκ hell (fun x => Real.log (u (t,x)))
    rw [← hEt] at hh
    change m t = M⁻¹ * E t at hh
    rw [hh]
    field_simp [ne_of_gt hM]
  exact c8_log_variance_time_bound_of_energy (by linarith) hM hC hst V D E m hv hd hp hms hmt henergy


/-- A real upper bound for the cutoff mass, uniform in the coefficients. -/
theorem c8_squared_cutoff_density_mass_le {d : ℕ} {κ : ℝ} (hκ : 0 < κ)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (hell : IsUniformlyElliptic κ ρ α) :
    (∫ x in sourceBall (0 : Vec d) 1,
      ρ x * PDE.Parabolic.WeakHarnack.radialCutoff d x ^ 2) ≤
      κ⁻¹ * (volume (sourceBall (0 : Vec d) 1)).toReal := by
  have hv : volume (sourceBall (0 : Vec d) 1) ≠ ⊤ := by
    rw [c8_sourceBall_eq_euclideanBall 0 (by norm_num)]
    exact PDE.volume_euclideanBall_ne_top 0 (by norm_num)
  have h := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hv)
    (c8_log_cutoff_mass_le hκ hell)
  rw [c8_log_cutoff_mass_eq hκ hell, ENNReal.toReal_ofReal
    (c8_squared_cutoff_density_mass_pos hκ hell).le, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (inv_nonneg.mpr hκ.le)] at h
  exact h


/-- The actual variance inequality holds for almost every pair of ordered
endpoints when the energy representative agrees with its integral almost everywhere. -/
theorem c8_actual_log_variance_time_bound_off_null_set (d : ℕ) {κ : ℝ} (hκ : 0 < κ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
      IsUniformlyElliptic κ ρ α → ∀ (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
      {ε : ℝ}, 0 < ε →
      IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1) u G →
      (∀ᵐ z ∂volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1), ε ≤ u z) →
      ∀ (E : ℝ → ℝ) (K : ℝ),
      (∀ᵐ q ∂volume.restrict (Set.Ioo (-1 : ℝ) 1),
        E q = ∫ x in sourceBall (0 : Vec d) 1,
          ρ x * PDE.Parabolic.WeakHarnack.radialCutoff d x ^ 2 * Real.log (u (q,x))) →
      (∀ s ∈ Set.Ioo (-1 : ℝ) 1, ∀ t ∈ Set.Ioo (-1 : ℝ) 1, s ≤ t →
        (κ / 2) * (∫ q in s..t, ∫ x in sourceBall (0 : Vec d) 1,
          PDE.vecNormSq ((u (q,x))⁻¹ • G (q,x)) *
            PDE.Parabolic.WeakHarnack.radialCutoff d x ^ 2) ≤ E t - E s + K * (t - s)) →
      ∃ N : Set ℝ, volume N = 0 ∧
      ∀ s ∈ Set.Ioo (-1 : ℝ) 1, ∀ t ∈ Set.Ioo (-1 : ℝ) 1,
        s ∉ N → t ∉ N → s ≤ t →
      let M := ∫ x in sourceBall (0 : Vec d) 1,
        ρ x * PDE.Parabolic.WeakHarnack.radialCutoff d x ^ 2
      ∫ q in s..t, (((κ / 2 / M) / C) *
        (∫ x, (Real.log (u (q,x)) -
          ∫ y, Real.log (u (q,y)) ∂c8LogCutoffMeasure ρ) ^ 2 ∂c8LogCutoffMeasure ρ) - K / M) ≤
        (∫ x, Real.log (u (t,x)) ∂c8LogCutoffMeasure ρ) -
          ∫ x, Real.log (u (s,x)) ∂c8LogCutoffMeasure ρ := by
  obtain ⟨C, hC, hbound⟩ := c8_actual_log_variance_time_bound d hκ
  refine ⟨C, hC, ?_⟩
  intro ρ α hell u G ε hε hcal hpositive E K hE henergy
  let N : Set ℝ := {q | q ∈ Set.Ioo (-1 : ℝ) 1 ∧
    E q ≠ ∫ x in sourceBall (0 : Vec d) 1,
      ρ x * PDE.Parabolic.WeakHarnack.radialCutoff d x ^ 2 * Real.log (u (q,x))}
  have hN : volume N = 0 := by
    have hh := (ae_iff).1 ((ae_restrict_iff' measurableSet_Ioo).1 hE)
    simpa only [not_imp, not_not] using hh
  refine ⟨N, hN, ?_⟩
  intro s hs t ht hsN htN hst
  have hEs : E s = ∫ x in sourceBall (0 : Vec d) 1,
      ρ x * PDE.Parabolic.WeakHarnack.radialCutoff d x ^ 2 * Real.log (u (s,x)) := by
    by_contra hh
    exact hsN ⟨hs, hh⟩
  have hEt : E t = ∫ x in sourceBall (0 : Vec d) 1,
      ρ x * PDE.Parabolic.WeakHarnack.radialCutoff d x ^ 2 * Real.log (u (t,x)) := by
    by_contra hh
    exact htN ⟨ht, hh⟩
  exact hbound ρ α hell u G hε hcal hpositive E K hs ht hst hEs hEt
    (henergy s hs t ht hst)


/-- Lowering the variance coefficient and increasing the error term
preserves the integrated inequality. -/
theorem c8_log_variance_time_bound_mono {c c' K K' s t : ℝ}
    (hst : s ≤ t) (hc : c ≤ c') (hK : K ≤ K')
    (V m : ℝ → ℝ) (hV : IntervalIntegrable V volume s t)
    (hVnonneg : ∀ᵐ q ∂volume.restrict (Set.Icc s t), 0 ≤ V q)
    (hbound : ∫ q in s..t, (c' * V q - K) ≤ m t - m s) :
    ∫ q in s..t, (c * V q - K') ≤ m t - m s := by
  have hi : IntervalIntegrable (fun q => c * V q - K') volume s t :=
    (hV.const_mul c).sub intervalIntegrable_const
  have hi' : IntervalIntegrable (fun q => c' * V q - K) volume s t :=
    (hV.const_mul c').sub intervalIntegrable_const
  apply (intervalIntegral.integral_mono_ae_restrict hst hi hi' ?_).trans hbound
  filter_upwards [hVnonneg] with q hq
  nlinarith [mul_nonneg (sub_nonneg.mpr hc) hq]


/-- The logarithmic variance inequality has coefficients depending only on
the dimension, ellipticity and the cutoff error, outside one null set. -/
theorem c8_uniform_log_variance_time_bound (d : ℕ) {κ : ℝ} (hκ : 0 < κ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
      IsUniformlyElliptic κ ρ α → ∀ (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
      {ε : ℝ}, 0 < ε →
      IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1) u G →
      (∀ᵐ z ∂volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1), ε ≤ u z) →
      ∀ (E : ℝ → ℝ) (K : ℝ), 0 ≤ K →
      (∀ᵐ q ∂volume.restrict (Set.Ioo (-1 : ℝ) 1),
        E q = ∫ x in sourceBall (0 : Vec d) 1,
          ρ x * PDE.Parabolic.WeakHarnack.radialCutoff d x ^ 2 * Real.log (u (q,x))) →
      (∀ s ∈ Set.Ioo (-1 : ℝ) 1, ∀ t ∈ Set.Ioo (-1 : ℝ) 1, s ≤ t →
        (κ / 2) * (∫ q in s..t, ∫ x in sourceBall (0 : Vec d) 1,
          PDE.vecNormSq ((u (q,x))⁻¹ • G (q,x)) *
            PDE.Parabolic.WeakHarnack.radialCutoff d x ^ 2) ≤ E t - E s + K * (t - s)) →
      ∃ N : Set ℝ, volume N = 0 ∧
      ∀ s ∈ Set.Ioo (-1 : ℝ) 1, ∀ t ∈ Set.Ioo (-1 : ℝ) 1,
        s ∉ N → t ∉ N → s ≤ t →
      let L := κ * (volume (PDE.euclideanBall (0 : Vec d) (3 / 4))).toReal
      let U := κ⁻¹ * (volume (sourceBall (0 : Vec d) 1)).toReal
      ∫ q in s..t, (((κ / 2 / U) / C) *
        (∫ x, (Real.log (u (q,x)) -
          ∫ y, Real.log (u (q,y)) ∂c8LogCutoffMeasure ρ) ^ 2 ∂c8LogCutoffMeasure ρ) - K / L) ≤
        (∫ x, Real.log (u (t,x)) ∂c8LogCutoffMeasure ρ) -
          ∫ x, Real.log (u (s,x)) ∂c8LogCutoffMeasure ρ := by
  obtain ⟨C, hC, hbound⟩ := c8_actual_log_variance_time_bound_off_null_set d hκ
  refine ⟨C, hC, ?_⟩
  intro ρ α hell u G ε hε hcal hpositive E K hK hE henergy
  obtain ⟨N, hN, hNbound⟩ := hbound ρ α hell u G hε hcal hpositive E K hE henergy
  refine ⟨N, hN, ?_⟩
  intro s hs t ht hsN htN hst
  let L := κ * (volume (PDE.euclideanBall (0 : Vec d) (3 / 4))).toReal
  let U := κ⁻¹ * (volume (sourceBall (0 : Vec d) 1)).toReal
  let M := ∫ x in sourceBall (0 : Vec d) 1,
    ρ x * PDE.Parabolic.WeakHarnack.radialCutoff d x ^ 2
  let m : ℝ → ℝ := fun q => ∫ x, Real.log (u (q,x)) ∂c8LogCutoffMeasure ρ
  let V : ℝ → ℝ := fun q => ∫ x, (Real.log (u (q,x)) - m q) ^ 2 ∂c8LogCutoffMeasure ρ
  have hL : 0 < L := mul_pos hκ (PDE.volume_euclideanBall_toReal_pos 0 (by norm_num))
  have hM : 0 < M := c8_squared_cutoff_density_mass_pos hκ hell
  have hLM : L ≤ M := c8_squared_cutoff_density_mass hκ hell
  have hMU : M ≤ U := c8_squared_cutoff_density_mass_le hκ hell
  have hc : (κ / 2 / U) / C ≤ (κ / 2 / M) / C :=
    div_le_div_of_nonneg_right (div_le_div_of_nonneg_left (by positivity) hM hMU) hC.le
  have hk : K / M ≤ K / L := div_le_div_of_nonneg_left hK hL hLM
  have hioc : Set.Ioc s t ⊆ Set.Ioo (-1 : ℝ) 1 := fun q hq =>
    ⟨lt_trans hs.1 hq.1, lt_of_le_of_lt hq.2 ht.2⟩
  have hv : IntervalIntegrable V volume s t := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hst).2
    exact IntegrableOn.mono_set (c8_log_cutoff_variance_integrable hκ hell u G hε hcal hpositive) hioc
  apply c8_log_variance_time_bound_mono hst hc hk V m hv
  · exact ae_of_all _ fun q => integral_nonneg fun x => sq_nonneg _
  · exact hNbound s hs t ht hsN htN hst

/-- A weighted caloric function has a measurable logarithmic representative
in the spatial-time order used by the logarithmic tail estimate. -/
theorem c8_log_measurable_representative {d : ℕ} {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    {I : Set ℝ} {U : Set (Vec d)} {u : ℝ × Vec d → ℝ}
    {G : ℝ × Vec d → Vec d} (hcal : IsWeightedCaloric ρ α I U u G) :
    ∃ w : Vec d → ℝ → ℝ, Measurable (fun z : Vec d × ℝ => w z.1 z.2) ∧
      ∀ᵐ z ∂volume.restrict (I ×ˢ U), w z.2 z.1 = Real.log (u z) := by
  let hu := hcal.1.aestronglyMeasurable
  refine ⟨fun x t => Real.log (hu.mk u (t, x)), ?_, ?_⟩
  · exact Real.measurable_log.comp (hu.stronglyMeasurable_mk.measurable.comp measurable_swap)
  · filter_upwards [hu.ae_eq_mk] with z hz
    rw [← hz]

/-- The measurable logarithm agrees with the original on almost every
normalized weighted spatial slice. -/
theorem c8_log_representative_ae_cutoff_slices {d : ℕ} {κ : ℝ} (hκ : 0 < κ)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (hell : IsUniformlyElliptic κ ρ α)
    {I : Set ℝ} {u : ℝ × Vec d → ℝ} {w : Vec d → ℝ → ℝ}
    (hw : ∀ᵐ z ∂volume.restrict (I ×ˢ sourceBall 0 1),
      w z.2 z.1 = Real.log (u z)) :
    ∀ᵐ t ∂volume.restrict I, ∀ᵐ x ∂c8LogCutoffMeasure ρ,
      w x t = Real.log (u (t,x)) := by
  have hp : ∀ᵐ z ∂(volume.restrict I).prod (volume.restrict (sourceBall (0 : Vec d) 1)),
      w z.2 z.1 = Real.log (u z) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    exact hw
  filter_upwards [Measure.ae_ae_of_ae_prod hp] with t ht
  exact (Measure.ae_smul_measure ht _).filter_mono (ae_mono (c8_log_cutoff_measure_le hκ hell))

/-- Equivalent logarithmic slices have the same weighted means and variances. -/
theorem c8_log_representative_ae_mean_variance {d : ℕ} {κ : ℝ} (hκ : 0 < κ)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (hell : IsUniformlyElliptic κ ρ α)
    {I : Set ℝ} {u : ℝ × Vec d → ℝ} {w : Vec d → ℝ → ℝ}
    (hw : ∀ᵐ z ∂volume.restrict (I ×ˢ sourceBall 0 1),
      w z.2 z.1 = Real.log (u z)) :
    ∀ᵐ t ∂volume.restrict I,
      (∫ x, w x t ∂c8LogCutoffMeasure ρ) =
        (∫ x, Real.log (u (t,x)) ∂c8LogCutoffMeasure ρ) ∧
      (∫ x, (w x t - ∫ y, w y t ∂c8LogCutoffMeasure ρ) ^ 2 ∂c8LogCutoffMeasure ρ) =
        ∫ x, (Real.log (u (t,x)) -
          ∫ y, Real.log (u (t,y)) ∂c8LogCutoffMeasure ρ) ^ 2 ∂c8LogCutoffMeasure ρ := by
  filter_upwards [c8_log_representative_ae_cutoff_slices hκ hell hw] with t ht
  have hm := integral_congr_ae ht
  refine ⟨hm, ?_⟩
  apply integral_congr_ae
  filter_upwards [ht] with x hx
  rw [hx, hm]

/-- Transfer an integrated variance inequality to almost-everywhere equal
mean and variance representatives, enlarging the exceptional endpoint set. -/
theorem c8_variance_time_bound_congr {a b c K : ℝ}
    (V V' m m' : ℝ → ℝ) (N : Set ℝ) (hN : volume N = 0)
    (heq : ∀ᵐ q ∂volume.restrict (Set.Ioo a b), m' q = m q ∧ V' q = V q)
    (hbound : ∀ s ∈ Set.Ioo a b, ∀ t ∈ Set.Ioo a b,
      s ∉ N → t ∉ N → s ≤ t →
      ∫ q in s..t, (c * V q - K) ≤ m t - m s) :
    ∃ N' : Set ℝ, volume N' = 0 ∧
      ∀ s ∈ Set.Ioo a b, ∀ t ∈ Set.Ioo a b,
        s ∉ N' → t ∉ N' → s ≤ t →
        ∫ q in s..t, (c * V' q - K) ≤ m' t - m' s := by
  let B : Set ℝ := {q | q ∈ Set.Ioo a b ∧ ¬ (m' q = m q ∧ V' q = V q)}
  have hB : volume B = 0 := by
    have hh := (ae_iff).1 ((ae_restrict_iff' measurableSet_Ioo).1 heq)
    simpa only [not_imp] using hh
  refine ⟨N ∪ B, measure_union_null hN hB, ?_⟩
  intro s hs t ht hsN htN hst
  have hsB : s ∉ B := fun h => hsN (Or.inr h)
  have htB : t ∉ B := fun h => htN (Or.inr h)
  have hsEq : m' s = m s ∧ V' s = V s := by
    by_contra h
    exact hsB ⟨hs, h⟩
  have htEq : m' t = m t ∧ V' t = V t := by
    by_contra h
    exact htB ⟨ht, h⟩
  have hioc : Set.Ioc s t ⊆ Set.Ioo a b := fun q hq =>
    ⟨lt_trans hs.1 hq.1, lt_of_le_of_lt hq.2 ht.2⟩
  have hVeq : ∀ᵐ q ∂volume.restrict (Set.uIoc s t), V' q = V q := by
    rw [Set.uIoc_of_le hst]
    filter_upwards [heq.filter_mono (ae_mono (Measure.restrict_mono_set _ hioc))] with q hq
    exact hq.2
  have hint : (∫ q in s..t, (c * V' q - K)) = ∫ q in s..t, (c * V q - K) := by
    apply intervalIntegral.integral_congr_ae_restrict
    filter_upwards [hVeq] with q hq
    rw [hq]
  rw [hint, htEq.1, hsEq.1]
  exact hbound s hs t ht (fun h => hsN (Or.inl h)) (fun h => htN (Or.inl h)) hst

/-- The measurable logarithmic representative is square-integrable on almost
every normalized cutoff slice. -/
theorem c8_log_representative_ae_memLp {d : ℕ} {κ : ℝ} (hκ : 0 < κ)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (hell : IsUniformlyElliptic κ ρ α)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d) {ε : ℝ} (hε : 0 < ε)
    (hcal : IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1) u G)
    (hpositive : ∀ᵐ z ∂volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1), ε ≤ u z)
    {w : Vec d → ℝ → ℝ}
    (hw : ∀ᵐ z ∂volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1),
      w z.2 z.1 = Real.log (u z)) :
    ∀ᵐ t ∂volume.restrict (Set.Ioo (-1 : ℝ) 1),
      MemLp (fun x => w x t) 2 (c8LogCutoffMeasure ρ) := by
  have hs := c8_log_representative_ae_cutoff_slices hκ hell hw
  have hl := c8_ae_log_memLp_cutoff hκ hell u G hε hcal hpositive
  apply (hs.and hl).mono
  intro t ht
  exact (memLp_congr_ae ht.1).2 ht.2

/-- The variance of the measurable logarithmic representative is integrable
on the original time interval. -/
theorem c8_log_representative_variance_integrable {d : ℕ} {κ : ℝ} (hκ : 0 < κ)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (hell : IsUniformlyElliptic κ ρ α)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d) {ε : ℝ} (hε : 0 < ε)
    (hcal : IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1) u G)
    (hpositive : ∀ᵐ z ∂volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1), ε ≤ u z)
    {w : Vec d → ℝ → ℝ}
    (hw : ∀ᵐ z ∂volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1),
      w z.2 z.1 = Real.log (u z)) :
    IntegrableOn (fun t => ∫ x, (w x t - ∫ y, w y t ∂c8LogCutoffMeasure ρ) ^ 2
      ∂c8LogCutoffMeasure ρ) (Set.Ioo (-1 : ℝ) 1) := by
  apply (c8_log_cutoff_variance_integrable hκ hell u G hε hcal hpositive).congr
  filter_upwards [c8_log_representative_ae_mean_variance hκ hell hw] with t ht
  exact ht.2.symm

/-- One null set contains all times where the representative lacks the
weighted square-integrability needed by the tail estimate. -/
theorem c8_log_representative_good_slices {d : ℕ} {κ : ℝ} (hκ : 0 < κ)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (hell : IsUniformlyElliptic κ ρ α)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d) {ε : ℝ} (hε : 0 < ε)
    (hcal : IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1) u G)
    (hpositive : ∀ᵐ z ∂volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1), ε ≤ u z)
    {w : Vec d → ℝ → ℝ}
    (hw : ∀ᵐ z ∂volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1),
      w z.2 z.1 = Real.log (u z)) :
    ∃ N : Set ℝ, volume N = 0 ∧ ∀ t ∈ Set.Ioo (-1 : ℝ) 1, t ∉ N →
      MemLp (fun x => w x t) 2 (c8LogCutoffMeasure ρ) := by
  let N : Set ℝ := {t | t ∈ Set.Ioo (-1 : ℝ) 1 ∧
    ¬ MemLp (fun x => w x t) 2 (c8LogCutoffMeasure ρ)}
  have hN : volume N = 0 := by
    have hh := (ae_iff).1 ((ae_restrict_iff' measurableSet_Ioo).1
      (c8_log_representative_ae_memLp hκ hell u G hε hcal hpositive hw))
    simpa only [not_imp] using hh
  refine ⟨N, hN, ?_⟩
  intro t ht htN
  by_contra hh
  exact htN ⟨ht, hh⟩


/-- The integrated logarithmic variance bound gives a volume tail at a
level time chosen outside the exceptional sets. -/
theorem c8_log_tail_of_variance_bound {d : ℕ} {κ : ℝ} (hκ : 0 < κ)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (hell : IsUniformlyElliptic κ ρ α)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d) {ε : ℝ} (hε : 0 < ε)
    (hcal : IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1) u G)
    (hpositive : ∀ᵐ z ∂volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1), ε ≤ u z)
    {c K : ℝ} (hc : 0 < c) (hK : 0 ≤ K) (N : Set ℝ) (hN : volume N = 0)
    (hbound : ∀ s ∈ Set.Ioo (-1 : ℝ) 1, ∀ t ∈ Set.Ioo (-1 : ℝ) 1,
      s ∉ N → t ∉ N → s ≤ t →
      ∫ q in s..t, (c * ∫ x, (Real.log (u (q,x)) -
        ∫ y, Real.log (u (q,y)) ∂c8LogCutoffMeasure ρ) ^ 2 ∂c8LogCutoffMeasure ρ - K) ≤
        (∫ x, Real.log (u (t,x)) ∂c8LogCutoffMeasure ρ) -
          ∫ x, Real.log (u (s,x)) ∂c8LogCutoffMeasure ρ) :
    ∃ (w : Vec d → ℝ → ℝ) (t₀ : ℝ),
      Measurable (fun z : Vec d × ℝ => w z.1 z.2) ∧
      (∀ᵐ z ∂volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1),
        w z.2 z.1 = Real.log (u z)) ∧
      t₀ ∈ Set.Ioo (-3 / 8 : ℝ) (-11 / 32) ∧
      ∀ ℓ : ℝ, 0 < ℓ →
        volume ((PDE.euclideanBall (0 : Vec d) (3 / 4) ×ˢ Set.Ioc (-7 / 8 : ℝ) t₀) ∩
          {z | (∫ y, w y t₀ ∂c8LogCutoffMeasure ρ) + ℓ < w z.1 z.2}) +
        volume ((PDE.euclideanBall (0 : Vec d) (3 / 4) ×ˢ Set.Ioc t₀ 0) ∩
          {z | w z.1 z.2 < (∫ y, w y t₀ ∂c8LogCutoffMeasure ρ) - ℓ}) ≤
        ((ENNReal.ofReal κ)⁻¹ * (ENNReal.ofReal κ⁻¹ * volume (sourceBall (0 : Vec d) 1))) *
          ENNReal.ofReal ((4 / c + 4 * K * (0 - (-7 / 8 : ℝ)) ^ 2) / ℓ) := by
  obtain ⟨w, hwm, hw⟩ := c8_log_measurable_representative hcal
  let m : ℝ → ℝ := fun q => ∫ x, Real.log (u (q,x)) ∂c8LogCutoffMeasure ρ
  let m' : ℝ → ℝ := fun q => ∫ x, w x q ∂c8LogCutoffMeasure ρ
  let V : ℝ → ℝ := fun q => ∫ x, (Real.log (u (q,x)) - m q) ^ 2 ∂c8LogCutoffMeasure ρ
  let V' : ℝ → ℝ := fun q => ∫ x, (w x q - m' q) ^ 2 ∂c8LogCutoffMeasure ρ
  obtain ⟨N₁, hN₁, hb⟩ := c8_variance_time_bound_congr V V' m m' N hN
    (c8_log_representative_ae_mean_variance hκ hell hw) hbound
  obtain ⟨N₂, hN₂, hl⟩ := c8_log_representative_good_slices hκ hell u G hε hcal hpositive hw
  let N' := N₁ ∪ N₂
  have hN' : volume N' = 0 := measure_union_null hN₁ hN₂
  obtain ⟨t₀, ht₀, ht₀N⟩ := PDE.Parabolic.WeakHarnack.exists_levelTime hN'
  have hV : IntervalIntegrable V' volume (-7 / 8) 0 := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).2
    apply IntegrableOn.mono_set (c8_log_representative_variance_integrable hκ hell u G hε hcal hpositive hw)
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  refine ⟨w, t₀, hwm, hw, ht₀, ?_⟩
  intro ℓ hℓ
  apply c8_log_tail_volume hκ hell w hwm N' (by linarith [ht₀.1]) (by linarith [ht₀.2]) hc hK hN' ?_ hV ?_ ht₀N hℓ
  · intro t ht htN
    apply hl t ?_ (fun h => htN (Or.inr h))
    constructor <;> linarith [ht.1, ht.2]
  · intro s hs t ht hsN htN hst
    apply hb s ?_ t ?_ (fun h => hsN (Or.inl h)) (fun h => htN (Or.inl h)) hst.le
    all_goals constructor <;> linarith [hs.1, hs.2, ht.1, ht.2]


/-- The logarithmic cutoff is a compactly supported smooth test function in
 the unit source ball. -/
theorem c8_radial_cutoff_support (d : ℕ) :
    HasCompactSupport (PDE.Parabolic.WeakHarnack.radialCutoff d) ∧
    tsupport (PDE.Parabolic.WeakHarnack.radialCutoff d) ⊆ sourceBall (0 : Vec d) 1 := by
  have hs : tsupport (PDE.Parabolic.WeakHarnack.radialCutoff d) ⊆
      PDE.euclideanClosedBall (0 : Vec d) (7 / 8) := by
    apply closure_minimal ?_ (PDE.isClosed_euclideanClosedBall _ _)
    intro x hx
    by_contra h
    have hz : PDE.Parabolic.WeakHarnack.radialCutoff d x = 0 :=
      PDE.Parabolic.WeakHarnack.radialCutoff_eq_zero (fun hxball =>
        h (PDE.euclideanBall_subset_euclideanClosedBall _ _ hxball))
    exact hx hz
  refine ⟨(PDE.isCompact_euclideanClosedBall (0 : Vec d) (by norm_num)).of_isClosed_subset
    (isClosed_tsupport _) hs, ?_⟩
  rw [c8_sourceBall_eq_euclideanBall 0 (by norm_num)]
  exact hs.trans (PDE.euclideanClosedBall_subset_euclideanBall (by norm_num) (by norm_num))


/-- Restrict the two logarithmic slab tails to the cylinders used in the
weak Harnack iteration. -/
theorem c8_log_slab_tail_to_cylinders {d : ℕ} {t₀ k : ℝ} (B : ℝ → ℝ≥0∞)
    (ht₀ : t₀ ∈ Set.Ioo (-3 / 8 : ℝ) (-11 / 32))
    (w : Vec d → ℝ → ℝ)
    (htail : ∀ ℓ : ℝ, 0 < ℓ →
      volume ((PDE.euclideanBall (0 : Vec d) (3 / 4) ×ˢ Set.Ioc (-7 / 8 : ℝ) t₀) ∩
        {z | k + ℓ < w z.1 z.2}) +
      volume ((PDE.euclideanBall (0 : Vec d) (3 / 4) ×ˢ Set.Ioc t₀ 0) ∩
        {z | w z.1 z.2 < k - ℓ}) ≤ B ℓ) :
    ∀ ℓ : ℝ, 0 < ℓ →
      volume (PDE.Parabolic.WeakHarnack.posCyl d 1 ∩ {z | k + ℓ < w z.1 z.2}) +
      volume (PDE.Parabolic.WeakHarnack.negCyl d 1 ∩ {z | w z.1 z.2 < k - ℓ}) ≤
        B ℓ := by
  intro ℓ hℓ
  apply (add_le_add ?_ ?_).trans (htail ℓ hℓ)
  · exact measure_mono (Set.inter_subset_inter_left _
      (PDE.Parabolic.WeakHarnack.posCyl_one_subset_slab ht₀.1.le))
  · exact measure_mono (Set.inter_subset_inter_left _
      (PDE.Parabolic.WeakHarnack.negCyl_one_subset_slab ht₀.2.le))


/-- A positive weighted caloric function has a measurable, everywhere positive
representative in spatial-time order. -/
theorem c8_positive_measurable_representative {d : ℕ}
    (u : ℝ × Vec d → ℝ) {ε : ℝ} (hε : 0 < ε)
    (w : Vec d → ℝ → ℝ) (hwm : Measurable (fun z : Vec d × ℝ => w z.1 z.2))
    (hw : ∀ᵐ z ∂volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1),
      w z.2 z.1 = Real.log (u z))
    (hpositive : ∀ᵐ z ∂volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1), ε ≤ u z) :
    ∃ v : Vec d → ℝ → ℝ,
      v = (fun x t => max ε (Real.exp (w x t))) ∧
      Measurable (fun z : Vec d × ℝ => v z.1 z.2) ∧
      (∀ x t, ε ≤ v x t) ∧
      (∀ᵐ z ∂volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1),
        v z.2 z.1 = u z) := by
  refine ⟨fun x t => max ε (Real.exp (w x t)), rfl, ?_, ?_, ?_⟩
  · exact measurable_const.max (Real.measurable_exp.comp hwm)
  · intro x t
    exact le_max_left _ _
  · filter_upwards [hw, hpositive] with z hz hp
    simp only [hz, Real.exp_log (hε.trans_le hp), max_eq_right hp]


/-- Clipping the exponential representative preserves the lower log tail. -/
theorem c8_log_clipped_exp_ge (ε r : ℝ) :
    r ≤ Real.log (max ε (Real.exp r)) := by
  have h := Real.log_le_log (Real.exp_pos r) (le_max_right ε (Real.exp r))
  simpa only [Real.log_exp] using h


/-- The clipped representative's lower logarithmic tail is bounded by that
of the original logarithmic representative. -/
theorem c8_clipped_lower_log_tail_le {d : ℕ} (w : Vec d → ℝ → ℝ)
    (ε k ℓ : ℝ) :
    volume (PDE.Parabolic.WeakHarnack.negCyl d 1 ∩
      {z | Real.log (max ε (Real.exp (w z.1 z.2))) < k - ℓ}) ≤
    volume (PDE.Parabolic.WeakHarnack.negCyl d 1 ∩
      {z | w z.1 z.2 < k - ℓ}) := by
  apply measure_mono (Set.inter_subset_inter_right _ ?_)
  intro z hz
  exact lt_of_le_of_lt (c8_log_clipped_exp_ge ε (w z.1 z.2)) hz


/-- Put the cutoff dissipation in the order used by the variance estimate. -/
theorem c8_radial_log_energy_reorder {d : ℕ} (κ : ℝ)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d) (E : ℝ → ℝ)
    (s t K : ℝ)
    (henergy :
      (κ / 2) * (∫ q in s..t, ∫ x in sourceBall (0 : Vec d) 1,
        PDE.Parabolic.WeakHarnack.radialCutoff d x ^ 2 *
          euclideanSq ((u (q,x))⁻¹ • G (q,x))) ≤ E t - E s + K * (t - s)) :
      (κ / 2) * (∫ q in s..t, ∫ x in sourceBall (0 : Vec d) 1,
        PDE.vecNormSq ((u (q,x))⁻¹ • G (q,x)) *
          PDE.Parabolic.WeakHarnack.radialCutoff d x ^ 2) ≤ E t - E s + K * (t - s) := by
  have heq : (∫ q in s..t, ∫ x in sourceBall (0 : Vec d) 1,
      PDE.vecNormSq ((u (q,x))⁻¹ • G (q,x)) *
        PDE.Parabolic.WeakHarnack.radialCutoff d x ^ 2) =
    (∫ q in s..t, ∫ x in sourceBall (0 : Vec d) 1,
      PDE.Parabolic.WeakHarnack.radialCutoff d x ^ 2 *
        euclideanSq ((u (q,x))⁻¹ • G (q,x))) := by
    apply intervalIntegral.integral_congr
    intro q _
    apply integral_congr_ae
    filter_upwards [] with x
    exact mul_comm _ _
  rw [heq]
  exact henergy


/-- Uniform logarithmic energy gives a logarithmic volume tail with constants
independent of the coefficient fields and of the positive solution. -/
theorem c8_uniform_log_tail_of_energy (d : ℕ) {κ : ℝ} (hκ : 0 < κ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
      IsUniformlyElliptic κ ρ α → ∀ (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
      {ε : ℝ}, 0 < ε →
      IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1) u G →
      (∀ᵐ z ∂volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1), ε ≤ u z) →
      ∀ (E : ℝ → ℝ) (K : ℝ), 0 ≤ K →
      (∀ᵐ q ∂volume.restrict (Set.Ioo (-1 : ℝ) 1),
        E q = ∫ x in sourceBall (0 : Vec d) 1,
          ρ x * PDE.Parabolic.WeakHarnack.radialCutoff d x ^ 2 * Real.log (u (q,x))) →
      (∀ s ∈ Set.Ioo (-1 : ℝ) 1, ∀ t ∈ Set.Ioo (-1 : ℝ) 1, s ≤ t →
        (κ / 2) * (∫ q in s..t, ∫ x in sourceBall (0 : Vec d) 1,
          PDE.vecNormSq ((u (q,x))⁻¹ • G (q,x)) *
            PDE.Parabolic.WeakHarnack.radialCutoff d x ^ 2) ≤ E t - E s + K * (t - s)) →
      let L := κ * (volume (PDE.euclideanBall (0 : Vec d) (3 / 4))).toReal
      let U := κ⁻¹ * (volume (sourceBall (0 : Vec d) 1)).toReal
      ∃ (w : Vec d → ℝ → ℝ) (t₀ : ℝ),
        Measurable (fun z : Vec d × ℝ => w z.1 z.2) ∧
        (∀ᵐ z ∂volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1),
          w z.2 z.1 = Real.log (u z)) ∧
        t₀ ∈ Set.Ioo (-3 / 8 : ℝ) (-11 / 32) ∧
        ∀ ℓ : ℝ, 0 < ℓ →
          volume ((PDE.euclideanBall (0 : Vec d) (3 / 4) ×ˢ Set.Ioc (-7 / 8 : ℝ) t₀) ∩
            {z | (∫ y, w y t₀ ∂c8LogCutoffMeasure ρ) + ℓ < w z.1 z.2}) +
          volume ((PDE.euclideanBall (0 : Vec d) (3 / 4) ×ˢ Set.Ioc t₀ 0) ∩
            {z | w z.1 z.2 < (∫ y, w y t₀ ∂c8LogCutoffMeasure ρ) - ℓ}) ≤
          ((ENNReal.ofReal κ)⁻¹ * (ENNReal.ofReal κ⁻¹ * volume (sourceBall (0 : Vec d) 1))) *
            ENNReal.ofReal ((4 / ((κ / 2 / U) / C) +
              4 * (K / L) * (0 - (-7 / 8 : ℝ)) ^ 2) / ℓ) := by
  obtain ⟨C, hC, hbound⟩ := c8_uniform_log_variance_time_bound d hκ
  refine ⟨C, hC, ?_⟩
  intro ρ α hell u G ε hε hcal hpositive E K hK hE henergy
  obtain ⟨N, hN, hNbound⟩ := hbound ρ α hell u G hε hcal hpositive E K hK hE henergy
  have hvol : 0 < (volume (sourceBall (0 : Vec d) 1)).toReal := by
    rw [c8_sourceBall_eq_euclideanBall 0 (by norm_num)]
    exact PDE.volume_euclideanBall_toReal_pos 0 (by norm_num)
  have hL : 0 < κ * (volume (PDE.euclideanBall (0 : Vec d) (3 / 4))).toReal :=
    mul_pos hκ (PDE.volume_euclideanBall_toReal_pos 0 (by norm_num))
  have hU : 0 < κ⁻¹ * (volume (sourceBall (0 : Vec d) 1)).toReal :=
    mul_pos (inv_pos.mpr hκ) hvol
  exact c8_log_tail_of_variance_bound hκ hell u G hε hcal hpositive
    (div_pos (div_pos (by positivity) hU) hC) (div_nonneg hK hL.le) N hN hNbound


/-- The native logarithmic energy balance supplies the radial cutoff estimate
with an error depending only on the dimension and ellipticity. -/
theorem c8_radial_log_energy {d : ℕ} {κ : ℝ} (hκ : 0 < κ)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d) (hell : IsUniformlyElliptic κ ρ α)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d) {ε : ℝ} (hε : 0 < ε)
    (hcal : IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1) u G)
    (hpositive : ∀ᵐ z ∂volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1), ε ≤ u z) :
    let K := (2 / κ ^ 3) * (∫ x in sourceBall (0 : Vec d) 1,
      euclideanSq (fun j => fderiv ℝ (PDE.Parabolic.WeakHarnack.radialCutoff d) x (unitVector j)))
    0 ≤ K ∧ ∃ E : ℝ → ℝ,
      (∀ᵐ q ∂volume.restrict (Set.Ioo (-1 : ℝ) 1),
        E q = ∫ x in sourceBall (0 : Vec d) 1,
          ρ x * PDE.Parabolic.WeakHarnack.radialCutoff d x ^ 2 * Real.log (u (q,x))) ∧
      ∀ s ∈ Set.Ioo (-1 : ℝ) 1, ∀ t ∈ Set.Ioo (-1 : ℝ) 1, s ≤ t →
        (κ / 2) * (∫ q in s..t, ∫ x in sourceBall (0 : Vec d) 1,
          PDE.vecNormSq ((u (q,x))⁻¹ • G (q,x)) *
            PDE.Parabolic.WeakHarnack.radialCutoff d x ^ 2) ≤ E t - E s + K * (t - s) := by
  have hs := c8_radial_cutoff_support d
  obtain ⟨E, _, hE, henergy⟩ := c16_weighted_caloric_log_energy_balance hκ
    (by norm_num) (by norm_num) hε ρ α hell u G hcal hpositive
    (PDE.Parabolic.WeakHarnack.radialCutoff d)
    (PDE.Parabolic.WeakHarnack.radialCutoff_contDiff d) hs.1 hs.2
  constructor
  · apply mul_nonneg (by positivity)
    exact integral_nonneg (fun x => PDE.vecNormSq_nonneg _)
  · refine ⟨E, hE, ?_⟩
    intro s hs t ht hst
    apply c8_radial_log_energy_reorder κ u G E s t
    convert henergy s hs t ht hst using 1 <;> ring


/-- A strictly positive weighted caloric function satisfies the uniform
logarithmic slab tail estimate. -/
theorem c8_uniform_actual_log_tail (d : ℕ) {κ : ℝ} (hκ : 0 < κ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
      IsUniformlyElliptic κ ρ α → ∀ (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
      {ε : ℝ}, 0 < ε →
      IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1) u G →
      (∀ᵐ z ∂volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1), ε ≤ u z) →
      let K := (2 / κ ^ 3) * (∫ x in sourceBall (0 : Vec d) 1,
        euclideanSq (fun j => fderiv ℝ (PDE.Parabolic.WeakHarnack.radialCutoff d) x (unitVector j)))
      let L := κ * (volume (PDE.euclideanBall (0 : Vec d) (3 / 4))).toReal
      let U := κ⁻¹ * (volume (sourceBall (0 : Vec d) 1)).toReal
      ∃ (w : Vec d → ℝ → ℝ) (t₀ : ℝ),
        Measurable (fun z : Vec d × ℝ => w z.1 z.2) ∧
        (∀ᵐ z ∂volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1),
          w z.2 z.1 = Real.log (u z)) ∧
        t₀ ∈ Set.Ioo (-3 / 8 : ℝ) (-11 / 32) ∧
        ∀ ℓ : ℝ, 0 < ℓ →
          volume ((PDE.euclideanBall (0 : Vec d) (3 / 4) ×ˢ Set.Ioc (-7 / 8 : ℝ) t₀) ∩
            {z | (∫ y, w y t₀ ∂c8LogCutoffMeasure ρ) + ℓ < w z.1 z.2}) +
          volume ((PDE.euclideanBall (0 : Vec d) (3 / 4) ×ˢ Set.Ioc t₀ 0) ∩
            {z | w z.1 z.2 < (∫ y, w y t₀ ∂c8LogCutoffMeasure ρ) - ℓ}) ≤
          ((ENNReal.ofReal κ)⁻¹ * (ENNReal.ofReal κ⁻¹ * volume (sourceBall (0 : Vec d) 1))) *
            ENNReal.ofReal ((4 / ((κ / 2 / U) / C) +
              4 * (K / L) * (0 - (-7 / 8 : ℝ)) ^ 2) / ℓ) := by
  obtain ⟨C, hC, htail⟩ := c8_uniform_log_tail_of_energy d hκ
  refine ⟨C, hC, ?_⟩
  intro ρ α hell u G ε hε hcal hpositive
  obtain ⟨hK, E, hE, henergy⟩ := c8_radial_log_energy hκ ρ α hell u G hε hcal hpositive
  exact htail ρ α hell u G hε hcal hpositive E _ hK hE henergy


/-- Extend the logarithmic tail to the later target time. -/
theorem c8_log_tail_of_variance_bound_late {d : ℕ} {κ : ℝ} (hκ : 0 < κ)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (hell : IsUniformlyElliptic κ ρ α)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d) {ε : ℝ} (hε : 0 < ε)
    (hcal : IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1) u G)
    (hpositive : ∀ᵐ z ∂volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1), ε ≤ u z)
    {c K : ℝ} (hc : 0 < c) (hK : 0 ≤ K) (N : Set ℝ) (hN : volume N = 0)
    (hbound : ∀ s ∈ Set.Ioo (-1 : ℝ) 1, ∀ t ∈ Set.Ioo (-1 : ℝ) 1,
      s ∉ N → t ∉ N → s ≤ t →
      ∫ q in s..t, (c * ∫ x, (Real.log (u (q,x)) -
        ∫ y, Real.log (u (q,y)) ∂c8LogCutoffMeasure ρ) ^ 2 ∂c8LogCutoffMeasure ρ - K) ≤
        (∫ x, Real.log (u (t,x)) ∂c8LogCutoffMeasure ρ) -
          ∫ x, Real.log (u (s,x)) ∂c8LogCutoffMeasure ρ) :
    ∃ (w : Vec d → ℝ → ℝ) (t₀ : ℝ),
      Measurable (fun z : Vec d × ℝ => w z.1 z.2) ∧
      (∀ᵐ z ∂volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1),
        w z.2 z.1 = Real.log (u z)) ∧
      t₀ ∈ Set.Ioo (-3 / 8 : ℝ) (-11 / 32) ∧
      ∀ ℓ : ℝ, 0 < ℓ →
        volume ((PDE.euclideanBall (0 : Vec d) (3 / 4) ×ˢ Set.Ioc (-7 / 8 : ℝ) t₀) ∩
          {z | (∫ y, w y t₀ ∂c8LogCutoffMeasure ρ) + ℓ < w z.1 z.2}) +
        volume ((PDE.euclideanBall (0 : Vec d) (3 / 4) ×ˢ Set.Ioc t₀ (3 / 4)) ∩
          {z | w z.1 z.2 < (∫ y, w y t₀ ∂c8LogCutoffMeasure ρ) - ℓ}) ≤
        ((ENNReal.ofReal κ)⁻¹ * (ENNReal.ofReal κ⁻¹ * volume (sourceBall (0 : Vec d) 1))) *
          ENNReal.ofReal ((4 / c + 4 * K * ((3 / 4 : ℝ) - (-7 / 8 : ℝ)) ^ 2) / ℓ) := by
  obtain ⟨w, hwm, hw⟩ := c8_log_measurable_representative hcal
  let m : ℝ → ℝ := fun q => ∫ x, Real.log (u (q,x)) ∂c8LogCutoffMeasure ρ
  let m' : ℝ → ℝ := fun q => ∫ x, w x q ∂c8LogCutoffMeasure ρ
  let V : ℝ → ℝ := fun q => ∫ x, (Real.log (u (q,x)) - m q) ^ 2 ∂c8LogCutoffMeasure ρ
  let V' : ℝ → ℝ := fun q => ∫ x, (w x q - m' q) ^ 2 ∂c8LogCutoffMeasure ρ
  obtain ⟨N₁, hN₁, hb⟩ := c8_variance_time_bound_congr V V' m m' N hN
    (c8_log_representative_ae_mean_variance hκ hell hw) hbound
  obtain ⟨N₂, hN₂, hl⟩ := c8_log_representative_good_slices hκ hell u G hε hcal hpositive hw
  let N' := N₁ ∪ N₂
  have hN' : volume N' = 0 := measure_union_null hN₁ hN₂
  obtain ⟨t₀, ht₀, ht₀N⟩ := PDE.Parabolic.WeakHarnack.exists_levelTime hN'
  have hV : IntervalIntegrable V' volume (-7 / 8) (3 / 4) := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).2
    apply IntegrableOn.mono_set (c8_log_representative_variance_integrable hκ hell u G hε hcal hpositive hw)
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  refine ⟨w, t₀, hwm, hw, ht₀, ?_⟩
  intro ℓ hℓ
  apply c8_log_tail_volume hκ hell w hwm N' (by linarith [ht₀.1]) (by linarith [ht₀.2]) hc hK hN' ?_ hV ?_ ht₀N hℓ
  · intro t ht htN
    apply hl t ?_ (fun h => htN (Or.inr h))
    constructor <;> linarith [ht.1, ht.2]
  · intro s hs t ht hsN htN hst
    apply hb s ?_ t ?_ (fun h => hsN (Or.inl h)) (fun h => htN (Or.inl h)) hst.le
    all_goals constructor <;> linarith [hs.1, hs.2, ht.1, ht.2]


/-- Uniform energy controls the tail through the later target time. -/
theorem c8_uniform_log_tail_of_energy_late (d : ℕ) {κ : ℝ} (hκ : 0 < κ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
      IsUniformlyElliptic κ ρ α → ∀ (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
      {ε : ℝ}, 0 < ε →
      IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1) u G →
      (∀ᵐ z ∂volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1), ε ≤ u z) →
      ∀ (E : ℝ → ℝ) (K : ℝ), 0 ≤ K →
      (∀ᵐ q ∂volume.restrict (Set.Ioo (-1 : ℝ) 1),
        E q = ∫ x in sourceBall (0 : Vec d) 1,
          ρ x * PDE.Parabolic.WeakHarnack.radialCutoff d x ^ 2 * Real.log (u (q,x))) →
      (∀ s ∈ Set.Ioo (-1 : ℝ) 1, ∀ t ∈ Set.Ioo (-1 : ℝ) 1, s ≤ t →
        (κ / 2) * (∫ q in s..t, ∫ x in sourceBall (0 : Vec d) 1,
          PDE.vecNormSq ((u (q,x))⁻¹ • G (q,x)) *
            PDE.Parabolic.WeakHarnack.radialCutoff d x ^ 2) ≤ E t - E s + K * (t - s)) →
      let L := κ * (volume (PDE.euclideanBall (0 : Vec d) (3 / 4))).toReal
      let U := κ⁻¹ * (volume (sourceBall (0 : Vec d) 1)).toReal
      ∃ (w : Vec d → ℝ → ℝ) (t₀ : ℝ),
        Measurable (fun z : Vec d × ℝ => w z.1 z.2) ∧
        (∀ᵐ z ∂volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1),
          w z.2 z.1 = Real.log (u z)) ∧
        t₀ ∈ Set.Ioo (-3 / 8 : ℝ) (-11 / 32) ∧
        ∀ ℓ : ℝ, 0 < ℓ →
          volume ((PDE.euclideanBall (0 : Vec d) (3 / 4) ×ˢ Set.Ioc (-7 / 8 : ℝ) t₀) ∩
            {z | (∫ y, w y t₀ ∂c8LogCutoffMeasure ρ) + ℓ < w z.1 z.2}) +
          volume ((PDE.euclideanBall (0 : Vec d) (3 / 4) ×ˢ Set.Ioc t₀ (3 / 4)) ∩
            {z | w z.1 z.2 < (∫ y, w y t₀ ∂c8LogCutoffMeasure ρ) - ℓ}) ≤
          ((ENNReal.ofReal κ)⁻¹ * (ENNReal.ofReal κ⁻¹ * volume (sourceBall (0 : Vec d) 1))) *
            ENNReal.ofReal ((4 / ((κ / 2 / U) / C) +
              4 * (K / L) * ((3 / 4 : ℝ) - (-7 / 8 : ℝ)) ^ 2) / ℓ) := by
  obtain ⟨C, hC, hbound⟩ := c8_uniform_log_variance_time_bound d hκ
  refine ⟨C, hC, ?_⟩
  intro ρ α hell u G ε hε hcal hpositive E K hK hE henergy
  obtain ⟨N, hN, hNbound⟩ := hbound ρ α hell u G hε hcal hpositive E K hK hE henergy
  have hvol : 0 < (volume (sourceBall (0 : Vec d) 1)).toReal := by
    rw [c8_sourceBall_eq_euclideanBall 0 (by norm_num)]
    exact PDE.volume_euclideanBall_toReal_pos 0 (by norm_num)
  have hL : 0 < κ * (volume (PDE.euclideanBall (0 : Vec d) (3 / 4))).toReal :=
    mul_pos hκ (PDE.volume_euclideanBall_toReal_pos 0 (by norm_num))
  have hU : 0 < κ⁻¹ * (volume (sourceBall (0 : Vec d) 1)).toReal :=
    mul_pos (inv_pos.mpr hκ) hvol
  exact c8_log_tail_of_variance_bound_late hκ hell u G hε hcal hpositive
    (div_pos (div_pos (by positivity) hU) hC) (div_nonneg hK hL.le) N hN hNbound


/-- Actual logarithmic tails cover the later target time. -/
theorem c8_uniform_actual_log_tail_late (d : ℕ) {κ : ℝ} (hκ : 0 < κ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
      IsUniformlyElliptic κ ρ α → ∀ (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
      {ε : ℝ}, 0 < ε →
      IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1) u G →
      (∀ᵐ z ∂volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1), ε ≤ u z) →
      let K := (2 / κ ^ 3) * (∫ x in sourceBall (0 : Vec d) 1,
        euclideanSq (fun j => fderiv ℝ (PDE.Parabolic.WeakHarnack.radialCutoff d) x (unitVector j)))
      let L := κ * (volume (PDE.euclideanBall (0 : Vec d) (3 / 4))).toReal
      let U := κ⁻¹ * (volume (sourceBall (0 : Vec d) 1)).toReal
      ∃ (w : Vec d → ℝ → ℝ) (t₀ : ℝ),
        Measurable (fun z : Vec d × ℝ => w z.1 z.2) ∧
        (∀ᵐ z ∂volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1),
          w z.2 z.1 = Real.log (u z)) ∧
        t₀ ∈ Set.Ioo (-3 / 8 : ℝ) (-11 / 32) ∧
        ∀ ℓ : ℝ, 0 < ℓ →
          volume ((PDE.euclideanBall (0 : Vec d) (3 / 4) ×ˢ Set.Ioc (-7 / 8 : ℝ) t₀) ∩
            {z | (∫ y, w y t₀ ∂c8LogCutoffMeasure ρ) + ℓ < w z.1 z.2}) +
          volume ((PDE.euclideanBall (0 : Vec d) (3 / 4) ×ˢ Set.Ioc t₀ (3 / 4)) ∩
            {z | w z.1 z.2 < (∫ y, w y t₀ ∂c8LogCutoffMeasure ρ) - ℓ}) ≤
          ((ENNReal.ofReal κ)⁻¹ * (ENNReal.ofReal κ⁻¹ * volume (sourceBall (0 : Vec d) 1))) *
            ENNReal.ofReal ((4 / ((κ / 2 / U) / C) +
              4 * (K / L) * ((3 / 4 : ℝ) - (-7 / 8 : ℝ)) ^ 2) / ℓ) := by
  obtain ⟨C, hC, htail⟩ := c8_uniform_log_tail_of_energy_late d hκ
  refine ⟨C, hC, ?_⟩
  intro ρ α hell u G ε hε hcal hpositive
  obtain ⟨hK, E, hE, henergy⟩ := c8_radial_log_energy hκ ρ α hell u G hε hcal hpositive
  exact htail ρ α hell u G hε hcal hpositive E _ hK hE henergy


/-- The negative-power cylinders shifted to the later part of the source
cylinder. -/
def c8LateNegCyl (d : ℕ) (σ : ℝ) : Set (Vec d × ℝ) :=
  {z | (z.1, z.2 - 3 / 4) ∈ PDE.Parabolic.WeakHarnack.negCyl d σ}

/-- The shifted outer cylinder lies in the later logarithmic slab. -/
theorem c8_lateNegCyl_one_subset_slab {d : ℕ} {t₀ : ℝ}
    (ht₀ : t₀ ≤ -11 / 32) :
    c8LateNegCyl d 1 ⊆ PDE.euclideanBall (0 : Vec d) (3 / 4) ×ˢ Set.Ioc t₀ (3 / 4) := by
  intro z hz
  change (z.1, z.2 - 3 / 4) ∈ PDE.Parabolic.WeakHarnack.negCyl d 1 at hz
  have h := PDE.Parabolic.WeakHarnack.negCyl_one_subset_slab
    (d := d) (t₀ := t₀ - 3 / 4) (by linarith) hz
  exact ⟨h.1, by constructor <;> linarith [h.2.1, h.2.2]⟩


/-- The shifted inner negative-power cylinders. -/
def c8LateNegCylInner (d : ℕ) (σ : ℝ) : Set (Vec d × ℝ) :=
  {z | (z.1, z.2 - 3 / 4) ∈ PDE.Parabolic.WeakHarnack.negCylInner d σ}

/-- The innermost shifted cylinder has exactly the target time interval,
up to its harmless right-closed endpoint. -/
theorem c8_lateNegCylInner_half (d : ℕ) :
    c8LateNegCylInner d (1 / 2) =
      PDE.euclideanBall (0 : Vec d) (1 / 2) ×ˢ Set.Ioc (1 / 2 : ℝ) (3 / 4) := by
  ext ⟨x, t⟩
  simp only [c8LateNegCylInner, Set.mem_setOf_eq,
    PDE.Parabolic.WeakHarnack.negCylInner_half, Set.mem_prod, Set.mem_Ioc]
  constructor <;> rintro ⟨hx, h1, h2⟩ <;> refine ⟨hx, ?_, ?_⟩ <;> linarith


/-- The extended slab tails restrict to the early and shifted late cylinders. -/
theorem c8_log_slab_tail_to_late_cylinders {d : ℕ} {t₀ k : ℝ} (B : ℝ → ℝ≥0∞)
    (ht₀ : t₀ ∈ Set.Ioo (-3 / 8 : ℝ) (-11 / 32))
    (w : Vec d → ℝ → ℝ)
    (htail : ∀ ℓ : ℝ, 0 < ℓ →
      volume ((PDE.euclideanBall (0 : Vec d) (3 / 4) ×ˢ Set.Ioc (-7 / 8 : ℝ) t₀) ∩
        {z | k + ℓ < w z.1 z.2}) +
      volume ((PDE.euclideanBall (0 : Vec d) (3 / 4) ×ˢ Set.Ioc t₀ (3 / 4)) ∩
        {z | w z.1 z.2 < k - ℓ}) ≤ B ℓ) :
    ∀ ℓ : ℝ, 0 < ℓ →
      volume (PDE.Parabolic.WeakHarnack.posCyl d 1 ∩ {z | k + ℓ < w z.1 z.2}) +
      volume (c8LateNegCyl d 1 ∩ {z | w z.1 z.2 < k - ℓ}) ≤ B ℓ := by
  intro ℓ hℓ
  apply (add_le_add ?_ ?_).trans (htail ℓ hℓ)
  · exact measure_mono (Set.inter_subset_inter_left _
      (PDE.Parabolic.WeakHarnack.posCyl_one_subset_slab ht₀.1.le))
  · exact measure_mono (Set.inter_subset_inter_left _
      (c8_lateNegCyl_one_subset_slab ht₀.2.le))

/-- A regularized early-power bound passes to the unshifted function. -/
theorem c8_weak_harnack_remove_epsilon {d : ℕ} {p C : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (u : ℝ × Vec d → ℝ)
    (hu : MemLp u 2 (volume.restrict
      (Set.Ioo (-3/4 : ℝ) (-1/2) ×ˢ sourceBall 0 (1/2))))
    (hbound : ∀ ε : ℝ, 0 < ε →
      Real.rpow (∫ z in Set.Ioo (-3/4 : ℝ) (-1/2) ×ˢ sourceBall 0 (1/2),
        Real.rpow (|u z| + ε) p) p⁻¹ ≤
      C * (essInf u (volume.restrict
        (Set.Ioo (1/2 : ℝ) (3/4) ×ˢ sourceBall 0 (1/2))) + ε)) :
    Real.rpow (∫ z in Set.Ioo (-3/4 : ℝ) (-1/2) ×ˢ sourceBall 0 (1/2),
      Real.rpow |u z| p) p⁻¹ ≤
      C * essInf u (volume.restrict
        (Set.Ioo (1/2 : ℝ) (3/4) ×ˢ sourceBall 0 (1/2))) := by
  have heps : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  have hint := c8_weak_harnack_epsilon_integral_limit (d := d)
    (a := -3/4) (b := -1/2) (r := 1/2) (by norm_num) (by norm_num) hp hp1 u hu
  have hl := (Real.continuous_rpow_const (inv_nonneg.mpr hp.le)).tendsto _ |>.comp hint
  have hr : Tendsto (fun n : ℕ => C * (essInf u (volume.restrict
      (Set.Ioo (1/2 : ℝ) (3/4) ×ˢ sourceBall 0 (1/2))) + ((n : ℝ) + 1)⁻¹))
      atTop (𝓝 (C * (essInf u (volume.restrict
      (Set.Ioo (1/2 : ℝ) (3/4) ×ˢ sourceBall 0 (1/2))) + 0))) :=
    tendsto_const_nhds.mul (tendsto_const_nhds.add heps)
  have hb : ∀ n : ℕ,
      Real.rpow (∫ z in Set.Ioo (-3/4 : ℝ) (-1/2) ×ˢ sourceBall 0 (1/2),
        Real.rpow (|u z| + ((n : ℝ) + 1)⁻¹) p) p⁻¹ ≤
      C * (essInf u (volume.restrict
        (Set.Ioo (1/2 : ℝ) (3/4) ×ˢ sourceBall 0 (1/2))) + ((n : ℝ) + 1)⁻¹) := by
    intro n
    exact hbound _ (by positivity)
  have h := le_of_tendsto_of_tendsto hl hr (Filter.Eventually.of_forall hb)
  simpa only [add_zero, Real.rpow_eq_pow] using h

/-- Actual weighted solutions have uniform log tails on the Harnack cylinders. -/
theorem c8_uniform_actual_cylinder_log_tail (d : ℕ) {κ : ℝ} (hκ : 0 < κ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
      IsUniformlyElliptic κ ρ α → ∀ (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
      {ε : ℝ}, 0 < ε →
      IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1) u G →
      (∀ᵐ z ∂volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1), ε ≤ u z) →
      let K := (2 / κ ^ 3) * (∫ x in sourceBall (0 : Vec d) 1,
        euclideanSq (fun j => fderiv ℝ (PDE.Parabolic.WeakHarnack.radialCutoff d) x (unitVector j)))
      let L := κ * (volume (PDE.euclideanBall (0 : Vec d) (3 / 4))).toReal
      let U := κ⁻¹ * (volume (sourceBall (0 : Vec d) 1)).toReal
      ∃ (w : Vec d → ℝ → ℝ) (k : ℝ),
        Measurable (fun z : Vec d × ℝ => w z.1 z.2) ∧
        (∀ᵐ z ∂volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1),
          w z.2 z.1 = Real.log (u z)) ∧
        ∀ ℓ : ℝ, 0 < ℓ →
          volume (PDE.Parabolic.WeakHarnack.posCyl d 1 ∩ {z | k + ℓ < w z.1 z.2}) +
          volume (c8LateNegCyl d 1 ∩ {z | w z.1 z.2 < k - ℓ}) ≤
          ((ENNReal.ofReal κ)⁻¹ * (ENNReal.ofReal κ⁻¹ * volume (sourceBall (0 : Vec d) 1))) *
            ENNReal.ofReal ((4 / ((κ / 2 / U) / C) +
              4 * (K / L) * ((3 / 4 : ℝ) - (-7 / 8 : ℝ)) ^ 2) / ℓ) := by
  obtain ⟨C, hC, htail⟩ := c8_uniform_actual_log_tail_late d hκ
  refine ⟨C, hC, ?_⟩
  intro ρ α hell u G ε hε hcal hpos
  obtain ⟨w, t₀, hw, hweq, ht₀, hbound⟩ := htail ρ α hell u G hε hcal hpos
  refine ⟨w, ∫ y, w y t₀ ∂c8LogCutoffMeasure ρ, hw, hweq, ?_⟩
  exact c8_log_slab_tail_to_late_cylinders _ ht₀ w hbound

/-- A positive measurable representative retains both uniform logarithmic tails. -/
theorem c8_uniform_positive_representative_log_tail (d : ℕ) {κ : ℝ} (hκ : 0 < κ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
      IsUniformlyElliptic κ ρ α → ∀ (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
      {ε : ℝ}, 0 < ε →
      IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1) u G →
      (∀ᵐ z ∂volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1), ε ≤ u z) →
      let K := (2 / κ ^ 3) * (∫ x in sourceBall (0 : Vec d) 1,
        euclideanSq (fun j => fderiv ℝ (PDE.Parabolic.WeakHarnack.radialCutoff d) x (unitVector j)))
      let L := κ * (volume (PDE.euclideanBall (0 : Vec d) (3 / 4))).toReal
      let U := κ⁻¹ * (volume (sourceBall (0 : Vec d) 1)).toReal
      ∃ (v : Vec d → ℝ → ℝ) (k : ℝ),
        Measurable (fun z : Vec d × ℝ => v z.1 z.2) ∧
        (∀ x t, 0 < v x t) ∧
        (∀ᵐ z ∂volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1),
          v z.2 z.1 = u z) ∧
        ∀ ℓ : ℝ, 0 < ℓ →
          volume (PDE.Parabolic.WeakHarnack.posCyl d 1 ∩ {z | k + ℓ < Real.log (v z.1 z.2)}) +
          volume (c8LateNegCyl d 1 ∩ {z | Real.log (v z.1 z.2) < k - ℓ}) ≤
          ((ENNReal.ofReal κ)⁻¹ * (ENNReal.ofReal κ⁻¹ * volume (sourceBall (0 : Vec d) 1))) *
            ENNReal.ofReal ((4 / ((κ / 2 / U) / C) +
              4 * (K / L) * ((3 / 4 : ℝ) - (-7 / 8 : ℝ)) ^ 2) / ℓ) := by
  obtain ⟨C, hC, htail⟩ := c8_uniform_actual_cylinder_log_tail d hκ
  refine ⟨C, hC, ?_⟩
  intro ρ α hell u G ε hε hcal hpos
  obtain ⟨w, k, hw, hweq, hbound⟩ := htail ρ α hell u G hε hcal hpos
  refine ⟨fun x t => Real.exp (w x t), k, Real.continuous_exp.measurable.comp hw,
    fun x t => Real.exp_pos _, ?_, ?_⟩
  · filter_upwards [hweq, hpos] with z hwz hpz
    rw [hwz, Real.exp_log (lt_of_lt_of_le hε hpz)]
  · intro ℓ hℓ
    simpa only [Real.log_exp] using hbound ℓ hℓ

/-- Normalize a two-cylinder logarithmic tail for the Bombieri–Giusti hypotheses. -/
theorem c8_normalized_two_cylinder_log_tail {d : ℕ}
    (S T : Set (Vec d × ℝ)) (hS : MeasurableSet S) (hT : MeasurableSet T)
    (hS0 : volume S ≠ 0) (hSt : volume S ≠ ⊤)
    (hT0 : volume T ≠ 0) (hTt : volume T ≠ ⊤)
    (v : Vec d × ℝ → ℝ) (hv : ∀ z, 0 < v z) {k D c₁ c₂ : ℝ}
    (htail : ∀ ℓ : ℝ, 0 < ℓ →
      volume (S ∩ {z | k + ℓ < Real.log (v z)}) +
        volume (T ∩ {z | Real.log (v z) < k - ℓ}) ≤ ENNReal.ofReal (D / ℓ))
    (hc₁ : D / (volume S).toReal ≤ c₁) (hc₂ : D / (volume T).toReal ≤ c₂) :
    (∀ ℓ : ℝ, 0 < ℓ → PDE.Parabolic.WeakHarnack.cylMeasure S
      (S ∩ {z | ℓ < Real.log (Real.exp (-k) * v z)}) ≤ ENNReal.ofReal (c₁ / ℓ)) ∧
    (∀ ℓ : ℝ, 0 < ℓ → PDE.Parabolic.WeakHarnack.cylMeasure T
      (T ∩ {z | ℓ < Real.log (Real.exp k / v z)}) ≤ ENNReal.ofReal (c₂ / ℓ)) := by
  constructor
  · intro ℓ hℓ
    have heq : S ∩ {z | ℓ < Real.log (Real.exp (-k) * v z)} =
        S ∩ {z | k + ℓ < Real.log (v z)} := by
      ext z
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq, and_congr_right_iff]
      intro _
      rw [Real.log_mul (Real.exp_pos _).ne' (hv z).ne', Real.log_exp]
      constructor <;> intro h <;> linarith
    rw [heq]
    exact PDE.Parabolic.WeakHarnack.cylMeasure_inter_le hS hS0 hSt hℓ
      (le_trans le_self_add (htail ℓ hℓ)) hc₁
  · intro ℓ hℓ
    have heq : T ∩ {z | ℓ < Real.log (Real.exp k / v z)} =
        T ∩ {z | Real.log (v z) < k - ℓ} := by
      ext z
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq, and_congr_right_iff]
      intro _
      rw [Real.log_div (Real.exp_pos _).ne' (hv z).ne', Real.log_exp]
      constructor <;> intro h <;> linarith
    rw [heq]
    exact PDE.Parabolic.WeakHarnack.cylMeasure_inter_le hT hT0 hTt hℓ
      (le_trans le_add_self (htail ℓ hℓ)) hc₂

/-- Combine the positive and reciprocal iterations with a common log center.
The two functions allow the late cylinder to be translated independently. -/
theorem c8_bombieri_two_sides {d : ℕ} {χ A₁ m₁ q A₂ β₂ m₂ A₃ β₃ m₃ k c₀ ε : ℝ}
    (hχ : 1 < χ) (hA₁ : 1 ≤ A₁) (hm₁ : 0 < m₁) (hq : 0 < q)
    (hA₂ : 1 ≤ A₂) (hβ₂ : 0 ≤ β₂) (hm₂ : 0 < m₂)
    (hA₃ : 1 ≤ A₃) (hβ₃ : 0 ≤ β₃) (hm₃ : 0 < m₃) (hε : 0 < ε)
    (v w : Vec d × ℝ → ℝ) (hv : Measurable v) (hw : Measurable w)
    (hvpos : ∀ z, 0 < v z) (hwε : ∀ z, ε ≤ w z)
    (hfin : eLpNorm v (ENNReal.ofReal (q * χ))
      ((PDE.Parabolic.WeakHarnack.cylMeasure (PDE.Parabolic.WeakHarnack.posCyl d 1)).restrict
        (PDE.Parabolic.WeakHarnack.posCyl d 1)) < ⊤)
    (hpos : ∀ σ' σ : ℝ, 1 / 2 ≤ σ' → σ' < σ → σ ≤ 1 → ∀ p : ℝ, 0 < p → p ≤ q →
      eLpNorm v (ENNReal.ofReal (χ * p))
        ((PDE.Parabolic.WeakHarnack.cylMeasure (PDE.Parabolic.WeakHarnack.posCyl d 1)).restrict
          (PDE.Parabolic.WeakHarnack.posCyl d σ')) ≤
      ENNReal.ofReal ((A₁ * (σ - σ') ^ (-m₁)) ^ (1 / p)) *
      eLpNorm v (ENNReal.ofReal p)
        ((PDE.Parabolic.WeakHarnack.cylMeasure (PDE.Parabolic.WeakHarnack.posCyl d 1)).restrict
          (PDE.Parabolic.WeakHarnack.posCyl d σ)))
    (hneg : ∀ σ' σ : ℝ, 1 / 2 ≤ σ' → σ' < σ → σ ≤ 1 → ∀ p : ℝ, 0 < p →
      eLpNorm (fun z => 1 / w z) (ENNReal.ofReal (χ * p))
        ((PDE.Parabolic.WeakHarnack.cylMeasure (PDE.Parabolic.WeakHarnack.negCyl d 1)).restrict
          (PDE.Parabolic.WeakHarnack.negCyl d σ')) ≤
      ENNReal.ofReal ((A₂ * (1 + p) ^ β₂ * (σ - σ') ^ (-m₂)) ^ (1 / p)) *
      eLpNorm (fun z => 1 / w z) (ENNReal.ofReal p)
        ((PDE.Parabolic.WeakHarnack.cylMeasure (PDE.Parabolic.WeakHarnack.negCyl d 1)).restrict
          (PDE.Parabolic.WeakHarnack.negCyl d σ)))
    (hinner : ∀ σ' σ : ℝ, 1 / 2 ≤ σ' → σ' < σ → σ ≤ 1 → ∀ p : ℝ, 0 < p →
      eLpNorm (fun z => 1 / w z) (ENNReal.ofReal (χ * p))
        ((PDE.Parabolic.WeakHarnack.cylMeasure (PDE.Parabolic.WeakHarnack.negCylInner d 1)).restrict
          (PDE.Parabolic.WeakHarnack.negCylInner d σ')) ≤
      ENNReal.ofReal ((A₃ * (1 + p) ^ β₃ * (σ - σ') ^ (-m₃)) ^ (1 / p)) *
      eLpNorm (fun z => 1 / w z) (ENNReal.ofReal p)
        ((PDE.Parabolic.WeakHarnack.cylMeasure (PDE.Parabolic.WeakHarnack.negCylInner d 1)).restrict
          (PDE.Parabolic.WeakHarnack.negCylInner d σ)))
    (hlogpos : ∀ ℓ : ℝ, 0 < ℓ →
      PDE.Parabolic.WeakHarnack.cylMeasure (PDE.Parabolic.WeakHarnack.posCyl d 1)
        (PDE.Parabolic.WeakHarnack.posCyl d 1 ∩
          {z | ℓ < Real.log (Real.exp (-k) * v z)}) ≤ ENNReal.ofReal (c₀ / ℓ))
    (hlogneg : ∀ ℓ : ℝ, 0 < ℓ →
      PDE.Parabolic.WeakHarnack.cylMeasure (PDE.Parabolic.WeakHarnack.negCyl d 1)
        (PDE.Parabolic.WeakHarnack.negCyl d 1 ∩
          {z | ℓ < Real.log (Real.exp k / w z)}) ≤ ENNReal.ofReal (c₀ / ℓ)) :
    eLpNorm v (ENNReal.ofReal (q * χ))
        ((PDE.Parabolic.WeakHarnack.cylMeasure (PDE.Parabolic.WeakHarnack.posCyl d 1)).restrict
          (PDE.Parabolic.WeakHarnack.posCyl d (1 / 2))) *
      eLpNorm (fun z => 1 / w z) ⊤
        ((PDE.Parabolic.WeakHarnack.cylMeasure (PDE.Parabolic.WeakHarnack.negCyl d 1)).restrict
          (PDE.Parabolic.WeakHarnack.negCylInner d (1 / 2))) ≤
      ENNReal.ofReal (PDE.Bombieri.giustiConst (1 / 2) (q * χ)
        (max c₀ (PDE.ParabIter.posC χ A₁ m₁ q)) (PDE.ParabIter.posM χ m₁ q) *
        PDE.Parabolic.WeakHarnack.negTopConst d χ A₂ β₂ m₂ A₃ β₃ m₃ c₀) := by
  have hp := PDE.Parabolic.WeakHarnack.pos_side hχ hA₁ hm₁ hq hv hvpos hfin hpos hlogpos
  have hn := PDE.Parabolic.WeakHarnack.neg_side hχ hA₂ hβ₂ hm₂ hA₃ hβ₃ hm₃ hε hw hwε
    hneg hinner hlogneg
  have hP := PDE.Bombieri.giustiConst_pos (1 / 2) (q * χ)
    (max c₀ (PDE.ParabIter.posC χ A₁ m₁ q)) (PDE.ParabIter.posM χ m₁ q)
  calc
    _ ≤ _ := mul_le_mul' hp hn
    _ = _ := by
      rw [← ENNReal.ofReal_mul (mul_nonneg hP.le (Real.exp_pos k).le)]
      congr 1
      rw [show (PDE.Bombieri.giustiConst (1 / 2) (q * χ)
        (max c₀ (PDE.ParabIter.posC χ A₁ m₁ q)) (PDE.ParabIter.posM χ m₁ q) * Real.exp k) *
          (PDE.Parabolic.WeakHarnack.negTopConst d χ A₂ β₂ m₂ A₃ β₃ m₃ c₀ * Real.exp (-k)) =
        (PDE.Bombieri.giustiConst (1 / 2) (q * χ)
          (max c₀ (PDE.ParabIter.posC χ A₁ m₁ q)) (PDE.ParabIter.posM χ m₁ q) *
          PDE.Parabolic.WeakHarnack.negTopConst d χ A₂ β₂ m₂ A₃ β₃ m₃ c₀) *
          (Real.exp k * Real.exp (-k)) by ring]
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]

/-- Convert two centered bounds to an average-versus-infimum estimate, allowing
an independently translated representative on the later cylinder. -/
theorem c8_two_sided_bounds_to_average {d : ℕ} {r : ℝ} (hr : 0 < r)
    (u v w : Vec d × ℝ → ℝ) (hv : Measurable v) (hw : Measurable w)
    (huv : ∀ᵐ z ∂(volume.restrict (PDE.Parabolic.WeakHarnack.posCyl d (1 / 2))), u z ≤ v z)
    (hwpos : ∀ᵐ z ∂(volume.restrict (PDE.Parabolic.WeakHarnack.negCylInner d (1 / 2))), 0 < w z)
    {C₁ C₂ k : ℝ} (hC₁ : 0 ≤ C₁) (hC₂ : 0 < C₂)
    (h1 : eLpNorm v (ENNReal.ofReal r)
      ((PDE.Parabolic.WeakHarnack.cylMeasure (PDE.Parabolic.WeakHarnack.posCyl d 1)).restrict
        (PDE.Parabolic.WeakHarnack.posCyl d (1 / 2))) ≤ ENNReal.ofReal (C₁ * Real.exp k))
    (h2 : eLpNorm (fun z => 1 / w z) ⊤
      ((PDE.Parabolic.WeakHarnack.cylMeasure (PDE.Parabolic.WeakHarnack.negCyl d 1)).restrict
        (PDE.Parabolic.WeakHarnack.negCylInner d (1 / 2))) ≤ ENNReal.ofReal (C₂ * Real.exp (-k))) :
    PDE.Parabolic.WeakHarnack.weakHarnackAvg d r u ≤
      ENNReal.ofReal ((PDE.Parabolic.WeakHarnack.posVolRatio d) ^ (1 / r) * C₁ * C₂) *
        essInf (fun z => ENNReal.ofReal (w z))
          (volume.restrict (PDE.Parabolic.WeakHarnack.negCylInner d (1 / 2))) := by
  have hE : ENNReal.ofReal (Real.exp k / C₂) ≤
      essInf (fun z => ENNReal.ofReal (w z))
        (volume.restrict (PDE.Parabolic.WeakHarnack.negCylInner d (1 / 2))) := by
    rw [← PDE.Parabolic.WeakHarnack.eLpNorm_top_inv_negCylInner hw hwpos]
    have hp : 0 < C₂ * Real.exp (-k) := by positivity
    calc ENNReal.ofReal (Real.exp k / C₂) = (ENNReal.ofReal (C₂ * Real.exp (-k)))⁻¹ := by
          rw [← ENNReal.ofReal_inv_of_pos hp, Real.exp_neg]
          congr 1
          field_simp
      _ ≤ _ := ENNReal.inv_le_inv.2 h2
  have hk : ENNReal.ofReal (Real.exp k) ≤ ENNReal.ofReal C₂ *
      essInf (fun z => ENNReal.ofReal (w z))
        (volume.restrict (PDE.Parabolic.WeakHarnack.negCylInner d (1 / 2))) := by
    calc ENNReal.ofReal (Real.exp k) = ENNReal.ofReal C₂ * ENNReal.ofReal (Real.exp k / C₂) := by
          rw [← ENNReal.ofReal_mul hC₂.le]
          congr 1
          field_simp
      _ ≤ _ := by gcongr
  refine (PDE.Parabolic.WeakHarnack.weakHarnackAvg_le_eLpNorm hr u hv huv).trans ?_
  have hR : 0 ≤ (PDE.Parabolic.WeakHarnack.posVolRatio d) ^ (1 / r) :=
    Real.rpow_nonneg (PDE.Parabolic.WeakHarnack.posVolRatio_pos d).le _
  calc
    _ ≤ ENNReal.ofReal ((PDE.Parabolic.WeakHarnack.posVolRatio d) ^ (1 / r)) *
        ENNReal.ofReal (C₁ * Real.exp k) := by gcongr
    _ = ENNReal.ofReal ((PDE.Parabolic.WeakHarnack.posVolRatio d) ^ (1 / r) * C₁) *
        ENNReal.ofReal (Real.exp k) := by
      rw [← ENNReal.ofReal_mul hR, ← ENNReal.ofReal_mul (mul_nonneg hR hC₁)]
      congr 1
      ring
    _ ≤ ENNReal.ofReal ((PDE.Parabolic.WeakHarnack.posVolRatio d) ^ (1 / r) * C₁) *
        (ENNReal.ofReal C₂ * essInf (fun z => ENNReal.ofReal (w z))
          (volume.restrict (PDE.Parabolic.WeakHarnack.negCylInner d (1 / 2)))) := by gcongr
    _ = _ := by rw [← mul_assoc, ← ENNReal.ofReal_mul (mul_nonneg hR hC₁)]

/-- Essential infima commute with measurable embeddings and their image measures. -/
theorem c8_essInf_map_embedding {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (f : α → β) (hf : MeasurableEmbedding f) (μ : Measure α) (g : β → ℝ≥0∞) :
    essInf g (Measure.map f μ) = essInf (fun x => g (f x)) μ := by
  rw [essInf_eq_sSup, essInf_eq_sSup]
  congr 1
  ext a
  simp only [Set.mem_setOf_eq, hf.map_apply, Set.preimage_setOf_eq]

/-- Time translation maps each negative cylinder and its restricted measure to
the corresponding late cylinder. -/
theorem c8_lateNegCyl_measure_map {d : ℕ} (σ : ℝ) :
    Measure.map (fun z : Vec d × ℝ => (z.1, z.2 + 3 / 4))
      (volume.restrict (PDE.Parabolic.WeakHarnack.negCyl d σ)) =
    volume.restrict (c8LateNegCyl d σ) := by
  let f : Vec d × ℝ → Vec d × ℝ := fun z => (z.1, z.2 + 3 / 4)
  have hf : MeasurableEmbedding f := by
    have heq : f = fun z => z + ((0, 3 / 4) : Vec d × ℝ) := by
      funext z
      simp [f, Prod.add_def]
    rw [heq]
    exact (Homeomorph.addRight ((0, 3 / 4) : Vec d × ℝ)).measurableEmbedding
  have hmap : Measure.map f volume = volume := by
    have h : MeasurePreserving (Prod.map (id : Vec d → Vec d) (fun t : ℝ => t + 3 / 4))
        (volume.prod volume) (volume.prod volume) :=
      (MeasurePreserving.id volume).prod (measurePreserving_add_right volume (3 / 4))
    rw [Measure.volume_eq_prod]
    exact h.map_eq
  have hpre : f ⁻¹' c8LateNegCyl d σ = PDE.Parabolic.WeakHarnack.negCyl d σ := by
    ext ⟨x, t⟩
    simp only [Set.mem_preimage, f, c8LateNegCyl, Set.mem_setOf_eq, add_sub_cancel_right]
  change Measure.map f (volume.restrict (PDE.Parabolic.WeakHarnack.negCyl d σ)) = _
  rw [← hpre, ← hf.restrict_map, hmap]

/-- Time translation maps each inner negative cylinder and its restricted measure to
the corresponding late cylinder. -/
theorem c8_lateNegCylInner_measure_map {d : ℕ} (σ : ℝ) :
    Measure.map (fun z : Vec d × ℝ => (z.1, z.2 + 3 / 4))
      (volume.restrict (PDE.Parabolic.WeakHarnack.negCylInner d σ)) =
    volume.restrict (c8LateNegCylInner d σ) := by
  let f : Vec d × ℝ → Vec d × ℝ := fun z => (z.1, z.2 + 3 / 4)
  have hf : MeasurableEmbedding f := by
    have heq : f = fun z => z + ((0, 3 / 4) : Vec d × ℝ) := by
      funext z
      simp [f, Prod.add_def]
    rw [heq]
    exact (Homeomorph.addRight ((0, 3 / 4) : Vec d × ℝ)).measurableEmbedding
  have hmap : Measure.map f volume = volume := by
    have h : MeasurePreserving (Prod.map (id : Vec d → Vec d) (fun t : ℝ => t + 3 / 4))
        (volume.prod volume) (volume.prod volume) :=
      (MeasurePreserving.id volume).prod (measurePreserving_add_right volume (3 / 4))
    rw [Measure.volume_eq_prod]
    exact h.map_eq
  have hpre : f ⁻¹' c8LateNegCylInner d σ = PDE.Parabolic.WeakHarnack.negCylInner d σ := by
    ext ⟨x, t⟩
    simp only [Set.mem_preimage, f, c8LateNegCylInner, Set.mem_setOf_eq, add_sub_cancel_right]
  change Measure.map f (volume.restrict (PDE.Parabolic.WeakHarnack.negCylInner d σ)) = _
  rw [← hpre, ← hf.restrict_map, hmap]

/-- Translate the late-cylinder essential infimum to the negative inner cylinder. -/
theorem c8_lateNegCylInner_essInf {d : ℕ} (σ : ℝ) (g : Vec d × ℝ → ℝ≥0∞) :
    essInf g (volume.restrict (c8LateNegCylInner d σ)) =
      essInf (fun z => g (z.1, z.2 + 3 / 4))
        (volume.restrict (PDE.Parabolic.WeakHarnack.negCylInner d σ)) := by
  let f : Vec d × ℝ → Vec d × ℝ := fun z => (z.1, z.2 + 3 / 4)
  have hf : MeasurableEmbedding f := by
    have heq : f = fun z => z + ((0, 3 / 4) : Vec d × ℝ) := by
      funext z
      simp [f, Prod.add_def]
    rw [heq]
    exact (Homeomorph.addRight ((0, 3 / 4) : Vec d × ℝ)).measurableEmbedding
  rw [← c8_lateNegCylInner_measure_map σ]
  exact c8_essInf_map_embedding f hf _ g

/-- The two-sided estimate on the translated late cylinder. -/
theorem c8_two_sided_bounds_to_late_average {d : ℕ} {r : ℝ} (hr : 0 < r)
    (u v g : Vec d × ℝ → ℝ) (hv : Measurable v) (hg : Measurable g)
    (huv : ∀ᵐ z ∂(volume.restrict (PDE.Parabolic.WeakHarnack.posCyl d (1 / 2))), u z ≤ v z)
    (hgpos : ∀ᵐ z ∂(volume.restrict (PDE.Parabolic.WeakHarnack.negCylInner d (1 / 2))),
      0 < g (z.1, z.2 + 3 / 4))
    {C₁ C₂ k : ℝ} (hC₁ : 0 ≤ C₁) (hC₂ : 0 < C₂)
    (h1 : eLpNorm v (ENNReal.ofReal r)
      ((PDE.Parabolic.WeakHarnack.cylMeasure (PDE.Parabolic.WeakHarnack.posCyl d 1)).restrict
        (PDE.Parabolic.WeakHarnack.posCyl d (1 / 2))) ≤ ENNReal.ofReal (C₁ * Real.exp k))
    (h2 : eLpNorm (fun z => 1 / g (z.1, z.2 + 3 / 4)) ⊤
      ((PDE.Parabolic.WeakHarnack.cylMeasure (PDE.Parabolic.WeakHarnack.negCyl d 1)).restrict
        (PDE.Parabolic.WeakHarnack.negCylInner d (1 / 2))) ≤ ENNReal.ofReal (C₂ * Real.exp (-k))) :
    PDE.Parabolic.WeakHarnack.weakHarnackAvg d r u ≤
      ENNReal.ofReal ((PDE.Parabolic.WeakHarnack.posVolRatio d) ^ (1 / r) * C₁ * C₂) *
        essInf (fun z => ENNReal.ofReal (g z)) (volume.restrict (c8LateNegCylInner d (1 / 2))) := by
  have hw : Measurable (fun z : Vec d × ℝ => g (z.1, z.2 + 3 / 4)) :=
    hg.comp (measurable_fst.prodMk (measurable_snd.add_const _))
  have h := c8_two_sided_bounds_to_average hr u v (fun z => g (z.1, z.2 + 3 / 4))
    hv hw huv hgpos hC₁ hC₂ h1 h2
  rw [c8_lateNegCylInner_essInf] at ⊢
  exact h

/-- The closed time endpoint has zero volume on the late inner cylinder. -/
theorem c8_lateNegCylInner_half_restrict (d : ℕ) :
    volume.restrict (c8LateNegCylInner d (1 / 2)) =
      volume.restrict (PDE.euclideanBall (0 : Vec d) (1 / 2) ×ˢ
        Set.Ioo (1 / 2 : ℝ) (3 / 4)) := by
  rw [c8_lateNegCylInner_half]
  simp only [Measure.volume_eq_prod, ← Measure.prod_restrict]
  rw [restrict_Ioo_eq_restrict_Ioc]

/-- Coordinate swap identifies the late cylinder with the target time-first set. -/
theorem c8_lateNegCylInner_half_swap_measure (d : ℕ) :
    Measure.map (Prod.swap : ℝ × Vec d → Vec d × ℝ)
      (volume.restrict (Set.Ioo (1 / 2 : ℝ) (3 / 4) ×ˢ sourceBall 0 (1 / 2))) =
      volume.restrict (c8LateNegCylInner d (1 / 2)) := by
  rw [c8_lateNegCylInner_half_restrict, c8_sourceBall_eq_euclideanBall 0 (by norm_num)]
  simp only [Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.prod_swap]

/-- The late essential infimum agrees with the time-first target cylinder. -/
theorem c8_lateNegCylInner_half_essInf_swap (d : ℕ) (g : ℝ × Vec d → ℝ≥0∞) :
    essInf (fun z : Vec d × ℝ => g (z.2, z.1))
        (volume.restrict (c8LateNegCylInner d (1 / 2))) =
      essInf g (volume.restrict
        (Set.Ioo (1 / 2 : ℝ) (3 / 4) ×ˢ sourceBall 0 (1 / 2))) := by
  rw [← c8_lateNegCylInner_half_swap_measure d]
  exact c8_essInf_map_embedding Prod.swap MeasurableEquiv.prodComm.measurableEmbedding _ _

/-- The early inner cylinder also agrees with the time-first target measure. -/
theorem c8_posCyl_half_swap_measure (d : ℕ) :
    Measure.map (Prod.swap : ℝ × Vec d → Vec d × ℝ)
      (volume.restrict (Set.Ioo (-3 / 4 : ℝ) (-1 / 2) ×ˢ sourceBall 0 (1 / 2))) =
      volume.restrict (PDE.Parabolic.WeakHarnack.posCyl d (1 / 2)) := by
  rw [PDE.Parabolic.WeakHarnack.posCyl_half,
    c8_sourceBall_eq_euclideanBall 0 (by norm_num)]
  simp only [Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.prod_swap]

/-- A common cutoff mass and energy bound yields the small positive-power
Sobolev gain needed for the backward iteration. -/
theorem c8_small_positive_power_integral_gain (d : ℕ) (hd : 2 ≤ d)
    (κ : ℝ) (hκ : 0 < κ) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
    IsUniformlyElliptic κ ρ α → ∀ (I : Set ℝ) (U : Set (Vec d)),
    MeasurableSet I → IsOpen U →
    ∀ (u η : ℝ × Vec d → ℝ) (J : ℝ × Vec d → Vec d) (p : ℝ),
    0 < p →
    let v := fun z : ℝ × Vec d => η z * Real.rpow (u z) (p / 2)
    MemLp v 2 (volume.restrict (I ×ˢ U)) →
    AEStronglyMeasurable J (volume.restrict (I ×ˢ U)) →
    MemLp (fun z => euclideanNorm (J z)) 2 (volume.restrict (I ×ˢ U)) →
    (∀ᵐ t ∂volume.restrict I, HasWeakGradient U (fun x => v (t,x)) (fun x => J (t,x))) →
    ∀ K : Set (Vec d), IsCompact K → K ⊆ U →
    (∀ᵐ t ∂volume.restrict I, ∀ x ∈ U, x ∉ K → v (t,x) = 0) →
    ∀ S T : Set (ℝ × Vec d), MeasurableSet S → S ⊆ I ×ˢ U →
    (∀ z ∈ S, η z = 1 ∧ 0 ≤ u z) → ∀ D : ℝ≥0∞,
    (∀ᵐ t ∂volume.restrict I,
      (∫⁻ x in U, ENNReal.ofReal (ρ x) * ‖v (t,x)‖ₑ ^ (2 : ℝ)) ≤
        D * ∫⁻ z in T, ENNReal.ofReal (u z) ^ p) →
    ((∫⁻ t in I, ∫⁻ x in U, ENNReal.ofReal
      (dot ((α x).mulVec (J (t,x))) (J (t,x)))) ≤
        D * ∫⁻ z in T, ENNReal.ofReal (u z) ^ p) →
    (∫⁻ z in S, ENNReal.ofReal (u z) ^ (p * (((d : ℝ) + 2) / d))) ≤
      C * (D * ∫⁻ z in T, ENNReal.ofReal (u z) ^ p) ^ (((d : ℝ) + 2) / d) := by
  obtain ⟨C, hC, hsob⟩ := c13_small_power_parabolic_sobolev_gain d hd κ hκ
  refine ⟨ENNReal.ofReal κ⁻¹ * C, ENNReal.mul_ne_top ENNReal.ofReal_ne_top hC, ?_⟩
  intro ρ α hell I U hI hU u η J p hp v hv hJm hJ hw K hK hKU hs S T hS hSI hinner D hmass henergy
  let B := D * ∫⁻ z in T, ENNReal.ofReal (u z) ^ p
  have hb := hsob ρ α hell I U hI hU u η J p hp hv hJm hJ hw K hK hKU hs
    S hS hSI hinner B B hmass henergy
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hexp : 2 / (d : ℝ) + 1 = ((d : ℝ) + 2) / d := by
    field_simp
    <;> ring
  have hpow : B ^ (2 / (d : ℝ)) * B = B ^ (((d : ℝ) + 2) / d) := by
    calc
      _ = B ^ (2 / (d : ℝ)) * B ^ (1 : ℝ) := by rw [ENNReal.rpow_one]
      _ = B ^ (2 / (d : ℝ) + 1) := by
        rw [ENNReal.rpow_add_of_nonneg _ _ (by positivity) (by norm_num)]
      _ = _ := by rw [hexp]
  calc
    _ ≤ ENNReal.ofReal κ⁻¹ * (C * B ^ (2 / (d : ℝ)) * B) := hb
    _ = (ENNReal.ofReal κ⁻¹ * C) * (B ^ (2 / (d : ℝ)) * B) := by ac_rfl
    _ = _ := by rw [hpow]

/-- A common mass and energy bound gives a Sobolev gain for the actual caloric field. -/
theorem c8_actual_small_positive_power_integral_gain (d : ℕ) (hd : 2 ≤ d)
    (κ : ℝ) (hκ : 0 < κ) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
    IsUniformlyElliptic κ ρ α → ∀ (I : Set ℝ) (U : Set (Vec d)),
    MeasurableSet I → IsOpen U → volume (I ×ˢ U) < ∞ →
    ∀ (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d),
    IsWeightedCaloric ρ α I U u G →
    ∀ (η : ℝ × Vec d → ℝ), ContDiff ℝ (⊤ : ℕ∞) η → HasCompactSupport η →
    ∀ K : Set (Vec d), IsCompact K → K ⊆ U →
    (∀ t x, x ∉ K → η (t,x) = 0) →
    ∀ S T : Set (ℝ × Vec d), MeasurableSet S → S ⊆ I ×ˢ U →
    (∀ z ∈ S, η z = 1) →
    ∀ p ε : ℝ, 0 < p → p < 1 → 0 < ε →
    (∀ᵐ z ∂volume.restrict (I ×ˢ U), ε ≤ u z) → ∀ D : ℝ≥0∞,
    let v : ℝ × Vec d → ℝ := fun z => η z * (u z) ^ (p / 2)
    let J : ℝ × Vec d → Vec d := fun z =>
      η z • ((p / 2 * (u z) ^ (p / 2 - 1)) • G z) +
        (u z) ^ (p / 2) • (fun j => fderiv ℝ η z (0, unitVector j))
    (∀ᵐ t ∂volume.restrict I, (∫⁻ x in U, ENNReal.ofReal (ρ x) * ‖v (t,x)‖ₑ ^ (2 : ℝ)) ≤
      D * ∫⁻ z in T, ENNReal.ofReal (u z) ^ p) →
    AEMeasurable (fun z => ENNReal.ofReal (dot ((α z.2).mulVec (J z)) (J z)))
      (volume.restrict (I ×ˢ U)) →
    (∫⁻ z in I ×ˢ U, ENNReal.ofReal (dot ((α z.2).mulVec (J z)) (J z))) ≤
      D * ∫⁻ z in T, ENNReal.ofReal (u z) ^ p →
    (∫⁻ z in S, ENNReal.ofReal (u z) ^ (p * (((d : ℝ) + 2) / d))) ≤
      C * (D * ∫⁻ z in T, ENNReal.ofReal (u z) ^ p) ^ (((d : ℝ) + 2) / d) := by
  obtain ⟨C, hC, hsob⟩ := c13_actual_small_power_cutoff_sobolev_gain d hd κ hκ
  refine ⟨ENNReal.ofReal κ⁻¹ * C, ENNReal.mul_ne_top ENNReal.ofReal_ne_top hC, ?_⟩
  intro ρ α hell I U hI hU hfinite u G hu η hη hcη K hK hKU hzero S T hS hSI hηone p ε hp hp1 hε hpos D v J hmass hEm henergy
  let B := D * ∫⁻ z in T, ENNReal.ofReal (u z) ^ p
  have hb := hsob ρ α hell I U hI hU hfinite u G hu η hη hcη K hK hKU hzero
    S hS hSI hηone p ε hp hp1 hε hpos B B hmass hEm henergy
  have hexp : 2 / (d : ℝ) + 1 = ((d : ℝ) + 2) / d := by
    field_simp
    <;> ring
  have hpow : B ^ (2 / (d : ℝ)) * B = B ^ (((d : ℝ) + 2) / d) := by
    calc
      _ = B ^ (2 / (d : ℝ)) * B ^ (1 : ℝ) := by rw [ENNReal.rpow_one]
      _ = B ^ (2 / (d : ℝ) + 1) := by
        rw [ENNReal.rpow_add_of_nonneg _ _ (by positivity) (by norm_num)]
      _ = _ := by rw [hexp]
  calc
    _ ≤ ENNReal.ofReal κ⁻¹ * (C * B ^ (2 / (d : ℝ)) * B) := hb
    _ = (ENNReal.ofReal κ⁻¹ * C) * (B ^ (2 / (d : ℝ)) * B) := by ac_rfl
    _ = _ := by rw [hpow]

/-- Turn a positive-power integral gain into the norm gain used in iteration. -/
theorem c8_positive_integral_gain_to_eLpNorm {X : Type*} [MeasurableSpace X]
    (μ ν : Measure X) (u : X → ℝ) {p χ : ℝ} (hp : 0 < p) (hχ : 0 < χ)
    (huμ : AEStronglyMeasurable u μ) (huν : AEStronglyMeasurable u ν)
    (hposμ : ∀ᵐ x ∂μ, 0 ≤ u x) (hposν : ∀ᵐ x ∂ν, 0 ≤ u x)
    (C D : ℝ≥0∞)
    (hgain : (∫⁻ x, ENNReal.ofReal (u x) ^ (p * χ) ∂μ) ≤
      C * (D * ∫⁻ x, ENNReal.ofReal (u x) ^ p ∂ν) ^ χ) :
    eLpNorm u (ENNReal.ofReal (p * χ)) μ ≤
      (C ^ ((p * χ)⁻¹) * D ^ p⁻¹) * eLpNorm u (ENNReal.ofReal p) ν := by
  have hn (τ : Measure X) (r : ℝ) (hr : 0 < r)
      (hm : AEStronglyMeasurable u τ) (hpos : ∀ᵐ x ∂τ, 0 ≤ u x) :
      eLpNorm u (ENNReal.ofReal r) τ =
        (∫⁻ x, ENNReal.ofReal (u x) ^ r ∂τ) ^ r⁻¹ := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal ((ENNReal.ofReal_pos.mpr hr).ne')
      ENNReal.ofReal_ne_top hm, ENNReal.toReal_ofReal hr.le, one_div]
    congr 1
    apply lintegral_congr_ae
    filter_upwards [hpos] with x hx
    simp [Real.enorm_eq_ofReal_abs, abs_of_nonneg hx]
  have hpχ : 0 < p * χ := mul_pos hp hχ
  rw [hn μ (p * χ) hpχ huμ hposμ, hn ν p hp huν hposν]
  have h := ENNReal.rpow_le_rpow hgain (inv_nonneg.mpr hpχ.le)
  rw [ENNReal.mul_rpow_of_nonneg _ _ (inv_nonneg.mpr hpχ.le), ← ENNReal.rpow_mul] at h
  have he : χ * (p * χ)⁻¹ = p⁻¹ := by
    field_simp
  rw [he, ENNReal.mul_rpow_of_nonneg _ _ (inv_nonneg.mpr hp.le)] at h
  simpa only [mul_assoc] using h


/-- Remove the positive shift from a real-valued weak-Harnack estimate. -/
theorem c8_weak_harnack_shifted_to_unshifted {d : ℕ} {p C : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (u : ℝ × Vec d → ℝ)
    (hu : MemLp u 2 (volume.restrict
      (Set.Ioo (-3/4 : ℝ) (-1/2) ×ˢ sourceBall 0 (1/2))))
    (hu0 : ∀ᵐ z ∂volume.restrict
      (Set.Ioo (-3/4 : ℝ) (-1/2) ×ˢ sourceBall 0 (1/2)), 0 ≤ u z)
    (hbelow : ∀ᵐ z ∂volume.restrict
      (Set.Ioo (1/2 : ℝ) (3/4) ×ˢ sourceBall 0 (1/2)), 0 ≤ u z)
    (hbound : ∀ ε : ℝ, 0 < ε →
      Real.rpow (∫ z in Set.Ioo (-3/4 : ℝ) (-1/2) ×ˢ sourceBall 0 (1/2),
        Real.rpow |u z + ε| p) p⁻¹ ≤
      C * essInf (fun z => u z + ε) (volume.restrict
        (Set.Ioo (1/2 : ℝ) (3/4) ×ˢ sourceBall 0 (1/2)))) :
    Real.rpow (∫ z in Set.Ioo (-3/4 : ℝ) (-1/2) ×ˢ sourceBall 0 (1/2),
      Real.rpow |u z| p) p⁻¹ ≤
      C * essInf u (volume.restrict
        (Set.Ioo (1/2 : ℝ) (3/4) ×ˢ sourceBall 0 (1/2))) := by
  let μ := volume.restrict (Set.Ioo (1/2 : ℝ) (3/4) ×ˢ sourceBall (0 : Vec d) (1/2))
  have hμ : μ ≠ 0 := by
    intro hz
    have hlate : volume.restrict (c8LateNegCylInner d (1 / 2)) = 0 := by
      rw [← c8_lateNegCylInner_half_swap_measure d, show
        volume.restrict (Set.Ioo (1/2 : ℝ) (3/4) ×ˢ sourceBall (0 : Vec d) (1/2)) = 0 from hz,
        Measure.map_zero]
    have hm := c8_lateNegCylInner_measure_map (d := d) (1 / 2)
    rw [hlate] at hm
    have hm' := congrArg (fun m : Measure (Vec d × ℝ) => m Set.univ) hm
    simp only [Measure.map_apply (measurable_fst.prodMk (measurable_snd.add_const _))
      MeasurableSet.univ, Set.preimage_univ, Measure.restrict_apply_univ, Measure.coe_zero, Pi.zero_apply] at hm'
    exact (PDE.Parabolic.WeakHarnack.volume_negCylInner_pos (d := d) (by norm_num)).ne' hm'
  haveI : NeBot (ae μ) := ae_neBot.2 hμ
  have hco : Filter.IsCoboundedUnder (· ≥ ·) (ae μ) u := by
    by_contra h
    have hn : ∀ n : ℕ, ∀ᵐ z ∂μ, (n : ℝ) ≤ u z := by
      intro n
      by_contra hn
      apply h
      refine ⟨(n : ℝ), ?_⟩
      intro a ha
      change ∀ᵐ z ∂μ, a ≤ u z at ha
      by_contra hna
      apply hn
      filter_upwards [ha] with z hz
      exact le_trans (le_of_lt (lt_of_not_ge hna)) hz
    have hall : ∀ᵐ z ∂μ, ∀ n : ℕ, (n : ℝ) ≤ u z := ae_all_iff.mpr hn
    obtain ⟨z, hz⟩ := hall.exists
    obtain ⟨n, hn⟩ := exists_nat_gt (u z)
    exact (not_lt_of_ge (hz n)) hn
  have hshift (ε : ℝ) : essInf (fun z => u z + ε) μ = essInf u μ + ε := by
    unfold essInf
    exact liminf_add_const (ae μ) u ε hco ⟨0, hbelow⟩
  apply c8_weak_harnack_remove_epsilon hp hp1 u hu
  intro ε hε
  have hi : (∫ z in Set.Ioo (-3/4 : ℝ) (-1/2) ×ˢ sourceBall 0 (1/2),
      Real.rpow (|u z| + ε) p) =
      ∫ z in Set.Ioo (-3/4 : ℝ) (-1/2) ×ˢ sourceBall 0 (1/2),
        Real.rpow |u z + ε| p := by
    apply integral_congr_ae
    filter_upwards [hu0] with z hz
    rw [abs_of_nonneg hz, abs_of_nonneg (add_nonneg hz hε.le)]
  rw [hi, ← hshift ε]
  exact hbound ε hε

/-- Every positive iteration cylinder has the corresponding time-first measure. -/
theorem c8_posCyl_swap_measure (d : ℕ) (σ : ℝ) (hσ : 1 / 2 ≤ σ) :
    Measure.map (Prod.swap : ℝ × Vec d → Vec d × ℝ)
      (volume.restrict (Set.Ioo (-3 / 4 - (σ - 1 / 2) / 4)
        (-1 / 2 + (σ - 1 / 2) / 4) ×ˢ
        sourceBall 0 (1 / 2 + (σ - 1 / 2) / 2))) =
      volume.restrict (PDE.Parabolic.WeakHarnack.posCyl d σ) := by
  rw [PDE.Parabolic.WeakHarnack.posCyl,
    c8_sourceBall_eq_euclideanBall 0 (by linarith)]
  simp only [Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.prod_swap]

/-- The normalized iteration norm commutes with the time-space swap. -/
theorem c8_posCyl_swap_eLpNorm (d : ℕ) (σ : ℝ) (hσ : 1 / 2 ≤ σ)
    (c q : ℝ≥0∞) (u : ℝ × Vec d → ℝ) :
    eLpNorm (fun z : Vec d × ℝ => u (z.2, z.1)) q
      (c • volume.restrict (PDE.Parabolic.WeakHarnack.posCyl d σ)) =
    eLpNorm u q (c • volume.restrict
      (Set.Ioo (-3 / 4 - (σ - 1 / 2) / 4) (-1 / 2 + (σ - 1 / 2) / 4) ×ˢ
        sourceBall 0 (1 / 2 + (σ - 1 / 2) / 2))) := by
  have hf : MeasurableEmbedding (Prod.swap : ℝ × Vec d → Vec d × ℝ) :=
    MeasurableEquiv.prodComm.measurableEmbedding
  rw [← c8_posCyl_swap_measure d σ hσ, ← Measure.map_smul c hf.measurable.aemeasurable,
    hf.eLpNorm_map_measure]
  rfl

/-- Translate each negative iteration norm to its actual late cylinder. -/
theorem c8_lateNegCyl_eLpNorm {d : ℕ} (σ : ℝ) (c q : ℝ≥0∞)
    (g : Vec d × ℝ → ℝ) :
    eLpNorm (fun z : Vec d × ℝ => g (z.1, z.2 + 3 / 4)) q
      (c • volume.restrict (PDE.Parabolic.WeakHarnack.negCyl d σ)) =
    eLpNorm g q (c • volume.restrict (c8LateNegCyl d σ)) := by
  let f : Vec d × ℝ → Vec d × ℝ := fun z => (z.1, z.2 + 3 / 4)
  have hf : MeasurableEmbedding f := by
    have heq : f = fun z => z + ((0, 3 / 4) : Vec d × ℝ) := by
      funext z
      simp [f, Prod.add_def]
    rw [heq]
    exact (Homeomorph.addRight ((0, 3 / 4) : Vec d × ℝ)).measurableEmbedding
  rw [← c8_lateNegCyl_measure_map σ, ← Measure.map_smul c hf.measurable.aemeasurable,
    hf.eLpNorm_map_measure]
  rfl

/-- The same translation applies to the inner negative iteration. -/
theorem c8_lateNegCylInner_eLpNorm {d : ℕ} (σ : ℝ) (c q : ℝ≥0∞)
    (g : Vec d × ℝ → ℝ) :
    eLpNorm (fun z : Vec d × ℝ => g (z.1, z.2 + 3 / 4)) q
      (c • volume.restrict (PDE.Parabolic.WeakHarnack.negCylInner d σ)) =
    eLpNorm g q (c • volume.restrict (c8LateNegCylInner d σ)) := by
  let f : Vec d × ℝ → Vec d × ℝ := fun z => (z.1, z.2 + 3 / 4)
  have hf : MeasurableEmbedding f := by
    have heq : f = fun z => z + ((0, 3 / 4) : Vec d × ℝ) := by
      funext z
      simp [f, Prod.add_def]
    rw [heq]
    exact (Homeomorph.addRight ((0, 3 / 4) : Vec d × ℝ)).measurableEmbedding
  rw [← c8_lateNegCylInner_measure_map σ, ← Measure.map_smul c hf.measurable.aemeasurable,
    hf.eLpNorm_map_measure]
  rfl

/-- Small positive powers have a continuous cutoff-mass trace even when the
caloric function itself is only specified almost everywhere. -/
theorem c8_small_power_ae_time_balance {d : ℕ} {κ R a b ε p : ℝ}
    (hκ : 0 < κ) (hR : 0 < R) (hab : a < b)
    (hε : 0 < ε) (hp : 0 < p) (hp1 : p < 1)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d) (hell : IsUniformlyElliptic κ ρ α)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hcal : IsWeightedCaloric ρ α (Set.Ioo a b) (sourceBall 0 R) u G)
    (hu : ∀ᵐ z ∂volume.restrict (Set.Ioo a b ×ˢ sourceBall 0 R), ε ≤ u z)
    (χ : Vec d → ℝ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hχc : HasCompactSupport χ) (hχU : tsupport χ ⊆ sourceBall 0 R) :
    ∃ E : ℝ → ℝ, ContinuousOn E (Set.Ioo a b) ∧
      (∀ᵐ t ∂volume.restrict (Set.Ioo a b),
        E t = ∫ x in sourceBall 0 R, ρ x * χ x ^ 2 * Real.rpow (u (t,x)) p) ∧
      ∀ s ∈ Set.Ioo a b, ∀ t ∈ Set.Ioo a b,
        E t - E s = ∫ r in s..t, ∫ x in sourceBall 0 R,
          p*(1-p)*χ x^2*Real.rpow (u (r,x)) (p-2)*dot ((α x).mulVec (G (r,x))) (G (r,x)) -
          2*p*χ x*Real.rpow (u (r,x)) (p-1)*dot ((α x).mulVec (G (r,x)))
            (fun j => fderiv ℝ χ x (unitVector j)) := by
  obtain ⟨F, c, M, hF, hF0, hM, hb, hval, hd, hdd⟩ :=
    c13_small_positive_power_normalized_extension ε p hε hp hp1
  obtain ⟨E, hE, hEae, hdiff⟩ :=
    c13_actual_weighted_C2_continuous_energy hκ hR hab ρ α hell u G hcal
      F hF hF0 M hM (fun x => (hb x).2) χ hχ hχc hχU
  haveI : IsFiniteMeasure (volume.restrict (Set.Ioo a b ×ˢ sourceBall (0 : Vec d) R)) :=
    c20_sourceCylinder_isFiniteMeasure a b R 0
  have hfinite : volume (Set.Ioo a b ×ˢ sourceBall (0 : Vec d) R) < ∞ := by
    simpa only [Measure.restrict_apply_univ] using
      (measure_lt_top (volume.restrict (Set.Ioo a b ×ˢ sourceBall (0 : Vec d) R)) Set.univ)
  have hm := c13_C2_cutoff_mass_integrable hκ ρ α hell (Set.Ioo a b) (sourceBall 0 R)
    u G hcal hfinite F hF M hM (fun x => (hb x).2) χ hχ hχc
  have hk := c16_density_cutoff_integrable (a := a) (b := b) (R := R)
    hκ ρ α hell χ hχ hχc
  have hu' := hu
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict] at hu' hm hk
  have hslices := Measure.ae_ae_of_ae_prod hu'
  refine ⟨fun t => E t + c * (∫ x in sourceBall 0 R, ρ x * χ x ^ 2),
    hE.add continuousOn_const, ?_, ?_⟩
  · filter_upwards [hEae, hm.prod_right_ae, hk.prod_right_ae, hslices] with t ht hmt hkt hpos
    have hmshift : Integrable (fun x => ρ x * χ x ^ 2 * (Real.rpow (u (t,x)) p - c))
        (volume.restrict (sourceBall 0 R)) := by
      apply hmt.congr
      filter_upwards [hpos] with x hx
      rw [hval (u (t,x)) hx]
    have heq : (∫ x in sourceBall 0 R, ρ x * χ x ^ 2 * F (u (t,x))) =
        ∫ x in sourceBall 0 R, ρ x * χ x ^ 2 * (Real.rpow (u (t,x)) p - c) := by
      apply integral_congr_ae
      filter_upwards [hpos] with x hx
      rw [hval (u (t,x)) hx]
    rw [ht, heq, ← integral_const_mul, ← integral_add hmshift (hkt.const_mul c)]
    apply integral_congr_ae
    filter_upwards with x
    ring
  · intro s hs t ht
    have hsub : Set.uIoc s t ⊆ Set.Ioo a b := by
      intro r hr
      have hr' := Set.uIoc_subset_uIcc hr
      rcases le_total s t with hst | hts
      · rw [Set.uIcc_of_le hst] at hr'
        exact ⟨lt_of_lt_of_le hs.1 hr'.1, lt_of_le_of_lt hr'.2 ht.2⟩
      · rw [Set.uIcc_of_ge hts] at hr'
        exact ⟨lt_of_lt_of_le ht.1 hr'.1, lt_of_le_of_lt hr'.2 hs.2⟩
    have heq : -(∫ r in s..t, ∫ x in sourceBall 0 R,
        χ x ^ 2 * deriv (deriv F) (u (r,x)) * dot ((α x).mulVec (G (r,x))) (G (r,x)) +
        2 * χ x * deriv F (u (r,x)) * dot ((α x).mulVec (G (r,x)))
          (fun j => fderiv ℝ χ x (unitVector j))) =
        ∫ r in s..t, ∫ x in sourceBall 0 R,
          p*(1-p)*χ x^2*Real.rpow (u (r,x)) (p-2)*dot ((α x).mulVec (G (r,x))) (G (r,x)) -
          2*p*χ x*Real.rpow (u (r,x)) (p-1)*dot ((α x).mulVec (G (r,x)))
            (fun j => fderiv ℝ χ x (unitVector j)) := by
      rw [← intervalIntegral.integral_neg]
      apply intervalIntegral.integral_congr_ae_restrict
      filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub hslices] with r hr
      rw [← integral_neg]
      apply integral_congr_ae
      filter_upwards [hr] with x hx
      rw [hd (u (r,x)) hx, hdd (u (r,x)) hx]
      ring
    have h := hdiff s hs t ht
    rw [heq] at h
    linarith

/-- Conditional iteration bounds imply the weak-Harnack average estimate. -/
theorem c8_nested_gains_to_average {d : ℕ} {χ A₁ m₁ q A₂ β₂ m₂ A₃ β₃ m₃ k c₀ ε : ℝ}
    (hχ : 1 < χ) (hA₁ : 1 ≤ A₁) (hm₁ : 0 < m₁) (hq : 0 < q)
    (hA₂ : 1 ≤ A₂) (hβ₂ : 0 ≤ β₂) (hm₂ : 0 < m₂)
    (hA₃ : 1 ≤ A₃) (hβ₃ : 0 ≤ β₃) (hm₃ : 0 < m₃) (hε : 0 < ε)
    (u v w : Vec d × ℝ → ℝ) (hv : Measurable v) (hw : Measurable w)
    (huv : ∀ᵐ z ∂(volume.restrict (PDE.Parabolic.WeakHarnack.posCyl d (1 / 2))), u z ≤ v z)
    (hvpos : ∀ z, 0 < v z) (hwε : ∀ z, ε ≤ w z)
    (hfin : eLpNorm v (ENNReal.ofReal (q * χ))
      ((PDE.Parabolic.WeakHarnack.cylMeasure (PDE.Parabolic.WeakHarnack.posCyl d 1)).restrict
        (PDE.Parabolic.WeakHarnack.posCyl d 1)) < ⊤)
    (hpos : ∀ σ' σ : ℝ, 1 / 2 ≤ σ' → σ' < σ → σ ≤ 1 → ∀ p : ℝ, 0 < p → p ≤ q →
      eLpNorm v (ENNReal.ofReal (χ * p))
        ((PDE.Parabolic.WeakHarnack.cylMeasure (PDE.Parabolic.WeakHarnack.posCyl d 1)).restrict
          (PDE.Parabolic.WeakHarnack.posCyl d σ')) ≤
      ENNReal.ofReal ((A₁ * (σ - σ') ^ (-m₁)) ^ (1 / p)) *
      eLpNorm v (ENNReal.ofReal p)
        ((PDE.Parabolic.WeakHarnack.cylMeasure (PDE.Parabolic.WeakHarnack.posCyl d 1)).restrict
          (PDE.Parabolic.WeakHarnack.posCyl d σ)))
    (hneg : ∀ σ' σ : ℝ, 1 / 2 ≤ σ' → σ' < σ → σ ≤ 1 → ∀ p : ℝ, 0 < p →
      eLpNorm (fun z => 1 / w z) (ENNReal.ofReal (χ * p))
        ((PDE.Parabolic.WeakHarnack.cylMeasure (PDE.Parabolic.WeakHarnack.negCyl d 1)).restrict
          (PDE.Parabolic.WeakHarnack.negCyl d σ')) ≤
      ENNReal.ofReal ((A₂ * (1 + p) ^ β₂ * (σ - σ') ^ (-m₂)) ^ (1 / p)) *
      eLpNorm (fun z => 1 / w z) (ENNReal.ofReal p)
        ((PDE.Parabolic.WeakHarnack.cylMeasure (PDE.Parabolic.WeakHarnack.negCyl d 1)).restrict
          (PDE.Parabolic.WeakHarnack.negCyl d σ)))
    (hinner : ∀ σ' σ : ℝ, 1 / 2 ≤ σ' → σ' < σ → σ ≤ 1 → ∀ p : ℝ, 0 < p →
      eLpNorm (fun z => 1 / w z) (ENNReal.ofReal (χ * p))
        ((PDE.Parabolic.WeakHarnack.cylMeasure (PDE.Parabolic.WeakHarnack.negCylInner d 1)).restrict
          (PDE.Parabolic.WeakHarnack.negCylInner d σ')) ≤
      ENNReal.ofReal ((A₃ * (1 + p) ^ β₃ * (σ - σ') ^ (-m₃)) ^ (1 / p)) *
      eLpNorm (fun z => 1 / w z) (ENNReal.ofReal p)
        ((PDE.Parabolic.WeakHarnack.cylMeasure (PDE.Parabolic.WeakHarnack.negCylInner d 1)).restrict
          (PDE.Parabolic.WeakHarnack.negCylInner d σ)))
    (hlogpos : ∀ ℓ : ℝ, 0 < ℓ →
      PDE.Parabolic.WeakHarnack.cylMeasure (PDE.Parabolic.WeakHarnack.posCyl d 1)
        (PDE.Parabolic.WeakHarnack.posCyl d 1 ∩
          {z | ℓ < Real.log (Real.exp (-k) * v z)}) ≤ ENNReal.ofReal (c₀ / ℓ))
    (hlogneg : ∀ ℓ : ℝ, 0 < ℓ →
      PDE.Parabolic.WeakHarnack.cylMeasure (PDE.Parabolic.WeakHarnack.negCyl d 1)
        (PDE.Parabolic.WeakHarnack.negCyl d 1 ∩
          {z | ℓ < Real.log (Real.exp k / w z)}) ≤ ENNReal.ofReal (c₀ / ℓ)) :
    PDE.Parabolic.WeakHarnack.weakHarnackAvg d (q * χ) u ≤
      ENNReal.ofReal ((PDE.Parabolic.WeakHarnack.posVolRatio d) ^ (1 / (q * χ)) *
        PDE.Bombieri.giustiConst (1 / 2) (q * χ)
          (max c₀ (PDE.ParabIter.posC χ A₁ m₁ q)) (PDE.ParabIter.posM χ m₁ q) *
        PDE.Parabolic.WeakHarnack.negTopConst d χ A₂ β₂ m₂ A₃ β₃ m₃ c₀) *
        essInf (fun z => ENNReal.ofReal (w z))
          (volume.restrict (PDE.Parabolic.WeakHarnack.negCylInner d (1 / 2))) := by
  have hp := PDE.Parabolic.WeakHarnack.pos_side hχ hA₁ hm₁ hq hv hvpos hfin hpos hlogpos
  have hn := PDE.Parabolic.WeakHarnack.neg_side hχ hA₂ hβ₂ hm₂ hA₃ hβ₃ hm₃ hε hw hwε
    hneg hinner hlogneg
  have hC₁ := PDE.Bombieri.giustiConst_pos (1 / 2) (q * χ)
    (max c₀ (PDE.ParabIter.posC χ A₁ m₁ q)) (PDE.ParabIter.posM χ m₁ q)
  have hC₂ := PDE.Parabolic.WeakHarnack.negTopConst_pos d (A := A₂) (β := β₂)
    (m := m₂) (c₀ := c₀) hχ hA₃ hβ₃ hm₃
  exact c8_two_sided_bounds_to_average (mul_pos hq (by linarith)) u v w hv hw huv
    (Filter.Eventually.of_forall (fun z => lt_of_lt_of_le hε (hwε z))) hC₁.le hC₂ hp hn

/-- Clipping a positive representative from below preserves its reciprocal logarithmic tail. -/
theorem c8_reciprocal_log_tail_clip {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (S : Set X) (v : X → ℝ) {ε k c : ℝ}
    (hv : ∀ z, 0 < v z)
    (htail : ∀ ℓ : ℝ, 0 < ℓ →
      μ (S ∩ {z | ℓ < Real.log (Real.exp k / v z)}) ≤ ENNReal.ofReal (c / ℓ)) :
    ∀ ℓ : ℝ, 0 < ℓ →
      μ (S ∩ {z | ℓ < Real.log (Real.exp k / max ε (v z))}) ≤ ENNReal.ofReal (c / ℓ) := by
  intro ℓ hℓ
  apply (measure_mono ?_).trans (htail ℓ hℓ)
  intro z hz
  refine ⟨hz.1, ?_⟩
  have hzlog : ℓ < Real.log (Real.exp k / max ε (v z)) := hz.2
  change ℓ < Real.log (Real.exp k / v z)
  apply lt_of_lt_of_le hzlog
  apply Real.log_le_log
  · exact div_pos (Real.exp_pos _) (lt_of_lt_of_le (hv z) (le_max_right _ _))
  · exact div_le_div_of_nonneg_left (Real.exp_pos _).le (hv z) (le_max_right _ _)

/-- Remove a positive shift from essential-infimum Harnack bounds. -/
theorem c8_essInf_harnack_remove_shift {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] (μ : Measure X) (ν : Measure Y)
    (u : X → ℝ) (v : Y → ℝ) (p C : ℝ) (hC : 0 < C)
    (hu : AEStronglyMeasurable u μ) (hu0 : ∀ᵐ x ∂μ, 0 ≤ u x)
    (hbound : ∀ ε : ℝ, 0 < ε →
      eLpNorm (fun x => u x + ε) (ENNReal.ofReal p) μ ≤
        ENNReal.ofReal C * essInf (fun y => ENNReal.ofReal (v y + ε)) ν) :
    eLpNorm u (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal C * essInf (fun y => ENNReal.ofReal (v y)) ν := by
  have h := c9_harnack_epsilon_removal μ ν u v p C hu hu0
  have h' := h (by
    intro n
    have hε : 0 < 1 / ((n : ℝ) + 1) := by positivity
    filter_upwards [ae_essInf_le (f := fun y => ENNReal.ofReal (v y + 1 / ((n : ℝ) + 1)))] with y hy
    exact (hbound _ hε).trans (mul_le_mul' le_rfl hy))
  have hC0 : ENNReal.ofReal C ≠ 0 := (ENNReal.ofReal_pos.mpr hC).ne'
  rw [mul_comm, ← ENNReal.div_le_iff hC0 ENNReal.ofReal_ne_top]
  refine le_essInf_of_ae_le _ ?_ ⟨⊤, fun _ _ => le_top⟩
  filter_upwards [h'] with y hy
  apply (ENNReal.div_le_iff hC0 ENNReal.ofReal_ne_top).2
  simpa only [mul_comm] using hy

/-- The unnormalized early-cylinder norm is its volume factor times the Harnack average. -/
theorem c8_posCyl_norm_eq_volume_mul_average {d : ℕ} {p : ℝ} (hp : 0 < p)
    (u : Vec d × ℝ → ℝ)
    (hu : AEStronglyMeasurable u (volume.restrict (PDE.Parabolic.WeakHarnack.posCyl d (1 / 2))))
    (hu0 : ∀ᵐ z ∂volume.restrict (PDE.Parabolic.WeakHarnack.posCyl d (1 / 2)), 0 ≤ u z) :
    eLpNorm u (ENNReal.ofReal p) (volume.restrict (PDE.Parabolic.WeakHarnack.posCyl d (1 / 2))) =
      (volume (PDE.Parabolic.WeakHarnack.posCyl d (1 / 2))) ^ (1 / p) *
        PDE.Parabolic.WeakHarnack.weakHarnackAvg d p u := by
  have hV0 : volume (PDE.Parabolic.WeakHarnack.posCyl d (1 / 2)) ≠ 0 :=
    (PDE.Parabolic.WeakHarnack.volume_posCyl_pos (by norm_num)).ne'
  have hVt : volume (PDE.Parabolic.WeakHarnack.posCyl d (1 / 2)) ≠ ⊤ :=
    PDE.Parabolic.WeakHarnack.volume_posCyl_ne_top le_rfl
  have hlin : (∫⁻ z in PDE.Parabolic.WeakHarnack.posCyl d (1 / 2), ‖u z‖ₑ ^ p) =
      ∫⁻ z in PDE.Parabolic.WeakHarnack.posCyl d (1 / 2), ENNReal.ofReal (u z) ^ p := by
    apply lintegral_congr_ae
    filter_upwards [hu0] with z hz
    rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg hz]
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simpa using hp) ENNReal.ofReal_ne_top hu,
    ENNReal.toReal_ofReal hp.le, hlin]
  unfold PDE.Parabolic.WeakHarnack.weakHarnackAvg
  rw [← PDE.Parabolic.WeakHarnack.posCyl_half,
    ← ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← mul_assoc,
    ENNReal.mul_inv_cancel hV0 hVt, one_mul]

/-- Transport a spatial-first Harnack average bound to the time-first cylinder. -/
theorem c8_time_first_norm_of_average_bound {d : ℕ} {p : ℝ} (hp : 0 < p)
    (u : ℝ × Vec d → ℝ) (D : ℝ≥0∞)
    (hu : AEStronglyMeasurable (fun z : Vec d × ℝ => u (z.2, z.1))
      (volume.restrict (PDE.Parabolic.WeakHarnack.posCyl d (1 / 2))))
    (hu0 : ∀ᵐ z ∂volume.restrict (PDE.Parabolic.WeakHarnack.posCyl d (1 / 2)),
      0 ≤ u (z.2, z.1))
    (havg : PDE.Parabolic.WeakHarnack.weakHarnackAvg d p (fun z => u (z.2, z.1)) ≤
      D * essInf (fun z : Vec d × ℝ => ENNReal.ofReal (u (z.2, z.1)))
        (volume.restrict (c8LateNegCylInner d (1 / 2)))) :
    eLpNorm u (ENNReal.ofReal p) (volume.restrict
      (Set.Ioo (-3 / 4 : ℝ) (-1 / 2) ×ˢ sourceBall 0 (1 / 2))) ≤
      ((volume (PDE.Parabolic.WeakHarnack.posCyl d (1 / 2))) ^ (1 / p) * D) *
        essInf (fun z => ENNReal.ofReal (u z)) (volume.restrict
          (Set.Ioo (1 / 2 : ℝ) (3 / 4) ×ˢ sourceBall 0 (1 / 2))) := by
  have hnorm : eLpNorm u (ENNReal.ofReal p) (volume.restrict
      (Set.Ioo (-3 / 4 : ℝ) (-1 / 2) ×ˢ sourceBall 0 (1 / 2))) =
      eLpNorm (fun z : Vec d × ℝ => u (z.2, z.1)) (ENNReal.ofReal p)
        (volume.restrict (PDE.Parabolic.WeakHarnack.posCyl d (1 / 2))) := by
    rw [← c8_posCyl_half_swap_measure d]
    symm
    exact MeasurableEquiv.prodComm.measurableEmbedding.eLpNorm_map_measure
  rw [hnorm, c8_posCyl_norm_eq_volume_mul_average hp _ hu hu0,
    ← c8_lateNegCylInner_half_essInf_swap d (fun z => ENNReal.ofReal (u z))]
  exact (mul_le_mul' le_rfl havg).trans_eq (mul_assoc _ _ _).symm


/-- The actual log tails admit one real constant uniform in the coefficients and solution. -/
theorem c8_uniform_real_positive_representative_log_tail (d : ℕ) {κ : ℝ} (hκ : 0 < κ) :
    ∃ D : ℝ, ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
      IsUniformlyElliptic κ ρ α → ∀ (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
      {ε : ℝ}, 0 < ε →
      IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1) u G →
      (∀ᵐ z ∂volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1), ε ≤ u z) →
      ∃ (v : Vec d → ℝ → ℝ) (k : ℝ),
        Measurable (fun z : Vec d × ℝ => v z.1 z.2) ∧
        (∀ x t, 0 < v x t) ∧
        (∀ᵐ z ∂volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1),
          v z.2 z.1 = u z) ∧
        ∀ ℓ : ℝ, 0 < ℓ →
          volume (PDE.Parabolic.WeakHarnack.posCyl d 1 ∩ {z | k + ℓ < Real.log (v z.1 z.2)}) +
          volume (c8LateNegCyl d 1 ∩ {z | Real.log (v z.1 z.2) < k - ℓ}) ≤
            ENNReal.ofReal (D / ℓ) := by
  obtain ⟨C, hC, htail⟩ := c8_uniform_positive_representative_log_tail d hκ
  let K := (2 / κ ^ 3) * (∫ x in sourceBall (0 : Vec d) 1,
    euclideanSq (fun j => fderiv ℝ (PDE.Parabolic.WeakHarnack.radialCutoff d) x (unitVector j)))
  let L := κ * (volume (PDE.euclideanBall (0 : Vec d) (3 / 4))).toReal
  let U := κ⁻¹ * (volume (sourceBall (0 : Vec d) 1)).toReal
  let A := (ENNReal.ofReal κ)⁻¹ * (ENNReal.ofReal κ⁻¹ * volume (sourceBall (0 : Vec d) 1))
  let B := 4 / ((κ / 2 / U) / C) + 4 * (K / L) * ((3 / 4 : ℝ) - (-7 / 8 : ℝ)) ^ 2
  have hA : A ≠ ⊤ := by
    apply ENNReal.mul_ne_top
    · exact ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr hκ).ne'
    · apply ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      rw [c8_sourceBall_eq_euclideanBall 0 (by norm_num)]
      exact PDE.volume_euclideanBall_ne_top 0 (by norm_num)
  refine ⟨A.toReal * B, ?_⟩
  intro ρ α hell u G ε hε hcal hpos
  obtain ⟨v, k, hv, hvpos, hveq, hbound⟩ := htail ρ α hell u G hε hcal hpos
  refine ⟨v, k, hv, hvpos, hveq, ?_⟩
  intro ℓ hℓ
  have h := hbound ℓ hℓ
  change _ ≤ A * ENNReal.ofReal (B / ℓ) at h
  apply h.trans_eq
  calc
    A * ENNReal.ofReal (B / ℓ) = ENNReal.ofReal A.toReal * ENNReal.ofReal (B / ℓ) := by
      rw [ENNReal.ofReal_toReal hA]
    _ = ENNReal.ofReal (A.toReal * (B / ℓ)) :=
      (ENNReal.ofReal_mul ENNReal.toReal_nonneg).symm
    _ = ENNReal.ofReal ((A.toReal * B) / ℓ) := by congr 1; ring


/-- Time translation preserves the normalized negative-cylinder measure. -/
theorem c8_lateNegCyl_cylMeasure_map (d : ℕ) :
    Measure.map (fun z : Vec d × ℝ => (z.1, z.2 + 3 / 4))
      (PDE.Parabolic.WeakHarnack.cylMeasure (PDE.Parabolic.WeakHarnack.negCyl d 1)) =
    PDE.Parabolic.WeakHarnack.cylMeasure (c8LateNegCyl d 1) := by
  let f : Vec d × ℝ → Vec d × ℝ := fun z => (z.1, z.2 + 3 / 4)
  have hf : Measurable f := measurable_fst.prodMk (measurable_snd.add_const _)
  have hmap := c8_lateNegCyl_measure_map (d := d) 1
  have hvol : volume (PDE.Parabolic.WeakHarnack.negCyl d 1) =
      volume (c8LateNegCyl d 1) := by
    have h := congrArg (fun μ : Measure (Vec d × ℝ) => μ Set.univ) hmap
    simpa only [Measure.map_apply (measurable_fst.prodMk (measurable_snd.add_const _))
      MeasurableSet.univ, Set.preimage_univ, Measure.restrict_apply_univ] using h
  change Measure.map f _ = _
  unfold PDE.Parabolic.WeakHarnack.cylMeasure
  rw [Measure.map_smul _ hf.aemeasurable, hmap, hvol]


/-- A normalized late-cylinder logarithmic tail transfers to the negative cylinder. -/
theorem c8_lateNegCyl_log_tail_translate {d : ℕ} (v : Vec d × ℝ → ℝ)
    (hv : Measurable v) (k c : ℝ)
    (htail : ∀ ℓ : ℝ, 0 < ℓ →
      PDE.Parabolic.WeakHarnack.cylMeasure (c8LateNegCyl d 1)
        (c8LateNegCyl d 1 ∩ {z | ℓ < Real.log (Real.exp k / v z)}) ≤ ENNReal.ofReal (c / ℓ)) :
    ∀ ℓ : ℝ, 0 < ℓ →
      PDE.Parabolic.WeakHarnack.cylMeasure (PDE.Parabolic.WeakHarnack.negCyl d 1)
        (PDE.Parabolic.WeakHarnack.negCyl d 1 ∩
          {z | ℓ < Real.log (Real.exp k / v (z.1, z.2 + 3 / 4))}) ≤ ENNReal.ofReal (c / ℓ) := by
  intro ℓ hℓ
  let f : Vec d × ℝ → Vec d × ℝ := fun z => (z.1, z.2 + 3 / 4)
  have hf : Measurable f := measurable_fst.prodMk (measurable_snd.add_const _)
  have hlate : MeasurableSet (c8LateNegCyl d 1) := by
    change MeasurableSet ((fun z : Vec d × ℝ => (z.1, z.2 - 3 / 4)) ⁻¹'
      PDE.Parabolic.WeakHarnack.negCyl d 1)
    exact PDE.Parabolic.WeakHarnack.measurableSet_negCyl 1 |>.preimage
      (measurable_fst.prodMk (measurable_snd.sub_const _))
  have hE : MeasurableSet (c8LateNegCyl d 1 ∩ {z | ℓ < Real.log (Real.exp k / v z)}) :=
    hlate.inter (measurableSet_lt measurable_const
      (Real.measurable_log.comp (measurable_const.div hv)))
  have hpre : f ⁻¹' (c8LateNegCyl d 1 ∩ {z | ℓ < Real.log (Real.exp k / v z)}) =
      PDE.Parabolic.WeakHarnack.negCyl d 1 ∩
        {z | ℓ < Real.log (Real.exp k / v (z.1, z.2 + 3 / 4))} := by
    ext z
    simp [f, c8LateNegCyl]
  have h := htail ℓ hℓ
  rw [← c8_lateNegCyl_cylMeasure_map d, Measure.map_apply hf hE, hpre] at h
  exact h


/-- Normalize actual two-cylinder logarithmic tails with one structural constant. -/
theorem c8_normalized_translated_log_tails (d : ℕ) (D : ℝ) :
    ∃ c : ℝ, ∀ (v : Vec d × ℝ → ℝ), Measurable v → (∀ z, 0 < v z) → ∀ k : ℝ,
      (∀ ℓ : ℝ, 0 < ℓ →
        volume (PDE.Parabolic.WeakHarnack.posCyl d 1 ∩ {z | k + ℓ < Real.log (v z)}) +
          volume (c8LateNegCyl d 1 ∩ {z | Real.log (v z) < k - ℓ}) ≤ ENNReal.ofReal (D / ℓ)) →
      (∀ ℓ : ℝ, 0 < ℓ →
        PDE.Parabolic.WeakHarnack.cylMeasure (PDE.Parabolic.WeakHarnack.posCyl d 1)
          (PDE.Parabolic.WeakHarnack.posCyl d 1 ∩
            {z | ℓ < Real.log (Real.exp (-k) * v z)}) ≤ ENNReal.ofReal (c / ℓ)) ∧
      (∀ ℓ : ℝ, 0 < ℓ →
        PDE.Parabolic.WeakHarnack.cylMeasure (PDE.Parabolic.WeakHarnack.negCyl d 1)
          (PDE.Parabolic.WeakHarnack.negCyl d 1 ∩
            {z | ℓ < Real.log (Real.exp k / v (z.1, z.2 + 3 / 4))}) ≤ ENNReal.ofReal (c / ℓ)) := by
  let S := PDE.Parabolic.WeakHarnack.posCyl d 1
  let T := c8LateNegCyl d 1
  let c := max (D / (volume S).toReal) (D / (volume T).toReal)
  have hS : MeasurableSet S := PDE.Parabolic.WeakHarnack.measurableSet_posCyl 1
  have hS0 : volume S ≠ 0 :=
    (PDE.Parabolic.WeakHarnack.volume_posCyl_pos (by norm_num)).ne'
  have hSt : volume S ≠ ⊤ := PDE.Parabolic.WeakHarnack.volume_posCyl_ne_top (by norm_num)
  have hT : MeasurableSet T := by
    change MeasurableSet ((fun z : Vec d × ℝ => (z.1, z.2 - 3 / 4)) ⁻¹'
      PDE.Parabolic.WeakHarnack.negCyl d 1)
    exact (PDE.Parabolic.WeakHarnack.measurableSet_negCyl 1).preimage
      (measurable_fst.prodMk (measurable_snd.sub_const _))
  have hvol : volume (PDE.Parabolic.WeakHarnack.negCyl d 1) = volume T := by
    have h := congrArg (fun μ : Measure (Vec d × ℝ) => μ Set.univ)
      (c8_lateNegCyl_measure_map (d := d) 1)
    simpa only [Measure.map_apply (measurable_fst.prodMk (measurable_snd.add_const _))
      MeasurableSet.univ, Set.preimage_univ, Measure.restrict_apply_univ] using h
  have hT0 : volume T ≠ 0 := by
    rw [← hvol]
    exact (PDE.Parabolic.WeakHarnack.volume_negCyl_pos (by norm_num)).ne'
  have hTt : volume T ≠ ⊤ := by
    rw [← hvol]
    exact PDE.Parabolic.WeakHarnack.volume_negCyl_ne_top (by norm_num)
  refine ⟨c, ?_⟩
  intro v hv hvpos k htail
  obtain ⟨hpos, hneg⟩ := c8_normalized_two_cylinder_log_tail S T hS hT hS0 hSt hT0 hTt v hvpos
    htail (le_max_left _ _) (le_max_right _ _)
  exact ⟨hpos, c8_lateNegCyl_log_tail_translate v hv k c hneg⟩


/-- Actual positive caloric functions have uniform normalized iteration tails. -/
theorem c8_actual_normalized_iteration_tails (d : ℕ) {κ : ℝ} (hκ : 0 < κ) :
    ∃ c : ℝ, ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
      IsUniformlyElliptic κ ρ α → ∀ (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
      {ε : ℝ}, 0 < ε →
      IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1) u G →
      (∀ᵐ z ∂volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1), ε ≤ u z) →
      ∃ (v : Vec d × ℝ → ℝ) (k : ℝ), Measurable v ∧ (∀ z, 0 < v z) ∧
        (∀ᵐ z ∂volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1), v (z.2, z.1) = u z) ∧
        (∀ ℓ : ℝ, 0 < ℓ →
          PDE.Parabolic.WeakHarnack.cylMeasure (PDE.Parabolic.WeakHarnack.posCyl d 1)
            (PDE.Parabolic.WeakHarnack.posCyl d 1 ∩
              {z | ℓ < Real.log (Real.exp (-k) * v z)}) ≤ ENNReal.ofReal (c / ℓ)) ∧
        (∀ ℓ : ℝ, 0 < ℓ →
          PDE.Parabolic.WeakHarnack.cylMeasure (PDE.Parabolic.WeakHarnack.negCyl d 1)
            (PDE.Parabolic.WeakHarnack.negCyl d 1 ∩
              {z | ℓ < Real.log (Real.exp k / v (z.1, z.2 + 3 / 4))}) ≤ ENNReal.ofReal (c / ℓ)) := by
  obtain ⟨D, hD⟩ := c8_uniform_real_positive_representative_log_tail d hκ
  obtain ⟨c, hc⟩ := c8_normalized_translated_log_tails d D
  refine ⟨c, ?_⟩
  intro ρ α hell u G ε hε hcal hpos
  obtain ⟨v, k, hv, hvpos, hveq, htail⟩ := hD ρ α hell u G hε hcal hpos
  refine ⟨fun z => v z.1 z.2, k, hv, ?_, hveq, ?_⟩
  · intro z
    exact hvpos z.1 z.2
  · exact hc (fun z => v z.1 z.2) hv (fun z => hvpos z.1 z.2) k htail

/-- Clipping the translated representative preserves the normalized late tail. -/
theorem c8_normalized_late_tail_clip {d : ℕ} (v : Vec d × ℝ → ℝ)
    {ε k c : ℝ} (hv : ∀ z, 0 < v z)
    (htail : ∀ ℓ : ℝ, 0 < ℓ →
      PDE.Parabolic.WeakHarnack.cylMeasure (PDE.Parabolic.WeakHarnack.negCyl d 1)
        (PDE.Parabolic.WeakHarnack.negCyl d 1 ∩
          {z | ℓ < Real.log (Real.exp k / v (z.1, z.2 + 3 / 4))}) ≤ ENNReal.ofReal (c / ℓ)) :
    ∀ ℓ : ℝ, 0 < ℓ →
      PDE.Parabolic.WeakHarnack.cylMeasure (PDE.Parabolic.WeakHarnack.negCyl d 1)
        (PDE.Parabolic.WeakHarnack.negCyl d 1 ∩
          {z | ℓ < Real.log (Real.exp k / max ε (v (z.1, z.2 + 3 / 4)))}) ≤
        ENNReal.ofReal (c / ℓ) := by
  exact c8_reciprocal_log_tail_clip
    (PDE.Parabolic.WeakHarnack.cylMeasure (PDE.Parabolic.WeakHarnack.negCyl d 1))
    (PDE.Parabolic.WeakHarnack.negCyl d 1) (fun z => v (z.1, z.2 + 3 / 4))
    (fun z => hv (z.1, z.2 + 3 / 4)) htail

/-- Clipping preserves a representative that already has the lower bound almost everywhere. -/
theorem c8_clip_eq_of_ae_eq {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (v u : X → ℝ) (ε : ℝ) (heq : ∀ᵐ z ∂μ, v z = u z)
    (hε : ∀ᵐ z ∂μ, ε ≤ u z) :
    ∀ᵐ z ∂μ, max ε (v z) = u z := by
  filter_upwards [heq, hε] with z hz hbound
  rw [hz, max_eq_right hbound]

/-- The clipped representative has the actual late-cylinder essential infimum. -/
theorem c8_clipped_late_representative_essInf {d : ℕ}
    (v u : Vec d × ℝ → ℝ) (ε : ℝ)
    (heq : ∀ᵐ z ∂volume.restrict (c8LateNegCylInner d (1 / 2)), v z = u z)
    (hε : ∀ᵐ z ∂volume.restrict (c8LateNegCylInner d (1 / 2)), ε ≤ u z) :
    essInf (fun z => ENNReal.ofReal (max ε (v (z.1, z.2 + 3 / 4))))
      (volume.restrict (PDE.Parabolic.WeakHarnack.negCylInner d (1 / 2))) =
    essInf (fun z => ENNReal.ofReal (u z))
      (volume.restrict (c8LateNegCylInner d (1 / 2))) := by
  rw [← (c8_lateNegCylInner_essInf (d := d) (1 / 2)
    (fun z => ENNReal.ofReal (max ε (v z))))]
  apply essInf_congr_ae
  filter_upwards [heq, hε] with z hz hbound
  rw [hz, max_eq_right hbound]

/-- Assemble normalized tails with explicit nested positive and reciprocal gains. -/
theorem c8_normalized_nested_gains_to_average {d : ℕ} {χ A₁ m₁ q A₂ β₂ m₂ A₃ β₃ m₃ k c₀ ε : ℝ}
    (hχ : 1 < χ) (hA₁ : 1 ≤ A₁) (hm₁ : 0 < m₁) (hq : 0 < q)
    (hA₂ : 1 ≤ A₂) (hβ₂ : 0 ≤ β₂) (hm₂ : 0 < m₂)
    (hA₃ : 1 ≤ A₃) (hβ₃ : 0 ≤ β₃) (hm₃ : 0 < m₃) (hε : 0 < ε)
    (u v : Vec d × ℝ → ℝ) (hv : Measurable v)
    (huv : ∀ᵐ z ∂(volume.restrict (PDE.Parabolic.WeakHarnack.posCyl d (1 / 2))), u z ≤ v z)
    (hvpos : ∀ z, 0 < v z)
    (hfin : eLpNorm v (ENNReal.ofReal (q * χ))
      ((PDE.Parabolic.WeakHarnack.cylMeasure (PDE.Parabolic.WeakHarnack.posCyl d 1)).restrict
        (PDE.Parabolic.WeakHarnack.posCyl d 1)) < ⊤)
    (hpos : ∀ σ' σ : ℝ, 1 / 2 ≤ σ' → σ' < σ → σ ≤ 1 → ∀ p : ℝ, 0 < p → p ≤ q →
      eLpNorm v (ENNReal.ofReal (χ * p))
        ((PDE.Parabolic.WeakHarnack.cylMeasure (PDE.Parabolic.WeakHarnack.posCyl d 1)).restrict
          (PDE.Parabolic.WeakHarnack.posCyl d σ')) ≤
      ENNReal.ofReal ((A₁ * (σ - σ') ^ (-m₁)) ^ (1 / p)) *
      eLpNorm v (ENNReal.ofReal p)
        ((PDE.Parabolic.WeakHarnack.cylMeasure (PDE.Parabolic.WeakHarnack.posCyl d 1)).restrict
          (PDE.Parabolic.WeakHarnack.posCyl d σ)))
    (hneg : ∀ σ' σ : ℝ, 1 / 2 ≤ σ' → σ' < σ → σ ≤ 1 → ∀ p : ℝ, 0 < p →
      eLpNorm (fun z => 1 / max ε (v (z.1, z.2 + 3 / 4))) (ENNReal.ofReal (χ * p))
        ((PDE.Parabolic.WeakHarnack.cylMeasure (PDE.Parabolic.WeakHarnack.negCyl d 1)).restrict
          (PDE.Parabolic.WeakHarnack.negCyl d σ')) ≤
      ENNReal.ofReal ((A₂ * (1 + p) ^ β₂ * (σ - σ') ^ (-m₂)) ^ (1 / p)) *
      eLpNorm (fun z => 1 / max ε (v (z.1, z.2 + 3 / 4))) (ENNReal.ofReal p)
        ((PDE.Parabolic.WeakHarnack.cylMeasure (PDE.Parabolic.WeakHarnack.negCyl d 1)).restrict
          (PDE.Parabolic.WeakHarnack.negCyl d σ)))
    (hinner : ∀ σ' σ : ℝ, 1 / 2 ≤ σ' → σ' < σ → σ ≤ 1 → ∀ p : ℝ, 0 < p →
      eLpNorm (fun z => 1 / max ε (v (z.1, z.2 + 3 / 4))) (ENNReal.ofReal (χ * p))
        ((PDE.Parabolic.WeakHarnack.cylMeasure (PDE.Parabolic.WeakHarnack.negCylInner d 1)).restrict
          (PDE.Parabolic.WeakHarnack.negCylInner d σ')) ≤
      ENNReal.ofReal ((A₃ * (1 + p) ^ β₃ * (σ - σ') ^ (-m₃)) ^ (1 / p)) *
      eLpNorm (fun z => 1 / max ε (v (z.1, z.2 + 3 / 4))) (ENNReal.ofReal p)
        ((PDE.Parabolic.WeakHarnack.cylMeasure (PDE.Parabolic.WeakHarnack.negCylInner d 1)).restrict
          (PDE.Parabolic.WeakHarnack.negCylInner d σ)))
    (hlogpos : ∀ ℓ : ℝ, 0 < ℓ →
      PDE.Parabolic.WeakHarnack.cylMeasure (PDE.Parabolic.WeakHarnack.posCyl d 1)
        (PDE.Parabolic.WeakHarnack.posCyl d 1 ∩
          {z | ℓ < Real.log (Real.exp (-k) * v z)}) ≤ ENNReal.ofReal (c₀ / ℓ))
    (hlogneg : ∀ ℓ : ℝ, 0 < ℓ →
      PDE.Parabolic.WeakHarnack.cylMeasure (PDE.Parabolic.WeakHarnack.negCyl d 1)
        (PDE.Parabolic.WeakHarnack.negCyl d 1 ∩
          {z | ℓ < Real.log (Real.exp k / v (z.1, z.2 + 3 / 4))}) ≤ ENNReal.ofReal (c₀ / ℓ)) :
    PDE.Parabolic.WeakHarnack.weakHarnackAvg d (q * χ) u ≤
      ENNReal.ofReal ((PDE.Parabolic.WeakHarnack.posVolRatio d) ^ (1 / (q * χ)) *
        PDE.Bombieri.giustiConst (1 / 2) (q * χ)
          (max c₀ (PDE.ParabIter.posC χ A₁ m₁ q)) (PDE.ParabIter.posM χ m₁ q) *
        PDE.Parabolic.WeakHarnack.negTopConst d χ A₂ β₂ m₂ A₃ β₃ m₃ c₀) *
        essInf (fun z => ENNReal.ofReal (max ε (v (z.1, z.2 + 3 / 4))))
          (volume.restrict (PDE.Parabolic.WeakHarnack.negCylInner d (1 / 2))) := by
  let w : Vec d × ℝ → ℝ := fun z => max ε (v (z.1, z.2 + 3 / 4))
  have hw : Measurable w := measurable_const.max
    (hv.comp (measurable_fst.prodMk (measurable_snd.add_const _)))
  exact c8_nested_gains_to_average hχ hA₁ hm₁ hq hA₂ hβ₂ hm₂ hA₃ hβ₃ hm₃ hε
    u v w hv hw huv hvpos (fun z => le_max_left _ _) hfin hpos hneg hinner hlogpos
    (c8_normalized_late_tail_clip v hvpos hlogneg)

/-- Conditional nested gains control the average by the actual late representative. -/
theorem c8_normalized_nested_gains_to_late_average {d : ℕ} {χ A₁ m₁ q A₂ β₂ m₂ A₃ β₃ m₃ k c₀ ε : ℝ}
    (hχ : 1 < χ) (hA₁ : 1 ≤ A₁) (hm₁ : 0 < m₁) (hq : 0 < q)
    (hA₂ : 1 ≤ A₂) (hβ₂ : 0 ≤ β₂) (hm₂ : 0 < m₂)
    (hA₃ : 1 ≤ A₃) (hβ₃ : 0 ≤ β₃) (hm₃ : 0 < m₃) (hε : 0 < ε)
    (u v g : Vec d × ℝ → ℝ) (hv : Measurable v)
    (hvg : ∀ᵐ z ∂volume.restrict (c8LateNegCylInner d (1 / 2)), v z = g z)
    (hglower : ∀ᵐ z ∂volume.restrict (c8LateNegCylInner d (1 / 2)), ε ≤ g z)
    (huv : ∀ᵐ z ∂(volume.restrict (PDE.Parabolic.WeakHarnack.posCyl d (1 / 2))), u z ≤ v z)
    (hvpos : ∀ z, 0 < v z)
    (hfin : eLpNorm v (ENNReal.ofReal (q * χ))
      ((PDE.Parabolic.WeakHarnack.cylMeasure (PDE.Parabolic.WeakHarnack.posCyl d 1)).restrict
        (PDE.Parabolic.WeakHarnack.posCyl d 1)) < ⊤)
    (hpos : ∀ σ' σ : ℝ, 1 / 2 ≤ σ' → σ' < σ → σ ≤ 1 → ∀ p : ℝ, 0 < p → p ≤ q →
      eLpNorm v (ENNReal.ofReal (χ * p))
        ((PDE.Parabolic.WeakHarnack.cylMeasure (PDE.Parabolic.WeakHarnack.posCyl d 1)).restrict
          (PDE.Parabolic.WeakHarnack.posCyl d σ')) ≤
      ENNReal.ofReal ((A₁ * (σ - σ') ^ (-m₁)) ^ (1 / p)) *
      eLpNorm v (ENNReal.ofReal p)
        ((PDE.Parabolic.WeakHarnack.cylMeasure (PDE.Parabolic.WeakHarnack.posCyl d 1)).restrict
          (PDE.Parabolic.WeakHarnack.posCyl d σ)))
    (hneg : ∀ σ' σ : ℝ, 1 / 2 ≤ σ' → σ' < σ → σ ≤ 1 → ∀ p : ℝ, 0 < p →
      eLpNorm (fun z => 1 / max ε (v (z.1, z.2 + 3 / 4))) (ENNReal.ofReal (χ * p))
        ((PDE.Parabolic.WeakHarnack.cylMeasure (PDE.Parabolic.WeakHarnack.negCyl d 1)).restrict
          (PDE.Parabolic.WeakHarnack.negCyl d σ')) ≤
      ENNReal.ofReal ((A₂ * (1 + p) ^ β₂ * (σ - σ') ^ (-m₂)) ^ (1 / p)) *
      eLpNorm (fun z => 1 / max ε (v (z.1, z.2 + 3 / 4))) (ENNReal.ofReal p)
        ((PDE.Parabolic.WeakHarnack.cylMeasure (PDE.Parabolic.WeakHarnack.negCyl d 1)).restrict
          (PDE.Parabolic.WeakHarnack.negCyl d σ)))
    (hinner : ∀ σ' σ : ℝ, 1 / 2 ≤ σ' → σ' < σ → σ ≤ 1 → ∀ p : ℝ, 0 < p →
      eLpNorm (fun z => 1 / max ε (v (z.1, z.2 + 3 / 4))) (ENNReal.ofReal (χ * p))
        ((PDE.Parabolic.WeakHarnack.cylMeasure (PDE.Parabolic.WeakHarnack.negCylInner d 1)).restrict
          (PDE.Parabolic.WeakHarnack.negCylInner d σ')) ≤
      ENNReal.ofReal ((A₃ * (1 + p) ^ β₃ * (σ - σ') ^ (-m₃)) ^ (1 / p)) *
      eLpNorm (fun z => 1 / max ε (v (z.1, z.2 + 3 / 4))) (ENNReal.ofReal p)
        ((PDE.Parabolic.WeakHarnack.cylMeasure (PDE.Parabolic.WeakHarnack.negCylInner d 1)).restrict
          (PDE.Parabolic.WeakHarnack.negCylInner d σ)))
    (hlogpos : ∀ ℓ : ℝ, 0 < ℓ →
      PDE.Parabolic.WeakHarnack.cylMeasure (PDE.Parabolic.WeakHarnack.posCyl d 1)
        (PDE.Parabolic.WeakHarnack.posCyl d 1 ∩
          {z | ℓ < Real.log (Real.exp (-k) * v z)}) ≤ ENNReal.ofReal (c₀ / ℓ))
    (hlogneg : ∀ ℓ : ℝ, 0 < ℓ →
      PDE.Parabolic.WeakHarnack.cylMeasure (PDE.Parabolic.WeakHarnack.negCyl d 1)
        (PDE.Parabolic.WeakHarnack.negCyl d 1 ∩
          {z | ℓ < Real.log (Real.exp k / v (z.1, z.2 + 3 / 4))}) ≤ ENNReal.ofReal (c₀ / ℓ)) :
    PDE.Parabolic.WeakHarnack.weakHarnackAvg d (q * χ) u ≤
      ENNReal.ofReal ((PDE.Parabolic.WeakHarnack.posVolRatio d) ^ (1 / (q * χ)) *
        PDE.Bombieri.giustiConst (1 / 2) (q * χ)
          (max c₀ (PDE.ParabIter.posC χ A₁ m₁ q)) (PDE.ParabIter.posM χ m₁ q) *
        PDE.Parabolic.WeakHarnack.negTopConst d χ A₂ β₂ m₂ A₃ β₃ m₃ c₀) *
        essInf (fun z => ENNReal.ofReal (g z))
          (volume.restrict (c8LateNegCylInner d (1 / 2))) := by
  have h := c8_normalized_nested_gains_to_average hχ hA₁ hm₁ hq hA₂ hβ₂ hm₂
    hA₃ hβ₃ hm₃ hε u v hv huv hvpos hfin hpos hneg hinner hlogpos hlogneg
  rw [c8_clipped_late_representative_essInf v g ε hvg hglower] at h
  exact h

/-- Explicit nested gains yield the time-first norm estimate. -/
theorem c8_normalized_nested_gains_to_time_first_norm {d : ℕ} {χ A₁ m₁ q A₂ β₂ m₂ A₃ β₃ m₃ k c₀ ε : ℝ}
    (hχ : 1 < χ) (hA₁ : 1 ≤ A₁) (hm₁ : 0 < m₁) (hq : 0 < q)
    (hA₂ : 1 ≤ A₂) (hβ₂ : 0 ≤ β₂) (hm₂ : 0 < m₂)
    (hA₃ : 1 ≤ A₃) (hβ₃ : 0 ≤ β₃) (hm₃ : 0 < m₃) (hε : 0 < ε)
    (u : ℝ × Vec d → ℝ) (v : Vec d × ℝ → ℝ) (hv : Measurable v)
    (hu : AEStronglyMeasurable (fun z : Vec d × ℝ => u (z.2, z.1))
      (volume.restrict (PDE.Parabolic.WeakHarnack.posCyl d (1 / 2))))
    (hu0 : ∀ᵐ z ∂volume.restrict (PDE.Parabolic.WeakHarnack.posCyl d (1 / 2)),
      0 ≤ u (z.2, z.1))
    (hvg : ∀ᵐ z ∂volume.restrict (c8LateNegCylInner d (1 / 2)), v z = u (z.2, z.1))
    (hglower : ∀ᵐ z ∂volume.restrict (c8LateNegCylInner d (1 / 2)), ε ≤ u (z.2, z.1))
    (huv : ∀ᵐ z ∂(volume.restrict (PDE.Parabolic.WeakHarnack.posCyl d (1 / 2))), u (z.2, z.1) ≤ v z)
    (hvpos : ∀ z, 0 < v z)
    (hfin : eLpNorm v (ENNReal.ofReal (q * χ))
      ((PDE.Parabolic.WeakHarnack.cylMeasure (PDE.Parabolic.WeakHarnack.posCyl d 1)).restrict
        (PDE.Parabolic.WeakHarnack.posCyl d 1)) < ⊤)
    (hpos : ∀ σ' σ : ℝ, 1 / 2 ≤ σ' → σ' < σ → σ ≤ 1 → ∀ p : ℝ, 0 < p → p ≤ q →
      eLpNorm v (ENNReal.ofReal (χ * p))
        ((PDE.Parabolic.WeakHarnack.cylMeasure (PDE.Parabolic.WeakHarnack.posCyl d 1)).restrict
          (PDE.Parabolic.WeakHarnack.posCyl d σ')) ≤
      ENNReal.ofReal ((A₁ * (σ - σ') ^ (-m₁)) ^ (1 / p)) *
      eLpNorm v (ENNReal.ofReal p)
        ((PDE.Parabolic.WeakHarnack.cylMeasure (PDE.Parabolic.WeakHarnack.posCyl d 1)).restrict
          (PDE.Parabolic.WeakHarnack.posCyl d σ)))
    (hneg : ∀ σ' σ : ℝ, 1 / 2 ≤ σ' → σ' < σ → σ ≤ 1 → ∀ p : ℝ, 0 < p →
      eLpNorm (fun z => 1 / max ε (v (z.1, z.2 + 3 / 4))) (ENNReal.ofReal (χ * p))
        ((PDE.Parabolic.WeakHarnack.cylMeasure (PDE.Parabolic.WeakHarnack.negCyl d 1)).restrict
          (PDE.Parabolic.WeakHarnack.negCyl d σ')) ≤
      ENNReal.ofReal ((A₂ * (1 + p) ^ β₂ * (σ - σ') ^ (-m₂)) ^ (1 / p)) *
      eLpNorm (fun z => 1 / max ε (v (z.1, z.2 + 3 / 4))) (ENNReal.ofReal p)
        ((PDE.Parabolic.WeakHarnack.cylMeasure (PDE.Parabolic.WeakHarnack.negCyl d 1)).restrict
          (PDE.Parabolic.WeakHarnack.negCyl d σ)))
    (hinner : ∀ σ' σ : ℝ, 1 / 2 ≤ σ' → σ' < σ → σ ≤ 1 → ∀ p : ℝ, 0 < p →
      eLpNorm (fun z => 1 / max ε (v (z.1, z.2 + 3 / 4))) (ENNReal.ofReal (χ * p))
        ((PDE.Parabolic.WeakHarnack.cylMeasure (PDE.Parabolic.WeakHarnack.negCylInner d 1)).restrict
          (PDE.Parabolic.WeakHarnack.negCylInner d σ')) ≤
      ENNReal.ofReal ((A₃ * (1 + p) ^ β₃ * (σ - σ') ^ (-m₃)) ^ (1 / p)) *
      eLpNorm (fun z => 1 / max ε (v (z.1, z.2 + 3 / 4))) (ENNReal.ofReal p)
        ((PDE.Parabolic.WeakHarnack.cylMeasure (PDE.Parabolic.WeakHarnack.negCylInner d 1)).restrict
          (PDE.Parabolic.WeakHarnack.negCylInner d σ)))
    (hlogpos : ∀ ℓ : ℝ, 0 < ℓ →
      PDE.Parabolic.WeakHarnack.cylMeasure (PDE.Parabolic.WeakHarnack.posCyl d 1)
        (PDE.Parabolic.WeakHarnack.posCyl d 1 ∩
          {z | ℓ < Real.log (Real.exp (-k) * v z)}) ≤ ENNReal.ofReal (c₀ / ℓ))
    (hlogneg : ∀ ℓ : ℝ, 0 < ℓ →
      PDE.Parabolic.WeakHarnack.cylMeasure (PDE.Parabolic.WeakHarnack.negCyl d 1)
        (PDE.Parabolic.WeakHarnack.negCyl d 1 ∩
          {z | ℓ < Real.log (Real.exp k / v (z.1, z.2 + 3 / 4))}) ≤ ENNReal.ofReal (c₀ / ℓ)) :
    eLpNorm u (ENNReal.ofReal (q * χ)) (volume.restrict
      (Set.Ioo (-3 / 4 : ℝ) (-1 / 2) ×ˢ sourceBall 0 (1 / 2))) ≤
      ((volume (PDE.Parabolic.WeakHarnack.posCyl d (1 / 2))) ^ (1 / (q * χ)) *
        ENNReal.ofReal ((PDE.Parabolic.WeakHarnack.posVolRatio d) ^ (1 / (q * χ)) *
          PDE.Bombieri.giustiConst (1 / 2) (q * χ)
            (max c₀ (PDE.ParabIter.posC χ A₁ m₁ q)) (PDE.ParabIter.posM χ m₁ q) *
          PDE.Parabolic.WeakHarnack.negTopConst d χ A₂ β₂ m₂ A₃ β₃ m₃ c₀)) *
        essInf (fun z => ENNReal.ofReal (u z)) (volume.restrict
          (Set.Ioo (1 / 2 : ℝ) (3 / 4) ×ˢ sourceBall 0 (1 / 2))) := by
  have havg := c8_normalized_nested_gains_to_late_average hχ hA₁ hm₁ hq hA₂ hβ₂ hm₂
    hA₃ hβ₃ hm₃ hε (fun z => u (z.2, z.1)) v (fun z => u (z.2, z.1))
    hv hvg hglower huv hvpos hfin hpos hneg hinner hlogpos hlogneg
  exact c8_time_first_norm_of_average_bound (mul_pos hq (by linarith)) u _ hu hu0 havg

/-- A uniform shifted caloric estimate implies the unshifted weak Harnack estimate. -/
theorem c8_native_unit_weak_harnack_of_shifted (d : ℕ) (hd : 2 ≤ d) (κ : ℝ) (hκ : 0 < κ)
    (hshift : ∃ p C : ℝ, 0 < p ∧ 0 < C ∧
      ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
        IsUniformlyElliptic κ ρ α →
        ∀ (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d),
          IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1) u G →
          (∀ᵐ z ∂volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1), 0 ≤ u z) →
          ∀ ε : ℝ, 0 < ε →
            eLpNorm (fun z => u z + ε) (ENNReal.ofReal p)
              (volume.restrict (Set.Ioo (-3/4 : ℝ) (-1/2) ×ˢ sourceBall 0 (1/2))) ≤
            ENNReal.ofReal C * essInf (fun z : ℝ × Vec d => ENNReal.ofReal (u z + ε))
              (volume.restrict (Set.Ioo (1/2 : ℝ) (3/4) ×ˢ sourceBall 0 (1/2)))) :
    ∃ p C : ℝ, 0 < p ∧ 0 < C ∧ ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
      IsUniformlyElliptic κ ρ α → ∀ (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d),
        IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1) u G →
        (∀ᵐ z ∂volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1), 0 ≤ u z) →
        eLpNorm u (ENNReal.ofReal p)
          (volume.restrict (Set.Ioo (-3/4 : ℝ) (-1/2) ×ˢ sourceBall 0 (1/2))) ≤
        ENNReal.ofReal C * essInf (fun z : ℝ × Vec d => ENNReal.ofReal (u z))
          (volume.restrict (Set.Ioo (1/2 : ℝ) (3/4) ×ˢ sourceBall 0 (1/2))) := by
  obtain ⟨p, C, hp, hC, hshift⟩ := hshift
  have hdpos : 0 < (d : ℝ) := by exact_mod_cast (show 0 < d by omega)
  have hpdim : 0 < p * ((d : ℝ) * κ) := mul_pos hp (mul_pos hdpos hκ)
  refine ⟨p, C, (mul_pos_iff_of_pos_right (mul_pos hdpos hκ)).mp hpdim, hC, ?_⟩
  intro ρ α hell u G hcal hu0
  have hsub : Set.Ioo (-3/4 : ℝ) (-1/2) ×ˢ sourceBall (0 : Vec d) (1/2) ⊆
      Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall (0 : Vec d) 1 := by
    intro z hz
    refine ⟨⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩, ?_⟩
    change euclideanNorm (z.2 - 0) < 1
    have hball : euclideanNorm (z.2 - 0) < 1/2 := hz.2
    linarith [hball]
  have hmeasure := Measure.restrict_mono_set (volume : Measure (ℝ × Vec d)) hsub
  exact c8_essInf_harnack_remove_shift _ _ u u p C hC
    (hcal.1.aestronglyMeasurable.mono_measure hmeasure)
    (hu0.filter_mono (ae_mono hmeasure)) (hshift ρ α hell u G hcal hu0)

/-- A nonnegative caloric function has uniform iteration tails after every positive shift. -/
theorem c8_shifted_caloric_normalized_iteration_tails (d : ℕ) {κ : ℝ} (hκ : 0 < κ) :
    ∃ c : ℝ, ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
      IsUniformlyElliptic κ ρ α → ∀ (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d),
      IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1) u G →
      (∀ᵐ z ∂volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1), 0 ≤ u z) →
      ∀ ε : ℝ, 0 < ε →
      ∃ (v : Vec d × ℝ → ℝ) (k : ℝ), Measurable v ∧ (∀ z, 0 < v z) ∧
        (∀ᵐ z ∂volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1),
          v (z.2, z.1) = u z + ε) ∧
        (∀ ℓ : ℝ, 0 < ℓ →
          PDE.Parabolic.WeakHarnack.cylMeasure (PDE.Parabolic.WeakHarnack.posCyl d 1)
            (PDE.Parabolic.WeakHarnack.posCyl d 1 ∩
              {z | ℓ < Real.log (Real.exp (-k) * v z)}) ≤ ENNReal.ofReal (c / ℓ)) ∧
        (∀ ℓ : ℝ, 0 < ℓ →
          PDE.Parabolic.WeakHarnack.cylMeasure (PDE.Parabolic.WeakHarnack.negCyl d 1)
            (PDE.Parabolic.WeakHarnack.negCyl d 1 ∩
              {z | ℓ < Real.log (Real.exp k / v (z.1, z.2 + 3 / 4))}) ≤
                ENNReal.ofReal (c / ℓ)) := by
  obtain ⟨c, htail⟩ := c8_actual_normalized_iteration_tails d hκ
  refine ⟨c, ?_⟩
  intro ρ α hell u G hcal hu0 ε hε
  obtain ⟨hshift, hpositive⟩ := c8_weighted_caloric_positive_shift hκ hell hcal hu0 hε
  exact htail ρ α hell (fun z => u z + ε) G hε hshift hpositive

/-- Restrict a shifted representative to the two cylinders used by the iteration. -/
theorem c8_shifted_representative_iteration_interfaces {d : ℕ}
    (u : ℝ × Vec d → ℝ) (v : Vec d × ℝ → ℝ) (ε : ℝ)
    (hv : Measurable v) (hvpos : ∀ z, 0 < v z)
    (hu0 : ∀ᵐ z ∂volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1), 0 ≤ u z)
    (heq : ∀ᵐ z ∂volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1),
      v (z.2, z.1) = u z + ε) :
    AEStronglyMeasurable (fun z : Vec d × ℝ => u (z.2, z.1) + ε)
      (volume.restrict (PDE.Parabolic.WeakHarnack.posCyl d (1 / 2))) ∧
    (∀ᵐ z ∂volume.restrict (PDE.Parabolic.WeakHarnack.posCyl d (1 / 2)),
      0 ≤ u (z.2, z.1) + ε) ∧
    (∀ᵐ z ∂volume.restrict (PDE.Parabolic.WeakHarnack.posCyl d (1 / 2)),
      u (z.2, z.1) + ε ≤ v z) ∧
    (∀ᵐ z ∂volume.restrict (c8LateNegCylInner d (1 / 2)),
      v z = u (z.2, z.1) + ε) ∧
    (∀ᵐ z ∂volume.restrict (c8LateNegCylInner d (1 / 2)),
      ε ≤ u (z.2, z.1) + ε) := by
  have hearly : Set.Ioo (-3/4 : ℝ) (-1/2) ×ˢ sourceBall (0 : Vec d) (1/2) ⊆
      Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall (0 : Vec d) 1 := by
    intro z hz
    refine ⟨⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩, ?_⟩
    change euclideanNorm (z.2 - 0) < 1
    have hb : euclideanNorm (z.2 - 0) < 1/2 := hz.2
    linarith
  have hlate : Set.Ioo (1/2 : ℝ) (3/4) ×ˢ sourceBall (0 : Vec d) (1/2) ⊆
      Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall (0 : Vec d) 1 := by
    intro z hz
    refine ⟨⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩, ?_⟩
    change euclideanNorm (z.2 - 0) < 1
    have hb : euclideanNorm (z.2 - 0) < 1/2 := hz.2
    linarith
  have he : ∀ᵐ z ∂volume.restrict (PDE.Parabolic.WeakHarnack.posCyl d (1 / 2)),
      v z = u (z.2, z.1) + ε := by
    rw [← c8_posCyl_half_swap_measure d]
    apply MeasurableEquiv.prodComm.measurableEmbedding.ae_map_iff.mpr
    exact heq.filter_mono (ae_mono (Measure.restrict_mono_set volume hearly))
  have hl : ∀ᵐ z ∂volume.restrict (c8LateNegCylInner d (1 / 2)),
      v z = u (z.2, z.1) + ε := by
    rw [← c8_lateNegCylInner_half_swap_measure d]
    apply MeasurableEquiv.prodComm.measurableEmbedding.ae_map_iff.mpr
    exact heq.filter_mono (ae_mono (Measure.restrict_mono_set volume hlate))
  have hl0 : ∀ᵐ z ∂volume.restrict (c8LateNegCylInner d (1 / 2)),
      0 ≤ u (z.2, z.1) := by
    rw [← c8_lateNegCylInner_half_swap_measure d]
    apply MeasurableEquiv.prodComm.measurableEmbedding.ae_map_iff.mpr
    exact hu0.filter_mono (ae_mono (Measure.restrict_mono_set volume hlate))
  refine ⟨hv.aestronglyMeasurable.congr he, ?_, ?_, hl, ?_⟩
  · filter_upwards [he] with z hz
    rw [← hz]
    exact (hvpos z).le
  · exact he.mono fun _ h => h.ge
  · filter_upwards [hl0] with z hz
    linarith

/-- The positive iteration starts with a finite moment up to exponent two. -/
@[nolint unusedArguments]
theorem c8_shifted_representative_initial_moment {d : ℕ} {κ : ℝ} (hκ : 0 < κ)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (hell : IsUniformlyElliptic κ ρ α)
    {u : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    (hcal : IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1) u G)
    (hu0 : ∀ᵐ z ∂volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1), 0 ≤ u z)
    {ε : ℝ} (hε : 0 < ε) (v : Vec d × ℝ → ℝ) (hv : Measurable v)
    (heq : ∀ᵐ z ∂volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1),
      v (z.2, z.1) = u z + ε) {p : ℝ} (hp : p ≤ 2) :
    eLpNorm v (ENNReal.ofReal p)
      ((PDE.Parabolic.WeakHarnack.cylMeasure (PDE.Parabolic.WeakHarnack.posCyl d 1)).restrict
        (PDE.Parabolic.WeakHarnack.posCyl d 1)) < ⊤ := by
  let T := Set.Ioo (-7/8 : ℝ) (-3/8) ×ˢ sourceBall (0 : Vec d) (3/4)
  have hsub : T ⊆ Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall (0 : Vec d) 1 := by
    intro z hz
    refine ⟨⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩, ?_⟩
    change euclideanNorm (z.2 - 0) < 1
    have hb : euclideanNorm (z.2 - 0) < 3/4 := hz.2
    linarith
  have hT := Measure.restrict_mono_set (volume : Measure (ℝ × Vec d)) hsub
  have hshift := (c8_weighted_caloric_positive_shift hκ hell hcal hu0 hε).1.1.mono_measure hT
  have heqT := heq.filter_mono (ae_mono hT)
  have hvs : MemLp (fun z : ℝ × Vec d => v (z.2, z.1)) 2 (volume.restrict T) :=
    (memLp_congr_ae heqT).2 hshift
  have hmap : Measure.map (Prod.swap : ℝ × Vec d → Vec d × ℝ) (volume.restrict T) =
      volume.restrict (PDE.Parabolic.WeakHarnack.posCyl d 1) := by
    convert c8_posCyl_swap_measure d 1 (by norm_num) using 1 <;> norm_num [T]
  have hv2 : MemLp v 2 (volume.restrict (PDE.Parabolic.WeakHarnack.posCyl d 1)) := by
    rw [← hmap]
    exact (MeasurableEquiv.prodComm.measurableEmbedding.memLp_map_measure_iff).2 hvs
  have hc : (volume (PDE.Parabolic.WeakHarnack.posCyl d 1))⁻¹ ≠ ⊤ :=
    ENNReal.inv_ne_top.mpr (PDE.Parabolic.WeakHarnack.volume_posCyl_pos (by norm_num)).ne'
  have hnorm : MemLp v 2
      (PDE.Parabolic.WeakHarnack.cylMeasure (PDE.Parabolic.WeakHarnack.posCyl d 1)) :=
    hv2.smul_measure hc
  have hp2 : ENNReal.ofReal p ≤ 2 := by
    simpa using ENNReal.ofReal_le_ofReal hp
  exact ((hnorm.mono_exponent hp2).restrict _).eLpNorm_lt_top

/-- Actual shifted caloric data yield the Harnack estimate from three explicit nested gains. -/
theorem c8_shifted_caloric_harnack_of_nested_gains (d : ℕ) {κ : ℝ} (hκ : 0 < κ)
    {χ A₁ m₁ q A₂ β₂ m₂ A₃ β₃ m₃ : ℝ}
    (hχ : 1 < χ) (hA₁ : 1 ≤ A₁) (hm₁ : 0 < m₁) (hq : 0 < q)
    (hA₂ : 1 ≤ A₂) (hβ₂ : 0 ≤ β₂) (hm₂ : 0 < m₂)
    (hA₃ : 1 ≤ A₃) (hβ₃ : 0 ≤ β₃) (hm₃ : 0 < m₃) (hqχ : q * χ ≤ 2) :
    ∃ c₀ : ℝ, ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
    IsUniformlyElliptic κ ρ α → ∀ (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d),
    IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1) u G →
    (∀ᵐ z ∂volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1), 0 ≤ u z) →
    ∀ ε : ℝ, 0 < ε →
    (∀ (v : Vec d × ℝ → ℝ), Measurable v → (∀ z, 0 < v z) →
      (∀ᵐ z ∂volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1),
        v (z.2, z.1) = u z + ε) →
      (∀ σ' σ : ℝ, 1 / 2 ≤ σ' → σ' < σ → σ ≤ 1 → ∀ p : ℝ, 0 < p → p ≤ q →
      eLpNorm v (ENNReal.ofReal (χ * p))
        ((PDE.Parabolic.WeakHarnack.cylMeasure (PDE.Parabolic.WeakHarnack.posCyl d 1)).restrict
          (PDE.Parabolic.WeakHarnack.posCyl d σ')) ≤
      ENNReal.ofReal ((A₁ * (σ - σ') ^ (-m₁)) ^ (1 / p)) *
      eLpNorm v (ENNReal.ofReal p)
        ((PDE.Parabolic.WeakHarnack.cylMeasure (PDE.Parabolic.WeakHarnack.posCyl d 1)).restrict
          (PDE.Parabolic.WeakHarnack.posCyl d σ))) ∧
      (∀ σ' σ : ℝ, 1 / 2 ≤ σ' → σ' < σ → σ ≤ 1 → ∀ p : ℝ, 0 < p →
      eLpNorm (fun z => 1 / max ε (v (z.1, z.2 + 3 / 4))) (ENNReal.ofReal (χ * p))
        ((PDE.Parabolic.WeakHarnack.cylMeasure (PDE.Parabolic.WeakHarnack.negCyl d 1)).restrict
          (PDE.Parabolic.WeakHarnack.negCyl d σ')) ≤
      ENNReal.ofReal ((A₂ * (1 + p) ^ β₂ * (σ - σ') ^ (-m₂)) ^ (1 / p)) *
      eLpNorm (fun z => 1 / max ε (v (z.1, z.2 + 3 / 4))) (ENNReal.ofReal p)
        ((PDE.Parabolic.WeakHarnack.cylMeasure (PDE.Parabolic.WeakHarnack.negCyl d 1)).restrict
          (PDE.Parabolic.WeakHarnack.negCyl d σ))) ∧
      (∀ σ' σ : ℝ, 1 / 2 ≤ σ' → σ' < σ → σ ≤ 1 → ∀ p : ℝ, 0 < p →
      eLpNorm (fun z => 1 / max ε (v (z.1, z.2 + 3 / 4))) (ENNReal.ofReal (χ * p))
        ((PDE.Parabolic.WeakHarnack.cylMeasure (PDE.Parabolic.WeakHarnack.negCylInner d 1)).restrict
          (PDE.Parabolic.WeakHarnack.negCylInner d σ')) ≤
      ENNReal.ofReal ((A₃ * (1 + p) ^ β₃ * (σ - σ') ^ (-m₃)) ^ (1 / p)) *
      eLpNorm (fun z => 1 / max ε (v (z.1, z.2 + 3 / 4))) (ENNReal.ofReal p)
        ((PDE.Parabolic.WeakHarnack.cylMeasure (PDE.Parabolic.WeakHarnack.negCylInner d 1)).restrict
          (PDE.Parabolic.WeakHarnack.negCylInner d σ)))) →
    eLpNorm (fun z => u z + ε) (ENNReal.ofReal (q * χ)) (volume.restrict
      (Set.Ioo (-3 / 4 : ℝ) (-1 / 2) ×ˢ sourceBall 0 (1 / 2))) ≤
      ((volume (PDE.Parabolic.WeakHarnack.posCyl d (1 / 2))) ^ (1 / (q * χ)) *
        ENNReal.ofReal ((PDE.Parabolic.WeakHarnack.posVolRatio d) ^ (1 / (q * χ)) *
          PDE.Bombieri.giustiConst (1 / 2) (q * χ)
            (max c₀ (PDE.ParabIter.posC χ A₁ m₁ q)) (PDE.ParabIter.posM χ m₁ q) *
          PDE.Parabolic.WeakHarnack.negTopConst d χ A₂ β₂ m₂ A₃ β₃ m₃ c₀)) *
        essInf (fun z => ENNReal.ofReal (u z + ε)) (volume.restrict
          (Set.Ioo (1 / 2 : ℝ) (3 / 4) ×ˢ sourceBall 0 (1 / 2))) := by
  obtain ⟨c₀, htail⟩ := c8_shifted_caloric_normalized_iteration_tails d hκ
  refine ⟨c₀, ?_⟩
  intro ρ α hell u G hcal hu0 ε hε hgain
  obtain ⟨v, k, hv, hvpos, heq, hlogpos, hlogneg⟩ :=
    htail ρ α hell u G hcal hu0 ε hε
  obtain ⟨hu, hu0', huv, hvg, hlower⟩ :=
    c8_shifted_representative_iteration_interfaces u v ε hv hvpos hu0 heq
  have hfin := c8_shifted_representative_initial_moment hκ hell hcal hu0 hε v hv heq hqχ
  obtain ⟨hpos, hneg, hinner⟩ := hgain v hv hvpos heq
  exact c8_normalized_nested_gains_to_time_first_norm hχ hA₁ hm₁ hq hA₂ hβ₂ hm₂
    hA₃ hβ₃ hm₃ hε (fun z => u z + ε) v hv hu hu0' hvg hlower huv hvpos hfin
    hpos hneg hinner hlogpos hlogneg

/-- Uniform nested gains imply the unshifted caloric weak Harnack estimate. -/
theorem c8_native_unit_weak_harnack_of_nested_gains (d : ℕ) (hd : 2 ≤ d)
    (κ : ℝ) (hκ : 0 < κ) {χ A₁ m₁ q A₂ β₂ m₂ A₃ β₃ m₃ : ℝ}
    (hχ : 1 < χ) (hA₁ : 1 ≤ A₁) (hm₁ : 0 < m₁) (hq : 0 < q)
    (hA₂ : 1 ≤ A₂) (hβ₂ : 0 ≤ β₂) (hm₂ : 0 < m₂)
    (hA₃ : 1 ≤ A₃) (hβ₃ : 0 ≤ β₃) (hm₃ : 0 < m₃) (hqχ : q * χ ≤ 2)
    (hgain : ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
      IsUniformlyElliptic κ ρ α → ∀ (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d),
      IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1) u G →
      (∀ᵐ z ∂volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1), 0 ≤ u z) →
      ∀ ε : ℝ, 0 < ε →
    (∀ (v : Vec d × ℝ → ℝ), Measurable v → (∀ z, 0 < v z) →
      (∀ᵐ z ∂volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1),
        v (z.2, z.1) = u z + ε) →
      (∀ σ' σ : ℝ, 1 / 2 ≤ σ' → σ' < σ → σ ≤ 1 → ∀ p : ℝ, 0 < p → p ≤ q →
      eLpNorm v (ENNReal.ofReal (χ * p))
        ((PDE.Parabolic.WeakHarnack.cylMeasure (PDE.Parabolic.WeakHarnack.posCyl d 1)).restrict
          (PDE.Parabolic.WeakHarnack.posCyl d σ')) ≤
      ENNReal.ofReal ((A₁ * (σ - σ') ^ (-m₁)) ^ (1 / p)) *
      eLpNorm v (ENNReal.ofReal p)
        ((PDE.Parabolic.WeakHarnack.cylMeasure (PDE.Parabolic.WeakHarnack.posCyl d 1)).restrict
          (PDE.Parabolic.WeakHarnack.posCyl d σ))) ∧
      (∀ σ' σ : ℝ, 1 / 2 ≤ σ' → σ' < σ → σ ≤ 1 → ∀ p : ℝ, 0 < p →
      eLpNorm (fun z => 1 / max ε (v (z.1, z.2 + 3 / 4))) (ENNReal.ofReal (χ * p))
        ((PDE.Parabolic.WeakHarnack.cylMeasure (PDE.Parabolic.WeakHarnack.negCyl d 1)).restrict
          (PDE.Parabolic.WeakHarnack.negCyl d σ')) ≤
      ENNReal.ofReal ((A₂ * (1 + p) ^ β₂ * (σ - σ') ^ (-m₂)) ^ (1 / p)) *
      eLpNorm (fun z => 1 / max ε (v (z.1, z.2 + 3 / 4))) (ENNReal.ofReal p)
        ((PDE.Parabolic.WeakHarnack.cylMeasure (PDE.Parabolic.WeakHarnack.negCyl d 1)).restrict
          (PDE.Parabolic.WeakHarnack.negCyl d σ))) ∧
      (∀ σ' σ : ℝ, 1 / 2 ≤ σ' → σ' < σ → σ ≤ 1 → ∀ p : ℝ, 0 < p →
      eLpNorm (fun z => 1 / max ε (v (z.1, z.2 + 3 / 4))) (ENNReal.ofReal (χ * p))
        ((PDE.Parabolic.WeakHarnack.cylMeasure (PDE.Parabolic.WeakHarnack.negCylInner d 1)).restrict
          (PDE.Parabolic.WeakHarnack.negCylInner d σ')) ≤
      ENNReal.ofReal ((A₃ * (1 + p) ^ β₃ * (σ - σ') ^ (-m₃)) ^ (1 / p)) *
      eLpNorm (fun z => 1 / max ε (v (z.1, z.2 + 3 / 4))) (ENNReal.ofReal p)
        ((PDE.Parabolic.WeakHarnack.cylMeasure (PDE.Parabolic.WeakHarnack.negCylInner d 1)).restrict
          (PDE.Parabolic.WeakHarnack.negCylInner d σ))))) :
    ∃ p C : ℝ, 0 < p ∧ 0 < C ∧ ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
      IsUniformlyElliptic κ ρ α → ∀ (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d),
        IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1) u G →
        (∀ᵐ z ∂volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1), 0 ≤ u z) →
        eLpNorm u (ENNReal.ofReal p)
          (volume.restrict (Set.Ioo (-3/4 : ℝ) (-1/2) ×ˢ sourceBall 0 (1/2))) ≤
        ENNReal.ofReal C * essInf (fun z : ℝ × Vec d => ENNReal.ofReal (u z))
          (volume.restrict (Set.Ioo (1/2 : ℝ) (3/4) ×ˢ sourceBall 0 (1/2))) := by
  obtain ⟨c₀, hc₀⟩ := c8_shifted_caloric_harnack_of_nested_gains d hκ hχ hA₁ hm₁ hq
    hA₂ hβ₂ hm₂ hA₃ hβ₃ hm₃ hqχ
  let D : ℝ≥0∞ := (volume (PDE.Parabolic.WeakHarnack.posCyl d (1 / 2))) ^ (1 / (q * χ)) *
    ENNReal.ofReal ((PDE.Parabolic.WeakHarnack.posVolRatio d) ^ (1 / (q * χ)) *
      PDE.Bombieri.giustiConst (1 / 2) (q * χ)
        (max c₀ (PDE.ParabIter.posC χ A₁ m₁ q)) (PDE.ParabIter.posM χ m₁ q) *
      PDE.Parabolic.WeakHarnack.negTopConst d χ A₂ β₂ m₂ A₃ β₃ m₃ c₀)
  have hD : D ≠ ⊤ := ENNReal.mul_ne_top
    (ENNReal.rpow_ne_top_of_nonneg (div_nonneg zero_le_one (mul_pos hq (by linarith)).le)
      (PDE.Parabolic.WeakHarnack.volume_posCyl_ne_top (by norm_num))) ENNReal.ofReal_ne_top
  have hDle : D ≤ ENNReal.ofReal (D.toReal + 1) := by
    calc
      D = ENNReal.ofReal D.toReal := (ENNReal.ofReal_toReal hD).symm
      _ ≤ ENNReal.ofReal (D.toReal + 1) := ENNReal.ofReal_le_ofReal (by linarith)
  apply c8_native_unit_weak_harnack_of_shifted d hd κ hκ
  refine ⟨q * χ, D.toReal + 1, mul_pos hq (by linarith), by positivity, ?_⟩
  intro ρ α hell u G hcal hu0 ε hε
  apply (hc₀ ρ α hell u G hcal hu0 ε hε (hgain ρ α hell u G hcal hu0 ε hε)).trans
  change D * _ ≤ _
  exact mul_le_mul_left hDle _

/-- A shifted caloric representative has the same positive-cylinder moments as the field. -/
theorem c8_shifted_representative_positive_nested_norm {d : ℕ}
    (u : ℝ × Vec d → ℝ) (v : Vec d × ℝ → ℝ) (ε : ℝ)
    (heq : ∀ᵐ z ∂volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1),
      v (z.2, z.1) = u z + ε) (σ : ℝ) (p : ℝ≥0∞) :
    eLpNorm v p
      ((PDE.Parabolic.WeakHarnack.cylMeasure (PDE.Parabolic.WeakHarnack.posCyl d 1)).restrict
        (PDE.Parabolic.WeakHarnack.posCyl d σ)) =
    eLpNorm (fun z : Vec d × ℝ => u (z.2, z.1) + ε) p
      ((PDE.Parabolic.WeakHarnack.cylMeasure (PDE.Parabolic.WeakHarnack.posCyl d 1)).restrict
        (PDE.Parabolic.WeakHarnack.posCyl d σ)) := by
  let T := Set.Ioo (-7/8 : ℝ) (-3/8) ×ˢ sourceBall (0 : Vec d) (3/4)
  have hsub : T ⊆ Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall (0 : Vec d) 1 := by
    intro z hz
    refine ⟨⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩, ?_⟩
    change euclideanNorm (z.2 - 0) < 1
    have hb : euclideanNorm (z.2 - 0) < 3/4 := hz.2
    linarith
  have hmap : Measure.map (Prod.swap : ℝ × Vec d → Vec d × ℝ) (volume.restrict T) =
      volume.restrict (PDE.Parabolic.WeakHarnack.posCyl d 1) := by
    convert c8_posCyl_swap_measure d 1 (by norm_num) using 1 <;> norm_num [T]
  have he : v =ᵐ[volume.restrict (PDE.Parabolic.WeakHarnack.posCyl d 1)]
      (fun z : Vec d × ℝ => u (z.2, z.1) + ε) := by
    rw [← hmap]
    apply MeasurableEquiv.prodComm.measurableEmbedding.ae_map_iff.mpr
    exact heq.filter_mono (ae_mono (Measure.restrict_mono_set volume hsub))
  apply eLpNorm_congr_ae
  apply ae_restrict_of_ae
  exact Measure.ae_smul_measure he _

/-- A positive nested gain for the shifted field transfers to its iteration representative. -/
theorem c8_shifted_representative_positive_nested_gain {d : ℕ}
    (u : ℝ × Vec d → ℝ) (v : Vec d × ℝ → ℝ) (ε χ A m q : ℝ)
    (heq : ∀ᵐ z ∂volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1),
      v (z.2, z.1) = u z + ε)
    (hgain : ∀ σ' σ : ℝ, 1 / 2 ≤ σ' → σ' < σ → σ ≤ 1 → ∀ p : ℝ, 0 < p → p ≤ q →
      eLpNorm (fun z : Vec d × ℝ => u (z.2, z.1) + ε) (ENNReal.ofReal (χ * p))
        ((PDE.Parabolic.WeakHarnack.cylMeasure (PDE.Parabolic.WeakHarnack.posCyl d 1)).restrict
          (PDE.Parabolic.WeakHarnack.posCyl d σ')) ≤
      ENNReal.ofReal ((A * (σ - σ') ^ (-m)) ^ (1 / p)) *
      eLpNorm (fun z : Vec d × ℝ => u (z.2, z.1) + ε) (ENNReal.ofReal p)
        ((PDE.Parabolic.WeakHarnack.cylMeasure (PDE.Parabolic.WeakHarnack.posCyl d 1)).restrict
          (PDE.Parabolic.WeakHarnack.posCyl d σ))) :
    ∀ σ' σ : ℝ, 1 / 2 ≤ σ' → σ' < σ → σ ≤ 1 → ∀ p : ℝ, 0 < p → p ≤ q →
      eLpNorm v (ENNReal.ofReal (χ * p))
        ((PDE.Parabolic.WeakHarnack.cylMeasure (PDE.Parabolic.WeakHarnack.posCyl d 1)).restrict
          (PDE.Parabolic.WeakHarnack.posCyl d σ')) ≤
      ENNReal.ofReal ((A * (σ - σ') ^ (-m)) ^ (1 / p)) *
      eLpNorm v (ENNReal.ofReal p)
        ((PDE.Parabolic.WeakHarnack.cylMeasure (PDE.Parabolic.WeakHarnack.posCyl d 1)).restrict
          (PDE.Parabolic.WeakHarnack.posCyl d σ)) := by
  intro σ' σ hσ' hσσ' hσ p hp hpq
  rw [c8_shifted_representative_positive_nested_norm u v ε heq σ' (ENNReal.ofReal (χ * p)),
    c8_shifted_representative_positive_nested_norm u v ε heq σ (ENNReal.ofReal p)]
  exact hgain σ' σ hσ' hσσ' hσ p hp hpq

/-- The late translated outer cylinder lies in the full source cylinder. -/
theorem c8_lateNegCyl_one_subset_full (d : ℕ) :
    c8LateNegCyl d 1 ⊆ sourceBall (0 : Vec d) 1 ×ˢ Set.Ioo (-1 : ℝ) 1 := by
  intro z hz
  have hs := c8_lateNegCyl_one_subset_slab (t₀ := (-11 / 32 : ℝ)) (by norm_num) hz
  refine ⟨?_, ⟨by linarith [hs.2.1], by linarith [hs.2.2]⟩⟩
  rw [c8_sourceBall_eq_euclideanBall 0 (by norm_num)]
  exact PDE.euclideanBall_mono (by norm_num) (by norm_num) hs.1

/-- Reciprocal-power norms are unchanged by the shifted caloric representative. -/
theorem c8_shifted_representative_negative_nested_norm {d : ℕ}
    (u : ℝ × Vec d → ℝ) (v : Vec d × ℝ → ℝ) (ε : ℝ)
    (heq : ∀ᵐ z ∂volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1),
      v (z.2, z.1) = u z + ε)
    (S T : Set (Vec d × ℝ)) (hS : S ⊆ PDE.Parabolic.WeakHarnack.negCyl d 1)
    (p : ℝ≥0∞) :
    eLpNorm (fun z => 1 / max ε (v (z.1, z.2 + 3 / 4))) p
      ((PDE.Parabolic.WeakHarnack.cylMeasure S).restrict T) =
    eLpNorm (fun z => 1 / max ε (u (z.2 + 3 / 4, z.1) + ε)) p
      ((PDE.Parabolic.WeakHarnack.cylMeasure S).restrict T) := by
  have hmap : Measure.map (Prod.swap : ℝ × Vec d → Vec d × ℝ)
      (volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall (0 : Vec d) 1)) =
      volume.restrict (sourceBall (0 : Vec d) 1 ×ˢ Set.Ioo (-1 : ℝ) 1) := by
    simp only [Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.prod_swap]
  have hfull : ∀ᵐ z ∂volume.restrict (sourceBall (0 : Vec d) 1 ×ˢ Set.Ioo (-1 : ℝ) 1),
      v z = u (z.2, z.1) + ε := by
    rw [← hmap]
    apply MeasurableEquiv.prodComm.measurableEmbedding.ae_map_iff.mpr
    exact heq
  have hlate := hfull.filter_mono (ae_mono (Measure.restrict_mono_set volume
    (c8_lateNegCyl_one_subset_full d)))
  have htrans : ∀ᵐ z ∂volume.restrict (PDE.Parabolic.WeakHarnack.negCyl d 1),
      v (z.1, z.2 + 3 / 4) = u (z.2 + 3 / 4, z.1) + ε := by
    rw [← c8_lateNegCyl_measure_map (d := d) 1] at hlate
    have hf : MeasurableEmbedding (fun z : Vec d × ℝ => (z.1, z.2 + 3 / 4)) := by
      have hf' : (fun z : Vec d × ℝ => (z.1, z.2 + 3 / 4)) =
          fun z => z + ((0, 3 / 4) : Vec d × ℝ) := by
        funext z
        simp [Prod.add_def]
      rw [hf']
      exact (Homeomorph.addRight ((0, 3 / 4) : Vec d × ℝ)).measurableEmbedding
    exact hf.ae_map_iff.mp hlate
  have hSae := htrans.filter_mono (ae_mono (Measure.restrict_mono_set volume hS))
  apply eLpNorm_congr_ae
  apply ae_restrict_of_ae
  exact (Measure.ae_smul_measure hSae _).mono fun _ h =>
    congrArg (fun x : ℝ => 1 / max ε x) h


/-- An inverse gain for the shifted field transfers to the caloric representative. -/
theorem c8_shifted_representative_negative_nested_gain {d : ℕ}
    (u : ℝ × Vec d → ℝ) (v : Vec d × ℝ → ℝ) (ε χ A β m : ℝ)
    (heq : ∀ᵐ z ∂volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1),
      v (z.2, z.1) = u z + ε)
    (S : Set (Vec d × ℝ)) (T : ℝ → Set (Vec d × ℝ))
    (hS : S ⊆ PDE.Parabolic.WeakHarnack.negCyl d 1)
    (hgain : ∀ σ' σ : ℝ, 1 / 2 ≤ σ' → σ' < σ → σ ≤ 1 → ∀ p : ℝ, 0 < p →
      eLpNorm (fun z => 1 / max ε (u (z.2 + 3 / 4, z.1) + ε))
        (ENNReal.ofReal (χ * p)) ((PDE.Parabolic.WeakHarnack.cylMeasure S).restrict (T σ')) ≤
      ENNReal.ofReal ((A * (1 + p) ^ β * (σ - σ') ^ (-m)) ^ (1 / p)) *
      eLpNorm (fun z => 1 / max ε (u (z.2 + 3 / 4, z.1) + ε))
        (ENNReal.ofReal p) ((PDE.Parabolic.WeakHarnack.cylMeasure S).restrict (T σ))) :
    ∀ σ' σ : ℝ, 1 / 2 ≤ σ' → σ' < σ → σ ≤ 1 → ∀ p : ℝ, 0 < p →
      eLpNorm (fun z => 1 / max ε (v (z.1, z.2 + 3 / 4)))
        (ENNReal.ofReal (χ * p)) ((PDE.Parabolic.WeakHarnack.cylMeasure S).restrict (T σ')) ≤
      ENNReal.ofReal ((A * (1 + p) ^ β * (σ - σ') ^ (-m)) ^ (1 / p)) *
      eLpNorm (fun z => 1 / max ε (v (z.1, z.2 + 3 / 4)))
        (ENNReal.ofReal p) ((PDE.Parabolic.WeakHarnack.cylMeasure S).restrict (T σ)) := by
  intro σ' σ hσ' hσσ' hσ p hp
  rw [c8_shifted_representative_negative_nested_norm u v ε heq S (T σ') hS
      (ENNReal.ofReal (χ * p)),
    c8_shifted_representative_negative_nested_norm u v ε heq S (T σ) hS
      (ENNReal.ofReal p)]
  exact hgain σ' σ hσ' hσσ' hσ p hp

/-- Uniform gains for the shifted field imply the native weak Harnack estimate.
The positive nested gain is the c5 producer (with c20 slice-mass and c13 energy
inputs); the two inverse nested gains require the c17 inverse gain and its
radius/translation assembly. Their full statements are retained as hypotheses. -/
theorem c8_native_unit_weak_harnack_of_field_nested_gains (d : ℕ) (hd : 2 ≤ d)
    (κ : ℝ) (hκ : 0 < κ) {χ A₁ m₁ q A₂ β₂ m₂ A₃ β₃ m₃ : ℝ}
    (hχ : 1 < χ) (hA₁ : 1 ≤ A₁) (hm₁ : 0 < m₁) (hq : 0 < q)
    (hA₂ : 1 ≤ A₂) (hβ₂ : 0 ≤ β₂) (hm₂ : 0 < m₂)
    (hA₃ : 1 ≤ A₃) (hβ₃ : 0 ≤ β₃) (hm₃ : 0 < m₃) (hqχ : q * χ ≤ 2)
    (hpos : ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
      IsUniformlyElliptic κ ρ α → ∀ (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d),
      IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1) u G →
      (∀ᵐ z ∂volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1), 0 ≤ u z) →
      ∀ ε : ℝ, 0 < ε →
      (∀ σ' σ : ℝ, 1 / 2 ≤ σ' → σ' < σ → σ ≤ 1 → ∀ p : ℝ, 0 < p → p ≤ q →
      eLpNorm (fun z : Vec d × ℝ => u (z.2, z.1) + ε) (ENNReal.ofReal (χ * p))
        ((PDE.Parabolic.WeakHarnack.cylMeasure (PDE.Parabolic.WeakHarnack.posCyl d 1)).restrict
          (PDE.Parabolic.WeakHarnack.posCyl d σ')) ≤
      ENNReal.ofReal ((A₁ * (σ - σ') ^ (-m₁)) ^ (1 / p)) *
      eLpNorm (fun z : Vec d × ℝ => u (z.2, z.1) + ε) (ENNReal.ofReal p)
        ((PDE.Parabolic.WeakHarnack.cylMeasure (PDE.Parabolic.WeakHarnack.posCyl d 1)).restrict
          (PDE.Parabolic.WeakHarnack.posCyl d σ))))
    (hneg : ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
      IsUniformlyElliptic κ ρ α → ∀ (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d),
      IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1) u G →
      (∀ᵐ z ∂volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1), 0 ≤ u z) →
      ∀ ε : ℝ, 0 < ε →
      (∀ σ' σ : ℝ, 1 / 2 ≤ σ' → σ' < σ → σ ≤ 1 → ∀ p : ℝ, 0 < p →
      eLpNorm (fun z => 1 / max ε (u (z.2 + 3 / 4, z.1) + ε)) (ENNReal.ofReal (χ * p))
        ((PDE.Parabolic.WeakHarnack.cylMeasure (PDE.Parabolic.WeakHarnack.negCyl d 1)).restrict
          (PDE.Parabolic.WeakHarnack.negCyl d σ')) ≤
      ENNReal.ofReal ((A₂ * (1 + p) ^ β₂ * (σ - σ') ^ (-m₂)) ^ (1 / p)) *
      eLpNorm (fun z => 1 / max ε (u (z.2 + 3 / 4, z.1) + ε)) (ENNReal.ofReal p)
        ((PDE.Parabolic.WeakHarnack.cylMeasure (PDE.Parabolic.WeakHarnack.negCyl d 1)).restrict
          (PDE.Parabolic.WeakHarnack.negCyl d σ))))
    (hinner : ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
      IsUniformlyElliptic κ ρ α → ∀ (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d),
      IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1) u G →
      (∀ᵐ z ∂volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1), 0 ≤ u z) →
      ∀ ε : ℝ, 0 < ε →
      (∀ σ' σ : ℝ, 1 / 2 ≤ σ' → σ' < σ → σ ≤ 1 → ∀ p : ℝ, 0 < p →
      eLpNorm (fun z => 1 / max ε (u (z.2 + 3 / 4, z.1) + ε)) (ENNReal.ofReal (χ * p))
        ((PDE.Parabolic.WeakHarnack.cylMeasure (PDE.Parabolic.WeakHarnack.negCylInner d 1)).restrict
          (PDE.Parabolic.WeakHarnack.negCylInner d σ')) ≤
      ENNReal.ofReal ((A₃ * (1 + p) ^ β₃ * (σ - σ') ^ (-m₃)) ^ (1 / p)) *
      eLpNorm (fun z => 1 / max ε (u (z.2 + 3 / 4, z.1) + ε)) (ENNReal.ofReal p)
        ((PDE.Parabolic.WeakHarnack.cylMeasure (PDE.Parabolic.WeakHarnack.negCylInner d 1)).restrict
          (PDE.Parabolic.WeakHarnack.negCylInner d σ)))) :
    ∃ p C : ℝ, 0 < p ∧ 0 < C ∧ ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
      IsUniformlyElliptic κ ρ α → ∀ (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d),
        IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1) u G →
        (∀ᵐ z ∂volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1), 0 ≤ u z) →
        eLpNorm u (ENNReal.ofReal p)
          (volume.restrict (Set.Ioo (-3/4 : ℝ) (-1/2) ×ˢ sourceBall 0 (1/2))) ≤
        ENNReal.ofReal C * essInf (fun z : ℝ × Vec d => ENNReal.ofReal (u z))
          (volume.restrict (Set.Ioo (1/2 : ℝ) (3/4) ×ˢ sourceBall 0 (1/2))) := by
  apply c8_native_unit_weak_harnack_of_nested_gains d hd κ hκ hχ hA₁ hm₁ hq
    hA₂ hβ₂ hm₂ hA₃ hβ₃ hm₃ hqχ
  intro ρ α hell u G hcal hu ε hε v hv hvpos heq
  have hp := hpos ρ α hell u G hcal hu ε hε
  have hn := hneg ρ α hell u G hcal hu ε hε
  have hni := hinner ρ α hell u G hcal hu ε hε
  refine ⟨c8_shifted_representative_positive_nested_gain u v ε χ A₁ m₁ q heq hp, ?_, ?_⟩
  · exact c8_shifted_representative_negative_nested_gain u v ε χ A₂ β₂ m₂ heq
      (PDE.Parabolic.WeakHarnack.negCyl d 1) (PDE.Parabolic.WeakHarnack.negCyl d)
      subset_rfl hn
  · exact c8_shifted_representative_negative_nested_gain u v ε χ A₃ β₃ m₃ heq
      (PDE.Parabolic.WeakHarnack.negCylInner d 1) (PDE.Parabolic.WeakHarnack.negCylInner d)
      ((PDE.Parabolic.WeakHarnack.negCylInner_one (d := d)).subset.trans
        (PDE.Parabolic.WeakHarnack.negCyl_mono (by norm_num) (by norm_num))) hni

end EinsteinFull.Calculus
