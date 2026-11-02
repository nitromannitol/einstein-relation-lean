import EinsteinFull.Calculus.C20TubeSignedTruncationIntegratedEnergy
import EinsteinFull.Calculus.C20TubePositivePowerNormLimit

open EinsteinRelation MeasureTheory Filter EinsteinFull.External.Source.GMP
open PDE hiding Vec Mat
open PDE.Parabolic.LocalMax
open scoped ENNReal Topology

namespace EinsteinFull.Calculus

/-- A symmetric truncated power has uniformly controlled derivative and
nonnegative curvature on the whole real line. -/
theorem b_symmetric_truncated_power_uniform_structure {p ε : ℝ}
    (hp : 2 ≤ p) (hε : 0 < ε) (n : ℕ) :
    let F := fun s => powF p ε (n : ℝ) s + powF p ε (n : ℝ) (-s)
    ContDiff ℝ 2 F ∧
    (∃ M : ℝ, 0 ≤ M ∧ ∀ s, |deriv (deriv F) s| ≤ M) ∧
    ∀ s, 0 ≤ F s ∧ 0 ≤ deriv (deriv F) s ∧
      (deriv F s) ^ 2 ≤ 8 * deriv (deriv F) s * F s := by
  let f := powF p ε (n : ℝ)
  let F : ℝ → ℝ := fun s => f s + f (-s)
  let H : ℝ → ℝ := fun s => F s - 2 * f 0
  have hder : deriv H = deriv F := by
    funext s
    exact deriv_sub_const (2 * f 0)
  have hf : ContDiff ℝ 2 f := powF_contDiff hε (Nat.cast_nonneg n)
  have hF : ContDiff ℝ 2 F := hf.add (hf.comp contDiff_neg)
  obtain ⟨_, M, hM, hbound⟩ := c20_signed_truncation_regular p ε hp hε n
  have hbound' : ∀ s, |deriv (deriv F) s| ≤ M := by
    intro s
    have hh := hbound s
    change |deriv (deriv H) s| ≤ M at hh
    rwa [hder] at hh
  refine ⟨hF, ⟨M, hM, hbound'⟩, ?_⟩
  intro s
  have hFnonneg : 0 ≤ F s := by
    exact add_nonneg (c5_all_real_truncated_power_structure hp hε n s).1
      (c5_all_real_truncated_power_structure hp hε n (-s)).1
  have hcurv : 0 ≤ deriv (deriv F) s := by
    have hh := c5_symmetric_truncated_energy_curvature_nonneg hp hε n s
    change 0 ≤ deriv (deriv H) s at hh
    rwa [hder] at hh
  have hstruct : (deriv F s) ^ 2 ≤
      2 * (2 + p / (p - 1)) * deriv (deriv F) s * F s := by
    have hh := c5_symmetric_truncated_energy_derivative_bound hp hε n s
    change (deriv H s) ^ 2 ≤
      2 * (2 + p / (p - 1)) * deriv (deriv H) s * F s at hh
    rwa [hder] at hh
  have hcoeff : 2 * (2 + p / (p - 1)) ≤ 8 := by
    have hh := c5_signed_truncation_coefficient_le_four hp
    linarith
  refine ⟨hFnonneg, hcurv, hstruct.trans ?_⟩
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcoeff hcurv) hFnonneg

/-- Actual weighted caloric energy and time-slice bounds for signed truncated
powers. The cutoff constant is uniform in the coefficients, solution, exponent,
regularization and truncation. -/
theorem b_weighted_signed_truncation_cutoff_energy {d : ℕ} {κ R a b : ℝ}
    (hκ : 0 < κ) (hR : 0 < R) (hab : a < b)
    (η : ℝ × Vec d → ℝ) (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hηc : HasCompactSupport η)
    (hηs : tsupport η ⊆ Set.Ioo a b ×ˢ sourceBall 0 R) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
      IsUniformlyElliptic κ ρ α →
      ∀ (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d),
      IsWeightedCaloric ρ α (Set.Ioo a b) (sourceBall 0 R) u G →
      ∀ p ε : ℝ, 2 ≤ p → 0 < ε → ∀ n : ℕ,
      let F := fun s => powF p ε (n : ℝ) s + powF p ε (n : ℝ) (-s)
      (∀ᵐ t ∂volume.restrict (Set.Ioo a b),
        (∫⁻ x in sourceBall 0 R, ENNReal.ofReal (ρ x * (F (u (t,x)) * η (t,x) ^ 2))) ≤
          ENNReal.ofReal B * ∫⁻ z in Set.Ioo a b ×ˢ sourceBall 0 R, ENNReal.ofReal (F (u z))) ∧
      (∫⁻ z in Set.Ioo a b ×ˢ sourceBall 0 R,
        ENNReal.ofReal (κ / 2 * deriv (deriv F) (u z) * euclideanSq (G z) * η z ^ 2)) ≤
          ENNReal.ofReal B * ∫⁻ z in Set.Ioo a b ×ˢ sourceBall 0 R, ENNReal.ofReal (F (u z)) := by
  obtain ⟨B, hB, hcut⟩ := c11_compact_cutoff_ramp_error_bound hκ η hη hηc 8 (by norm_num)
  refine ⟨B, hB, ?_⟩
  intro ρ α hell u G hcal p ε hp hε n
  obtain ⟨hF, ⟨M, hM, hder⟩, hstructure⟩ :=
    b_symmetric_truncated_power_uniform_structure hp hε n
  exact c11_weighted_caloric_renormalized_energy_bounds hκ hR hab ρ α hell u G hcal
    _ hF M hM hder η hη hηc hηs 8 B (by norm_num) hB
    (Filter.Eventually.of_forall (fun z => hstructure (u z)))
    (Filter.Eventually.of_forall (hcut ρ α hell))

/-- The two signed truncations are dominated by the shifted absolute power. -/
theorem b_symmetric_truncation_le_abs_power {p ε : ℝ}
    (hp : 2 ≤ p) (hε : 0 < ε) (n : ℕ) (s : ℝ) :
    powF p ε (n : ℝ) s + powF p ε (n : ℝ) (-s) ≤
      2 * Real.rpow (|s| + ε) p := by
  have h₁ := c5_all_real_truncated_power_le_abs hp hε n s
  have h₂ := c5_all_real_truncated_power_le_abs hp hε n (-s)
  rw [abs_neg] at h₂
  linarith

/-- The symmetric truncation mass is uniformly bounded by twice the absolute
shifted-power mass, for any measure and any exponent at least two. -/
theorem b_symmetric_truncation_mass_le_abs_power {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (u : X → ℝ) {p ε : ℝ}
    (hp : 2 ≤ p) (hε : 0 < ε) (n : ℕ) :
    (∫⁻ z, ENNReal.ofReal (powF p ε (n : ℝ) (u z) + powF p ε (n : ℝ) (-u z)) ∂μ) ≤
      2 * ∫⁻ z, ENNReal.ofReal (Real.rpow (|u z| + ε) p) ∂μ := by
  calc
    _ ≤ ∫⁻ z, ENNReal.ofReal (2 * Real.rpow (|u z| + ε) p) ∂μ := by
      apply lintegral_mono
      intro z
      exact ENNReal.ofReal_le_ofReal (b_symmetric_truncation_le_abs_power hp hε n (u z))
    _ = _ := by
      simp_rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      norm_num

/-- The regularized absolute p-moment converges to the pth power of the
unregularized Lp seminorm on a finite measure space. -/
theorem b_regularized_abs_moment_tendsto {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (u : X → ℝ)
    (p : ℝ) (hp : 0 < p) (hu : MemLp u (ENNReal.ofReal p) μ)
    (ε : ℕ → ℝ) (hε : ∀ n, 0 ≤ ε n) (hε0 : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun n => ∫⁻ x, ENNReal.ofReal (|u x| + ε n) ^ p ∂μ) atTop
      (𝓝 ((eLpNorm u (ENNReal.ofReal p) μ) ^ p)) := by
  have hv : MemLp (fun x => |u x|) (ENNReal.ofReal p) μ := by
    simpa only [Real.norm_eq_abs] using hu.norm
  have hlim := c20_regularized_positive_eLpNorm_tendsto μ (fun x => |u x|)
    (ae_of_all μ fun x => abs_nonneg (u x)) p hp hv ε hε hε0
  have heqnorm : eLpNorm (fun x => |u x|) (ENNReal.ofReal p) μ =
      eLpNorm u (ENNReal.ofReal p) μ := by
    simpa only [Real.norm_eq_abs] using eLpNorm_norm u hu.aestronglyMeasurable
  rw [heqnorm] at hlim
  have heq (n : ℕ) : (eLpNorm (fun x => |u x| + ε n) (ENNReal.ofReal p) μ)^p =
      ∫⁻ x, ENNReal.ofReal (|u x| + ε n)^p ∂μ := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.mpr hp).ne'
      ENNReal.ofReal_ne_top (hv.aestronglyMeasurable.add_const (ε n)),
      ENNReal.toReal_ofReal hp.le, ← ENNReal.rpow_mul, one_div_mul_cancel hp.ne',
      ENNReal.rpow_one]
    apply lintegral_congr
    intro x
    rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (add_nonneg (abs_nonneg _) (hε n))]
  have h : Tendsto (fun n => (eLpNorm (fun x => |u x| + ε n)
      (ENNReal.ofReal p) μ)^p) atTop (𝓝 ((eLpNorm u (ENNReal.ofReal p) μ)^p)) :=
    (ENNReal.continuous_rpow_const.tendsto (eLpNorm u (ENNReal.ofReal p) μ)).comp hlim
  simpa only [heq] using h



/-- Actual weighted caloricity bounds the slice mass of both signed
half-power truncations by one symmetric energy, with a constant uniform in
the exponent and in the coefficients. -/
theorem b_weighted_signed_truncation_slice_bound {d : ℕ} {κ R a b : ℝ}
    (hκ : 0 < κ) (hR : 0 < R) (hab : a < b)
    (η : ℝ × Vec d → ℝ) (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hηc : HasCompactSupport η)
    (hηs : tsupport η ⊆ Set.Ioo a b ×ˢ sourceBall 0 R) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
      IsUniformlyElliptic κ ρ α →
      ∀ (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d),
      IsWeightedCaloric ρ α (Set.Ioo a b) (sourceBall 0 R) u G →
      ∀ p ε : ℝ, 2 ≤ p → 0 < ε → ∀ n : ℕ,
      ∀ v : ℝ × Vec d → ℝ, (v = u ∨ v = fun z => -u z) →
      ∀ᵐ t ∂volume.restrict (Set.Ioo a b),
        (∫⁻ x in sourceBall 0 R, ENNReal.ofReal (ρ x) *
          ‖η (t,x) * powG p ε n (v (t,x))‖ₑ ^ (2 : ℝ)) ≤
        ENNReal.ofReal B * ∫⁻ z in Set.Ioo a b ×ˢ sourceBall 0 R,
          ENNReal.ofReal (powF p ε (n : ℝ) (u z) + powF p ε (n : ℝ) (-u z)) := by
  obtain ⟨B, hB, henergy⟩ := b_weighted_signed_truncation_cutoff_energy hκ hR hab η hη hηc hηs
  refine ⟨4*B, by positivity, ?_⟩
  intro ρ α hell u G hcal p ε hp hε n v hv
  have hFv : ∀ z, powF p ε (n : ℝ) (v z) + powF p ε (n : ℝ) (-v z) =
      powF p ε (n : ℝ) (u z) + powF p ε (n : ℝ) (-u z) := by
    intro z
    rcases hv with rfl | rfl
    · rfl
    · simp only [neg_neg, add_comm]
  have hslice := (henergy ρ α hell u G hcal p ε hp hε n).1
  filter_upwards [hslice] with t ht
  have heq : (∫⁻ x in sourceBall 0 R, ENNReal.ofReal (ρ x) *
        ENNReal.ofReal (η (t,x)^2 *
          (powF p ε (n : ℝ) (v (t,x)) + powF p ε (n : ℝ) (-v (t,x))))) =
      ∫⁻ x in sourceBall 0 R, ENNReal.ofReal (ρ x *
        ((powF p ε (n : ℝ) (u (t,x)) + powF p ε (n : ℝ) (-u (t,x))) * η (t,x)^2)) := by
    apply lintegral_congr
    intro x
    rw [← ENNReal.ofReal_mul (hκ.le.trans (hell.2.2 x).1), hFv]
    congr 1
    ring
  calc
    _ ≤ ENNReal.ofReal (2 + p / (p - 1)) *
        (∫⁻ x in sourceBall 0 R, ENNReal.ofReal (ρ x) *
          ENNReal.ofReal (η (t,x)^2 *
            (powF p ε (n : ℝ) (v (t,x)) + powF p ε (n : ℝ) (-v (t,x))))) :=
      c5_symmetric_truncated_power_slice_mass_le (fun x => v (t,x)) (fun x => η (t,x)) hp hε n
    _ ≤ ENNReal.ofReal (4 : ℝ) * (ENNReal.ofReal B *
        ∫⁻ z in Set.Ioo a b ×ˢ sourceBall 0 R,
          ENNReal.ofReal (powF p ε (n : ℝ) (u z) + powF p ε (n : ℝ) (-u z))) := by
      rw [heq]
      exact mul_le_mul' (ENNReal.ofReal_le_ofReal (c5_signed_truncation_coefficient_le_four hp)) ht
    _ = _ := by rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4), mul_assoc]


/-- Integrating the signed chain-rule estimate controls the actual coefficient
energy by symmetric dissipation and the cutoff-gradient cost. -/
theorem b_signed_truncated_cutoff_energy_integral {d : ℕ} {κ : ℝ}
    (hκ : 0 < κ) {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (hell : IsUniformlyElliptic κ ρ α) {I : Set ℝ} {U : Set (Vec d)}
    {u : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    (hcal : IsWeightedCaloric ρ α I U u G)
    (η : ℝ × Vec d → ℝ) (hη : Continuous η) (P : ℝ × Vec d → Vec d)
    {p ε : ℝ} (hp : 2 ≤ p) (hε : 0 < ε) (n : ℕ) :
    let F := fun s => powF p ε (n : ℝ) s + powF p ε (n : ℝ) (-s)
    (∫⁻ z in I ×ˢ U, ENNReal.ofReal
      (dot ((α z.2).mulVec
        (η z • (deriv (powG p ε n) (u z) • G z) + powG p ε n (u z) • P z))
        (η z • (deriv (powG p ε n) (u z) • G z) + powG p ε n (u z) • P z))) ≤
    ENNReal.ofReal (8 * κ⁻¹) *
      ((∫⁻ z in I ×ˢ U, ENNReal.ofReal
        (η z ^ 2 * deriv (deriv F) (u z) * euclideanSq (G z))) +
      ∫⁻ z in I ×ˢ U, ENNReal.ofReal (F (u z) * euclideanSq (P z))) := by
  dsimp only
  let F : ℝ → ℝ := fun s => powF p ε (n : ℝ) s + powF p ε (n : ℝ) (-s)
  let H : ℝ → ℝ := fun s => F s - 2 * powF p ε (n : ℝ) 0
  let A : ℝ × Vec d → ℝ := fun z => η z ^ 2 * deriv (deriv F) (u z) * euclideanSq (G z)
  let B : ℝ × Vec d → ℝ := fun z => F (u z) * euclideanSq (P z)
  have hder : deriv H = deriv F := by
    funext s
    exact deriv_sub_const (2 * powF p ε (n : ℝ) 0)
  have hF : ContDiff ℝ 2 F := (b_symmetric_truncated_power_uniform_structure hp hε n).1
  have hA : AEMeasurable (fun z => ENNReal.ofReal (A z)) (volume.restrict (I ×ˢ U)) := by
    have hF'' : Continuous (deriv (deriv F)) :=
      (PDE.Parabolic.Chain.contDiff_deriv_of_two hF).continuous_deriv_one
    have hsq : Continuous (fun v : Vec d => euclideanSq v) := by
      unfold euclideanSq dot
      fun_prop
    exact ENNReal.measurable_ofReal.comp_aemeasurable
      (((hη.measurable.aemeasurable.pow_const 2).mul
        (hF''.measurable.comp_aemeasurable hcal.1.aestronglyMeasurable.aemeasurable)).mul
        (hsq.measurable.comp_aemeasurable hcal.2.1.aemeasurable))
  have hC : 0 ≤ 8 * κ⁻¹ := by positivity
  have hcoeff : 2 * κ⁻¹ * (2 + p / (p - 1)) ≤ 8 * κ⁻¹ := by
    have hpbound := c5_signed_truncation_coefficient_le_four hp
    have hmul := mul_le_mul_of_nonneg_left hpbound (show 0 ≤ 2 * κ⁻¹ by positivity)
    nlinarith
  calc
    _ ≤ ∫⁻ z in I ×ˢ U, ENNReal.ofReal (8 * κ⁻¹) *
        (ENNReal.ofReal (A z) + ENNReal.ofReal (B z)) := by
      apply lintegral_mono
      intro z
      have hc : 0 ≤ A z + B z := by
        have hcurv := ((b_symmetric_truncated_power_uniform_structure hp hε n).2.2 (u z)).2.1
        have hF0 := ((b_symmetric_truncated_power_uniform_structure hp hε n).2.2 (u z)).1
        change 0 ≤ deriv (deriv F) (u z) at hcurv
        change 0 ≤ F (u z) at hF0
        exact add_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) hcurv)
          (PDE.vecNormSq_nonneg _)) (mul_nonneg hF0 (PDE.vecNormSq_nonneg _))
      have hpoint := c5_signed_truncated_power_cutoff_energy_pointwise hκ hell hp hε n
        (u z) z.2 (G z) (P z) (η z)
      change dot ((α z.2).mulVec
        (η z • (deriv (powG p ε n) (u z) • G z) + powG p ε n (u z) • P z))
        (η z • (deriv (powG p ε n) (u z) • G z) + powG p ε n (u z) • P z) ≤
        2 * κ⁻¹ * (2 + p / (p - 1)) *
          (η z ^ 2 * deriv (deriv H) (u z) * euclideanSq (G z) +
            F (u z) * euclideanSq (P z)) at hpoint
      rw [hder] at hpoint
      calc
        _ ≤ ENNReal.ofReal ((8 * κ⁻¹) * (A z + B z)) :=
          ENNReal.ofReal_le_ofReal (hpoint.trans (mul_le_mul_of_nonneg_right hcoeff hc))
        _ = ENNReal.ofReal (8 * κ⁻¹) * ENNReal.ofReal (A z + B z) :=
          ENNReal.ofReal_mul hC
        _ ≤ _ := mul_le_mul' le_rfl ENNReal.ofReal_add_le
    _ = _ := by rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_add_left' hA]


/-- A compact cutoff bounds the coefficient energy of each signed half-power
by the symmetric truncated mass, uniformly in the exponent. -/
theorem b_weighted_signed_truncation_cutoff_gradient_bound
    {d : ℕ} {κ R a b : ℝ} (hκ : 0 < κ) (hR : 0 < R) (hab : a < b)
    (η : ℝ × Vec d → ℝ) (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hηc : HasCompactSupport η)
    (hηs : tsupport η ⊆ Set.Ioo a b ×ˢ sourceBall 0 R) :
    ∃ E : ℝ≥0∞, E ≠ ⊤ ∧ ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
    IsUniformlyElliptic κ ρ α →
    ∀ (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d),
    IsWeightedCaloric ρ α (Set.Ioo a b) (sourceBall 0 R) u G →
    ∀ p ε : ℝ, 2 ≤ p → 0 < ε → ∀ n : ℕ,
      (∫⁻ z in Set.Ioo a b ×ˢ sourceBall 0 R, ENNReal.ofReal
        (dot ((α z.2).mulVec
          (η z • (deriv (powG p ε n) (u z) • G z) +
            powG p ε n (u z) • (fun j => fderiv ℝ η z (0, unitVector j))))
          (η z • (deriv (powG p ε n) (u z) • G z) +
            powG p ε n (u z) • (fun j => fderiv ℝ η z (0, unitVector j))))) ≤
      E * ∫⁻ z in Set.Ioo a b ×ˢ sourceBall 0 R,
        ENNReal.ofReal (powF p ε (n : ℝ) (u z) + powF p ε (n : ℝ) (-u z)) := by
  obtain ⟨B, hB, henergy⟩ := b_weighted_signed_truncation_cutoff_energy hκ hR hab η hη hηc hηs
  obtain ⟨_, ⟨D, hD, hd⟩, _⟩ := c18_compact_test_spatial_derivative_bounded η hη hηc
  have hsq (z : ℝ × Vec d) :
      euclideanSq (fun j => fderiv ℝ η z (0, unitVector j)) ≤ D ^ 2 := by
    have hn := hd z
    have hn0 : 0 ≤ euclideanNorm (fun j => fderiv ℝ η z (0, unitVector j)) := Real.sqrt_nonneg _
    have he : euclideanNorm (fun j => fderiv ℝ η z (0, unitVector j)) ^ 2 =
        euclideanSq (fun j => fderiv ℝ η z (0, unitVector j)) :=
      Real.sq_sqrt (PDE.vecNormSq_nonneg _)
    nlinarith
  let A : ℝ≥0∞ := ENNReal.ofReal (2 / κ) * ENNReal.ofReal B
  let C : ℝ≥0∞ := ENNReal.ofReal (8 * κ⁻¹)
  refine ⟨C * (A + ENNReal.ofReal (D ^ 2)),
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top,
        ENNReal.ofReal_ne_top⟩), ?_⟩
  intro ρ α hell u G hcal p ε hp hε n
  let F : ℝ → ℝ := fun s => powF p ε (n : ℝ) s + powF p ε (n : ℝ) (-s)
  let M : ℝ≥0∞ := ∫⁻ z in Set.Ioo a b ×ˢ sourceBall 0 R, ENNReal.ofReal (F (u z))
  have he := (henergy ρ α hell u G hcal p ε hp hε n).2
  have hfactor : 0 ≤ 2 / κ := by positivity
  have hpoint (z : ℝ × Vec d) :
      η z ^ 2 * deriv (deriv F) (u z) * euclideanSq (G z) =
      (2 / κ) * (κ / 2 * deriv (deriv F) (u z) * euclideanSq (G z) * η z ^ 2) := by
    field_simp
    <;> ring
  have hgrad : (∫⁻ z in Set.Ioo a b ×ˢ sourceBall 0 R, ENNReal.ofReal
      (η z ^ 2 * deriv (deriv F) (u z) * euclideanSq (G z))) ≤ A * M := by
    calc
      _ = ENNReal.ofReal (2 / κ) *
          (∫⁻ z in Set.Ioo a b ×ˢ sourceBall 0 R, ENNReal.ofReal
            (κ / 2 * deriv (deriv F) (u z) * euclideanSq (G z) * η z ^ 2)) := by
        simp_rw [hpoint, ENNReal.ofReal_mul hfactor]
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ ≤ ENNReal.ofReal (2 / κ) * (ENNReal.ofReal B * M) := by gcongr
      _ = A * M := by dsimp [A]; rw [mul_assoc]
  have herr : (∫⁻ z in Set.Ioo a b ×ˢ sourceBall 0 R, ENNReal.ofReal
      (F (u z) * euclideanSq (fun j => fderiv ℝ η z (0, unitVector j)))) ≤
      ENNReal.ofReal (D ^ 2) * M := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply lintegral_mono
    intro z
    change ENNReal.ofReal (F (u z) * euclideanSq (fun j => fderiv ℝ η z (0, unitVector j))) ≤
      ENNReal.ofReal (D ^ 2) * ENNReal.ofReal (F (u z))
    rw [← ENNReal.ofReal_mul (sq_nonneg D)]
    apply ENNReal.ofReal_le_ofReal
    have hF0 : 0 ≤ F (u z) :=
      ((b_symmetric_truncated_power_uniform_structure hp hε n).2.2 (u z)).1
    have hh := mul_le_mul_of_nonneg_left (hsq z) hF0
    nlinarith
  have hc := b_signed_truncated_cutoff_energy_integral hκ hell hcal η hη.continuous
    (fun z j => fderiv ℝ η z (0, unitVector j)) hp hε n
  calc
    _ ≤ C * ((∫⁻ z in Set.Ioo a b ×ˢ sourceBall 0 R, ENNReal.ofReal
          (η z ^ 2 * deriv (deriv F) (u z) * euclideanSq (G z))) +
        ∫⁻ z in Set.Ioo a b ×ˢ sourceBall 0 R, ENNReal.ofReal
          (F (u z) * euclideanSq (fun j => fderiv ℝ η z (0, unitVector j)))) := hc
    _ ≤ C * (A * M + ENNReal.ofReal (D ^ 2) * M) := by gcongr
    _ = _ := by rw [← add_mul, mul_assoc]


/-- The genuine weighted equation gives a uniform signed Sobolev gain for
regularized moments on any pair of cylinders joined by a compact cutoff. -/
theorem b_weighted_signed_regularized_cutoff_gain
    (d : ℕ) (hd : 2 ≤ d) {κ R a b : ℝ}
    (hκ : 0 < κ) (hR : 0 < R) (hab : a < b)
    (η : ℝ × Vec d → ℝ) (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hηc : HasCompactSupport η)
    (hηs : tsupport η ⊆ Set.Ioo a b ×ˢ sourceBall 0 R)
    (htest : ∀ᵐ t ∂volume.restrict (Set.Ioo a b),
      IsSpatialTest (sourceBall 0 R) (fun x => η (t,x)))
    (K : Set (Vec d)) (hK : IsCompact K) (hKU : K ⊆ sourceBall 0 R)
    (hzero : ∀ t x, x ∉ K → η (t,x) = 0)
    (S : Set (ℝ × Vec d)) (hS : MeasurableSet S)
    (hSQ : S ⊆ Set.Ioo a b ×ˢ sourceBall 0 R)
    (hηone : ∀ z ∈ S, η z = 1) :
    ∃ C A E : ℝ≥0∞, C ≠ ⊤ ∧ A ≠ ⊤ ∧ E ≠ ⊤ ∧
    ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
    IsUniformlyElliptic κ ρ α →
    ∀ (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d),
    IsWeightedCaloric ρ α (Set.Ioo a b) (sourceBall 0 R) u G →
    ∀ p ε : ℝ, 2 ≤ p → 0 < ε →
    let M := ∫⁻ z in Set.Ioo a b ×ˢ sourceBall 0 R, ENNReal.ofReal (|u z| + ε) ^ p
    (∫⁻ z in S, ENNReal.ofReal (|u z| + ε) ^ (p * (((d : ℝ) + 2) / d))) ≤
      ENNReal.ofReal κ⁻¹ * (C * (A * M) ^ (2 / (d : ℝ)) * (E * M)) +
      ENNReal.ofReal κ⁻¹ * (C * (A * M) ^ (2 / (d : ℝ)) * (E * M)) := by
  obtain ⟨C, hC, hsob⟩ := c5_signed_cutoff_powG_sobolev_gain d hd κ hκ
  obtain ⟨A, hA, hslice⟩ := b_weighted_signed_truncation_slice_bound hκ hR hab η hη hηc hηs
  obtain ⟨E, hE, hgrad⟩ := b_weighted_signed_truncation_cutoff_gradient_bound hκ hR hab η hη hηc hηs
  refine ⟨C, ENNReal.ofReal A * 2, E * 2, hC,
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (by norm_num),
    ENNReal.mul_ne_top hE (by norm_num), ?_⟩
  intro ρ α hell u G hcal p ε hp hε
  let μ := volume.restrict (Set.Ioo a b ×ˢ sourceBall (0 : Vec d) R)
  let M : ℝ≥0∞ := ∫⁻ z, ENNReal.ofReal (|u z| + ε) ^ p ∂μ
  have hfinite : volume (Set.Ioo a b ×ˢ sourceBall (0 : Vec d) R) < ∞ := by
    letI : IsFiniteMeasure μ := c20_sourceCylinder_isFiniteMeasure a b R 0
    simpa [μ] using (measure_lt_top μ Set.univ)
  have hmom (v : ℝ × Vec d → ℝ) (hv : v = u ∨ v = fun z => -u z) (n : ℕ) :
      (∫⁻ z, ENNReal.ofReal (powF p ε (n : ℝ) (v z) + powF p ε (n : ℝ) (-v z)) ∂μ) ≤
        2 * M := by
    calc
      _ ≤ 2 * ∫⁻ z, ENNReal.ofReal (Real.rpow (|v z| + ε) p) ∂μ :=
        b_symmetric_truncation_mass_le_abs_power μ v hp hε n
      _ = 2 * M := by
        congr 1
        apply lintegral_congr
        intro z
        rw [ENNReal.ofReal_rpow_of_nonneg (by linarith [abs_nonneg (v z), abs_nonneg (u z)]) (by linarith)]
        rcases hv with rfl | rfl <;> simp [M]
  apply hsob ρ α hell (Set.Ioo a b) (sourceBall 0 R) measurableSet_Ioo
    (c17_isOpen_sourceBall 0 R) hfinite u G hcal η hη hηc htest K hK hKU hzero
    S hS hSQ hηone p ε hp hε ((ENNReal.ofReal A * 2) * M) ((E * 2) * M)
  · intro n v hv
    filter_upwards [hslice ρ α hell u G hcal p ε hp hε n v hv] with t ht
    calc
      _ ≤ ENNReal.ofReal A *
          (∫⁻ z, ENNReal.ofReal (powF p ε (n : ℝ) (u z) + powF p ε (n : ℝ) (-u z)) ∂μ) := ht
      _ ≤ ENNReal.ofReal A * (2 * M) := mul_le_mul' le_rfl (hmom u (Or.inl rfl) n)
      _ = _ := by rw [mul_assoc]
  · intro n v H hvH
    have hv : v = u ∨ v = fun z => -u z := by
      rcases hvH with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
    have hvcal : IsWeightedCaloric ρ α (Set.Ioo a b) (sourceBall 0 R) v H := by
      rcases hvH with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hcal
      · exact c11_weighted_caloric_neg hcal
    let f := powG p ε n
    let V : ℝ × Vec d → Vec d := fun z =>
      η z • (deriv f (v z) • H z) + f (v z) •
        (fun j => fderiv ℝ η z (0, unitVector j))
    have hf : ContDiff ℝ 1 f := powG_contDiff hε (Nat.cast_nonneg n)
    have hηd : Continuous (fun z => fun j => fderiv ℝ η z (0, unitVector j)) :=
      continuous_pi fun j => (hη.continuous_fderiv (by simp)).clm_apply continuous_const
    have hV : AEStronglyMeasurable V μ :=
      (hη.continuous.aestronglyMeasurable.smul
        ((hf.continuous_deriv_one.comp_aestronglyMeasurable hvcal.1.aestronglyMeasurable).smul hvcal.2.1)).add
        ((hf.continuous.comp_aestronglyMeasurable hvcal.1.aestronglyMeasurable).smul hηd.aestronglyMeasurable)
    have hfub := c11_weighted_coefficient_energy_lintegral_prod hell V hV
    rw [← hfub]
    calc
      _ ≤ E * (∫⁻ z, ENNReal.ofReal
            (powF p ε (n : ℝ) (v z) + powF p ε (n : ℝ) (-v z)) ∂μ) :=
        hgrad ρ α hell v H hvcal p ε hp hε n
      _ ≤ E * (2 * M) := mul_le_mul' le_rfl (hmom v hv n)
      _ = _ := by rw [mul_assoc]


/-- A finite, positive coefficient permits the removal of an absolute-value
regularization from any finite-exponent gain. -/
theorem b_remove_signed_regularization {X : Type*} [MeasurableSpace X]
    (μ ν : Measure X) [IsFiniteMeasure μ] (u : X → ℝ)
    (huμ : AEStronglyMeasurable u μ) (huν : AEStronglyMeasurable u ν)
    (p q : ℝ) (hp : 0 < p) (D : ℝ≥0∞) (hD : D ≠ ⊤) (hD0 : D ≠ 0)
    (hreg : ∀ ε : ℝ, 0 < ε →
      eLpNorm (fun x => |u x| + ε) (ENNReal.ofReal q) ν ≤
        D * eLpNorm (fun x => |u x| + ε) (ENNReal.ofReal p) μ) :
    eLpNorm u (ENNReal.ofReal q) ν ≤ D * eLpNorm u (ENNReal.ofReal p) μ := by
  by_cases ht : eLpNorm u (ENNReal.ofReal p) μ = ⊤
  · simp [ht, hD0]
  have humem : MemLp u (ENNReal.ofReal p) μ := lt_top_iff_ne_top.mpr ht
  have hav : MemLp (fun x => |u x|) (ENNReal.ofReal p) μ := by
    simpa only [Real.norm_eq_abs] using humem.norm
  let ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hε (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  have hε0 : Tendsto ε atTop (𝓝 0) := by
    simpa [ε] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hlim := c20_regularized_positive_eLpNorm_tendsto μ (fun x => |u x|)
    (ae_of_all μ fun x => abs_nonneg (u x)) p hp hav ε (fun n => (hε n).le) hε0
  have habs : eLpNorm (fun x => |u x|) (ENNReal.ofReal p) μ =
      eLpNorm u (ENNReal.ofReal p) μ := by
    simpa only [Real.norm_eq_abs] using eLpNorm_norm u huμ
  rw [habs] at hlim
  have hlim' := (ENNReal.continuous_const_mul hD).tendsto _ |>.comp hlim
  apply ge_of_tendsto hlim'
  apply Filter.Eventually.of_forall
  intro n
  have hmono : eLpNorm u (ENNReal.ofReal q) ν ≤
      eLpNorm (fun x => |u x| + ε n) (ENNReal.ofReal q) ν := by
    apply eLpNorm_mono_ae_real huν
    exact ae_of_all ν fun x => by
      rw [Real.norm_eq_abs]
      exact le_add_of_nonneg_right (hε n).le
  exact hmono.trans (hreg (ε n) (hε n))


/-- The weighted signed Sobolev gain on compactly nested cylinders, expressed
as a finite-exponent norm estimate with a uniform structural constant. -/
theorem b_weighted_signed_cutoff_norm_gain
    (d : ℕ) (hd : 2 ≤ d) {κ R a b : ℝ}
    (hκ : 0 < κ) (hR : 0 < R) (hab : a < b)
    (η : ℝ × Vec d → ℝ) (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hηc : HasCompactSupport η)
    (hηs : tsupport η ⊆ Set.Ioo a b ×ˢ sourceBall 0 R)
    (htest : ∀ᵐ t ∂volume.restrict (Set.Ioo a b),
      IsSpatialTest (sourceBall 0 R) (fun x => η (t,x)))
    (K : Set (Vec d)) (hK : IsCompact K) (hKU : K ⊆ sourceBall 0 R)
    (hzero : ∀ t x, x ∉ K → η (t,x) = 0)
    (S : Set (ℝ × Vec d)) (hS : MeasurableSet S)
    (hSQ : S ⊆ Set.Ioo a b ×ˢ sourceBall 0 R)
    (hηone : ∀ z ∈ S, η z = 1) :
    ∃ B : ℝ≥0∞, 1 ≤ B ∧ B ≠ ⊤ ∧
    ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
    IsUniformlyElliptic κ ρ α →
    ∀ (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d),
    IsWeightedCaloric ρ α (Set.Ioo a b) (sourceBall 0 R) u G →
    ∀ p : ℝ, 2 ≤ p →
      eLpNorm u (ENNReal.ofReal (p * (((d : ℝ) + 2) / d))) (volume.restrict S) ≤
        B ^ (1 / (p * (((d : ℝ) + 2) / d))) *
          eLpNorm u (ENNReal.ofReal p)
            (volume.restrict (Set.Ioo a b ×ˢ sourceBall 0 R)) := by
  obtain ⟨C, A, E, hC, hA, hE, hgain⟩ :=
    b_weighted_signed_regularized_cutoff_gain d hd hκ hR hab η hη hηc hηs
      htest K hK hKU hzero S hS hSQ hηone
  let s : ℝ := 2 / (d : ℝ)
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hs : 0 ≤ s := by dsimp [s]; positivity
  have hγ : ((d : ℝ) + 2) / d = 1 + s := by
    dsimp [s]
    field_simp
    <;> ring
  let B₀ : ℝ≥0∞ := 2 * ENNReal.ofReal κ⁻¹ * C * A ^ s * E
  have hB₀ : B₀ ≠ ⊤ := by
    dsimp [B₀]
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top (ENNReal.mul_ne_top
        (ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top) hC)
        (ENNReal.rpow_ne_top_of_nonneg hs hA)) hE
  let B : ℝ≥0∞ := 1 + B₀
  have hB1 : 1 ≤ B := by dsimp [B]; exact le_add_of_nonneg_right (show 0 ≤ B₀ from zero_le)
  have hBtop : B ≠ ⊤ := ENNReal.add_ne_top.mpr ⟨by norm_num, hB₀⟩
  refine ⟨B, hB1, hBtop, ?_⟩
  intro ρ α hell u G hcal p hp
  let μ := volume.restrict (Set.Ioo a b ×ˢ sourceBall (0 : Vec d) R)
  let ν := volume.restrict S
  letI : IsFiniteMeasure μ := c20_sourceCylinder_isFiniteMeasure a b R 0
  have huμ : AEStronglyMeasurable u μ := hcal.1.aestronglyMeasurable
  have huν : AEStronglyMeasurable u ν :=
    huμ.mono_measure (Measure.restrict_mono hSQ le_rfl)
  have hp0 : 0 < p := by linarith
  have hγ0 : 0 < ((d : ℝ) + 2) / d := by positivity
  have hr : 0 ≤ 1 / (p * (((d : ℝ) + 2) / d)) := by positivity
  have hroot0 : B ^ (1 / (p * (((d : ℝ) + 2) / d))) ≠ 0 := by
    apply ne_of_gt
    have hh := ENNReal.rpow_le_rpow hB1 hr
    rw [ENNReal.one_rpow] at hh
    exact lt_of_lt_of_le (by norm_num) hh
  have hroottop : B ^ (1 / (p * (((d : ℝ) + 2) / d))) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg hr hBtop
  apply b_remove_signed_regularization μ ν u huμ huν p
    (p * (((d : ℝ) + 2) / d)) hp0 _ hroottop hroot0
  intro ε hε
  let v : ℝ × Vec d → ℝ := fun z => |u z| + ε
  have hvμ : AEStronglyMeasurable v μ := (continuous_abs.comp_aestronglyMeasurable huμ).add_const ε
  have hvν : AEStronglyMeasurable v ν := (continuous_abs.comp_aestronglyMeasurable huν).add_const ε
  have hnonneg : ∀ z, 0 ≤ v z := fun z => add_nonneg (abs_nonneg _) hε.le
  have hmoment : (∫⁻ z, ENNReal.ofReal (v z) ^ (p * (1 + s)) ∂ν) ≤
      (2 * ENNReal.ofReal κ⁻¹ * C) *
        (A * (∫⁻ z, ENNReal.ofReal (v z) ^ p ∂μ)) ^ s *
        (E * (∫⁻ z, ENNReal.ofReal (v z) ^ p ∂μ)) := by
    have hh := hgain ρ α hell u G hcal p ε hp hε
    dsimp only at hh
    rw [hγ] at hh
    calc
      _ ≤ ENNReal.ofReal κ⁻¹ * (C *
          (A * (∫⁻ z, ENNReal.ofReal (v z) ^ p ∂μ)) ^ s *
          (E * (∫⁻ z, ENNReal.ofReal (v z) ^ p ∂μ))) +
          ENNReal.ofReal κ⁻¹ * (C *
          (A * (∫⁻ z, ENNReal.ofReal (v z) ^ p ∂μ)) ^ s *
          (E * (∫⁻ z, ENNReal.ofReal (v z) ^ p ∂μ))) := by
            simpa only [μ, ν, v, s] using hh
      _ = _ := by rw [← two_mul]; ring
  have hnorm := c11_moser_norm_step_of_nonnegative_moment_gain μ ν v hvμ hvν
    (ae_of_all μ hnonneg) (ae_of_all ν hnonneg) p s hp0 hs
    (2 * ENNReal.ofReal κ⁻¹ * C) A E hmoment
  rw [← hγ] at hnorm
  calc
    _ ≤ B₀ ^ (1 / (p * (((d : ℝ) + 2) / d))) * eLpNorm v (ENNReal.ofReal p) μ := hnorm
    _ ≤ _ := mul_le_mul' (ENNReal.rpow_le_rpow (le_add_self : B₀ ≤ B) hr) le_rfl


/-- Unit-cylinder signed gain with the quadratic exponent coefficient required
by the local maximum iteration. -/
theorem b_weighted_signed_unit_gain (d : ℕ) (hd : 2 ≤ d) (κ : ℝ) (hκ : 0 < κ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
      IsUniformlyElliptic κ ρ α →
      ∀ (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d),
      IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1) u G →
      ∀ p : ℝ, 2 ≤ p →
        eLpNorm u (ENNReal.ofReal (p * ((d : ℝ) + 2) / d))
          (volume.restrict (Set.Ioo (-(1/4 : ℝ)) (1/4) ×ˢ sourceBall 0 (1/2))) ≤
        ENNReal.ofReal (Real.rpow (C * p^2) (1/p)) *
          eLpNorm u (ENNReal.ofReal p)
            (volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1)) := by
  let ξ : Vec d → ℝ := PDE.canonicalBallCutoff (0 : Vec d) (1/2) 1
  let η : ℝ × Vec d → ℝ := fun z =>
    (cylTimeRamp (-1/2) ((-1/4 - (-1/2))/2) z.1 *
      timeRamp (1/2) (1/4) z.1) * ξ z.2
  let S : Set (ℝ × Vec d) :=
    Set.Ioo (-(1/4 : ℝ)) (1/4) ×ˢ sourceBall 0 (1/2)
  have hready := c11_nested_cutoff_ready (d := d) (r := (1/2 : ℝ)) (R := 1)
    (a := -1) (T := -1/2) (T' := -1/4) (b := 1/2) (B := 1) (h := 1/4)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  dsimp only at hready
  obtain ⟨hη, hηc, hηs, htest, hK, hKU, hzero, hone⟩ := hready
  have hS : MeasurableSet S := measurableSet_Ioo.prod (c20_sourceBall_measurable 0 _)
  have hSQ : S ⊆ Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1 := by
    rintro ⟨t, x⟩ ⟨ht, hx⟩
    refine ⟨⟨by linarith [ht.1], by linarith [ht.2]⟩, ?_⟩
    change euclideanNorm (x - 0) < 1/2 at hx
    change euclideanNorm (x - 0) < 1
    linarith
  have hηone : ∀ z ∈ S, η z = 1 := by
    intro z hz
    apply hone z
    rcases hz with ⟨ht, hx⟩
    exact ⟨⟨by linarith [ht.1], by linarith [ht.2]⟩, hx⟩
  obtain ⟨B, hB1, hBtop, hgain⟩ := b_weighted_signed_cutoff_norm_gain d hd
    hκ (by norm_num : (0 : ℝ) < 1) (by norm_num : (-1 : ℝ) < 1)
    η hη hηc hηs (Filter.Eventually.of_forall htest) (tsupport ξ) hK hKU hzero
    S hS hSQ hηone
  let C : ℝ := B.toReal + 1
  have hC : 0 < C := by
    dsimp [C]
    have h : 0 ≤ B.toReal := ENNReal.toReal_nonneg
    linarith
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hγ1 : 1 ≤ ((d : ℝ) + 2) / d := by rw [le_div_iff₀ hd0]; linarith
  refine ⟨C, hC, ?_⟩
  intro ρ α hell u G hcal p hp
  have hp0 : 0 < p := by linarith
  have hpow : 1 ≤ p ^ 2 := by nlinarith
  have hCp : C ≤ C * p ^ 2 := by
    nlinarith [mul_nonneg hC.le (sub_nonneg.mpr hpow)]
  have hBbound : B ≤ ENNReal.ofReal (C * p ^ 2) := by
    rw [← ENNReal.ofReal_toReal hBtop]
    apply ENNReal.ofReal_le_ofReal
    dsimp [C] at hCp ⊢
    linarith
  have hrexponent : 1 / (p * (((d : ℝ) + 2) / d)) ≤ 1 / p := by
    apply one_div_le_one_div_of_le hp0
    nlinarith [mul_nonneg hp0.le (sub_nonneg.mpr hγ1)]
  have hcoef : B ^ (1 / (p * (((d : ℝ) + 2) / d))) ≤
      ENNReal.ofReal (Real.rpow (C * p^2) (1/p)) := by
    calc
      _ ≤ B ^ (1 / p) := ENNReal.rpow_le_rpow_of_exponent_le hB1 hrexponent
      _ ≤ ENNReal.ofReal (C * p^2) ^ (1 / p) :=
        ENNReal.rpow_le_rpow hBbound (by positivity)
      _ = _ := ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity)
  have hnorm := hgain ρ α hell u G hcal p hp
  have hresult := hnorm.trans (mul_le_mul' hcoef le_rfl)
  simpa only [S, mul_div_assoc] using hresult

end EinsteinFull.Calculus

