import EinsteinFull.Homogenization.HeatSelectedFluxExistence
import EinsteinFull.Homogenization.HeatPotentialWeakGradient
import EinsteinFull.Calculus.C2BallPoincareFromPDE
import EinsteinRelation.Correctors.PairedParabolicEquation
import EinsteinRelation.Correctors.WeakGradientCentering
import EinsteinRelation.Correctors.SpatialWeakLocalization

/-!
# The potential of the heat-selected flux gradient

The truncations of the heat formula (6.7) of Armstrong, Kuusi and Mourrat, *Quantitative
Stochastic Homogenization and Large-Scale Regularity*, are the weak gradients of the truncated
first-derivative formulas `∫_{1/(p+1)}^{p+1} (∂ⱼΦ_t * g_k - ∂ₖΦ_t * g_j) dt`. Normalized by their
averages over the unit ball, these potentials are Cauchy in `L²` on every ball by the Poincaré
inequality, and their selected limit is a potential of the heat-selected flux gradient.
-/

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace EinsteinFull.Homogenization

open EinsteinRelation EinsteinRelation.Correctors EinsteinRelation.External.AKM
open EinsteinRelation.Correctors.HeatSelectedSkewMeaning

variable {d : ℕ}

theorem isFiniteMeasure_restrict_ball (ρ : ℝ) :
    IsFiniteMeasure (volume.restrict (ball (0 : Vec d) ρ)) :=
  isFiniteMeasure_restrict.mpr (volume_ball_zero_lt_top ρ).ne

/-- Testing against a compactly supported continuous function is continuous for `L²`
convergence on a ball containing its support. -/
theorem tendsto_integral_mul_of_eLpNorm {u : Vec d → ℝ} {un : ℕ → Vec d → ℝ}
    (hu : ∀ R : ℝ, MemLp u 2 (volume.restrict (ball 0 R)))
    (hun : ∀ n (R : ℝ), MemLp (un n) 2 (volume.restrict (ball 0 R)))
    {φ : Vec d → ℝ} (hφ : Continuous φ) (hφc : HasCompactSupport φ) {ρ : ℝ}
    (hρ : tsupport φ ⊆ ball 0 ρ)
    (hconv : Tendsto (fun n => eLpNorm (fun x => un n x - u x) 2
      (volume.restrict (ball 0 ρ))) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, un n x * φ x) atTop (𝓝 (∫ x, u x * φ x)) := by
  have := isFiniteMeasure_restrict_ball (d := d) ρ
  obtain ⟨M, hM⟩ := hφc.exists_bound_of_continuous hφ
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM 0)
  set V : ℝ≥0∞ := (volume.restrict (ball (0 : Vec d) ρ)) univ ^ (1 / (1 : ℝ≥0∞).toReal -
    1 / (2 : ℝ≥0∞).toReal) with hV
  have hVfin : V ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) (measure_ne_top _ _)
  have hint : ∀ n, Integrable (fun x => un n x * φ x) volume := fun n => by
    simpa only [smul_eq_mul] using
      (locallyIntegrable_of_memLp_ball (hun n)).integrable_smul_right_of_hasCompactSupport hφ hφc
  have huint : Integrable (fun x => u x * φ x) volume := by
    simpa only [smul_eq_mul] using
      (locallyIntegrable_of_memLp_ball hu).integrable_smul_right_of_hasCompactSupport hφ hφc
  have hbound : ∀ n, ‖(∫ x, un n x * φ x) - ∫ x, u x * φ x‖ ≤
      M * (eLpNorm (fun x => un n x - u x) 2 (volume.restrict (ball 0 ρ)) * V).toReal := by
    intro n
    have hF2 : MemLp (fun x => un n x - u x) 2 (volume.restrict (ball 0 ρ)) :=
      (hun n ρ).sub (hu ρ)
    have hF := hF2.aestronglyMeasurable
    rw [← integral_sub (hint n) huint]
    have hzero : ∀ x ∉ ball (0 : Vec d) ρ, un n x * φ x - u x * φ x = 0 := fun x hx => by
      rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hρ h)), mul_zero, mul_zero, sub_zero]
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
    calc ‖∫ x in ball 0 ρ, (un n x * φ x - u x * φ x)‖
        ≤ ∫ x in ball 0 ρ, ‖un n x * φ x - u x * φ x‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ x in ball 0 ρ, M * ‖un n x - u x‖ := by
          refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _)
            ((hF2.integrable (by norm_num)).norm.const_mul M)
            (Filter.Eventually.of_forall fun x => ?_)
          simp only
          rw [← sub_mul, norm_mul, mul_comm]
          exact mul_le_mul_of_nonneg_right (hM x) (norm_nonneg _)
      _ = M * (eLpNorm (fun x => un n x - u x) 1 (volume.restrict (ball 0 ρ))).toReal := by
          rw [integral_const_mul, integral_norm_eq_lintegral_enorm hF,
            eLpNorm_one_eq_lintegral_enorm hF]
      _ ≤ M * (eLpNorm (fun x => un n x - u x) 2 (volume.restrict (ball 0 ρ)) * V).toReal :=
          mul_le_mul_of_nonneg_left (ENNReal.toReal_mono
            (ENNReal.mul_ne_top hF2.eLpNorm_ne_top hVfin)
            (eLpNorm_le_eLpNorm_mul_rpow_measure_univ (by norm_num) hF)) hM0
  have hlim : Tendsto (fun n => M * (eLpNorm (fun x => un n x - u x) 2
      (volume.restrict (ball 0 ρ)) * V).toReal) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n => eLpNorm (fun x => un n x - u x) 2
        (volume.restrict (ball 0 ρ)) * V) atTop (𝓝 0) := by
      simpa using ENNReal.Tendsto.mul_const hconv (Or.inr hVfin)
    have h2 := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h1
    simpa using h2.const_mul M
  rw [tendsto_iff_norm_sub_tendsto_zero]
  exact squeeze_zero (fun _ => norm_nonneg _) hbound hlim

/-- **Closure of weak partial derivatives** under `L²` convergence on balls. -/
theorem hasWeakPartialDerivative_of_tendsto {u v : Vec d → ℝ} {un vn : ℕ → Vec d → ℝ}
    (i : Fin d) (hn : ∀ n, HasWeakPartialDerivative univ i (un n) (vn n))
    (hu : ∀ R : ℝ, MemLp u 2 (volume.restrict (ball 0 R)))
    (hv : ∀ R : ℝ, MemLp v 2 (volume.restrict (ball 0 R)))
    (hun : ∀ n (R : ℝ), MemLp (un n) 2 (volume.restrict (ball 0 R)))
    (hvn : ∀ n (R : ℝ), MemLp (vn n) 2 (volume.restrict (ball 0 R)))
    (hconvu : ∀ R : ℝ, Tendsto (fun n => eLpNorm (fun x => un n x - u x) 2
      (volume.restrict (ball 0 R))) atTop (𝓝 0))
    (hconvv : ∀ R : ℝ, Tendsto (fun n => eLpNorm (fun x => vn n x - v x) 2
      (volume.restrict (ball 0 R))) atTop (𝓝 0)) :
    HasWeakPartialDerivative univ i u v := by
  refine ⟨locallyIntegrableOn_univ.mpr (locallyIntegrable_of_memLp_ball hu),
    locallyIntegrableOn_univ.mpr (locallyIntegrable_of_memLp_ball hv), fun ψ hψt => ?_⟩
  have hψ : IsSmoothCompact ψ := ⟨hψt.1, hψt.2.1⟩
  have hiψ := hψ.coordinateDerivative i
  obtain ⟨ρ, hρ⟩ := exists_euclideanNorm_le_of_hasCompactSupport hψ.2
  have hsub : tsupport ψ ⊆ ball 0 (ρ + 1) := fun x hx => by
    change euclideanNorm (x - 0) < ρ + 1
    rw [sub_zero]
    linarith [hρ x hx]
  have hsub' : tsupport (coordinateDerivative i ψ) ⊆ ball 0 (ρ + 1) :=
    (tsupport_fderiv_apply_subset ℝ _).trans hsub
  have hl := tendsto_integral_mul_of_eLpNorm hu hun hiψ.1.continuous hiψ.2 hsub' (hconvu _)
  have hr := (tendsto_integral_mul_of_eLpNorm hv hvn hψ.1.continuous hψ.2 hsub (hconvv _)).neg
  rw [Measure.restrict_univ]
  refine tendsto_nhds_unique hl (hr.congr fun n => ?_)
  have h := (hn n).2.2 ψ hψt
  rw [Measure.restrict_univ] at h
  exact h.symm

theorem volume_ball_zero_pos {ρ : ℝ} (hρ : 0 < ρ) : 0 < volume (ball (0 : Vec d) ρ) :=
  (isOpen_ball_zero ρ).measure_pos volume ⟨0, by
    change euclideanNorm ((0 : Vec d) - 0) < ρ
    simp [euclideanNorm, euclideanSq, dot, hρ]⟩

theorem setAverage_sub_const {s : Set (Vec d)} (hs0 : volume s ≠ 0) (hs : volume s ≠ ⊤)
    {f : Vec d → ℝ} (hf : IntegrableOn f s volume) (c : ℝ) :
    ⨍ x in s, (f x - c) = (⨍ x in s, f x) - c := by
  have hpos : 0 < volume.real s := ENNReal.toReal_pos hs0 hs
  rw [setAverage_eq, setAverage_eq, integral_sub hf (integrableOn_const hs), setIntegral_const,
    smul_eq_mul, smul_eq_mul, smul_eq_mul, mul_sub, ← mul_assoc, inv_mul_cancel₀ hpos.ne', one_mul]

theorem sqrt_sum_sq_le_sum {ι : Type*} (s : Finset ι) {a : ι → ℝ} (ha : ∀ i, 0 ≤ a i) :
    Real.sqrt (∑ i ∈ s, a i ^ 2) ≤ ∑ i ∈ s, a i := by
  rw [Real.sqrt_le_left (Finset.sum_nonneg fun i _ => ha i)]
  rw [sq, Finset.sum_mul_sum]
  refine Finset.sum_le_sum fun i hi => ?_
  rw [sq]
  exact Finset.single_le_sum (f := fun j => a i * a j) (fun j _ => mul_nonneg (ha i) (ha j)) hi

/-- **Poincaré inequality normalized on the unit ball**: on `B_R`, `R ≥ 1`, a weak potential
minus its unit-ball average is bounded in `L²` by its gradient. -/
theorem exists_eLpNorm_sub_unitBallAverage_le (hd : 2 ≤ d) {R : ℝ} (hR : 1 ≤ R) :
    ∃ K : ℝ≥0∞, K ≠ ⊤ ∧ ∀ (w : Vec d → ℝ) (W : Vec d → Vec d),
      MemLp w 2 (volume.restrict (ball 0 R)) →
      (∀ l, MemLp (fun x => W x l) 2 (volume.restrict (ball 0 R))) →
      HasWeakGradient univ w W →
      eLpNorm (fun x => w x - ⨍ y in ball 0 1, w y) 2 (volume.restrict (ball 0 R)) ≤
        K * ∑ l, eLpNorm (fun x => W x l) 2 (volume.restrict (ball 0 R)) := by
  obtain ⟨C, hC, hP⟩ := EinsteinFull.ballPoincareEstimate_from_pde d hd
  have hR0 : 0 < R := lt_of_lt_of_le one_pos hR
  set μ := volume.restrict (ball (0 : Vec d) R) with hμ
  set μ₁ := volume.restrict (ball (0 : Vec d) 1) with hμ₁
  have hfin := isFiniteMeasure_restrict_ball (d := d) R
  have hfin₁ := isFiniteMeasure_restrict_ball (d := d) 1
  have hB₁0 : volume (ball (0 : Vec d) 1) ≠ 0 := (volume_ball_zero_pos one_pos).ne'
  have hB₁ : volume (ball (0 : Vec d) 1) ≠ ⊤ := (volume_ball_zero_lt_top 1).ne
  have hBR0 : volume (ball (0 : Vec d) R) ≠ 0 := (volume_ball_zero_pos hR0).ne'
  have hBR : volume (ball (0 : Vec d) R) ≠ ⊤ := (volume_ball_zero_lt_top R).ne
  have hsub : ball (0 : Vec d) 1 ⊆ ball 0 R := ball_subset_ball_of_le hR
  have hμ₁μ : μ₁ ≤ μ := Measure.restrict_mono hsub le_rfl
  set V₁ : ℝ≥0∞ := μ₁ univ ^ (1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal) with hV₁
  set VR : ℝ≥0∞ := μ univ ^ (1 / (2 : ℝ≥0∞).toReal) with hVR
  set K : ℝ≥0∞ := (1 + VR * ENNReal.ofReal (volume.real (ball (0 : Vec d) 1))⁻¹ * V₁) *
    ENNReal.ofReal (C * R) with hK
  have hV₁fin : V₁ ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) (measure_ne_top _ _)
  have hVRfin : VR ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) (measure_ne_top _ _)
  refine ⟨K, ENNReal.mul_ne_top (ENNReal.add_ne_top.mpr ⟨ENNReal.one_ne_top,
    ENNReal.mul_ne_top (ENNReal.mul_ne_top hVRfin ENNReal.ofReal_ne_top) hV₁fin⟩)
      ENNReal.ofReal_ne_top, fun w W hw hW hweak => ?_⟩
  set m := ⨍ y in ball (0 : Vec d) R, w y with hm
  have hwm : MemLp (fun x => w x - m) 2 μ := hw.sub (memLp_const m)
  have hW2 : MemLp W 2 μ := memLp_pi_iff.mpr hW
  have hpoinc := hP 0 R hR0 w W hw hW2 (hasWeakGradient_mono (subset_univ _) hweak)
  have hsqW : ∫ x in ball 0 R, euclideanSq (W x) =
      ∑ l, (eLpNorm (fun x => W x l) 2 μ).toReal ^ 2 := by
    simp_rw [euclideanSq, dot]
    rw [integral_finsetSum _ fun l _ => ?_]
    · refine Finset.sum_congr rfl fun l _ => ?_
      rw [_root_.Homogenization.toReal_eLpNorm_two_sq_eq_integral_sq (hW l)]
      simp_rw [sq]
      rfl
    · simpa only [sq] using (memLp_two_iff_integrable_sq (hW l).aestronglyMeasurable).1 (hW l)
  have hwmL : eLpNorm (fun x => w x - m) 2 μ =
      ENNReal.ofReal (Real.sqrt (∫ x in ball 0 R, |w x - m| ^ 2)) := by
    rw [← ENNReal.ofReal_toReal hwm.eLpNorm_ne_top]
    congr 1
    rw [← Real.sqrt_sq ENNReal.toReal_nonneg,
      _root_.Homogenization.toReal_eLpNorm_two_sq_eq_integral_sq hwm]
    simp_rw [sq_abs]
    rfl
  have hstep1 : eLpNorm (fun x => w x - m) 2 μ ≤
      ENNReal.ofReal (C * R) * ∑ l, eLpNorm (fun x => W x l) 2 μ := by
    rw [hwmL]
    calc ENNReal.ofReal (Real.sqrt (∫ x in ball 0 R, |w x - m| ^ 2))
        ≤ ENNReal.ofReal (C * R * Real.sqrt (∫ x in ball 0 R, euclideanSq (W x))) :=
          ENNReal.ofReal_le_ofReal hpoinc
      _ ≤ ENNReal.ofReal (C * R * ∑ l, (eLpNorm (fun x => W x l) 2 μ).toReal) := by
          refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ (by positivity))
          rw [hsqW]
          exact sqrt_sum_sq_le_sum _ fun _ => ENNReal.toReal_nonneg
      _ = ENNReal.ofReal (C * R) * ∑ l, eLpNorm (fun x => W x l) 2 μ := by
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_sum_of_nonneg
            (fun _ _ => ENNReal.toReal_nonneg)]
          congr 1
          exact Finset.sum_congr rfl fun l _ => ENNReal.ofReal_toReal (hW l).eLpNorm_ne_top
  have hwint₁ : IntegrableOn w (ball 0 1) volume :=
    ((hw.mono_measure hμ₁μ).integrable (by norm_num))
  have havg : (⨍ y in ball (0 : Vec d) 1, w y) - m = ⨍ y in ball (0 : Vec d) 1, (w y - m) :=
    (setAverage_sub_const hB₁0 hB₁ hwint₁ m).symm
  have hconst : ‖(⨍ y in ball (0 : Vec d) 1, w y) - m‖ₑ ≤
      ENNReal.ofReal (volume.real (ball (0 : Vec d) 1))⁻¹ * V₁ *
        eLpNorm (fun x => w x - m) 2 μ := by
    have hF := (hwm.mono_measure hμ₁μ).aestronglyMeasurable
    rw [havg, setAverage_eq, smul_eq_mul, enorm_mul, Real.enorm_eq_ofReal (inv_nonneg.mpr
      measureReal_nonneg), mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ zero_le
    calc ‖∫ y in ball (0 : Vec d) 1, (w y - m)‖ₑ ≤ ∫⁻ y in ball (0 : Vec d) 1, ‖w y - m‖ₑ :=
          enorm_integral_le_lintegral_enorm _
      _ = eLpNorm (fun x => w x - m) 1 μ₁ := (eLpNorm_one_eq_lintegral_enorm hF).symm
      _ ≤ eLpNorm (fun x => w x - m) 2 μ₁ * V₁ :=
          eLpNorm_le_eLpNorm_mul_rpow_measure_univ (by norm_num) hF
      _ ≤ eLpNorm (fun x => w x - m) 2 μ * V₁ := by
          gcongr
      _ = V₁ * eLpNorm (fun x => w x - m) 2 μ := mul_comm _ _
  have hsplit : (fun x => w x - ⨍ y in ball (0 : Vec d) 1, w y) =
      (fun x => w x - m) - (fun _ => (⨍ y in ball (0 : Vec d) 1, w y) - m) := by
    funext x
    simp only [Pi.sub_apply]
    ring
  rw [hsplit]
  calc eLpNorm ((fun x => w x - m) - fun _ => (⨍ y in ball (0 : Vec d) 1, w y) - m) 2 μ
      ≤ eLpNorm (fun x => w x - m) 2 μ +
          eLpNorm (fun _ : Vec d => (⨍ y in ball (0 : Vec d) 1, w y) - m) 2 μ :=
        eLpNorm_sub_le (by norm_num)
    _ = eLpNorm (fun x => w x - m) 2 μ +
          ‖(⨍ y in ball (0 : Vec d) 1, w y) - m‖ₑ * VR := by
        rw [eLpNorm_const' _ two_ne_zero ENNReal.ofNat_ne_top]
    _ ≤ eLpNorm (fun x => w x - m) 2 μ +
          ENNReal.ofReal (volume.real (ball (0 : Vec d) 1))⁻¹ * V₁ *
            eLpNorm (fun x => w x - m) 2 μ * VR := by
        gcongr
    _ = (1 + VR * ENNReal.ofReal (volume.real (ball (0 : Vec d) 1))⁻¹ * V₁) *
          eLpNorm (fun x => w x - m) 2 μ := by ring
    _ ≤ (1 + VR * ENNReal.ofReal (volume.real (ball (0 : Vec d) 1))⁻¹ * V₁) *
          (ENNReal.ofReal (C * R) * ∑ l, eLpNorm (fun x => W x l) 2 μ) := by
        gcongr
    _ = K * ∑ l, eLpNorm (fun x => W x l) 2 μ := by rw [hK]; ring

end EinsteinFull.Homogenization
