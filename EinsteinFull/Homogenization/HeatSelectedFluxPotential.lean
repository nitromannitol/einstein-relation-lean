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

/-- The truncated first-derivative heat formula: a potential of the truncation of (6.7). -/
noncomputable def heatPotentialTruncation (g : Vec d → Vec d) (p : ℕ) (j k : Fin d)
    (x : Vec d) : ℝ :=
  heatGradWindow ((p + 1 : ℕ) : ℝ)⁻¹ ((p + 1 : ℕ) : ℝ) j (fun y => g y k) x -
    heatGradWindow ((p + 1 : ℕ) : ℝ)⁻¹ ((p + 1 : ℕ) : ℝ) k (fun y => g y j) x

/-- The truncated potential normalized by its average over the unit ball. -/
noncomputable def centeredHeatPotential (g : Vec d → Vec d) (p : ℕ) (j k : Fin d)
    (x : Vec d) : ℝ :=
  heatPotentialTruncation g p j k x - ⨍ y in ball (0 : Vec d) 1, heatPotentialTruncation g p j k y

/-- **The heat-selected flux potential**: the selected `L²_loc` limit of the normalized
truncated potentials. -/
noncomputable def heatSelectedPotential (g : Vec d → Vec d) (x : Vec d) : Mat d :=
  Matrix.of fun j k => locL2Limit (fun p => centeredHeatPotential g p j k) x

theorem heatSelectedPotential_apply (g : Vec d → Vec d) (x : Vec d) (j k : Fin d) :
    heatSelectedPotential g x j k = locL2Limit (fun p => centeredHeatPotential g p j k) x :=
  Matrix.of_apply _ _ _

namespace HeatFormulaHypotheses

variable {g : Vec d → Vec d} (hg : HeatFormulaHypotheses g)
include hg

theorem hasWeakGradient_heatPotentialTruncation (p : ℕ) (j k : Fin d) :
    HasWeakGradient univ (heatPotentialTruncation g p j k)
      (fun x l => iteratedAKMHeatGradientTruncation g p p j k l x) := by
  intro l
  have h1 := (hg.moments k).hasWeakPartialDerivative_heatGradWindow (hg.measurable k)
    (natCast_succ_inv_pos p) (natCast_succ_inv_le_natCast_succ p p) j l
  have h2 := (hg.moments j).hasWeakPartialDerivative_heatGradWindow (hg.measurable j)
    (natCast_succ_inv_pos p) (natCast_succ_inv_le_natCast_succ p p) k l
  have heq : (fun x => iteratedAKMHeatGradientTruncation g p p j k l x) =
      fun x => heatHessianWindow ((p + 1 : ℕ) : ℝ)⁻¹ ((p + 1 : ℕ) : ℝ) j l (fun y => g y k) x -
        heatHessianWindow ((p + 1 : ℕ) : ℝ)⁻¹ ((p + 1 : ℕ) : ℝ) k l (fun y => g y j) x :=
    funext (hg.truncation_eq p p j k l)
  show HasWeakPartialDerivative univ l _ (fun x => iteratedAKMHeatGradientTruncation g p p j k l x)
  rw [heq]
  exact hasWeakPartialDerivative_sub h1 h2

theorem measurable_heatPotentialTruncation (p : ℕ) (j k : Fin d) :
    Measurable (heatPotentialTruncation g p j k) :=
  (stronglyMeasurable_heatGradWindow _ _ j (hg.measurable k)).measurable.sub
    (stronglyMeasurable_heatGradWindow _ _ k (hg.measurable j)).measurable

theorem memLp_heatPotentialTruncation (p : ℕ) (j k : Fin d) (ρ : ℝ) :
    MemLp (heatPotentialTruncation g p j k) 2 (volume.restrict (ball 0 ρ)) :=
  ((hg.moments k).memLp_heatGradWindow (natCast_succ_inv_pos p)
    (natCast_succ_inv_le_natCast_succ p p) j (hg.measurable k) ρ).sub
    ((hg.moments j).memLp_heatGradWindow (natCast_succ_inv_pos p)
      (natCast_succ_inv_le_natCast_succ p p) k (hg.measurable j) ρ)

theorem measurable_centeredHeatPotential (p : ℕ) (j k : Fin d) :
    Measurable (centeredHeatPotential g p j k) :=
  (hg.measurable_heatPotentialTruncation p j k).sub measurable_const

theorem memLp_centeredHeatPotential (p : ℕ) (j k : Fin d) (ρ : ℝ) :
    MemLp (centeredHeatPotential g p j k) 2 (volume.restrict (ball 0 ρ)) := by
  have := isFiniteMeasure_restrict_ball (d := d) ρ
  exact (hg.memLp_heatPotentialTruncation p j k ρ).sub (memLp_const _)

theorem hasWeakGradient_centeredHeatPotential (p : ℕ) (j k : Fin d) :
    HasWeakGradient univ (centeredHeatPotential g p j k)
      (fun x l => iteratedAKMHeatGradientTruncation g p p j k l x) :=
  hasWeakGradient_sub_const univ (hg.hasWeakGradient_heatPotentialTruncation p j k) _

theorem centeredHeatPotential_sub (p q : ℕ) (j k : Fin d) :
    (fun x => centeredHeatPotential g p j k x - centeredHeatPotential g q j k x) =
      fun x => (heatPotentialTruncation g p j k x - heatPotentialTruncation g q j k x) -
        ⨍ y in ball (0 : Vec d) 1,
          (heatPotentialTruncation g p j k y - heatPotentialTruncation g q j k y) := by
  have hfin := isFiniteMeasure_restrict_ball (d := d) 1
  have hip := (hg.memLp_heatPotentialTruncation p j k 1).integrable (by norm_num)
  have hiq := (hg.memLp_heatPotentialTruncation q j k 1).integrable (by norm_num)
  funext x
  unfold centeredHeatPotential
  rw [setAverage_eq, setAverage_eq, setAverage_eq, integral_sub hip hiq, smul_eq_mul,
    smul_eq_mul, smul_eq_mul]
  ring

/-- **The normalized potentials are Cauchy in `L²` on every ball.** -/
theorem isLocL2Cauchy_centeredHeatPotential (hd : 2 ≤ d) (j k : Fin d) :
    IsLocL2Cauchy (fun p => centeredHeatPotential g p j k) := by
  intro ρ δ hδ
  set R := max ρ 1 with hR
  obtain ⟨K, hKfin, hK⟩ := exists_eLpNorm_sub_unitBallAverage_le hd (le_max_right ρ 1)
  have hKd : K * (d : ℝ≥0∞) ≠ ⊤ := ENNReal.mul_ne_top hKfin (ENNReal.natCast_ne_top d)
  obtain ⟨δ', hδ', hδ'le⟩ : ∃ δ' : ℝ≥0∞, 0 < δ' ∧ K * (d : ℝ≥0∞) * δ' ≤ δ := by
    by_cases h0 : K * (d : ℝ≥0∞) = 0
    · exact ⟨1, one_pos, by rw [h0, zero_mul]; exact zero_le⟩
    · refine ⟨δ / (K * d), ENNReal.div_pos hδ.ne' hKd, ?_⟩
      rw [ENNReal.mul_div_cancel h0 hKd]
  choose N hN using fun l : Fin d => hg.exists_eLpNorm_truncation_sub_le j k l R hδ'
  refine ⟨Finset.univ.sup N, fun p q hp hq => ?_⟩
  have hNl : ∀ l, N l ≤ Finset.univ.sup N := fun l => Finset.le_sup (Finset.mem_univ l)
  rw [hg.centeredHeatPotential_sub p q j k]
  have hw : MemLp (fun x => heatPotentialTruncation g p j k x -
      heatPotentialTruncation g q j k x) 2 (volume.restrict (ball 0 R)) :=
    (hg.memLp_heatPotentialTruncation p j k R).sub (hg.memLp_heatPotentialTruncation q j k R)
  have hW : ∀ l, MemLp (fun x => iteratedAKMHeatGradientTruncation g p p j k l x -
      iteratedAKMHeatGradientTruncation g q q j k l x) 2 (volume.restrict (ball 0 R)) := fun l =>
    (hg.memLp_truncation p p j k l R).sub (hg.memLp_truncation q q j k l R)
  have hweak := hasWeakGradient_sub (hg.hasWeakGradient_heatPotentialTruncation p j k)
    (hg.hasWeakGradient_heatPotentialTruncation q j k)
  have hP := hK _ _ hw hW hweak
  calc eLpNorm _ 2 (volume.restrict (ball 0 ρ))
      ≤ eLpNorm (fun x => (heatPotentialTruncation g p j k x -
          heatPotentialTruncation g q j k x) - ⨍ y in ball (0 : Vec d) 1,
            (heatPotentialTruncation g p j k y - heatPotentialTruncation g q j k y)) 2
          (volume.restrict (ball 0 R)) :=
        eLpNorm_mono_measure _ (Measure.restrict_mono (ball_subset_ball_of_le
          (le_max_left ρ 1)) le_rfl)
    _ ≤ K * ∑ l, eLpNorm (fun x => iteratedAKMHeatGradientTruncation g p p j k l x -
          iteratedAKMHeatGradientTruncation g q q j k l x) 2 (volume.restrict (ball 0 R)) := hP
    _ ≤ K * ∑ _l : Fin d, δ' := by
        gcongr with l
        exact hN l p p q q ((hNl l).trans hp) ((hNl l).trans hp) ((hNl l).trans hq)
          ((hNl l).trans hq)
    _ = K * (d : ℝ≥0∞) * δ' := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_assoc]
    _ ≤ δ := hδ'le

theorem tendsto_eLpNorm_centeredHeatPotential (hd : 2 ≤ d) (j k : Fin d) (ρ : ℝ) :
    Tendsto (fun p => eLpNorm (fun x => centeredHeatPotential g p j k x -
      heatSelectedPotential g x j k) 2 (volume.restrict (ball 0 ρ))) atTop (𝓝 0) := by
  simp_rw [heatSelectedPotential_apply]
  exact (hg.isLocL2Cauchy_centeredHeatPotential hd j k).tendsto_eLpNorm
    (fun p => hg.measurable_centeredHeatPotential p j k) ρ

theorem measurable_heatSelectedPotential (j k : Fin d) :
    Measurable (fun x => heatSelectedPotential g x j k) := by
  simp_rw [heatSelectedPotential_apply]
  exact measurable_locL2Limit fun p => hg.measurable_centeredHeatPotential p j k

theorem memLp_heatSelectedPotential (hd : 2 ≤ d) (j k : Fin d) (ρ : ℝ) :
    MemLp (fun x => heatSelectedPotential g x j k) 2 (volume.restrict (ball 0 ρ)) := by
  obtain ⟨p, hp⟩ := eventually_atTop.mp
    ((ENNReal.tendsto_nhds_zero.mp (hg.tendsto_eLpNorm_centeredHeatPotential hd j k ρ)) 1
      one_pos)
  have hdiff : MemLp (fun x => centeredHeatPotential g p j k x -
      heatSelectedPotential g x j k) 2 (volume.restrict (ball 0 ρ)) :=
    lt_of_le_of_lt (hp p le_rfl) ENNReal.one_lt_top
  refine ((hg.memLp_centeredHeatPotential p j k ρ).sub hdiff).congr_norm
    (hg.measurable_heatSelectedPotential j k).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  simp only [Pi.sub_apply, sub_sub_cancel]

/-- **The heat-selected flux potential has the heat-selected flux gradient as its weak
gradient.** -/
theorem hasWeakGradient_heatSelectedPotential (hd : 2 ≤ d) (j k : Fin d) :
    HasWeakGradient univ (fun x => heatSelectedPotential g x j k) (heatSelectedGradient g j k) :=
  fun l => hasWeakPartialDerivative_of_tendsto l
    (fun p => hg.hasWeakGradient_centeredHeatPotential p j k l)
    (hg.memLp_heatSelectedPotential hd j k) (hg.memLp_heatSelectedGradient j k l)
    (hg.memLp_centeredHeatPotential · j k) (fun p => hg.memLp_truncation p p j k l)
    (hg.tendsto_eLpNorm_centeredHeatPotential hd j k) (hg.tendsto_eLpNorm_diagonal j k l)

end HeatFormulaHypotheses

end EinsteinFull.Homogenization
