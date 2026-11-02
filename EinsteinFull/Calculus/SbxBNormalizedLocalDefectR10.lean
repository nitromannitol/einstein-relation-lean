import EinsteinFull.Calculus.SbxBPrescribedStartSurvivalR06
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

open EinsteinRelation MeasureTheory Filter EinsteinFull.External.Source.GMP
open PDE hiding Vec Mat
open EinsteinFull.Blueprint.TubeProbability
open EinsteinFull.Blueprint.SbxS3UniformCrossHeat
open scoped Topology NNReal ENNReal

namespace EinsteinFull.Calculus

/-- Exponential decay absorbs the normalization at a sufficiently small scale. -/
private theorem b_small_scale_exponential (d : ℕ) {D ε : ℝ} (hD : 0 < D)
    (hε : 0 < ε) :
    ∃ a : ℝ, 0 < a ∧ a < 1/2 ∧ D * a⁻¹ ^ d * Real.exp (-(1 / (D * a^2))) ≤ ε := by
  have hlim : Tendsto (fun x : ℝ => D * (x ^ (d : ℝ) * Real.exp (-(D⁻¹) * x))) atTop (𝓝 0) := by
    simpa using (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (d : ℝ) D⁻¹ (inv_pos.mpr hD)).const_mul D
  have hevent : ∀ᶠ x : ℝ in atTop, D * (x ^ (d : ℝ) * Real.exp (-(D⁻¹) * x)) < ε :=
    hlim.eventually (gt_mem_nhds hε)
  obtain ⟨M, hM, hbound⟩ : ∃ M : ℝ, 2 < M ∧ D * (M ^ (d : ℝ) * Real.exp (-(D⁻¹) * M)) < ε := by
    have h := hevent.and (eventually_gt_atTop (2 : ℝ))
    obtain ⟨M, hM⟩ := h.exists
    exact ⟨M, hM.2, hM.1⟩
  have hMpos : 0 < M := by linarith
  refine ⟨M⁻¹, inv_pos.mpr hMpos, ?_, ?_⟩
  · rw [← one_div, div_lt_iff₀ hMpos]
    linarith
  · have harg : -(1 / (D * (M⁻¹)^2)) ≤ -(D⁻¹) * M := by
      have hM1 : 1 ≤ M := by linarith
      have hM2 : M ≤ M^2 := by nlinarith
      have : D⁻¹ * M ≤ D⁻¹ * M^2 := mul_le_mul_of_nonneg_left hM2 (le_of_lt (inv_pos.mpr hD))
      have hid : 1 / (D * (M⁻¹)^2) = D⁻¹ * M^2 := by field_simp
      rw [hid]
      linarith
    have hexp := Real.exp_le_exp.mpr harg
    have hmul := mul_le_mul_of_nonneg_left hexp (mul_nonneg hD.le (pow_nonneg hMpos.le d))
    rw [Real.rpow_natCast] at hbound
    have hbound' : D * M ^ d * Real.exp (-(D⁻¹) * M) ≤ ε := by
      simpa only [mul_assoc] using hbound.le
    simpa only [inv_inv] using hmul.trans hbound'

/-- A uniform annular exponential estimate yields the normalized local defect. -/
theorem b_normalized_local_defect_of_exponential_estimate
    (d : ℕ) (hd : 2 ≤ d) (κ C : ℝ) (hκ : 0 < κ) (hC : 0 < C)
    (hDecay : ∃ D : ℝ, 0 < D ∧
      ∀ (R : ℝ), 0 < R → ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
        IsUniformlyElliptic κ ρ α →
      ∀ (s : DirichletSpectralResolution ρ α R) (x : Vec d) (r : ℝ), 0 < r →
        sourceBall x (2*r) ⊆ sourceBall 0 R →
      ∀ φ : Vec d → ℝ, IsSpatialTest (sourceBall 0 R) φ →
        tsupport φ ⊆ sourceBall x (2*r) →
        (∀ z, 0 ≤ φ z ∧ φ z ≤ 1) →
        (∀ z ∈ sourceBall x r, φ z = 1) →
        (∀ z, euclideanSq (fun i => fderiv ℝ φ z (unitVector i)) ≤ 1024 / r^2) →
      ∀ T : ℝ, 0 < T → T ≤ r^2 →
        (∫ z in Set.Ioo (0 : ℝ) T ×ˢ sourceBall x (r/2),
          |(∫ y, (∑' n, Real.exp (-s.eigenvalue n * z.1) *
              s.eigenfunction n z.2 * s.eigenfunction n y) * φ y ∂dirichletVolume ρ R) - 1| ^ 2)
          ≤ D * T * r^d * Real.exp (-(r^2 / (D*T)))) :
    ∃ a : ℝ, 0 < a ∧ a < 1/2 ∧
      ∀ (R : ℝ), 0 < R → ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
        IsUniformlyElliptic κ ρ α →
      ∀ (s : DirichletSpectralResolution ρ α R) (x : Vec d) (r : ℝ), 0 < r →
        sourceBall x (2*r) ⊆ sourceBall 0 R →
      ∀ φ : Vec d → ℝ, IsSpatialTest (sourceBall 0 R) φ →
        tsupport φ ⊆ sourceBall x (2*r) →
        (∀ z, 0 ≤ φ z ∧ φ z ≤ 1) →
        (∀ z ∈ sourceBall x r, φ z = 1) →
        (∀ z, euclideanSq (fun i => fderiv ℝ φ z (unitVector i)) ≤ 1024 / r^2) →
      ((a*r)^(d+2))⁻¹ *
        (∫ z in Set.Ioo (-(a*r)^2) ((a*r)^2) ×ˢ sourceBall x (a*r),
          |if 0 < z.1 then
            (∫ y, (∑' n, Real.exp (-s.eigenvalue n * z.1) *
              s.eigenfunction n z.2 * s.eigenfunction n y) * φ y ∂dirichletVolume ρ R) - 1
            else 0| ^ 2) ≤ (1 / (2*C))^2 := by
  classical
  obtain ⟨D, hD, hDecay⟩ := hDecay
  have hε : 0 < (1 / (2*C))^2 := by positivity
  obtain ⟨a, ha, ha2, hasmall⟩ := b_small_scale_exponential d hD hε
  refine ⟨a, ha, ha2, ?_⟩
  intro R hR ρ α hell s x r hr hinside φ hφ hsupp hbounds hplateau hgrad
  let T : ℝ := (a*r)^2
  let V : Set (Vec d) := sourceBall x (r/2)
  let W : Set (Vec d) := sourceBall x (a*r)
  let F : ℝ × Vec d → ℝ := fun z =>
    (∫ y, (∑' n, Real.exp (-s.eigenvalue n * z.1) *
      s.eigenfunction n z.2 * s.eigenfunction n y) * φ y ∂dirichletVolume ρ R) - 1
  have hT : 0 < T := sq_pos_of_pos (mul_pos ha hr)
  have hTr : T ≤ r^2 := by dsimp [T]; nlinarith [sq_nonneg (a*r-r), sq_nonneg r]
  have hWV : W ⊆ V := by
    intro z hz
    change euclideanNorm (z-x) < a*r at hz
    change euclideanNorm (z-x) < r/2
    nlinarith
  have hVB : V ⊆ sourceBall (0 : Vec d) R := by
    intro z hz
    apply hinside
    change euclideanNorm (z-x) < r/2 at hz
    change euclideanNorm (z-x) < 2*r
    linarith
  let hp := c9_cutoff_memLp_dirichletVolume hR hell φ hφ hbounds
  obtain ⟨u, hb, hv⟩ := b_supplied_modes_have_dirichlet_carriers hκ hR hell s
  have hs := br06_native_spectral_eigenvalue_tendsto_atTop hd hκ hR hell s
  have hmem := c9_native_kernel_action_memLp hd hκ hR hell s u hs hb hv (hp.toLp φ) T
  have heq : (fun z : ℝ × Vec d => ∫ y,
      (∑' n, Real.exp (-s.eigenvalue n * z.1) * s.eigenfunction n z.2 *
        s.eigenfunction n y) * (hp.toLp φ) y ∂dirichletVolume ρ R) =
      (fun z => ∫ y, (∑' n, Real.exp (-s.eigenvalue n * z.1) *
        s.eigenfunction n z.2 * s.eigenfunction n y) * φ y ∂dirichletVolume ρ R) := by
    funext z
    apply integral_congr_ae
    filter_upwards [hp.coeFn_toLp] with y hy
    rw [hy]
  rw [heq] at hmem
  have hsub : Set.Ioo (0 : ℝ) T ×ˢ V ⊆ Set.Ioo 0 T ×ˢ sourceBall (0 : Vec d) R :=
    Set.prod_mono Set.Subset.rfl hVB
  haveI : IsFiniteMeasure (volume.restrict V) :=
    isFiniteMeasure_restrict.mpr ((measure_mono hVB).trans_lt (lt_top_iff_ne_top.mpr
      (c18_sourceBall_measure_ne_top (0 : Vec d) R))).ne
  haveI : IsFiniteMeasure (volume.restrict (Set.Ioo (0 : ℝ) T ×ˢ V)) := by
    have hfinite : IsFiniteMeasure ((volume.restrict (Set.Ioo (0 : ℝ) T)).prod
        (volume.restrict V)) := inferInstance
    rwa [Measure.prod_restrict] at hfinite
  have hdiff := (hmem.mono_measure (Measure.restrict_mono_set volume hsub)).sub
    (memLp_const (1 : ℝ))
  have hi : Integrable (fun z => |F z|^2) (volume.restrict (Set.Ioo 0 T ×ˢ V)) := by
    simpa only [F, sq_abs, Pi.sub_apply] using hdiff.integrable_sq
  have hmono : (∫ z in Set.Ioo (0 : ℝ) T ×ˢ W, |F z|^2) ≤
      ∫ z in Set.Ioo (0 : ℝ) T ×ˢ V, |F z|^2 := by
    apply integral_mono_measure (Measure.restrict_mono_set volume (Set.prod_mono Set.Subset.rfl hWV))
    · exact Filter.Eventually.of_forall (fun z => sq_nonneg _)
    · exact hi
  have hzero : (∫ z in Set.Ioo (-T) T ×ˢ W, |if 0 < z.1 then F z else 0|^2) =
      ∫ z in Set.Ioo (0 : ℝ) T ×ˢ W, |F z|^2 := by
    let P : Set (ℝ × Vec d) := Set.Ioi 0 ×ˢ Set.univ
    have hP : MeasurableSet P := measurableSet_Ioi.prod MeasurableSet.univ
    have hset : P ∩ (Set.Ioo (-T) T ×ˢ W) = Set.Ioo 0 T ×ˢ W := by
      ext ⟨t,z⟩
      simp only [P, Set.mem_inter_iff, Set.mem_prod, Set.mem_Ioi, Set.mem_univ,
        and_true, Set.mem_Ioo]
      constructor
      · rintro ⟨ht, ⟨⟨_, htT⟩, hz⟩⟩
        exact ⟨⟨ht, htT⟩, hz⟩
      · rintro ⟨⟨ht, htT⟩, hz⟩
        exact ⟨ht, ⟨⟨by linarith, htT⟩, hz⟩⟩
    have heq : (fun z : ℝ × Vec d => |if 0 < z.1 then F z else 0|^2) =
        P.indicator (fun z => |F z|^2) := by
      funext z
      by_cases hz : 0 < z.1 <;> simp [P, hz]
    rw [heq, integral_indicator hP, Measure.restrict_restrict hP, hset]
  have hraw := hDecay R hR ρ α hell s x r hr hinside φ hφ hsupp hbounds hplateau hgrad T hT hTr
  change (∫ z in Set.Ioo 0 T ×ˢ V, |F z|^2) ≤ D * T * r^d * Real.exp (-(r^2 / (D*T))) at hraw
  have hnorm : ((a*r)^(d+2))⁻¹ * (D * T * r^d * Real.exp (-(r^2 / (D*T)))) =
      D * a⁻¹^d * Real.exp (-(1 / (D*a^2))) := by
    have he : r^2 / (D*T) = 1 / (D*a^2) := by
      dsimp [T]
      field_simp [ne_of_gt hD, ne_of_gt ha, ne_of_gt hr]
    rw [he]
    dsimp [T]
    simp only [pow_add, mul_pow, mul_inv_rev, ← inv_pow]
    field_simp [ne_of_gt ha, ne_of_gt hr, pow_ne_zero d (ne_of_gt ha),
      pow_ne_zero d (ne_of_gt hr)]
    <;> ring
    rw [← mul_pow]
    simp [ne_of_gt hr]
  change ((a*r)^(d+2))⁻¹ * (∫ z in Set.Ioo (-T) T ×ˢ W, |if 0 < z.1 then F z else 0|^2) ≤ _
  rw [hzero]
  calc
    _ ≤ ((a*r)^(d+2))⁻¹ * (D*T*r^d*Real.exp (-(r^2/(D*T)))) :=
      mul_le_mul_of_nonneg_left (hmono.trans hraw) (inv_nonneg.mpr (pow_nonneg (mul_nonneg ha.le hr.le) _))
    _ = D * a⁻¹^d * Real.exp (-(1/(D*a^2))) := hnorm
    _ ≤ _ := hasmall

end EinsteinFull.Calculus
