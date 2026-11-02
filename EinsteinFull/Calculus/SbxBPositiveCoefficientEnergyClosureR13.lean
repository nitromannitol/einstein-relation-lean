import EinsteinFull.Calculus.C9TubeCutoffCoefficientEnergy
import EinsteinFull.Calculus.C5TubePositiveConcentricGain
import EinsteinFull.Calculus.SbxBPositiveNestedGainR12
import EinsteinFull.Calculus.SbxBPositiveGradientMeasurabilityR12

open EinsteinRelation MeasureTheory EinsteinFull.External.Source.GMP
open scoped Topology ENNReal

namespace EinsteinFull.Calculus
namespace BPositiveEnergyClosureR13

/-- The square of the positive-power chain factor is controlled uniformly
as the exponent decreases to zero. -/
theorem b_positive_power_coercivity_uniform {κ p M J D : ℝ}
    (hκ : 0 < κ) (hp : 0 < p) (hp2 : p ≤ 1 / 2) (hJ : 0 ≤ J)
    (henergy : (κ * p * (1 - p) / 2) * J ≤ D * M) :
    (p / 2) ^ 2 * J ≤ κ⁻¹ * D * M := by
  have hcoef : (p / 2) ^ 2 ≤ κ⁻¹ * (κ * p * (1 - p) / 2) := by
    have heq : κ⁻¹ * (κ * p * (1 - p) / 2) = p * (1 - p) / 2 := by
      field_simp [ne_of_gt hκ]
    rw [heq]
    nlinarith [mul_nonneg hp.le (show 0 ≤ 2 - 3 * p by linarith)]
  have hfirst := mul_le_mul_of_nonneg_right hcoef hJ
  have hsecond := mul_le_mul_of_nonneg_left henergy (inv_nonneg.mpr hκ.le)
  calc
    (p / 2) ^ 2 * J ≤ κ⁻¹ * ((κ * p * (1 - p) / 2) * J) := by nlinarith [hfirst]
    _ ≤ κ⁻¹ * (D * M) := hsecond
    _ = κ⁻¹ * D * M := by ring

/-- Uniform bound for the spatial-cutoff coefficient in the positive-power
energy inequality. -/
theorem b_positive_power_cutoff_coefficient_uniform {κ p L T : ℝ}
    (hκ : 0 < κ) (hp2 : p ≤ 1 / 2) :
    T + (2 * p / (κ ^ 3 * (1 - p))) * (L ^ 2 * κ⁻¹) ≤
      T + (2 / κ ^ 3) * (L ^ 2 * κ⁻¹) := by
  have hp1 : 0 < 1 - p := by linarith
  have hr : p / (1 - p) ≤ 1 := (div_le_one hp1).2 (by linarith)
  have hc : 0 ≤ 2 / κ ^ 3 := by positivity
  have hd : 0 ≤ L ^ 2 * κ⁻¹ := by positivity
  have habs := mul_le_mul_of_nonneg_left hr hc
  have hprod := mul_le_mul_of_nonneg_right habs hd
  have hid : 2 * p / (κ ^ 3 * (1 - p)) = (2 / κ ^ 3) * (p / (1 - p)) := by
    field_simp [ne_of_gt hκ, ne_of_gt hp1]
  rw [hid]
  nlinarith

/-- Uniform positive-power chain-energy bound corresponding to the selected
trace estimate. -/
theorem b_positive_power_trace_chain_energy_uniform {κ p L T M J : ℝ}
    (hκ : 0 < κ) (hp : 0 < p) (hp2 : p ≤ 1 / 2)
    (hM : 0 ≤ M) (hJ : 0 ≤ J)
    (henergy : (κ * p * (1 - p) / 2) * J ≤
      (T + (2 * p / (κ ^ 3 * (1 - p))) * (L ^ 2 * κ⁻¹)) * M) :
    (p / 2) ^ 2 * J ≤
      κ⁻¹ * (T + (2 / κ ^ 3) * (L ^ 2 * κ⁻¹)) * M := by
  have hcoef := b_positive_power_cutoff_coefficient_uniform (p := p) (L := L) (T := T) hκ hp2
  have hm := mul_le_mul_of_nonneg_right hcoef hM
  have hi := mul_le_mul_of_nonneg_left hm (inv_nonneg.mpr hκ.le)
  calc
    (p / 2) ^ 2 * J ≤
        κ⁻¹ * (T + (2 * p / (κ ^ 3 * (1 - p))) * (L ^ 2 * κ⁻¹)) * M :=
      b_positive_power_coercivity_uniform hκ hp hp2 hJ henergy
    _ = κ⁻¹ * ((T + (2 * p / (κ ^ 3 * (1 - p))) * (L ^ 2 * κ⁻¹)) * M) := by ring
    _ ≤ κ⁻¹ * ((T + (2 / κ ^ 3) * (L ^ 2 * κ⁻¹)) * M) := hi
    _ = κ⁻¹ * (T + (2 / κ ^ 3) * (L ^ 2 * κ⁻¹)) * M := by ring


/-- The selected-trace gradient estimate has a uniform inverse-square
bound in the gap between nested positive cylinders. -/
theorem b_positive_power_trace_chain_energy_gap {κ p Δ M J : ℝ}
    (hκ : 0 < κ) (hp : 0 < p) (hp2 : p ≤ 1 / 2)
    (hΔ : 0 < Δ) (hΔ1 : Δ ≤ 1) (hM : 0 ≤ M) (hJ : 0 ≤ J)
    (henergy : (κ * p * (1 - p) / 2) * J ≤
      (8 / Δ + (2 * p / (κ ^ 3 * (1 - p))) * ((64 / Δ) ^ 2 * κ⁻¹)) * M) :
    (p / 2) ^ 2 * J ≤ κ⁻¹ * ((8 + 8192 / κ ^ 4) / Δ ^ 2) * M := by
  have hbound := b_positive_power_trace_chain_energy_uniform
    (L := 64 / Δ) (T := 8 / Δ) hκ hp hp2 hM hJ henergy
  have hΔ2 : 0 < Δ ^ 2 := sq_pos_of_pos hΔ
  have hfirst : 8 / Δ ≤ 8 / Δ ^ 2 := by
    apply (div_le_div_iff₀ hΔ hΔ2).2
    nlinarith [sq_nonneg Δ]
  have hsecond : (2 / κ ^ 3) * ((64 / Δ) ^ 2 * κ⁻¹) =
      (8192 / κ ^ 4) / Δ ^ 2 := by
    field_simp [ne_of_gt hκ, ne_of_gt hΔ]; ring
  have hcoef : 8 / Δ + (2 / κ ^ 3) * ((64 / Δ) ^ 2 * κ⁻¹) ≤
      (8 + 8192 / κ ^ 4) / Δ ^ 2 := by
    calc
      _ ≤ 8 / Δ ^ 2 + (2 / κ ^ 3) * ((64 / Δ) ^ 2 * κ⁻¹) := add_le_add hfirst le_rfl
      _ = (8 + 8192 / κ ^ 4) / Δ ^ 2 := by rw [hsecond]; ring
  have hh := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hcoef (inv_nonneg.mpr hκ.le)) hM
  exact hbound.trans hh


/-- The cutoff coefficient grows at most quadratically in the inverse gap. -/
theorem b_positive_concentric_coefficient_gap {κ Δ : ℝ}
    (hκ : 0 < κ) (hΔ : 0 < Δ) (hΔ1 : Δ ≤ 1) :
    8 / Δ + (2 / κ ^ 3) * ((64 / Δ) ^ 2 * κ⁻¹) ≤
      (8 + 8192 / κ ^ 4) / Δ ^ 2 := by
  have hΔ2 : 0 < Δ ^ 2 := sq_pos_of_pos hΔ
  have hfirst : 8 / Δ ≤ 8 / Δ ^ 2 := by
    apply (div_le_div_iff₀ hΔ hΔ2).2
    nlinarith [sq_nonneg Δ]
  have hsecond : (2 / κ ^ 3) * ((64 / Δ) ^ 2 * κ⁻¹) =
      (8192 / κ ^ 4) / Δ ^ 2 := by
    field_simp [ne_of_gt hκ, ne_of_gt hΔ]
    ring
  calc
    _ ≤ 8 / Δ ^ 2 + (2 / κ ^ 3) * ((64 / Δ) ^ 2 * κ⁻¹) := add_le_add hfirst le_rfl
    _ = (8 + 8192 / κ ^ 4) / Δ ^ 2 := by rw [hsecond]; ring


/-- Selected traces and chain energy of a positive weighted-caloric field,
with coefficients uniform for powers up to one half. -/
theorem b_positive_power_selected_traces_uniform {d : ℕ} {κ R a b ε p : ℝ}
    {s₀ s₁ t₀ t₁ : ℝ}
    (hκ : 0 < κ) (hR : 0 < R) (hab : a < b)
    (hε : 0 < ε) (hp : 0 < p) (hp2 : p ≤ 1 / 2)
    (hs : s₀ < s₁) (ht : t₀ < t₁) (hsep : s₁ ≤ t₀)
    (hsI : Set.Ioo s₀ s₁ ⊆ Set.Ioo a b) (htI : Set.Ioo t₀ t₁ ⊆ Set.Ioo a b)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d) (hell : IsUniformlyElliptic κ ρ α)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hcal : IsWeightedCaloric ρ α (Set.Ioo a b) (sourceBall 0 R) u G)
    (hu : ∀ᵐ z ∂volume.restrict (Set.Ioo a b ×ˢ sourceBall 0 R), ε ≤ u z)
    (χ : Vec d → ℝ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχc : HasCompactSupport χ)
    (hχU : tsupport χ ⊆ sourceBall 0 R) (hχ0 : ∀ x, 0 ≤ χ x) (hχ1 : ∀ x, χ x ≤ 1)
    (L : ℝ) (hL : ∀ x, euclideanSq (fun j => fderiv ℝ χ x (unitVector j)) ≤ L ^ 2) :
    ∃ (E : ℝ → ℝ) (s t : ℝ), s ∈ Set.Ioo s₀ s₁ ∧ t ∈ Set.Ioo t₀ t₁ ∧
      (∀ᵐ q ∂volume.restrict (Set.Ioo a b),
        E q = ∫ x in sourceBall 0 R, ρ x * χ x ^ 2 * Real.rpow (u (q,x)) p) ∧
      (∀ q ∈ Set.Ioo a b, q < t → E q ≤
        ((t₁ - t₀)⁻¹ + (2 / κ ^ 3) * (L ^ 2 * κ⁻¹)) *
          (∫ z in Set.Ioo a b ×ˢ sourceBall 0 R, ρ z.2 * Real.rpow (u z) p)) ∧
      s < t ∧
      (p / 2) ^ 2 * (∫ q in s..t, ∫ x in sourceBall 0 R,
        χ x ^ 2 * (Real.rpow (u (q,x)) (p-2) * euclideanSq (G (q,x)))) ≤
      κ⁻¹ * ((t₁ - t₀)⁻¹ + (2 / κ ^ 3) * (L ^ 2 * κ⁻¹)) *
        (∫ z in Set.Ioo a b ×ˢ sourceBall 0 R, ρ z.2 * Real.rpow (u z) p) := by
  have hp1 : p < 1 := by linarith
  obtain ⟨E, s, t, hs', ht', _, _, hrep, _, _, htrace, hst, hgrad⟩ :=
    c5_positive_power_cutoff_selected_traces hκ hR hab hε hp hp1 hs ht hsep hsI htI
      ρ α hell u G hcal hu χ hχ hχc hχU hχ0 hχ1 L hL
  have hM : 0 ≤ (∫ z in Set.Ioo a b ×ˢ sourceBall 0 R, ρ z.2 * Real.rpow (u z) p) := by
    apply integral_nonneg_of_ae
    filter_upwards [hu] with z hz
    exact mul_nonneg (hκ.le.trans (hell.2.2 z.2).1)
      (Real.rpow_nonneg (le_of_lt (lt_of_lt_of_le hε hz)) _)
  have hsI' := hsI hs'
  have htI' := htI ht'
  have hsub : Set.Ioo s t ⊆ Set.Ioo a b := by
    intro q hq
    exact ⟨lt_trans hsI'.1 hq.1, lt_trans hq.2 htI'.2⟩
  have hpos := ae_restrict_of_ae_restrict_of_subset
    (Set.prod_mono hsub (Set.Subset.rfl)) hu
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict] at hpos
  have hJ : 0 ≤ ∫ q in s..t, ∫ x in sourceBall 0 R,
      χ x ^ 2 * (Real.rpow (u (q,x)) (p-2) * euclideanSq (G (q,x))) := by
    rw [intervalIntegral.integral_of_le hst.le, integral_Ioc_eq_integral_Ioo]
    apply integral_nonneg_of_ae
    filter_upwards [Measure.ae_ae_of_ae_prod hpos] with q hq
    apply integral_nonneg_of_ae
    filter_upwards [hq] with x hx
    exact mul_nonneg (sq_nonneg _) (mul_nonneg
      (Real.rpow_nonneg (le_of_lt (lt_of_lt_of_le hε hx)) _) (PDE.vecNormSq_nonneg _))
  have hcoef := b_positive_power_cutoff_coefficient_uniform
    (p := p) (L := L) (T := (t₁-t₀)⁻¹) hκ hp2
  refine ⟨E, s, t, hs', ht', hrep, ?_, hst, ?_⟩
  · intro q hq hqt
    exact (htrace q hq hqt).trans (mul_le_mul_of_nonneg_right hcoef hM)
  · exact b_positive_power_trace_chain_energy_uniform hκ hp hp2 hM hJ hgrad


/-- The canonical spatial cutoff has a bound controlled by the nested-cylinder gap. -/
theorem b_positive_concentric_spatial_cutoff (d : ℕ) (σ' σ : ℝ)
    (hσ' : 1 / 2 ≤ σ') (hσ : σ' < σ) (hσ1 : σ ≤ 1) :
    let r : ℝ := 1 / 2 + (σ' - 1 / 2) / 2
    let R : ℝ := 1 / 2 + (σ - 1 / 2) / 2
    let χ : Vec d → ℝ := PDE.canonicalBallCutoff (0 : Vec d) r R
    0 < r ∧ r < R ∧ R < 1 ∧
    ContDiff ℝ (⊤ : ℕ∞) χ ∧ HasCompactSupport χ ∧
    tsupport χ ⊆ sourceBall 0 R ∧
    (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) ∧
    (∀ x ∈ sourceBall (0 : Vec d) r, χ x = 1) ∧
    (∀ x, euclideanSq (fun j => fderiv ℝ χ x (unitVector j)) ≤ (64 / (σ - σ')) ^ 2) := by
  dsimp only
  let r : ℝ := 1 / 2 + (σ' - 1 / 2) / 2
  let R : ℝ := 1 / 2 + (σ - 1 / 2) / 2
  let χ : Vec d → ℝ := PDE.canonicalBallCutoff (0 : Vec d) r R
  have hr : 0 < r := by dsimp [r]; linarith
  have hrR : r < R := by dsimp [r, R]; linarith
  have hR1 : R < 1 := by dsimp [R]; linarith
  have hR : 0 < R := hr.trans hrR
  have hgap : 0 < σ - σ' := sub_pos.mpr hσ
  refine ⟨hr, hrR, hR1, PDE.canonicalBallCutoff_smooth 0 hr.le hrR,
    PDE.canonicalBallCutoff_hasCompactSupport hr.le hrR, ?_, ?_, ?_, ?_⟩
  · rw [← EinsteinFull.Blueprint.TubeProbability.DimensionLift.pde_ball_eq_sourceBall
      (0 : PDE.Vec d) hR]
    exact PDE.canonicalBallCutoff_tsupport_subset_outer hr.le hrR
  · intro x
    exact ⟨PDE.canonicalBallCutoff_nonneg _ _ _ x, PDE.canonicalBallCutoff_le_one _ _ _ x⟩
  · intro x hx
    rw [← EinsteinFull.Blueprint.TubeProbability.DimensionLift.pde_ball_eq_sourceBall
      (0 : PDE.Vec d) hr] at hx
    exact PDE.canonicalBallCutoff_eq_one_on_inner hr.le hrR hx
  · intro x
    have hb := PDE.canonicalBallCutoff_gradient_bound (x₀ := (0 : PDE.Vec d)) hr.le hrR x
    have hs := pow_le_pow_left₀ (PDE.vecEuclideanNorm_nonneg _) hb 2
    rw [PDE.vecEuclideanNorm_sq, div_pow] at hs
    have hdiff : R - r = (σ - σ') / 2 := by dsimp [r, R]; ring
    rw [hdiff] at hs
    change euclideanSq (fun j => fderiv ℝ (PDE.canonicalBallCutoff 0 r R) x (unitVector j)) ≤ _
    have hleft : euclideanSq (fun j => fderiv ℝ (PDE.canonicalBallCutoff 0 r R) x
        (unitVector j)) = PDE.vecNormSq (PDE.classicalGradient (PDE.canonicalBallCutoff 0 r R) x) := by
      simp only [PDE.vecNormSq, PDE.vecDot, euclideanSq, dot,
        PDE.classicalGradient_apply, PDE.basisVec, unitVector]
    rw [hleft]
    have heq : (64 / (σ - σ')) ^ 2 = 32 ^ 2 / ((σ - σ') / 2) ^ 2 := by
      field_simp [ne_of_gt hgap]
      ring
    rw [heq]
    exact hs

/-- The selected trace windows fit inside the outer positive cylinder. -/
theorem b_positive_concentric_time_windows (σ' σ : ℝ)
    (hσ' : 1 / 2 ≤ σ') (hσ : σ' < σ) (hσ1 : σ ≤ 1) :
    let a : ℝ := -3 / 4 - (σ - 1 / 2) / 4
    let b : ℝ := -1 / 2 + (σ - 1 / 2) / 4
    let δ : ℝ := (σ - σ') / 8
    a < b ∧ 0 < δ ∧ a + δ ≤ b - δ ∧
    Set.Ioo a (a + δ) ⊆ Set.Ioo a b ∧
    Set.Ioo (b - δ) b ⊆ Set.Ioo a b ∧
    (b - (b - δ))⁻¹ = 8 / (σ - σ') := by
  dsimp only
  have hgap : 0 < σ - σ' := sub_pos.mpr hσ
  have hsep : -3 / 4 - (σ - 1 / 2) / 4 + (σ - σ') / 8 ≤
      -1 / 2 + (σ - 1 / 2) / 4 - (σ - σ') / 8 := by linarith
  refine ⟨by linarith, by linarith, hsep, ?_, ?_, ?_⟩
  · intro x hx
    constructor <;> linarith [hx.1, hx.2]
  · intro x hx
    constructor <;> linarith [hx.1, hx.2]
  · have hid : (-1 / 2 + (σ - 1 / 2) / 4) -
        ((-1 / 2 + (σ - 1 / 2) / 4) - (σ - σ') / 8) = (σ - σ') / 8 := by ring
    rw [hid]
    field_simp [ne_of_gt hgap]



/-- On nested positive cylinders, selected traces and chain energy have a
uniform bound in terms of the actual outer weighted power mass. -/
theorem b_positive_concentric_selected_traces_uniform (d : ℕ) (κ : ℝ) (hκ : 0 < κ)
    (σ' σ : ℝ) (hσ' : 1 / 2 ≤ σ') (hσ : σ' < σ) (hσ1 : σ ≤ 1)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d) (hell : IsUniformlyElliptic κ ρ α)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hcal : IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1) u G)
    (hu : ∀ᵐ z ∂volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1), 0 ≤ u z)
    (ε p : ℝ) (hε : 0 < ε) (hp : 0 < p) (hp2 : p ≤ 1 / 2) :
    let r : ℝ := 1 / 2 + (σ' - 1 / 2) / 2
    let R : ℝ := 1 / 2 + (σ - 1 / 2) / 2
    let a : ℝ := -3 / 4 - (σ - 1 / 2) / 4
    let b : ℝ := -1 / 2 + (σ - 1 / 2) / 4
    let δ : ℝ := (σ - σ') / 8
    let χ : Vec d → ℝ := PDE.canonicalBallCutoff (0 : Vec d) r R
    let M : ℝ := ∫ z in Set.Ioo a b ×ˢ sourceBall (0 : Vec d) R,
      ρ z.2 * Real.rpow (u z + ε) p
    let D : ℝ := (8 + 8192 / κ ^ 4) / (σ - σ') ^ 2
    ∃ (E : ℝ → ℝ) (s t : ℝ), s ∈ Set.Ioo a (a + δ) ∧ t ∈ Set.Ioo (b - δ) b ∧
      (∀ᵐ q ∂volume.restrict (Set.Ioo a b),
        E q = ∫ x in sourceBall 0 R, ρ x * χ x ^ 2 * Real.rpow (u (q,x) + ε) p) ∧
      (∀ q ∈ Set.Ioo a b, q < t → E q ≤ D * M) ∧ s < t ∧
      (p / 2) ^ 2 * (∫ q in s..t, ∫ x in sourceBall 0 R,
        χ x ^ 2 * (Real.rpow (u (q,x) + ε) (p-2) * euclideanSq (G (q,x)))) ≤
        κ⁻¹ * D * M := by
  dsimp only
  let r : ℝ := 1 / 2 + (σ' - 1 / 2) / 2
  let R : ℝ := 1 / 2 + (σ - 1 / 2) / 2
  let a : ℝ := -3 / 4 - (σ - 1 / 2) / 4
  let b : ℝ := -1 / 2 + (σ - 1 / 2) / 4
  let δ : ℝ := (σ - σ') / 8
  let χ : Vec d → ℝ := PDE.canonicalBallCutoff (0 : Vec d) r R
  let M : ℝ := ∫ z in Set.Ioo a b ×ˢ sourceBall (0 : Vec d) R,
    ρ z.2 * Real.rpow (u z + ε) p
  have hgap : 0 < σ - σ' := sub_pos.mpr hσ
  have hgap1 : σ - σ' ≤ 1 := by linarith
  obtain ⟨hr, hrR, hR1, hχ, hχc, hχU, hχbounds, _, hgrad⟩ :=
    b_positive_concentric_spatial_cutoff d σ' σ hσ' hσ hσ1
  obtain ⟨hab, hδ, hsep, hsI, htI, htinv⟩ :=
    b_positive_concentric_time_windows σ' σ hσ' hσ hσ1
  have hδ' : 0 < δ := by simpa only [δ] using hδ
  have hR : 0 < R := hr.trans hrR
  have htime : Set.Ioo a b ⊆ Set.Ioo (-1 : ℝ) 1 := by
    intro q hq
    dsimp [a, b] at hq
    constructor <;> linarith [hq.1, hq.2]
  have hspace : sourceBall (0 : Vec d) R ⊆ sourceBall 0 1 := by
    intro x hx
    change euclideanNorm (x - 0) < R at hx
    change euclideanNorm (x - 0) < 1
    exact lt_trans hx hR1
  obtain ⟨hshift, hpos⟩ := c8_weighted_caloric_positive_shift hκ hell hcal hu hε
  have hcal' := c11_weighted_caloric_cylinder_mono measurableSet_Ioo measurableSet_Ioo
    (c17_isOpen_sourceBall (0 : Vec d) 1).measurableSet htime hspace hshift
  have hpos' := ae_restrict_of_ae_restrict_of_subset (Set.prod_mono htime hspace) hpos
  have hM : 0 ≤ M := by
    dsimp [M]
    apply integral_nonneg_of_ae
    filter_upwards [hpos'] with z hz
    exact mul_nonneg (hκ.le.trans (hell.2.2 z.2).1)
      (Real.rpow_nonneg (le_of_lt (lt_of_lt_of_le hε hz)) _)
  obtain ⟨E, s, t, hs, ht, hrep, htrace, hst, henergy⟩ :=
    b_positive_power_selected_traces_uniform hκ hR hab hε hp hp2
      (by linarith [hδ'] : a < a + δ) (by linarith [hδ'] : b - δ < b) hsep hsI htI
      ρ α hell (fun z => u z + ε) G hcal' hpos' χ hχ hχc hχU
      (fun x => (hχbounds x).1) (fun x => (hχbounds x).2) (64 / (σ - σ')) hgrad
  have hcoef := b_positive_concentric_coefficient_gap hκ hgap hgap1
  have hm := mul_le_mul_of_nonneg_right hcoef hM
  have hchain := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hcoef (inv_nonneg.mpr hκ.le)) hM
  rw [htinv] at htrace henergy
  refine ⟨E, s, t, hs, ht, hrep, ?_, hst, ?_⟩
  · intro q hq hqt
    exact (htrace q hq hqt).trans hm
  · exact henergy.trans hchain



/-- Combining the two literal Euclidean-square estimates gives the matrix
coefficient-energy estimate with their common mass factored out. -/
theorem b_positive_coefficient_energy_of_square_bounds {d : ℕ}
    (κ : ℝ) (hκ : 0 < κ) (ρ : Vec d → ℝ) (α : Vec d → Mat d)
    (hell : IsUniformlyElliptic κ ρ α)
    (μ : Measure (ℝ × Vec d)) (η w : ℝ × Vec d → ℝ)
    (G : ℝ × Vec d → Vec d) (p : ℝ) (A B M : ℝ≥0∞)
    (hmA : AEMeasurable (fun z => ENNReal.ofReal
      (η z ^ 2 * euclideanSq ((p / 2 * (w z) ^ (p / 2 - 1)) • G z))) μ)
    (hmB : AEMeasurable (fun z => ENNReal.ofReal
      (((w z) ^ (p / 2)) ^ 2 * euclideanSq (fun j => fderiv ℝ η z (0, unitVector j)))) μ)
    (hA : (∫⁻ z, ENNReal.ofReal
      (η z ^ 2 * euclideanSq ((p / 2 * (w z) ^ (p / 2 - 1)) • G z)) ∂μ) ≤ A * M)
    (hB : (∫⁻ z, ENNReal.ofReal
      (((w z) ^ (p / 2)) ^ 2 * euclideanSq (fun j => fderiv ℝ η z (0, unitVector j))) ∂μ) ≤ B * M) :
    (∫⁻ z, ENNReal.ofReal (dot
      ((α z.2).mulVec (η z • ((p / 2 * (w z) ^ (p / 2 - 1)) • G z) +
        (w z) ^ (p / 2) • (fun j => fderiv ℝ η z (0, unitVector j))))
      (η z • ((p / 2 * (w z) ^ (p / 2 - 1)) • G z) +
        (w z) ^ (p / 2) • (fun j => fderiv ℝ η z (0, unitVector j)))) ∂μ) ≤
      (ENNReal.ofReal (2 * κ⁻¹) * (A + B)) * M := by
  have h := c9_small_power_cutoff_coefficient_energy_lintegral κ hκ ρ α hell μ η w G p
    (A * M) (B * M) hmA hmB hA hB
  simpa only [add_mul, mul_assoc] using h

/-- Conditional assembly for the actual nested cutoff. The two displayed
square estimates and their measurability are the remaining analytic inputs. -/
theorem b_positive_nested_coefficient_energy_of_square_bounds
    (d : ℕ) (κ : ℝ) (hκ : 0 < κ) (A B : ℝ≥0∞)
    (hAfin : A ≠ ⊤) (hBfin : B ≠ ⊤) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (σ' σ : ℝ) (ρ : Vec d → ℝ) (α : Vec d → Mat d),
    IsUniformlyElliptic κ ρ α →
    ∀ (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d) (ε p : ℝ),
    let r : ℝ := 1 / 2 + (σ' - 1 / 2) / 2
    let R : ℝ := 1 / 2 + (σ - 1 / 2) / 2
    let a : ℝ := -3 / 4 - (σ - 1 / 2) / 4
    let a' : ℝ := -3 / 4 - (σ' - 1 / 2) / 4
    let b : ℝ := -1 / 2 + (σ - 1 / 2) / 4
    let δ : ℝ := (σ - σ') / 8
    let η : ℝ × Vec d → ℝ := fun z =>
      (PDE.Parabolic.LocalMax.cylTimeRamp (a + δ) ((a' - (a + δ)) / 2) z.1 *
        PDE.Parabolic.LocalMax.timeRamp (b - δ) δ z.1) *
          PDE.canonicalBallCutoff (0 : Vec d) r R z.2
    let w : ℝ × Vec d → ℝ := fun z => u z + ε
    let μ : Measure (ℝ × Vec d) := volume.restrict
      (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall (0 : Vec d) 1)
    let M : ℝ≥0∞ := ∫⁻ z in Set.Ioo a b ×ˢ sourceBall (0 : Vec d) R,
      ENNReal.ofReal (w z) ^ p
    let D : ℝ≥0∞ := ENNReal.ofReal ((σ - σ')⁻¹ ^ 2)
    AEMeasurable (fun z => ENNReal.ofReal
      (η z ^ 2 * euclideanSq ((p / 2 * (w z) ^ (p / 2 - 1)) • G z))) μ →
    AEMeasurable (fun z => ENNReal.ofReal
      (((w z) ^ (p / 2)) ^ 2 * euclideanSq (fun j => fderiv ℝ η z (0, unitVector j)))) μ →
    (∫⁻ z, ENNReal.ofReal
      (η z ^ 2 * euclideanSq ((p / 2 * (w z) ^ (p / 2 - 1)) • G z)) ∂μ) ≤ (A * D) * M →
    (∫⁻ z, ENNReal.ofReal
      (((w z) ^ (p / 2)) ^ 2 * euclideanSq (fun j => fderiv ℝ η z (0, unitVector j))) ∂μ) ≤ (B * D) * M →
    (∫⁻ z, ENNReal.ofReal (dot
      ((α z.2).mulVec (η z • ((p / 2 * (w z) ^ (p / 2 - 1)) • G z) +
        (w z) ^ (p / 2) • (fun j => fderiv ℝ η z (0, unitVector j))))
      (η z • ((p / 2 * (w z) ^ (p / 2 - 1)) • G z) +
        (w z) ^ (p / 2) • (fun j => fderiv ℝ η z (0, unitVector j)))) ∂μ) ≤
      (C * D) * M := by
  refine ⟨ENNReal.ofReal (2 * κ⁻¹) * (A + B),
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.add_ne_top.mpr ⟨hAfin, hBfin⟩), ?_⟩
  intro σ' σ ρ α hell u G ε p r R a a' b δ η w μ M D hmA hmB hA hB
  have h := b_positive_coefficient_energy_of_square_bounds κ hκ ρ α hell μ η w G p
    (A * D) (B * D) M hmA hmB hA hB
  simpa only [← add_mul, mul_assoc] using h

/-- The spatial derivative part is controlled by the mass on the cutoff
support and the uniform spatial gradient bound. -/
theorem b_positive_cutoff_derivative_square_bound {d : ℕ}
    (μ : Measure (ℝ × Vec d)) (η w : ℝ × Vec d → ℝ)
    (T : Set (ℝ × Vec d)) (hT : MeasurableSet T)
    (hsupp : tsupport η ⊆ T) (L p : ℝ) (hp : 0 ≤ p)
    (hw : ∀ᵐ z ∂μ, 0 ≤ w z)
    (hgrad : ∀ z, euclideanSq (fun j => fderiv ℝ η z (0, unitVector j)) ≤ L ^ 2) :
    (∫⁻ z, ENNReal.ofReal
      (((w z) ^ (p / 2)) ^ 2 * euclideanSq (fun j => fderiv ℝ η z (0, unitVector j))) ∂μ) ≤
      ENNReal.ofReal (L ^ 2) * ∫⁻ z in T, ENNReal.ofReal (w z) ^ p ∂μ := by
  calc
    _ ≤ ∫⁻ z, T.indicator (fun z => ENNReal.ofReal (L ^ 2) *
        ENNReal.ofReal (w z) ^ p) z ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [hw] with z hz
      by_cases hzT : z ∈ T
      · rw [Set.indicator_of_mem hzT]
        have heq : (w z ^ (p / 2)) ^ 2 = w z ^ p := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hz]
          congr 1 <;> norm_num
        rw [heq, ENNReal.ofReal_mul (Real.rpow_nonneg hz _),
          ENNReal.ofReal_rpow_of_nonneg hz hp]
        simpa only [mul_comm] using
          mul_le_mul_left (ENNReal.ofReal_le_ofReal (hgrad z)) (ENNReal.ofReal (w z ^ p))
      · rw [Set.indicator_of_notMem hzT]
        have hn : z ∉ tsupport η := fun h => hzT (hsupp h)
        simp [fderiv_of_notMem_tsupport ℝ hn, euclideanSq, dot]
    _ = _ := by
      rw [lintegral_indicator hT, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

/-- The spatial derivative of the canonical nested cutoff has the required
inverse-gap-square bound against the outer-cylinder mass. -/
theorem b_positive_nested_cutoff_derivative_square_bound
    (d : ℕ) (σ' σ : ℝ) (hσ' : 1 / 2 ≤ σ') (hσ : σ' < σ) (hσ1 : σ ≤ 1)
    (w : ℝ × Vec d → ℝ) (p : ℝ) (hp : 0 ≤ p)
    (hw : ∀ᵐ z ∂volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall (0 : Vec d) 1),
      0 ≤ w z) :
    let r : ℝ := 1 / 2 + (σ' - 1 / 2) / 2
    let R : ℝ := 1 / 2 + (σ - 1 / 2) / 2
    let a : ℝ := -3 / 4 - (σ - 1 / 2) / 4
    let a' : ℝ := -3 / 4 - (σ' - 1 / 2) / 4
    let b : ℝ := -1 / 2 + (σ - 1 / 2) / 4
    let δ : ℝ := (σ - σ') / 8
    let η : ℝ × Vec d → ℝ := fun z =>
      (PDE.Parabolic.LocalMax.cylTimeRamp (a + δ) ((a' - (a + δ)) / 2) z.1 *
        PDE.Parabolic.LocalMax.timeRamp (b - δ) δ z.1) *
          PDE.canonicalBallCutoff (0 : Vec d) r R z.2
    (∫⁻ z in Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall (0 : Vec d) 1, ENNReal.ofReal
      (((w z) ^ (p / 2)) ^ 2 * euclideanSq (fun j => fderiv ℝ η z (0, unitVector j)))) ≤
      (ENNReal.ofReal 4096 * ENNReal.ofReal ((σ - σ')⁻¹ ^ 2)) *
        ∫⁻ z in Set.Ioo a b ×ˢ sourceBall (0 : Vec d) R, ENNReal.ofReal (w z) ^ p := by
  intro r R a a' b δ η
  have hr := c5_positive_concentric_radius_bounds σ' σ hσ' hσ hσ1
  have ht := c5_positive_concentric_time_gaps σ' σ hσ' hσ hσ1
  have hc := c11_compact_cylinder_cutoff (d := d) (r := r) (R := R)
    (T := a + δ) (T' := a') (b := b - δ) (h := δ) hr.1.le hr.2.1 ht.2.2.1 ht.1
  have hsupp : tsupport η ⊆ Set.Ioo a b ×ˢ sourceBall (0 : Vec d) R := by
    intro z hz
    have h := hc.2.2.1 hz
    have hx := hc.2.2.2.1 h.2
    rw [← c8_sourceBall_eq_euclideanBall (0 : Vec d) (lt_trans hr.1 hr.2.1)] at hx
    refine ⟨⟨?_, ?_⟩, hx⟩ <;> dsimp [a, b, δ] at * <;> linarith [ht.1, h.1.1, h.1.2]
  obtain ⟨C, hC, hd⟩ := c5_positive_concentric_cutoff_derivatives
  have hg := (hd d σ' σ hσ' hσ).2
  have hT : MeasurableSet (Set.Ioo a b ×ˢ sourceBall (0 : Vec d) R) :=
    measurableSet_Ioo.prod (c17_isOpen_sourceBall (0 : Vec d) R).measurableSet
  have h := b_positive_cutoff_derivative_square_bound
    (volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall (0 : Vec d) 1)) η w _ hT hsupp
    (64 / (σ - σ')) p hp hw hg
  calc
    _ ≤ ENNReal.ofReal ((64 / (σ - σ')) ^ 2) *
        ∫⁻ z in Set.Ioo a b ×ˢ sourceBall (0 : Vec d) R,
          ENNReal.ofReal (w z) ^ p :=
      h.trans (mul_le_mul_right (lintegral_mono' (Measure.restrict_mono le_rfl Measure.restrict_le_self) le_rfl) _)
    _ = _ := by
      have heq : (64 / (σ - σ')) ^ 2 = 4096 * (σ - σ')⁻¹ ^ 2 := by
        rw [div_eq_mul_inv]; ring
      rw [heq, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4096)]

/-- For the canonical nested cutoff, only the chain-gradient square bound
and the two measurability assertions remain to be supplied. -/
theorem b_positive_nested_coefficient_energy_of_chain_bound
    (d : ℕ) (κ : ℝ) (hκ : 0 < κ) (A : ℝ≥0∞) (hAfin : A ≠ ⊤) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (σ' σ : ℝ),
    1 / 2 ≤ σ' → σ' < σ → σ ≤ 1 →
    ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d), IsUniformlyElliptic κ ρ α →
    ∀ (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d) (ε p : ℝ), 0 ≤ p →
    let r : ℝ := 1 / 2 + (σ' - 1 / 2) / 2
    let R : ℝ := 1 / 2 + (σ - 1 / 2) / 2
    let a : ℝ := -3 / 4 - (σ - 1 / 2) / 4
    let a' : ℝ := -3 / 4 - (σ' - 1 / 2) / 4
    let b : ℝ := -1 / 2 + (σ - 1 / 2) / 4
    let δ : ℝ := (σ - σ') / 8
    let η : ℝ × Vec d → ℝ := fun z =>
      (PDE.Parabolic.LocalMax.cylTimeRamp (a + δ) ((a' - (a + δ)) / 2) z.1 *
        PDE.Parabolic.LocalMax.timeRamp (b - δ) δ z.1) *
          PDE.canonicalBallCutoff (0 : Vec d) r R z.2
    let w : ℝ × Vec d → ℝ := fun z => u z + ε
    let μ : Measure (ℝ × Vec d) := volume.restrict
      (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall (0 : Vec d) 1)
    let M : ℝ≥0∞ := ∫⁻ z in Set.Ioo a b ×ˢ sourceBall (0 : Vec d) R,
      ENNReal.ofReal (w z) ^ p
    let D : ℝ≥0∞ := ENNReal.ofReal ((σ - σ')⁻¹ ^ 2)
    (∀ᵐ z ∂μ, 0 ≤ w z) →
    AEMeasurable (fun z => ENNReal.ofReal
      (η z ^ 2 * euclideanSq ((p / 2 * (w z) ^ (p / 2 - 1)) • G z))) μ →
    AEMeasurable (fun z => ENNReal.ofReal
      (((w z) ^ (p / 2)) ^ 2 * euclideanSq (fun j => fderiv ℝ η z (0, unitVector j)))) μ →
    (∫⁻ z, ENNReal.ofReal
      (η z ^ 2 * euclideanSq ((p / 2 * (w z) ^ (p / 2 - 1)) • G z)) ∂μ) ≤ (A * D) * M →
    (∫⁻ z, ENNReal.ofReal (dot
      ((α z.2).mulVec (η z • ((p / 2 * (w z) ^ (p / 2 - 1)) • G z) +
        (w z) ^ (p / 2) • (fun j => fderiv ℝ η z (0, unitVector j))))
      (η z • ((p / 2 * (w z) ^ (p / 2 - 1)) • G z) +
        (w z) ^ (p / 2) • (fun j => fderiv ℝ η z (0, unitVector j)))) ∂μ) ≤
      (C * D) * M := by
  obtain ⟨C, hC, h⟩ := b_positive_nested_coefficient_energy_of_square_bounds
    d κ hκ A (ENNReal.ofReal 4096) hAfin ENNReal.ofReal_ne_top
  refine ⟨C, hC, ?_⟩
  intro σ' σ hσ' hσ hσ1 ρ α hell u G ε p hp r R a a' b δ η w μ M D hw hmA hmB hA
  apply h σ' σ ρ α hell u G ε p hmA hmB hA
  exact b_positive_nested_cutoff_derivative_square_bound d σ' σ hσ' hσ hσ1 w p hp hw

/-- Both square summands are measurable for a shifted nonnegative caloric
field and a smooth cutoff. -/
theorem b_positive_cutoff_square_aemeasurable {d : ℕ}
    (ρ : Vec d → ℝ) (α : Vec d → Mat d)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hcal : IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1) u G)
    (hu : ∀ᵐ z ∂volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall (0 : Vec d) 1), 0 ≤ u z)
    (ε p : ℝ) (hε : 0 < ε) (η : ℝ × Vec d → ℝ) (hη : ContDiff ℝ (⊤ : ℕ∞) η) :
    let μ : Measure (ℝ × Vec d) := volume.restrict
      (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall (0 : Vec d) 1)
    AEMeasurable (fun z => ENNReal.ofReal
      (η z ^ 2 * euclideanSq ((p / 2 * (u z + ε) ^ (p / 2 - 1)) • G z))) μ ∧
    AEMeasurable (fun z => ENNReal.ofReal
      (((u z + ε) ^ (p / 2)) ^ 2 * euclideanSq
        (fun j => fderiv ℝ η z (0, unitVector j)))) μ := by
  intro μ
  have hpw (q : ℝ) : AEStronglyMeasurable (fun z => (u z + ε) ^ q) μ := by
    have hc : Continuous (fun x : ℝ => Real.rpow (max ε x) q) := by
      apply (continuous_const.max continuous_id).rpow_const
      intro x
      left
      exact ne_of_gt (lt_of_lt_of_le hε (le_max_left ε x))
    have hwm : AEStronglyMeasurable (fun z => u z + ε) μ :=
      hcal.1.aestronglyMeasurable.add aestronglyMeasurable_const
    have hm := hc.comp_aestronglyMeasurable hwm
    apply hm.congr
    filter_upwards [hu] with z hz
    simp only [max_eq_right (show ε ≤ u z + ε by linarith), Real.rpow_eq_pow]
  have hs : Continuous (euclideanSq : Vec d → ℝ) := by
    unfold euclideanSq dot
    fun_prop
  have hD : Continuous (fun z : ℝ × Vec d =>
      euclideanSq (fun j => fderiv ℝ η z (0, unitVector j))) := by
    apply hs.comp
    apply continuous_pi
    intro j
    exact (hη.continuous_fderiv_apply (by simp)).comp (continuous_id.prodMk continuous_const)
  have hchain : AEStronglyMeasurable (fun z =>
      η z ^ 2 * euclideanSq ((p / 2 * (u z + ε) ^ (p / 2 - 1)) • G z)) μ := by
    have hscalar : AEStronglyMeasurable (fun z =>
        p / 2 * (u z + ε) ^ (p / 2 - 1)) μ :=
      aestronglyMeasurable_const.mul (hpw (p / 2 - 1))
    have hvec := hscalar.smul hcal.2.1
    exact (hη.continuous.aestronglyMeasurable.pow 2).mul
      (hs.comp_aestronglyMeasurable hvec)
  have hderiv : AEStronglyMeasurable (fun z =>
      ((u z + ε) ^ (p / 2)) ^ 2 * euclideanSq
        (fun j => fderiv ℝ η z (0, unitVector j))) μ :=
    ((hpw (p / 2)).pow 2).mul hD.aestronglyMeasurable
  exact ⟨hchain.aemeasurable.ennreal_ofReal, hderiv.aemeasurable.ennreal_ofReal⟩

/-- The caloric hypotheses discharge the square measurability obligations. -/
theorem b_positive_nested_coefficient_energy_of_caloric_chain_bound
    (d : ℕ) (κ : ℝ) (hκ : 0 < κ) (A : ℝ≥0∞) (hAfin : A ≠ ⊤) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (σ' σ : ℝ),
    1 / 2 ≤ σ' → σ' < σ → σ ≤ 1 →
    ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d), IsUniformlyElliptic κ ρ α →
    ∀ (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d),
    IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1) u G →
    (∀ᵐ z ∂volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall (0 : Vec d) 1), 0 ≤ u z) →
    ∀ ε p : ℝ, 0 < ε → 0 ≤ p →
    let r : ℝ := 1 / 2 + (σ' - 1 / 2) / 2
    let R : ℝ := 1 / 2 + (σ - 1 / 2) / 2
    let a : ℝ := -3 / 4 - (σ - 1 / 2) / 4
    let a' : ℝ := -3 / 4 - (σ' - 1 / 2) / 4
    let b : ℝ := -1 / 2 + (σ - 1 / 2) / 4
    let δ : ℝ := (σ - σ') / 8
    let η : ℝ × Vec d → ℝ := fun z =>
      (PDE.Parabolic.LocalMax.cylTimeRamp (a + δ) ((a' - (a + δ)) / 2) z.1 *
        PDE.Parabolic.LocalMax.timeRamp (b - δ) δ z.1) *
          PDE.canonicalBallCutoff (0 : Vec d) r R z.2
    let w : ℝ × Vec d → ℝ := fun z => u z + ε
    let μ : Measure (ℝ × Vec d) := volume.restrict
      (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall (0 : Vec d) 1)
    let M : ℝ≥0∞ := ∫⁻ z in Set.Ioo a b ×ˢ sourceBall (0 : Vec d) R,
      ENNReal.ofReal (w z) ^ p
    let D : ℝ≥0∞ := ENNReal.ofReal ((σ - σ')⁻¹ ^ 2)
    (∫⁻ z, ENNReal.ofReal
      (η z ^ 2 * euclideanSq ((p / 2 * (w z) ^ (p / 2 - 1)) • G z)) ∂μ) ≤ (A * D) * M →
    (∫⁻ z, ENNReal.ofReal (dot
      ((α z.2).mulVec (η z • ((p / 2 * (w z) ^ (p / 2 - 1)) • G z) +
        (w z) ^ (p / 2) • (fun j => fderiv ℝ η z (0, unitVector j))))
      (η z • ((p / 2 * (w z) ^ (p / 2 - 1)) • G z) +
        (w z) ^ (p / 2) • (fun j => fderiv ℝ η z (0, unitVector j)))) ∂μ) ≤
      (C * D) * M := by
  obtain ⟨C, hC, h⟩ := b_positive_nested_coefficient_energy_of_chain_bound d κ hκ A hAfin
  refine ⟨C, hC, ?_⟩
  intro σ' σ hσ' hσ hσ1 ρ α hell u G hcal hu ε p hε hp r R a a' b δ η w μ M D hA
  have hr := c5_positive_concentric_radius_bounds σ' σ hσ' hσ hσ1
  have ht := c5_positive_concentric_time_gaps σ' σ hσ' hσ hσ1
  have hη : ContDiff ℝ (⊤ : ℕ∞) η :=
    (c11_compact_cylinder_cutoff (d := d) (r := r) (R := R)
      (T := a + δ) (T' := a') (b := b - δ) (h := δ)
      hr.1.le hr.2.1 ht.2.2.1 ht.1).1
  obtain ⟨hmA, hmB⟩ := b_positive_cutoff_square_aemeasurable ρ α u G hcal hu ε p hε η hη
  have hw : ∀ᵐ z ∂μ, 0 ≤ w z := by
    filter_upwards [hu] with z hz
    dsimp [w]
    linarith
  exact h σ' σ hσ' hσ hσ1 ρ α hell u G ε p hp hw hmA hmB hA

/-- Localize the chain-gradient square to the interval supporting the cutoff,
where it is bounded by the positive-power energy of its spatial cutoff. -/
theorem b_positive_chain_square_le_interval_energy {d : ℕ}
    (μ : Measure (ℝ × Vec d)) (T : Set (ℝ × Vec d)) (hT : MeasurableSet T)
    (η w : ℝ × Vec d → ℝ) (χ : Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (p : ℝ) (hsupp : tsupport η ⊆ T)
    (hcut : ∀ z, η z ^ 2 ≤ χ z.2 ^ 2) (hw : ∀ᵐ z ∂μ, 0 < w z) :
    (∫⁻ z, ENNReal.ofReal
      (η z ^ 2 * euclideanSq ((p / 2 * (w z) ^ (p / 2 - 1)) • G z)) ∂μ) ≤
    ENNReal.ofReal ((p / 2) ^ 2) *
      ∫⁻ z in T, ENNReal.ofReal
        (χ z.2 ^ 2 * ((w z) ^ (p - 2) * euclideanSq (G z))) ∂μ := by
  calc
    _ ≤ ∫⁻ z, T.indicator (fun z => ENNReal.ofReal ((p / 2) ^ 2) *
        ENNReal.ofReal (χ z.2 ^ 2 * ((w z) ^ (p - 2) * euclideanSq (G z)))) z ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [hw] with z hz
      by_cases hzT : z ∈ T
      · rw [Set.indicator_of_mem hzT]
        have hr : ((w z) ^ (p / 2 - 1)) ^ 2 = (w z) ^ (p - 2) := by
          have hh := Real.rpow_add hz (p / 2 - 1) (p / 2 - 1)
          have hex : p / 2 - 1 + (p / 2 - 1) = p - 2 := by ring
          rw [hex] at hh
          simpa only [Real.rpow_eq_pow, pow_two] using hh.symm
        have hg : 0 ≤ euclideanSq (G z) := by
          unfold euclideanSq dot
          exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
        have hreal : η z ^ 2 * euclideanSq ((p / 2 * (w z) ^ (p / 2 - 1)) • G z) ≤
            (p / 2) ^ 2 * (χ z.2 ^ 2 * ((w z) ^ (p - 2) * euclideanSq (G z))) := by
          rw [EinsteinRelation.Environment.AKMTestIntegralSupport.euclideanSq_smul, mul_pow, hr]
          have := mul_le_mul_of_nonneg_right (hcut z)
            (mul_nonneg (sq_nonneg (p / 2)) (mul_nonneg (Real.rpow_nonneg hz.le (p - 2)) hg))
          nlinarith
        have h := ENNReal.ofReal_le_ofReal hreal
        rw [ENNReal.ofReal_mul (sq_nonneg (p / 2))] at h
        exact h
      · rw [Set.indicator_of_notMem hzT]
        have hn : z ∉ tsupport η := fun h => hzT (hsupp h)
        have he : η z = 0 := image_eq_zero_of_notMem_tsupport hn
        simp [he]
    _ = _ := by
      rw [lintegral_indicator hT, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

/-- The exact nested cutoff localizes the chain square to any interval
covering its time support. -/
theorem b_positive_nested_chain_square_le_interval_energy
    (d : ℕ) (σ' σ : ℝ) (hσ' : 1 / 2 ≤ σ') (hσ : σ' < σ) (hσ1 : σ ≤ 1)
    (w : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d) (p s t : ℝ)
    (hs : s < (-3 / 4 - (σ - 1 / 2) / 4) + (σ - σ') / 8)
    (ht : (-1 / 2 + (σ - 1 / 2) / 4) - (σ - σ') / 8 < t)
    (hw : ∀ᵐ z ∂volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall (0 : Vec d) 1),
      0 < w z) :
    let r : ℝ := 1 / 2 + (σ' - 1 / 2) / 2
    let R : ℝ := 1 / 2 + (σ - 1 / 2) / 2
    let a : ℝ := -3 / 4 - (σ - 1 / 2) / 4
    let a' : ℝ := -3 / 4 - (σ' - 1 / 2) / 4
    let b : ℝ := -1 / 2 + (σ - 1 / 2) / 4
    let δ : ℝ := (σ - σ') / 8
    let χ : Vec d → ℝ := PDE.canonicalBallCutoff (0 : Vec d) r R
    let η : ℝ × Vec d → ℝ := fun z =>
      (PDE.Parabolic.LocalMax.cylTimeRamp (a + δ) ((a' - (a + δ)) / 2) z.1 *
        PDE.Parabolic.LocalMax.timeRamp (b - δ) δ z.1) * χ z.2
    (∫⁻ z in Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall (0 : Vec d) 1, ENNReal.ofReal
      (η z ^ 2 * euclideanSq ((p / 2 * (w z) ^ (p / 2 - 1)) • G z))) ≤
      ENNReal.ofReal ((p / 2) ^ 2) *
        ∫⁻ z in Set.Ioo s t ×ˢ sourceBall (0 : Vec d) R, ENNReal.ofReal
          (χ z.2 ^ 2 * ((w z) ^ (p - 2) * euclideanSq (G z))) := by
  intro r R a a' b δ χ η
  have hr := c5_positive_concentric_radius_bounds σ' σ hσ' hσ hσ1
  have htgap := c5_positive_concentric_time_gaps σ' σ hσ' hσ hσ1
  have hc := c11_compact_cylinder_cutoff (d := d) (r := r) (R := R)
    (T := a + δ) (T' := a') (b := b - δ) (h := δ) hr.1.le hr.2.1 htgap.2.2.1 htgap.1
  have hsupp : tsupport η ⊆ Set.Ioo s t ×ˢ sourceBall (0 : Vec d) R := by
    intro z hz
    have h := hc.2.2.1 hz
    have hx := hc.2.2.2.1 h.2
    rw [← c8_sourceBall_eq_euclideanBall (0 : Vec d) (lt_trans hr.1 hr.2.1)] at hx
    exact ⟨⟨lt_of_lt_of_le hs h.1.1, lt_of_le_of_lt h.1.2 ht⟩, hx⟩
  have hcut : ∀ z, η z ^ 2 ≤ χ z.2 ^ 2 := by
    intro z
    have hθ0 : 0 ≤ PDE.Parabolic.LocalMax.cylTimeRamp (a + δ) ((a' - (a + δ)) / 2) z.1 *
        PDE.Parabolic.LocalMax.timeRamp (b - δ) δ z.1 :=
      mul_nonneg (Real.smoothTransition.nonneg _) (PDE.Parabolic.LocalMax.timeRamp_nonneg _ _ _)
    have hθ1 : PDE.Parabolic.LocalMax.cylTimeRamp (a + δ) ((a' - (a + δ)) / 2) z.1 *
        PDE.Parabolic.LocalMax.timeRamp (b - δ) δ z.1 ≤ 1 :=
      (mul_le_mul (Real.smoothTransition.le_one _) (PDE.Parabolic.LocalMax.timeRamp_le_one _ _ _)
        (PDE.Parabolic.LocalMax.timeRamp_nonneg _ _ _) zero_le_one).trans_eq (one_mul 1)
    have hθsq : (PDE.Parabolic.LocalMax.cylTimeRamp (a + δ) ((a' - (a + δ)) / 2) z.1 *
        PDE.Parabolic.LocalMax.timeRamp (b - δ) δ z.1) ^ 2 ≤ 1 := by nlinarith
    dsimp only [η]
    rw [mul_pow]
    nlinarith [mul_le_mul_of_nonneg_right hθsq (sq_nonneg (χ z.2))]
  have hT : MeasurableSet (Set.Ioo s t ×ˢ sourceBall (0 : Vec d) R) :=
    measurableSet_Ioo.prod (c17_isOpen_sourceBall (0 : Vec d) R).measurableSet
  have h := b_positive_chain_square_le_interval_energy
    (volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall (0 : Vec d) 1)) _ hT η w χ G p hsupp hcut hw
  exact h.trans (mul_le_mul_right
    (lintegral_mono' (Measure.restrict_mono le_rfl Measure.restrict_le_self) le_rfl) _)

/-- Convert the selected-interval gradient energy to its nonnegative
spacetime lintegral. -/
theorem b_positive_interval_lintegral_eq_integral {d : ℕ}
    (s t R : ℝ) (hst : s ≤ t) (f : ℝ × Vec d → ℝ)
    (hi : Integrable f (volume.restrict (Set.Ioo s t ×ˢ sourceBall (0 : Vec d) R)))
    (hf : ∀ᵐ z ∂volume.restrict (Set.Ioo s t ×ˢ sourceBall (0 : Vec d) R), 0 ≤ f z) :
    (∫⁻ z in Set.Ioo s t ×ˢ sourceBall (0 : Vec d) R, ENNReal.ofReal (f z)) =
      ENNReal.ofReal (∫ q in s..t, ∫ x in sourceBall (0 : Vec d) R, f (q,x)) := by
  have hprod : (volume.restrict (Set.Ioo s t)).prod
      (volume.restrict (sourceBall (0 : Vec d) R)) =
      (volume : Measure (ℝ × Vec d)).restrict (Set.Ioo s t ×ˢ sourceBall 0 R) := by
    rw [Measure.prod_restrict]
    rfl
  have hi' : Integrable f ((volume.restrict (Set.Ioo s t)).prod
      (volume.restrict (sourceBall (0 : Vec d) R))) := by rw [hprod]; exact hi
  rw [← ofReal_integral_eq_lintegral_ofReal hi hf]
  congr 1
  rw [intervalIntegral.integral_of_le hst, integral_Ioc_eq_integral_Ioo]
  rw [← integral_prod _ hi', hprod]

/-- Ellipticity bounds the weighted positive-power mass by the unweighted mass. -/
theorem b_positive_weighted_mass_le {d : ℕ} (κ : ℝ) (hκ : 0 < κ)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d) (hell : IsUniformlyElliptic κ ρ α)
    (μ : Measure (ℝ × Vec d)) (w : ℝ × Vec d → ℝ) (p : ℝ) (hp : 0 ≤ p)
    (hw : ∀ᵐ z ∂μ, 0 ≤ w z)
    (hi : Integrable (fun z => ρ z.2 * Real.rpow (w z) p) μ) :
    ENNReal.ofReal (∫ z, ρ z.2 * Real.rpow (w z) p ∂μ) ≤
      ENNReal.ofReal κ⁻¹ * ∫⁻ z, ENNReal.ofReal (w z) ^ p ∂μ := by
  have hn : ∀ᵐ z ∂μ, 0 ≤ ρ z.2 * Real.rpow (w z) p := by
    filter_upwards [hw] with z hz
    exact mul_nonneg (hκ.le.trans (hell.2.2 z.2).1) (Real.rpow_nonneg hz p)
  rw [ofReal_integral_eq_lintegral_ofReal hi hn]
  calc
    _ ≤ ∫⁻ z, ENNReal.ofReal κ⁻¹ * ENNReal.ofReal (w z) ^ p ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [hw] with z hz
      rw [ENNReal.ofReal_mul (hκ.le.trans (hell.2.2 z.2).1), Real.rpow_eq_pow,
        ← ENNReal.ofReal_rpow_of_nonneg hz hp]
      exact mul_le_mul_left (ENNReal.ofReal_le_ofReal (hell.2.2 z.2).2.1) _
    _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-- The selected positive-power energy controls the chain part of the nested cutoff. -/
theorem b_positive_nested_chain_square_bound
    (d : ℕ) (κ : ℝ) (hκ : 0 < κ) :
    ∃ A : ℝ≥0∞, A ≠ ⊤ ∧ ∀ (σ' σ : ℝ),
    1 / 2 ≤ σ' → σ' < σ → σ ≤ 1 →
    ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d), IsUniformlyElliptic κ ρ α →
    ∀ (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d),
    IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1) u G →
    (∀ᵐ z ∂volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall (0 : Vec d) 1), 0 ≤ u z) →
    ∀ ε p : ℝ, 0 < ε → 0 < p → p ≤ 1 / 2 →
    let r : ℝ := 1 / 2 + (σ' - 1 / 2) / 2
    let R : ℝ := 1 / 2 + (σ - 1 / 2) / 2
    let a : ℝ := -3 / 4 - (σ - 1 / 2) / 4
    let a' : ℝ := -3 / 4 - (σ' - 1 / 2) / 4
    let b : ℝ := -1 / 2 + (σ - 1 / 2) / 4
    let δ : ℝ := (σ - σ') / 8
    let η : ℝ × Vec d → ℝ := fun z =>
      (PDE.Parabolic.LocalMax.cylTimeRamp (a + δ) ((a' - (a + δ)) / 2) z.1 *
        PDE.Parabolic.LocalMax.timeRamp (b - δ) δ z.1) *
          PDE.canonicalBallCutoff (0 : Vec d) r R z.2
    (∫⁻ z in Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall (0 : Vec d) 1, ENNReal.ofReal
      (η z ^ 2 * euclideanSq ((p / 2 * (u z + ε) ^ (p / 2 - 1)) • G z))) ≤
      (A * ENNReal.ofReal ((σ - σ')⁻¹ ^ 2)) *
        ∫⁻ z in Set.Ioo a b ×ˢ sourceBall (0 : Vec d) R, ENNReal.ofReal (u z + ε) ^ p := by
  let K : ℝ := 8 + 8192 / κ ^ 4
  refine ⟨ENNReal.ofReal (κ⁻¹ * K) * ENNReal.ofReal κ⁻¹,
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top, ?_⟩
  intro σ' σ hσ' hσ hσ1 ρ α hell u G hcal hu ε p hε hp hp2 r R a a' b δ η
  let χ : Vec d → ℝ := PDE.canonicalBallCutoff (0 : Vec d) r R
  let M : ℝ := ∫ z in Set.Ioo a b ×ˢ sourceBall (0 : Vec d) R,
    ρ z.2 * Real.rpow (u z + ε) p
  let D : ℝ := K / (σ - σ') ^ 2
  have hr := c5_positive_concentric_radius_bounds σ' σ hσ' hσ hσ1
  have htime : Set.Ioo a b ⊆ Set.Ioo (-1 : ℝ) 1 := by
    intro q hq
    dsimp [a, b] at hq
    constructor <;> linarith [hq.1, hq.2]
  have hspace : sourceBall (0 : Vec d) R ⊆ sourceBall 0 1 := by
    intro x hx
    change euclideanNorm (x - 0) < R at hx
    change euclideanNorm (x - 0) < 1
    exact lt_trans hx hr.2.2
  obtain ⟨hshift, hpos⟩ := c8_weighted_caloric_positive_shift hκ hell hcal hu hε
  have hcal' := c11_weighted_caloric_cylinder_mono measurableSet_Ioo measurableSet_Ioo
    (c17_isOpen_sourceBall (0 : Vec d) 1).measurableSet htime hspace hshift
  have hpos' := ae_restrict_of_ae_restrict_of_subset (Set.prod_mono htime hspace) hpos
  have hw : ∀ᵐ z ∂volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall (0 : Vec d) 1),
      0 < u z + ε := by
    filter_upwards [hpos] with z hz
    exact lt_of_lt_of_le hε hz
  obtain ⟨E, s, t, hs, ht, hrep, htrace, hst, henergy⟩ :=
    b_positive_concentric_selected_traces_uniform d κ hκ σ' σ hσ' hσ hσ1
      ρ α hell u G hcal hu ε p hε hp hp2
  have hχ : ContDiff ℝ (⊤ : ℕ∞) χ := PDE.canonicalBallCutoff_smooth _ hr.1.le hr.2.1
  have hχc : HasCompactSupport χ := PDE.canonicalBallCutoff_hasCompactSupport hr.1.le hr.2.1
  have hp1 : p < 1 := by linarith
  have hg := c13_positive_power_cutoff_gradient_integrable hε hp hp1 ρ α
    (fun z => u z + ε) G hcal' hpos' χ hχ hχc
  have hsub : Set.Ioo s t ×ˢ sourceBall (0 : Vec d) R ⊆
      Set.Ioo a b ×ˢ sourceBall (0 : Vec d) R := by
    apply Set.prod_mono _ Set.Subset.rfl
    intro q hq
    exact ⟨lt_trans hs.1 hq.1, lt_trans hq.2 ht.2⟩
  have hi := hg.mono_measure (Measure.restrict_mono hsub le_rfl)
  have hpselect := ae_restrict_of_ae_restrict_of_subset hsub hpos'
  have hf : ∀ᵐ z ∂volume.restrict (Set.Ioo s t ×ˢ sourceBall (0 : Vec d) R),
      0 ≤ χ z.2 ^ 2 * (Real.rpow (u z + ε) (p - 2) * euclideanSq (G z)) := by
    filter_upwards [hpselect] with z hz
    have hg0 : 0 ≤ euclideanSq (G z) := by
      unfold euclideanSq dot
      exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
    exact mul_nonneg (sq_nonneg _) (mul_nonneg
      (Real.rpow_nonneg (le_of_lt (lt_of_lt_of_le hε hz)) _) hg0)
  have hconv := b_positive_interval_lintegral_eq_integral s t R hst.le
    (fun z => χ z.2 ^ 2 * (Real.rpow (u z + ε) (p - 2) * euclideanSq (G z))) hi hf
  have hchain := b_positive_nested_chain_square_le_interval_energy d σ' σ hσ' hσ hσ1
    (fun z => u z + ε) G p s t hs.2 ht.1 hw
  dsimp only at hchain
  change _ ≤ ENNReal.ofReal ((p / 2) ^ 2) *
    (∫⁻ z in Set.Ioo s t ×ˢ sourceBall (0 : Vec d) R, ENNReal.ofReal
      (χ z.2 ^ 2 * (Real.rpow (u z + ε) (p - 2) * euclideanSq (G z)))) at hchain
  rw [hconv, ← ENNReal.ofReal_mul (sq_nonneg (p / 2))] at hchain
  have hmassint := c13_weighted_positive_power_integrable hκ hε hp hp1 ρ α hell
    (fun z => u z + ε) G hcal' hpos'
  have hmass := b_positive_weighted_mass_le κ hκ ρ α hell
    (volume.restrict (Set.Ioo a b ×ˢ sourceBall (0 : Vec d) R)) (fun z => u z + ε) p hp.le
    (hpos'.mono fun z hz => le_of_lt (lt_of_lt_of_le hε hz)) hmassint
  have hD : 0 ≤ D := by dsimp [D, K]; positivity
  have hKD : κ⁻¹ * D = (κ⁻¹ * K) * (σ - σ')⁻¹ ^ 2 := by
    dsimp [D]; rw [div_eq_mul_inv, inv_pow]; ring
  have he := ENNReal.ofReal_le_ofReal henergy
  change ENNReal.ofReal ((p / 2) ^ 2 * _) ≤ ENNReal.ofReal (κ⁻¹ * D * M) at he
  rw [ENNReal.ofReal_mul (mul_nonneg (inv_nonneg.mpr hκ.le) hD), hKD,
    ENNReal.ofReal_mul (mul_nonneg (inv_nonneg.mpr hκ.le) (by dsimp [K]; positivity))] at he
  exact hchain.trans (he.trans (by
    simpa only [mul_assoc, mul_left_comm, mul_comm] using
      mul_le_mul_left hmass (ENNReal.ofReal (κ⁻¹ * K) * ENNReal.ofReal ((σ - σ')⁻¹ ^ 2))))

/-- The coefficient energy of the exact nested positive-power cutoff is
controlled by the unweighted power mass, uniformly in the small exponent. -/
theorem b_positive_nested_coefficient_energy
    (d : ℕ) (κ : ℝ) (hκ : 0 < κ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (σ' σ : ℝ),
    1 / 2 ≤ σ' → σ' < σ → σ ≤ 1 →
    ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d), IsUniformlyElliptic κ ρ α →
    ∀ (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d),
    IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1) u G →
    (∀ᵐ z ∂volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall (0 : Vec d) 1), 0 ≤ u z) →
    ∀ ε p : ℝ, 0 < ε → 0 < p → p ≤ (d : ℝ) / (2 * ((d : ℝ) + 2)) →
    let r : ℝ := 1 / 2 + (σ' - 1 / 2) / 2
    let R : ℝ := 1 / 2 + (σ - 1 / 2) / 2
    let a : ℝ := -3 / 4 - (σ - 1 / 2) / 4
    let a' : ℝ := -3 / 4 - (σ' - 1 / 2) / 4
    let b : ℝ := -1 / 2 + (σ - 1 / 2) / 4
    let δ : ℝ := (σ - σ') / 8
    let η : ℝ × Vec d → ℝ := fun z =>
      (PDE.Parabolic.LocalMax.cylTimeRamp (a + δ) ((a' - (a + δ)) / 2) z.1 *
        PDE.Parabolic.LocalMax.timeRamp (b - δ) δ z.1) *
          PDE.canonicalBallCutoff (0 : Vec d) r R z.2
    let w : ℝ × Vec d → ℝ := fun z => u z + ε
    let J : ℝ × Vec d → Vec d := fun z =>
      η z • ((p / 2 * (w z) ^ (p / 2 - 1)) • G z) +
        (w z) ^ (p / 2) • (fun j => fderiv ℝ η z (0, unitVector j))
    (∫⁻ z in Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall (0 : Vec d) 1,
      ENNReal.ofReal (dot ((α z.2).mulVec (J z)) (J z))) ≤
      ENNReal.ofReal (C * (σ - σ')⁻¹ ^ (2 : ℕ)) *
        ∫⁻ z in Set.Ioo a b ×ˢ sourceBall (0 : Vec d) R, ENNReal.ofReal (w z) ^ p := by
  obtain ⟨A, hA, hchain⟩ := b_positive_nested_chain_square_bound d κ hκ
  obtain ⟨C, hC, hcoeff⟩ := b_positive_nested_coefficient_energy_of_caloric_chain_bound d κ hκ A hA
  refine ⟨C.toReal, ENNReal.toReal_nonneg, ?_⟩
  intro σ' σ hσ' hσ hσ1 ρ α hell u G hcal hu ε p hε hp hpr r R a a' b δ η w J
  have hden : 0 < 2 * ((d : ℝ) + 2) := by positivity
  have hp2 : p ≤ 1 / 2 := by
    have hb : (d : ℝ) / (2 * ((d : ℝ) + 2)) ≤ 1 / 2 := by
      apply (div_le_iff₀ hden).2
      nlinarith
    exact hpr.trans hb
  have hc := hchain σ' σ hσ' hσ hσ1 ρ α hell u G hcal hu ε p hε hp hp2
  have he := hcoeff σ' σ hσ' hσ hσ1 ρ α hell u G hcal hu ε p hε hp.le hc
  dsimp only at he
  rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hC]
  exact he


end BPositiveEnergyClosureR13

/-- The canonical positive cutoff has measurable coefficient energy bounded by
its outer-cylinder power mass, with a uniform inverse-square gap constant. -/
theorem b_positive_actual_coefficient_energy (d : ℕ) (κ : ℝ) (hκ : 0 < κ) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
      IsUniformlyElliptic κ ρ α → ∀ (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d),
      IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1) u G →
      (∀ᵐ z ∂volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1), 0 ≤ u z) →
      ∀ ε : ℝ, 0 < ε → ∀ σ' σ : ℝ, 1 / 2 ≤ σ' → σ' < σ → σ ≤ 1 →
      ∀ p : ℝ, 0 < p → p ≤ (d : ℝ) / (2 * ((d : ℝ) + 2)) →
      let η := sbxBPositiveCutoff d σ' σ
      let w : ℝ × Vec d → ℝ := fun z => u z + ε
      let J : ℝ × Vec d → Vec d := fun z =>
        η z • ((p / 2 * (w z) ^ (p / 2 - 1)) • G z) +
          (w z) ^ (p / 2) • (fun j => fderiv ℝ η z (0, unitVector j))
      AEMeasurable (fun z => ENNReal.ofReal (dot ((α z.2).mulVec (J z)) (J z)))
        (volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1)) ∧
      (∫⁻ z in Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall (0 : Vec d) 1,
        ENNReal.ofReal (dot ((α z.2).mulVec (J z)) (J z))) ≤
          ENNReal.ofReal (A * (σ - σ') ^ (-(2 : ℝ))) *
            ∫⁻ z in sbxBPositiveCylinder d σ, ENNReal.ofReal (w z) ^ p := by
  obtain ⟨C, hC, hbound⟩ := BPositiveEnergyClosureR13.b_positive_nested_coefficient_energy d κ hκ
  refine ⟨max 1 C, le_max_left _ _, ?_⟩
  intro ρ α hell u G hcal hu ε hε σ' σ hσ' hσ hσ1 p hp hpbound η w J
  have hη := (sbxB_positive_cutoff_admissible d σ' σ hσ' hσ hσ1).1
  constructor
  · exact (b_positive_cutoff_gradient_energy_aemeasurable ρ α hell u G hcal ε η hη p).2
  · have hh := hbound σ' σ hσ' hσ hσ1 ρ α hell u G hcal hu ε p hε hp hpbound
    have hCmax : C ≤ max 1 C := le_max_right _ _
    have hfactor : 0 ≤ (σ - σ')⁻¹ ^ (2 : ℕ) := sq_nonneg _
    have hc := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hCmax hfactor)
    have h := mul_le_mul_left hc (∫⁻ z in sbxBPositiveCylinder d σ, ENNReal.ofReal (w z) ^ p)
    rw [Real.rpow_neg_eq_inv_rpow, Real.rpow_two]
    exact (show _ ≤ ENNReal.ofReal (C * (σ - σ')⁻¹ ^ (2 : ℕ)) *
      (∫⁻ z in sbxBPositiveCylinder d σ, ENNReal.ofReal (w z) ^ p) by
      simpa only [J, w, η, sbxBPositiveCylinder, sbxBPositiveCutoff] using hh).trans h

#print axioms b_positive_actual_coefficient_energy

end EinsteinFull.Calculus
