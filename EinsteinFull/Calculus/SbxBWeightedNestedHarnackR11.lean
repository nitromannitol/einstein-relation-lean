import EinsteinFull.Calculus.SbxBPositiveNestedGainR12
import EinsteinFull.Calculus.SbxBPositiveNormNormalizationR11
import EinsteinFull.Calculus.C8TubeWeightedWeakHarnack
import EinsteinFull.Calculus.SbxBNegativeNestedGainAdapterR11
import EinsteinFull.Calculus.SbxBBackwardLocalGainClosureR13
import EinsteinFull.Calculus.SbxBNegativeFieldGainsClosureR13
import EinsteinFull.Calculus.SbxBPositiveCoefficientEnergyClosureR13
import EinsteinFull.Calculus.SbxBPositiveSliceTraceR12
import EinsteinFull.Calculus.SbxBPositiveSliceLIntegralR12

open EinsteinRelation MeasureTheory EinsteinFull.External.Source.GMP
open scoped Topology ENNReal

namespace EinsteinFull.Calculus

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


/-- The time cutoff preserves the selected weighted positive-power slice bound. -/
theorem b_positive_time_cutoff_slice_lintegral_bound {d : ℕ} {κ R a b ε p s t B : ℝ}
    (hκ : 0 < κ) (hε : 0 < ε) (hp : 0 < p) (hp1 : p < 1)
    (hs : s ∈ Set.Ioo a b) (ht : t ∈ Set.Ioo a b)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d) (hell : IsUniformlyElliptic κ ρ α)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hcal : IsWeightedCaloric ρ α (Set.Ioo a b) (sourceBall 0 R) u G)
    (hu : ∀ᵐ z ∂volume.restrict (Set.Ioo a b ×ˢ sourceBall 0 R), ε ≤ u z)
    (χ : Vec d → ℝ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχc : HasCompactSupport χ)
    (E : ℝ → ℝ)
    (hrep : ∀ᵐ q ∂volume.restrict (Set.Ioo a b),
      E q = ∫ x in sourceBall 0 R, ρ x * χ x ^ 2 * Real.rpow (u (q,x)) p)
    (hEbound : ∀ q ∈ Set.Ioo a b, q < t → E q ≤ B)
    (θ : ℝ → ℝ) (hθ0 : ∀ q, 0 ≤ θ q) (hθ1 : ∀ q, θ q ≤ 1) :
    ∀ᵐ q ∂volume.restrict (Set.Ioo s t),
      (∫⁻ x in sourceBall 0 R, ENNReal.ofReal (ρ x) *
        ‖(θ q * χ x) * Real.rpow (u (q,x)) (p / 2)‖ₑ ^ (2 : ℝ)) ≤ ENNReal.ofReal B := by
  have hsub : Set.Ioo s t ⊆ Set.Ioo a b := by
    intro q hq
    exact ⟨lt_trans hs.1 hq.1, lt_trans hq.2 ht.2⟩
  have hi := c13_positive_power_literal_mass_integrable hκ hε hp hp1 ρ α hell u G hcal hu χ hχ hχc
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict] at hi hu
  filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub hi.prod_right_ae,
    ae_restrict_of_ae_restrict_of_subset hsub (Measure.ae_ae_of_ae_prod hu),
    ae_restrict_of_ae_restrict_of_subset hsub hrep,
    ae_restrict_mem measurableSet_Ioo] with q hqi hqu hqrep hq
  have hqI := hsub hq
  have hn : ∀ᵐ x ∂volume.restrict (sourceBall (0 : Vec d) R),
      0 ≤ ρ x * χ x ^ 2 * Real.rpow (u (q,x)) p := by
    filter_upwards [hqu] with x hx
    exact mul_nonneg (mul_nonneg (hκ.le.trans (hell.2.2 x).1) (sq_nonneg _))
      (Real.rpow_nonneg (le_of_lt (lt_of_lt_of_le hε hx)) _)
  calc
    _ ≤ ∫⁻ x in sourceBall 0 R, ENNReal.ofReal
        (ρ x * χ x ^ 2 * Real.rpow (u (q,x)) p) := by
      apply lintegral_mono_ae
      filter_upwards [hqu] with x hx
      rw [Real.enorm_eq_ofReal_abs, ENNReal.rpow_two,
        ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs,
        ← ENNReal.ofReal_mul (hκ.le.trans (hell.2.2 x).1)]
      apply ENNReal.ofReal_le_ofReal
      have hpow : (Real.rpow (u (q,x)) (p/2)) ^ 2 = Real.rpow (u (q,x)) p := by
        change (u (q,x) ^ (p/2 : ℝ)) ^ (2 : ℕ) = u (q,x) ^ (p : ℝ)
        rw [← Real.rpow_mul_natCast (le_of_lt (lt_of_lt_of_le hε hx))]
        congr 1
        ring
      rw [mul_pow, mul_pow, hpow]
      have hθsq : (θ q)^2 ≤ 1 := by nlinarith [hθ0 q, hθ1 q, sq_nonneg (θ q)]
      have hc : 0 ≤ ρ x * χ x ^ 2 * Real.rpow (u (q,x)) p :=
        mul_nonneg (mul_nonneg (hκ.le.trans (hell.2.2 x).1) (sq_nonneg _))
          (Real.rpow_nonneg (le_of_lt (lt_of_lt_of_le hε hx)) _)
      have hh := mul_le_mul_of_nonneg_right hθsq hc
      nlinarith [hh]
    _ = ENNReal.ofReal (∫ x in sourceBall 0 R,
        ρ x * χ x ^ 2 * Real.rpow (u (q,x)) p) :=
      (ofReal_integral_eq_lintegral_ofReal hqi hn).symm
    _ ≤ _ := by rw [← hqrep]; exact ENNReal.ofReal_le_ofReal (hEbound q hqI hq.2)


/-- The normalized positive gain follows from the separate canonical-cutoff
slice-mass, energy-measurability, and coefficient-energy bounds. -/
theorem b_positive_normalized_nested_gain_of_cutoff_bounds
    (d : ℕ) (hd : 2 ≤ d) (κ : ℝ) (hκ : 0 < κ) (A m : ℝ) (hA : 1 ≤ A) (hm : 0 < m)
    (hslice : ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
      IsUniformlyElliptic κ ρ α → ∀ (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d),
      IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1) u G →
      (∀ᵐ z ∂volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1), 0 ≤ u z) →
      ∀ ε : ℝ, 0 < ε → ∀ σ' σ : ℝ, 1 / 2 ≤ σ' → σ' < σ → σ ≤ 1 →
      ∀ p : ℝ, 0 < p → p ≤ (d : ℝ) / (2 * ((d : ℝ) + 2)) →
      let η := sbxBPositiveCutoff d σ' σ
      let w : ℝ × Vec d → ℝ := fun z => u z + ε
      let v : ℝ × Vec d → ℝ := fun z => η z * (w z) ^ (p / 2)
      ∀ᵐ t ∂volume.restrict (Set.Ioo (-1 : ℝ) 1),
        (∫⁻ x in sourceBall (0 : Vec d) 1, ENNReal.ofReal (ρ x) * ‖v (t,x)‖ₑ ^ (2 : ℝ)) ≤
          ENNReal.ofReal (A * (σ - σ') ^ (-m)) *
            ∫⁻ z in sbxBPositiveCylinder d σ, ENNReal.ofReal (w z) ^ p)
    (hmeas : ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
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
        (volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1)))
    (henergy : ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
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
      (∫⁻ z in Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall (0 : Vec d) 1,
        ENNReal.ofReal (dot ((α z.2).mulVec (J z)) (J z))) ≤
          ENNReal.ofReal (A * (σ - σ') ^ (-m)) *
            ∫⁻ z in sbxBPositiveCylinder d σ, ENNReal.ofReal (w z) ^ p) :
    ∃ A' : ℝ, 1 ≤ A' ∧ ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
      IsUniformlyElliptic κ ρ α → ∀ (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d),
      IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1) u G →
      (∀ᵐ z ∂volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1), 0 ≤ u z) →
      ∀ ε : ℝ, 0 < ε → ∀ σ' σ : ℝ, 1 / 2 ≤ σ' → σ' < σ → σ ≤ 1 →
      ∀ p : ℝ, 0 < p → p ≤ (d : ℝ) / (2 * ((d : ℝ) + 2)) →
      eLpNorm (fun z : Vec d × ℝ => u (z.2, z.1) + ε)
        (ENNReal.ofReal ((((d : ℝ) + 2) / d) * p))
        ((PDE.Parabolic.WeakHarnack.cylMeasure (PDE.Parabolic.WeakHarnack.posCyl d 1)).restrict
          (PDE.Parabolic.WeakHarnack.posCyl d σ')) ≤
      ENNReal.ofReal ((A' * (σ - σ') ^ (-m)) ^ (1 / p)) *
      eLpNorm (fun z : Vec d × ℝ => u (z.2, z.1) + ε) (ENNReal.ofReal p)
        ((PDE.Parabolic.WeakHarnack.cylMeasure (PDE.Parabolic.WeakHarnack.posCyl d 1)).restrict
          (PDE.Parabolic.WeakHarnack.posCyl d σ)) := by
  obtain ⟨B, hB, hgain⟩ := sbxB_positive_nested_gain d hd κ hκ
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hχ : 1 < ((d : ℝ) + 2) / d := by
    apply (lt_div_iff₀ hd0).2
    linarith
  have hq : 0 < (d : ℝ) / (2 * ((d : ℝ) + 2)) := by positivity
  have hBA : 1 ≤ B * A := one_le_mul_of_one_le_of_one_le hB hA
  apply sbxB_positive_nested_gain_normalize d κ (((d : ℝ) + 2) / d)
    (B * A) m ((d : ℝ) / (2 * ((d : ℝ) + 2))) hχ hBA hm hq
  intro ρ α hell u G hcal hu ε hε σ' σ hσ' hσσ hσ p hp hpq
  have hh := hgain A hA m ρ α hell u G hcal hu ε hε σ' σ hσ' hσσ hσ p hp hpq
    (hslice ρ α hell u G hcal hu ε hε σ' σ hσ' hσσ hσ p hp hpq)
    (hmeas ρ α hell u G hcal hu ε hε σ' σ hσ' hσσ hσ p hp hpq)
    (henergy ρ α hell u G hcal hu ε hε σ' σ hσ' hσσ hσ p hp hpq)
  simpa only [sbxBPositiveCylinder, mul_comm p (((d : ℝ) + 2) / d)] using hh

#print axioms b_positive_power_selected_traces_uniform
#print axioms b_positive_power_trace_chain_energy_gap
#print axioms b_positive_power_trace_chain_energy_uniform
#print axioms b_positive_concentric_selected_traces_uniform
#print axioms b_positive_normalized_nested_gain_of_cutoff_bounds

/-- Conditional weak Harnack estimate from canonical cutoff bounds and a local backward gain. -/
theorem b_native_unit_weak_harnack_of_local_cutoff_bounds (d : ℕ) (hd : 2 ≤ d) (κ : ℝ) (hκ : 0 < κ)
    (A m : ℝ) (hA : 1 ≤ A) (hm : 0 < m)
    (C₀ : ℝ) (hC₀ : 1 ≤ C₀)
    (hslice : ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
      IsUniformlyElliptic κ ρ α → ∀ (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d),
      IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1) u G →
      (∀ᵐ z ∂volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1), 0 ≤ u z) →
      ∀ ε : ℝ, 0 < ε → ∀ σ' σ : ℝ, 1 / 2 ≤ σ' → σ' < σ → σ ≤ 1 →
      ∀ p : ℝ, 0 < p → p ≤ (d : ℝ) / (2 * ((d : ℝ) + 2)) →
      let η := sbxBPositiveCutoff d σ' σ
      let w : ℝ × Vec d → ℝ := fun z => u z + ε
      let v : ℝ × Vec d → ℝ := fun z => η z * (w z) ^ (p / 2)
      ∀ᵐ t ∂volume.restrict (Set.Ioo (-1 : ℝ) 1),
        (∫⁻ x in sourceBall (0 : Vec d) 1, ENNReal.ofReal (ρ x) * ‖v (t,x)‖ₑ ^ (2 : ℝ)) ≤
          ENNReal.ofReal (A * (σ - σ') ^ (-m)) *
            ∫⁻ z in sbxBPositiveCylinder d σ, ENNReal.ofReal (w z) ^ p)
    (hmeas : ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
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
        (volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1)))
    (henergy : ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
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
      (∫⁻ z in Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall (0 : Vec d) 1,
        ENNReal.ofReal (dot ((α z.2).mulVec (J z)) (J z))) ≤
          ENNReal.ofReal (A * (σ - σ') ^ (-m)) *
            ∫⁻ z in sbxBPositiveCylinder d σ, ENNReal.ofReal (w z) ^ p)
    (hback : ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d), IsUniformlyElliptic κ ρ α →
    ∀ (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d),
    IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1) u G →
    (∀ᵐ z ∂volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1), 0 ≤ u z) →
    ∀ (ε p : ℝ), 0 < ε → 0 < p → ∀ (x : ℝ × Vec d) (r : ℝ), 0 < r →
    (∀ z ∈ sbxBBackPiece x r,
      (z.1 + 3 / 4, z.2) ∈ Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall (0 : Vec d) 1) →
    eLpNorm (fun z => 1 / max ε (u (z.1 + 3 / 4, z.2) + ε))
        (ENNReal.ofReal ((((d : ℝ) + 2) / d) * p))
        (volume.restrict (sbxBBackHalfPiece x r)) ≤
      ENNReal.ofReal ((C₀ * (1 + p) ^ (2 : ℝ) * r ^ (-2 : ℝ)) ^ (1 / p)) *
        eLpNorm (fun z => 1 / max ε (u (z.1 + 3 / 4, z.2) + ε))
          (ENNReal.ofReal p) (volume.restrict (sbxBBackPiece x r))) :
    ∃ p C : ℝ, 0 < p ∧ 0 < C ∧ ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
      IsUniformlyElliptic κ ρ α → ∀ (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d),
        IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1) u G →
        (∀ᵐ z ∂volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1), 0 ≤ u z) →
        eLpNorm u (ENNReal.ofReal p)
          (volume.restrict (Set.Ioo (-3/4 : ℝ) (-1/2) ×ˢ sourceBall 0 (1/2))) ≤
        ENNReal.ofReal C * essInf (fun z : ℝ × Vec d => ENNReal.ofReal (u z))
          (volume.restrict (Set.Ioo (1/2 : ℝ) (3/4) ×ˢ sourceBall 0 (1/2))) := by
  obtain ⟨A₁, hA₁, hpos⟩ := b_positive_normalized_nested_gain_of_cutoff_bounds
    d hd κ hκ A m hA hm hslice hmeas henergy
  obtain ⟨A₂, β₂, m₂, A₃, β₃, m₃, hA₂, hβ₂, hm₂, hA₃, hβ₃, hm₃, hneg, hinner⟩ :=
    sbxB_both_shifted_negative_normalized_gains_of_local d hd κ C₀ hC₀ hback
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hχ : 1 < ((d : ℝ) + 2) / d := by
    apply (lt_div_iff₀ hd0).2
    linarith
  have hq : 0 < (d : ℝ) / (2 * ((d : ℝ) + 2)) := by positivity
  have hqχ : ((d : ℝ) / (2 * ((d : ℝ) + 2))) * (((d : ℝ) + 2) / d) ≤ 2 := by
    have heq : ((d : ℝ) / (2 * ((d : ℝ) + 2))) * (((d : ℝ) + 2) / d) = 1 / 2 := by
      field_simp
    linarith
  exact c8_native_unit_weak_harnack_of_field_nested_gains d hd κ hκ
    (χ := ((d : ℝ) + 2) / d) (q := (d : ℝ) / (2 * ((d : ℝ) + 2)))
    (A₁ := A₁) (m₁ := m) (A₂ := A₂) (β₂ := β₂) (m₂ := m₂)
    (A₃ := A₃) (β₃ := β₃) (m₃ := m₃)
    hχ hA₁ hm hq hA₂ hβ₂ hm₂ hA₃ hβ₃ hm₃ hqχ hpos hneg hinner

#print axioms b_native_unit_weak_harnack_of_local_cutoff_bounds

/-- The native weak Harnack estimate follows from the three positive cutoff bounds. -/
theorem b_native_unit_weak_harnack_of_positive_cutoff_bounds (d : ℕ) (hd : 2 ≤ d) (κ : ℝ) (hκ : 0 < κ)
    (A m : ℝ) (hA : 1 ≤ A) (hm : 0 < m)
    (hslice : ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
      IsUniformlyElliptic κ ρ α → ∀ (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d),
      IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1) u G →
      (∀ᵐ z ∂volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1), 0 ≤ u z) →
      ∀ ε : ℝ, 0 < ε → ∀ σ' σ : ℝ, 1 / 2 ≤ σ' → σ' < σ → σ ≤ 1 →
      ∀ p : ℝ, 0 < p → p ≤ (d : ℝ) / (2 * ((d : ℝ) + 2)) →
      let η := sbxBPositiveCutoff d σ' σ
      let w : ℝ × Vec d → ℝ := fun z => u z + ε
      let v : ℝ × Vec d → ℝ := fun z => η z * (w z) ^ (p / 2)
      ∀ᵐ t ∂volume.restrict (Set.Ioo (-1 : ℝ) 1),
        (∫⁻ x in sourceBall (0 : Vec d) 1, ENNReal.ofReal (ρ x) * ‖v (t,x)‖ₑ ^ (2 : ℝ)) ≤
          ENNReal.ofReal (A * (σ - σ') ^ (-m)) *
            ∫⁻ z in sbxBPositiveCylinder d σ, ENNReal.ofReal (w z) ^ p)
    (hmeas : ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
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
        (volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1)))
    (henergy : ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
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
      (∫⁻ z in Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall (0 : Vec d) 1,
        ENNReal.ofReal (dot ((α z.2).mulVec (J z)) (J z))) ≤
          ENNReal.ofReal (A * (σ - σ') ^ (-m)) *
            ∫⁻ z in sbxBPositiveCylinder d σ, ENNReal.ofReal (w z) ^ p)
 :
    ∃ p C : ℝ, 0 < p ∧ 0 < C ∧ ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
      IsUniformlyElliptic κ ρ α → ∀ (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d),
        IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1) u G →
        (∀ᵐ z ∂volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1), 0 ≤ u z) →
        eLpNorm u (ENNReal.ofReal p)
          (volume.restrict (Set.Ioo (-3/4 : ℝ) (-1/2) ×ˢ sourceBall 0 (1/2))) ≤
        ENNReal.ofReal C * essInf (fun z : ℝ × Vec d => ENNReal.ofReal (u z))
          (volume.restrict (Set.Ioo (1/2 : ℝ) (3/4) ×ˢ sourceBall 0 (1/2))) := by
  obtain ⟨C, hC, hback⟩ := b_translated_backward_local_gain d hd κ hκ
  have hback' : sbxBTranslatedBackwardLocalGain d κ (max 1 C) :=
    sbxB_translated_backward_local_gain_mono d κ C (max 1 C) hC.le
      (le_max_right 1 C) hback
  exact b_native_unit_weak_harnack_of_local_cutoff_bounds d hd κ hκ A m hA hm
    (max 1 C) (le_max_left 1 C) hslice hmeas henergy hback'

#print axioms b_native_unit_weak_harnack_of_positive_cutoff_bounds

private theorem b_positive_gap_absorb {C A m M g : ℝ}
    (hC : 0 ≤ C) (hCA : C ≤ A) (hmM : m ≤ M) (hg : 0 < g) (hg1 : g ≤ 1) :
    C * g ^ (-m) ≤ A * g ^ (-M) := by
  have hp := Real.rpow_le_rpow_of_exponent_ge hg hg1 (neg_le_neg hmM)
  exact (mul_le_mul_of_nonneg_left hp hC).trans
    (mul_le_mul_of_nonneg_right hCA (Real.rpow_nonneg hg.le _))

/-- Nonnegative weighted caloric fields satisfy the native unit weak Harnack estimate. -/
theorem b_native_unit_weak_harnack
    (d : ℕ) (hd : 2 ≤ d) (κ : ℝ) (hκ : 0 < κ) :
    ∃ p C : ℝ, 0 < p ∧ 0 < C ∧ ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
      IsUniformlyElliptic κ ρ α → ∀ (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d),
        IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1) u G →
        (∀ᵐ z ∂volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1), 0 ≤ u z) →
        eLpNorm u (ENNReal.ofReal p)
          (volume.restrict (Set.Ioo (-3/4 : ℝ) (-1/2) ×ˢ sourceBall 0 (1/2))) ≤
        ENNReal.ofReal C * essInf (fun z : ℝ × Vec d => ENNReal.ofReal (u z))
          (volume.restrict (Set.Ioo (1/2 : ℝ) (3/4) ×ˢ sourceBall 0 (1/2))) := by
  obtain ⟨Cs, ms, hCs, hms, htrace⟩ := b_positive_nested_slice_trace d hd κ hκ
  obtain ⟨Ce, hCe, hcoeff⟩ := b_positive_actual_coefficient_energy d κ hκ
  let A : ℝ := max 1 (max Cs Ce)
  let m : ℝ := max ms 2
  have hA : 1 ≤ A := le_max_left _ _
  have hCsA : Cs ≤ A := le_trans (le_max_left _ _) (le_max_right _ _)
  have hCeA : Ce ≤ A := le_trans (le_max_right _ _) (le_max_right _ _)
  have hm : 0 < m := lt_of_lt_of_le hms (le_max_left _ _)
  have hslice : ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
      IsUniformlyElliptic κ ρ α → ∀ (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d),
      IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1) u G →
      (∀ᵐ z ∂volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1), 0 ≤ u z) →
      ∀ ε : ℝ, 0 < ε → ∀ σ' σ : ℝ, 1 / 2 ≤ σ' → σ' < σ → σ ≤ 1 →
      ∀ p : ℝ, 0 < p → p ≤ (d : ℝ) / (2 * ((d : ℝ) + 2)) →
      let η := sbxBPositiveCutoff d σ' σ
      let w : ℝ × Vec d → ℝ := fun z => u z + ε
      let v : ℝ × Vec d → ℝ := fun z => η z * (w z) ^ (p / 2)
      ∀ᵐ t ∂volume.restrict (Set.Ioo (-1 : ℝ) 1),
        (∫⁻ x in sourceBall (0 : Vec d) 1, ENNReal.ofReal (ρ x) * ‖v (t,x)‖ₑ ^ (2 : ℝ)) ≤
          ENNReal.ofReal (A * (σ - σ') ^ (-m)) *
            ∫⁻ z in sbxBPositiveCylinder d σ, ENNReal.ofReal (w z) ^ p := by
    intro ρ α hell u G hcal hu ε hε σ' σ hσ' hσσ hσ p hp hpq
    have hg : 0 < σ - σ' := sub_pos.mpr hσσ
    have hg1 : σ - σ' ≤ 1 := by linarith
    have hcoeff := b_positive_gap_absorb hCs.le hCsA (le_max_left ms 2) hg hg1
    have hcut := sbxB_positive_cutoff_admissible d σ' σ hσ' hσσ hσ
    have hp1 : p < 1 := lt_trans (c5_positive_gain_exponent_lt_half d hd p hpq) (by norm_num)
    have ht := htrace σ' σ hσ' hσσ hσ ρ α hell u G hcal hu ε p hε hp hpq
    have ht' := b_positive_slice_lintegral hκ hε hp hp1
      (show 0 ≤ Cs * (σ - σ') ^ (-ms) by positivity)
      ρ α hell u G hcal hu (sbxBPositiveCutoff d σ' σ) hcut.1 hcut.2.1
      (sbxBPositiveCylinder d σ)
      (sbxB_positive_cylinder_subset d σ (le_trans hσ' hσσ.le) hσ) ht
    filter_upwards [ht'] with t ht
    exact ht.trans (mul_le_mul_left (ENNReal.ofReal_le_ofReal hcoeff) _)
  have hmeas : ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
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
        (volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1)) := by
    intro ρ α hell u G hcal hu ε hε σ' σ hσ' hσσ hσ p hp hpq
    exact (hcoeff ρ α hell u G hcal hu ε hε σ' σ hσ' hσσ hσ p hp hpq).1
  have hE : ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
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
      (∫⁻ z in Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall (0 : Vec d) 1,
        ENNReal.ofReal (dot ((α z.2).mulVec (J z)) (J z))) ≤
          ENNReal.ofReal (A * (σ - σ') ^ (-m)) *
            ∫⁻ z in sbxBPositiveCylinder d σ, ENNReal.ofReal (w z) ^ p := by
    intro ρ α hell u G hcal hu ε hε σ' σ hσ' hσσ hσ p hp hpq
    have hg : 0 < σ - σ' := sub_pos.mpr hσσ
    have hg1 : σ - σ' ≤ 1 := by linarith
    have hc := b_positive_gap_absorb (le_trans zero_le_one hCe) hCeA
      (le_max_right ms 2) hg hg1
    have he := (hcoeff ρ α hell u G hcal hu ε hε σ' σ hσ' hσσ hσ p hp hpq).2
    exact he.trans (mul_le_mul_left (ENNReal.ofReal_le_ofReal hc) _)
  exact b_native_unit_weak_harnack_of_positive_cutoff_bounds d hd κ hκ A m hA hm
    hslice hmeas hE


#print axioms b_native_unit_weak_harnack

end EinsteinFull.Calculus
