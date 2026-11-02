import EinsteinFull.Calculus.ParabolicLibraryBridgeOscReduce
import EllipticRegularity.Parabolic.Rescale.Affine
import EllipticRegularity.Parabolic.Rescale.AffineEnergy

/-!
# Oscillation reduction on parabolic cylinders of arbitrary center, time and radius
-/

open scoped ENNReal

noncomputable section
namespace EinsteinFull.ParabolicBridge

open MeasureTheory Set Filter PDE PDE.Parabolic.Rescale

theorem ae_of_comp_of_map_eq_smul' {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {F : α → β} {μ : Measure α} {ν : Measure β} {k : ℝ≥0∞} (hF : MeasurableEmbedding F)
    (hk : k ≠ 0) (h : μ.map F = k • ν) {P : β → Prop} (hP : ∀ᵐ x ∂μ, P (F x)) :
    ∀ᵐ y ∂ν, P y := by
  have h1 : ∀ᵐ y ∂(μ.map F), P y := hF.ae_map_iff.mpr hP
  rw [h] at h1
  have hac : ν ≪ k • ν := fun s hs => by
    rw [Measure.smul_apply, smul_eq_mul, mul_eq_zero] at hs
    exact hs.resolve_left hk
  exact hac.ae_le h1

theorem timeMap_image_Ioc' (T₀ : ℝ) {r : ℝ} (hr : 0 < r) (b : ℝ) :
    timeMap T₀ r '' Ioc b 0 = Ioc (T₀ + r ^ 2 * b) T₀ := by
  have hr2 : 0 < r ^ 2 := pow_pos hr 2
  ext t
  constructor
  · rintro ⟨s, ⟨h1, h2⟩, rfl⟩
    rw [timeMap_apply]
    constructor
    · have := mul_lt_mul_of_pos_left h1 hr2
      linarith only [this]
    · have := mul_nonpos_of_nonneg_of_nonpos hr2.le h2
      linarith only [this]
  · rintro ⟨h1, h2⟩
    refine ⟨(t - T₀) / r ^ 2, ⟨?_, ?_⟩, ?_⟩
    · rw [lt_div_iff₀ hr2]; linarith only [h1]
    · exact div_nonpos_of_nonpos_of_nonneg (by linarith only [h2]) hr2.le
    · rw [timeMap_apply]; field_simp; ring

variable {d : ℕ}

theorem cylMap_image_halfCylinder (c : Vec d) {ρ : ℝ} (hρ : 0 < ρ) (T₀ : ℝ) :
    cylMap c ρ T₀ '' (euclideanBall (0 : Vec d) (1 / 2) ×ˢ Ioc (-1 / 4 : ℝ) 0) =
      euclideanBall c (ρ / 2) ×ˢ Ioc (T₀ - (ρ / 2) ^ 2) T₀ := by
  rw [cylMap_image_prod, spaceMap_image_euclideanBall c 0 hρ (1 / 2), timeMap_image_Ioc' T₀ hρ]
  have e1 : spaceMap c ρ 0 = c := by simp [spaceMap_apply]
  have e2 : ρ * (1 / 2) = ρ / 2 := by ring
  have e3 : T₀ + ρ ^ 2 * (-1 / 4) = T₀ - (ρ / 2) ^ 2 := by ring
  rw [e1, e2, e3]

/-- One step of oscillation reduction on `B(c,ρ) × (T₀ - ρ², T₀]`. -/
theorem osc_reduction_scaled (d : ℕ) (hd : 0 < d) (Lam : ℝ) (hLam : 1 ≤ Lam) :
    ∃ η : ℝ, 0 < η ∧ η ≤ 1 / 2 ∧ ∀ (a : ParCoeffField d) (c : Vec d) (T₀ ρ : ℝ), 0 < ρ →
      ∀ {I' : Set ℝ}, MeasurableSet I' → Ioc (T₀ - ρ ^ 2) T₀ ⊆ I' →
      IsParabolicCoeff 1 Lam a (euclideanBall c ρ) I' →
      ∀ u : ParH1Function (euclideanBall c ρ) I',
      IsParabolicWeakSolution a (euclideanBall c ρ) I' u →
      ∀ m M : ℝ, m ≤ M →
      (∀ᵐ z ∂(volume.restrict (euclideanBall c ρ ×ˢ Ioc (T₀ - ρ ^ 2) T₀)),
        m ≤ u.toFun z ∧ u.toFun z ≤ M) →
      ∃ m' M' : ℝ,
        (∀ᵐ z ∂(volume.restrict (euclideanBall c (ρ / 2) ×ˢ Ioc (T₀ - (ρ / 2) ^ 2) T₀)),
          m' ≤ u.toFun z ∧ u.toFun z ≤ M') ∧ m ≤ m' ∧ M' ≤ M ∧ m' ≤ M' ∧
          M' - m' ≤ (1 - η) * (M - m) := by
  obtain ⟨η, hη, hη2, hred⟩ := osc_reduction d hd Lam hLam
  refine ⟨η, hη, hη2, ?_⟩
  intro a c T₀ ρ hρ I' hI'meas hI' ha u hu m M hmM hbd
  obtain ⟨a', ũ, ha', hũ, hval, -⟩ :=
    exists_unit_rescaling a c hρ T₀ hI'meas hI' ha u hu
  have hF := cylMap_measurableEmbedding c hρ T₀
  have hmap := map_restrict_unitCylinder c hρ T₀
  have hk0 : ENNReal.ofReal ((ρ ^ (d + 2))⁻¹) ≠ 0 := ofReal_inv_pow_ne_zero hρ (d + 2)
  have hbd' : ∀ᵐ z ∂(volume.restrict (euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0)),
      m ≤ ũ.toFun z ∧ ũ.toFun z ≤ M := by
    have h := ae_comp_of_map_eq_smul hF hmap (P := fun w => m ≤ u.toFun w ∧ u.toFun w ≤ M) hbd
    filter_upwards [h] with z hz
    have e : ũ.toFun z = u.toFun (cylMap c ρ T₀ z) := by
      obtain ⟨y, s⟩ := z
      exact hval y s
    rw [e]
    exact hz
  obtain ⟨m', M', hae, h1, h2, h4, h3⟩ := hred a' ha' ũ hũ m M hmM hbd'
  refine ⟨m', M', ?_, h1, h2, h4, h3⟩
  have hmapS := map_restrict_cylMap c hρ T₀
    (euclideanBall (0 : Vec d) (1 / 2) ×ˢ Ioc (-1 / 4 : ℝ) 0)
  rw [cylMap_image_halfCylinder c hρ T₀] at hmapS
  refine ae_of_comp_of_map_eq_smul' hF hk0 hmapS ?_
  filter_upwards [hae] with z hz
  have e : ũ.toFun z = u.toFun (cylMap c ρ T₀ z) := by
    obtain ⟨y, s⟩ := z
    exact hval y s
  rw [← e]
  exact hz

end EinsteinFull.ParabolicBridge
