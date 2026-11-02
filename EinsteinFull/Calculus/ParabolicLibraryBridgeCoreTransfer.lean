import EinsteinFull.Calculus.ParabolicLibraryBridgeOscHolder
import EinsteinFull.Calculus.ParabolicLibraryBridgeSignedMaxL2

/-!
# Transfer lemmas between the unit cylinder and `B(c, ρ) × (T₀ - ρ², T₀]`
-/

open scoped ENNReal

noncomputable section
namespace EinsteinFull.ParabolicBridge

open MeasureTheory Set Filter PDE PDE.Parabolic.Rescale

variable {d : ℕ}

theorem timeMap_image_Ioo' (T₀ : ℝ) {r : ℝ} (hr : 0 < r) (b : ℝ) :
    timeMap T₀ r '' Ioo b 0 = Ioo (T₀ + r ^ 2 * b) T₀ := by
  have hr2 : 0 < r ^ 2 := pow_pos hr 2
  ext t
  constructor
  · rintro ⟨s, ⟨h1, h2⟩, rfl⟩
    rw [timeMap_apply]
    constructor
    · have := mul_lt_mul_of_pos_left h1 hr2
      linarith only [this]
    · have := mul_neg_of_pos_of_neg hr2 h2
      linarith only [this]
  · rintro ⟨h1, h2⟩
    refine ⟨(t - T₀) / r ^ 2, ⟨?_, ?_⟩, ?_⟩
    · rw [lt_div_iff₀ hr2]; linarith only [h1]
    · exact div_neg_of_neg_of_pos (by linarith only [h2]) hr2
    · rw [timeMap_apply]; field_simp; ring

/-- The image of the top-time Moser region under the parabolic rescaling. -/
theorem cylMap_image_moserRegion (c : Vec d) {ρ : ℝ} (hρ : 0 < ρ) (T₀ : ℝ) :
    cylMap c ρ T₀ '' SignedLocalMax.moserCylZ d (3 / 8) (-11 / 16) =
      euclideanBall c (ρ * (3 / 8)) ×ˢ Ioo (T₀ + ρ ^ 2 * (-11 / 16)) T₀ := by
  unfold SignedLocalMax.moserCylZ
  rw [cylMap_image_prod, spaceMap_image_euclideanBall c 0 hρ (3 / 8), timeMap_image_Ioo' T₀ hρ]
  have e1 : spaceMap c ρ 0 = c := by simp [spaceMap_apply]
  rw [e1]

/-- Change of variables for the `L²` integral. -/
theorem lintegral_comp_cylMap_unit (c : Vec d) {ρ : ℝ} (hρ : 0 < ρ) (T₀ : ℝ) (f : Vec d × ℝ → ℝ) :
    ∫⁻ z in euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0,
        ENNReal.ofReal |f (cylMap c ρ T₀ z)| ^ (2 : ℝ) =
      ENNReal.ofReal ((ρ ^ (d + 2))⁻¹) *
        ∫⁻ y in euclideanBall c ρ ×ˢ Ioc (T₀ - ρ ^ 2) T₀, ENNReal.ofReal |f y| ^ (2 : ℝ) := by
  have hF := cylMap_measurableEmbedding c hρ T₀
  have hmap := map_restrict_unitCylinder c hρ T₀
  have h := hF.lintegral_map (μ := volume.restrict (euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0))
    (fun y : Vec d × ℝ => ENNReal.ofReal |f y| ^ (2 : ℝ))
  rw [hmap, lintegral_smul_measure] at h
  exact h.symm

end EinsteinFull.ParabolicBridge
