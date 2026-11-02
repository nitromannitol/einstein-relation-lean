import EllipticRegularity.Parabolic.ParabolicDef
import Mathlib.MeasureTheory.Integral.Average

/-!
# Time rescaling and carrier swap

`Tm τ K (y, s) = (τ + K s, y)` swaps the carrier from `Vec d × ℝ` to `ℝ × Vec d` and rescales time
by `K`.  It is a measurable equivalence pushing Lebesgue measure to `K⁻¹` times Lebesgue measure.
-/

open scoped ENNReal

noncomputable section
namespace EinsteinFull.ParabolicBridge

open MeasureTheory Set PDE

variable {d : ℕ}

/-- Time rescaling combined with the carrier swap. -/
def Tm (τ K : ℝ) (z : Vec d × ℝ) : ℝ × Vec d := (τ + K * z.2, z.1)

theorem Tm_measurable (τ K : ℝ) : Measurable (Tm (d := d) τ K) :=
  (measurable_const.add (measurable_const.mul measurable_snd)).prodMk measurable_fst

/-- The measurable equivalence underlying `Tm`. -/
def TmE (τ K : ℝ) (hK : 0 < K) : Vec d × ℝ ≃ᵐ ℝ × Vec d where
  toFun := Tm τ K
  invFun := fun p => (p.2, (p.1 - τ) / K)
  left_inv := fun z => Prod.ext rfl (by
    simp only [Tm]
    first | (field_simp; ring) | field_simp)
  right_inv := fun p => Prod.ext (by
    simp only [Tm]
    first | (field_simp; ring) | field_simp) rfl
  measurable_toFun := Tm_measurable τ K
  measurable_invFun := measurable_snd.prodMk ((measurable_fst.sub_const τ).div_const K)

theorem TmE_apply (τ K : ℝ) (hK : 0 < K) (z : Vec d × ℝ) : TmE τ K hK z = Tm τ K z := rfl

theorem map_aff_volume (τ K : ℝ) (hK : 0 < K) :
    Measure.map (fun s : ℝ => τ + K * s) volume = ENNReal.ofReal K⁻¹ • (volume : Measure ℝ) := by
  have h : (fun s : ℝ => τ + K * s) = (fun x : ℝ => τ + x) ∘ (fun s : ℝ => K * s) := rfl
  rw [h, ← Measure.map_map (measurable_const_add τ) (measurable_const_mul K),
    Real.map_volume_mul_left hK.ne', Measure.map_smul, map_add_left_eq_self,
    abs_of_pos (inv_pos.mpr hK)]
  all_goals exact (measurable_const_add τ).aemeasurable

theorem volume_map_Tm (τ K : ℝ) (hK : 0 < K) :
    Measure.map (Tm (d := d) τ K) volume = ENNReal.ofReal K⁻¹ • (volume : Measure (ℝ × Vec d)) := by
  have hT : Tm (d := d) τ K =
      Prod.swap ∘ Prod.map (id : Vec d → Vec d) (fun s : ℝ => τ + K * s) := by
    funext z
    rfl
  have haff : Measurable fun s : ℝ => τ + K * s :=
    measurable_const.add (measurable_const.mul measurable_id)
  rw [hT, ← Measure.map_map measurable_swap (measurable_id.prodMap haff), Measure.volume_eq_prod,
    ← Measure.map_prod_map _ _ measurable_id haff, Measure.map_id, map_aff_volume τ K hK,
    Measure.prod_smul_right, Measure.map_smul, Measure.prod_swap, Measure.volume_eq_prod]
  all_goals exact measurable_swap.aemeasurable

/-- Change of variables for set integrals. -/
theorem setIntegral_Tm (τ K : ℝ) (hK : 0 < K) (F : ℝ × Vec d → ℝ) (S : Set (ℝ × Vec d)) :
    ∫ z in S, F z = K * ∫ z in Tm τ K ⁻¹' S, F (Tm τ K z) := by
  have h := (TmE (d := d) τ K hK).measurableEmbedding.setIntegral_map (μ := volume) F S
  simp only [TmE_apply] at h
  have h' : ∫ z in S, F z ∂(Measure.map (TmE (d := d) τ K hK) volume) =
      ∫ z in S, F z ∂(ENNReal.ofReal K⁻¹ • (volume : Measure (ℝ × Vec d))) := by
    have : Measure.map (TmE (d := d) τ K hK) volume = Measure.map (Tm τ K) volume := rfl
    rw [this, volume_map_Tm τ K hK]
  rw [h', Measure.restrict_smul, integral_smul_measure, ENNReal.toReal_ofReal (inv_pos.mpr hK).le,
    smul_eq_mul] at h
  have h2 : Tm τ K ⁻¹' S = (TmE (d := d) τ K hK) ⁻¹' S := rfl
  rw [h2, ← h]
  field_simp

/-- Volume of the preimage. -/
theorem volume_Tm_preimage (τ K : ℝ) (hK : 0 < K) {S : Set (ℝ × Vec d)} (hS : MeasurableSet S) :
    volume (Tm τ K ⁻¹' S) = ENNReal.ofReal K⁻¹ * volume S := by
  have h := (TmE (d := d) τ K hK).measurableEmbedding.map_apply (μ := volume) S
  have h' : Measure.map (TmE (d := d) τ K hK) volume = ENNReal.ofReal K⁻¹ • volume := by
    have : Measure.map (TmE (d := d) τ K hK) volume = Measure.map (Tm τ K) volume := rfl
    rw [this, volume_map_Tm τ K hK]
  rw [h'] at h
  have h2 : Tm τ K ⁻¹' S = (TmE (d := d) τ K hK) ⁻¹' S := rfl
  rw [h2]
  simpa using h.symm

/-- Averages are invariant under the rescaling. -/
theorem setAverage_Tm (τ K : ℝ) (hK : 0 < K) (F : ℝ × Vec d → ℝ) {S : Set (ℝ × Vec d)}
    (hS : MeasurableSet S) :
    ⨍ z in S, F z = ⨍ z in Tm τ K ⁻¹' S, F (Tm τ K z) := by
  rw [setAverage_eq, setAverage_eq, setIntegral_Tm τ K hK F S]
  have hv : volume.real (Tm τ K ⁻¹' S) = K⁻¹ * volume.real S := by
    unfold Measure.real
    rw [volume_Tm_preimage τ K hK hS, ENNReal.toReal_mul, ENNReal.toReal_ofReal (inv_pos.mpr hK).le]
  rw [hv, smul_eq_mul, smul_eq_mul]
  by_cases h0 : volume.real S = 0
  · simp [h0]
  · field_simp

/-- Preimage of a parabolic cylinder. -/
theorem Tm_preimage_cyl (τ K : ℝ) (hK : 0 < K) (ρ : ℝ) (B : Set (Vec d)) :
    Tm τ K ⁻¹' (Ioo (τ - ρ ^ 2) τ ×ˢ B) = B ×ˢ Ioo (-ρ ^ 2 / K) 0 := by
  ext ⟨y, s⟩
  simp only [Tm, mem_preimage, mem_prod, mem_Ioo]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨h3, ?_, ?_⟩
    · rw [div_lt_iff₀ hK]; nlinarith
    · by_contra h
      push_neg at h
      nlinarith
  · rintro ⟨h3, h1, h2⟩
    refine ⟨⟨?_, ?_⟩, h3⟩
    · rw [div_lt_iff₀ hK] at h1; nlinarith
    · nlinarith

end EinsteinFull.ParabolicBridge
