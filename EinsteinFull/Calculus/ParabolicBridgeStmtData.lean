import EinsteinFull.Calculus.ParabolicBridgeScale
import EinsteinFull.Calculus.ParabolicBridgeMolData

/-!
# From the distributional hypotheses of the statement to `MolData`

The statement is on `ℝ × Vec d` (time first) with the time-independent coefficient `ω.1`; the
bridge uses the carrier `Vec d × ℝ` after the rescaling `Tm τ K`.
-/

open scoped ENNReal

noncomputable section
namespace EinsteinFull.ParabolicBridge

open MeasureTheory Set Filter Topology PDE

variable {d : ℕ}

/-- Inverse of `Tm`. -/
def TmInv (τ K : ℝ) (p : ℝ × Vec d) : Vec d × ℝ := (p.2, (p.1 - τ) * K⁻¹)

theorem TmInv_Tm (τ K : ℝ) (hK : 0 < K) (z : Vec d × ℝ) : TmInv τ K (Tm τ K z) = z :=
  Prod.ext rfl (by
    simp only [TmInv, Tm]
    first | (field_simp; ring) | field_simp)

theorem Tm_TmInv (τ K : ℝ) (hK : 0 < K) (p : ℝ × Vec d) : Tm τ K (TmInv τ K p) = p :=
  Prod.ext (by
    simp only [TmInv, Tm]
    first | (field_simp; ring) | field_simp) rfl

theorem TmInv_contDiff (τ K : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (TmInv (d := d) τ K) :=
  contDiff_snd.prodMk ((contDiff_fst.sub contDiff_const).mul contDiff_const)

theorem Tm_continuous (τ K : ℝ) : Continuous (Tm (d := d) τ K) :=
  (continuous_const.add (continuous_const.mul continuous_snd)).prodMk continuous_fst

theorem TmInv_hasFDerivAt (τ K : ℝ) (p : ℝ × Vec d) :
    HasFDerivAt (TmInv (d := d) τ K)
      ((ContinuousLinearMap.snd ℝ ℝ (Vec d)).prod
        (K⁻¹ • ContinuousLinearMap.fst ℝ ℝ (Vec d))) p :=
  (hasFDerivAt_snd).prodMk (((hasFDerivAt_fst).sub_const τ).mul_const K⁻¹)

theorem fderiv_xfer (τ K : ℝ) (φ : Vec d × ℝ → ℝ) (hφ : Differentiable ℝ φ)
    (p : ℝ × Vec d) (a : ℝ) (w : Vec d) :
    fderiv ℝ (φ ∘ TmInv τ K) p (a, w) = fderiv ℝ φ (TmInv τ K p) (w, K⁻¹ * a) := by
  have h := (hφ (TmInv τ K p)).hasFDerivAt.comp p (TmInv_hasFDerivAt τ K p)
  rw [h.fderiv]
  simp

theorem xfer_hasCompactSupport (τ K : ℝ) (hK : 0 < K) (φ : Vec d × ℝ → ℝ)
    (hc : HasCompactSupport φ) :
    HasCompactSupport (φ ∘ TmInv τ K) ∧ tsupport (φ ∘ TmInv τ K) ⊆ Tm τ K '' tsupport φ := by
  have hsub : tsupport (φ ∘ TmInv τ K) ⊆ Tm τ K '' tsupport φ := by
    intro p hp
    have h1 := tsupport_comp_subset_preimage φ (f := TmInv (d := d) τ K)
      (TmInv_contDiff τ K).continuous hp
    exact ⟨TmInv τ K p, h1, Tm_TmInv τ K hK p⟩
  have hK' : IsCompact (Tm τ K '' tsupport φ) :=
    (show IsCompact (tsupport φ) from hc).image (Tm_continuous τ K)
  exact ⟨hK'.of_isClosed_subset (isClosed_tsupport _) hsub, hsub⟩

theorem memLp_comp_Tm (τ K : ℝ) (hK : 0 < K) {S : Set (ℝ × Vec d)} (hS : MeasurableSet S)
    {f : ℝ × Vec d → ℝ} (hf : MemLp f 2 (volume.restrict S)) :
    MemLp (fun z => f (Tm τ K z)) 2 (volume.restrict (Tm τ K ⁻¹' S)) := by
  have hE := (TmE (d := d) τ K hK).measurableEmbedding
  have hmap : Measure.map (Tm (d := d) τ K) (volume.restrict (Tm τ K ⁻¹' S)) =
      ENNReal.ofReal K⁻¹ • volume.restrict S := by
    have h1 : Measure.map (TmE (d := d) τ K hK) (volume.restrict (TmE τ K hK ⁻¹' S)) =
        (Measure.map (TmE (d := d) τ K hK) volume).restrict S :=
      (hE.restrict_map volume S).symm
    have h2 : Measure.map (TmE (d := d) τ K hK) volume = ENNReal.ofReal K⁻¹ • volume := by
      have : Measure.map (TmE (d := d) τ K hK) volume = Measure.map (Tm τ K) volume := rfl
      rw [this, volume_map_Tm τ K hK]
    have h3 : Measure.map (Tm (d := d) τ K) (volume.restrict (Tm τ K ⁻¹' S)) =
        Measure.map (TmE (d := d) τ K hK) (volume.restrict (TmE τ K hK ⁻¹' S)) := rfl
    rw [h3, h1, h2, Measure.restrict_smul]
  have h4 : MemLp f 2 (Measure.map (Tm (d := d) τ K) (volume.restrict (Tm τ K ⁻¹' S))) := by
    rw [hmap]
    exact hf.smul_measure ENNReal.ofReal_ne_top
  have h5 : MeasurableEmbedding (Tm (d := d) τ K) := hE
  exact (h5.memLp_map_measure_iff).mp h4

end EinsteinFull.ParabolicBridge
