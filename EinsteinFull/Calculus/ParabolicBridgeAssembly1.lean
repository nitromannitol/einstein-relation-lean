import EinsteinFull.Calculus.ParabolicBridgeOsc
import EinsteinFull.Calculus.ParabolicBridgeMolData
import EinsteinFull.Calculus.ParabolicBridgeMolShift
import EllipticRegularity.Parabolic.ParabolicDef

/-!
# Helper lemmas for the final assembly
-/

open scoped ENNReal

noncomputable section
namespace EinsteinFull.ParabolicBridge

open MeasureTheory Set Filter Topology PDE

/-- Conversion between the `ENNReal` form of the core estimate and `eLpNorm`. -/
theorem core_norm_eq {α : Type*} [MeasurableSpace α] (μ : Measure α) (c : ℝ) (hc : 0 ≤ c)
    (f : α → ℝ) (hf : AEStronglyMeasurable f μ) :
    ((ENNReal.ofReal c * ∫⁻ z, ENNReal.ofReal |f z| ^ (2 : ℝ) ∂μ) ^ (2 : ℝ)⁻¹).toReal =
      c ^ (1 / 2 : ℝ) * (eLpNorm f 2 μ).toReal := by
  have h1 : eLpNorm f 2 μ = (∫⁻ z, ENNReal.ofReal |f z| ^ (2 : ℝ) ∂μ) ^ (2 : ℝ)⁻¹ := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hf]
    simp only [ENNReal.toReal_ofNat, one_div]
    congr 1
    refine lintegral_congr fun z => ?_
    rw [Real.enorm_eq_ofReal_abs]
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ENNReal.toReal_mul, ← h1,
    ← ENNReal.toReal_rpow, ENNReal.toReal_ofReal hc, one_div]

/-- Away from the top time, the extension of `V` by zero agrees with `V` on the upper-closed
sub-cylinder. -/
theorem ae_indicator_eq_on_Ioc {d : ℕ} {U U' : Set (Vec d)} {b b' : ℝ} (hU : U' ⊆ U)
    (hU'm : MeasurableSet U') (hb : b ≤ b') (V : Vec d × ℝ → ℝ) :
    ∀ᵐ z ∂(volume.restrict (U' ×ˢ Ioc b' 0)), (U ×ˢ Ioo b 0).indicator V z = V z := by
  have hne : ∀ᵐ z : Vec d × ℝ ∂(volume : Measure (Vec d × ℝ)), z.2 ∉ ({0} : Set ℝ) := by
    rw [Measure.volume_eq_prod]
    exact (Measure.quasiMeasurePreserving_snd (μ := (volume : Measure (Vec d)))
      (ν := (volume : Measure ℝ))).ae
      ((Set.countable_singleton (0 : ℝ)).ae_notMem (volume : Measure ℝ))
  have hne' : ∀ᵐ z : Vec d × ℝ ∂(volume.restrict (U' ×ˢ Ioc b' 0)), z.2 ∉ ({0} : Set ℝ) :=
    ae_restrict_of_ae hne
  have hmeas : MeasurableSet (U' ×ˢ Ioc b' 0) := hU'm.prod measurableSet_Ioc
  filter_upwards [ae_restrict_mem hmeas, hne'] with z hz hz0
  have hzS : z ∈ U ×ˢ Ioo b 0 :=
    ⟨hU hz.1, lt_of_le_of_lt hb hz.2.1, lt_of_le_of_ne hz.2.2 (fun h => hz0 h)⟩
  exact Set.indicator_of_mem hzS V

end EinsteinFull.ParabolicBridge
