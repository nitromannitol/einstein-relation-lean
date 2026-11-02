import EinsteinFull.Calculus.ParabolicBridgeOsc
import EllipticRegularity.Parabolic.ParabolicDef

/-!
# Volumes and averages for the final assembly
-/

open scoped ENNReal

noncomputable section
namespace EinsteinFull.ParabolicBridge

open MeasureTheory Set Filter Topology PDE

/-- Volume of a rescaled parabolic cylinder. -/
theorem vol_cyl {d : ℕ} (x : Vec d) {ρ : ℝ} (hρ : 0 < ρ) {K : ℝ} (hK : 0 < K) :
    (volume (euclideanBall x ρ ×ˢ Ioo (-ρ ^ 2 / K) 0)).toReal =
      (volume (euclideanBall (0 : Vec d) 1)).toReal * ρ ^ d * (ρ ^ 2 / K) := by
  rw [Measure.volume_eq_prod, Measure.prod_prod, ENNReal.toReal_mul,
    volume_euclideanBall_toReal_eq_unit_mul_of_pos x hρ, Real.volume_Ioo,
    ENNReal.toReal_ofReal (by
      have : 0 < ρ ^ 2 / K := by positivity
      have h3 : (0 : ℝ) - -ρ ^ 2 / K = ρ ^ 2 / K := by ring
      rw [h3]; exact this.le)]
  have h3 : (0 : ℝ) - -ρ ^ 2 / K = ρ ^ 2 / K := by ring
  rw [h3]
  ring

/-- Restriction to a set that is almost a subset of another. -/
theorem restrict_le_of_subset_union_null {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {Q S N : Set α} (hQ : MeasurableSet Q) (hS : MeasurableSet S) (hN : μ N = 0)
    (hsub : Q ⊆ S ∪ N) : μ.restrict Q ≤ μ.restrict S := by
  rw [Measure.le_iff]
  intro s hs
  rw [Measure.restrict_apply hs, Measure.restrict_apply hs]
  calc μ (s ∩ Q) ≤ μ (s ∩ S ∪ N) := by
        refine measure_mono ?_
        intro z hz
        rcases hsub hz.2 with h | h
        · exact Or.inl ⟨hz.1, h⟩
        · exact Or.inr h
    _ ≤ μ (s ∩ S) + μ N := measure_union_le _ _
    _ = μ (s ∩ S) := by rw [hN, add_zero]

theorem sqrt_integral_eq_mul_avg {α : Type*} [MeasurableSpace α] (ν : Measure α)
    (hpos : 0 < ν.real Set.univ) (f : α → ℝ) :
    Real.sqrt (∫ z, f z ^ 2 ∂ν) =
      Real.sqrt (ν.real Set.univ) * Real.sqrt (⨍ z, |f z| ^ 2 ∂ν) := by
  rw [← Real.sqrt_mul hpos.le, average_eq, smul_eq_mul]
  congr 1
  have : ∫ z, |f z| ^ 2 ∂ν = ∫ z, f z ^ 2 ∂ν :=
    integral_congr_ae (Filter.Eventually.of_forall fun z => sq_abs _)
  rw [this, mul_inv_cancel_left₀ hpos.ne']

/-- The average mean-square deviation is bounded by that around any constant. -/
theorem sqrt_avg_osc_le_const {α : Type*} [MeasurableSpace α] (ν : Measure α)
    [IsFiniteMeasure ν] {V : α → ℝ} (hV : MemLp V 2 ν) (κ : ℝ) :
    Real.sqrt (⨍ z, |V z - ⨍ w, V w ∂ν| ^ 2 ∂ν) ≤ Real.sqrt (⨍ z, |V z - κ| ^ 2 ∂ν) := by
  refine Real.sqrt_le_sqrt ?_
  have e1 := average_eq (μ := ν) (fun z => |V z - ⨍ w, V w ∂ν| ^ 2)
  have e2 := average_eq (μ := ν) (fun z => |V z - κ| ^ 2)
  rw [e1, e2, smul_eq_mul, smul_eq_mul]
  refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr measureReal_nonneg)
  have h1 : ∫ z, |V z - ⨍ w, V w ∂ν| ^ 2 ∂ν = ∫ z, (V z - ⨍ w, V w ∂ν) ^ 2 ∂ν :=
    integral_congr_ae (Filter.Eventually.of_forall fun z => sq_abs _)
  have h2 : ∫ z, |V z - κ| ^ 2 ∂ν = ∫ z, (V z - κ) ^ 2 ∂ν :=
    integral_congr_ae (Filter.Eventually.of_forall fun z => sq_abs _)
  rw [h1, h2]
  exact integral_sq_sub_average_le ν hV κ

/-- Comparison of mean squares on nested sets. -/
theorem avg_sq_le_of_subset {α : Type*} [MeasurableSpace α] (μ : Measure α) {E S : Set α}
    (hE : MeasurableSet E) (hS : MeasurableSet S) (hsub : E ⊆ S)
    (hEpos : 0 < μ.real E) (hSpos : 0 < μ.real S) (hSfin : μ S ≠ ⊤) {g : α → ℝ}
    (hg : IntegrableOn (fun z => |g z| ^ 2) S μ) :
    ⨍ z in E, |g z| ^ 2 ∂μ ≤ (μ.real S / μ.real E) * ⨍ z in S, |g z| ^ 2 ∂μ := by
  rw [setAverage_eq, setAverage_eq, smul_eq_mul, smul_eq_mul]
  have hI : ∫ z in E, |g z| ^ 2 ∂μ ≤ ∫ z in S, |g z| ^ 2 ∂μ :=
    setIntegral_mono_set hg (Filter.Eventually.of_forall fun z => by positivity)
      (Filter.Eventually.of_forall hsub)
  have hdiv : (μ.real E)⁻¹ * ∫ z in E, |g z| ^ 2 ∂μ ≤ (μ.real E)⁻¹ * ∫ z in S, |g z| ^ 2 ∂μ :=
    mul_le_mul_of_nonneg_left hI (inv_nonneg.mpr hEpos.le)
  refine hdiv.trans (le_of_eq ?_)
  field_simp

end EinsteinFull.ParabolicBridge
